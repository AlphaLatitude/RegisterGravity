#!/usr/bin/env python3
"""scripts/cassini.py: the external-field quadrupole of the Sun in the Galaxy's field, for the
paper's law read in the total field (Sec. IV.B of the paper; not a Lean proof).

    python3 cassini.py [eta] [nr] [nth]        default eta = 1.6, 1120 x 96 grid, about 10 min

Needs numpy and scipy.  The result for the paper's law, q2 = 0.348 at eta = 1.6 (Q2 = 4.0e-26 s^-2),
is carried into Numerics.lean as `q2_total_field`; `Numerics.cassini_total_field` certifies what
follows from it.  Blanchet & Novak, Mon. Not. R. Astron. Soc. 412, 2530 (2011), Table 1, is
reproduced for their functions as a check of the method.
"""
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from numpy.polynomial.legendre import legval

# ---------------------------------------------------------------- interpolating functions mu(x), x = a/a0

def _x_of_s(s):
    """x = s^2/(1 - e^{-s}) with s = sqrt(y), y = g_N/a0; series for small s."""
    s = np.asarray(s, dtype=float)
    small = s < 1e-6
    with np.errstate(divide='ignore', invalid='ignore'):
        x = np.where(small, s + s * s / 2, s * s / (-np.expm1(-s)))
    return x

def mu_paper(x):
    """b(x) = y/x where x = y/(1 - exp(-sqrt y)): the carrier fraction as a function of a/a0 (Sec. IV C,
    second reading).  Bisection on s = sqrt(y), x(s) being increasing; b -> x - x^2 for small x and
    1 - e^{-sqrt x} for large x."""
    x = np.asarray(x, dtype=float)
    lo = np.zeros_like(x)
    hi = np.maximum(np.sqrt(x), x) + 1.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        xm = _x_of_s(mid)
        lo = np.where(xm < x, mid, lo)
        hi = np.where(xm < x, hi, mid)
    s_ = 0.5 * (lo + hi)
    with np.errstate(divide='ignore', invalid='ignore'):
        b = np.where(x > 0, s_ * s_ / x, 0.0)
    return np.clip(b, 0.0, 1.0)

def mu_simple(x):
    return x / (1 + x)

def mu_standard(x):
    return x / np.sqrt(1 + x * x)

def mu_exp(x):
    return 1 - np.exp(-x)

def mu_newton(x):
    return np.ones_like(np.asarray(x, dtype=float))

def mu_n(n):
    return lambda x: x / (1 + np.asarray(x, dtype=float) ** n) ** (1.0 / n)

MUS = {'paper': mu_paper, 'simple': mu_simple, 'standard': mu_standard, 'exp': mu_exp, 'newton': mu_newton,
       'mu5': mu_n(5), 'mu20': mu_n(20)}

# ---------------------------------------------------------------- the grid and the operator

class Grid:
    def __init__(self, rmin=1e-3, rmax=1e4, nr=560, nth=96):
        self.s = np.linspace(np.log(rmin), np.log(rmax), nr)
        self.ds = self.s[1] - self.s[0]
        self.dth = np.pi / nth
        self.th = (np.arange(nth) + 0.5) * self.dth
        self.nr, self.nth = nr, nth
        self.r = np.exp(self.s)
        self.R, self.TH = np.meshgrid(self.r, self.th, indexing='ij')
        self.S = np.log(self.R)
        self.sin = np.sin(self.TH); self.cos = np.cos(self.TH)
        self.sin_half_p = np.sin(self.th + 0.5 * self.dth)   # sin at theta_{j+1/2}
        self.sin_half_m = np.sin(self.th - 0.5 * self.dth)   # sin at theta_{j-1/2}; 0 at the poles

    def phi0(self, eta):
        return -1.0 / self.R - eta * self.R * self.cos

    def grad(self, F):
        """(d_s F, d_theta F) by centred differences, one-sided at the s ends (theta ends: natural)."""
        Fs = np.empty_like(F); Ft = np.empty_like(F)
        Fs[1:-1] = (F[2:] - F[:-2]) / (2 * self.ds)
        Fs[0] = (F[1] - F[0]) / self.ds
        Fs[-1] = (F[-1] - F[-2]) / self.ds
        Ft[:, 1:-1] = (F[:, 2:] - F[:, :-2]) / (2 * self.dth)
        Ft[:, 0] = (F[:, 1] - F[:, 0]) / self.dth
        Ft[:, -1] = (F[:, -1] - F[:, -2]) / self.dth
        return Fs, Ft

    def field_magnitude(self, Phi):
        Fs, Ft = self.grad(Phi)
        return np.sqrt(Fs**2 + Ft**2) / self.R

    def operator(self, mu, outer='robin'):
        """Sparse matrix of L_mu[psi] = d_s(mu d_s psi) + mu d_s psi + (1/sin) d_th(sin mu d_th psi),
        with psi = 0 at s_min (row kept as identity) and d_r(r psi) = 0 at s_max, i.e. d_s psi = -psi.
        Vectorised assembly."""
        nr, nth, ds, dth = self.nr, self.nth, self.ds, self.dth
        N = nr * nth
        I, J = np.meshgrid(np.arange(nr), np.arange(nth), indexing='ij')
        idx = (I * nth + J)
        mu_sp = np.zeros((nr, nth)); mu_sp[:-1] = 0.5 * (mu[1:] + mu[:-1])     # at s_{i+1/2}
        mu_sm = np.zeros((nr, nth)); mu_sm[1:] = mu_sp[:-1]                       # at s_{i-1/2}
        mu_tp = np.zeros((nr, nth)); mu_tp[:, :-1] = 0.5 * (mu[:, 1:] + mu[:, :-1])  # at theta_{j+1/2}
        mu_tm = np.zeros((nr, nth)); mu_tm[:, 1:] = mu_tp[:, :-1]
        interior = (I > 0) & (I < nr - 1)
        rows, cols, vals = [], [], []
        def add(mask, di, dj, v):
            m = mask & (I + di >= 0) & (I + di < nr) & (J + dj >= 0) & (J + dj < nth)
            rows.append(idx[m]); cols.append(((I + di) * nth + (J + dj))[m]); vals.append(v[m])
        # d_s(mu d_s psi) + mu d_s psi
        add(interior, +1, 0, mu_sp / ds**2 + mu / (2 * ds))
        add(interior, -1, 0, mu_sm / ds**2 - mu / (2 * ds))
        diag = -(mu_sp + mu_sm) / ds**2
        # theta part
        sinj = self.sin
        cp = self.sin_half_p[None, :] * mu_tp / (sinj * dth**2)
        cm = self.sin_half_m[None, :] * mu_tm / (sinj * dth**2)
        cp = np.where(J + 1 < nth, cp, 0.0); cm = np.where(J - 1 >= 0, cm, 0.0)
        add(interior, 0, +1, cp)
        add(interior, 0, -1, cm)
        diag = diag - cp - cm
        add(interior, 0, 0, diag)
        # boundaries
        first = (I == 0)
        add(first, 0, 0, np.ones((nr, nth)))
        last = (I == nr - 1)
        if outer == 'robin':
            add(last, 0, 0, np.full((nr, nth), 1.0 / ds + 1.0))
            add(last, -1, 0, np.full((nr, nth), -1.0 / ds))
        else:   # Neumann: (psi_i - psi_{i-1})/ds = given value (in the right-hand side)
            add(last, 0, 0, np.full((nr, nth), 1.0 / ds))
            add(last, -1, 0, np.full((nr, nth), -1.0 / ds))
        rows = np.concatenate(rows); cols = np.concatenate(cols); vals = np.concatenate(vals)
        return sp.csr_matrix((vals, (rows, cols)), shape=(N, N))

    def apply(self, A, F):
        return (A @ F.ravel()).reshape(F.shape)

def solve_aqual(mu_fn, eta, grid, tol=1e-10, maxit=400, omega=0.5, verbose=False, psi0=None,
                outer='robin', outer_value=0.0):
    """Damped Picard iteration (omega = 1/2 converges in every regime, since the map's multiplier is
    1 - omega(1 + L) with L = d ln mu/d ln x in [0, 1]).  Returns psi (anomaly), Phi, mu, the log."""
    Phi0 = grid.phi0(eta)
    psi = np.zeros_like(Phi0) if psi0 is None else psi0.copy()
    A1 = grid.operator(np.ones_like(Phi0), outer=outer)
    res1 = grid.apply(A1, Phi0)       # the discrete residual of the harmonic Phi0: truncation error only
    log = []
    for k in range(maxit):
        Phi = Phi0 + psi
        x = grid.field_magnitude(Phi)
        mu = mu_fn(x)
        A = grid.operator(mu, outer=outer)
        rhs = -(grid.apply(A, Phi0) - res1)   # = -div((mu - 1) grad Phi0), the physical source only
        # boundary rows: psi = 0 at s_min; at s_max the condition is on psi alone
        rhs[0, :] = 0.0
        rhs[-1, :] = outer_value
        psi_star = spla.spsolve(A.tocsc(), rhs.ravel()).reshape(psi.shape)
        dpsi = psi_star - psi
        psi = psi + omega * dpsi
        err = np.max(np.abs(dpsi))
        log.append(err)
        if verbose and (k % 10 == 0 or err < tol):
            print(f'  it {k:4d}  max|dpsi| = {err:.3e}')
        if err < tol:
            break
    return psi, Phi0 + psi, mu, log

def legendre_modes(grid, F, lmax=4, lfit=14):
    """F_l(r) by least squares of F(r, theta) on P_0..P_lfit at each r (exact for polynomial content, no
    quadrature aliasing of the monopole into l = 2 as the midpoint rule has)."""
    c = np.cos(grid.th)
    V = np.stack([legval(c, np.eye(lfit + 1)[l]) for l in range(lfit + 1)], axis=1)   # (nth, lfit+1)
    coef, *_ = np.linalg.lstsq(V, F.T, rcond=None)      # (lfit+1, nr)
    return {l: coef[l] for l in range(lmax + 1)}

def inner_coefficients(grid, psi, r_lo=0.01, r_hi=0.05):
    """c_l = psi_l / r^l averaged over r in [r_lo, r_hi] (inner region: mu = 1 to e^{-1/r_hi}), with its spread."""
    modes = legendre_modes(grid, psi)
    sel = (grid.r >= r_lo) & (grid.r <= r_hi)
    res = {}
    for l, Fl in modes.items():
        cl = Fl[sel] / grid.r[sel] ** l
        res[l] = (cl.mean(), cl.std(), cl.min(), cl.max())
    return res

def q2_from_phantom(grid, Phi, mu):
    """c2 = (1/4pi) int (mu-1) grad Phi . grad(r^-3 P2) dV over the whole grid (check of the projection)."""
    Fs, Ft = grid.grad(Phi)
    gr, gt = Fs / grid.R, Ft / grid.R
    P2 = 0.5 * (3 * grid.cos**2 - 1)
    dP2 = -3 * grid.cos * grid.sin   # dP2/dtheta
    hr = -3 * grid.R**-4 * P2
    ht = grid.R**-4 * dP2            # (1/r) d_theta (r^-3 P2)
    integrand = (mu - 1) * (gr * hr + gt * ht) * 2 * np.pi * grid.R**2 * grid.sin
    # trapezoid in s (dV = r^2 sin dr dtheta = r^3 sin ds dtheta), midpoint in theta
    I = (integrand * grid.R).sum(axis=1) * grid.dth
    c2 = np.trapezoid(I, grid.s) / (4 * np.pi)
    return c2

def algebraic_a(mu_fn, r):
    """the spherical law mu(a) a = 1/r^2 solved for a by bisection"""
    r = np.asarray(r, dtype=float); gN = 1 / r**2
    lo = np.zeros_like(r); hi = np.maximum(gN, np.sqrt(gN)) * 2 + 1
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        f = mu_fn(mid) * mid
        lo = np.where(f < gN, mid, lo); hi = np.where(f < gN, hi, mid)
    return 0.5 * (lo + hi)

def spherical_check(mu_fn, grid):
    """eta = 0: the solution must satisfy mu(a) a = 1/r^2 (the algebraic law); the outer condition is the
    exact slope d_s psi = -r a(r) - 1/r at r_max, since the deep potential grows like ln r."""
    rmax = grid.r[-1]
    val = rmax * algebraic_a(mu_fn, rmax) - 1 / rmax
    psi, Phi, mu, log = solve_aqual(mu_fn, 0.0, grid, tol=1e-11, outer='neumann', outer_value=float(val))
    a = grid.field_magnitude(Phi)[:, grid.nth // 2]
    r = grid.r
    gN = 1 / r**2
    err = np.abs(mu_fn(a) * a - gN) / gN
    sel = (r > 0.01) & (r < 100)
    return err[sel].max(), len(log), err


# ---------------------------------------------------------------- the runs of Sec. IV.B

if __name__ == '__main__':
    import sys, time
    eta = float(sys.argv[1]) if len(sys.argv) > 1 else 1.6
    nr = int(sys.argv[2]) if len(sys.argv) > 2 else 1120
    nth = int(sys.argv[3]) if len(sys.argv) > 3 else 96
    A0, GMS = 1.1996372e-10, 1.3271244e20          # the paper's a0 (Numerics.a0v), GM_sun
    rM = (GMS / A0) ** 0.5
    unit = A0 / rM                                   # Q2 in s^-2 per unit of q2
    g = Grid(rmin=1e-3, rmax=1e4, nr=nr, nth=nth)
    print(f'eta = g_e/a0 = {eta}; grid {nr} x {nth}; a0/r_M = {unit:.4e} s^-2')
    print('Blanchet & Novak (2011) Table 1 at eta = 1.6: simple 0.33, standard 0.19, exp 0.26, mu5 0.065, mu20 0.018')
    for name in ['paper', 'simple', 'standard', 'exp', 'mu5', 'mu20']:
        t = time.time()
        psi, Phi, mu, log = solve_aqual(MUS[name], eta, g, tol=1e-10, maxit=400)
        co = inner_coefficients(g, psi, 0.02, 0.06)
        q2 = -3 * co[2][0]
        print(f'  {name:9s}  q2 = {q2:.4f}   Q2 = {q2 * unit:.3e} s^-2   (c1/r = {co[1][0]:+.1e}, {len(log)} iterations, {time.time() - t:.0f} s)')
    print('Cassini (Hees et al. 2014): Q2 = (3 +- 3) x 10^-27 s^-2')
