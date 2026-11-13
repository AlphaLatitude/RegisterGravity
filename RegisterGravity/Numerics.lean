import RegisterGravity.Cosmo
import RegisterGravity.DeSitter
import RegisterGravity.Capacity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.GCongr

/-!
# The numbers of the paper, certified

Every number that *Gravitation from Hilbert-Space Granularity* (the version named in README.md)
computes from its inputs, in
Table I, the text, and Appendix A, recomputed from the Appendix's inputs and certified by an
interval: each theorem states `lo < quantity < hi`, and every number in the interval rounds to the
value the paper quotes.  Observational values and their uncertainties are inputs, not claims.

## Inputs, as exact rationals

Appendix A prints `c`, `ℏ` and `G` to four figures, with the values used here beside them, and
prints `GM☉` in full.  The megaparsec, the astronomical unit, the year, the solar radius and
Mercury's orbit are standard units and solar-system constants that the paper does not print: its
Data availability refers to these files for them.  `k_B` is not printed either; it cancels in
every figure certified here.  `q`, Palmer's range and Davies' number are in the paper's text.

`c = 299792458 m/s`, `ℏ = 1.054571817e-34 J s`, `k_B = 1.380649e-23 J/K`,
`G = 6.67430e-11 m³ kg⁻¹ s⁻²`, `H₀ = 67.4 km/s/Mpc` with Planck's uncertainty `±0.5` and with
`1 Mpc = 3.0856775814913673e22 m`, the local `H₀ = 73 km/s/Mpc` (`log2_L73`),
`Ω_Λ = 0.685` with Planck's uncertainty `±0.007`, DESI's `Ω_Λ = 0.7025 ± 0.0086` [DESI DR2 2025],
the measured scale `a₀ = 1.20e-10 m/s²` with the uncertainties `±0.02 ± 0.24` [McGaugh 2016] and
`1.19 ± 0.04 ± 0.09` [Desmond 2023], `1 kpc = 3.0856775814913673e19 m` and Neptune's orbit at
`30.07 au`; the Galaxy's field at the Sun, `1.9e-10 m/s²`, and the Sun's distance from the Galactic
center, `8.2 kpc` (`ge₀`, `R₀`); for the Sun the IAU heliocentric constant at its nominal
value, `GM☉ = 1.3271244e20 m³/s²` (so `M☉ = GM☉/G`), `1 au = 149597870700 m`, `R☉ = 6.957e8 m`, and
for Mercury `a = 5.7909050e10 m`, `e = 0.205630`, `T = 87.9691 d`; `1 yr = 365.25 d`;
`Ω_m = 0.315`, `q = −0.53`; the lunar-laser-ranging bound `|Ġ/G| ≲ 10⁻¹³ yr⁻¹`; Palmer's range
of `L`, `10⁶⁴` to `10¹⁰⁹`, and Davies' `10¹²²`; and `1 MeV = 1.602176634e-13 J` with the fine-structure constant
`α_e = 7.2973525643e-3` (CODATA 2022; `1/α_e` is `137.036` to the figures the paper prints) for
`scatter_1MeV`, the bath's scatterings in the bit's history (Sec. II, Appendix A).

## `π`, `ln 2` and `e`

`π` and `ln 2` are Mathlib's `Real.pi` and `Real.log 2`, and they enter through Mathlib's bounds
`3.141592 < π < 3.141593` (`Real.pi_gt_d6`, `Real.pi_lt_d6`) and
`0.6931471803 < ln 2 < 0.6931471808` (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`); `e` enters
the values of the law, the departure at Neptune and `ln(L_cos²/4)`, through `Real.exp_one_gt_d9`,
`Real.exp_one_lt_d9`, `Real.quadratic_le_exp_of_nonneg`,
`Real.exp_bound'`, `Real.exp_bound_div_one_sub_of_interval'`, `Real.add_one_le_exp` and
`Real.one_sub_inv_le_log_of_pos`; other values of `exp` are bounded by `1 + x ≤ eˣ` and, for
`0 < x < 1`, `eˣ < 1/(1 − x)`, applied to `x = 0.001` and raised to a power.  Nothing else is
assumed.

## Bridge to the chain

`reg` is the register of `Chain.lean` with these inputs, `π` and `ln 2`, the cell fixed from `G`,
and `L` from the horizon.  With these choices the hypotheses of the chain hold by construction:
Jacobson's relation `hJ` (`reg_jacobson`), since the cell is fixed from `G`; the horizon at the
observed de Sitter radius (`reg_RL`), since `L` is fixed from the horizon; and the boundary
condition `hdS` for the observed `Λ` (`reg_deSitter`).  What they show is that the observed
universe meets the hypotheses together, so that the chain's quantities for these inputs are the
numbers certified here (`reg_*`); the chain's scale is the certified `a₀` (`reg_a0`).
-/

open Real

-- `norm_num` evaluates powers such as `2 ^ 41003` exactly; raise Lean's guard on large exponents.
set_option exponentiation.threshold 50000

namespace Register
namespace Numerics

local notation "c₀" => (299792458 : ℝ)
local notation "ℏ₀" => ((1054571817 : ℝ) / 10 ^ 43)
local notation "kB₀" => ((1380649 : ℝ) / 10 ^ 29)
local notation "G₀" => ((66743 : ℝ) / 10 ^ 15)
local notation "Mpc₀" => ((30856775814913673 : ℝ) * 10 ^ 6)
local notation "H₀" => ((67400 : ℝ) / ((30856775814913673 : ℝ) * 10 ^ 6))
local notation "ΩΛ₀" => ((685 : ℝ) / 1000)
local notation "a₀" => ((12 : ℝ) / 10 ^ 11)
local notation "GMs₀" => ((13271244 : ℝ) * 10 ^ 13)
local notation "au₀" => ((149597870700 : ℝ))
local notation "yr₀" => ((31557600 : ℝ))
local notation "Rs₀" => ((6957 : ℝ) * 10 ^ 5)
local notation "kpc₀" => ((30856775814913673 : ℝ) * 10 ^ 3)

lemma ln2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- Mathlib's bounds on `π` and `ln 2`, and their positivity, in the local context. -/
macro "pi_ln2" : tactic => `(tactic| (
  have := Real.pi_gt_d6; have := Real.pi_lt_d6; have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9; have := Real.pi_pos; have := Real.log_pos one_lt_two
  have := Real.pi_pos.ne'; have := (Real.log_pos one_lt_two).ne'))

lemma lt_of_sq {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 ≤ a) (h : a ^ 2 < Q ^ 2) : a < Q :=
  (pow_lt_pow_iff_left₀ ha hQ two_ne_zero).1 h

lemma lt_of_sq' {Q b : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b) (h : Q ^ 2 < b ^ 2) : Q < b :=
  (pow_lt_pow_iff_left₀ hQ hb two_ne_zero).1 h

/-! ## `π` and `ln 2` in the combinations the numbers use -/

lemma pl_lo : (3.141592 : ℝ) * 0.6931471803 < π * Real.log 2 :=
  mul_lt_mul'' Real.pi_gt_d6 Real.log_two_gt_d9 (by norm_num) (by norm_num)

lemma pl_hi : π * Real.log 2 < (3.141593 : ℝ) * 0.6931471808 :=
  mul_lt_mul'' Real.pi_lt_d6 Real.log_two_lt_d9 Real.pi_pos.le ln2_pos.le

lemma pq_lo : (3.141592 : ℝ) / 0.6931471808 < π / Real.log 2 := by
  pi_ln2
  rw [lt_div_iff₀ ln2_pos]
  have : (3.141592 : ℝ) / 0.6931471808 * Real.log 2 < 3.141592 / 0.6931471808 * 0.6931471808 :=
    mul_lt_mul_of_pos_left Real.log_two_lt_d9 (by norm_num)
  linarith [show (3.141592 : ℝ) / 0.6931471808 * 0.6931471808 = 3.141592 by norm_num]

lemma pq_hi : π / Real.log 2 < (3.141593 : ℝ) / 0.6931471803 := by
  pi_ln2
  rw [div_lt_iff₀ ln2_pos]
  have : (3.141593 : ℝ) / 0.6931471803 * 0.6931471803 < 3.141593 / 0.6931471803 * Real.log 2 :=
    mul_lt_mul_of_pos_left Real.log_two_gt_d9 (by norm_num)
  linarith [show (3.141593 : ℝ) / 0.6931471803 * 0.6931471803 = 3.141593 by norm_num]

lemma p2_lo : (3.141592 : ℝ) ^ 2 < π ^ 2 :=
  pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num) two_ne_zero

lemma p2_hi : π ^ 2 < (3.141593 : ℝ) ^ 2 :=
  pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le two_ne_zero

lemma p3q_lo : (3.141592 : ℝ) ^ 3 / 0.6931471808 < π ^ 3 / Real.log 2 := by
  have h3 : (3.141592 : ℝ) ^ 3 < π ^ 3 := pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num) (by norm_num)
  calc (3.141592 : ℝ) ^ 3 / 0.6931471808 < π ^ 3 / 0.6931471808 := by gcongr
    _ < π ^ 3 / Real.log 2 := by
      apply div_lt_div_of_pos_left (by positivity) ln2_pos Real.log_two_lt_d9

lemma p3q_hi : π ^ 3 / Real.log 2 < (3.141593 : ℝ) ^ 3 / 0.6931471803 := by
  have h3 : π ^ 3 < (3.141593 : ℝ) ^ 3 := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by norm_num)
  calc π ^ 3 / Real.log 2 < π ^ 3 / 0.6931471803 := by
        apply div_lt_div_of_pos_left (by positivity) (by norm_num) Real.log_two_gt_d9
    _ < (3.141593 : ℝ) ^ 3 / 0.6931471803 := by gcongr

/-! ## The derived quantities -/

/-- the Planck length, `ℓ_P = √(ℏG/c³)` -/
noncomputable def lP : ℝ := Real.sqrt (ℏ₀ * G₀ / c₀ ^ 3)
/-- the cell, Eq. (cell): `ℓ_c = √(π ln 2 ℏG/c³)` -/
noncomputable def lc : ℝ := Real.sqrt (π * Real.log 2 * ℏ₀ * G₀ / c₀ ^ 3)
/-- the asymptotic Hubble rate, `H_∞ = H₀√Ω_Λ` -/
noncomputable def Hinf : ℝ := H₀ * Real.sqrt ΩΛ₀
/-- the de Sitter radius, `R_Λ = c/H_∞` -/
noncomputable def RL : ℝ := c₀ / Hinf
/-- `L` from the horizon, Eq. (Lcos): `L = 2πR_Λ/ℓ_c` -/
noncomputable def Lcos : ℝ := 2 * π * RL / lc
/-- the scale, Eq. (f): `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)` -/
noncomputable def a0v : ℝ := (1 - Real.log 2) * c₀ ^ 2 / (2 * Real.log 2 * RL)
/-- the coefficient of the scale, `(1 − ln 2)/2 ln 2` -/
noncomputable def κ0 : ℝ := (1 - Real.log 2) / (2 * Real.log 2)
/-- the Sun's mass in cell masses, `α = M☉/m_c = M☉cℓ_c/ℏ` with `M☉ = GM☉/G` -/
noncomputable def αs : ℝ := GMs₀ / G₀ * c₀ * lc / ℏ₀
/-- Newton's constant from `L`, Eq. (G): `G = 4πc³R_Λ²/(ℏL² ln 2)` -/
noncomputable def Gof (L : ℝ) : ℝ := 4 * π * c₀ ^ 3 * RL ^ 2 / (ℏ₀ * L ^ 2 * Real.log 2)

lemma lc_pos : 0 < lc := by pi_ln2; unfold lc; positivity

lemma lc_sq : lc ^ 2 = π * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3) := by
  pi_ln2; unfold lc; rw [Real.sq_sqrt (by positivity)]; ring

lemma lP_pos : 0 < lP := by unfold lP; positivity

lemma lP_sq : lP ^ 2 = ℏ₀ * G₀ / c₀ ^ 3 := by unfold lP; rw [Real.sq_sqrt (by positivity)]

lemma Hinf_pos : 0 < Hinf := by unfold Hinf; positivity

lemma Hinf_sq : Hinf ^ 2 = H₀ ^ 2 * ΩΛ₀ := by
  unfold Hinf; rw [mul_pow, Real.sq_sqrt (by norm_num)]

lemma RL_pos : 0 < RL := by unfold RL; have := Hinf_pos; positivity

lemma RL_sq : RL ^ 2 = c₀ ^ 2 / (H₀ ^ 2 * ΩΛ₀) := by
  unfold RL; rw [div_pow, Hinf_sq]

lemma Lcos_pos : 0 < Lcos := by
  have := lc_pos; have := RL_pos; unfold Lcos; positivity

lemma Lcos_sq : Lcos ^ 2 = π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
  pi_ln2
  unfold Lcos
  rw [div_pow, mul_pow, mul_pow, RL_sq, lc_sq]
  field_simp
  ring

lemma αs_pos : 0 < αs := by
  have := lc_pos; unfold αs; positivity

lemma αs_sq : αs ^ 2 = π * Real.log 2 * (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) := by
  unfold αs
  rw [div_pow, mul_pow, mul_pow, lc_sq]
  field_simp

lemma Gof_eq (L : ℝ) :
    Gof L = π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * L ^ 2)) := by
  pi_ln2
  unfold Gof
  rw [RL_sq]
  field_simp

/-! ## Bridge to the chain -/

/-- The register of `Chain.lean` with the Appendix's inputs, Mathlib's `π` and `ln 2`, the cell from
`G`, and `L` from the horizon. -/
noncomputable def reg : Reg where
  c := c₀
  ℏ := ℏ₀
  kB := kB₀
  ℓc := lc
  L := Lcos
  c_pos := by norm_num
  ℏ_pos := by norm_num
  kB_pos := by norm_num
  ℓc_pos := lc_pos
  L_pos := Lcos_pos

/-- The horizon of Eq. (ident) is at the observed de Sitter radius, by construction: `L` is fixed
from the horizon. -/
theorem reg_RL : reg.RL = RL := by
  have := lc_pos; have := Real.pi_pos
  simp only [Reg.RL, reg, Reg.pi_def]
  unfold Lcos
  field_simp

/-- The observed `Λ = 3/R_Λ²` satisfies the boundary condition of the chain: the horizon of the
solution without a mass is the register's (`Reg.deSitter`). -/
theorem reg_deSitter : reg.fSdS G₀ 0 (3 / RL ^ 2) reg.RL = 0 :=
  (reg.deSitter G₀ _).2 (by rw [reg_RL])

/-- **Jacobson's relation holds for these inputs**, by construction: with the cell fixed from the
measured `G`, the register's entropy density gives that `G` back, so the hypothesis `hJ` of every
theorem of the chain is met. -/
theorem reg_jacobson : G₀ = reg.c ^ 3 * reg.kB / (4 * reg.ℏ * reg.η) := by
  pi_ln2
  rw [Reg.eta_eq]
  simp only [reg, Reg.pi_def, Reg.ln2_def]
  rw [lc_sq]
  field_simp

/-- **The cell is `√(π ln 2)` Planck lengths** (Eq. (cell)), from the chain's `cell_from_G`. -/
theorem reg_cell : lc = Real.sqrt (π * Real.log 2) * lP := by
  have h := (reg.cell_from_G G₀ reg_jacobson).2
  simp only [reg] at h
  rw [h]
  rfl

/-- **The chain's scale is the certified one**: `reg.a₀ = a₀` with the observed `R_Λ`. -/
theorem reg_a0 : reg.a0 = a0v := by
  unfold Reg.a0 a0v
  rw [reg_RL]
  rfl

/-- The chain's `G = 4πc³R_Λ²/(ℏL² ln 2)` for these inputs is `Gof L`, and at `L_cos` it is the
measured `G` (the identity the paper notes: with `L_cos`, Eq. (G) returns its input). -/
theorem Gof_Lcos : Gof Lcos = G₀ := by
  have h := (reg.G_eq G₀ reg_jacobson).2
  rw [reg_RL] at h
  rw [h]
  rfl

/-- The chain's temperature `E_c/L` for these inputs is `ℏH_∞/2π`, Eq. (energy). -/
theorem reg_temperature : reg.Ec / reg.L = ℏ₀ * Hinf / (2 * π) := by
  have := Real.pi_pos; have := lc_pos; have := Hinf_pos
  simp only [Reg.Ec, reg]
  unfold Lcos RL
  field_simp

/-- The chain's lap time `Lt_c` for these inputs is the de Sitter period `2π/H_∞`, and its Hubble
rate `2π/Lt_c` is `H_∞`. -/
theorem reg_clock : reg.L * reg.tc = 2 * π / Hinf ∧ 2 * π / (reg.L * reg.tc) = Hinf := by
  have := Real.pi_pos; have := Hinf_pos
  have h : reg.L * reg.tc = 2 * π / Hinf := by
    rw [reg.lap_time, reg_RL]
    simp only [reg, Reg.pi_def]
    unfold RL
    field_simp
  refine ⟨h, ?_⟩
  rw [h]; field_simp

/-! ## The cell and the units of the cell (Table I, Eq. (cell), Appendix A) -/

/-- A tight enclosure of the cell. -/
lemma lc_tight : 2.38504e-35 < lc ∧ lc < 2.38506e-35 := by
  constructor
  · apply lt_of_sq lc_pos.le (by norm_num)
    rw [lc_sq]
    calc (2.38504e-35 : ℝ) ^ 2 < (3.141592 * 0.6931471803) * (ℏ₀ * G₀ / c₀ ^ 3) := by norm_num
      _ < π * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3) := mul_lt_mul_of_pos_right pl_lo (by norm_num)
  · apply lt_of_sq' lc_pos.le (by norm_num)
    rw [lc_sq]
    calc π * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3) < (3.141593 * 0.6931471808) * (ℏ₀ * G₀ / c₀ ^ 3) :=
          mul_lt_mul_of_pos_right pl_hi (by norm_num)
      _ < (2.38506e-35 : ℝ) ^ 2 := by norm_num

/-- `ℓ_P = 1.616×10⁻³⁵ m` (`1.62` to three figures) and `ℓ_c = √(π ln 2) ℓ_P = 2.385×10⁻³⁵ m`
(`2.39` to three figures). -/
theorem cell_val :
    (1.6155e-35 < lP ∧ lP < 1.6165e-35) ∧ (2.38504e-35 < lc ∧ lc < 2.38506e-35) := by
  refine ⟨⟨?_, ?_⟩, lc_tight⟩
  · apply lt_of_sq lP_pos.le (by norm_num); rw [lP_sq]; norm_num
  · apply lt_of_sq' lP_pos.le (by norm_num); rw [lP_sq]; norm_num

/-- The units of the cell (Appendix A): `t_c = 7.96×10⁻⁴⁴ s`, `m_c = 1.475×10⁻⁸ kg`,
`E_c = 1.326×10⁹ J`, `a_c = 3.77×10⁵¹ m/s²`. -/
theorem cell_units :
    (7.955e-44 < lc / c₀ ∧ lc / c₀ < 7.965e-44) ∧
    (1.4745e-8 < ℏ₀ / (c₀ * lc) ∧ ℏ₀ / (c₀ * lc) < 1.4755e-8) ∧
    (1.3255e9 < ℏ₀ * c₀ / lc ∧ ℏ₀ * c₀ / lc < 1.3265e9) ∧
    (3.765e51 < c₀ ^ 2 / lc ∧ c₀ ^ 2 / lc < 3.775e51) := by
  obtain ⟨h1, h2⟩ := lc_tight
  have := lc_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-! ## The horizon (Sec. II, Sec. IV.D, Appendix A) -/

lemma Hinf_tight : 1.8078e-18 < Hinf ∧ Hinf < 1.8079e-18 := by
  constructor
  · apply lt_of_sq Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num
  · apply lt_of_sq' Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num

lemma RL_tight : 1.6583e26 < RL ∧ RL < 1.6584e26 := by
  constructor
  · apply lt_of_sq RL_pos.le (by norm_num); rw [RL_sq]; norm_num
  · apply lt_of_sq' RL_pos.le (by norm_num); rw [RL_sq]; norm_num

/-- **The observer's own rings at one meter** (Sec. II, after Eq. (N); `Reg.observer_rings`): the
fraction `R_Λℓ_c/πr²` of `N_s(r)` that the `L/2` rings through an observer's cell can add is
`1.26×10⁻⁹` at `r = 1 m`, which the paper prints as `1.3×10⁻⁹`. -/
theorem observer_fraction_1m :
    1.255e-9 < RL * lc / (π * 1 ^ 2) ∧ RL * lc / (π * 1 ^ 2) < 1.265e-9 := by
  obtain ⟨hR1, hR2⟩ := RL_tight
  obtain ⟨hl1, hl2⟩ := lc_tight
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hpos := Real.pi_pos
  have hRLp := RL_pos
  have hlcp := lc_pos
  rw [one_pow, mul_one]
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith [mul_lt_mul'' hR1 hl1 (by norm_num) (by norm_num)]
  · rw [div_lt_iff₀ hpos]
    nlinarith [mul_lt_mul'' hR2 hl2 hRLp.le hlcp.le]

/-- The horizon (Appendix A, Sec. IV.C–D): `H_∞ = H₀√Ω_Λ = 1.81×10⁻¹⁸ s⁻¹`,
`Λ = 3H_∞²/c² = 1.09×10⁻⁵² m⁻²`, `R_Λ = c/H_∞ = 1.66×10²⁶ m`, and the horizon's surface gravity
`c²/R_Λ = cH_∞ = 5.4×10⁻¹⁰ m/s²`. -/
theorem horizon_val :
    (1.805e-18 < Hinf ∧ Hinf < 1.815e-18) ∧
    (1.085e-52 < 3 / RL ^ 2 ∧ 3 / RL ^ 2 < 1.095e-52) ∧
    (1.655e26 < RL ∧ RL < 1.665e26) ∧
    (5.35e-10 < c₀ ^ 2 / RL ∧ c₀ ^ 2 / RL < 5.45e-10) ∧
    c₀ ^ 2 / RL = c₀ * Hinf ∧ 3 / RL ^ 2 = 3 * Hinf ^ 2 / c₀ ^ 2 := by
  obtain ⟨h1, h2⟩ := Hinf_tight
  obtain ⟨r1, r2⟩ := RL_tight
  have hH := Hinf_pos
  have hs : c₀ ^ 2 / RL = c₀ * Hinf := by unfold RL; field_simp
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, hs, ?_⟩
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num
  · rw [hs]; nlinarith
  · rw [hs]; nlinarith
  · unfold RL; field_simp

/-! ## `L` from the horizon, and the qubit ceiling (Eqs. (Lcos), (nmax); Appendix A) -/

/-- **`L` from the horizon**, Eq. (Lcos): `L_cos = 4.37×10⁶¹` (`4.4×10⁶¹` to two figures). -/
theorem Lcos_val : 4.365e61 < Lcos ∧ Lcos < 4.375e61 := by
  constructor
  · apply lt_of_sq Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc (4.365e61 : ℝ) ^ 2
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · apply lt_of_sq' Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (4.375e61 : ℝ) ^ 2 := by norm_num

/-- A tighter enclosure of `L_cos`, for the Appendix's products. -/
lemma Lcos_tight : 4.3686e61 < Lcos ∧ Lcos < 4.3687e61 := by
  constructor
  · apply lt_of_sq Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc (4.3686e61 : ℝ) ^ 2
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · apply lt_of_sq' Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (4.3687e61 : ℝ) ^ 2 := by norm_num

/-- `L_cos²` lies between `1.4435·2⁴⁰⁹` and `1.4436·2⁴⁰⁹`. -/
lemma Lcos_sq_bounds : 1.4435 * (2 : ℝ) ^ 409 < Lcos ^ 2 ∧ Lcos ^ 2 < 1.4436 * (2 : ℝ) ^ 409 := by
  rw [Lcos_sq]
  constructor
  · calc 1.4435 * (2 : ℝ) ^ 409
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < 1.4436 * (2 : ℝ) ^ 409 := by norm_num

/-- **`log₂ L_cos = 204.76`** (`204.8` to one decimal): `2⁴⁰⁹⁵¹ < L_cos²⁰⁰ < 2⁴⁰⁹⁵³`, that is,
`204.755 < log₂ L_cos < 204.765`. -/
theorem log2_Lcos : (2 : ℝ) ^ 40951 < Lcos ^ 200 ∧ Lcos ^ 200 < 2 ^ 40953 := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have e : Lcos ^ 200 = (Lcos ^ 2) ^ 100 := by ring
  rw [e]
  constructor
  · calc (2 : ℝ) ^ 40951 < (1.4435 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lcos ^ 2) ^ 100 := by gcongr
  · calc (Lcos ^ 2) ^ 100 < (1.4436 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 40953 := by norm_num

/-- **The ceiling from the horizon**: `2²⁰⁴ < L_cos < 2²⁰⁵`. -/
theorem ceiling_cos : (2 : ℝ) ^ 204 < Lcos ∧ Lcos < 2 ^ 205 := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  constructor
  · apply lt_of_sq Lcos_pos.le (by positivity)
    calc ((2 : ℝ) ^ 204) ^ 2 < 1.4435 * (2 : ℝ) ^ 409 := by norm_num
      _ < _ := h1
  · apply lt_of_sq' Lcos_pos.le (by positivity)
    calc Lcos ^ 2 < 1.4436 * (2 : ℝ) ^ 409 := h2
      _ < ((2 : ℝ) ^ 205) ^ 2 := by norm_num

/-- **`N_max = 204`**, Eq. (nmax): `2^N ≤ L_cos` exactly when `N ≤ 204` (`Capacity.ceiling` gives
`2^N ≤ L` for a random state of `N` qubits, and for every state in which all joint outcomes
occur).  The register's rings are the largest rings, of `L_cos` cells, the ring length of the
de Sitter horizon, whatever mass a horizon holds: a mass at rest inside a horizon shortens that
horizon's circumference, to `L_M = L − 2α/ln 2` cells (Sec. IV.C), not the register's rings
(Sec. IV.A). -/
theorem nmax_cos (N : ℕ) : (2 : ℝ) ^ N ≤ Lcos ↔ N ≤ 204 :=
  Capacity.nmax_iff 204 ceiling_cos.1.le ceiling_cos.2 N

/-- **`203` logical qubits** (Secs. IV.A, VI): `2^(N+1) ≤ L_cos` exactly when `N ≤ 203`, the ceiling
of `Coding.ceiling_line_code` for logical qubits in the surface code (`Coding.surfaceCode_match`, at
every distance); no physical string has more conditional states to hold, with the blocks read in
order (`Coding.card_condStates_le`). -/
theorem logical_ceiling_cos (N : ℕ) : (2 : ℝ) ^ (N + 1) ≤ Lcos ↔ N ≤ 203 := by
  rw [nmax_cos]
  omega

/-- **The softness of the ceiling** (Sec. V, Appendix A): a block of `r` cells resolves the last
qubit's conditional probability and phase to one part in `r`, and `2^(N−1) r ≤ L`
(`Capacity.ceiling_soft`) holds at `L_cos` for `N ≤ 202` when `r = 10`, for `N ≤ 200` when `r = 30`,
and for `N ≤ 199` when `r = 100`, and fails at the next `N` in each case. -/
theorem soft_ceilings :
    ((2 : ℝ) ^ 201 * 10 < Lcos ∧ Lcos < 2 ^ 202 * 10) ∧
    ((2 : ℝ) ^ 199 * 30 < Lcos ∧ Lcos < 2 ^ 200 * 30) ∧
    ((2 : ℝ) ^ 198 * 100 < Lcos ∧ Lcos < 2 ^ 199 * 100) := by
  obtain ⟨h1, h2⟩ := Lcos_tight
  have a1 : (2 : ℝ) ^ 201 * 10 < 4.3686e61 := by norm_num
  have a2 : (4.3687e61 : ℝ) < 2 ^ 202 * 10 := by norm_num
  have b1 : (2 : ℝ) ^ 199 * 30 < 4.3686e61 := by norm_num
  have b2 : (4.3687e61 : ℝ) < 2 ^ 200 * 30 := by norm_num
  have c1 : (2 : ℝ) ^ 198 * 100 < 4.3686e61 := by norm_num
  have c2 : (4.3687e61 : ℝ) < 2 ^ 199 * 100 := by norm_num
  exact ⟨⟨a1.trans h1, h2.trans a2⟩, ⟨b1.trans h1, h2.trans b2⟩, ⟨c1.trans h1, h2.trans c2⟩⟩

/-- **The blocks at the ceiling** (Sec. V, Appendix A): at `N = 204` the `2²⁰³` blocks of the
last string average `L_cos/2²⁰³ = 3.4` cells, certified as `3.35·2²⁰³ < L_cos < 3.45·2²⁰³`. -/
theorem average_block : 3.35 * (2 : ℝ) ^ 203 < Lcos ∧ Lcos < 3.45 * (2 : ℝ) ^ 203 := by
  obtain ⟨h1, h2⟩ := Lcos_tight
  have a1 : 3.35 * (2 : ℝ) ^ 203 < 4.3686e61 := by norm_num
  have a2 : (4.3687e61 : ℝ) < 3.45 * (2 : ℝ) ^ 203 := by norm_num
  exact ⟨a1.trans h1, h2.trans a2⟩

/-- **The missing joint outcomes above the ceiling** (Sec. IV.A, Appendix A): a state of `N`
qubits in which all `2^N` joint outcomes occur cannot be held once `2^N > L`, and at least
`2^N − L` of its outcomes are missing, the fraction `1 − L/2^N`: `0.15` at `N = 205` and `0.58`
at `N = 206` for `L_cos`, certified as `0.149 < 1 − L_cos/2²⁰⁵ < 0.151` and
`0.575 < 1 − L_cos/2²⁰⁶ < 0.5755`. -/
theorem missing_fraction :
    (0.149 < 1 - Lcos / 2 ^ 205 ∧ 1 - Lcos / 2 ^ 205 < 0.151) ∧
    (0.575 < 1 - Lcos / 2 ^ 206 ∧ 1 - Lcos / 2 ^ 206 < 0.5755) := by
  obtain ⟨h1, h2⟩ := Lcos_tight
  have p5 : (0 : ℝ) < 2 ^ 205 := by positivity
  have p6 : (0 : ℝ) < 2 ^ 206 := by positivity
  have u5 : Lcos / 2 ^ 205 < 0.851 := by
    rw [div_lt_iff₀ p5]
    calc Lcos < 4.3687e61 := h2
      _ < 0.851 * 2 ^ 205 := by norm_num
  have l5 : 0.849 < Lcos / 2 ^ 205 := by
    rw [lt_div_iff₀ p5]
    calc (0.849 : ℝ) * 2 ^ 205 < 4.3686e61 := by norm_num
      _ < Lcos := h1
  have u6 : Lcos / 2 ^ 206 < 0.425 := by
    rw [div_lt_iff₀ p6]
    calc Lcos < 4.3687e61 := h2
      _ < 0.425 * 2 ^ 206 := by norm_num
  have l6 : 0.4245 < Lcos / 2 ^ 206 := by
    rw [lt_div_iff₀ p6]
    calc (0.4245 : ℝ) * 2 ^ 206 < 4.3686e61 := by norm_num
      _ < Lcos := h1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- **What a million shots see** (Sec. IV.A: "No sample shows which outcomes are missing, since a
million shots on `205` qubits see at most a million of their `2^205` outcomes, fewer than one in
`10^55`").  A sample of `n` shots shows at most `n` outcomes (`Pairing.sample_outcomes_le`), and
`10⁶/2²⁰⁵ = 1.9×10⁻⁵⁶`, certified as below `10⁻⁵⁵`. -/
theorem shots_fraction : (10 : ℝ) ^ 6 / 2 ^ 205 < 1 / 10 ^ 55 := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num

/-- **The return bound above the ceiling** (Sec. IV.A, Appendix A).  Let `y = L_cos/2²⁰⁵`, the
fraction of the joint outcomes that a state of `205` qubits keeps; at `N = 205 + k` qubits the kept
fraction is `y/2^k`.  Under the Porter–Thomas distribution the lightest fraction `f` of the outcomes
carries the probability `f + (1 − f) ln(1 − f)`, which with `1 − f = y/2^k` is
`1 − (y/2^k)(1 − ln(y/2^k))`, and the overlap of the register's state with the random state is at
most the rest, `(y/2^k)(1 − ln(y/2^k))`.  Certified here: the lightest `15%` carry `1.2%`
(`0.0118 < 1 − y + y ln y < 0.0120`), the lightest `58%` carry `21%`
(`0.2110 < 1 − y/2 + (y/2) ln(y/2) < 0.2120`), and the bounds on the return are `0.988` at `205`,
`0.79` at `206`, `0.54` at `207` and `0.12` at `210` qubits (the values are `0.98807`, `0.78847`,
`0.54146` and `0.12289`).  The logarithm is bounded by six terms of the series of `ln(1 − x)` at
`x = 1 − y` (`Real.abs_log_sub_add_sum_range_le`), with `y` from `Lcos_tight`. -/
theorem porter_thomas_bound :
    (0.0118 < 1 - Lcos / 2 ^ 205 + Lcos / 2 ^ 205 * Real.log (Lcos / 2 ^ 205) ∧
      1 - Lcos / 2 ^ 205 + Lcos / 2 ^ 205 * Real.log (Lcos / 2 ^ 205) < 0.0120) ∧
    (0.2110 < 1 - Lcos / 2 ^ 206 + Lcos / 2 ^ 206 * Real.log (Lcos / 2 ^ 206) ∧
      1 - Lcos / 2 ^ 206 + Lcos / 2 ^ 206 * Real.log (Lcos / 2 ^ 206) < 0.2120) ∧
    (0.9875 < Lcos / 2 ^ 205 * (1 - Real.log (Lcos / 2 ^ 205)) ∧
      Lcos / 2 ^ 205 * (1 - Real.log (Lcos / 2 ^ 205)) < 0.9885) ∧
    (0.785 < Lcos / 2 ^ 206 * (1 - Real.log (Lcos / 2 ^ 206)) ∧
      Lcos / 2 ^ 206 * (1 - Real.log (Lcos / 2 ^ 206)) < 0.795) ∧
    (0.535 < Lcos / 2 ^ 207 * (1 - Real.log (Lcos / 2 ^ 207)) ∧
      Lcos / 2 ^ 207 * (1 - Real.log (Lcos / 2 ^ 207)) < 0.545) ∧
    (0.115 < Lcos / 2 ^ 210 * (1 - Real.log (Lcos / 2 ^ 210)) ∧
      Lcos / 2 ^ 210 * (1 - Real.log (Lcos / 2 ^ 210)) < 0.125) := by
  obtain ⟨hL1, hL2⟩ := Lcos_tight
  have p5 : (0 : ℝ) < 2 ^ 205 := by positivity
  -- the kept fraction at `205` qubits
  have ylo : (0.84955 : ℝ) < Lcos / 2 ^ 205 := by
    rw [lt_div_iff₀ p5]
    calc (0.84955 : ℝ) * 2 ^ 205 < 4.3686e61 := by norm_num
      _ < Lcos := hL1
  have yhi : Lcos / 2 ^ 205 < 0.84958 := by
    rw [div_lt_iff₀ p5]
    calc Lcos < 4.3687e61 := hL2
      _ < 0.84958 * 2 ^ 205 := by norm_num
  set y := Lcos / 2 ^ 205 with hy
  have ypos : 0 < y := by linarith
  -- the other kept fractions are `y/2^k`
  have e6 : Lcos / 2 ^ 206 = y / 2 := by rw [hy, div_div]; norm_num
  have e7 : Lcos / 2 ^ 207 = y / 4 := by rw [hy, div_div]; norm_num
  have e10 : Lcos / 2 ^ 210 = y / 32 := by rw [hy, div_div]; norm_num
  -- `ln y` from the series of `ln(1 − x)` at `x = 1 − y`, six terms, the sum bounded by its
  -- values at the ends of the interval of `x`
  set x := 1 - y with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hxlo : (0.15042 : ℝ) < x := by rw [hx]; linarith
  have hxhi : x < 0.15045 := by rw [hx]; linarith
  have habs : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have hser := Real.abs_log_sub_add_sum_range_le habs 6
  have h1x : 1 - x = y := by rw [hx]; ring
  rw [h1x, abs_of_pos hx0, abs_le] at hser
  have hS_hi : (∑ i ∈ Finset.range 6, x ^ (i + 1) / ((i : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range 6, (0.15045 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) :=
    Finset.sum_le_sum fun i _ =>
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0.le hxhi.le _) (by positivity)
  have hS_lo : (∑ i ∈ Finset.range 6, (0.15042 : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range 6, x ^ (i + 1) / ((i : ℝ) + 1) :=
    Finset.sum_le_sum fun i _ =>
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hxlo.le _) (by positivity)
  have hSb : (∑ i ∈ Finset.range 6, (0.15045 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) < 0.163049 := by
    norm_num [Finset.sum_range_succ]
  have hSa : (0.163012 : ℝ) < ∑ i ∈ Finset.range 6, (0.15042 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
    norm_num [Finset.sum_range_succ]
  have herr : x ^ (6 + 1) / (1 - x) < 2.1e-6 := by
    rw [div_lt_iff₀ (by linarith)]
    have h7 : x ^ (6 + 1) < 1.75e-6 := by
      calc x ^ (6 + 1) < (0.15045 : ℝ) ^ (6 + 1) := pow_lt_pow_left₀ hxhi hx0.le (by norm_num)
        _ < 1.75e-6 := by norm_num
    linarith
  have llo : -0.16306 < Real.log y := by linarith [hser.1, hS_hi, hSb, herr]
  have lhi : Real.log y < -0.16300 := by linarith [hser.2, hS_lo, hSa, herr]
  -- the logarithms of the other fractions
  have l6 : Real.log (y / 2) = Real.log y - Real.log 2 := Real.log_div ypos.ne' two_ne_zero
  have l7 : Real.log (y / 4) = Real.log y - 2 * Real.log 2 := by
    rw [Real.log_div ypos.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have l10 : Real.log (y / 32) = Real.log y - 5 * Real.log 2 := by
    rw [Real.log_div ypos.ne' (by norm_num), show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have ln2lo := Real.log_two_gt_d9
  have ln2hi := Real.log_two_lt_d9
  -- products of the bounded quantities
  have m1 := mul_nonneg (sub_pos.2 ylo).le (sub_pos.2 llo).le
  have m2 := mul_nonneg (sub_pos.2 ylo).le (sub_pos.2 lhi).le
  have m3 := mul_nonneg (sub_pos.2 yhi).le (sub_pos.2 llo).le
  have m4 := mul_nonneg (sub_pos.2 yhi).le (sub_pos.2 lhi).le
  have n1 := mul_nonneg (sub_pos.2 ylo).le (sub_pos.2 ln2lo).le
  have n2 := mul_nonneg (sub_pos.2 ylo).le (sub_pos.2 ln2hi).le
  have n3 := mul_nonneg (sub_pos.2 yhi).le (sub_pos.2 ln2lo).le
  have n4 := mul_nonneg (sub_pos.2 yhi).le (sub_pos.2 ln2hi).le
  rw [e6, e7, e10, l6, l7, l10]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-! ### The robustness of the ceiling (Appendix A) -/

/-- **The margins of the ceiling** (Appendix A): `2²⁰⁴` and `2²⁰⁵` lie at `0.59` and `1.18` of
`L_cos`, certified as `0.585 L_cos < 2²⁰⁴ < 0.595 L_cos` and `1.175 L_cos < 2²⁰⁵ < 1.18 L_cos`
(the values are `0.5885` and `1.1771`). -/
theorem ceiling_margins :
    (0.585 * Lcos < 2 ^ 204 ∧ (2 : ℝ) ^ 204 < 0.595 * Lcos) ∧
    (1.175 * Lcos < 2 ^ 205 ∧ (2 : ℝ) ^ 205 < 1.18 * Lcos) := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have hL := Lcos_pos
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply lt_of_sq (by positivity) (by positivity)
    calc (0.585 * Lcos) ^ 2 = 0.585 ^ 2 * Lcos ^ 2 := by ring
      _ < 0.585 ^ 2 * (1.4436 * (2 : ℝ) ^ 409) := by gcongr
      _ < ((2 : ℝ) ^ 204) ^ 2 := by norm_num
  · apply lt_of_sq (by positivity) (by positivity)
    calc ((2 : ℝ) ^ 204) ^ 2 < 0.595 ^ 2 * (1.4435 * (2 : ℝ) ^ 409) := by norm_num
      _ < 0.595 ^ 2 * Lcos ^ 2 := by gcongr
      _ = (0.595 * Lcos) ^ 2 := by ring
  · apply lt_of_sq (by positivity) (by positivity)
    calc (1.175 * Lcos) ^ 2 = 1.175 ^ 2 * Lcos ^ 2 := by ring
      _ < 1.175 ^ 2 * (1.4436 * (2 : ℝ) ^ 409) := by gcongr
      _ < ((2 : ℝ) ^ 205) ^ 2 := by norm_num
  · apply lt_of_sq (by positivity) (by positivity)
    calc ((2 : ℝ) ^ 205) ^ 2 < 1.18 ^ 2 * (1.4435 * (2 : ℝ) ^ 409) := by norm_num
      _ < 1.18 ^ 2 * Lcos ^ 2 := by gcongr
      _ = (1.18 * Lcos) ^ 2 := by ring

/-- **The ceiling across the entropy per ring** (Sec. V, Appendix A).  With `s` bits of entropy
per ring in place of one, Eq. (cell) carries `s ln 2`, `ℓ_c = √(πs ln 2) ℓ_P` and `L = L_cos/√s`,
so `2²⁰⁴ ≤ L < 2²⁰⁵` exactly when `(L_cos/2²⁰⁵)² < s ≤ (L_cos/2²⁰⁴)²`; the two bounds are `0.7218`
and `2.887`, certified as `0.72175 < (L_cos/2²⁰⁵)² < 0.7218` and `2.8869 < (L_cos/2²⁰⁴)² < 2.8872`.
One bit (`s = 1`), one nat (`s = 1/ln 2 = 1.44`) and two bits all give `204`. -/
theorem ceiling_entropy_range :
    (0.72175 < (Lcos / 2 ^ 205) ^ 2 ∧ (Lcos / 2 ^ 205) ^ 2 < 0.7218) ∧
    (2.8869 < (Lcos / 2 ^ 204) ^ 2 ∧ (Lcos / 2 ^ 204) ^ 2 < 2.8872) ∧
    ∀ s : ℝ, 0 < s →
      (((2 : ℝ) ^ 204 ≤ Lcos / Real.sqrt s ↔ s ≤ (Lcos / 2 ^ 204) ^ 2) ∧
       (Lcos / Real.sqrt s < 2 ^ 205 ↔ (Lcos / 2 ^ 205) ^ 2 < s)) := by
  obtain ⟨t1, t2⟩ := Lcos_tight
  have hL := Lcos_pos
  have q1 : (4.3686e61 : ℝ) ^ 2 < Lcos ^ 2 := pow_lt_pow_left₀ t1 (by norm_num) (by norm_num)
  have q2 : Lcos ^ 2 < (4.3687e61 : ℝ) ^ 2 := pow_lt_pow_left₀ t2 hL.le (by norm_num)
  obtain ⟨s1, -⟩ := Lcos_sq_bounds
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [div_pow, lt_div_iff₀ (by positivity)]
    calc (0.72175 : ℝ) * ((2 : ℝ) ^ 205) ^ 2 = 1.4435 * (2 : ℝ) ^ 409 := by norm_num
      _ < Lcos ^ 2 := s1
  · rw [div_pow, div_lt_iff₀ (by positivity)]
    calc Lcos ^ 2 < (4.3687e61 : ℝ) ^ 2 := q2
      _ < 0.7218 * ((2 : ℝ) ^ 205) ^ 2 := by norm_num
  · rw [div_pow, lt_div_iff₀ (by positivity)]
    calc (2.8869 : ℝ) * ((2 : ℝ) ^ 204) ^ 2 < (4.3686e61 : ℝ) ^ 2 := by norm_num
      _ < Lcos ^ 2 := q1
  · rw [div_pow, div_lt_iff₀ (by positivity)]
    calc Lcos ^ 2 < (4.3687e61 : ℝ) ^ 2 := q2
      _ < 2.8872 * ((2 : ℝ) ^ 204) ^ 2 := by norm_num
  · intro s hs
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    constructor
    · have key : (2 : ℝ) ^ 204 * Real.sqrt s ≤ Lcos ↔
          ((2 : ℝ) ^ 204 * Real.sqrt s) ^ 2 ≤ Lcos ^ 2 :=
        (pow_le_pow_iff_left₀ (by positivity) hL.le two_ne_zero).symm
      rw [le_div_iff₀ hsq, key, mul_pow, Real.sq_sqrt hs.le, div_pow,
        le_div_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    · have key : Lcos < (2 : ℝ) ^ 205 * Real.sqrt s ↔
          Lcos ^ 2 < ((2 : ℝ) ^ 205 * Real.sqrt s) ^ 2 :=
        (pow_lt_pow_iff_left₀ hL.le (by positivity) two_ne_zero).symm
      rw [div_lt_iff₀ hsq, key, mul_pow, Real.sq_sqrt hs.le, div_pow,
        div_lt_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith

/-- `L` from the horizon for a Hubble rate `H` and a dark-energy fraction `Ω`: `2πR_Λ/ℓ_c` with
`R_Λ = c/(H√Ω)`. `Lof H₀ ΩΛ₀` is `L_cos`. -/
noncomputable def Lof (H Ω : ℝ) : ℝ := 2 * π * (c₀ / (H * Real.sqrt Ω)) / lc

lemma Lof_sq (H Ω : ℝ) (hH : H ≠ 0) (hΩ : 0 < Ω) :
    Lof H Ω ^ 2 = π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) := by
  pi_ln2
  have hsq : Real.sqrt Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  have hsqrt : Real.sqrt Ω ≠ 0 := (Real.sqrt_pos.2 hΩ).ne'
  unfold Lof
  rw [div_pow, mul_pow, mul_pow, div_pow, mul_pow, hsq, lc_sq]
  field_simp
  ring

lemma Lof_sq_73 :
    1.2305 * (2 : ℝ) ^ 409 < Lof (73000 / Mpc₀) ΩΛ₀ ^ 2 ∧
    Lof (73000 / Mpc₀) ΩΛ₀ ^ 2 < 1.2306 * (2 : ℝ) ^ 409 := by
  rw [Lof_sq _ _ (by norm_num) (by norm_num)]
  constructor
  · calc 1.2305 * (2 : ℝ) ^ 409
        < (3.141592 / 0.6931471808) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < 1.2306 * (2 : ℝ) ^ 409 := by norm_num

/-- **`log₂ L = 204.65` at the local `H₀ = 73 km/s/Mpc`** (Appendix A): `2⁴⁰⁹²⁹ < L²⁰⁰ < 2⁴⁰⁹³¹`,
that is, `204.645 < log₂ L < 204.655`; the ceiling is `204` at this `H₀` too. -/
theorem log2_L73 :
    (2 : ℝ) ^ 40929 < Lof (73000 / Mpc₀) ΩΛ₀ ^ 200 ∧
    Lof (73000 / Mpc₀) ΩΛ₀ ^ 200 < 2 ^ 40931 := by
  obtain ⟨h1, h2⟩ := Lof_sq_73
  have e : Lof (73000 / Mpc₀) ΩΛ₀ ^ 200 = (Lof (73000 / Mpc₀) ΩΛ₀ ^ 2) ^ 100 := by ring
  rw [e]
  constructor
  · calc (2 : ℝ) ^ 40929 < (1.2305 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lof (73000 / Mpc₀) ΩΛ₀ ^ 2) ^ 100 := by gcongr
  · calc (Lof (73000 / Mpc₀) ΩΛ₀ ^ 2) ^ 100 < (1.2306 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 40931 := by norm_num

/-- the least `L_cos` over the box of Planck's `H₀ = 67.4 ± 0.5 km/s/Mpc` and `Ω_Λ = 0.685 ± 0.007`,
its value at the corner of the largest `H₀` and `Ω_Λ` (`Lof_box`) -/
noncomputable def LcosMin : ℝ := Lof (67900 / Mpc₀) 0.692

/-- the greatest `L_cos` over the same box, its value at the corner of the least `H₀` and `Ω_Λ`
(`Lof_box`) -/
noncomputable def LcosMax : ℝ := Lof (66900 / Mpc₀) 0.678

lemma LcosMin_sq : LcosMin ^ 2 < 1.408 * (2 : ℝ) ^ 409 := by
  unfold LcosMin
  rw [Lof_sq _ _ (by norm_num) (by norm_num)]
  calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((67900 / Mpc₀) ^ 2 * 0.692)))
      < (3.141593 / 0.6931471803) *
          (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((67900 / Mpc₀) ^ 2 * 0.692))) :=
        mul_lt_mul_of_pos_right pq_hi (by norm_num)
    _ < 1.408 * (2 : ℝ) ^ 409 := by norm_num

lemma LcosMax_sq : 1.4803 * (2 : ℝ) ^ 409 < LcosMax ^ 2 := by
  unfold LcosMax
  rw [Lof_sq _ _ (by norm_num) (by norm_num)]
  calc 1.4803 * (2 : ℝ) ^ 409
      < (3.141592 / 0.6931471808) *
          (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((66900 / Mpc₀) ^ 2 * 0.678))) := by norm_num
    _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((66900 / Mpc₀) ^ 2 * 0.678))) :=
        mul_lt_mul_of_pos_right pq_lo (by norm_num)

/-- **Planck's uncertainties move `log₂ L_cos` by about `±0.02`** (Appendix A): for `H₀` within
`±0.5 km/s/Mpc` of `67.4` and `Ω_Λ` within `±0.007` of `0.685`, `2⁴⁰⁹⁴⁹ < L²⁰⁰ < 2⁴⁰⁹⁵⁷`, that is,
`204.745 < log₂ L < 204.785`, against `log₂ L_cos = 204.76` (`log2_Lcos`); the ceiling is `204`
throughout the band.  Against `L_cos` itself, `L²⁰⁰` stays within a factor `2⁴` of `L_cos²⁰⁰` over
the band, a shift below `0.02`, and at the two corners of the band it differs from `L_cos²⁰⁰` by
more than a factor `2³`, a shift above `0.015` (the two shifts are `+0.018` and `−0.018`). -/
theorem log2_planck_band (H Ω : ℝ) (hH1 : 66900 / Mpc₀ ≤ H) (hH2 : H ≤ 67900 / Mpc₀)
    (hΩ1 : 0.678 ≤ Ω) (hΩ2 : Ω ≤ 0.692) :
    ((2 : ℝ) ^ 40949 < Lof H Ω ^ 200 ∧ Lof H Ω ^ 200 < 2 ^ 40957) ∧
    (Lcos ^ 200 < 2 ^ 4 * Lof H Ω ^ 200 ∧ Lof H Ω ^ 200 < 2 ^ 4 * Lcos ^ 200) ∧
    2 ^ 3 * Lcos ^ 200 < Lof (66900 / Mpc₀) 0.678 ^ 200 ∧
    2 ^ 3 * Lof (67900 / Mpc₀) 0.692 ^ 200 < Lcos ^ 200 := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH1
  have hΩpos : 0 < Ω := lt_of_lt_of_le (by norm_num) hΩ1
  have hsq := Lof_sq H Ω hHpos.ne' hΩpos
  have hlo : (66900 / Mpc₀) ^ 2 * 0.678 ≤ H ^ 2 * Ω :=
    mul_le_mul (pow_le_pow_left₀ (by norm_num) hH1 2) hΩ1 (by norm_num) (by positivity)
  have hhi : H ^ 2 * Ω ≤ (67900 / Mpc₀) ^ 2 * 0.692 :=
    mul_le_mul (pow_le_pow_left₀ hHpos.le hH2 2) hΩ2 hΩpos.le (by positivity)
  have hpos : 0 < H ^ 2 * Ω := by positivity
  have hL2lo : 1.4079 * (2 : ℝ) ^ 409 < Lof H Ω ^ 2 := by
    rw [hsq]
    calc 1.4079 * (2 : ℝ) ^ 409
        < (3.141592 / 0.6931471808) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((67900 / Mpc₀) ^ 2 * 0.692))) := by norm_num
      _ ≤ (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) := by
          gcongr
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) :=
          mul_lt_mul_of_pos_right pq_lo (by positivity)
  have hL2hi : Lof H Ω ^ 2 < 1.4805 * (2 : ℝ) ^ 409 := by
    rw [hsq]
    calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) :=
          mul_lt_mul_of_pos_right pq_hi (by positivity)
      _ ≤ (3.141593 / 0.6931471803) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((66900 / Mpc₀) ^ 2 * 0.678))) := by
          gcongr
      _ < 1.4805 * (2 : ℝ) ^ 409 := by norm_num
  have e : Lof H Ω ^ 200 = (Lof H Ω ^ 2) ^ 100 := by ring
  have ec : Lcos ^ 200 = (Lcos ^ 2) ^ 100 := by ring
  have eA : Lof (66900 / Mpc₀) 0.678 ^ 200 = (Lof (66900 / Mpc₀) 0.678 ^ 2) ^ 100 := by ring
  have eB : Lof (67900 / Mpc₀) 0.692 ^ 200 = (Lof (67900 / Mpc₀) 0.692 ^ 2) ^ 100 := by ring
  obtain ⟨c1, c2⟩ := Lcos_sq_bounds
  -- the two corners of the band
  have hA : 1.4803 * (2 : ℝ) ^ 409 < Lof (66900 / Mpc₀) 0.678 ^ 2 := LcosMax_sq
  have hB : Lof (67900 / Mpc₀) 0.692 ^ 2 < 1.408 * (2 : ℝ) ^ 409 := LcosMin_sq
  rw [e, ec, eA, eB]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · calc (2 : ℝ) ^ 40949 < (1.4079 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lof H Ω ^ 2) ^ 100 := by gcongr
  · calc (Lof H Ω ^ 2) ^ 100 < (1.4805 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 40957 := by norm_num
  · calc (Lcos ^ 2) ^ 100 < (1.4436 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 4 * (1.4079 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < 2 ^ 4 * (Lof H Ω ^ 2) ^ 100 := by gcongr
  · calc (Lof H Ω ^ 2) ^ 100 < (1.4805 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 4 * (1.4435 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < 2 ^ 4 * (Lcos ^ 2) ^ 100 := by gcongr
  · calc 2 ^ 3 * (Lcos ^ 2) ^ 100 < 2 ^ 3 * (1.4436 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < (1.4803 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lof (66900 / Mpc₀) 0.678 ^ 2) ^ 100 := by gcongr
  · calc 2 ^ 3 * (Lof (67900 / Mpc₀) 0.692 ^ 2) ^ 100
        < 2 ^ 3 * (1.408 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < (1.4435 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lcos ^ 2) ^ 100 := by gcongr

/-- **`L_cos` over Planck's box lies between its values at two corners** (Appendix A): for `H₀`
within `±0.5 km/s/Mpc` of `67.4` and `Ω_Λ` within `±0.007` of `0.685`, `L_cos = 2πc/(H₀√Ω_Λ ℓ_c)`
falls as either grows, so it is least at the corner of the largest `H₀` and `Ω_Λ` (`LcosMin`) and
greatest at the corner of the least (`LcosMax`). -/
theorem Lof_box (H Ω : ℝ) (hH1 : 66900 / Mpc₀ ≤ H) (hH2 : H ≤ 67900 / Mpc₀)
    (hΩ1 : 0.678 ≤ Ω) (hΩ2 : Ω ≤ 0.692) : LcosMin ≤ Lof H Ω ∧ Lof H Ω ≤ LcosMax := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH1
  have hΩpos : 0 < Ω := lt_of_lt_of_le (by norm_num) hΩ1
  have := lc_pos
  unfold LcosMin LcosMax Lof
  constructor
  · gcongr
  · gcongr

/-- **A register's `L` in Planck's band** (Sec. II, Appendix A): `52289` is prime, so
`L = 2(52289¹³ + 1)`, which is `4.36882 × 10⁶¹`, has `L/2 − 1` a prime power; and it lies strictly
between `LcosMin` and `LcosMax`, the least and the greatest `L_cos` over Planck's box (`Lof_box`):
`L²` is `1.4436 × 2⁴⁰⁹`, between `1.408 × 2⁴⁰⁹` and `1.4803 × 2⁴⁰⁹`. -/
theorem witness_in_band :
    Nat.Prime 52289 ∧ LcosMin < ((2 * (52289 ^ 13 + 1) : ℕ) : ℝ) ∧
      ((2 * (52289 ^ 13 + 1) : ℕ) : ℝ) < LcosMax := by
  have h1 : 1.408 * (2 : ℝ) ^ 409 < ((2 * (52289 ^ 13 + 1) : ℕ) : ℝ) ^ 2 := by norm_num
  have h2 : ((2 * (52289 ^ 13 + 1) : ℕ) : ℝ) ^ 2 < 1.4803 * (2 : ℝ) ^ 409 := by norm_num
  have hmin : 0 ≤ LcosMin := by unfold LcosMin Lof; have := lc_pos; positivity
  have hmax : 0 ≤ LcosMax := by unfold LcosMax Lof; have := lc_pos; positivity
  exact ⟨by norm_num, lt_of_sq' hmin (Nat.cast_nonneg _) (LcosMin_sq.trans h1),
    lt_of_sq hmax (Nat.cast_nonneg _) (h2.trans LcosMax_sq)⟩

/-- Powers of two: `2²⁰⁴ = 2.57×10⁶¹` and `2²⁰⁵ = 5.14×10⁶¹` (Appendix A); `2²¹² = 6.58×10⁶³` and
`2²¹³ = 1.32×10⁶⁴`, which the paper does not print, bracket `10⁶⁴` and enter Palmer's bit count
(`palmer_211`, `palmer_range`). -/
theorem powers_of_two :
    ((2.565e61 : ℝ) < 2 ^ 204 ∧ (2 : ℝ) ^ 204 < 2.575e61) ∧
    ((5.135e61 : ℝ) < 2 ^ 205 ∧ (2 : ℝ) ^ 205 < 5.145e61) ∧
    ((6.575e63 : ℝ) < 2 ^ 212 ∧ (2 : ℝ) ^ 212 < 6.585e63) ∧
    ((1.315e64 : ℝ) < 2 ^ 213 ∧ (2 : ℝ) ^ 213 < 1.325e64) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩⟩

/-- **Palmer's bit count** `2^(N+1) − 2 ≤ NL` (Sec. V, which prints the `211` only): with `L_cos`
it holds at `N = 211`, `2²¹² ≤ 211L_cos = 9.22×10⁶³`, and fails at `N = 212`,
`2²¹³ > 212L_cos = 9.26×10⁶³`; so it holds exactly for `N ≤ 211` (`Capacity.palmer_threshold`). -/
theorem palmer_211 :
    ((2 : ℝ) ^ 212 - 2 ≤ 211 * Lcos ∧ 212 * Lcos < 2 ^ 213 - 2) ∧
    (9.215e63 < 211 * Lcos ∧ 211 * Lcos < 9.225e63) ∧
    (9.255e63 < 212 * Lcos ∧ 212 * Lcos < 9.265e63) ∧
    ∀ N : ℕ, (2 : ℝ) ^ (N + 1) - 2 ≤ N * Lcos ↔ N ≤ 211 := by
  obtain ⟨h1, h2⟩ := Lcos_tight
  have hyes : (2 : ℝ) ^ 212 - 2 ≤ 211 * Lcos := by
    have : (2 : ℝ) ^ 212 - 2 ≤ 211 * 4.3686e61 := by norm_num
    linarith
  have hno : 212 * Lcos < (2 : ℝ) ^ 213 - 2 := by
    have : 212 * 4.3687e61 < (2 : ℝ) ^ 213 - 2 := by norm_num
    linarith
  refine ⟨⟨hyes, hno⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  intro N
  refine Capacity.palmer_threshold Lcos Lcos_pos 211 (by norm_num) ?_ ?_ N
  · push_cast; exact hyes
  · push_cast; norm_num; linarith

/-- **Palmer's range of `L`** (Sec. V): by `2^N ≤ L` the ceiling `⌊log₂ L⌋` is `212` for a
quantum-dot electron with `L = 10⁶⁴` and `362` for a hyperfine ion-trap qubit with `L = 10¹⁰⁹`;
and `L_cos` lies below the smaller. -/
theorem palmer_range :
    ((2 : ℝ) ^ 212 < 10 ^ 64 ∧ (10 : ℝ) ^ 64 < 2 ^ 213) ∧
    ((2 : ℝ) ^ 362 < 10 ^ 109 ∧ (10 : ℝ) ^ 109 < 2 ^ 363) ∧ Lcos < 10 ^ 64 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  have := Lcos_val.2
  linarith [show (4.375e61 : ℝ) < 10 ^ 64 by norm_num]

/-! ## The horizon's counts, and Davies (Sec. II, Sec. V, Appendix A) -/

/-- **The horizon's counts**, Eq. (counts) to leading order: `L²/2 = 9.5×10¹²²` cells,
`L²/4 = 4.8×10¹²²` rings, and the entropy `(L²/4) ln 2 = 3.3×10¹²²`, which equals `πR_Λ²/ℓ_P²`. -/
theorem horizon_counts :
    (9.45e122 < Lcos ^ 2 / 2 ∧ Lcos ^ 2 / 2 < 9.55e122) ∧
    (4.75e122 < Lcos ^ 2 / 4 ∧ Lcos ^ 2 / 4 < 4.85e122) ∧
    (3.25e122 < Lcos ^ 2 / 4 * Real.log 2 ∧ Lcos ^ 2 / 4 * Real.log 2 < 3.35e122) ∧
    Lcos ^ 2 / 4 * Real.log 2 = π * RL ^ 2 / lP ^ 2 := by
  pi_ln2
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have e : Lcos ^ 2 / 4 * Real.log 2 = π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [Lcos_sq]; field_simp
  have e2 : π * RL ^ 2 / lP ^ 2 = π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [RL_sq, lP_sq]; field_simp
  have b1 : (1.4435 * (2 : ℝ) ^ 409) / 2 > 9.45e122 := by norm_num
  have b2 : (1.4436 * (2 : ℝ) ^ 409) / 2 < 9.55e122 := by norm_num
  have b3 : (1.4435 * (2 : ℝ) ^ 409) / 4 > 4.75e122 := by norm_num
  have b4 : (1.4436 * (2 : ℝ) ^ 409) / 4 < 4.85e122 := by norm_num
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, by rw [e, e2]⟩
  · rw [e]
    calc (3.25e122 : ℝ) < 3.141592 * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right Real.pi_gt_d6 (by norm_num)
  · rw [e]
    calc π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < 3.141593 * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right Real.pi_lt_d6 (by norm_num)
      _ < (3.35e122 : ℝ) := by norm_num

/-- The chain's entropy for these inputs is the same number: `(L²/4) ln 2 = πR_Λ²/ℓ_P²`
(`Reg.entropy_quarter`). -/
theorem reg_entropy : reg.Shor = Lcos ^ 2 / 4 * Real.log 2 := by
  simp only [Reg.Shor, Reg.Rhor, reg, Reg.ln2_def]

/-- **Davies** (Sec. V): Davies' `10¹²²` bits have `log₂ 10¹²² = 405`
(`2⁸¹⁰ < 10²⁴⁴ < 2⁸¹¹`, that is, `405 < log₂ 10¹²² < 405.5`), and the logarithm of the horizon's
`L²/4` rings, which the paper takes to be the `N ≈ 400` that Palmer quotes, is
`2 log₂ L − 2 = 407.5`: `2⁸¹⁴⁹ < (L²/4)²⁰ < 2⁸¹⁵¹`, that is,
`407.45 < log₂(L²/4) < 407.55`. -/
theorem davies :
    ((2 : ℝ) ^ 810 < 10 ^ 244 ∧ (10 : ℝ) ^ 244 < 2 ^ 811) ∧
    ((2 : ℝ) ^ 8149 < (Lcos ^ 2 / 4) ^ 20 ∧ (Lcos ^ 2 / 4) ^ 20 < 2 ^ 8151) := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · calc (2 : ℝ) ^ 8149 < (1.4435 * (2 : ℝ) ^ 409 / 4) ^ 20 := by norm_num
      _ < (Lcos ^ 2 / 4) ^ 20 := by gcongr
  · calc (Lcos ^ 2 / 4) ^ 20 < (1.4436 * (2 : ℝ) ^ 409 / 4) ^ 20 := by gcongr
      _ < 2 ^ 8151 := by norm_num

/-! ## The bit's history (Sec. II and Appendix A; the paper's versions -6-26 to -6-33 did not print
these figures, and since -6-35 the time is that of the bath's scatterings)

New inputs: `1 MeV = 1.602176634×10⁻¹³ J` (the SI elementary charge, exact) and the fine-structure
constant `α_e = 7.2973525643×10⁻³` (CODATA 2022), for `scatter_1MeV`. -/

local notation "MeV₀" => ((1602176634 : ℝ) / 10 ^ 22)
local notation "α₀" => ((72973525643 : ℝ) / 10 ^ 13)

/-- **The strings of a horizon in scattering times** (Sec. II, "The bit's history", and Appendix A;
the paper's versions -6-26 to -6-33 did not print these figures):
`ln N = ln(L_cos²/4)` lies between `281.5` and `282.5`, so about `282` scattering times bring all
`N = L²/4` strings of a horizon to equilibrium. -/
theorem lnN_val : 281.5 < Real.log (Lcos ^ 2 / 4) ∧ Real.log (Lcos ^ 2 / 4) < 282.5 := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have e : ∀ a : ℝ, 0 < a → Real.log (a * (2 : ℝ) ^ 407) = Real.log a + 407 * Real.log 2 := by
    intro a ha
    rw [Real.log_mul ha.ne' (by positivity), Real.log_pow]
    norm_num
  have lo : 1.4435 * (2 : ℝ) ^ 407 < Lcos ^ 2 / 4 := by
    rw [lt_div_iff₀ (by norm_num)]
    calc 1.4435 * (2 : ℝ) ^ 407 * 4 = 1.4435 * (2 : ℝ) ^ 409 := by norm_num
      _ < Lcos ^ 2 := h1
  have hi : Lcos ^ 2 / 4 < 1.4436 * (2 : ℝ) ^ 407 := by
    rw [div_lt_iff₀ (by norm_num)]
    calc Lcos ^ 2 < 1.4436 * (2 : ℝ) ^ 409 := h2
      _ = 1.4436 * (2 : ℝ) ^ 407 * 4 := by norm_num
  have a1 : (1 : ℝ) - (1.4435 : ℝ)⁻¹ ≤ Real.log 1.4435 :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have a1' : (0.307 : ℝ) < 1 - (1.4435 : ℝ)⁻¹ := by norm_num
  have a2 : Real.log 1.4436 < 0.38 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.38 by norm_num)
    have h3 : (1.4436 : ℝ) < 1 + 0.38 + 0.38 ^ 2 / 2 := by norm_num
    linarith
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  constructor
  · have := Real.log_lt_log (by positivity) lo
    rw [e 1.4435 (by norm_num)] at this
    linarith
  · have hpos : 0 < Lcos ^ 2 / 4 := by have := Lcos_pos; positivity
    have := Real.log_lt_log hpos hi
    rw [e 1.4436 (by norm_num)] at this
    linarith

/-- **Equilibrium by the first second** (Sec. II, "The bit's history", and Appendix A): in the bath
of the early universe, photons and charged particles scatter about once per `ℏ/α²k_BT`, and `ln N`
such times at `k_BT = 1 MeV` take `3.5×10⁻¹⁵ s` (between `3.45` and `3.55×10⁻¹⁵ s`).  Since -6-35 the
paper prints this figure in place of the `2×10⁻¹⁹ s` of `ln N` thermal times `ℏ/k_BT`. -/
theorem scatter_1MeV :
    3.45e-15 < Real.log (Lcos ^ 2 / 4) * (ℏ₀ / (α₀ ^ 2 * MeV₀)) ∧
      Real.log (Lcos ^ 2 / 4) * (ℏ₀ / (α₀ ^ 2 * MeV₀)) < 3.55e-15 := by
  obtain ⟨h1, h2⟩ := lnN_val
  have hτ : (0 : ℝ) < ℏ₀ / (α₀ ^ 2 * MeV₀) := by norm_num
  constructor
  · calc (3.45e-15 : ℝ) < 281.5 * (ℏ₀ / (α₀ ^ 2 * MeV₀)) := by norm_num
      _ < Real.log (Lcos ^ 2 / 4) * (ℏ₀ / (α₀ ^ 2 * MeV₀)) := mul_lt_mul_of_pos_right h1 hτ
  · calc Real.log (Lcos ^ 2 / 4) * (ℏ₀ / (α₀ ^ 2 * MeV₀))
        < 282.5 * (ℏ₀ / (α₀ ^ 2 * MeV₀)) := mul_lt_mul_of_pos_right h2 hτ
      _ < 3.55e-15 := by norm_num

/-! ## Newton's constant from the ceiling (Sec. V, Prediction 2, Appendix A) -/

/-- **The bracket**: Eq. (G) with `L = 2²⁰⁴` and `2²⁰⁵` gives `1.93×10⁻¹⁰` and `4.82×10⁻¹¹`
(`1.9×10⁻¹⁰` and `4.8×10⁻¹¹` to two figures), and the measured `G` lies strictly between them:
not in the bracket of a ceiling of `205`, `[G(2²⁰⁶), G(2²⁰⁵)]`, which every higher ceiling's
bracket lies below, nor in that of `203`, `[G(2²⁰⁴), G(2²⁰³)]`. -/
theorem G_bracket :
    (1.925e-10 < Gof (2 ^ 204) ∧ Gof (2 ^ 204) < 1.935e-10) ∧
    (4.815e-11 < Gof (2 ^ 205) ∧ Gof (2 ^ 205) < 4.825e-11) ∧
    (Gof (2 ^ 205) < G₀ ∧ G₀ < Gof (2 ^ 204)) := by
  rw [Gof_eq, Gof_eq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · calc (1.925e-10 : ℝ)
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 204) ^ 2)) := by
          norm_num
      _ < _ := mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc _ < (3.141593 / 0.6931471803) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 204) ^ 2)) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (1.935e-10 : ℝ) := by norm_num
  · calc (4.815e-11 : ℝ)
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 205) ^ 2)) := by
          norm_num
      _ < _ := mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc _ < (3.141593 / 0.6931471803) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 205) ^ 2)) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (4.825e-11 : ℝ) := by norm_num
  · calc _ < (3.141593 / 0.6931471803) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 205) ^ 2)) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < G₀ := by norm_num
  · calc G₀ < (3.141592 / 0.6931471808) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 204) ^ 2)) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right pq_lo (by norm_num)

/-- **A factor of two in `L` is a factor of four in `G`** (Sec. V): `G(2^N) = 4G(2^(N+1))`, so a
measured ceiling at which the bound is itself reached, `2^N ≤ L < 2^(N+1)`, returns `ℓ_c = 2πR_Λ/L` to
a factor of two and `G` to a factor of four (Sec. V and Prediction 2, which ask that the shortfall
above the ceiling be larger than the error of the experiment). -/
theorem Gof_factor_four (N : ℕ) : Gof (2 ^ N) = 4 * Gof (2 ^ (N + 1)) := by
  rw [Gof_eq, Gof_eq, pow_succ]
  field_simp
  ring

/-- **`G` falls as `L` grows**: Eq. (G) goes as `1/L²`, so for `0 < L₁ ≤ L₂`, `G(L₂) ≤ G(L₁)`. -/
theorem Gof_antitone {L₁ L₂ : ℝ} (h1 : 0 < L₁) (h12 : L₁ ≤ L₂) : Gof L₂ ≤ Gof L₁ := by
  pi_ln2
  unfold Gof
  have hR := RL_pos
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : L₁ ^ 2 ≤ L₂ ^ 2 := pow_le_pow_left₀ h1.le h12 2
  have hℏ : (0 : ℝ) < ℏ₀ := by norm_num
  nlinarith [this, hℏ, Real.log_pos one_lt_two]

/-- **A measured ceiling of `205` or more contradicts Eq. (G)** (Sec. V, Prediction 2): for every
`N ≥ 205`, `G(2^N) ≤ G(2²⁰⁵) < G₀`.  A measured ceiling `N`, with a shortfall above it larger than the
error of the experiment, gives `2^N ≤ L` and so, through Eq. (G), `G ≤ G(2^N)`, which for `N ≥ 205`
lies below the measured `G`. -/
theorem ceiling_above_204 (N : ℕ) (hN : 205 ≤ N) : Gof (2 ^ N) < G₀ := by
  have h205 : Gof (2 ^ 205) < G₀ := G_bracket.2.2.1
  have hle : Gof (2 ^ N) ≤ Gof (2 ^ 205) :=
    Gof_antitone (by positivity) (pow_le_pow_right₀ (by norm_num) hN)
  exact lt_of_le_of_lt hle h205

/-! ## The solar scale (Sec. IV.B–C, Table I, Appendix A) -/

/-- The chain's `α` for the Sun, its mass in cell masses `M☉/m_c` with `M☉ = GM☉/G`, is `αs`. -/
theorem reg_αs : reg.α (GMs₀ / G₀) = αs := by
  have := lc_pos
  simp only [Reg.α, Reg.mc, reg]
  unfold αs
  field_simp

/-- **The Sun** (Sec. IV.B, Table I, Appendix A): `α = M☉/m_c = 1.35×10³⁸`; the horizon is drawn
in by `GM☉/c²ℓ_c = α/(π ln 2) = 6.19×10³⁷` cells (`Reg.shift_in_cells`); the entropy the Sun
removes is `Lα = 5.9×10⁹⁹`.  For a galaxy of `10¹¹ M☉` it is `5.9×10¹¹⁰`, a figure of earlier
versions that the paper no longer prints. -/
theorem sun_counts :
    (1.345e38 < αs ∧ αs < 1.355e38) ∧
    GMs₀ / (c₀ ^ 2 * lc) = αs / (π * Real.log 2) ∧
    (6.185e37 < αs / (π * Real.log 2) ∧ αs / (π * Real.log 2) < 6.195e37) ∧
    (5.85e99 < Lcos * αs ∧ Lcos * αs < 5.95e99) ∧
    (5.85e110 < Lcos * (1e11 * αs) ∧ Lcos * (1e11 * αs) < 5.95e110) := by
  pi_ln2
  have ha := αs_pos; have hL := Lcos_pos; have hl := lc_pos
  have hshift : GMs₀ / (c₀ ^ 2 * lc) = αs / (π * Real.log 2) := by
    have h := reg.shift_in_cells G₀ (GMs₀ / G₀) reg_jacobson
    rw [reg_αs] at h
    simp only [reg, Reg.pi_def, Reg.ln2_def] at h
    have e : G₀ * (GMs₀ / G₀) / c₀ ^ 2 = GMs₀ / c₀ ^ 2 := by field_simp
    rw [e] at h
    rw [div_mul_eq_div_div, h]
    field_simp
  have hα : 1.345e38 < αs ∧ αs < 1.355e38 := by
    constructor
    · apply lt_of_sq ha.le (by norm_num)
      rw [αs_sq]
      calc (1.345e38 : ℝ) ^ 2 < (3.141592 * 0.6931471803) * (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) := by
            norm_num
        _ < _ := mul_lt_mul_of_pos_right pl_lo (by norm_num)
    · apply lt_of_sq' ha.le (by norm_num)
      rw [αs_sq]
      calc _ < (3.141593 * 0.6931471808) * (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) :=
            mul_lt_mul_of_pos_right pl_hi (by norm_num)
        _ < (1.355e38 : ℝ) ^ 2 := by norm_num
  -- `(α/π ln 2)² = (GM☉²/Gcℏ)/(π ln 2)`
  have eα : (αs / (π * Real.log 2)) ^ 2 = (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) / (π * Real.log 2) := by
    rw [div_pow, αs_sq]; field_simp
  -- `(Lα)² = π² · 4c⁴GM☉²/(ℏ²G²H²Ω_Λ)`
  have eL : (Lcos * αs) ^ 2 = π ^ 2 * (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [mul_pow, Lcos_sq, αs_sq]; field_simp
  have hLα : 5.85e99 < Lcos * αs ∧ Lcos * αs < 5.95e99 := by
    constructor
    · apply lt_of_sq (by positivity) (by norm_num)
      rw [eL]
      calc (5.85e99 : ℝ) ^ 2 < (3.141592 : ℝ) ^ 2 *
            (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
        _ < _ := mul_lt_mul_of_pos_right p2_lo (by norm_num)
    · apply lt_of_sq' (by positivity) (by norm_num)
      rw [eL]
      calc _ < (3.141593 : ℝ) ^ 2 *
            (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) :=
            mul_lt_mul_of_pos_right p2_hi (by norm_num)
        _ < (5.95e99 : ℝ) ^ 2 := by norm_num
  have eg : Lcos * (1e11 * αs) = 1e11 * (Lcos * αs) := by ring
  refine ⟨hα, hshift, ⟨?_, ?_⟩, hLα, ?_, ?_⟩
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [eα]
    calc (6.185e37 : ℝ) ^ 2 < (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) / (3.141593 * 0.6931471808) := by
          norm_num
      _ < _ := div_lt_div_of_pos_left (by norm_num) (by positivity) pl_hi
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [eα]
    calc _ < (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) / (3.141592 * 0.6931471803) :=
          div_lt_div_of_pos_left (by norm_num) (by norm_num) pl_lo
      _ < (6.195e37 : ℝ) ^ 2 := by norm_num
  · rw [eg]; linarith [hLα.1]
  · rw [eg]; linarith [hLα.2]

/-- **Which horizon the count describes** (Secs. II, IV.D, Appendix A).  The Galaxy,
`10¹² M☉ = 2.0×10⁴² kg`, a mass at rest, has `α = 1.35×10⁵⁰` and `2α/ln 2 = 3.9×10⁵⁰`, and
`(2α/ln 2)/L = GM/c²R_Λ` is one part in `10¹¹` of `L_cos` (`8.9×10⁻¹²`).  The matter of a ball of
radius `R_Λ` at today's mean density, `Ω_m = 0.315` of the critical density `3H₀²/8πG`, is
`M = Ω_m H₀² R_Λ³/2G`, so with `R_Λ² = c²/H₀²Ω_Λ` its `GM/c²R_Λ = Ω_m/2Ω_Λ = 0.23`, beyond the
Nariai limit `1/3√3 = 0.19` up to which the Schwarzschild–de Sitter solution has a horizon
(`Reg.sds_outer_horizon` asks for `13 GM/c² < R_Λ`): it is not a mass at rest inside a static
horizon, Eq. (SM) does not apply to it, and the count of Sec. II is that of the horizon of the
solution without a mass. -/
theorem cosmic_mass_beyond_nariai :
    (1.95e42 < 1e12 * (GMs₀ / G₀) ∧ 1e12 * (GMs₀ / G₀) < 2.05e42) ∧
    (1.345e50 < 1e12 * αs ∧ 1e12 * αs < 1.355e50) ∧
    (3.85e50 < 2 * (1e12 * αs) / Real.log 2 ∧ 2 * (1e12 * αs) / Real.log 2 < 3.95e50) ∧
    (8.9e-12 < 1e12 * GMs₀ / (c₀ ^ 2 * RL) ∧ 1e12 * GMs₀ / (c₀ ^ 2 * RL) < 8.91e-12) ∧
    (0.315 : ℝ) * H₀ ^ 2 * RL ^ 3 / (2 * G₀) * G₀ / (c₀ ^ 2 * RL) = 0.315 / (2 * ΩΛ₀) ∧
    (0.229 < (0.315 : ℝ) / (2 * ΩΛ₀) ∧ (0.315 : ℝ) / (2 * ΩΛ₀) < 0.2305) ∧
    (0.192 < 1 / (3 * Real.sqrt 3) ∧ 1 / (3 * Real.sqrt 3) < 0.1925) ∧
    1 / (3 * Real.sqrt 3) < (0.315 : ℝ) / (2 * ΩΛ₀) := by
  pi_ln2
  obtain ⟨r1, r2⟩ := RL_tight
  have hR := RL_pos
  have hR' : RL ≠ 0 := hR.ne'
  have hα := sun_counts.1
  have hcR : (0 : ℝ) < c₀ ^ 2 * RL := mul_pos (by norm_num) hR
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h3lo : (1.732 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3hi : Real.sqrt 3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h33 : (0 : ℝ) < 3 * Real.sqrt 3 := mul_pos (by norm_num) hs3
  have n1 : 1 / (3 * Real.sqrt 3) < 0.1925 := by
    rw [div_lt_iff₀ h33]; linarith
  have n2 : 0.192 < 1 / (3 * Real.sqrt 3) := by
    rw [lt_div_iff₀ h33]; linarith
  have m1 : 0.229 < (0.315 : ℝ) / (2 * ΩΛ₀) := by norm_num
  have m2 : (0.315 : ℝ) / (2 * ΩΛ₀) < 0.2305 := by norm_num
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨m1, m2⟩, ⟨n2, n1⟩, ?_⟩
  · linarith [hα.1]
  · linarith [hα.2]
  · rw [lt_div_iff₀ ln2_pos]; linarith [hα.1]
  · rw [div_lt_iff₀ ln2_pos]; linarith [hα.2]
  · rw [lt_div_iff₀ hcR]
    calc (8.9e-12 : ℝ) * (c₀ ^ 2 * RL) < 8.9e-12 * (c₀ ^ 2 * 1.6584e26) := by gcongr
      _ < 1e12 * GMs₀ := by norm_num
  · rw [div_lt_iff₀ hcR]
    calc (1e12 * GMs₀ : ℝ) < 8.91e-12 * (c₀ ^ 2 * 1.6583e26) := by norm_num
      _ < 8.91e-12 * (c₀ ^ 2 * RL) := by gcongr
  · have e : RL ^ 3 = RL * RL ^ 2 := by ring
    rw [e, RL_sq]
    field_simp
  · linarith

/-- The chain's entropy removed by the Sun, `Lα = 2πM☉cR_Λ/ℏ` (`Reg.entropy_removed`), for these
inputs. -/
theorem reg_sun_entropy : reg.L * reg.α (GMs₀ / G₀) = Lcos * αs := by
  rw [reg_αs]; rfl

/-- **The Earth's orbit** (Sec. IV.B, Table I, Appendix A): `n = 1 au/ℓ_c = 6.27×10⁴⁵`, and
`a_cα/(πn² ln 2) = GM☉/r² = 5.93×10⁻³ m/s²` (the chain's Eq. (newton), `reg_newton_earth`); the
push there is `c²r/R_Λ² = 4.9×10⁻²⁵ m/s²` (`5×10⁻²⁵` to one figure). -/
theorem earth_orbit :
    (6.265e45 < au₀ / lc ∧ au₀ / lc < 6.275e45) ∧
    (5.925e-3 < GMs₀ / au₀ ^ 2 ∧ GMs₀ / au₀ ^ 2 < 5.935e-3) ∧
    (4.85e-25 < c₀ ^ 2 * au₀ / RL ^ 2 ∧ c₀ ^ 2 * au₀ / RL ^ 2 < 4.95e-25) := by
  pi_ln2
  have hl := lc_pos
  have e : (au₀ / lc) ^ 2 = au₀ ^ 2 / (ℏ₀ * G₀ / c₀ ^ 3) / (π * Real.log 2) := by
    rw [div_pow, lc_sq]; field_simp
  refine ⟨⟨?_, ?_⟩, ⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [e]
    calc (6.265e45 : ℝ) ^ 2 < au₀ ^ 2 / (ℏ₀ * G₀ / c₀ ^ 3) / (3.141593 * 0.6931471808) := by
          norm_num
      _ < _ := div_lt_div_of_pos_left (by norm_num) (by positivity) pl_hi
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [e]
    calc _ < au₀ ^ 2 / (ℏ₀ * G₀ / c₀ ^ 3) / (3.141592 * 0.6931471803) :=
          div_lt_div_of_pos_left (by norm_num) (by norm_num) pl_lo
      _ < (6.275e45 : ℝ) ^ 2 := by norm_num
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num

/-- The chain's Newton's law in cells, `a/a_c = α/(πn² ln 2)` (`Reg.newton`), for the pull of the
Sun at 1 au, at the solution's constant `3/R_Λ²`, is `GM☉/r²`. -/
theorem reg_newton_earth :
    reg.ac * (reg.α (GMs₀ / G₀) / (reg.pi * reg.n au₀ ^ 2 * reg.ln2)) = GMs₀ / au₀ ^ 2 := by
  have hr : (0 : ℝ) < au₀ := by norm_num
  have ha0 : (0 : ℝ) < GMs₀ / au₀ ^ 2 := by positivity
  have ha : GMs₀ / au₀ ^ 2 = reg.pull G₀ (GMs₀ / G₀) (3 / reg.RL ^ 2) au₀ := by
    rw [reg.pull_eq _ _ _ _ hr.ne']; field_simp
  have I1 : reg.kB * (reg.ℏ / (reg.La (GMs₀ / au₀ ^ 2) * reg.tc) / reg.kB)
      = reg.ℏ / (reg.La (GMs₀ / au₀ ^ 2) * reg.tc) := by
    have := reg.kB_pos.ne'; field_simp
  have h := (reg.newton G₀ (GMs₀ / G₀) (3 / reg.RL ^ 2) au₀ (GMs₀ / au₀ ^ 2) _ hr ha0 reg_jacobson ha
    I1).2.2
  have hac : reg.ac ≠ 0 := by
    have := reg.c_pos; have := reg.ℓc_pos; unfold Reg.ac; positivity
  unfold Reg.α
  rw [← h]
  field_simp

/-- **Mercury and the deflection of light** (Sec. IV.B): the anomalous advance `6πGM☉/(a(1−e²)c²)`
is `42.98″` per century (the `π` of the advance cancels the `π` of the conversion to arcseconds),
`5.0×10⁻⁷ rad` per orbit, a figure the paper does not print; the deflection of starlight at the
solar limb `4GM☉/(c²R☉)` is `1.75″`. -/
theorem solar_tests :
    (5.0e-7 < 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) ∧
      6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) < 5.05e-7) ∧
    (42.975 < 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
        (648000 / π) ∧
      6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
        (648000 / π) < 42.985) ∧
    (1.75 < 4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / π) ∧
      4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / π) < 1.755) := by
  pi_ln2
  have e : 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
      (648000 / π) = 6 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
      648000 := by field_simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · calc (5.0e-7 : ℝ) < 6 * 3.141592 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) := by
          norm_num
      _ < _ := by gcongr
  · calc _ < 6 * 3.141593 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) := by gcongr
      _ < (5.05e-7 : ℝ) := by norm_num
  · rw [e]; norm_num
  · rw [e]; norm_num
  · calc (1.75 : ℝ) < 4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / 3.141593) := by norm_num
      _ < _ := by gcongr
  · calc _ < 4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / 3.141592) := by gcongr
      _ < (1.755 : ℝ) := by norm_num

/-- **The phase grid**, a check kept from earlier versions of the paper, whose Sec. IV.B remarked
on it; the paper no longer does.  The kinematic effect of a `2π/L` grid, `1.4×10⁻⁶¹ rad`
(`∼10⁻⁶¹`), lies fifty-four orders of magnitude below Mercury's `5×10⁻⁷ rad` per orbit: the ratio
is between `10⁵⁴` and `10⁵⁵`. -/
theorem phase_grid :
    (1.43e-61 < 2 * π / Lcos ∧ 2 * π / Lcos < 1.44e-61) ∧
    (10 ^ 54 < 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * π / Lcos) ∧
      6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * π / Lcos) < 10 ^ 55) := by
  pi_ln2
  obtain ⟨h1, h2⟩ := Lcos_val
  have hL := Lcos_pos
  have e : 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * π / Lcos)
      = 3 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * Lcos := by
    field_simp; norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hL]; nlinarith
  · rw [div_lt_iff₀ hL]; nlinarith
  · rw [e]; nlinarith
  · rw [e]; nlinarith

/-! ## The galactic scale (Sec. IV.C, Table I, Appendix A) -/

lemma cHinf_eq : c₀ ^ 2 / RL = c₀ * Hinf := by
  have := Hinf_pos; unfold RL; field_simp

lemma a0v_eq : a0v = κ0 * (c₀ * Hinf) := by
  have := ln2_pos.ne'; have := Hinf_pos.ne'
  unfold a0v κ0 RL
  field_simp

lemma Hinf_tight7 : 1.8078177e-18 < Hinf ∧ Hinf < 1.8078178e-18 := by
  constructor
  · apply lt_of_sq Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num
  · apply lt_of_sq' Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num

lemma κ0_tight : 0.2213475 < κ0 ∧ κ0 < 0.2213476 := by
  have h1 := Real.log_two_gt_d9; have h2 := Real.log_two_lt_d9; have h0 := ln2_pos
  unfold κ0
  constructor
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith

lemma a0_tight : 1.1996372e-10 < a0v ∧ a0v < 1.199638e-10 := by
  obtain ⟨k1, k2⟩ := κ0_tight
  obtain ⟨h1, h2⟩ := Hinf_tight7
  have hH := Hinf_pos
  rw [a0v_eq]
  constructor
  · calc (1.1996372e-10 : ℝ) < 0.2213475 * (c₀ * 1.8078177e-18) := by norm_num
      _ < κ0 * (c₀ * Hinf) := mul_lt_mul'' k1 (by linarith) (by norm_num) (by norm_num)
  · calc κ0 * (c₀ * Hinf) < 0.2213476 * (c₀ * 1.8078178e-18) :=
          mul_lt_mul'' k2 (by linarith) (by linarith) (by positivity)
      _ < 1.199638e-10 := by norm_num

lemma a0v_pos : 0 < a0v := by have := a0_tight.1; linarith

/-- **The scale**, Eq. (f), Table I and Appendix A: `a₀ = 1.1996×10⁻¹⁰ m/s²`, `1.200` to the
precision quoted, and `0.2213 c²/R_Λ` (the coefficient `(1 − ln 2)/2 ln 2 = 0.22135`). -/
theorem a0_val :
    (1.19963e-10 < a0v ∧ a0v < 1.19964e-10) ∧ (1.1995e-10 < a0v ∧ a0v < 1.2005e-10) ∧
    (0.221345 < κ0 ∧ κ0 < 0.221355) := by
  obtain ⟨h1, h2⟩ := a0_tight
  obtain ⟨k1, k2⟩ := κ0_tight
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The chain's `a₀` with these inputs (`reg_a0`) is the same number. -/
theorem reg_a0_val : 1.1995e-10 < reg.a0 ∧ reg.a0 < 1.2005e-10 := by
  rw [reg_a0]; exact a0_val.2.1

/-- the relative uncertainty of `a₀` from Planck's `H₀ ± 0.5` and `Ω_Λ ± 0.007`, in quadrature -/
noncomputable def relErr : ℝ :=
  Real.sqrt ((1 / 2 / (674 / 10)) ^ 2 + (7 / 1000 / (2 * (685 / 1000))) ^ 2)
/-- McGaugh's total uncertainty, `√(0.02² + 0.24²) × 10⁻¹⁰` -/
noncomputable def σM : ℝ := Real.sqrt ((0.02e-10) ^ 2 + (0.24e-10) ^ 2)
/-- Desmond's total uncertainty, `√(0.04² + 0.09²) × 10⁻¹⁰` -/
noncomputable def σD : ℝ := Real.sqrt ((0.04e-10) ^ 2 + (0.09e-10) ^ 2)

lemma relErr_tight : 0.0090 < relErr ∧ relErr < 0.0091 := by
  unfold relErr
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma σM_tight : 2.408e-11 < σM ∧ σM < 2.409e-11 := by
  unfold σM
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma σD_tight : 9.848e-12 < σD ∧ σD < 9.849e-12 := by
  unfold σD
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The uncertainty of the scale** (Table I, Appendix A): `±0.011×10⁻¹⁰ m/s²`, a relative `0.9%`
from Planck's `H₀` and `Ω_Λ`. -/
theorem a0_uncertainty :
    (0.0085 < relErr ∧ relErr < 0.0095) ∧
    (1.05e-12 < a0v * relErr ∧ a0v * relErr < 1.15e-12) := by
  obtain ⟨r1, r2⟩ := relErr_tight
  obtain ⟨a1, a2⟩ := a0_tight
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · calc (1.05e-12 : ℝ) < 1.1996372e-10 * 0.0090 := by norm_num
      _ < a0v * relErr := mul_lt_mul'' a1 r1 (by norm_num) (by norm_num)
  · calc a0v * relErr < 1.199638e-10 * 0.0091 :=
          mul_lt_mul'' a2 r2 (by linarith) (by linarith)
      _ < (1.15e-12 : ℝ) := by norm_num

/-- **Against the measurements** (Table I): the derived `a₀` lies `0.0σ` from McGaugh's `1.20` and
`0.1σ` from Desmond's `1.19`, counting the systematic errors. -/
theorem a0_sigmas :
    (-0.05 < (a0v - 1.20e-10) / σM ∧ (a0v - 1.20e-10) / σM < 0.05) ∧
    (0.05 < (a0v - 1.19e-10) / σD ∧ (a0v - 1.19e-10) / σD < 0.15) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨m1, m2⟩ := σM_tight
  obtain ⟨d1, d2⟩ := σD_tight
  have hM : 0 < σM := by linarith
  have hD : 0 < σD := by linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hM]; linarith
  · rw [div_lt_iff₀ hM]; linarith
  · rw [lt_div_iff₀ hD]; linarith
  · rw [div_lt_iff₀ hD]; linarith

/-- **With the local `H₀ = 73`** (Appendix A): `a₀ = 1.30×10⁻¹⁰ m/s²`; it lies `0.4σ` and `1.1σ`
from the two measurements, figures the paper does not print. -/
theorem a0_local_H0 :
    (1.295e-10 < a0v * 73 / 67.4 ∧ a0v * 73 / 67.4 < 1.305e-10) ∧
    (0.35 < (a0v * 73 / 67.4 - 1.20e-10) / σM ∧ (a0v * 73 / 67.4 - 1.20e-10) / σM < 0.45) ∧
    (1.05 < (a0v * 73 / 67.4 - 1.19e-10) / σD ∧ (a0v * 73 / 67.4 - 1.19e-10) / σD < 1.15) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨m1, m2⟩ := σM_tight
  obtain ⟨d1, d2⟩ := σD_tight
  have hM : 0 < σM := by linarith
  have hD : 0 < σD := by linarith
  rw [show a0v * 73 / 67.4 = a0v * 365 / 337 by ring]
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hM]; linarith
  · rw [div_lt_iff₀ hM]; linarith
  · rw [lt_div_iff₀ hD]; linarith
  · rw [div_lt_iff₀ hD]; linarith

/-- **The threshold's mean, read from the data** (Sec. IV.C): the scale goes as the square of the
mean (`Reg.law_scale_mean`), so McGaugh's `a₀` puts the mean at `√(1.20/a₀) = 1.00`, with the
spread `0.24/(2 × 1.20) = 0.10`: one qubit. -/
theorem threshold_mean_from_data :
    (0.995 < Real.sqrt (1.20e-10 / a0v) ∧ Real.sqrt (1.20e-10 / a0v) < 1.005) ∧
    (0.095 < σM / (2 * 1.20e-10) ∧ σM / (2 * 1.20e-10) < 0.105) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨m1, m2⟩ := σM_tight
  have ha := a0v_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]; linarith
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- `L_gal(a₀)`, Eq. (Lgal): the ring's length from a measured `a₀`, with the cell from `G`. -/
noncomputable def Lgal (a : ℝ) : ℝ := (1 - Real.log 2) * π * c₀ ^ 2 / (Real.log 2 * a * lc)

/-- `L_gal/L_cos` is the derived `a₀` over the measured one: the cell cancels (Sec. V). -/
lemma Lgal_div_Lcos (a : ℝ) (ha : a ≠ 0) : Lgal a / Lcos = a0v / a := by
  have hl : lc ≠ 0 := lc_pos.ne'
  have hR : RL ≠ 0 := RL_pos.ne'
  have h2 : Real.log 2 ≠ 0 := ln2_pos.ne'
  have hπ : π ≠ 0 := Real.pi_pos.ne'
  unfold Lgal Lcos a0v
  field_simp

/-- **The two pins of `L`** (Table I, Sec. V, Appendix A): `L_gal = 4.37×10⁶¹` with McGaugh's
`a₀ = 1.20×10⁻¹⁰ m/s²` and `4.40×10⁶¹` with Desmond's `1.19×10⁻¹⁰`, against `L_cos = 4.37×10⁶¹`;
the ratios `L_gal/L_cos` are `1.00` and `1.01`; the first-order errors, `20%` and `8.4%` of the
values, are `0.87×10⁶¹` and `0.37×10⁶¹`; both values lie between `2²⁰⁴` and `2²⁰⁵`, and
`2⁴⁰⁹⁵⁰ < L_gal²⁰⁰ < 2⁴⁰⁹⁵⁶` puts `log₂ L_gal` between `204.75` and `204.78` for both: the
ceiling is `204` from either pin, and `log₂ L = 204.8`. -/
theorem two_pins :
    (4.365e61 < Lgal 1.20e-10 ∧ Lgal 1.20e-10 < 4.375e61) ∧
    (4.395e61 < Lgal 1.19e-10 ∧ Lgal 1.19e-10 < 4.405e61) ∧
    (0.9995 < Lgal 1.20e-10 / Lcos ∧ Lgal 1.20e-10 / Lcos < 1) ∧
    (1.008 < Lgal 1.19e-10 / Lcos ∧ Lgal 1.19e-10 / Lcos < 1.0081) ∧
    (0.87e61 < 0.24 / 1.20 * Lgal 1.20e-10 ∧ 0.24 / 1.20 * Lgal 1.20e-10 < 0.875e61) ∧
    (0.365e61 < 0.10 / 1.19 * Lgal 1.19e-10 ∧ 0.10 / 1.19 * Lgal 1.19e-10 < 0.375e61) ∧
    ((2 : ℝ) ^ 204 < Lgal 1.20e-10 ∧ Lgal 1.19e-10 < 2 ^ 205) ∧
    ((2 : ℝ) ^ 40950 < Lgal 1.20e-10 ^ 200 ∧ Lgal 1.19e-10 ^ 200 < 2 ^ 40956) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨c1, c2⟩ := Lcos_tight
  have hL := Lcos_pos
  have rM : Lgal 1.20e-10 / Lcos = a0v / 1.20e-10 := Lgal_div_Lcos _ (by norm_num)
  have rD : Lgal 1.19e-10 / Lcos = a0v / 1.19e-10 := Lgal_div_Lcos _ (by norm_num)
  have eM : Lgal 1.20e-10 = a0v / 1.20e-10 * Lcos := by
    rw [← rM]; field_simp
  have eD : Lgal 1.19e-10 = a0v / 1.19e-10 * Lcos := by
    rw [← rD]; field_simp
  have m1 : 0.9995 < a0v / 1.20e-10 := by rw [lt_div_iff₀ (by norm_num)]; linarith
  have m2 : a0v / 1.20e-10 < 1 := by rw [div_lt_iff₀ (by norm_num)]; linarith
  have d1 : 1.008 < a0v / 1.19e-10 := by rw [lt_div_iff₀ (by norm_num)]; linarith
  have d2 : a0v / 1.19e-10 < 1.0081 := by rw [div_lt_iff₀ (by norm_num)]; linarith
  have LM1 : 0.9995 * 4.3686e61 < Lgal 1.20e-10 := by
    rw [eM]; exact mul_lt_mul'' m1 c1 (by norm_num) (by norm_num)
  have LM2 : Lgal 1.20e-10 < 1 * 4.3687e61 := by
    rw [eM]; exact mul_lt_mul'' m2 c2 (by linarith) (by linarith)
  have LD1 : 1.008 * 4.3686e61 < Lgal 1.19e-10 := by
    rw [eD]; exact mul_lt_mul'' d1 c1 (by norm_num) (by norm_num)
  have LD2 : Lgal 1.19e-10 < 1.0081 * 4.3687e61 := by
    rw [eD]; exact mul_lt_mul'' d2 c2 (by linarith) (by linarith)
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by rwa [rM], by rwa [rM]⟩,
    ⟨by rwa [rD], by rwa [rD]⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · -- `L_gal²⁰⁰ = (a₀/1.20)²⁰⁰ L_cos²⁰⁰ > 0.9995²⁰⁰ · 2⁴⁰⁹⁵¹ > 2⁴⁰⁹⁵⁰`
    obtain ⟨p1, -⟩ := log2_Lcos
    rw [eM, mul_pow]
    have q : (0.9995 : ℝ) ^ 200 < (a0v / 1.20e-10) ^ 200 :=
      pow_lt_pow_left₀ m1 (by norm_num) (by norm_num)
    calc (2 : ℝ) ^ 40950 = (1 / 2) * 2 ^ 40951 := by norm_num
      _ < (0.9995 : ℝ) ^ 200 * 2 ^ 40951 := by
          apply mul_lt_mul_of_pos_right _ (by positivity); norm_num
      _ < (a0v / 1.20e-10) ^ 200 * Lcos ^ 200 :=
          mul_lt_mul'' q p1 (by positivity) (by positivity)
  · -- `L_gal²⁰⁰ < 1.0081²⁰⁰ · 2⁴⁰⁹⁵³ < 8 · 2⁴⁰⁹⁵³ = 2⁴⁰⁹⁵⁶`
    obtain ⟨-, p2⟩ := log2_Lcos
    rw [eD, mul_pow]
    have q : (a0v / 1.19e-10) ^ 200 < (1.0081 : ℝ) ^ 200 :=
      pow_lt_pow_left₀ d2 (by positivity) (by norm_num)
    calc (a0v / 1.19e-10) ^ 200 * Lcos ^ 200 < (1.0081 : ℝ) ^ 200 * 2 ^ 40953 :=
          mul_lt_mul'' q p2 (by positivity) (by positivity)
      _ < 8 * 2 ^ 40953 := by
          apply mul_lt_mul_of_pos_right _ (by positivity); norm_num
      _ = (2 : ℝ) ^ 40956 := by norm_num

/-- **The measured coefficient** (Sec. V, Appendix A): in units of `c²/R_Λ`, McGaugh's `a₀` is
`0.22 ± 0.04` and Desmond's `0.22 ± 0.02`, against the derived `(1 − ln 2)/2 ln 2 = 0.2213`. -/
theorem coefficient_measured :
    (0.221 < 1.20e-10 * RL / c₀ ^ 2 ∧ 1.20e-10 * RL / c₀ ^ 2 < 0.222) ∧
    (0.044 < 0.24e-10 * RL / c₀ ^ 2 ∧ 0.24e-10 * RL / c₀ ^ 2 < 0.0445) ∧
    (0.219 < 1.19e-10 * RL / c₀ ^ 2 ∧ 1.19e-10 * RL / c₀ ^ 2 < 0.220) ∧
    (0.018 < 0.10e-10 * RL / c₀ ^ 2 ∧ 0.10e-10 * RL / c₀ ^ 2 < 0.019) := by
  obtain ⟨r1, r2⟩ := RL_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **The horizon's thermal energy and the matter in a string's mean energy** (Sec. IV.E,
Appendix A): `k_BT_dS = ℏc/2πR_Λ = 3.034×10⁻⁵³ J`, which Appendix A prints as `3.03`, and
`u = (1 − ln 2)k_BT_dS = 9.31×10⁻⁵⁴ J`; the
matter part of a string's mean energy is `1 − ln 2 = 0.307`. -/
theorem string_matter :
    (3.0335e-53 < ℏ₀ * c₀ / (2 * π * RL) ∧ ℏ₀ * c₀ / (2 * π * RL) < 3.0345e-53) ∧
    (9.3105e-54 < (1 - Real.log 2) * (ℏ₀ * c₀ / (2 * π * RL)) ∧
      (1 - Real.log 2) * (ℏ₀ * c₀ / (2 * π * RL)) < 9.3115e-54) ∧
    (0.3065 < 1 - Real.log 2 ∧ 1 - Real.log 2 < 0.3075) := by
  have e : ℏ₀ * c₀ / (2 * π * RL) = ℏ₀ * Hinf / (2 * π) := by
    have := Hinf_pos; have := Real.pi_pos; unfold RL; field_simp
  rw [e]
  obtain ⟨h1, h2⟩ := Hinf_tight7
  have hH := Hinf_pos
  pi_ln2
  have k1 : 3.03424e-53 < ℏ₀ * Hinf / (2 * π) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have k2 : ℏ₀ * Hinf / (2 * π) < 3.03425e-53 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨by linarith, by linarith⟩⟩
  · calc (9.3105e-54 : ℝ) < (1 - 0.6931471808) * 3.03424e-53 := by norm_num
      _ < (1 - Real.log 2) * (ℏ₀ * Hinf / (2 * π)) :=
        mul_lt_mul'' (by linarith) k1 (by norm_num) (by norm_num)
  · calc (1 - Real.log 2) * (ℏ₀ * Hinf / (2 * π)) < (1 - 0.6931471803) * 3.03425e-53 :=
          mul_lt_mul'' (by linarith) k2 (by linarith) (by positivity)
      _ < (9.3115e-54 : ℝ) := by norm_num

/-- **A string's heat** (Sec. IV.E, Appendix A): the horizon's temperature times the string's one
bit, `k_BT_dS ln 2 = 2.10×10⁻⁵³ J`, the vacuum's energy per string. -/
theorem heat_per_string :
    2.1025e-53 < ℏ₀ * c₀ / (2 * π * RL) * Real.log 2 ∧
    ℏ₀ * c₀ / (2 * π * RL) * Real.log 2 < 2.1035e-53 := by
  obtain ⟨⟨t1, t2⟩, -, -⟩ := string_matter
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  constructor
  · calc (2.1025e-53 : ℝ) < 3.0335e-53 * 0.6931471803 := by norm_num
      _ < ℏ₀ * c₀ / (2 * π * RL) * Real.log 2 := mul_lt_mul'' t1 l1 (by norm_num) (by norm_num)
  · calc ℏ₀ * c₀ / (2 * π * RL) * Real.log 2 < 3.0345e-53 * 0.6931471808 :=
          mul_lt_mul'' t2 l2 (by linarith) ln2_pos.le
      _ < 2.1035e-53 := by norm_num

/-- **The predicted vacuum share against the measurements** (Table I, Secs. IV.E, Appendix A): the
share `ln 2 = 0.6931` lies `1.2σ` above Planck's `Ω_Λ = 0.685 ± 0.007` and `1.1σ` below DESI's
`0.7025 ± 0.0086`; the energy inside the horizon at the measured `Ω_Λ` would be `ln 2/Ω_Λ = 1.012`
thermal energies per string, a figure the paper does not print. -/
theorem vacuum_share :
    (0.69305 < Real.log 2 ∧ Real.log 2 < 0.69315) ∧
    (1.15 < (Real.log 2 - 0.685) / 0.007 ∧ (Real.log 2 - 0.685) / 0.007 < 1.25) ∧
    (-1.15 < (Real.log 2 - 0.7025) / 0.0086 ∧ (Real.log 2 - 0.7025) / 0.0086 < -1.05) ∧
    (1.0115 < Real.log 2 / ΩΛ₀ ∧ Real.log 2 / ΩΛ₀ < 1.0125) := by
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **The baryonic Tully–Fisher speeds** (Sec. IV.C): `v⁴ = a₀GM` gives `112 km/s` for
`10¹⁰ M☉` and `200 km/s` for `10¹¹ M☉`. -/
theorem tully_fisher_speeds :
    ((111500 : ℝ) ^ 4 < a0v * (1e10 * GMs₀) ∧ a0v * (1e10 * GMs₀) < (112500 : ℝ) ^ 4) ∧
    ((199500 : ℝ) ^ 4 < a0v * (1e11 * GMs₀) ∧ a0v * (1e11 * GMs₀) < (200500 : ℝ) ^ 4) := by
  obtain ⟨a1, a2⟩ := a0_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : (111500 : ℝ) ^ 4 < 1.1996372e-10 * (1e10 * GMs₀) := by norm_num
    exact this.trans (mul_lt_mul_of_pos_right a1 (by norm_num))
  · have : 1.199638e-10 * (1e10 * GMs₀) < (112500 : ℝ) ^ 4 := by norm_num
    exact (mul_lt_mul_of_pos_right a2 (by norm_num)).trans this
  · have : (199500 : ℝ) ^ 4 < 1.1996372e-10 * (1e11 * GMs₀) := by norm_num
    exact this.trans (mul_lt_mul_of_pos_right a1 (by norm_num))
  · have : 1.199638e-10 * (1e11 * GMs₀) < (200500 : ℝ) ^ 4 := by norm_num
    exact (mul_lt_mul_of_pos_right a2 (by norm_num)).trans this

/-- **Where the deep regime begins** (Secs. IV.B and IV.C, Appendix A): `√(GM/a₀) = 1.05×10¹⁵ m
= 7031 au` for the Sun (`7000` to two figures), and `10.8 kpc` for `10¹¹ M☉` (`11` to two
figures). -/
theorem deep_radii :
    (1.045e15 < Real.sqrt (GMs₀ / a0v) ∧ Real.sqrt (GMs₀ / a0v) < 1.055e15) ∧
    (7030.5 * au₀ < Real.sqrt (GMs₀ / a0v) ∧ Real.sqrt (GMs₀ / a0v) < 7031.5 * au₀) ∧
    (10.75 * kpc₀ < Real.sqrt (1e11 * GMs₀ / a0v) ∧
      Real.sqrt (1e11 * GMs₀ / a0v) < 10.85 * kpc₀) := by
  obtain ⟨a1, a2⟩ := a0_tight
  have ha := a0v_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (1.045e15 : ℝ) ^ 2 * 1.199638e-10 < GMs₀ := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ < (1.055e15 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (7030.5 * au₀) ^ 2 * 1.199638e-10 < GMs₀ := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ < (7031.5 * au₀) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (10.75 * kpc₀) ^ 2 * 1.199638e-10 < 1e11 * GMs₀ := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : 1e11 * GMs₀ < (10.85 * kpc₀) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))

/-- **The solar system** (Sec. IV.B, Appendix A): at Earth's orbit `g_N = 5.93×10⁻³ m/s²` and
`h = √(g_N/a₀) = 7031`; at Neptune's, `30.07 au`, `g_N = 6.56×10⁻⁶ m/s²` and `h = 233.8`, `234` to
the nearest integer. -/
theorem solar_system :
    (5.925e-3 < GMs₀ / au₀ ^ 2 ∧ GMs₀ / au₀ ^ 2 < 5.935e-3) ∧
    (7030.5 < Real.sqrt (GMs₀ / au₀ ^ 2 / a0v) ∧ Real.sqrt (GMs₀ / au₀ ^ 2 / a0v) < 7031.5) ∧
    (6.555e-6 < GMs₀ / (30.07 * au₀) ^ 2 ∧ GMs₀ / (30.07 * au₀) ^ 2 < 6.565e-6) ∧
    (233.8145 < Real.sqrt (GMs₀ / (30.07 * au₀) ^ 2 / a0v) ∧
      Real.sqrt (GMs₀ / (30.07 * au₀) ^ 2 / a0v) < 233.8151) := by
  obtain ⟨a1, a2⟩ := a0_tight
  have ha := a0v_pos
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩, ⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩⟩
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (7030.5 : ℝ) ^ 2 * 1.199638e-10 < GMs₀ / au₀ ^ 2 := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ / au₀ ^ 2 < (7031.5 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (233.8145 : ℝ) ^ 2 * 1.199638e-10 < GMs₀ / (30.07 * au₀) ^ 2 := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ / (30.07 * au₀) ^ 2 < (233.8151 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))

/-- **The departure at Neptune** (Secs. IV.B and IV.C, Appendix A): `e^{−h} = 2.9×10⁻¹⁰²`, and the
departure from Newton's law, `e^{−h}/(1 − e^{−h})`, is `3×10⁻¹⁰²` of `g_N`. -/
theorem neptune_departure :
    let hN := Real.sqrt (GMs₀ / (30.07 * au₀) ^ 2 / a0v)
    (2.85e-102 < Real.exp (-hN) ∧ Real.exp (-hN) < 2.95e-102) ∧
    (2.5e-102 < Real.exp (-hN) / (1 - Real.exp (-hN)) ∧
      Real.exp (-hN) / (1 - Real.exp (-hN)) < 3.5e-102) := by
  intro hN
  obtain ⟨-, -, -, ⟨s1, s2⟩⟩ := solar_system
  have s1' : (233.8145 : ℝ) < hN := s1
  have s2' : hN < (233.8151 : ℝ) := s2
  have e233 : Real.exp 233 = Real.exp 1 ^ 233 := by rw [← Real.exp_nat_mul]; norm_num
  have E1 : (2.7182818283 : ℝ) ^ 233 < Real.exp 233 := by
    rw [e233]; exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have E2 : Real.exp 233 < (2.7182818286 : ℝ) ^ 233 := by
    rw [e233]; exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have f1 : (1.0009999 : ℝ) < Real.exp 0.001 := by
    have := Real.add_one_le_exp (0.001 : ℝ); linarith
  have f2 : Real.exp 0.001 < 1 / (1 - 0.001) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have g1 : (1.0009999 : ℝ) ^ 814 * 1.0005 < Real.exp 0.8145 := by
    have e : Real.exp 0.8145 = Real.exp 0.001 ^ 814 * Real.exp 0.0005 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    apply mul_lt_mul (pow_lt_pow_left₀ f1 (by norm_num) (by norm_num))
    · have := Real.add_one_le_exp (0.0005 : ℝ); linarith
    · norm_num
    · positivity
  have g2 : Real.exp 0.8151 < (1 / (1 - 0.001)) ^ 815 * (1 / (1 - 0.0001)) := by
    have e : Real.exp 0.8151 = Real.exp 0.001 ^ 815 * Real.exp 0.0001 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    exact mul_lt_mul'' (pow_lt_pow_left₀ f2 (Real.exp_pos _).le (by norm_num))
      (Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num))
      (by positivity) (by positivity)
  have hlo : Real.exp 233 * Real.exp 0.8145 < Real.exp hN := by
    rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
  have hhi : Real.exp hN < Real.exp 233 * Real.exp 0.8151 := by
    rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
  have LB : (2.7182818283 : ℝ) ^ 233 * ((1.0009999 : ℝ) ^ 814 * 1.0005) < Real.exp hN :=
    (mul_lt_mul'' E1 g1 (by norm_num) (by norm_num)).trans hlo
  have UB : Real.exp hN <
      (2.7182818286 : ℝ) ^ 233 * ((1 / (1 - 0.001)) ^ 815 * (1 / (1 - 0.0001))) :=
    hhi.trans (mul_lt_mul'' E2 g2 (Real.exp_pos _).le (Real.exp_pos _).le)
  have hE := Real.exp_pos hN
  have hx : Real.exp (-hN) = 1 / Real.exp hN := by rw [Real.exp_neg, one_div]
  have x1 : 2.85e-102 < Real.exp (-hN) := by
    rw [hx, lt_div_iff₀ hE]
    have : (2.85e-102 : ℝ) * ((2.7182818286 : ℝ) ^ 233 * ((1 / (1 - 0.001)) ^ 815 *
      (1 / (1 - 0.0001)))) < 1 := by norm_num
    exact (mul_lt_mul_of_pos_left UB (by norm_num)).trans this
  have x2 : Real.exp (-hN) < 2.95e-102 := by
    rw [hx, div_lt_iff₀ hE]
    have : (1 : ℝ) < 2.95e-102 * ((2.7182818283 : ℝ) ^ 233 * ((1.0009999 : ℝ) ^ 814 * 1.0005)) := by
      norm_num
    exact this.trans (mul_lt_mul_of_pos_left LB (by norm_num))
  have hpos : 0 < 1 - Real.exp (-hN) := by linarith
  refine ⟨⟨x1, x2⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-- the law as a function of `x = g_N/a₀`: `a/g_N = 1/(1 − e^{−√x})` -/
noncomputable def rar (x : ℝ) : ℝ := 1 / (1 - Real.exp (-Real.sqrt x))

lemma rar_eq (s : ℝ) (hs : 0 < s) :
    1 / (1 - Real.exp (-s)) = Real.exp s / (Real.exp s - 1) := by
  have h1 : 1 < Real.exp s := by
    have := Real.exp_lt_exp.2 hs; rwa [Real.exp_zero] at this
  rw [Real.exp_neg]
  have : Real.exp s - 1 ≠ 0 := by linarith
  have : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp

/-- **The law at four accelerations** (Sec. IV.C, Appendix A): `a/g_N = 1.04, 1.58, 3.69, 10.5` at
`g_N/a₀ = 10, 1, 0.1, 0.01`; the departure is `4%` at `10a₀` and `58%` at `a₀`. -/
theorem rar_table :
    (1.035 < rar 10 ∧ rar 10 < 1.045) ∧ (1.575 < rar 1 ∧ rar 1 < 1.585) ∧
    (3.685 < rar 0.1 ∧ rar 0.1 < 3.695) ∧ (10.45 < rar 0.01 ∧ rar 0.01 < 10.55) ∧
    (0.035 < rar 10 - 1 ∧ rar 10 - 1 < 0.045) ∧ (0.575 < rar 1 - 1 ∧ rar 1 - 1 < 0.585) := by
  have f1 : (1.0009999 : ℝ) < Real.exp 0.001 := by
    have := Real.add_one_le_exp (0.001 : ℝ); linarith
  have f2 : Real.exp 0.001 < 1 / (1 - 0.001) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have T10 : 1.035 < rar 10 ∧ rar 10 < 1.045 := by
    have hs1 : (3.1622 : ℝ) < Real.sqrt 10 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs2 : Real.sqrt 10 < 3.1623 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have hE1 : (23.3 : ℝ) < Real.exp (Real.sqrt 10) := by
      have ha : Real.exp 3 * Real.exp 0.1622 < Real.exp (Real.sqrt 10) := by
        rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
      have hb : (0.1622 : ℝ) + 1 ≤ Real.exp 0.1622 := Real.add_one_le_exp _
      have hc : (2.7182818283 : ℝ) ^ 3 < Real.exp 3 := by
        rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
      have hd : (2.7182818283 : ℝ) ^ 3 * 1.1622 < Real.exp 3 * Real.exp 0.1622 := by
        apply mul_lt_mul hc (by linarith) (by norm_num) (Real.exp_pos _).le
      have : (23.3 : ℝ) < 2.7182818283 ^ 3 * 1.1622 := by norm_num
      linarith
    have hE2 : Real.exp (Real.sqrt 10) < 24 := by
      have ha : Real.exp (Real.sqrt 10) < Real.exp 3 * Real.exp 0.1623 := by
        rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
      have hb : Real.exp 0.1623 < 1 / (1 - 0.1623) :=
        Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
      have hc : Real.exp 3 < (2.7182818286 : ℝ) ^ 3 := by
        rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
      have hd : Real.exp 3 * Real.exp 0.1623 < (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) := by
        apply mul_lt_mul'' hc hb (Real.exp_pos _).le (Real.exp_pos _).le
      have : (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) < 24 := by norm_num
      linarith
    unfold rar
    rw [rar_eq (Real.sqrt 10) (by linarith)]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  have T1 : 1.575 < rar 1 ∧ rar 1 < 1.585 := by
    have e1 := Real.exp_one_gt_d9; have e2 := Real.exp_one_lt_d9
    unfold rar
    rw [Real.sqrt_one, rar_eq 1 one_pos]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  have T01 : 3.685 < rar 0.1 ∧ rar 0.1 < 3.695 := by
    have hs1 : (0.3162 : ℝ) < Real.sqrt 0.1 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs2 : Real.sqrt 0.1 < 0.3163 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have g1 : (1.0009999 : ℝ) ^ 316 * 1.0002 < Real.exp (Real.sqrt 0.1) := by
      have e : Real.exp 0.3162 = Real.exp 0.001 ^ 316 * Real.exp 0.0002 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h0 : Real.exp 0.3162 < Real.exp (Real.sqrt 0.1) := Real.exp_lt_exp.2 hs1
      have : (1.0009999 : ℝ) ^ 316 * 1.0002 < Real.exp 0.3162 := by
        rw [e]
        apply mul_lt_mul (pow_lt_pow_left₀ f1 (by norm_num) (by norm_num))
        · have := Real.add_one_le_exp (0.0002 : ℝ); linarith
        · norm_num
        · positivity
      linarith
    have g2 : Real.exp (Real.sqrt 0.1) < (1 / (1 - 0.001)) ^ 316 * (1 / (1 - 0.0003)) := by
      have e : Real.exp 0.3163 = Real.exp 0.001 ^ 316 * Real.exp 0.0003 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h0 : Real.exp (Real.sqrt 0.1) < Real.exp 0.3163 := Real.exp_lt_exp.2 hs2
      have : Real.exp 0.3163 < (1 / (1 - 0.001)) ^ 316 * (1 / (1 - 0.0003)) := by
        rw [e]
        exact mul_lt_mul'' (pow_lt_pow_left₀ f2 (Real.exp_pos _).le (by norm_num))
          (Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num))
          (by positivity) (by positivity)
      linarith
    have c1 : (1.3711 : ℝ) < 1.0009999 ^ 316 * 1.0002 := by norm_num
    have c2 : ((1 : ℝ) / (1 - 0.001)) ^ 316 * (1 / (1 - 0.0003)) < 1.3724 := by norm_num
    have k1 : (1.3711 : ℝ) < Real.exp (Real.sqrt 0.1) := c1.trans g1
    have k2 : Real.exp (Real.sqrt 0.1) < 1.3724 := g2.trans c2
    unfold rar
    rw [rar_eq (Real.sqrt 0.1) (by linarith)]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  have T001 : 10.45 < rar 0.01 ∧ rar 0.01 < 10.55 := by
    have hs : Real.sqrt 0.01 = 0.1 := by
      rw [show (0.01 : ℝ) = 0.1 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    have e : Real.exp 0.1 = Real.exp 0.001 ^ 100 := by rw [← Real.exp_nat_mul]; norm_num
    have g1 : (1.0009999 : ℝ) ^ 100 < Real.exp 0.1 := by
      rw [e]; exact pow_lt_pow_left₀ f1 (by norm_num) (by norm_num)
    have g2 : Real.exp 0.1 < (1 / (1 - 0.001)) ^ 100 := by
      rw [e]; exact pow_lt_pow_left₀ f2 (Real.exp_pos _).le (by norm_num)
    have c1 : (1.1048 : ℝ) < 1.0009999 ^ 100 := by norm_num
    have c2 : ((1 : ℝ) / (1 - 0.001)) ^ 100 < 1.1058 := by norm_num
    have k1 : (1.1048 : ℝ) < Real.exp 0.1 := c1.trans g1
    have k2 : Real.exp 0.1 < 1.1058 := g2.trans c2
    unfold rar
    rw [hs, rar_eq 0.1 (by norm_num)]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  exact ⟨T10, T1, T01, T001, ⟨by linarith [T10.1], by linarith [T10.2]⟩,
    ⟨by linarith [T1.1], by linarith [T1.2]⟩⟩

/-- the Galaxy's field at the Sun, `1.9×10⁻¹⁰ m/s²` [Blanchet & Novak 2011; Hees et al. 2014], and
the Sun's distance from the Galactic center, `8.2 kpc` [GRAVITY Collaboration 2019, a reference of
the files]: observed inputs that Appendix A lists, used in Sec. IV.B -/
noncomputable def ge₀ : ℝ := 1.9e-10
noncomputable def R₀ : ℝ := 8.2 * kpc₀

/-- **The quadrupole coefficient in the total-field reading**, `q₂ = 0.348` at `g_e = 1.6a₀`: the
result of `scripts/cassini.py`, a numerical solution of the Bekenstein–Milgrom equation for the Sun
in a uniform external field with `μ = b(a/a₀)` (the reading the paper does not adopt), checked
against Blanchet & Novak (2011), Table 1, to 3%.  It is a number carried in, not a Lean proof;
`cassini_total_field` certifies only what follows from it. -/
noncomputable def q2_total_field : ℝ := 0.348

/-- the Sun's deep radius `r_M = √(GM☉/a₀)` to four digits, `1.0518×10¹⁵ m` -/
lemma rM_tight : 1.0517e15 < Real.sqrt (GMs₀ / a0v) ∧ Real.sqrt (GMs₀ / a0v) < 1.0519e15 := by
  obtain ⟨a1, a2⟩ := a0_tight
  have ha := a0v_pos
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (1.0517e15 : ℝ) ^ 2 * 1.199638e-10 < GMs₀ := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ < (1.0519e15 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))

/-- **Cassini, had the carriers sensed the total field** (Sec. IV.B, Appendix A): `Q₂ = q₂a₀/r_M =
4.0×10⁻²⁶ s⁻²`, twelve standard deviations (`12.2`) from Cassini's `(3 ± 3)×10⁻²⁷ s⁻²`
[Hees et al. 2014].  The paper's reading, the proper acceleration, gives no such quadrupole. -/
theorem cassini_total_field :
    (3.96e-26 < q2_total_field * a0v / Real.sqrt (GMs₀ / a0v) ∧
      q2_total_field * a0v / Real.sqrt (GMs₀ / a0v) < 3.98e-26) ∧
    (12.2 < (q2_total_field * a0v / Real.sqrt (GMs₀ / a0v) - 3e-27) / 3e-27 ∧
      (q2_total_field * a0v / Real.sqrt (GMs₀ / a0v) - 3e-27) / 3e-27 < 12.3) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨r1, r2⟩ := rM_tight
  have hr : 0 < Real.sqrt (GMs₀ / a0v) := by linarith
  have lo : 3.96e-26 < q2_total_field * a0v / Real.sqrt (GMs₀ / a0v) := by
    rw [lt_div_iff₀ hr]; unfold q2_total_field; nlinarith
  have hi : q2_total_field * a0v / Real.sqrt (GMs₀ / a0v) < 3.98e-26 := by
    rw [div_lt_iff₀ hr]; unfold q2_total_field; nlinarith
  refine ⟨⟨lo, hi⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **The Galaxy's tide at the Sun** (Sec. IV.B, Appendix A): `g_e/R₀ = 7.5×10⁻³¹ s⁻²`, below
`10⁻³⁰ s⁻²`, three orders below Cassini's bound. -/
theorem galactic_tide : 7.5e-31 < ge₀ / R₀ ∧ ge₀ / R₀ < 7.52e-31 ∧ ge₀ / R₀ < 1e-30 := by
  unfold ge₀ R₀
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **A test body's excess at `g_N = 10⁻¹⁰ m/s²`** (Sec. IV.C, Appendix A): `1/(1 − e^{−h})` with
`h = √(10⁻¹⁰/a₀) = 0.913` is `1.67`, against the `1.43 ± 0.06` one analysis of the Gaia wide
binaries reads and the `1.0` of another. -/
theorem test_body_excess :
    1.665 < 1 / (1 - Real.exp (-Real.sqrt (1e-10 / a0v))) ∧
    1 / (1 - Real.exp (-Real.sqrt (1e-10 / a0v))) < 1.675 := by
  obtain ⟨a1, a2⟩ := a0_tight
  have ha := a0v_pos
  -- h = √(10⁻¹⁰/a₀) between 0.91300 and 0.91302
  have hs1 : (0.913 : ℝ) < Real.sqrt (1e-10 / a0v) := by
    rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (0.913 : ℝ) ^ 2 * 1.199638e-10 < 1e-10 := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  have hs2 : Real.sqrt (1e-10 / a0v) < 0.91302 := by
    rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : (1e-10 : ℝ) < (0.91302 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))
  -- e^{0.087} between its quadratic lower bound and its fourth-order upper bound
  have q1 : (1 : ℝ) + 0.087 + 0.087 ^ 2 / 2 ≤ Real.exp 0.087 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have q2 : Real.exp 0.087 ≤ (∑ i ∈ Finset.range 4, (0.087 : ℝ) ^ i / (Nat.factorial i)) +
      (0.087 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) :=
    Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
  have q2' : Real.exp 0.087 ≤ 1.0909 := by
    refine q2.trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have e1 := Real.exp_one_gt_d9; have e2 := Real.exp_one_lt_d9
  have hmul : Real.exp (Real.sqrt (1e-10 / a0v)) * Real.exp 0.087 = Real.exp (Real.sqrt (1e-10 / a0v) + 0.087) := by
    rw [Real.exp_add]
  -- e^h = e^{h + 0.087} / e^{0.087}, with e^{h + 0.087} between e^{1} and e^{1.00002}
  have hE1 : (2.4906 : ℝ) < Real.exp (Real.sqrt (1e-10 / a0v)) := by
    have hp : Real.exp 1 ≤ Real.exp (Real.sqrt (1e-10 / a0v) + 0.087) := Real.exp_le_exp.2 (by linarith)
    have hq : 0 < Real.exp 0.087 := Real.exp_pos _
    rw [← hmul] at hp
    have : (2.4906 : ℝ) * 1.0909 < Real.exp 1 := by linarith
    nlinarith [Real.exp_pos (Real.sqrt (1e-10 / a0v))]
  have hE2 : Real.exp (Real.sqrt (1e-10 / a0v)) < 2.4922 := by
    have hp : Real.exp (Real.sqrt (1e-10 / a0v) + 0.087) ≤ Real.exp 1.00002 := Real.exp_le_exp.2 (by linarith)
    have hb : Real.exp 1.00002 < 1.0000201 * Real.exp 1 := by
      have : Real.exp 1.00002 = Real.exp 1 * Real.exp 0.00002 := by rw [← Real.exp_add]; norm_num
      rw [this, mul_comm]
      have := Real.exp_bound_div_one_sub_of_interval' (x := 0.00002) (by norm_num) (by norm_num)
      have hpos := Real.exp_pos (1 : ℝ)
      have : Real.exp 0.00002 < 1.0000201 := by linarith [show (1 : ℝ) / (1 - 0.00002) < 1.0000201 by norm_num]
      nlinarith
    rw [← hmul] at hp
    have hq : (1 : ℝ) + 0.087 + 0.087 ^ 2 / 2 > 1.0907 := by norm_num
    nlinarith [Real.exp_pos (Real.sqrt (1e-10 / a0v)), Real.exp_pos (0.087 : ℝ)]
  rw [rar_eq _ (by linarith)]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- **Why the temperature cannot lead** (Sec. IV.C): `2c²/R_Λ` is nine times the observed `a₀`;
`√(1 + 2a_Λ/g_N)` at `g_N = 10a₀` is `1.38`, a transition 38% above Newton; and the observed
relation there, `1/(1 − e^{−√10})` [McGaugh 2016], is `1.044`, 4% above (Sec. IV.C; Appendix A prints
`1.04`), certified as `1.0435 < 1/(1 − e^{−√10}) < 1.0445`. -/
theorem temperature_led_numbers :
    (9.0 < 2 * c₀ ^ 2 / (RL * a₀) ∧ 2 * c₀ ^ 2 / (RL * a₀) < 9.1) ∧
    (1.375 < Real.sqrt (1 + 2 * (c₀ ^ 2 / RL) / (10 * a₀)) ∧
      Real.sqrt (1 + 2 * (c₀ ^ 2 / RL) / (10 * a₀)) < 1.385) ∧
    (1.0435 < 1 / (1 - Real.exp (-Real.sqrt 10)) ∧
      1 / (1 - Real.exp (-Real.sqrt 10)) < 1.0445) := by
  have hR := RL_pos; have hH := Hinf_pos
  have e1 : 2 * c₀ ^ 2 / (RL * a₀) = 2 * c₀ * Hinf / a₀ := by unfold RL; field_simp
  have e2 : c₀ ^ 2 / RL = c₀ * Hinf := by unfold RL; field_simp
  obtain ⟨j1, j2⟩ := Hinf_tight
  -- `e^{√10}` lies between `23.6` and `23.98`
  have hs1 : (3.1622 : ℝ) < Real.sqrt 10 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 10 < 3.1623 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hE1 : (23.6 : ℝ) < Real.exp (Real.sqrt 10) := by
    have ha : Real.exp 3 * Real.exp 0.1622 < Real.exp (Real.sqrt 10) := by
      rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
    have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.1622 by norm_num)
    have hb : (1.1753 : ℝ) ≤ Real.exp 0.1622 := by
      have h3 : (1.1753 : ℝ) < 1 + 0.1622 + 0.1622 ^ 2 / 2 := by norm_num
      linarith
    have hc : (2.7182818283 : ℝ) ^ 3 < Real.exp 3 := by
      rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
    have hd : (2.7182818283 : ℝ) ^ 3 * 1.1753 < Real.exp 3 * Real.exp 0.1622 := by
      apply mul_lt_mul hc hb (by norm_num) (Real.exp_pos _).le
    have : (23.6 : ℝ) < 2.7182818283 ^ 3 * 1.1753 := by norm_num
    linarith
  have hE2 : Real.exp (Real.sqrt 10) < 23.98 := by
    have ha : Real.exp (Real.sqrt 10) < Real.exp 3 * Real.exp 0.1623 := by
      rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
    have hb : Real.exp 0.1623 < 1 / (1 - 0.1623) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    have hc : Real.exp 3 < (2.7182818286 : ℝ) ^ 3 := by
      rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have hd : Real.exp 3 * Real.exp 0.1623 < (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) := by
      apply mul_lt_mul'' hc hb (Real.exp_pos _).le (Real.exp_pos _).le
    have : (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) < 23.98 := by norm_num
    linarith
  have hrar : 1 / (1 - Real.exp (-Real.sqrt 10))
      = Real.exp (Real.sqrt 10) / (Real.exp (Real.sqrt 10) - 1) := by
    rw [Real.exp_neg]
    have : Real.exp (Real.sqrt 10) - 1 ≠ 0 := by linarith
    field_simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [e1, lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [e1, div_lt_iff₀ (by norm_num)]; nlinarith
  · rw [e2, Real.lt_sqrt (by norm_num)]
    have : (1.375 : ℝ) ^ 2 < 1 + 2 * (c₀ * 1.8078e-18) / (10 * a₀) := by norm_num
    have h3 : 2 * (c₀ * 1.8078e-18) / (10 * a₀) < 2 * (c₀ * Hinf) / (10 * a₀) := by gcongr
    linarith
  · rw [e2, Real.sqrt_lt' (by norm_num)]
    have : 1 + 2 * (c₀ * 1.8079e-18) / (10 * a₀) < (1.385 : ℝ) ^ 2 := by norm_num
    have h3 : 2 * (c₀ * Hinf) / (10 * a₀) < 2 * (c₀ * 1.8079e-18) / (10 * a₀) := by gcongr
    linarith
  · rw [hrar, lt_div_iff₀ (by linarith)]; nlinarith
  · rw [hrar, div_lt_iff₀ (by linarith)]; nlinarith

/-! ## The cosmological scale (Sec. IV.D, Table I, Appendix A) -/

/-- **Eq. (EL)**: the chain's `E_Λ = (LE_c/4) ln 2 = c⁴R_Λ/2G` for these inputs is
`1.00×10⁷⁰ J`. -/
theorem EΛ_val :
    reg.EΛ = c₀ ^ 4 * RL / (2 * G₀) ∧
    1.003e70 < c₀ ^ 4 * RL / (2 * G₀) ∧ c₀ ^ 4 * RL / (2 * G₀) < 1.004e70 := by
  have hR := RL_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [(reg.EΛ_eq G₀ reg_jacobson).2, reg_RL]; rfl
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num

/-- **The energy inside `R_Λ` at the measured `Ω_Λ`** (Appendix A): with the vacuum's energy `E_Λ`
and the measured share `Ω_Λ`, the energy inside `R_Λ` is `E_Λ/Ω_Λ = 1.46×10⁷⁰ J`, of which matter is
`E_Λ(1 − Ω_Λ)/Ω_Λ = 0.46×10⁷⁰ J`; the derived share `ln 2` would give `E_Λ/ln 2` (`vacuum_share`). -/
theorem energy_today :
    (1.455e70 < c₀ ^ 4 * RL / (2 * G₀ * ΩΛ₀) ∧ c₀ ^ 4 * RL / (2 * G₀ * ΩΛ₀) < 1.465e70) ∧
    (0.455e70 < c₀ ^ 4 * RL / (2 * G₀ * ΩΛ₀) * (1 - ΩΛ₀) ∧
      c₀ ^ 4 * RL / (2 * G₀ * ΩΛ₀) * (1 - ΩΛ₀) < 0.465e70) := by
  have hR := RL_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num
  · have e : c₀ ^ 4 * RL / (2 * G₀ * ΩΛ₀) * (1 - ΩΛ₀) = c₀ ^ 4 * RL * ((1 - ΩΛ₀) / (2 * G₀ * ΩΛ₀)) := by
      ring
    rw [e]
    apply lt_of_sq (by positivity) (by norm_num)
    rw [mul_pow, mul_pow, RL_sq]; norm_num
  · have e : c₀ ^ 4 * RL / (2 * G₀ * ΩΛ₀) * (1 - ΩΛ₀) = c₀ ^ 4 * RL * ((1 - ΩΛ₀) / (2 * G₀ * ΩΛ₀)) := by
      ring
    rw [e]
    apply lt_of_sq' (by positivity) (by norm_num)
    rw [mul_pow, mul_pow, RL_sq]; norm_num

/-- **The energy inside the horizon** (Sec. IV.E, Appendix A): at `k_BT_dS` per string on average
it is
`E_Λ/ln 2 = 1.45×10⁷⁰ J`, of which matter, the fraction `1 − ln 2`, is `0.44×10⁷⁰ J`;
`energy_today` gives the values at the measured `Ω_Λ`. -/
theorem energy_inside_horizon :
    (1.445e70 < c₀ ^ 4 * RL / (2 * G₀) / Real.log 2 ∧
      c₀ ^ 4 * RL / (2 * G₀) / Real.log 2 < 1.455e70) ∧
    (0.44e70 < c₀ ^ 4 * RL / (2 * G₀) * (1 - Real.log 2) / Real.log 2 ∧
      c₀ ^ 4 * RL / (2 * G₀) * (1 - Real.log 2) / Real.log 2 < 0.445e70) := by
  obtain ⟨-, e1, e2⟩ := EΛ_val
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  have hl := ln2_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hl]; linarith
  · rw [div_lt_iff₀ hl]; linarith
  · rw [lt_div_iff₀ hl]
    have : 1.003e70 * (1 - 0.6931471808) < c₀ ^ 4 * RL / (2 * G₀) * (1 - Real.log 2) :=
      mul_lt_mul'' e1 (by linarith) (by norm_num) (by norm_num)
    linarith
  · rw [div_lt_iff₀ hl]
    have : c₀ ^ 4 * RL / (2 * G₀) * (1 - Real.log 2) < 1.004e70 * (1 - 0.6931471803) :=
      mul_lt_mul'' e2 (by linarith) (by linarith) (by linarith)
    linarith

/-- **The vacuum energy density**: the chain's `ρ_Λ = 3π²ρ_c ln 2/2L²` for these inputs equals
`Λc⁴/8πG`, which is `5.25×10⁻¹⁰ J/m³` (`5.3` to two figures, as in Sec. IV.D). -/
theorem ρΛ_val :
    reg.ρΛ = 3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) ∧
    5.25e-10 < 3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) ∧
    3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) < 5.255e-10 := by
  pi_ln2
  have e : 3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) = 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / π := by
    rw [RL_sq]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have h := (reg.ρΛ_eq G₀ (3 / RL ^ 2) reg_jacobson reg_deSitter).2
    rw [h]; rfl
  · rw [e]
    calc (5.25e-10 : ℝ) < 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / 3.141593 := by norm_num
      _ < _ := div_lt_div_of_pos_left (by norm_num) Real.pi_pos Real.pi_lt_d6
  · rw [e]
    calc _ < 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / 3.141592 :=
          div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_d6
      _ < (5.255e-10 : ℝ) := by norm_num

/-- **Eq. (Lambda)**: the chain's `GΛ = 12πc³/(ℏL² ln 2)` for these inputs is `GΛ` with the
observed `Λ`, `7.28×10⁻⁶³`. -/
theorem GΛ_val :
    G₀ * (3 / RL ^ 2) = 12 * π * c₀ ^ 3 / (ℏ₀ * Lcos ^ 2 * Real.log 2) ∧
    7.275e-63 < G₀ * (3 / RL ^ 2) ∧ G₀ * (3 / RL ^ 2) < 7.285e-63 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (reg.G_Lambda G₀ (3 / RL ^ 2) reg_jacobson reg_deSitter).1
    rw [h]; rfl
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num

/-- **The horizon's temperature and the reduction clock** (Sec. II, Table I, Appendix A):
`k_BT_dS = E_c/L = ℏH_∞/2π = 3.03×10⁻⁵³ J` (`3.0` to two figures); `τ* = Lt_c = 2π/H_∞ =
3.5×10¹⁸ s = 1.1×10¹¹ yr`; and the Hubble rate `2π/Lt_c = H_∞ = 1.81×10⁻¹⁸ s⁻¹`
(`reg_clock`, `horizon_val`). -/
theorem temperature_and_clock :
    (3.025e-53 < ℏ₀ * Hinf / (2 * π) ∧ ℏ₀ * Hinf / (2 * π) < 3.035e-53) ∧
    (3.45e18 < 2 * π / Hinf ∧ 2 * π / Hinf < 3.55e18) ∧
    (1.05e11 < 2 * π / Hinf / yr₀ ∧ 2 * π / Hinf / yr₀ < 1.15e11) := by
  pi_ln2
  have hH := Hinf_pos
  obtain ⟨j1, j2⟩ := Hinf_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ hH]; nlinarith
  · rw [div_lt_iff₀ hH]; nlinarith
  · rw [div_div, lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_div, div_lt_iff₀ (by positivity)]; nlinarith

/-- **Where the push would meet Newton's pull** (Secs. IV.C and IV.D: the push "meets the pull only
far beyond any galaxy").  For a galaxy of `10¹² M☉` the radius `r_z` with `r_z³ = GMR_Λ²/c²`
(`Main.zero_gravity`) is `1.1` Mpc, certified as between `1100` and `1130` kpc; the pull of
Eq. (law) is at least Newton's, so it meets the push farther out still
(`Main.pull_and_push`). -/
theorem zero_gravity_radius (rz : ℝ) (hrz : 0 < rz)
    (h : rz ^ 3 = 1e12 * GMs₀ * RL ^ 2 / c₀ ^ 2) : 1100 * kpc₀ < rz ∧ rz < 1130 * kpc₀ := by
  obtain ⟨r1, r2⟩ := RL_tight
  have hR := RL_pos
  have hlo : (1.6583e26 : ℝ) ^ 2 < RL ^ 2 := pow_lt_pow_left₀ r1 (by norm_num) (by norm_num)
  have hhi : RL ^ 2 < (1.6584e26 : ℝ) ^ 2 := pow_lt_pow_left₀ r2 hR.le (by norm_num)
  constructor
  · apply lt_of_pow_lt_pow_left₀ 3 hrz.le
    rw [h, lt_div_iff₀ (by norm_num)]
    calc (1100 * kpc₀) ^ 3 * c₀ ^ 2 < 1e12 * GMs₀ * (1.6583e26 : ℝ) ^ 2 := by norm_num
      _ < 1e12 * GMs₀ * RL ^ 2 := mul_lt_mul_of_pos_left hlo (by norm_num)
  · apply lt_of_pow_lt_pow_left₀ 3 (by norm_num)
    rw [h, div_lt_iff₀ (by norm_num)]
    calc 1e12 * GMs₀ * RL ^ 2 < 1e12 * GMs₀ * (1.6584e26 : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_left hhi (by norm_num)
      _ < (1130 * kpc₀) ^ 3 * c₀ ^ 2 := by norm_num

/-- **Any galaxy, group or cluster** (Sec. IV.D, Appendix A): the zero-gravity radius lies in the
deep regime
when `M < ((1 − ln 2)/2 ln 2)³ c²R_Λ/G` (`Reg.zero_gravity_mass`), which is `1.2×10²¹ M☉`, above any
cluster; for these inputs, every mass up to `10¹⁶ M☉` has
`r_z < (1 − ln 2)R_Λ/(2 ln 2)`. -/
theorem zero_gravity_masses :
    (1.2e21 * (GMs₀ / G₀) < κ0 ^ 3 * (c₀ ^ 2 * RL / G₀) ∧
      κ0 ^ 3 * (c₀ ^ 2 * RL / G₀) < 1.25e21 * (GMs₀ / G₀)) ∧
    ∀ M rz : ℝ, 0 < M → M ≤ 1e16 * (GMs₀ / G₀) → 0 < rz →
      rz ^ 3 = G₀ * M * RL ^ 2 / c₀ ^ 2 → rz < (1 - Real.log 2) * RL / (2 * Real.log 2) := by
  pi_ln2
  obtain ⟨r1, r2⟩ := RL_tight
  obtain ⟨k1, k2⟩ := κ0_tight
  have hR := RL_pos
  have hk0 : 0 < κ0 := by linarith
  have k3lo : (0.2213475 : ℝ) ^ 3 < κ0 ^ 3 := pow_lt_pow_left₀ k1 (by norm_num) (by norm_num)
  have k3hi : κ0 ^ 3 < (0.2213476 : ℝ) ^ 3 := pow_lt_pow_left₀ k2 hk0.le (by norm_num)
  have hlo : 1.2e21 * (GMs₀ / G₀) < κ0 ^ 3 * (c₀ ^ 2 * RL / G₀) := by
    have : (1.2e21 : ℝ) * (GMs₀ / G₀) < (0.2213475 : ℝ) ^ 3 * (c₀ ^ 2 * 1.6583e26 / G₀) := by
      norm_num
    have h2 : (0.2213475 : ℝ) ^ 3 * (c₀ ^ 2 * 1.6583e26 / G₀) < κ0 ^ 3 * (c₀ ^ 2 * RL / G₀) := by
      apply mul_lt_mul'' k3lo _ (by norm_num) (by norm_num)
      rw [div_lt_div_iff_of_pos_right (by norm_num)]
      nlinarith
    linarith
  have hhi : κ0 ^ 3 * (c₀ ^ 2 * RL / G₀) < 1.25e21 * (GMs₀ / G₀) := by
    have : (0.2213476 : ℝ) ^ 3 * (c₀ ^ 2 * 1.6584e26 / G₀) < 1.25e21 * (GMs₀ / G₀) := by norm_num
    have h2 : κ0 ^ 3 * (c₀ ^ 2 * RL / G₀) < (0.2213476 : ℝ) ^ 3 * (c₀ ^ 2 * 1.6584e26 / G₀) := by
      apply mul_lt_mul'' k3hi _ (by positivity) (by positivity)
      rw [div_lt_div_iff_of_pos_right (by norm_num)]
      nlinarith
    linarith
  refine ⟨⟨hlo, hhi⟩, ?_⟩
  intro M rz hM hMle hrz h3
  have h3' : rz ^ 3 = G₀ * M * reg.RL ^ 2 / reg.c ^ 2 := by rw [reg_RL]; exact h3
  have key := (reg.zero_gravity_mass G₀ M rz (by norm_num) hrz h3').2
  rw [reg_RL] at key
  have hM' : M < κ0 ^ 3 * (c₀ ^ 2 * RL / G₀) := by
    have : (1e16 : ℝ) * (GMs₀ / G₀) < 1.2e21 * (GMs₀ / G₀) := by norm_num
    linarith
  exact key hM'

/-- **The 123 orders are `L²`** (Table I, Sec. IV.D): the Planck density `c⁷/ℏG²`, the quantum field
theory estimate of the vacuum energy density, is `4.6×10¹¹³ J/m³`, the paper's `10¹¹³`; it exceeds
the ring's `ρ_Λ` by `(2 ln 2/3) L²` (`Reg.vacuum_ratio`), `8.8×10¹²²`, with `L² = 1.9×10¹²³`, the
paper's 123 orders.  The paper prints the orders only. -/
theorem vacuum_orders :
    (4.6e113 < c₀ ^ 7 / (ℏ₀ * G₀ ^ 2) ∧ c₀ ^ 7 / (ℏ₀ * G₀ ^ 2) < 4.65e113) ∧
    c₀ ^ 7 / (ℏ₀ * G₀ ^ 2) / reg.ρΛ = 2 * Real.log 2 / 3 * Lcos ^ 2 ∧
    (8.8e122 < 2 * Real.log 2 / 3 * Lcos ^ 2 ∧ 2 * Real.log 2 / 3 * Lcos ^ 2 < 8.85e122) ∧
    (1.9e123 < Lcos ^ 2 ∧ Lcos ^ 2 < 1.91e123) := by
  pi_ln2
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have e : 2 * Real.log 2 / 3 * Lcos ^ 2 = π * (8 * c₀ ^ 5 / (3 * ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [Lcos_sq]; field_simp; ring
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := (reg.vacuum_ratio G₀ reg_jacobson).2
    simp only [reg] at h
    exact h
  · rw [e]
    calc (8.8e122 : ℝ) < 3.141592 * (8 * c₀ ^ 5 / (3 * ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right Real.pi_gt_d6 (by norm_num)
  · rw [e]
    calc _ < 3.141593 * (8 * c₀ ^ 5 / (3 * ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right Real.pi_lt_d6 (by norm_num)
      _ < (8.85e122 : ℝ) := by norm_num
  · have : (1.9e123 : ℝ) < 1.4435 * (2 : ℝ) ^ 409 := by norm_num
    linarith
  · have : 1.4436 * (2 : ℝ) ^ 409 < (1.91e123 : ℝ) := by norm_num
    linarith

/-! ## Predictions and the constancy of `G` (Secs. IV.D, VI, Appendix A) -/

/-- `a₀ ∝ cH(z)` predicts a scale `H(1)/H₀ = √(8Ω_m + Ω_Λ) = 1.79` times larger at `z = 1`
(`1.8` to two figures). -/
theorem redshift_one :
    1.785 < Real.sqrt (0.315 * 8 + 0.685) ∧ Real.sqrt (0.315 * 8 + 0.685) < 1.795 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The equation of state** (Sec. VI, Appendix A): the drift bounded is that of the term `Λc²/3`
of the expansion rate, `|Λ̇/Λ| = |Ġ/G| ≲ 10⁻¹³ yr⁻¹`, so with `H₀ = 6.89×10⁻¹¹ yr⁻¹`,
`|1 + w₀| ≲ 10⁻¹³/3H₀ = 4.8×10⁻⁴` (`5×10⁻⁴` to one figure), and twice that, `9.7×10⁻⁴`, if the drift
is referred to the density `Λc⁴/8πG`, which carries `G` as well, `ρ̇_Λ/ρ_Λ = 2Λ̇/Λ`
(`constancy_of_Lambda`); the drift a Hubble-radius horizon would give,
`Ġ/G = 2H(1+q) ≈ 6.5×10⁻¹¹ yr⁻¹` (`Reg.G_drift`), is about 650 times the lunar-laser-ranging
bound `10⁻¹³ yr⁻¹` (Sec. IV.D).  The deceleration parameter is `q = Ω_m/2 − Ω_Λ`, which is `−0.53`
to two figures for the Appendix's `Ω_m` and `Ω_Λ` (the last conjunct); the two figures are
certified with that `q` and with the rounded `q = −0.53`, and hold for both. -/
theorem constancy_numbers :
    (6.885e-11 < H₀ * yr₀ ∧ H₀ * yr₀ < 6.895e-11) ∧
    (4.8e-4 < 1e-13 / (3 * (H₀ * yr₀)) ∧ 1e-13 / (3 * (H₀ * yr₀)) < 4.85e-4) ∧
    (9.65e-4 < 2e-13 / (3 * (H₀ * yr₀)) ∧ 2e-13 / (3 * (H₀ * yr₀)) < 9.75e-4) ∧
    (6.45e-11 < 2 * (H₀ * yr₀) * (1 + ((0.315 : ℝ) / 2 - ΩΛ₀)) ∧
      2 * (H₀ * yr₀) * (1 + ((0.315 : ℝ) / 2 - ΩΛ₀)) < 6.55e-11) ∧
    (645 < 2 * (H₀ * yr₀) * (1 + ((0.315 : ℝ) / 2 - ΩΛ₀)) / 1e-13 ∧
      2 * (H₀ * yr₀) * (1 + ((0.315 : ℝ) / 2 - ΩΛ₀)) / 1e-13 < 655) ∧
    (6.45e-11 < 2 * (H₀ * yr₀) * (1 - 0.53) ∧ 2 * (H₀ * yr₀) * (1 - 0.53) < 6.55e-11) ∧
    (645 < 2 * (H₀ * yr₀) * (1 - 0.53) / 1e-13 ∧ 2 * (H₀ * yr₀) * (1 - 0.53) / 1e-13 < 655) ∧
    (-0.535 < (0.315 : ℝ) / 2 - ΩΛ₀ ∧ (0.315 : ℝ) / 2 - ΩΛ₀ < -0.525) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end Numerics
end Register
