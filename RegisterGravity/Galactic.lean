import RegisterGravity.Chain
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The galactic scale: the string (Sec. IV.C)

The shift of the horizon and the area deficit, both from the solution about a mass; the entropy a
mass removes, from the horizon and within a sphere; the temperature floor; the entropy inside a
sphere, with the fraction `4n/L` that `RouteB.lean` counts and `Bridge.lean` joins to it; the
crossing; Verlinde's elastic
response with the register's counts, with equality and as a bound on the deep regime; the
deep-regime law; and why the temperature cannot lead.  The inputs are the named hypotheses of each
theorem (see `Chain.lean`).  The proper distance to the horizon and the outer horizon with a mass
are in `DeSitter.lean`.
-/

open Real Filter Topology

namespace Register
namespace Reg

variable (R : Reg)

/-- a mass in cell masses, `α = M/m_c` -/
noncomputable def α (M : ℝ) : ℝ := M / R.mc

/-- **The horizon is drawn in by `GM/c²`**, exactly to first order.  With the boundary condition of
`deSitter`, the solution with the mass has, at `R_Λ − ε` with `ε = GM/c²`,
`f = −ε²(3R_Λ − ε)/(R_Λ²(R_Λ − ε))`, which is `O(ε²)`; `sds_outer_horizon` locates the outer
horizon within `2ε²/R_Λ` of `R_Λ − ε`. -/
theorem sds_horizon_shift (G M Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0)
    (hε : R.RL - G * M / R.c ^ 2 ≠ 0) :
    R.fSdS G M Λ (R.RL - G * M / R.c ^ 2)
      = -((G * M / R.c ^ 2) ^ 2 * (3 * R.RL - G * M / R.c ^ 2))
          / (R.RL ^ 2 * (R.RL - G * M / R.c ^ 2)) := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  have hε' : R.c ^ 2 * R.RL - G * M ≠ 0 := by
    have e : R.c ^ 2 * R.RL - G * M = R.c ^ 2 * (R.RL - G * M / R.c ^ 2) := by field_simp
    rw [e]; exact mul_ne_zero (by positivity) hε
  rw [(R.deSitter G Λ).1 hdS]
  unfold fSdS
  field_simp
  ring

/-- `GM/c² = ℓ_c α/(π ln 2)`: the mass draws the horizon in by `α/(π ln 2)` cells (Sec. IV.C). -/
theorem shift_in_cells (G M : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G * M / R.c ^ 2 = R.ℓc * R.α M / (R.pi * R.ln2) := by
  reg_facts R
  rw [(R.G_eq G hJ).1]
  unfold α mc
  field_simp

/-- **The entropy a mass removes**, Eq. (SM).  The circumference loses `2α/ln 2` cells; the entropy
is `(ln 2)/4` times the square of the circumference in cells, so the loss is
`(L/2)·(2α/ln 2)·ln 2 = Lα` to first order (exactly `Lα − α²/ln 2`); and
`Lα = Mc²/k_B T_dS = 2πMcR_Λ/ℏ` with `I1` for `T_dS`. -/
theorem entropy_removed (G M T : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) :
    2 * R.pi * (G * M / R.c ^ 2) / R.ℓc = 2 * R.α M / R.ln2 ∧
    (R.L / 2) * (2 * R.α M / R.ln2) * R.ln2 = R.L * R.α M ∧
    R.L ^ 2 / 4 * R.ln2 - (R.L - 2 * R.α M / R.ln2) ^ 2 / 4 * R.ln2
      = R.L * R.α M - R.α M ^ 2 / R.ln2 ∧
    R.L * R.α M = M * R.c ^ 2 / (R.kB * T) ∧
    R.L * R.α M = 2 * R.pi * M * R.c * R.RL / R.ℏ := by
  reg_facts R
  have h := (R.T_dS T I1).2
  refine ⟨?_, by field_simp, by field_simp; ring, ?_, ?_⟩
  · rw [R.shift_in_cells G M hJ]; field_simp
  · rw [h]; unfold α mc RL; field_simp
  · unfold α mc RL; field_simp

/-- **The temperature floor** (Sec. IV.C).  No ring has more than `L` cells, so by `I1` no horizon
is colder than `E_c/L`: a ring of `L_h ≤ L` cells has `k_BT = E_c/L_h ≥ E_c/L`.  And in de Sitter
space an observer held at acceleration `a` sees the two horizons combined in quadrature (`hDL`,
Deser–Levin), `k_BT = (ℏ/2πc)√(a² + a_Λ²)` with `a_Λ = c²/R_Λ`, never below `E_c/L`, whatever `a`
is. -/
theorem temperature_floor (Lh T a T' : ℝ) (hLh : 0 < Lh) (hLL : Lh ≤ R.L)
    (I1 : R.kB * T = R.ℏ / (Lh * R.tc))
    (hDL : R.kB * T' = R.ℏ / (2 * R.pi * R.c) * Real.sqrt (a ^ 2 + (R.c ^ 2 / R.RL) ^ 2)) :
    R.Ec / R.L ≤ R.kB * T ∧ R.Ec / R.L ≤ R.kB * T' := by
  reg_facts R
  have hRL := R.RL_pos
  constructor
  · rw [I1]
    unfold Ec tc
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : R.ℏ * R.c / R.ℓc * (Lh * (R.ℓc / R.c)) = R.ℏ * Lh := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hLL R.ℏ_pos.le
  · rw [hDL]
    have hsq : R.c ^ 2 / R.RL ≤ Real.sqrt (a ^ 2 + (R.c ^ 2 / R.RL) ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg a]
    have hfl : R.Ec / R.L = R.ℏ / (2 * R.pi * R.c) * (R.c ^ 2 / R.RL) := by
      unfold Ec RL; field_simp
    rw [hfl]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- the entropy the mass removes within a sphere of radius `r`, in units of `k_B`,
`S_M(r) = 2πMcr/ℏ = 2πnα` -/
noncomputable def SM (M r : ℝ) : ℝ := 2 * R.pi * M * R.c * r / R.ℏ

theorem SM_in_cells (M r : ℝ) : R.SM M r = 2 * R.pi * R.n r * R.α M := by
  reg_facts R
  unfold SM n α mc
  field_simp

/-- the rate at which a sphere about the mass gains area with geodesic distance: the sphere of
radius `r` has the area `4πr²`, and the radial part `dr²/f` of the metric makes a step `ds` of
geodesic distance a step `√f ds` of `r`, so `dA/ds = 8πr√f` -/
noncomputable def areaRate (G M Λ r : ℝ) : ℝ := 8 * R.pi * r * Real.sqrt (R.fSdS G M Λ r)

/-- **The area deficit.**  Near the mass (`Λ = 0`), a sphere gains area with geodesic distance more
slowly than `8π` times its radius, by a rate between `8πGM/c²` and `8πGM/c²√f`: to first order in
`GM/c²r`, by `8πGM/c²` per unit of geodesic distance. -/
theorem area_deficit (G M r : ℝ) (hr : 0 < r) (hm : 0 ≤ G * M) (hf : 0 < R.fSdS G M 0 r) :
    8 * R.pi * G * M / R.c ^ 2 ≤ 8 * R.pi * r - R.areaRate G M 0 r ∧
    8 * R.pi * r - R.areaRate G M 0 r
      ≤ 8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt (R.fSdS G M 0 r)) := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  set s := Real.sqrt (R.fSdS G M 0 r) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hf
  have hs2 : s ^ 2 = 1 - 2 * G * M / (R.c ^ 2 * r) := by
    rw [hs, Real.sq_sqrt hf.le]; unfold fSdS; ring
  -- `r(1 − s)(1 + s) = 2GM/c²`
  have key : r * (1 - s) * (1 + s) = 2 * G * M / R.c ^ 2 := by
    have : r * (1 - s) * (1 + s) = r * (1 - s ^ 2) := by ring
    rw [this, hs2]; field_simp; ring
  have hs1 : s ≤ 1 := by
    have h1 : 0 ≤ 2 * G * M / (R.c ^ 2 * r) := div_nonneg (by linarith) (by positivity)
    nlinarith
  have hA : 0 ≤ r * (1 - s) := mul_nonneg hr.le (by linarith)
  have e1 : 8 * R.pi * r - R.areaRate G M 0 r = 8 * R.pi * (r * (1 - s)) := by
    unfold areaRate; rw [← hs]; ring
  have e2 : 8 * R.pi * G * M / R.c ^ 2 = 4 * R.pi * (r * (1 - s) * (1 + s)) := by
    rw [key]; field_simp; ring
  rw [e1]
  constructor
  · rw [e2]
    have : r * (1 - s) * (1 + s) ≤ r * (1 - s) * 2 := by nlinarith
    nlinarith [R.pi_pos]
  · have e3 : 8 * R.pi * G * M / (R.c ^ 2 * s) = 4 * R.pi * (r * (1 - s) * (1 + s)) / s := by
      rw [← e2]; field_simp
    rw [e3, le_div_iff₀ hs0]
    have : r * (1 - s) * (2 * s) ≤ r * (1 - s) * (1 + s) := by nlinarith
    nlinarith [R.pi_pos]

/-- **Summing the deficit** (Sec. IV.C).  If the shortfall `D` of a sphere's area, as a function of
geodesic distance, grows at a rate between `k` and `K` from the body's surface `b` out to `r`, it
has grown by between `k(r − b)` and `K(r − b)`.  `shortfall_removes` applies it to the rate that
`area_deficit` bounds. -/
theorem shortfall_sum (D D' : ℝ → ℝ) (k K b r : ℝ) (hbr : b < r)
    (hD : ∀ s ∈ Set.Icc b r, HasDerivAt D (D' s) s)
    (hk : ∀ s ∈ Set.Ioo b r, k ≤ D' s) (hK : ∀ s ∈ Set.Ioo b r, D' s ≤ K) :
    k * (r - b) ≤ D r - D b ∧ D r - D b ≤ K * (r - b) := by
  have hcont : ContinuousOn D (Set.Icc b r) := fun s hs => (hD s hs).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope D D' hbr hcont
    (fun s hs => hD s (Set.Ioo_subset_Icc_self hs))
  have hrb : 0 < r - b := by linarith
  have e : D r - D b = D' ξ * (r - b) := by rw [hslope]; field_simp
  rw [e]
  exact ⟨mul_le_mul_of_nonneg_right (hk ξ hξ) hrb.le, mul_le_mul_of_nonneg_right (hK ξ hξ) hrb.le⟩

/-- **The shortfall in rings**: a shortfall of `8πGMr/c²` in a sphere's area is, at a ring's share
`4ℓ_c²/π`, `2πnα/ln 2` rings, one bit each, so it removes `S_M(r) = 2πnα`; at `r = R_Λ` this is
Eq. (SM).  `shortfall_removes` obtains the shortfall from `area_deficit` and `shortfall_sum`. -/
theorem removed_rings (G M r : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    8 * R.pi * G * M / R.c ^ 2 * r / R.ringShare = 2 * R.pi * R.n r * R.α M / R.ln2 ∧
    8 * R.pi * G * M / R.c ^ 2 * r / R.ringShare * R.ln2 = R.SM M r ∧
    R.SM M R.RL = R.L * R.α M := by
  reg_facts R
  refine ⟨?_, ?_, ?_⟩
  · rw [R.shares.2, (R.G_eq G hJ).1]
    unfold n α mc
    field_simp; ring
  · rw [R.shares.2, (R.G_eq G hJ).1]
    unfold SM
    field_simp; ring
  · unfold SM α mc RL; field_simp

/-- **The shortfall, summed, and the entropy it removes** (Sec. IV.C).  About the mass alone
(`Λ = 0`), let `ρ(s)` be the areal radius of the sphere at geodesic distance `s` from the body's
center, growing outward from the body's surface at `s = b`, and let `D(s)` be the sphere's
shortfall, which grows at the rate `8πρ − dA/ds` (`areaRate`).  By `area_deficit` the rate lies
between `8πGM/c²` and `8πGM/c²√f(ρ(b))`, since `f` grows outward, so by `shortfall_sum` the
shortfall from `b` out to `r` lies between `8πGM(r − b)/c²` and that over `√f(ρ(b))`.  At a ring's
share, one bit per ring (`removed_rings`), the entropy it removes lies between
`S_M(r − b) = S_M(r) − S_M(b)` and `S_M(r − b)/√f(ρ(b))`: to first order in `GM/c²ρ(b)`, and far
outside the body, it is `S_M(r) = 2πnα`. -/
theorem shortfall_removes (G M b r : ℝ) (ρ D : ℝ → ℝ) (hbr : b < r)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) (hM : 0 ≤ M)
    (hρb : 0 < ρ b) (hρ : ∀ s ∈ Set.Icc b r, ρ b ≤ ρ s) (hfb : 0 < R.fSdS G M 0 (ρ b))
    (hD : ∀ s ∈ Set.Icc b r, HasDerivAt D (8 * R.pi * ρ s - R.areaRate G M 0 (ρ s)) s) :
    R.SM M (r - b) ≤ (D r - D b) / R.ringShare * R.ln2 ∧
    (D r - D b) / R.ringShare * R.ln2 ≤ R.SM M (r - b) / Real.sqrt (R.fSdS G M 0 (ρ b)) ∧
    R.SM M (r - b) = R.SM M r - R.SM M b := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hm : 0 ≤ G * M := mul_nonneg hGpos.le hM
  have hsb : 0 < Real.sqrt (R.fSdS G M 0 (ρ b)) := Real.sqrt_pos.2 hfb
  -- `f` grows outward: `f(ρ(b)) ≤ f(ρ(s))`
  have hmono : ∀ s ∈ Set.Icc b r, R.fSdS G M 0 (ρ b) ≤ R.fSdS G M 0 (ρ s) := by
    intro s hs
    have h1 := hρ s hs
    have hs0 : 0 < ρ s := lt_of_lt_of_le hρb h1
    have h2 : 2 * G * M / (R.c ^ 2 * ρ s) ≤ 2 * G * M / (R.c ^ 2 * ρ b) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity)
        (mul_le_mul_of_nonneg_left h1 (by positivity))
    unfold fSdS
    linarith
  -- the rate lies between `8πGM/c²` and `8πGM/c²√f(ρ(b))`
  have hrate : ∀ s ∈ Set.Icc b r,
      8 * R.pi * G * M / R.c ^ 2 ≤ 8 * R.pi * ρ s - R.areaRate G M 0 (ρ s) ∧
      8 * R.pi * ρ s - R.areaRate G M 0 (ρ s)
        ≤ 8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt (R.fSdS G M 0 (ρ b))) := by
    intro s hs
    have hs0 : 0 < ρ s := lt_of_lt_of_le hρb (hρ s hs)
    have hfs : 0 < R.fSdS G M 0 (ρ s) := lt_of_lt_of_le hfb (hmono s hs)
    obtain ⟨h1, h2⟩ := R.area_deficit G M (ρ s) hs0 hm hfs
    refine ⟨h1, le_trans h2 ?_⟩
    have h8 : 0 ≤ 8 * R.pi * G * M := by
      have := R.pi_pos; nlinarith
    exact div_le_div_of_nonneg_left h8 (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hmono s hs)) (by positivity))
  obtain ⟨hlo, hhi⟩ := shortfall_sum D (fun s => 8 * R.pi * ρ s - R.areaRate G M 0 (ρ s))
    (8 * R.pi * G * M / R.c ^ 2) (8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt (R.fSdS G M 0 (ρ b))))
    b r hbr hD (fun s hs => (hrate s (Set.Ioo_subset_Icc_self hs)).1)
    (fun s hs => (hrate s (Set.Ioo_subset_Icc_self hs)).2)
  -- one bit per ring: `8πGM(r − b)/c²` at a ring's share is `S_M(r − b)`
  have hk := (R.removed_rings G M (r - b) hJ).2.1
  have hshare : 0 < R.ringShare := by rw [R.shares.2]; positivity
  have hw : 0 ≤ R.ln2 / R.ringShare := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [← hk]
    calc 8 * R.pi * G * M / R.c ^ 2 * (r - b) / R.ringShare * R.ln2
        = 8 * R.pi * G * M / R.c ^ 2 * (r - b) * (R.ln2 / R.ringShare) := by ring
      _ ≤ (D r - D b) * (R.ln2 / R.ringShare) := mul_le_mul_of_nonneg_right hlo hw
      _ = (D r - D b) / R.ringShare * R.ln2 := by ring
  · rw [← hk]
    calc (D r - D b) / R.ringShare * R.ln2 = (D r - D b) * (R.ln2 / R.ringShare) := by ring
      _ ≤ 8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt (R.fSdS G M 0 (ρ b))) * (r - b)
            * (R.ln2 / R.ringShare) := mul_le_mul_of_nonneg_right hhi hw
      _ = 8 * R.pi * G * M / R.c ^ 2 * (r - b) / R.ringShare * R.ln2
            / Real.sqrt (R.fSdS G M 0 (ρ b)) := by
          field_simp
  · unfold SM; ring

/-- **The string's share** (Sec. IV.C), from Postulate 1.  Which way a string moves is its entropy,
and every bit carries that alike, so the string's one bit is spread evenly over its cells inside
the horizon.  Of `m` cells numbered `1, …, m` from the body, the first `n` hold the share
`n/m`; `RouteB.route_B_fraction` counts them over the rings through a cell of the sphere. -/
theorem string_share (m n : ℕ) (hn : n ≤ m) :
    (((Finset.Icc 1 m).filter (fun k => k ≤ n)).card : ℝ) / ((Finset.Icc 1 m).card : ℝ)
      = (n : ℝ) / m := by
  have h1 : (Finset.Icc 1 m).filter (fun k => k ≤ n) = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h1, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel, Nat.add_sub_cancel]

/-- the entropy the sphere's strings hold inside it, in units of `k_B`: the share `κn/L` of their
`N_s(r)` bits.  `κ = 4` is the register's, the fraction `n/(L/4)` of `RouteB.route_B_fraction` to
leading order in `1/n` (`Bridge.Sin_from_count`); `κ = 2π` is Verlinde's flat ball. -/
noncomputable def Sin (κ r : ℝ) : ℝ := (κ * R.n r / R.L) * R.Ns r * R.ln2

/-- With `L/4` cells from the body to the horizon, the quarter lap, the share `n/(L/4)` is the
fraction `4n/L` of `Sin 4`. -/
theorem Sin_share (r : ℝ) : R.Sin 4 r = (R.n r / (R.L / 4)) * R.Ns r * R.ln2 := by
  reg_facts R
  unfold Sin
  field_simp

/-- **Eq. (volume)**: `S_in(r) = κπ²n³ ln 2/L`; with `κ = 4`, `4π²n³ ln 2/L`, a volume law. -/
theorem Sin_eq (κ r : ℝ) : R.Sin κ r = κ * R.pi ^ 2 * R.n r ^ 3 * R.ln2 / R.L := by
  reg_facts R
  unfold Sin
  rw [(R.bulk_counts r).2]
  field_simp

/-- **The crossing**, Eq. (criterion): `S_M(r) = S_in(r)` (with `κ = 4`) exactly when
`n² = Lα/(2π ln 2)`; there `N_s = πLα/(2 ln 2)` and `g_N = GM/r² = c²/πR_Λ`. -/
theorem crossing (G M r : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    (R.SM M r = R.Sin 4 r ↔ R.n r ^ 2 = R.L * R.α M / (2 * R.pi * R.ln2)) ∧
    (R.n r ^ 2 = R.L * R.α M / (2 * R.pi * R.ln2) →
      R.Ns r = R.pi * R.L * R.α M / (2 * R.ln2) ∧ G * M / r ^ 2 = R.c ^ 2 / (R.pi * R.RL)) := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  have hn : 0 < R.n r := by unfold n; positivity
  have hn' : R.n r ≠ 0 := hn.ne'
  have hα : 0 < R.α M := by unfold α mc; positivity
  rw [R.SM_in_cells, R.Sin_eq]
  constructor
  · constructor
    · intro h
      -- `2πnα = 4π²n³ ln 2/L` gives `n (2παL − 4π² ln 2 n²) = 0`, and `n ≠ 0`
      have h' : 2 * R.pi * R.n r * R.α M * R.L = 4 * R.pi ^ 2 * R.n r ^ 3 * R.ln2 := by
        rw [h]; field_simp
      have h0 : R.n r * (2 * R.pi * R.α M * R.L - 4 * R.pi ^ 2 * R.ln2 * R.n r ^ 2) = 0 := by
        linear_combination h'
      rcases mul_eq_zero.1 h0 with h0 | h0
      · exact absurd h0 hn'
      · have h1 : R.pi * (2 * (R.α M * R.L - 2 * R.pi * R.ln2 * R.n r ^ 2)) = 0 := by
          linear_combination h0
        have h2 : R.α M * R.L - 2 * R.pi * R.ln2 * R.n r ^ 2 = 0 := by
          rcases mul_eq_zero.1 h1 with h | h
          · exact absurd h R.pi_pos.ne'
          · linarith
        rw [eq_div_iff (by positivity)]
        linear_combination (-1 : ℝ) * h2
    · intro h
      rw [show R.n r ^ 3 = R.n r * R.n r ^ 2 by ring, h]
      field_simp; ring
  · intro h
    constructor
    · rw [(R.bulk_counts r).2, h]; field_simp
    · have hr2 : r ^ 2 = R.ℓc ^ 2 * (R.L * R.α M / (2 * R.pi * R.ln2)) := by
        have : r ^ 2 = R.ℓc ^ 2 * R.n r ^ 2 := by unfold n; field_simp
        rw [this, h]
      rw [(R.G_eq G hJ).1, hr2]
      unfold α mc RL
      field_simp

/-! ### The elastic response (Sec. IV.C) -/

/-- the volume of the sphere -/
noncomputable def V (r : ℝ) : ℝ := 4 / 3 * R.pi * r ^ 3
/-- the volume per unit of entropy, `V_0 = V(r)/S_in(r)` -/
noncomputable def V0 (κ r : ℝ) : ℝ := R.V r / R.Sin κ r
/-- the volume the removed entropy occupies, `V_M(r) = S_M(r) V_0` -/
noncomputable def VM (κ M r : ℝ) : ℝ := R.SM M r * R.V0 κ r
/-- the slope `dV_M/dr` of the linear function `V_M` -/
noncomputable def slope (κ M : ℝ) : ℝ := 8 * R.α M * R.L * R.ℓc ^ 2 / (3 * κ * R.ln2)
/-- the surface gravity of the horizon, `a_Λ = c²/R_Λ`; `DeSitter.horizon_period` derives it from the
solution with the boundary condition -/
noncomputable def aΛ : ℝ := R.c ^ 2 / R.RL
/-- the galactic acceleration for the string fraction `κn/L`: `a_M = πc²/(3κR_Λ)` -/
noncomputable def aM (κ : ℝ) : ℝ := R.pi * R.c ^ 2 / (3 * κ * R.RL)

/-- `V_0 = 4Lℓ_c³/(3πκ ln 2)`; with `κ = 4`, `V_0 = Lℓ_c³/(3π ln 2)` (Sec. IV.C). -/
theorem V0_eq (κ r : ℝ) (hκ : κ ≠ 0) (hr : 0 < r) :
    R.V0 κ r = 4 * R.L * R.ℓc ^ 3 / (3 * R.pi * κ * R.ln2) ∧
    R.V0 4 r = R.L * R.ℓc ^ 3 / (3 * R.pi * R.ln2) := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  constructor
  · unfold V0 V; rw [R.Sin_eq]; unfold n; field_simp
  · unfold V0 V; rw [R.Sin_eq]; unfold n; field_simp

/-- `V_M` is linear in `r`, with the slope `8αLℓ_c²/(3κ ln 2)`: `V_M(r) = r dV_M/dr`. -/
theorem VM_linear (κ M r : ℝ) (hκ : κ ≠ 0) (hr : 0 < r) :
    R.VM κ M r = R.slope κ M * r := by
  reg_facts R
  unfold VM slope
  rw [(R.V0_eq κ r hκ hr).1, R.SM_in_cells]
  unfold n
  field_simp; ring

/-- **Differentiating at fixed `M`** (Sec. IV.C): with equality in `I5`, the cumulative strain
`F(r) = ∫₀^r ε²A dr′` equals `V_M(r) = (dV_M/dr) r` (`VM_linear`) for every `r > 0`, and its
derivative, `ε²A`, is then `dV_M/dr`, the form of `I5` that `elastic` uses. -/
theorem differentiate_equality (F f : ℝ → ℝ) (k r : ℝ) (hr : 0 < r) (hF : HasDerivAt F (f r) r)
    (heq : ∀ s, 0 < s → F s = k * s) : f r = k := by
  have hlin : HasDerivAt (fun s => k * s) k r := by
    simpa using (hasDerivAt_id r).const_mul k
  have hev : F =ᶠ[𝓝 r] fun s => k * s := by
    filter_upwards [lt_mem_nhds hr] with s hs
    exact heq s hs
  exact (hF.congr_of_eventuallyEq hev.symm).unique hlin

/-- **Eq. (aM), with equality**: from `I5` with equality, differentiated at fixed `M`
(`ε²A = dV_M/dr`, under the principal-strain assumption), and `I6` (`Σ_D = (a_Λ/8πG) ε`, with
`Σ_D = M_D/4πr²` the apparent mass `M_D` per unit area of the sphere), the field `g_D` of the
apparent mass satisfies, by Gauss's law (`gauss`), `g_D² = a_M g_N`, with `g_N` the field of the
mass and `a_M = πc²/(3κR_Λ)`: the `ln 2` of the count cancels. -/
theorem elastic (κ G M MD r ε : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I5 : ε ^ 2 * (4 * R.pi * r ^ 2) = R.slope κ M)
    (I6 : MD / (4 * R.pi * r ^ 2) = (R.aΛ / (8 * R.pi * G)) * ε) :
    R.gSdS G MD 0 r ^ 2 = R.aM κ * R.gSdS G M 0 r := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hG0 : G ≠ 0 := hGpos.ne'
  have hr' : r ≠ 0 := hr.ne'
  have hRL := R.RL_pos.ne'
  have hgD : R.gSdS G MD 0 r = R.aΛ * ε / 2 := by
    have h1 : R.gSdS G MD 0 r = 4 * R.pi * G * (MD / (4 * R.pi * r ^ 2)) := by
      rw [R.gauss G MD r hr hG0]; field_simp
    rw [h1, I6]; field_simp; ring
  have hε2 : ε ^ 2 = R.slope κ M / (4 * R.pi * r ^ 2) := by
    rw [eq_div_iff (by positivity)]; exact I5
  rw [hgD, R.gSdS_mass G M r hr', div_pow, mul_pow, hε2, hG]
  unfold aΛ aM slope α mc RL
  field_simp; ring

/-- **The deep-regime bound** (Sec. IV.C; the averaging argument).  Without equality, `I5` says only
that the cumulative strain `F(r) = ∫₀^r ε²A dr'` stays below `V_M(r) = k r`, with `k = dV_M/dr`.
Where the rotation curve is flat the apparent mass grows as `r`, so `ε²A`, the derivative `f` of `F`,
tends to a constant `f∞`; the mean `F(r)/r` tends to the same constant, and so `f∞ ≤ k`. -/
theorem deep_bound (F f : ℝ → ℝ) (k finf : ℝ)
    (hF : ∀ r, 0 < r → HasDerivAt F (f r) r)
    (I5 : ∀ r, 0 < r → F r ≤ k * r)
    (hflat : Tendsto f atTop (𝓝 finf)) :
    finf ≤ k := by
  by_contra hlt
  push Not at hlt
  set m := (finf + k) / 2 with hm
  have hmk : k < m := by rw [hm]; linarith
  have hmf : m < finf := by rw [hm]; linarith
  -- eventually `f > m`
  have hev : ∀ᶠ s in atTop, m < f s := hflat.eventually (lt_mem_nhds hmf)
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hev
  set s₁ := max s₀ 1 with hs₁
  have hs₁pos : 0 < s₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- choose `r` far enough out that the mean exceeds `k`
  have hmk' : 0 < m - k := by linarith
  set A := |F s₁| + |k| * s₁ + 1 with hA
  have hApos : 0 < A := by positivity
  set r := s₁ + A / (m - k) + 1 with hr
  have hr1 : s₁ < r := by
    have : 0 ≤ A / (m - k) := div_nonneg hApos.le hmk'.le
    linarith
  have hrpos : 0 < r := lt_trans hs₁pos hr1
  -- the mean value theorem on `[s₁, r]`
  have hcont : ContinuousOn F (Set.Icc s₁ r) := fun s hs =>
    (hF s (lt_of_lt_of_le hs₁pos hs.1)).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope F f hr1 hcont
    (fun s hs => hF s (lt_trans hs₁pos hs.1))
  have hξm : m < f ξ := hs₀ ξ (le_trans (le_max_left _ _) hξ.1.le)
  have hgrow : F r - F s₁ = f ξ * (r - s₁) := by
    rw [hslope]; field_simp [(sub_pos.2 hr1).ne']
  have h1 : F s₁ + m * (r - s₁) < F r := by
    have : m * (r - s₁) < f ξ * (r - s₁) := mul_lt_mul_of_pos_right hξm (sub_pos.2 hr1)
    linarith
  have h2 := I5 r hrpos
  -- `k r < F s₁ + m (r − s₁)`, contradiction
  have h3 : k * r < F s₁ + m * (r - s₁) := by
    have e : (m - k) * (r - s₁) = A + (m - k) := by
      rw [hr]; field_simp; ring
    have hF1 : 0 ≤ F s₁ + |F s₁| := by linarith [neg_le_abs (F s₁)]
    have hk1 : k * s₁ ≤ |k| * s₁ := mul_le_mul_of_nonneg_right (le_abs_self k) hs₁pos.le
    have : F s₁ + m * (r - s₁) - k * r = F s₁ - k * s₁ + (m - k) * (r - s₁) := by ring
    rw [e, hA] at this
    linarith
  linarith

/-- **Eq. (aM) as an upper bound on the deep regime.**  Let `F(r) = ∫₀^r ε²A dr'` be the cumulative
strain, with `ε(r)` the strain and `A = 4πr²`, and let `M_D(r)` be the apparent mass within `r`.
By `I6` and Gauss's law (`gauss`), the field of the apparent mass is `g_D = a_Λε/2`, so
`ε²A = 16π(r g_D)²/a_Λ²`.  If the rotation curve is flat, `r g_D → v_c²`, and `deep_bound` with
`I5` and `k = dV_M/dr` gives `v_c⁴ ≤ a_M GM`: the coefficient of the deep regime is at most `a_M`,
with equality under the principal-strain assumption (`elastic`, `tully_fisher`). -/
theorem deep_regime_upper_bound (κ G M vc2 : ℝ) (F ε MD : ℝ → ℝ) (hκ : 0 < κ) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hF : ∀ r, 0 < r → HasDerivAt F (ε r ^ 2 * (4 * R.pi * r ^ 2)) r)
    (I5 : ∀ r, 0 < r → F r ≤ R.slope κ M * r)
    (I6 : ∀ r, 0 < r → MD r / (4 * R.pi * r ^ 2) = (R.aΛ / (8 * R.pi * G)) * ε r)
    (hflat : Tendsto (fun r => r * R.gSdS G (MD r) 0 r) atTop (𝓝 vc2)) :
    vc2 ^ 2 ≤ R.aM κ * G * M := by
  reg_facts R
  have hRL := R.RL_pos
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hG0 : G ≠ 0 := hGpos.ne'
  have haΛ : 0 < R.aΛ := by unfold aΛ; positivity
  have haΛ' : R.aΛ ≠ 0 := haΛ.ne'
  -- the strain from `I6` and Gauss's law: `ε²A = 16π(r g_D)²/a_Λ²`
  have hstrain : ∀ r, 0 < r → ε r ^ 2 * (4 * R.pi * r ^ 2)
      = 16 * R.pi * (r * R.gSdS G (MD r) 0 r) ^ 2 / R.aΛ ^ 2 := by
    intro r hr
    have hgD : R.gSdS G (MD r) 0 r = R.aΛ * ε r / 2 := by
      have h1 : R.gSdS G (MD r) 0 r = 4 * R.pi * G * (MD r / (4 * R.pi * r ^ 2)) := by
        rw [R.gauss G (MD r) r hr hG0]; field_simp
      rw [h1, I6 r hr]; field_simp; ring
    rw [hgD]; field_simp; ring
  have hlim0 : Tendsto (fun r => 16 * R.pi * (r * R.gSdS G (MD r) 0 r) ^ 2 / R.aΛ ^ 2) atTop
      (𝓝 (16 * R.pi * vc2 ^ 2 / R.aΛ ^ 2)) :=
    ((hflat.pow 2).const_mul (16 * R.pi)).div_const _
  have hlim : Tendsto (fun r => ε r ^ 2 * (4 * R.pi * r ^ 2)) atTop
      (𝓝 (16 * R.pi * vc2 ^ 2 / R.aΛ ^ 2)) := by
    refine hlim0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact (hstrain r hr).symm
  have hb := deep_bound F _ (R.slope κ M) _ hF I5 hlim
  have e : R.aM κ * G * M = R.aΛ ^ 2 * R.slope κ M / (16 * R.pi) := by
    rw [hG]; unfold aM aΛ slope α mc RL; field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hb
  nlinarith

/-- The two normalizations: the register's quarter lap, `κ = 4`, gives `a_M = πc²/12R_Λ`, which
is `(π²/6)c²/Lℓ_c` in the cell; Verlinde's flat ball, `κ = 2π`, gives `c²/6R_Λ`; the register's
is `π/2` larger. -/
theorem aM_values :
    R.aM 4 = R.pi * R.c ^ 2 / (12 * R.RL) ∧
    R.aM 4 = R.pi ^ 2 / 6 * R.c ^ 2 / (R.L * R.ℓc) ∧
    R.aM (2 * R.pi) = R.c ^ 2 / (6 * R.RL) ∧
    R.aM 4 = (R.pi / 2) * R.aM (2 * R.pi) := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold aM; field_simp; ring
  · unfold aM RL; field_simp; ring
  · unfold aM; field_simp; ring
  · unfold aM; field_simp; ring

/-- **The apparent dark mass**: with the register's `κ = 4`, the apparent mass of `elastic`
satisfies `M_D² = M²n²·π³ ln 2/(6Lα)`, so `M_D = Mn√(π³ ln 2/6Lα)` grows by a fixed amount per cell
of distance. -/
theorem apparent_mass (G M MD r ε : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I5 : ε ^ 2 * (4 * R.pi * r ^ 2) = R.slope 4 M)
    (I6 : MD / (4 * R.pi * r ^ 2) = (R.aΛ / (8 * R.pi * G)) * ε) :
    MD ^ 2 = M ^ 2 * R.n r ^ 2 * (R.pi ^ 3 * R.ln2 / (6 * R.L * R.α M)) := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hG0 : G ≠ 0 := hGpos.ne'
  have hr' : r ≠ 0 := hr.ne'
  have hRL := R.RL_pos.ne'
  have hdeep := R.elastic 4 G M MD r ε (by norm_num) hr hM hJ I5 I6
  rw [R.gSdS_mass G MD r hr', R.gSdS_mass G M r hr'] at hdeep
  have hMD : MD ^ 2 = R.aM 4 * M * r ^ 2 / G := by
    rw [div_pow, mul_pow] at hdeep
    field_simp at hdeep
    field_simp
    linear_combination hdeep
  rw [hMD, hG]
  unfold aM n α mc RL
  field_simp; ring

/-- **Eq. (btfr)**: in the deep regime, where the field of the apparent mass dominates, the field is
`g_D = √(a_M g_N)` (`elastic`), so a circular orbit, `v_c² = g_D r`, has `v_c⁴ = a_M GM`, the
baryonic Tully–Fisher relation. -/
theorem tully_fisher (κ G M MD r ε : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I5 : ε ^ 2 * (4 * R.pi * r ^ 2) = R.slope κ M)
    (I6 : MD / (4 * R.pi * r ^ 2) = (R.aΛ / (8 * R.pi * G)) * ε) :
    (R.gSdS G MD 0 r * r) ^ 2 = R.aM κ * G * M := by
  have hr' : r ≠ 0 := hr.ne'
  rw [mul_pow, R.elastic κ G M MD r ε hκ hr hM hJ I5 I6, R.gSdS_mass G M r hr']
  field_simp

/-- **The galactic pin**, Eq. (Lgal): `a_M = a_0` exactly when `L = (π²/6) c²/(a_0 ℓ_c)`. -/
theorem galactic_pin (a0 : ℝ) (ha0 : 0 < a0) :
    R.aM 4 = a0 ↔ R.L = R.pi ^ 2 / 6 * R.c ^ 2 / (a0 * R.ℓc) := by
  reg_facts R
  rw [R.aM_values.2.1]
  constructor
  · intro h
    rw [eq_div_iff (by positivity)]
    rw [div_eq_iff (by positivity)] at h
    linear_combination (-1 : ℝ) * h
  · intro h
    rw [h]; field_simp

/-- **The galactic pin as a bound** (Sec. IV.C): since Eq. (aM) is an upper bound on the deep
regime, an observed `a₀ ≤ a_M` gives `L ≤ (π²/6)c²/(a₀ℓ_c)`, and conversely. -/
theorem galactic_bound (a0 : ℝ) (ha0 : 0 < a0) :
    a0 ≤ R.aM 4 ↔ R.L ≤ R.pi ^ 2 / 6 * R.c ^ 2 / (a0 * R.ℓc) := by
  reg_facts R
  rw [R.aM_values.2.1, le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-! ### Why the temperature cannot lead (Sec. IV.C) -/

/-- **The rejected alternative.**  Its premise `hled`: gravity follows the excess of the
Deser–Levin temperature over the floor, `√(a² + a_Λ²) − a_Λ = g_N`, as Milgrom proposed.  Then
`a² = g_N² + 2a_Λ g_N`: the deep form with the coefficient `2a_Λ = 2c²/R_Λ`, which observation
rejects (`Numerics.temperature_led_numbers`). -/
theorem temperature_led (a gN : ℝ)
    (hled : Real.sqrt (a ^ 2 + R.aΛ ^ 2) - R.aΛ = gN) :
    a ^ 2 = gN ^ 2 + 2 * R.aΛ * gN ∧ 2 * R.aΛ = 2 * R.c ^ 2 / R.RL := by
  have h : Real.sqrt (a ^ 2 + R.aΛ ^ 2) = gN + R.aΛ := by linarith
  have h2 : a ^ 2 + R.aΛ ^ 2 = (gN + R.aΛ) ^ 2 := by
    rw [← h, Real.sq_sqrt (by positivity)]
  refine ⟨by linear_combination h2, ?_⟩
  unfold aΛ; ring

end Reg
end Register
