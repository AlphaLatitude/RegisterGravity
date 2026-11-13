import RegisterGravity.Chain
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The galactic scale: the horizon with a mass, and the temperature (Sec. IV.C)

The shift of the horizon and the area deficit, both from the solution about a mass; the entropy a
mass removes, from the horizon (`entropy_removed`, with the horizon's count
`massive_horizon_count`) and within a sphere, with the fraction of the strings a mass removes
(`removed_fraction`), by which the count of Eq. (N) falls about a mass (Sec. III.C); the temperature floor;
and why the temperature cannot lead.  The derivation of the galactic law itself, from the strings
that carry the body's information, is in `Carriers.lean`.  The inputs are the named hypotheses of
each theorem (see `Chain.lean`).  The proper distance to the horizon and the outer horizon with a
mass are in `DeSitter.lean`.
-/

open Real Filter Topology

namespace Register
namespace Reg

variable (R : Reg)

/-- a mass in cell masses, `α = M/m_c` -/
noncomputable def α (M : ℝ) : ℝ := M / R.mc

/-- `GM/c² = ℓ_c α/(π ln 2)`: the mass draws the horizon in by `α/(π ln 2)` cells (Sec. IV.C). -/
theorem shift_in_cells (G M : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G * M / R.c ^ 2 = R.ℓc * R.α M / (R.pi * R.ln2) := by
  reg_facts R
  rw [(R.G_eq G hJ).1]
  unfold α mc
  field_simp

/-- **The entropy a mass removes**, Eq. (SM).  To first order in the mass, the circumference of the
horizon with the mass inside is `L_M = L − 2α/ln 2` cells, and the area law, one bit per ring's
share of area, gives it `L_M²/4` bits (`massive_horizon_count`), the number Eqs. (counts) and (S)
would give with `L_M` in place of `L` (the great circles of that horizon, of `L_M` cells, are
shorter than a largest ring; whether they are rings, the shorter rings Postulate 1 allows, no
derivation needs, Secs. IV.C and IV.D).  The loss is `(L/2)·(2α/ln 2)·ln 2 = Lα` to
first order; the third conjunct is the difference of the two counts, `L²/4` and `L_M²/4` bits, for
this first-order `L_M`.  And `Lα = Mc²/k_B T_dS = 2πMcR_Λ/ℏ` with `I1` for `T_dS`. -/
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

/-- **The horizon with a mass inside holds `L_M²/4` bits, to first order** (Sec. IV.C).  The outer horizon lies at
`R_Λ − GM/c²` to first order in the mass (`sds_outer_horizon`), and the area law, one string for each
ring's share of the area (`ratio_of_areas`), gives a sphere of that radius `N_s = (L − 2α/ln 2)²/4`
strings, `L_M²/4` with `L_M = L − 2α/ln 2`. -/
theorem massive_horizon_count (G M : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.Ns (R.RL - G * M / R.c ^ 2) = (R.L - 2 * R.α M / R.ln2) ^ 2 / 4 := by
  reg_facts R
  rw [R.shift_in_cells G M hJ, R.bulk_counts]
  unfold n RL
  field_simp
  ring

/-- **The temperature floor** (Sec. IV.C).  In de Sitter space an observer held at acceleration `a`
sees the two horizons combined in quadrature (`hDL`, Deser–Levin), `k_BT = (ℏ/2πc)√(a² + a_Λ²)`
with `a_Λ = c²/R_Λ`, the surface gravity of de Sitter space's horizon at `R_Λ`, written into `hDL`
here (`DeSitter.horizon_period` derives it from `hdS`),
never below `E_c/L`, whatever `a` is: no observer in de Sitter space sees a
horizon colder than the cosmological one, `k_BT_dS = E_c/L` (`T_dS`), whose period is the lap of a
largest ring.  `Main.temperature_floor` takes `hDL` with the surface gravity of the horizon of the
solution without a mass, `−g(r_h)`, which `DeSitter.surface_gravity_eq` derives to be `a_Λ`. -/
theorem temperature_floor (a T' : ℝ)
    (hDL : R.kB * T' = R.ℏ / (2 * R.pi * R.c) * Real.sqrt (a ^ 2 + (R.c ^ 2 / R.RL) ^ 2)) :
    R.Ec / R.L ≤ R.kB * T' := by
  reg_facts R
  have hRL := R.RL_pos
  rw [hDL]
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

/-- **The area deficit the mass adds** (Sec. III.C).  At the same constant `Λ ≥ 0`, a sphere about
the mass gains area with geodesic distance more slowly than a sphere of the same area in the
solution without the mass, by a rate between `8πGM/c²` and `8πGM/c²√f`, with `f` the metric
function with the mass: the two rates differ by `16πGM/c²(√f₀ + √f)`, with `f ≤ f₀ ≤ 1` the metric
function without it.  To first order in `GM/c²r` and `Λr²` the deficit is `8πGM/c²` per unit of
geodesic distance.  As for the pull (`pull`), the comparison is at the same `Λ`; at `Λ = 0` it is
the comparison with flat space. -/
theorem area_deficit (G M Λ r : ℝ) (hr : 0 < r) (hm : 0 ≤ G * M) (hΛ : 0 ≤ Λ)
    (hf : 0 < R.fSdS G M Λ r) :
    8 * R.pi * G * M / R.c ^ 2 ≤ R.areaRate G 0 Λ r - R.areaRate G M Λ r ∧
    R.areaRate G 0 Λ r - R.areaRate G M Λ r
      ≤ 8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt (R.fSdS G M Λ r)) := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  set s := Real.sqrt (R.fSdS G M Λ r) with hs
  set s₀ := Real.sqrt (R.fSdS G 0 Λ r) with hs₀
  have hs0 : 0 < s := Real.sqrt_pos.2 hf
  have hm' : 0 ≤ 2 * (G * M) / (R.c ^ 2 * r) := by positivity
  -- without the mass the metric function is larger by `2GM/c²r`, and at most one
  have hf0 : R.fSdS G 0 Λ r = R.fSdS G M Λ r + 2 * (G * M) / (R.c ^ 2 * r) := by
    unfold fSdS; ring
  have hf0pos : 0 < R.fSdS G 0 Λ r := by rw [hf0]; linarith
  have hf01 : R.fSdS G 0 Λ r ≤ 1 := by
    have e : R.fSdS G 0 Λ r = 1 - Λ * r ^ 2 / 3 := by unfold fSdS; ring
    rw [e]; have := mul_nonneg hΛ (sq_nonneg r); linarith
  have hs2 : s ^ 2 = R.fSdS G M Λ r := Real.sq_sqrt hf.le
  have hs₀2 : s₀ ^ 2 = R.fSdS G 0 Λ r := Real.sq_sqrt hf0pos.le
  -- `r(s₀ − s)(s₀ + s) = 2GM/c²`
  have key : r * (s₀ - s) * (s₀ + s) = 2 * G * M / R.c ^ 2 := by
    have : r * (s₀ - s) * (s₀ + s) = r * (s₀ ^ 2 - s ^ 2) := by ring
    rw [this, hs₀2, hs2, hf0]; field_simp; ring
  -- `s ≤ s₀ ≤ 1`
  have hss₀ : s ≤ s₀ := Real.sqrt_le_sqrt (by rw [hf0]; linarith)
  have hs₀1 : s₀ ≤ 1 := (Real.sqrt_le_sqrt hf01).trans_eq Real.sqrt_one
  have hA : 0 ≤ r * (s₀ - s) := mul_nonneg hr.le (by linarith)
  have e1 : R.areaRate G 0 Λ r - R.areaRate G M Λ r = 8 * R.pi * (r * (s₀ - s)) := by
    unfold areaRate; rw [← hs, ← hs₀]; ring
  have e2 : 8 * R.pi * G * M / R.c ^ 2 = 4 * R.pi * (r * (s₀ - s) * (s₀ + s)) := by
    rw [key]; field_simp; ring
  rw [e1]
  constructor
  · rw [e2]
    have : r * (s₀ - s) * (s₀ + s) ≤ r * (s₀ - s) * 2 := by nlinarith
    nlinarith [R.pi_pos]
  · have e3 : 8 * R.pi * G * M / (R.c ^ 2 * s) = 4 * R.pi * (r * (s₀ - s) * (s₀ + s)) / s := by
      rw [← e2]; field_simp
    rw [e3, le_div_iff₀ hs0]
    have : r * (s₀ - s) * (2 * s) ≤ r * (s₀ - s) * (s₀ + s) := by nlinarith
    nlinarith [R.pi_pos]

/-- The metric function `f = 1 − 2GM/c²r − Λr²/3` is concave in `r > 0` for `GM, Λ ≥ 0`, so
between two radii it is at least the smaller of its two end values. -/
lemma fSdS_min_le (G M Λ a x b : ℝ) (hm : 0 ≤ G * M) (hΛ : 0 ≤ Λ) (ha : 0 < a) (hax : a ≤ x)
    (hxb : x ≤ b) :
    min (R.fSdS G M Λ a) (R.fSdS G M Λ b) ≤ R.fSdS G M Λ x := by
  reg_facts R
  have hx : 0 < x := ha.trans_le hax
  have hb : 0 < b := hx.trans_le hxb
  -- `f` is concave: `(b − a) f(x) − (b − x) f(a) − (x − a) f(b) ≥ 0`
  have key : (b - a) * R.fSdS G M Λ x - (b - x) * R.fSdS G M Λ a - (x - a) * R.fSdS G M Λ b
      = (b - a) * (x - a) * (b - x) * (2 * (G * M) / (R.c ^ 2 * a * b * x) + Λ / 3) := by
    unfold fSdS; field_simp; ring
  have hpos : 0 ≤ (b - a) * (x - a) * (b - x) * (2 * (G * M) / (R.c ^ 2 * a * b * x) + Λ / 3) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by positivity)
  rcases eq_or_lt_of_le (hax.trans hxb) with hab | hab
  · have hxa : x = a := le_antisymm (hab ▸ hxb) hax
    rw [hxa]; exact min_le_left _ _
  · have hba : 0 < b - a := sub_pos.2 hab
    rcases le_total (R.fSdS G M Λ a) (R.fSdS G M Λ b) with h | h
    · rw [min_eq_left h]
      have h2 : (b - a) * R.fSdS G M Λ a ≤ (b - a) * R.fSdS G M Λ x := by
        have : (x - a) * R.fSdS G M Λ a ≤ (x - a) * R.fSdS G M Λ b :=
          mul_le_mul_of_nonneg_left h (by linarith)
        nlinarith
      exact le_of_mul_le_mul_left h2 hba
    · rw [min_eq_right h]
      have h2 : (b - a) * R.fSdS G M Λ b ≤ (b - a) * R.fSdS G M Λ x := by
        have : (b - x) * R.fSdS G M Λ b ≤ (b - x) * R.fSdS G M Λ a :=
          mul_le_mul_of_nonneg_left h (by linarith)
        nlinarith
      exact le_of_mul_le_mul_left h2 hba

/-- **Summing the deficit** (Sec. III.C).  If the shortfall `D` of a sphere's area, as a function of
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

/-- **The fraction of the strings a mass removes** (Secs. II and III.C): the entropy `S_M(r)` a mass
removes within a sphere of radius `r`, which `shortfall_removes` finds to first order far outside the
body, is the fraction `2GM/c²r` of the strings' entropy `N_s(r) ln 2` of Eq. (N).  So to first order
a sphere about the mass holds the fraction `2GM/c²r` fewer strings than the count without a mass. -/
theorem removed_fraction (G M r : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.SM M r = 2 * G * M / (R.c ^ 2 * r) * (R.Ns r * R.ln2) := by
  reg_facts R
  have hη : R.η ≠ 0 := by rw [R.eta_eq]; positivity
  rcases eq_or_ne r 0 with hr | hr
  · subst hr; unfold SM Ns; simp
  rw [hJ]
  unfold SM Ns
  field_simp

/-- **The shortfall, summed, and the entropy it removes** (Sec. III.C).  About the mass, in the
solution with the constant `Λ ≥ 0`, let `ρ(s)` be the areal radius of the sphere at geodesic
distance `s` from the body's center, growing outward from the body's surface at `s = b` to `r`, and
let `D(s)` be the sphere's shortfall, which grows at the rate by which the sphere gains area more
slowly than a sphere of the same area in the solution without the mass (`areaRate`).  By
`area_deficit` the rate lies between `8πGM/c²` and `8πGM/c²√f_min`, with `f_min` the smaller value
of the metric function at the two ends (`fSdS_min_le`), so by `shortfall_sum` the shortfall from
`b` out to `r` lies between `8πGM(r − b)/c²` and that over `√f_min`.  At a ring's share, one bit
per ring (`removed_rings`), the entropy it removes lies between `S_M(r − b) = S_M(r) − S_M(b)` and
`S_M(r − b)/√f_min`: to first order in `GM/c²ρ(b)` and `Λρ(r)²`, far outside the body, it is
`S_M(r) = 2πnα`.  `Main.entropy_removed_sphere` derives the hypotheses on `ρ` from the metric. -/
theorem shortfall_removes (G M Λ b r : ℝ) (ρ D : ℝ → ℝ) (hbr : b < r)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) (hM : 0 ≤ M) (hΛ : 0 ≤ Λ)
    (hρb : 0 < ρ b) (hρ : ∀ s ∈ Set.Icc b r, ρ b ≤ ρ s ∧ ρ s ≤ ρ r)
    (hfb : 0 < R.fSdS G M Λ (ρ b)) (hfr : 0 < R.fSdS G M Λ (ρ r))
    (hD : ∀ s ∈ Set.Icc b r,
      HasDerivAt D (R.areaRate G 0 Λ (ρ s) - R.areaRate G M Λ (ρ s)) s) :
    R.SM M (r - b) ≤ (D r - D b) / R.ringShare * R.ln2 ∧
    (D r - D b) / R.ringShare * R.ln2
      ≤ R.SM M (r - b) / Real.sqrt (min (R.fSdS G M Λ (ρ b)) (R.fSdS G M Λ (ρ r))) ∧
    R.SM M (r - b) = R.SM M r - R.SM M b := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hm : 0 ≤ G * M := mul_nonneg hGpos.le hM
  set fmin := min (R.fSdS G M Λ (ρ b)) (R.fSdS G M Λ (ρ r)) with hfmin
  have hfmin0 : 0 < fmin := lt_min hfb hfr
  have hsmin : 0 < Real.sqrt fmin := Real.sqrt_pos.2 hfmin0
  -- between the two ends `f` is at least its smaller end value, `f` being concave
  have hlow : ∀ s ∈ Set.Icc b r, fmin ≤ R.fSdS G M Λ (ρ s) := fun s hs =>
    R.fSdS_min_le G M Λ (ρ b) (ρ s) (ρ r) hm hΛ hρb (hρ s hs).1 (hρ s hs).2
  -- the rate lies between `8πGM/c²` and `8πGM/c²√f_min`
  have hrate : ∀ s ∈ Set.Icc b r,
      8 * R.pi * G * M / R.c ^ 2 ≤ R.areaRate G 0 Λ (ρ s) - R.areaRate G M Λ (ρ s) ∧
      R.areaRate G 0 Λ (ρ s) - R.areaRate G M Λ (ρ s)
        ≤ 8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt fmin) := by
    intro s hs
    have hs0 : 0 < ρ s := lt_of_lt_of_le hρb (hρ s hs).1
    have hfs : 0 < R.fSdS G M Λ (ρ s) := lt_of_lt_of_le hfmin0 (hlow s hs)
    obtain ⟨h1, h2⟩ := R.area_deficit G M Λ (ρ s) hs0 hm hΛ hfs
    refine ⟨h1, le_trans h2 ?_⟩
    have h8 : 0 ≤ 8 * R.pi * G * M := by
      have := R.pi_pos; nlinarith
    exact div_le_div_of_nonneg_left h8 (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlow s hs)) (by positivity))
  obtain ⟨hlo, hhi⟩ := shortfall_sum D
    (fun s => R.areaRate G 0 Λ (ρ s) - R.areaRate G M Λ (ρ s))
    (8 * R.pi * G * M / R.c ^ 2) (8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt fmin))
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
      _ ≤ 8 * R.pi * G * M / (R.c ^ 2 * Real.sqrt fmin) * (r - b)
            * (R.ln2 / R.ringShare) := mul_le_mul_of_nonneg_right hhi hw
      _ = 8 * R.pi * G * M / R.c ^ 2 * (r - b) / R.ringShare * R.ln2
            / Real.sqrt fmin := by
          field_simp
  · unfold SM; ring

/-- the surface gravity of the horizon, `a_Λ = c²/R_Λ`; `DeSitter.horizon_period` derives it from the
solution with the boundary condition -/
noncomputable def aΛ : ℝ := R.c ^ 2 / R.RL

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
