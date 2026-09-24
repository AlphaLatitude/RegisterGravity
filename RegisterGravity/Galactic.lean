import RegisterGravity.Chain
import Mathlib.Order.Interval.Finset.Nat

/-!
# The galactic scale: the string (Sec. IV.C)

The shift of the horizon and the area deficit, both from the solution about a mass; the entropy a
mass removes, from the horizon and within a sphere; the entropy inside a sphere; the crossing;
Verlinde's elastic response with the register's counts; the deep-regime law; and why the
temperature cannot lead.  The inputs are the named hypotheses of each theorem (see `Chain.lean`).
-/

open Real

namespace Register
namespace Reg

variable (R : Reg)

/-- the flip rate of a mass, `α = M/m_c` -/
noncomputable def α (M : ℝ) : ℝ := M / R.mc

/-- **The horizon is drawn in by `GM/c²`**, exactly to first order.  With the boundary condition of
`deSitter`, the solution with the mass has, at `R_Λ − ε` with `ε = GM/c²`,
`f = −ε²(3R_Λ − ε)/(R_Λ²(R_Λ − ε))`, which is `O(ε²)`. -/
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

/-- `GM/c² = ℓ_c α/π`: the mass draws the horizon in by `α/π` cells (Sec. IV.C). -/
theorem shift_in_cells (G M : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G * M / R.c ^ 2 = R.ℓc * R.α M / R.pi := by
  reg_facts R
  rw [(R.G_eq G hJ).1]
  unfold α mc
  field_simp

/-- **The entropy a mass removes**, Eq. (SM): the circumference loses `2α` cells, the entropy is the
square of the circumference in cells over four, so the loss is `(L/2)·2α = Lα`; and
`Lα = Mc²/k_B T_dS = 2πMcR_Λ/ℏ` with I1 for `T_dS`. -/
theorem entropy_removed (M T : ℝ) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) :
    (R.L / 2) * (2 * R.α M) = R.L * R.α M ∧
    R.L * R.α M = M * R.c ^ 2 / (R.kB * T) ∧
    R.L * R.α M = 2 * R.pi * M * R.c * R.RL / R.ℏ := by
  reg_facts R
  have h := (R.T_dS T I1).2
  refine ⟨by ring, ?_, ?_⟩
  · rw [h]; unfold α mc RL; field_simp
  · unfold α mc RL; field_simp

/-- **The temperature floor** (Sec. IV.C): no ring has more than `L` cells, so the ring
`L_a = 2πc²/aℓ_c` of a held observer satisfies `L_a ≤ L` exactly when `a ≥ c²/R_Λ`. -/
theorem temperature_floor (a : ℝ) (ha : 0 < a) : R.La a ≤ R.L ↔ R.c ^ 2 / R.RL ≤ a := by
  reg_facts R
  have e1 : R.La a = (2 * R.pi * R.c ^ 2) / (a * R.ℓc) := rfl
  have e2 : R.c ^ 2 / R.RL = (2 * R.pi * R.c ^ 2) / (R.L * R.ℓc) := by unfold RL; field_simp
  rw [e1, e2, div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  constructor
  · intro h
    calc 2 * R.pi * R.c ^ 2 ≤ R.L * (a * R.ℓc) := h
      _ = a * (R.L * R.ℓc) := by ring
  · intro h
    calc 2 * R.pi * R.c ^ 2 ≤ a * (R.L * R.ℓc) := h
      _ = R.L * (a * R.ℓc) := by ring

/-- the entropy the mass removes within a sphere of radius `r`, `S_M(r) = 2πMcr/ℏ = 2πnα` -/
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
slowly than it would in flat space, `8πr`, by a rate between `8πGM/c²` and `8πGM/c²√f`: to first
order in `GM/c²r`, by `8πGM/c²` at every radius.  Over the geodesic distance `r` from the mass the
sphere has therefore lost the area `8πGMr/c²`. -/
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

/-- **The entropy a mass removes within a sphere**, `S_M(r)`: the area `8πGMr/c²` that the sphere
at geodesic distance `r` has lost (`area_deficit`) is, at a ring's share `4ℓ_c²/π`, `2πnα` rings,
Verlinde's Eq. (28) in cells. -/
theorem removed_rings (G M r : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    8 * R.pi * G * M / R.c ^ 2 * r / R.ringShare = R.SM M r ∧
    R.SM M r = 2 * R.pi * R.n r * R.α M := by
  reg_facts R
  refine ⟨?_, R.SM_in_cells M r⟩
  rw [R.shares.2, (R.G_eq G hJ).1]
  unfold SM
  field_simp; ring

/-- **The string's share** (Sec. IV.C), from Postulate 1.  The sense of motion that is a string's
entropy is carried by every bit alike, so the string's one unit is spread evenly over its cells.
Of the `m` cells between the body and the horizon, numbered `1, …, m` from the body, the first `n`
lie inside the sphere, and they hold the share `n/m`. -/
theorem string_share (m n : ℕ) (hn : n ≤ m) :
    (((Finset.Icc 1 m).filter (fun k => k ≤ n)).card : ℝ) / ((Finset.Icc 1 m).card : ℝ)
      = (n : ℝ) / m := by
  have h1 : (Finset.Icc 1 m).filter (fun k => k ≤ n) = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h1, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel, Nat.add_sub_cancel]

/-- the entropy the sphere's strings hold inside it: the share `κn/L` of each of its strings, which
run from the body to the horizon (Sec. IV.C); `κ = 4` puts the horizon a quarter lap, `L/4` cells,
from the body (`Sin_share`), and `κ = 2π` is Verlinde's flat ball -/
noncomputable def Sin (κ r : ℝ) : ℝ := (κ * R.n r / R.L) * R.Ns r

/-- With `m = L/4` cells from the body to the horizon, the quarter lap, the share `n/m` of
`string_share` is the fraction `4n/L` of `Sin 4`. -/
theorem Sin_share (r : ℝ) : R.Sin 4 r = (R.n r / (R.L / 4)) * R.Ns r := by
  reg_facts R
  unfold Sin
  field_simp

/-- **Eq. (volume)**: with `κ = 4`, `S_in(r) = 4π²n³/L`, a volume law. -/
theorem Sin_eq (κ r : ℝ) : R.Sin κ r = κ * R.pi ^ 2 * R.n r ^ 3 / R.L := by
  reg_facts R
  unfold Sin
  rw [(R.bulk_counts r).2]
  field_simp

/-- **The crossing**, Eq. (criterion): `S_M(r) = S_in(r)` (with `κ = 4`) exactly when
`n² = Lα/2π`; there `N_s = πLα/2` and `g_N = GM/r² = c²/πR_Λ`. -/
theorem crossing (G M r : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    (R.SM M r = R.Sin 4 r ↔ R.n r ^ 2 = R.L * R.α M / (2 * R.pi)) ∧
    (R.n r ^ 2 = R.L * R.α M / (2 * R.pi) →
      R.Ns r = R.pi * R.L * R.α M / 2 ∧ G * M / r ^ 2 = R.c ^ 2 / (R.pi * R.RL)) := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  have hn : 0 < R.n r := by unfold n; positivity
  have hn' : R.n r ≠ 0 := hn.ne'
  have hα : 0 < R.α M := by unfold α mc; positivity
  rw [R.SM_in_cells, R.Sin_eq]
  constructor
  · constructor
    · intro h
      -- `2πnα = 4π²n³/L` gives `n (2παL − 4π²n²) = 0`, and `n ≠ 0`
      have h' : 2 * R.pi * R.n r * R.α M * R.L = 4 * R.pi ^ 2 * R.n r ^ 3 := by
        rw [h]; field_simp
      have h0 : R.n r * (2 * R.pi * R.α M * R.L - 4 * R.pi ^ 2 * R.n r ^ 2) = 0 := by
        linear_combination h'
      rcases mul_eq_zero.1 h0 with h0 | h0
      · exact absurd h0 hn'
      · rw [eq_div_iff (by positivity)]
        have key : R.n r ^ 2 * (2 * R.pi) * (2 * R.pi) = R.L * R.α M * (2 * R.pi) := by
          linear_combination (-1 : ℝ) * h0
        exact mul_right_cancel₀ (by positivity) key
    · intro h
      rw [show R.n r ^ 3 = R.n r * R.n r ^ 2 by ring, h]
      field_simp; ring
  · intro h
    constructor
    · rw [(R.bulk_counts r).2, h]; field_simp
    · have hr2 : r ^ 2 = R.ℓc ^ 2 * (R.L * R.α M / (2 * R.pi)) := by
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
noncomputable def slope (κ M : ℝ) : ℝ := 8 * R.α M * R.L * R.ℓc ^ 2 / (3 * κ)
/-- the surface gravity of the horizon, `a_Λ = c²/R_Λ` -/
noncomputable def aΛ : ℝ := R.c ^ 2 / R.RL
/-- the galactic acceleration for the string fraction `κ n/L`: `a_M = πc²/(3κR_Λ)` -/
noncomputable def aM (κ : ℝ) : ℝ := R.pi * R.c ^ 2 / (3 * κ * R.RL)

/-- `V_0 = 4Lℓ_c³/(3πκ)`; with `κ = 4`, `V_0 = Lℓ_c³/3π` (Sec. IV.C). -/
theorem V0_eq (κ r : ℝ) (hκ : κ ≠ 0) (hr : 0 < r) :
    R.V0 κ r = 4 * R.L * R.ℓc ^ 3 / (3 * R.pi * κ) ∧ R.V0 4 r = R.L * R.ℓc ^ 3 / (3 * R.pi) := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  constructor
  · unfold V0 V; rw [R.Sin_eq]; unfold n; field_simp
  · unfold V0 V; rw [R.Sin_eq]; unfold n; field_simp

/-- `V_M` is linear in `r`, with the slope `8αLℓ_c²/3κ`. -/
theorem VM_linear (κ M r : ℝ) (hκ : κ ≠ 0) (hr : 0 < r) :
    R.VM κ M r = R.slope κ M * r := by
  reg_facts R
  unfold VM slope
  rw [(R.V0_eq κ r hκ hr).1, R.SM_in_cells]
  unfold n
  field_simp; ring

/-- **Eq. (aM)**: from I5 (`ε²A = dV_M/dr`, equality under the principal-strain assumption) and I6
(`Σ_D = (a_Λ/8πG) ε`, with `Σ_D = M_D/4πr²` the apparent mass `M_D` per unit area of the sphere),
the field `g_D` of the apparent mass satisfies, by Gauss's law (`gauss`), `g_D² = a_M g_N`, with
`g_N` the field of the mass and `a_M = πc²/(3κR_Λ)`. -/
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
satisfies `M_D² = M²n²·π³/6Lα`, so `M_D = Mn√(π³/6Lα)` grows by a fixed amount per cell of
distance. -/
theorem apparent_mass (G M MD r ε : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I5 : ε ^ 2 * (4 * R.pi * r ^ 2) = R.slope 4 M)
    (I6 : MD / (4 * R.pi * r ^ 2) = (R.aΛ / (8 * R.pi * G)) * ε) :
    MD ^ 2 = M ^ 2 * R.n r ^ 2 * (R.pi ^ 3 / (6 * R.L * R.α M)) := by
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
