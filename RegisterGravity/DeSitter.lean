import RegisterGravity.Galactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# The de Sitter solution: the horizon a quarter lap out, and the horizon drawn in by a mass

Two properties of the solution of `Chain.lean` that Sec. IV.C uses, derived from it.

* `proper_distance`: in de Sitter space (the boundary condition `hdS`, no mass) the proper distance
  from the observer along a radial line, the function `s` with `s(0) = 0` and `ds/dr = 1/√f` (the
  radial part `dr²/f` of the metric), reaches the horizon at `s(R_Λ) = πR_Λ/2`, which by
  Eq. (ident) is `Lℓ_c/4`, a quarter of a largest ring.  `R_Λ arcsin(r/R_Λ)` is such a function
  (`proper_distance_exists`), and every such function agrees with it at the horizon.
* `sds_outer_horizon`: with a mass, `ε = GM/c²` and `13ε < R_Λ`, the solution has a horizon between
  `R_Λ − ε − 2ε²/R_Λ` and `R_Λ − ε`, and none at or beyond `R_Λ − ε`: the outer horizon lies at
  `R_Λ − GM/c²` to first order in `M`.
-/

open Real Set

namespace Register
namespace Reg

variable (R : Reg)

/-- Without a mass, and with the boundary condition, the solution is `f(r) = 1 − r²/R_Λ²`. -/
lemma fdS_eq (G Λ r : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.fSdS G 0 Λ r = 1 - r ^ 2 / R.RL ^ 2 := by
  have hRL := R.RL_pos.ne'
  rw [(R.deSitter G Λ).1 hdS]
  unfold fSdS
  simp only [mul_zero, zero_div, sub_zero]
  field_simp

/-- the proper distance from the observer in de Sitter space, `s(r) = R_Λ arcsin(r/R_Λ)` -/
noncomputable def sdS (r : ℝ) : ℝ := R.RL * Real.arcsin (r / R.RL)

lemma continuous_sdS : Continuous R.sdS :=
  continuous_const.mul (Real.continuous_arcsin.comp (continuous_id.div_const _))

lemma hasDerivAt_sdS (r : ℝ) (hr0 : 0 < r) (hr : r < R.RL) :
    HasDerivAt R.sdS (1 / Real.sqrt (1 - r ^ 2 / R.RL ^ 2)) r := by
  have hRL := R.RL_pos
  have h1 : r / R.RL ≠ -1 := by
    intro h
    have : 0 < r / R.RL := div_pos hr0 hRL
    linarith
  have h2 : r / R.RL ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq hRL.ne'] at h
    linarith
  have hd := ((Real.hasDerivAt_arcsin h1 h2).comp r ((hasDerivAt_id r).div_const R.RL)).const_mul
    R.RL
  have e : R.sdS = fun y => R.RL * (Real.arcsin ∘ fun x => id x / R.RL) y := by
    funext y; rfl
  rw [e]
  convert hd using 1
  rw [div_pow]
  field_simp

/-- **The proper distance exists**: `s(r) = R_Λ arcsin(r/R_Λ)` starts at `0`, is continuous up to
the horizon, and has `ds/dr = 1/√f` inside it. -/
theorem proper_distance_exists (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.sdS 0 = 0 ∧ ContinuousOn R.sdS (Icc 0 R.RL) ∧
    ∀ r ∈ Ioo 0 R.RL, HasDerivAt R.sdS (1 / Real.sqrt (R.fSdS G 0 Λ r)) r := by
  refine ⟨by simp [sdS], R.continuous_sdS.continuousOn, ?_⟩
  intro r hr
  rw [R.fdS_eq G Λ r hdS]
  exact R.hasDerivAt_sdS r hr.1 hr.2

/-- **The horizon is a quarter lap out** (Sec. IV.C).  In de Sitter space the proper distance from
the observer along a radial line, any `s` with `s(0) = 0`, continuous up to the horizon, and
`ds/dr = 1/√f` inside it, reaches the horizon at `s(R_Λ) = πR_Λ/2`; with the register's `π` the
real one, that is `Lℓ_c/4`, a quarter of a largest ring (`quarter_lap`). -/
theorem proper_distance (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) (s : ℝ → ℝ) (hs0 : s 0 = 0)
    (hcont : ContinuousOn s (Icc 0 R.RL))
    (hds : ∀ r ∈ Ioo 0 R.RL, HasDerivAt s (1 / Real.sqrt (R.fSdS G 0 Λ r)) r) :
    s R.RL = Real.pi * R.RL / 2 ∧ (R.pi = Real.pi → s R.RL = R.L * R.ℓc / 4) := by
  have hRL := R.RL_pos
  obtain ⟨h0, hc0, hd0⟩ := R.proper_distance_exists G Λ hdS
  -- `s − s₀` has derivative `0` inside, so it does not change from `0` to `R_Λ`
  have hg : ∀ r ∈ Ioo 0 R.RL, HasDerivAt (fun y => s y - R.sdS y) 0 r := by
    intro r hr
    have := (hds r hr).fun_sub (hd0 r hr)
    rwa [sub_self] at this
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope (fun y => s y - R.sdS y) (fun _ => (0 : ℝ))
    hRL (hcont.sub hc0) hg
  have hsame : s R.RL - R.sdS R.RL = s 0 - R.sdS 0 := by
    have h := hξ.symm
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith
    · exact absurd h (by linarith)
  have hval : s R.RL = Real.pi * R.RL / 2 := by
    rw [hs0, h0] at hsame
    have : R.sdS R.RL = Real.pi * R.RL / 2 := by
      unfold sdS
      rw [div_self hRL.ne', Real.arcsin_one]
      ring
    linarith
  refine ⟨hval, fun hpi => ?_⟩
  rw [hval, ← hpi]
  exact R.quarter_lap

/-- With the boundary condition, `f(r)·R_Λ²r = R_Λ²r − 2εR_Λ² − r³`, with `ε = GM/c²`. -/
lemma fSdS_mul (G M Λ r : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) (hr : r ≠ 0) :
    R.fSdS G M Λ r * (R.RL ^ 2 * r)
      = R.RL ^ 2 * r - 2 * (G * M / R.c ^ 2) * R.RL ^ 2 - r ^ 3 := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  rw [(R.deSitter G Λ).1 hdS]
  unfold fSdS
  field_simp

/-- **The outer horizon with a mass** (Sec. IV.C).  With `ε = GM/c²` and `13ε < R_Λ`, the solution
about the mass has a horizon between `R_Λ − ε − 2ε²/R_Λ` and `R_Λ − ε`, and `f < 0` at and beyond
`R_Λ − ε`, so there is no horizon farther out: the outer horizon lies at `R_Λ − GM/c²` to first
order in `M`, within `2ε²/R_Λ`. -/
theorem sds_outer_horizon (G M Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0)
    (hε : 0 < G * M / R.c ^ 2) (h13 : 13 * (G * M / R.c ^ 2) < R.RL) :
    (∃ r ∈ Ioo (R.RL - G * M / R.c ^ 2 - 2 * (G * M / R.c ^ 2) ^ 2 / R.RL)
        (R.RL - G * M / R.c ^ 2), R.fSdS G M Λ r = 0) ∧
    ∀ r, R.RL - G * M / R.c ^ 2 ≤ r → R.fSdS G M Λ r < 0 := by
  have hRL := R.RL_pos
  set ε := G * M / R.c ^ 2 with hεdef
  set Rr := R.RL with hRr
  set a := Rr - ε - 2 * ε ^ 2 / Rr with ha
  set b := Rr - ε with hb
  -- where the polynomial `P(r) = R_Λ²r − 2εR_Λ² − r³` is negative, so is `f`
  have hfneg : ∀ r, 0 < r → Rr ^ 2 * r - 2 * ε * Rr ^ 2 - r ^ 3 < 0 → R.fSdS G M Λ r < 0 := by
    intro r hr hP
    have h := R.fSdS_mul G M Λ r hdS hr.ne'
    rw [← hεdef, ← hRr] at h
    have hpos : 0 < Rr ^ 2 * r := by positivity
    by_contra hge
    push Not at hge
    have : 0 ≤ R.fSdS G M Λ r * (Rr ^ 2 * r) := mul_nonneg hge hpos.le
    linarith
  have hfpos : ∀ r, 0 < r → 0 < Rr ^ 2 * r - 2 * ε * Rr ^ 2 - r ^ 3 → 0 < R.fSdS G M Λ r := by
    intro r hr hP
    have h := R.fSdS_mul G M Λ r hdS hr.ne'
    rw [← hεdef, ← hRr] at h
    have hpos : 0 < Rr ^ 2 * r := by positivity
    by_contra hle
    push Not at hle
    have : R.fSdS G M Λ r * (Rr ^ 2 * r) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hpos.le
    linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  -- `P` at `R_Λ − ε` is `−ε²(3R_Λ − ε) < 0`
  have hPb : Rr ^ 2 * b - 2 * ε * Rr ^ 2 - b ^ 3 < 0 := by
    have e : Rr ^ 2 * b - 2 * ε * Rr ^ 2 - b ^ 3 = -(ε ^ 2 * (3 * Rr - ε)) := by rw [hb]; ring
    rw [e]
    have : 0 < ε ^ 2 * (3 * Rr - ε) := mul_pos (by positivity) (by linarith)
    linarith
  -- `P` at `R_Λ − ε − 2ε²/R_Λ` is positive
  have ha0 : 0 < a := by
    have h1 : 2 * ε ^ 2 / Rr < ε := by
      rw [div_lt_iff₀ hRL]; nlinarith
    rw [ha]; linarith
  have hPa : 0 < Rr ^ 2 * a - 2 * ε * Rr ^ 2 - a ^ 3 := by
    have e : (Rr ^ 2 * a - 2 * ε * Rr ^ 2 - a ^ 3) * Rr
        = ε ^ 2 * (Rr ^ 2 - 12 * ε * Rr - 12 * ε ^ 2) + Rr * (ε + 2 * ε ^ 2 / Rr) ^ 3 := by
      rw [ha]; field_simp; ring
    have h1 : 0 < ε ^ 2 * (Rr ^ 2 - 12 * ε * Rr - 12 * ε ^ 2) := by
      apply mul_pos (by positivity)
      nlinarith
    have h2 : 0 < Rr * (ε + 2 * ε ^ 2 / Rr) ^ 3 := by positivity
    have h3 : 0 < (Rr ^ 2 * a - 2 * ε * Rr ^ 2 - a ^ 3) * Rr := by rw [e]; linarith
    exact pos_of_mul_pos_left h3 hRL.le
  have hab : a ≤ b := by
    rw [ha, hb]
    have : 0 ≤ 2 * ε ^ 2 / Rr := by positivity
    linarith
  refine ⟨?_, ?_⟩
  · -- the intermediate value theorem on `[a, b]`
    have hcont : ContinuousOn (R.fSdS G M Λ) (Icc a b) := by
      intro r hr
      have hr0 : r ≠ 0 := (lt_of_lt_of_le ha0 hr.1).ne'
      exact (R.hasDerivAt_fSdS G M Λ r hr0).continuousAt.continuousWithinAt
    have hmem : (0 : ℝ) ∈ Ioo (R.fSdS G M Λ b) (R.fSdS G M Λ a) :=
      ⟨hfneg b hb0 hPb, hfpos a ha0 hPa⟩
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hab hcont hmem
    exact ⟨r, hr, hr0⟩
  · -- beyond `R_Λ − ε`, `P` decreases
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hb0 hr
    apply hfneg r hr0
    have hb12 : 12 * Rr < 13 * b := by rw [hb]; linarith
    have key : (Rr ^ 2 * r - 2 * ε * Rr ^ 2 - r ^ 3) - (Rr ^ 2 * b - 2 * ε * Rr ^ 2 - b ^ 3)
        = (r - b) * (Rr ^ 2 - (r ^ 2 + r * b + b ^ 2)) := by ring
    have hsq : Rr ^ 2 < r ^ 2 + r * b + b ^ 2 := by nlinarith
    have hle : (r - b) * (Rr ^ 2 - (r ^ 2 + r * b + b ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith

/-- **The period of the horizon is the lap of the largest ring** (Sec. IV.D, the content of the
boundary condition).  With `hdS`, the field of the solution without a mass at the horizon is
`g(R_Λ) = −c²/R_Λ`, so the horizon's surface gravity is `a_Λ = c²/R_Λ`, here derived.  The ring
of an observer held at that acceleration, `L_a` of `Chain.lean`, whose lap time is the thermal
period `2πc/a` of his horizon, is the largest ring, `L_{a_Λ} = L`; so the period of the horizon,
`2πc/a_Λ = 2πR_Λ/c`, is the lap time `Lt_c` of the largest ring, Eq. (clock). -/
theorem horizon_period (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.gSdS G 0 Λ R.RL = -R.aΛ ∧ R.La R.aΛ = R.L ∧
    R.La R.aΛ * R.tc = 2 * R.pi * R.c / R.aΛ ∧ 2 * R.pi * R.c / R.aΛ = R.L * R.tc := by
  reg_facts R
  have hRL := R.RL_pos
  have haΛ : 0 < R.aΛ := by unfold aΛ; positivity
  refine ⟨?_, ?_, R.La_lap _ haΛ, ?_⟩
  · rw [R.gSdS_eq G 0 Λ R.RL hRL.ne', (R.deSitter G Λ).1 hdS]
    unfold aΛ
    field_simp
    ring
  · unfold La aΛ RL
    field_simp
  · rw [R.lap_time]
    unfold aΛ
    field_simp

/-- **Eq. (energy) from the boundary condition**: with `I1` for the ring of an observer held at
the horizon's surface gravity, which is the largest ring (`horizon_period`), the temperature of
the horizon is Unruh's at `a_Λ`, `ℏa_Λ/2πc`, and it is `E_c/L = ℏc/2πR_Λ`, the Gibbons–Hawking
temperature: `ℏ` over the lap time of the largest ring. -/
theorem horizon_temperature (G Λ T : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0)
    (I1 : R.kB * T = R.ℏ / (R.La R.aΛ * R.tc)) :
    R.kB * T = R.ℏ * R.aΛ / (2 * R.pi * R.c) ∧ R.kB * T = R.Ec / R.L ∧
    R.kB * T = R.ℏ * R.c / (2 * R.pi * R.RL) := by
  reg_facts R
  have hRL := R.RL_pos
  have haΛ : 0 < R.aΛ := by unfold aΛ; positivity
  have hL := (R.horizon_period G Λ hdS).2.1
  refine ⟨R.T_Unruh _ T haΛ I1, ?_⟩
  rw [hL] at I1
  exact R.T_dS T I1

/-- **The horizon's radius** (Sec. IV.D).  The solution without a mass has its horizon at `√(3/Λ)`,
given a horizon at all (`Λ > 0`, which the paper derives from the rings: the solutions with `Λ ≤ 0`
have no closed line of translation, and the files take it as the hypothesis `hΛ`).  Postulate 1
enters twice, as the register's own input, each time with a property of the solution's horizon.
A largest ring keeps its length, so it is at rest relative to its center, and nothing beyond the
horizon is at rest, so its radius `R_Λ` lies within that center's horizon, `f(R_Λ) ≥ 0` (`hrest`).
And the horizon's great circles are closed lines of translation, so they are rings, and no ring
has more than `L` cells: the circumference `2π√(3/Λ)` is at most `Lℓ_c` (`P1`).  Then the horizon
is at `R_Λ`: the hypothesis `hdS` of the chain follows, and with it `Λ = 3/R_Λ²`. -/
theorem horizon_radius (G Λ : ℝ) (hΛ : 0 < Λ) (hrest : 0 ≤ R.fSdS G 0 Λ R.RL)
    (P1 : 2 * R.pi * Real.sqrt (3 / Λ) ≤ R.L * R.ℓc) :
    R.fSdS G 0 Λ R.RL = 0 ∧ Λ = 3 / R.RL ^ 2 := by
  reg_facts R
  have hRL := R.RL_pos
  have h3 : (0 : ℝ) < 3 / Λ := by positivity
  -- from `hrest`: `R_Λ² ≤ 3/Λ`, so `R_Λ ≤ √(3/Λ)`
  have hsq : R.RL ^ 2 ≤ 3 / Λ := by
    unfold fSdS at hrest
    simp only [mul_zero, zero_div, sub_zero] at hrest
    rw [le_div_iff₀ hΛ]
    nlinarith
  have hle : R.RL ≤ Real.sqrt (3 / Λ) := Real.le_sqrt_of_sq_le hsq
  -- from `P1`: `√(3/Λ) ≤ Lℓ_c/2π = R_Λ`
  have hge : Real.sqrt (3 / Λ) ≤ R.RL := by
    unfold RL
    rw [le_div_iff₀ (by positivity)]
    linarith
  have heq : R.RL = Real.sqrt (3 / Λ) := le_antisymm hle hge
  have hRL2 : R.RL ^ 2 = 3 / Λ := by rw [heq, Real.sq_sqrt h3.le]
  refine ⟨?_, ?_⟩
  · unfold fSdS
    rw [hRL2]
    field_simp
    ring
  · rw [hRL2]
    field_simp

end Reg
end Register
