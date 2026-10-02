import RegisterGravity.Chain
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The strings of a sphere, from the symmetry of space (Sec. II, "Counting in the bulk")

Earlier versions of the paper listed the area law of a screen, that a sphere holds one string for
each ring's share of its area, as a reading of the postulates.  Here it is derived from the
symmetry of space, the input Sec. II names, in the form that input takes once a ring is a closed
geodesic of the solution (Sec. IV.D): a ring is a great circle of the three-sphere of radius `R_Λ`,
and no direction is preferred at any point; rotations about one point after another carry any
point to any other, so no point is preferred either.  So the fraction of the rings that pass within
angular distance `θ` of a point is the same at every point and equals its average over the
three-sphere; counted ring by ring, since a point is within `θ` of a ring exactly when the ring
passes within `θ` of the point, that average is the share of the three-sphere's volume within `θ`
of a great circle (hypothesis `hsym`, for `θ` up to `π/2`, the farthest a point is from a great
circle).  The rings within `θ` of the body's cell are those that cross the sphere of angular radius
`θ` about it.  The share is `sin²θ` (`tube_fraction`), and the sphere of
angular radius `θ` has the areal radius `R_Λ sin θ`, so the sphere of areal radius `r` holds
`R_hor (r/R_Λ)²` strings, which is `Ns r`, Eq. (N) (`strings_from_symmetry`), and the strings per
unit area are the same on every sphere (`density_uniform`).  At `θ = π/2`, the horizon, every ring
is counted, as Postulate 2 gives on its own (`Horizon.Positions.horizon_weight_ring`,
`Bridge.horizon_entropy_count`).  `tube_model` shows that the hypotheses can all be met, so no
theorem here holds vacuously.

The geometry of the three-sphere enters as the hypotheses `hV0`, `hcont` and `hV` of
`tube_volume`: in Hopf coordinates `(cos t e^{iα}, sin t e^{iβ})`, `0 ≤ t ≤ π/2`, the points at
angular distance `t` from the great circle `{(e^{iα}, 0)}` form a flat torus of radii `R_Λ cos t` and
`R_Λ sin t`, of area `4π²R_Λ² cos t sin t` (`torusArea`), and the volume within `t` grows at that
area times the thickness `R_Λ dt`, up to `t = π/2`, where it is the whole three-sphere.  It is classical, taken as known like the closed geodesics of de Sitter space
(`DeSitter.horizon_radius`); what is proved is that it makes the fraction `sin²θ`.
-/

open Real Set

namespace Register
namespace Reg

variable (R : Reg)

/-- the area of the torus of the three-sphere of radius `R_Λ` at angular distance `t` from a great
circle, a flat torus of radii `R_Λ cos t` and `R_Λ sin t`: `(2πR_Λ cos t)(2πR_Λ sin t)` -/
noncomputable def torusArea (t : ℝ) : ℝ := 4 * R.pi ^ 2 * R.RL ^ 2 * (Real.cos t * Real.sin t)

/-- **The volume within angular distance `θ` of a great circle** (the tube), `0 ≤ θ ≤ π/2`.  Any
`V` with `V(0) = 0`, continuous on `[0, π/2]`, that grows inside it at the torus's area times the
thickness `R_Λ dt` is `2π²R_Λ³ sin²θ`: the difference from that function has derivative `0` and
vanishes at `0`. -/
theorem tube_volume (V : ℝ → ℝ) (hV0 : V 0 = 0) (hcont : ContinuousOn V (Icc 0 (Real.pi / 2)))
    (hV : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivAt V (R.RL * R.torusArea t) t)
    (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    V θ = 2 * R.pi ^ 2 * R.RL ^ 3 * Real.sin θ ^ 2 := by
  have hWd : ∀ t, HasDerivAt (fun y => 2 * R.pi ^ 2 * R.RL ^ 3 * Real.sin y ^ 2)
      (R.RL * R.torusArea t) t := by
    intro t
    have h := ((Real.hasDerivAt_sin t).fun_pow 2).const_mul (2 * R.pi ^ 2 * R.RL ^ 3)
    convert h using 1
    unfold torusArea
    push_cast
    ring
  rcases eq_or_lt_of_le hθ.1 with h0 | hpos
  · rw [← h0, hV0, Real.sin_zero]
    ring
  · have hg : ∀ t ∈ Ioo 0 θ,
        HasDerivAt (fun y => V y - 2 * R.pi ^ 2 * R.RL ^ 3 * Real.sin y ^ 2) 0 t := by
      intro t ht
      have := (hV t ⟨ht.1, lt_of_lt_of_le ht.2 hθ.2⟩).fun_sub (hWd t)
      rwa [sub_self] at this
    have hcont' : ContinuousOn (fun y => V y - 2 * R.pi ^ 2 * R.RL ^ 3 * Real.sin y ^ 2)
        (Icc 0 θ) :=
      (hcont.mono (Icc_subset_Icc le_rfl hθ.2)).sub
        (continuous_const.mul (Real.continuous_sin.pow 2)).continuousOn
    obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope
      (fun y => V y - 2 * R.pi ^ 2 * R.RL ^ 3 * Real.sin y ^ 2) (fun _ => (0 : ℝ)) hpos hcont' hg
    have h := hξ.symm
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · rw [hV0, Real.sin_zero] at h
      linear_combination h
    · exact absurd h (by linarith)

/-- **The fraction of the three-sphere within angular distance `θ` of a great circle is `sin²θ`**,
`0 ≤ θ ≤ π/2`: the tube of angular radius `π/2` is the whole three-sphere, `2π²R_Λ³`. -/
theorem tube_fraction (V : ℝ → ℝ) (hV0 : V 0 = 0) (hcont : ContinuousOn V (Icc 0 (Real.pi / 2)))
    (hV : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivAt V (R.RL * R.torusArea t) t)
    (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    V (Real.pi / 2) = 2 * R.pi ^ 2 * R.RL ^ 3 ∧ V θ / V (Real.pi / 2) = Real.sin θ ^ 2 := by
  reg_facts R
  have hRL := R.RL_pos
  have hhalf : Real.pi / 2 ∈ Icc 0 (Real.pi / 2) := ⟨by positivity, le_rfl⟩
  have htot : V (Real.pi / 2) = 2 * R.pi ^ 2 * R.RL ^ 3 := by
    rw [R.tube_volume V hV0 hcont hV (Real.pi / 2) hhalf, Real.sin_pi_div_two]
    ring
  refine ⟨htot, ?_⟩
  have hRL' := hRL.ne'
  rw [htot, R.tube_volume V hV0 hcont hV θ hθ]
  field_simp

/-- **The strings of a sphere, from the symmetry of space** (Sec. II, "Counting in the bulk").
`rings θ` is the number of the register's largest rings that pass within angular distance `θ` of
the body's cell, `0 ≤ θ ≤ π/2`, that is, that cross the sphere of angular radius `θ` about it (a
great circle meets the ball in one arc, so it crosses the sphere twice, `Nc`).  The symmetry of
space is the hypothesis `hsym`: a ring is a great circle of the three-sphere of radius `R_Λ`
(Sec. IV.D), and no direction is preferred at any point, hence no point either (rotations about
one point after another carry any point to any other), so the fraction of the rings within `θ` of
a point is the same at every point and equals its average over the three-sphere, which,
counted ring by ring, is the share `V θ / V (π/2)` of its volume within `θ` of a great circle
(`tube_volume`).  Then the sphere of angular radius `θ`, whose areal radius is `r = R_Λ sin θ`,
holds `R_hor sin²θ = R_hor (r/R_Λ)²` strings, which is `Ns r`, Eq. (N): the area law of a screen,
derived.  At `θ = π/2`, the horizon, every ring is counted, as Postulate 2 gives on its own
(`Bridge.horizon_entropy_count`). -/
theorem strings_from_symmetry (V rings : ℝ → ℝ) (hV0 : V 0 = 0)
    (hcont : ContinuousOn V (Icc 0 (Real.pi / 2)))
    (hV : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivAt V (R.RL * R.torusArea t) t)
    (hsym : ∀ θ ∈ Icc 0 (Real.pi / 2), rings θ = R.Rhor * (V θ / V (Real.pi / 2)))
    (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    rings θ = R.Rhor * Real.sin θ ^ 2 ∧ rings θ = R.Ns (R.RL * Real.sin θ) ∧
    rings (Real.pi / 2) = R.Rhor := by
  reg_facts R
  have hRL := R.RL_pos
  have hhalf : Real.pi / 2 ∈ Icc 0 (Real.pi / 2) := ⟨by positivity, le_rfl⟩
  have h1 : rings θ = R.Rhor * Real.sin θ ^ 2 := by
    rw [hsym θ hθ, (R.tube_fraction V hV0 hcont hV θ hθ).2]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, (R.ratio_of_areas (R.RL * Real.sin θ)).1, mul_div_cancel_left₀ _ hRL.ne']
  · rw [hsym _ hhalf, (R.tube_fraction V hV0 hcont hV (Real.pi / 2) hhalf).2,
      Real.sin_pi_div_two]
    ring

/-- **The strings per unit area are the same on every sphere** (Sec. II; Sec. III uses it on every
local horizon): with `strings_from_symmetry`, the sphere of angular radius `θ`, of area
`4πR_Λ² sin²θ`, holds `R_hor/A_hor` strings per unit area, one for each ring's share `4ℓ_c²/π`,
whatever `θ` is in `(0, π/2]`. -/
theorem density_uniform (V rings : ℝ → ℝ) (hV0 : V 0 = 0)
    (hcont : ContinuousOn V (Icc 0 (Real.pi / 2)))
    (hV : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivAt V (R.RL * R.torusArea t) t)
    (hsym : ∀ θ ∈ Icc 0 (Real.pi / 2), rings θ = R.Rhor * (V θ / V (Real.pi / 2)))
    (θ : ℝ) (hθ : θ ∈ Ioc 0 (Real.pi / 2)) :
    rings θ / (4 * R.pi * (R.RL * Real.sin θ) ^ 2) = R.Rhor / R.Ahor ∧
    rings θ / (4 * R.pi * (R.RL * Real.sin θ) ^ 2) = 1 / R.ringShare := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  have hRh : R.Rhor ≠ 0 := by unfold Rhor; positivity
  have hs : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).ne'
  rw [(R.strings_from_symmetry V rings hV0 hcont hV hsym θ ⟨hθ.1.le, hθ.2⟩).1]
  constructor
  · unfold Ahor
    field_simp
  · unfold ringShare Ahor
    field_simp

/-- the volume of the three-sphere of radius `R_Λ` within angular distance `t ≤ π/2` of a great
circle, `2π²R_Λ³ sin²t` -/
noncomputable def tubeVol (t : ℝ) : ℝ := 2 * R.pi ^ 2 * R.RL ^ 3 * Real.sin t ^ 2

/-- **The hypotheses are met**, so no theorem above holds vacuously: `tubeVol` vanishes at `0`, is
continuous, and grows at the torus's area times `R_Λ`; and the count `R_hor sin²θ` meets `hsym`
with it. -/
theorem tube_model :
    R.tubeVol 0 = 0 ∧ ContinuousOn R.tubeVol (Icc 0 (Real.pi / 2)) ∧
    (∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivAt R.tubeVol (R.RL * R.torusArea t) t) ∧
    (∀ θ ∈ Icc 0 (Real.pi / 2),
      R.Rhor * Real.sin θ ^ 2 = R.Rhor * (R.tubeVol θ / R.tubeVol (Real.pi / 2))) := by
  reg_facts R
  have hRL := R.RL_pos
  have hd : ∀ t, HasDerivAt R.tubeVol (R.RL * R.torusArea t) t := by
    intro t
    have h := ((Real.hasDerivAt_sin t).fun_pow 2).const_mul (2 * R.pi ^ 2 * R.RL ^ 3)
    have e : R.tubeVol = fun y => 2 * R.pi ^ 2 * R.RL ^ 3 * Real.sin y ^ 2 := rfl
    rw [e]
    convert h using 1
    unfold torusArea
    push_cast
    ring
  refine ⟨by simp [tubeVol], fun t _ => (hd t).continuousAt.continuousWithinAt,
    fun t _ => hd t, ?_⟩
  intro θ _
  have hRL' := hRL.ne'
  unfold tubeVol
  rw [Real.sin_pi_div_two]
  field_simp

end Reg
end Register
