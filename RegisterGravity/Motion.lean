import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Circular orbits (Sec. IV.C)

A rotation curve is the speed of the bodies on circular orbits about a galaxy, at each radius.
Matter that moves freely, as dust, moves on geodesics (`Einstein.flow_geodesic`), and in a static weak field a
slow body on a geodesic has the acceleration of the field, `g` toward the center
(`Sources.Geometry.newtonian_motion`).  On the circle of radius `r` traversed at the speed `v` the
acceleration is `v²/r` toward the center (`accel_circle`), so `v² = gr` (`circular_speed`).
-/

open Real

namespace Register.Motion

/-- **The circular orbit** of radius `r` traversed at the speed `v`, in the plane of the orbit with
the center at the origin: `t ↦ (r cos(vt/r), r sin(vt/r))`. -/
noncomputable def circle (r v t : ℝ) : ℝ × ℝ := (r * cos (v / r * t), r * sin (v / r * t))

/-- the velocity on the circle -/
lemma hasDerivAt_circle (r v t : ℝ) :
    HasDerivAt (circle r v)
      (-(r * (v / r)) * sin (v / r * t), r * (v / r) * cos (v / r * t)) t := by
  have hc := ((hasDerivAt_id' t).const_mul (v / r)).cos.const_mul r
  have hs := ((hasDerivAt_id' t).const_mul (v / r)).sin.const_mul r
  simp only [mul_one] at hc hs
  refine (hc.prodMk hs).congr_deriv ?_
  simp only [Prod.mk.injEq]
  constructor <;> ring

lemma deriv_circle (r v : ℝ) :
    deriv (circle r v) =
      fun t => (-(r * (v / r)) * sin (v / r * t), r * (v / r) * cos (v / r * t)) :=
  funext fun t => (hasDerivAt_circle r v t).deriv

/-- **The acceleration on the circle** is `−(v/r)²` times the position: `v²/r` toward the
center. -/
theorem accel_circle (r v t : ℝ) :
    deriv (deriv (circle r v)) t = (-(v / r) ^ 2) • circle r v t := by
  rw [deriv_circle]
  have hc := ((hasDerivAt_id' t).const_mul (v / r)).sin.const_mul (-(r * (v / r)))
  have hs := ((hasDerivAt_id' t).const_mul (v / r)).cos.const_mul (r * (v / r))
  simp only [mul_one] at hc hs
  rw [(hc.prodMk hs).deriv]
  simp only [circle, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

/-- **On a circular orbit with the acceleration of the field, `v² = gr`** (Sec. IV.C): if a body on
the circle of radius `r > 0` at the speed `v` has the acceleration `g` toward the center at every
time, then at the time `0`, where it is at `(r, 0)`, `−(v/r)² r = −(g/r) r`, so `v² = gr`. -/
theorem circular_speed {r v g : ℝ} (hr : 0 < r)
    (h : ∀ t, deriv (deriv (circle r v)) t = (-(g / r)) • circle r v t) : v ^ 2 = g * r := by
  have e := h 0
  rw [accel_circle] at e
  have e1 := congrArg Prod.fst e
  simp only [circle, mul_zero, cos_zero, Prod.smul_mk, smul_eq_mul, mul_one] at e1
  field_simp at e1
  nlinarith [e1, hr]

end Register.Motion
