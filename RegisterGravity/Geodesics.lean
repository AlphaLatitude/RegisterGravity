import RegisterGravity.Crossing
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Module

/-!
# The closed geodesics of de Sitter space (Secs. II and IV.D)

Sec. IV.D finds the radius of the largest ring from the geometry of the solution without a mass.
By the last sentence of Postulate 2 a largest ring is a closed geodesic of space.  Without a mass
the geometry of space is the same at every slot (`Solution.geometry_same`, from the symmetry of
space, `Symmetry.lawAt_same`, the state the same at every crossing, and the thesis applied to the
geometry, `hgeom`), and `Space.lean` derives from it, with the rings, that the solution is de Sitter
space.  This file proves what the paper uses of the geometry of de Sitter space, that its closed
spacelike geodesics have one length and are great circles of its space at an instant.

The spacetimes here are quadrics of a space `T × E` of times `T` and places `E`, with the form
`−⟪t, t'⟫ + ⟪x, x'⟫` (`form`).  De Sitter space of radius `ρ` is `form X X = ρ²` with one time
(`T = ℝ`, `E = ℝ⁴`).  A geodesic of a quadric is a curve on it whose acceleration is normal to it, a
multiple of its position (`IsGeodesic`) [B. O'Neill, *Semi-Riemannian Geometry* (1983), Ch. 4].

* **De Sitter space** (`IsGeodesic.circle`, `IsGeodesic.hasLength`).  A spacelike geodesic keeps
  its speed, and its acceleration is `−ω²` times its position, so it runs on a circle of radius `ρ`
  in the plane of its starting point and its velocity, once in each period `2π/ω`: every closed
  spacelike geodesic has the length `2πρ`.
* **The hyperbola** (`hypCurve`, `hypCurve_geodesic`).  The curve `t ↦ (cosh t · a, sinh t · b)`
  with `‖a‖ = ‖b‖ = ℓ` is a geodesic of the quadric `form X X = −ℓ²`.  With one time the upper
  sheet of that quadric is hyperbolic space, and `Space.hyperbolic_space_no_rings` takes in this
  form the geodesics from its lowest point.
* **The space at an instant** (`InSpace`, `IsGeodesic.greatCircle`, `Crossing.Drawing.ofRings`).
  The section of de Sitter space by the hyperplane of time zero, the space at an instant of an
  observer at rest, is the sphere of radius `ρ` of `E`, a three-sphere.  A closed geodesic lying in
  it is a great circle `u a + v b`, `u² + v² = 1`, with `a ⊥ b` and `‖a‖ = ‖b‖ = ρ`.  So rings that
  are closed geodesics of space are drawn as great circles, which the count of a sphere's strings
  uses (`Bridge.sphere_strings_of_rings`).

`circleCurve` shows that rings exist in de Sitter space.  That a largest ring is a closed geodesic of space, made of its
cells as segments of length `ℓ_c`, is the last sentence of Postulate 2; here it enters as a hypothesis, as a postulate does (the rings of
`Bridge.sphere_strings_of_rings`).  It is also part of the admissible drawings (`Symmetry.admissible`) of the rings of the space at an
instant (`Space.SliceIsQubits`).
-/

open RealInnerProductSpace

namespace Geodesic

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The derivative of the inner product of two curves. -/
lemma hasDerivAt_inner' {f g : ℝ → V} {f' g' : V} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u => ⟪f u, g u⟫) (⟪f t, g'⟫ + ⟪f', g t⟫) t := by
  have h := ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := V)).hasFDerivAt (f t, g t)).comp t
    (hf.hasFDerivAt.prodMk hg.hasFDerivAt)
  convert h.hasDerivAt using 1
  · rfl
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.toSpanSingleton_apply,
    IsBoundedBilinearMap.deriv_apply, one_smul, one_smul]

end Inner

section Forms

variable {T E : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- **The form of a spacetime** on `T × E`, times `T` and places `E`: minus the inner product of
the times plus that of the places.  With `T = ℝ` it is the Minkowski form. -/
def form (p q : T × E) : ℝ := -⟪p.1, q.1⟫ + ⟪p.2, q.2⟫

lemma form_comm (p q : T × E) : form p q = form q p := by
  unfold form
  rw [real_inner_comm p.1, real_inner_comm p.2]

lemma form_smul_left (c : ℝ) (p q : T × E) : form (c • p) q = c * form p q := by
  unfold form
  rw [Prod.smul_fst, Prod.smul_snd, real_inner_smul_left, real_inner_smul_left]
  ring

lemma form_smul_right (c : ℝ) (p q : T × E) : form p (c • q) = c * form p q := by
  rw [form_comm, form_smul_left, form_comm]

lemma form_add_left (p p' q : T × E) : form (p + p') q = form p q + form p' q := by
  unfold form
  rw [Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_left]
  ring

lemma form_add_right (p q q' : T × E) : form p (q + q') = form p q + form p q' := by
  rw [form_comm, form_add_left, form_comm, form_comm q']

/-- The derivative of the form along two curves of `T × E`, given by their components. -/
lemma hasDerivAt_form {P Q P' Q' : ℝ → T × E} {t : ℝ}
    (hP1 : HasDerivAt (fun u => (P u).1) (P' t).1 t) (hP2 : HasDerivAt (fun u => (P u).2) (P' t).2 t)
    (hQ1 : HasDerivAt (fun u => (Q u).1) (Q' t).1 t) (hQ2 : HasDerivAt (fun u => (Q u).2) (Q' t).2 t) :
    HasDerivAt (fun u => form (P u) (Q u)) (form (P t) (Q' t) + form (P' t) (Q t)) t := by
  have h := ((hasDerivAt_inner' hP1 hQ1).neg).add (hasDerivAt_inner' hP2 hQ2)
  convert h using 1
  · rfl
  · unfold form
    ring

end Forms

/-- **A curve** of `T × E`, twice differentiable, given with its velocity `vel` and acceleration
`acc` component by component. -/
structure Curve (T E : Type*) [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- the point of the curve at parameter `t` -/
  pos : ℝ → T × E
  /-- its velocity -/
  vel : ℝ → T × E
  /-- its acceleration -/
  acc : ℝ → T × E
  hpos1 : ∀ t, HasDerivAt (fun u => (pos u).1) (vel t).1 t
  hpos2 : ∀ t, HasDerivAt (fun u => (pos u).2) (vel t).2 t
  hvel1 : ∀ t, HasDerivAt (fun u => (vel u).1) (acc t).1 t
  hvel2 : ∀ t, HasDerivAt (fun u => (vel u).2) (acc t).2 t

section Curves

variable {T E : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- **A geodesic of the quadric** `form X X = k` of `T × E`, `k ≠ 0`: a curve on the quadric
whose acceleration is a multiple of its position.  The position is the normal of the quadric for
the form, so the acceleration is normal to the quadric: the curve is a geodesic of the quadric with
the metric the form induces [B. O'Neill, *Semi-Riemannian Geometry* (1983), Ch. 4], run at a
constant speed (`IsGeodesic.speed_const`).  For `k = 0` the quadric is the null cone, whose metric
is degenerate.  No theorem derives anything from that case; `Bridge.sphere_strings_deSitter` takes
`k = 3/Λ` for every real `Λ`, so `Λ = 0` gives `k = 0` in Lean, and it excludes that case, as it
excludes `Λ < 0`, since a spacelike ring needs `k > 0`. -/
def IsGeodesic (k : ℝ) (γ : Curve T E) : Prop :=
  (∀ t, form (γ.pos t) (γ.pos t) = k) ∧ ∀ t, ∃ c : ℝ, γ.acc t = c • γ.pos t

/-- **A spacelike curve**: its velocity has positive square in the form. -/
def IsSpacelike (γ : Curve T E) : Prop := ∀ t, 0 < form (γ.vel t) (γ.vel t)

/-- **A closed spacelike curve of constant speed and length `len`**, traversed once: its position
is periodic, with a least period `P > 0`, and its speed `√(form vel vel)` covers `len` in that
period at every point.  The theorems use it for spacelike curves only (`IsSpacelike`); for a
timelike or null curve the square root is zero. -/
def HasLength (γ : Curve T E) (len : ℝ) : Prop :=
  ∃ P : ℝ, 0 < P ∧ Function.Periodic γ.pos P ∧
    (∀ P' : ℝ, 0 < P' → Function.Periodic γ.pos P' → P ≤ P') ∧
    ∀ t, Real.sqrt (form (γ.vel t) (γ.vel t)) * P = len

namespace Curve

variable (γ : Curve T E)

lemma hasDerivAt_pos_pos (t : ℝ) :
    HasDerivAt (fun u => form (γ.pos u) (γ.pos u)) (2 * form (γ.pos t) (γ.vel t)) t := by
  have h := hasDerivAt_form (P' := γ.vel) (Q' := γ.vel) (γ.hpos1 t) (γ.hpos2 t) (γ.hpos1 t)
    (γ.hpos2 t)
  convert h using 1
  rw [form_comm (γ.vel t)]
  ring

lemma hasDerivAt_pos_vel (t : ℝ) :
    HasDerivAt (fun u => form (γ.pos u) (γ.vel u))
      (form (γ.vel t) (γ.vel t) + form (γ.pos t) (γ.acc t)) t := by
  have h := hasDerivAt_form (P' := γ.vel) (Q' := γ.acc) (γ.hpos1 t) (γ.hpos2 t) (γ.hvel1 t)
    (γ.hvel2 t)
  convert h using 1
  ring

lemma hasDerivAt_vel_vel (t : ℝ) :
    HasDerivAt (fun u => form (γ.vel u) (γ.vel u)) (2 * form (γ.vel t) (γ.acc t)) t := by
  have h := hasDerivAt_form (P' := γ.acc) (Q' := γ.acc) (γ.hvel1 t) (γ.hvel2 t) (γ.hvel1 t)
    (γ.hvel2 t)
  convert h using 1
  rw [form_comm (γ.acc t)]
  ring

end Curve

end Curves

section Harmonic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **`y'' = −ω²y` with `y(0) = y'(0) = 0` has only the solution zero**: the energy
`⟪y', y'⟫ + ω²⟪y, y⟫` does not change, and it starts at zero. -/
lemma harmonic_zero {ω : ℝ} {y y' y'' : ℝ → V} (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy' : ∀ t, HasDerivAt y' (y'' t) t) (h : ∀ t, y'' t = -(ω ^ 2) • y t) (h0 : y 0 = 0)
    (h0' : y' 0 = 0) (t : ℝ) : y t = 0 := by
  have hE : ∀ u, HasDerivAt (fun u => ⟪y' u, y' u⟫ + ω ^ 2 * ⟪y u, y u⟫) 0 u := fun u => by
    have d := (hasDerivAt_inner' (hy' u) (hy' u)).add
      ((hasDerivAt_inner' (hy u) (hy u)).const_mul (ω ^ 2))
    convert d using 1
    rw [h u, real_inner_smul_right, real_inner_smul_left, real_inner_comm (y u) (y' u)]
    ring
  have hc : ∀ u, ⟪y' u, y' u⟫ + ω ^ 2 * ⟪y u, y u⟫ = 0 := fun u => by
    have := is_const_of_deriv_eq_zero (fun u => (hE u).differentiableAt)
      (fun u => (hE u).deriv) u 0
    rw [this, h0, h0']
    simp
  have hy'0 : ∀ u, y' u = 0 := fun u => by
    have h1 := real_inner_self_nonneg (x := y' u)
    have h2 := mul_nonneg (sq_nonneg ω) (real_inner_self_nonneg (x := y u))
    have : ⟪y' u, y' u⟫ = 0 := by linarith [hc u]
    exact inner_self_eq_zero.1 this
  have := is_const_of_deriv_eq_zero (fun u => (hy u).differentiableAt)
    (fun u => by rw [(hy u).deriv, hy'0 u]) t 0
  rw [this, h0]

/-- **The solutions of `z'' = −ω²z`**: `z t = cos(ωt) z(0) + sin(ωt) z'(0)/ω`. -/
lemma harmonic_eq {ω : ℝ} (hω : ω ≠ 0) {z z' z'' : ℝ → V} (hz : ∀ t, HasDerivAt z (z' t) t)
    (hz' : ∀ t, HasDerivAt z' (z'' t) t) (h : ∀ t, z'' t = -(ω ^ 2) • z t) (t : ℝ) :
    z t = Real.cos (ω * t) • z 0 + Real.sin (ω * t) • (ω⁻¹ • z' 0) := by
  have hl : ∀ u : ℝ, HasDerivAt (fun u : ℝ => ω * u) ω u := fun u => by
    simpa using (hasDerivAt_id u).const_mul ω
  have hc : ∀ u, HasDerivAt (fun u => Real.cos (ω * u) • z 0 + Real.sin (ω * u) • (ω⁻¹ • z' 0))
      ((-Real.sin (ω * u) * ω) • z 0 + (Real.cos (ω * u) * ω) • (ω⁻¹ • z' 0)) u := fun u =>
    ((hl u).cos.smul_const (z 0)).add ((hl u).sin.smul_const (ω⁻¹ • z' 0))
  have hc' : ∀ u, HasDerivAt
      (fun u => (-Real.sin (ω * u) * ω) • z 0 + (Real.cos (ω * u) * ω) • (ω⁻¹ • z' 0))
      ((-(Real.cos (ω * u) * ω) * ω) • z 0 + (-Real.sin (ω * u) * ω * ω) • (ω⁻¹ • z' 0)) u :=
    fun u => by
      have d1 : HasDerivAt (fun u => -Real.sin (ω * u) * ω) (-(Real.cos (ω * u) * ω) * ω) u :=
        (hl u).sin.neg.mul_const ω
      have d2 : HasDerivAt (fun u => Real.cos (ω * u) * ω) (-Real.sin (ω * u) * ω * ω) u :=
        (hl u).cos.mul_const ω
      exact (d1.smul_const (z 0)).add (d2.smul_const (ω⁻¹ • z' 0))
  have key := harmonic_zero (ω := ω)
    (y := fun u => z u - (Real.cos (ω * u) • z 0 + Real.sin (ω * u) • (ω⁻¹ • z' 0)))
    (y' := fun u => z' u - ((-Real.sin (ω * u) * ω) • z 0 + (Real.cos (ω * u) * ω) • (ω⁻¹ • z' 0)))
    (y'' := fun u => z'' u - ((-(Real.cos (ω * u) * ω) * ω) • z 0 +
      (-Real.sin (ω * u) * ω * ω) • (ω⁻¹ • z' 0)))
    (fun u => (hz u).sub (hc u)) (fun u => (hz' u).sub (hc' u)) (fun u => by
      rw [h u]
      module)
    (by simp) (by simp [smul_smul, hω]) t
  exact sub_eq_zero.1 key

end Harmonic

section Geodesics

variable {T E : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {k : ℝ} {γ : Curve T E}

/-- On a geodesic of a quadric the velocity is orthogonal to the position, for the form. -/
theorem IsGeodesic.form_pos_vel (h : IsGeodesic k γ) (t : ℝ) : form (γ.pos t) (γ.vel t) = 0 := by
  have e : (fun u => form (γ.pos u) (γ.pos u)) = fun _ => k := funext h.1
  have d := γ.hasDerivAt_pos_pos t
  rw [e] at d
  have := d.unique (hasDerivAt_const t k)
  linarith

theorem IsGeodesic.form_vel_acc (h : IsGeodesic k γ) (t : ℝ) : form (γ.vel t) (γ.acc t) = 0 := by
  obtain ⟨c, hc⟩ := h.2 t
  rw [hc, form_smul_right, form_comm, h.form_pos_vel t, mul_zero]

/-- **A geodesic keeps its speed**: the square of its velocity in the form is constant. -/
theorem IsGeodesic.speed_const (h : IsGeodesic k γ) (t : ℝ) :
    form (γ.vel t) (γ.vel t) = form (γ.vel 0) (γ.vel 0) := by
  have hd : ∀ u, HasDerivAt (fun u => form (γ.vel u) (γ.vel u)) 0 u := fun u => by
    have := γ.hasDerivAt_vel_vel u
    rwa [h.form_vel_acc u, mul_zero] at this
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0

/-- **The acceleration of a geodesic of a quadric** `form X X = k ≠ 0` is `−c/k` times its
position, with `c` the square of its speed. -/
theorem IsGeodesic.acc_eq (h : IsGeodesic k γ) (hk : k ≠ 0) (t : ℝ) :
    γ.acc t = (-form (γ.vel 0) (γ.vel 0) / k) • γ.pos t := by
  obtain ⟨c, hc⟩ := h.2 t
  have e : (fun u => form (γ.pos u) (γ.vel u)) = fun _ => 0 := funext h.form_pos_vel
  have d := γ.hasDerivAt_pos_vel t
  rw [e] at d
  have h0 := d.unique (hasDerivAt_const t (0 : ℝ))
  rw [hc, form_smul_right, h.1 t, h.speed_const t] at h0
  have hc' : c = -form (γ.vel 0) (γ.vel 0) / k := by
    field_simp
    linarith
  rw [hc, hc']

end Geodesics

section Closed

variable {T E : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {k : ℝ} {γ : Curve T E}

/-- **A spacelike geodesic of a quadric `form X X = k > 0` runs on a circle**:
`pos t = cos(ωt) pos 0 + sin(ωt) (vel 0)/ω`, with `ω = √(c/k)` and `c` the square of its speed. -/
theorem IsGeodesic.circle (h : IsGeodesic k γ) (hk : 0 < k) (hc : 0 < form (γ.vel 0) (γ.vel 0))
    (t : ℝ) :
    γ.pos t = Real.cos (Real.sqrt (form (γ.vel 0) (γ.vel 0) / k) * t) • γ.pos 0 +
      Real.sin (Real.sqrt (form (γ.vel 0) (γ.vel 0) / k) * t) •
        ((Real.sqrt (form (γ.vel 0) (γ.vel 0) / k))⁻¹ • γ.vel 0) := by
  obtain ⟨c, hcdef⟩ : ∃ c, form (γ.vel 0) (γ.vel 0) = c := ⟨_, rfl⟩
  rw [hcdef] at hc ⊢
  have hω : 0 < Real.sqrt (c / k) := Real.sqrt_pos.2 (div_pos hc hk)
  have hω2 : Real.sqrt (c / k) ^ 2 = c / k := Real.sq_sqrt (div_pos hc hk).le
  have hacc : ∀ u, γ.acc u = -(Real.sqrt (c / k) ^ 2) • γ.pos u := fun u => by
    rw [h.acc_eq hk.ne' u, hcdef, hω2, neg_div]
  have e1 := harmonic_eq hω.ne' γ.hpos1 γ.hvel1
    (fun u => by rw [hacc u, Prod.smul_fst]) t
  have e2 := harmonic_eq hω.ne' γ.hpos2 γ.hvel2
    (fun u => by rw [hacc u, Prod.smul_snd]) t
  exact Prod.ext (by rw [e1]; simp) (by rw [e2]; simp)

/-- **A closed curve has a unique length**: its least period and its speed are fixed. -/
theorem HasLength.unique {l₁ l₂ : ℝ} (h₁ : HasLength γ l₁) (h₂ : HasLength γ l₂) : l₁ = l₂ := by
  obtain ⟨P₁, hP₁, hper₁, hleast₁, hlen₁⟩ := h₁
  obtain ⟨P₂, hP₂, hper₂, hleast₂, hlen₂⟩ := h₂
  have e : P₁ = P₂ := le_antisymm (hleast₁ P₂ hP₂ hper₂) (hleast₂ P₁ hP₁ hper₁)
  rw [← hlen₁ 0, ← hlen₂ 0, e]

/-- **Every spacelike geodesic of a quadric `form X X = k > 0` is closed, of length `2π√k`**: it
runs once around a circle of radius `√k` in the period `2π/ω`, at the speed `√c = ω√k`. -/
theorem IsGeodesic.hasLength (h : IsGeodesic k γ) (hk : 0 < k) (hsp : IsSpacelike γ) :
    HasLength γ (2 * Real.pi * Real.sqrt k) := by
  have hc := hsp 0
  obtain ⟨c, hcdef⟩ : ∃ c, form (γ.vel 0) (γ.vel 0) = c := ⟨_, rfl⟩
  rw [hcdef] at hc
  have hcirc := h.circle hk (hcdef ▸ hsp 0)
  rw [hcdef] at hcirc
  obtain ⟨ω, hωdef⟩ : ∃ ω, Real.sqrt (c / k) = ω := ⟨_, rfl⟩
  rw [hωdef] at hcirc
  have hω : 0 < ω := hωdef ▸ Real.sqrt_pos.2 (div_pos hc hk)
  have hωc : Real.sqrt c = ω * Real.sqrt k := by
    rw [← hωdef, ← Real.sqrt_mul (div_pos hc hk).le, div_mul_cancel₀ c hk.ne']
  refine ⟨2 * Real.pi / ω, by positivity, ?_, ?_, ?_⟩
  · -- it returns after `2π/ω`
    intro t
    rw [hcirc (t + 2 * Real.pi / ω), hcirc t]
    have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
    rw [e, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · -- and not before
    intro P' hP' hper
    have hpk : form (γ.pos 0) (γ.pos 0) = k := h.1 0
    have hpv : form (γ.vel 0) (γ.pos 0) = 0 := by rw [form_comm]; exact h.form_pos_vel 0
    have e := congrArg (fun X => form X (γ.pos 0)) (hper 0)
    simp only [zero_add] at e
    rw [hcirc P', form_add_left, form_smul_left, form_smul_left, form_smul_left, hpk, hpv,
      mul_zero, mul_zero, add_zero] at e
    have hcos : Real.cos (ω * P') = 1 := by
      have := mul_right_cancel₀ hk.ne' (e.trans (one_mul k).symm)
      exact this
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos
    have hpos : (0 : ℝ) < n * (2 * Real.pi) := by rw [hn]; positivity
    have hn1 : (1 : ℝ) ≤ n := by
      have : (0 : ℝ) < n := pos_of_mul_pos_left hpos (by positivity)
      exact_mod_cast (show (0 : ℤ) < n by exact_mod_cast this)
    rw [div_le_iff₀ hω, mul_comm P' ω, ← hn]
    nlinarith [Real.pi_pos]
  · -- at the speed `√c`
    intro t
    rw [h.speed_const t, hcdef, hωc]
    field_simp

end Closed

/-- for `u² + v² = 1` there is an angle with cosine `u` and sine `v` -/
lemma exists_angle {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = u ∧ Real.sin θ = v := by
  have hu : |u| ≤ 1 := (sq_le_one_iff_abs_le_one u).1 (by nlinarith [sq_nonneg v])
  obtain ⟨hu1, hu2⟩ := abs_le.1 hu
  have hs : Real.sqrt (1 - u ^ 2) = |v| := by
    rw [show 1 - u ^ 2 = v ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 v with hv | hv
  · refine ⟨Real.arccos u, Real.cos_arccos hu1 hu2, ?_⟩
    rw [Real.sin_arccos, hs, abs_of_nonneg hv]
  · refine ⟨-Real.arccos u, by rw [Real.cos_neg, Real.cos_arccos hu1 hu2], ?_⟩
    rw [Real.sin_neg, Real.sin_arccos, hs, abs_of_neg hv, neg_neg]

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ρ : ℝ} {γ : Curve ℝ E}

/-- **A curve in the space at an instant** of an observer at rest in de Sitter space: in the
section of `ℝ × E` by the hyperplane of time zero.  With the quadric `form X X = ρ²` it is the
sphere of radius `ρ` of `E`, a three-sphere when `E` is four-dimensional, and the section is
totally geodesic, so its geodesics are geodesics of spacetime.  An isometry of de Sitter space
carries any observer at rest, at any instant, to this one.  The observer's static region is the
half of the three-sphere inside his horizon, which every great circle leaves. -/
def InSpace (γ : Curve ℝ E) : Prop := ∀ t, (γ.pos t).1 = 0

lemma InSpace.vel_fst (hin : InSpace γ) (t : ℝ) : (γ.vel t).1 = 0 := by
  have e : (fun u => (γ.pos u).1) = fun _ => (0 : ℝ) := funext hin
  have d := γ.hpos1 t
  rw [e] at d
  exact d.unique (hasDerivAt_const t 0)

/-- the angular speed `√(c/k)` of a geodesic of the quadric `form X X = k`, with `c` the square of
its speed -/
noncomputable def Curve.freq (γ : Curve ℝ E) (k : ℝ) : ℝ := Real.sqrt (form (γ.vel 0) (γ.vel 0) / k)

/-- **A closed geodesic of space is a great circle** (Sec. IV.D).  A spacelike geodesic of de
Sitter space `form X X = ρ²` that lies in the space at an instant runs on the great circle of the
sphere of radius `ρ` through `a = pos 0` and `b = vel 0/ω`, with `a ⊥ b` and `‖a‖ = ‖b‖ = ρ`. -/
theorem IsGeodesic.greatCircle (h : IsGeodesic (ρ ^ 2) γ) (hρ : 0 < ρ) (hsp : IsSpacelike γ)
    (hin : InSpace γ) :
    ⟪(γ.pos 0).2, (γ.freq (ρ ^ 2))⁻¹ • (γ.vel 0).2⟫ = 0 ∧ ‖(γ.pos 0).2‖ = ρ ∧
      ‖(γ.freq (ρ ^ 2))⁻¹ • (γ.vel 0).2‖ = ρ ∧
      Set.range (fun t => (γ.pos t).2) =
        Crossing.greatCircle (γ.pos 0).2 ((γ.freq (ρ ^ 2))⁻¹ • (γ.vel 0).2) := by
  have hk : 0 < ρ ^ 2 := by positivity
  have hc := hsp 0
  have hp1 := hin 0
  have hv1 := hin.vel_fst 0
  -- in space the form is the inner product of the places
  have hpp : ⟪(γ.pos 0).2, (γ.pos 0).2⟫ = ρ ^ 2 := by
    have := h.1 0
    unfold form at this
    rw [hp1, inner_zero_left, neg_zero, zero_add] at this
    exact this
  have hpv : ⟪(γ.pos 0).2, (γ.vel 0).2⟫ = 0 := by
    have := h.form_pos_vel 0
    unfold form at this
    rw [hp1, inner_zero_left, neg_zero, zero_add] at this
    exact this
  have hvv : ⟪(γ.vel 0).2, (γ.vel 0).2⟫ = form (γ.vel 0) (γ.vel 0) := by
    unfold form
    rw [hv1, inner_zero_left, neg_zero, zero_add]
  obtain ⟨c, hcdef⟩ : ∃ c, form (γ.vel 0) (γ.vel 0) = c := ⟨_, rfl⟩
  rw [hcdef] at hc hvv
  have hω : γ.freq (ρ ^ 2) = Real.sqrt c / ρ := by
    unfold Curve.freq
    rw [hcdef, Real.sqrt_div' _ hk.le, Real.sqrt_sq hρ.le]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [real_inner_smul_right, hpv, mul_zero]
  · rw [← Real.sqrt_sq hρ.le, ← hpp, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  · rw [norm_smul, hω, norm_inv, Real.norm_eq_abs, abs_of_pos (div_pos hsc hρ),
      ← Real.sqrt_sq (norm_nonneg (γ.vel 0).2), ← real_inner_self_eq_norm_sq, hvv]
    field_simp
  · have hcirc := h.circle hk (hcdef ▸ hc)
    rw [hcdef] at hcirc
    have hfreq : Real.sqrt (c / ρ ^ 2) = γ.freq (ρ ^ 2) := by
      unfold Curve.freq
      rw [hcdef]
    rw [hfreq] at hcirc
    have hωpos : 0 < γ.freq (ρ ^ 2) := by rw [hω]; positivity
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨Real.cos (γ.freq (ρ ^ 2) * t), Real.sin (γ.freq (ρ ^ 2) * t),
        Real.cos_sq_add_sin_sq _, ?_⟩
      show (γ.pos t).2 = _
      rw [hcirc t]
      simp
    · rintro ⟨u, v, huv, rfl⟩
      obtain ⟨θ, hcos, hsin⟩ := exists_angle huv
      refine ⟨θ / γ.freq (ρ ^ 2), ?_⟩
      show (γ.pos (θ / γ.freq (ρ ^ 2))).2 = _
      rw [hcirc (θ / γ.freq (ρ ^ 2))]
      have e : γ.freq (ρ ^ 2) * (θ / γ.freq (ρ ^ 2)) = θ := by field_simp
      simp only [Prod.snd_add, Prod.smul_snd, e, hcos, hsin]

end Space

/-- **The largest rings drawn from the solution** (Secs. II and IV.D): rings that are closed geodesics of
the space at an instant of de Sitter space `form X X = ρ²` give a drawing of the rings as great
circles of the sphere of radius `ρ` (`IsGeodesic.greatCircle`); ring `i`'s great circle is the
path of its geodesic (`ofRings_circle`). -/
noncomputable def _root_.Crossing.Drawing.ofRings {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} {ρ : ℝ} (hρ : 0 < ρ) (γ : ι → Curve ℝ E)
    (hgeo : ∀ i, IsGeodesic (ρ ^ 2) (γ i)) (hsp : ∀ i, IsSpacelike (γ i))
    (hin : ∀ i, InSpace (γ i)) : Crossing.Drawing ι E ρ where
  a i := ((γ i).pos 0).2
  b i := ((γ i).freq (ρ ^ 2))⁻¹ • ((γ i).vel 0).2
  orth i := ((hgeo i).greatCircle hρ (hsp i) (hin i)).1
  norm_a i := ((hgeo i).greatCircle hρ (hsp i) (hin i)).2.1
  norm_b i := ((hgeo i).greatCircle hρ (hsp i) (hin i)).2.2.1

/-- **Ring `i`'s great circle is the path of its geodesic.** -/
theorem ofRings_circle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    {ρ : ℝ} (hρ : 0 < ρ) (γ : ι → Curve ℝ E) (hgeo : ∀ i, IsGeodesic (ρ ^ 2) (γ i))
    (hsp : ∀ i, IsSpacelike (γ i)) (hin : ∀ i, InSpace (γ i)) (i : ι) :
    Crossing.greatCircle ((Crossing.Drawing.ofRings hρ γ hgeo hsp hin).a i)
      ((Crossing.Drawing.ofRings hρ γ hgeo hsp hin).b i) = Set.range (fun t => ((γ i).pos t).2) :=
  ((hgeo i).greatCircle hρ (hsp i) (hin i)).2.2.2.symm

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_mul_left' (ω u : ℝ) : HasDerivAt (fun u : ℝ => ω * u) ω u := by
  simpa using (hasDerivAt_id u).const_mul ω

/-- **A great circle run at the angular speed `ω`** in the space at an instant: the curve
`t ↦ (0, cos(ωt) a + sin(ωt) b)` of `ℝ × E`. -/
noncomputable def circleCurve (a b : E) (ω : ℝ) : Curve ℝ E where
  pos t := (0, Real.cos (ω * t) • a + Real.sin (ω * t) • b)
  vel t := (0, (-Real.sin (ω * t) * ω) • a + (Real.cos (ω * t) * ω) • b)
  acc t := (0, (-(Real.cos (ω * t) * ω) * ω) • a + (-Real.sin (ω * t) * ω * ω) • b)
  hpos1 t := hasDerivAt_const t 0
  hpos2 t := ((hasDerivAt_mul_left' ω t).cos.smul_const a).add
    ((hasDerivAt_mul_left' ω t).sin.smul_const b)
  hvel1 t := hasDerivAt_const t 0
  hvel2 t := by
    have d1 : HasDerivAt (fun u => -Real.sin (ω * u) * ω) (-(Real.cos (ω * t) * ω) * ω) t :=
      (hasDerivAt_mul_left' ω t).sin.neg.mul_const ω
    have d2 : HasDerivAt (fun u => Real.cos (ω * u) * ω) (-Real.sin (ω * t) * ω * ω) t :=
      (hasDerivAt_mul_left' ω t).cos.mul_const ω
    exact (d1.smul_const a).add (d2.smul_const b)

variable {a b : E} {ρ ω : ℝ}

lemma circleCurve_inSpace : InSpace (circleCurve a b ω) := fun _ => rfl

/-- The great circle through `a ⊥ b`, `‖a‖ = ‖b‖ = ρ`, is a geodesic of the quadric
`form X X = ρ²`, de Sitter space of radius `ρ`. -/
lemma circleCurve_geodesic (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) :
    IsGeodesic (ρ ^ 2) (circleCurve a b ω) := by
  refine ⟨fun t => ?_, fun t => ⟨-(ω ^ 2), ?_⟩⟩
  · show -⟪(0 : ℝ), 0⟫ + ⟪Real.cos (ω * t) • a + Real.sin (ω * t) • b,
      Real.cos (ω * t) • a + Real.sin (ω * t) • b⟫ = ρ ^ 2
    rw [inner_zero_left, neg_zero, zero_add, real_inner_self_eq_norm_sq,
      Crossing.norm_comb_sq hab ha hb, Real.cos_sq_add_sin_sq, one_mul]
  · show ((0 : ℝ), (-(Real.cos (ω * t) * ω) * ω) • a + (-Real.sin (ω * t) * ω * ω) • b) =
      -(ω ^ 2) • ((0 : ℝ), Real.cos (ω * t) • a + Real.sin (ω * t) • b)
    rw [Prod.smul_mk, smul_zero]
    congr 1
    module

lemma circleCurve_spacelike (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (hρ : 0 < ρ)
    (hω : ω ≠ 0) : IsSpacelike (circleCurve a b ω) := fun t => by
  show 0 < -⟪(0 : ℝ), 0⟫ + ⟪(-Real.sin (ω * t) * ω) • a + (Real.cos (ω * t) * ω) • b,
    (-Real.sin (ω * t) * ω) • a + (Real.cos (ω * t) * ω) • b⟫
  rw [inner_zero_left, neg_zero, zero_add, real_inner_self_eq_norm_sq,
    Crossing.norm_comb_sq hab ha hb]
  have e : (-Real.sin (ω * t) * ω) ^ 2 + (Real.cos (ω * t) * ω) ^ 2 = ω ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (ω * t)]
  rw [e]
  positivity

/-- `cosh` has the derivative `sinh` -/
lemma hasDerivAt_cosh' (t : ℝ) : HasDerivAt Real.cosh (Real.sinh t) t := by
  have h := ((Real.hasDerivAt_exp t).add
    ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t))).div_const 2
  convert h using 1
  · funext u
    rw [Real.cosh_eq]
    rfl
  · rw [Real.sinh_eq]
    ring

/-- `sinh` has the derivative `cosh` -/
lemma hasDerivAt_sinh' (t : ℝ) : HasDerivAt Real.sinh (Real.cosh t) t := by
  have h := ((Real.hasDerivAt_exp t).sub
    ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t))).div_const 2
  convert h using 1
  · funext u
    rw [Real.sinh_eq]
    rfl
  · rw [Real.cosh_eq]
    ring

variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]

/-- **A hyperbola** `t ↦ (cosh t · a, sinh t · b)` of `T × E`, a geodesic of the quadric
`form X X = −ℓ²` when `‖a‖ = ‖b‖ = ℓ` (`hypCurve_geodesic`); with one time, `T = ℝ`, a geodesic of
hyperbolic space from its lowest point (`Space.hyperbolic_space_no_rings`). -/
noncomputable def hypCurve (a : T) (b : E) : Curve T E where
  pos t := (Real.cosh t • a, Real.sinh t • b)
  vel t := (Real.sinh t • a, Real.cosh t • b)
  acc t := (Real.cosh t • a, Real.sinh t • b)
  hpos1 t := (hasDerivAt_cosh' t).smul_const a
  hpos2 t := (hasDerivAt_sinh' t).smul_const b
  hvel1 t := (hasDerivAt_sinh' t).smul_const a
  hvel2 t := (hasDerivAt_cosh' t).smul_const b

lemma hypCurve_geodesic {ℓ : ℝ} {a : T} {b : E} (ha : ‖a‖ = ℓ) (hb : ‖b‖ = ℓ) :
    IsGeodesic (-(ℓ ^ 2)) (hypCurve a b) := by
  refine ⟨fun t => ?_, fun t => ⟨1, (one_smul ℝ _).symm⟩⟩
  show -⟪Real.cosh t • a, Real.cosh t • a⟫ + ⟪Real.sinh t • b, Real.sinh t • b⟫ = -(ℓ ^ 2)
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hb]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

end Model

end Geodesic
