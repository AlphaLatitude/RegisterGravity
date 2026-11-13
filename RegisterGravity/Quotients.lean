import RegisterGravity.Geodesics

/-!
# The rotations of the three-sphere (Sec. IV.D), and rings in a quotient

The solution without a mass is found in `Space.lean` from its space at an instant, a quotient of
the three-sphere by a finite group `Γ` of rotations, which the rings make trivial
(`Space.sphere_rings`); this file proves what that step needs of such a group, the plane it turns
(`exists_rotation_plane`) and a plane that finitely many such maps leave (`exists_plane_not_turned`).

It also states what a ring in a quotient is, in the terms that `Space.lean` and `Solution.lean`
use.  A curve closes in the quotient by `Γ` after the time `P` when some map of `Γ` carries its
point at every `t` to its point at `t + P` (`Returns`).  A ring of length `len` closes so after a
least time `P > 0`, and its speed covers `len` in that time (`ClosesIn`); in the trivial quotient
it is a closed curve of length `len` (`closesIn_bot`).  A group acts properly discontinuously when
only finitely many of its maps carry a point of a compact set into that set (`ProperOn`), which is
what `Space.flat_space_no_rings` and `Space.hyperbolic_space_no_rings` use of the group.  The great
circles `t ↦ cos t · a + sin t · b` of de Sitter space (`planeCurve`) are geodesics of the quadric
`form X X = k` when `a` and `b` are orthogonal with `form a a = form b b = k`
(`planeCurve_isGeodesic`); `Space.sphere_rings` and the model rings of `Solution.lean` are such
circles.

One fact of geometry is taken as known: a closed geodesic of a quotient is a geodesic `c` of the
space with `c (t + P) = g (c t)` for one map `g` of `Γ` and every `t`, of length its speed times
the least such `P > 0`.
-/

open RealInnerProductSpace Set Geodesic

namespace Quotients

section Form

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The form of `ℝ × E`, one time: `−st + ⟪x, y⟫`. -/
lemma form_eq (p q : ℝ × E) : form p q = -(p.1 * q.1) + ⟪p.2, q.2⟫ := by
  unfold form
  simp [RCLike.inner_apply, mul_comm]

/-- Two orthonormal vectors in a space of at least two dimensions. -/
lemma exists_orthonormal_pair [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ f₁ f₂ : E, ‖f₁‖ = 1 ∧ ‖f₂‖ = 1 ∧ ⟪f₁, f₂⟫ = 0 := by
  obtain ⟨B⟩ : Nonempty (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :=
    ⟨stdOrthonormalBasis ℝ E⟩
  exact ⟨B ⟨0, by omega⟩, B ⟨1, by omega⟩, B.orthonormal.1 _, B.orthonormal.1 _,
    B.orthonormal.2 (by simp)⟩

/-- A unit vector orthogonal to a given vector `u ≠ 0`, in a space of at least two dimensions. -/
lemma exists_unit_perp [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E) {u : E} (hu : u ≠ 0) :
    ∃ w : E, ‖w‖ = 1 ∧ ⟪u, w⟫ = 0 := by
  obtain ⟨w', hw', hw0⟩ : ∃ w' ∈ (ℝ ∙ u)ᗮ, w' ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have h2 := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [h, finrank_bot, add_zero, finrank_span_singleton hu] at h2
    omega
  refine ⟨‖w'‖⁻¹ • w', ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
  · rw [real_inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hw', mul_zero]

lemma form_zero_zero (y y' : E) : form ((0 : ℝ), y) ((0 : ℝ), y') = ⟪y, y'⟫ := by
  rw [form_eq]
  simp

end Form

/-! ### Rings in a quotient -/

section Rings

variable {F X : Type*} [FunLike F X X]

/-- **The curve `c` closes in the quotient by `Γ` after the time `P`**: some map of `Γ` carries its
point at every `t` to its point at `t + P`, so that in the quotient the curve is back where it was. -/
def Returns (Γ : Set F) (c : ℝ → X) (P : ℝ) : Prop :=
  ∃ g ∈ Γ, ∀ t, c (t + P) = g (c t)

/-- **A ring of length `len` in the quotient by `Γ`**: the curve `c` closes in the quotient after a
least time `P > 0`, and its speed `v` covers `len` in that time at every point.  For the trivial
group this is a closed curve of length `len` (`closesIn_bot`), and for a group acting on de Sitter
space it is a closed geodesic of the quotient when `c` is a geodesic. -/
def ClosesIn (Γ : Set F) (c : ℝ → X) (v : ℝ → ℝ) (len : ℝ) : Prop :=
  ∃ P : ℝ, 0 < P ∧ Returns Γ c P ∧ (∀ P' : ℝ, 0 < P' → Returns Γ c P' → P ≤ P') ∧
    ∀ t, v t * P = len

end Rings

/-- the speed of a curve, `√(form vel vel)` -/
noncomputable def speed {T E : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (γ : Curve T E) (t : ℝ) : ℝ :=
  Real.sqrt (form (γ.vel t) (γ.vel t))

/-- **A group of maps of `X` acting properly discontinuously**: only finitely many of its maps
carry a point of a compact set `K` into `K`.  The quotient of a manifold by a group of
homeomorphisms that acts so, and whose maps other than the identity fix no point, is a Hausdorff
manifold. -/
def ProperOn {X : Type*} [TopologicalSpace X] (Γ : Set (Equiv.Perm X)) : Prop :=
  ∀ K : Set X, IsCompact K → {g | g ∈ Γ ∧ ((⇑g) '' K ∩ K).Nonempty}.Finite

/-! ### The trivial quotient of de Sitter space -/

section DeSitter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **In the trivial quotient a ring is a closed curve**: a curve closes in the quotient by the
trivial group, with the length `len`, exactly when it is a closed curve of length `len`. -/
lemma closesIn_bot {γ : Curve ℝ E} {len : ℝ} :
    ClosesIn ((⊥ : Subgroup ((ℝ × E) ≃ₗ[ℝ] (ℝ × E))) : Set ((ℝ × E) ≃ₗ[ℝ] (ℝ × E))) γ.pos
      (speed γ) len ↔ HasLength γ len := by
  have hret : ∀ P, Returns ((⊥ : Subgroup ((ℝ × E) ≃ₗ[ℝ] (ℝ × E))) :
      Set ((ℝ × E) ≃ₗ[ℝ] (ℝ × E))) γ.pos P ↔ Function.Periodic γ.pos P := by
    intro P
    constructor
    · rintro ⟨g, hg, hgP⟩ t
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
      rw [hgP t, hg]
      rfl
    · intro hP
      exact ⟨1, Subgroup.one_mem _, fun t => hP t⟩
  constructor
  · rintro ⟨P, hP, hr, hleast, hlen⟩
    exact ⟨P, hP, (hret P).1 hr, fun P' hP' h' => hleast P' hP' ((hret P').2 h'), hlen⟩
  · rintro ⟨P, hP, hper, hleast, hlen⟩
    exact ⟨P, hP, (hret P).2 hper, fun P' hP' h' => hleast P' hP' ((hret P').1 h'), hlen⟩

end DeSitter

/-! ### The components of a curve, and great circles of de Sitter space -/

section Curves

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_fst' {f : ℝ → ℝ × E} {f' : ℝ × E} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun u => (f u).1) f'.1 t := by
  have := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using this

lemma hasDerivAt_snd' {f : ℝ → ℝ × E} {f' : ℝ × E} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun u => (f u).2) f'.2 t := by
  have := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using this

end Curves

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℝ}

lemma hasDerivAt_plane (a b : ℝ × E) (t : ℝ) :
    HasDerivAt (fun u => Real.cos u • a + Real.sin u • b) ((-Real.sin t) • a + Real.cos t • b) t :=
  ((Real.hasDerivAt_cos t).smul_const a).add ((Real.hasDerivAt_sin t).smul_const b)

lemma hasDerivAt_plane' (a b : ℝ × E) (t : ℝ) :
    HasDerivAt (fun u => (-Real.sin u) • a + Real.cos u • b)
      ((-Real.cos t) • a + (-Real.sin t) • b) t :=
  ((Real.hasDerivAt_sin t).neg.smul_const a).add ((Real.hasDerivAt_cos t).smul_const b)

/-- **A great circle of de Sitter space**: `t ↦ cos t · a + sin t · b` in `ℝ × E`. -/
noncomputable def planeCurve (a b : ℝ × E) : Curve ℝ E where
  pos t := Real.cos t • a + Real.sin t • b
  vel t := (-Real.sin t) • a + Real.cos t • b
  acc t := (-Real.cos t) • a + (-Real.sin t) • b
  hpos1 t := hasDerivAt_fst' (hasDerivAt_plane a b t)
  hpos2 t := hasDerivAt_snd' (hasDerivAt_plane a b t)
  hvel1 t := hasDerivAt_fst' (hasDerivAt_plane' a b t)
  hvel2 t := hasDerivAt_snd' (hasDerivAt_plane' a b t)

lemma planeCurve_form {a b : ℝ × E} (ha : form a a = k) (hb : form b b = k) (hab : form a b = 0)
    (u v : ℝ) : form (u • a + v • b) (u • a + v • b) = (u ^ 2 + v ^ 2) * k := by
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right]
  rw [form_comm b a, ha, hb, hab]
  ring

lemma planeCurve_isGeodesic {a b : ℝ × E} (ha : form a a = k) (hb : form b b = k)
    (hab : form a b = 0) : IsGeodesic k (planeCurve a b) := by
  refine ⟨fun t => ?_, fun t => ⟨-1, ?_⟩⟩
  · show form (Real.cos t • a + Real.sin t • b) (Real.cos t • a + Real.sin t • b) = k
    rw [planeCurve_form ha hb hab, Real.cos_sq_add_sin_sq, one_mul]
  · show (-Real.cos t) • a + (-Real.sin t) • b = (-1 : ℝ) • (Real.cos t • a + Real.sin t • b)
    module

lemma planeCurve_spacelike {a b : ℝ × E} (hk : 0 < k) (ha : form a a = k) (hb : form b b = k)
    (hab : form a b = 0) : IsSpacelike (planeCurve a b) := fun t => by
  show 0 < form ((-Real.sin t) • a + Real.cos t • b) ((-Real.sin t) • a + Real.cos t • b)
  rw [planeCurve_form ha hb hab, neg_sq, Real.sin_sq_add_cos_sq, one_mul]
  exact hk

lemma planeCurve_speed {a b : ℝ × E} (ha : form a a = k) (hb : form b b = k)
    (hab : form a b = 0) (t : ℝ) :
    form ((planeCurve a b).vel t) ((planeCurve a b).vel t) = k := by
  show form ((-Real.sin t) • a + Real.cos t • b) ((-Real.sin t) • a + Real.cos t • b) = k
  rw [planeCurve_form ha hb hab, neg_sq, Real.sin_sq_add_cos_sq, one_mul]

end Plane

/-! ### A map that keeps the inner product turns a plane; a plane that finitely many leave -/

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The angle of a turn**: for `c² + s² = 1` and `c < 1`, an angle in `(0, 2π)` with cosine `c`
and sine `s`. -/
lemma exists_angle_pos {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (hc : c < 1) :
    ∃ θ, 0 < θ ∧ θ < 2 * Real.pi ∧ Real.cos θ = c ∧ Real.sin θ = s := by
  have hc' : -1 ≤ c := by nlinarith [sq_nonneg s]
  have hsq : Real.sqrt (1 - c ^ 2) = |s| := by
    rw [show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  have hpos := Real.arccos_pos.2 hc
  have hle := Real.arccos_le_pi c
  rcases le_or_gt 0 s with hs | hs
  · refine ⟨Real.arccos c, hpos, by linarith [Real.pi_pos], Real.cos_arccos hc' hc.le, ?_⟩
    rw [Real.sin_arccos, hsq, abs_of_nonneg hs]
  · refine ⟨2 * Real.pi - Real.arccos c, by linarith, by linarith, ?_, ?_⟩
    · rw [Real.cos_two_pi_sub, Real.cos_arccos hc' hc.le]
    · rw [Real.sin_two_pi_sub, Real.sin_arccos, hsq, abs_of_neg hs, neg_neg]

/-- **A linear map of `E` that keeps the inner product and fixes no vector but zero turns some
plane**: it turns an orthonormal pair `u, w` by an angle with cosine `c < 1`.  Let `u` be a unit
vector at which `⟪y, A y⟫` is largest on the unit sphere, with the value `m`.  Along the sphere the
value does not change to first order at `u`, so `A u + A⁻¹ u = 2m u`, and the plane of `u` and
`A u` is carried onto itself.  As `A` fixes no vector, `m < 1`.  If `m = −1`, `A = −1`, which turns
every plane by `π`; otherwise `A` turns the plane of `u` and `A u` by the angle with cosine `m`. -/
lemma exists_rotation_plane [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E)
    (A : E →ₗ[ℝ] E) (hA : ∀ x y, ⟪A x, A y⟫ = ⟪x, y⟫) (hfix : ∀ y, A y = y → y = 0) :
    ∃ u w : E, ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ ⟪u, w⟫ = 0 ∧ ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c < 1 ∧
      A u = c • u + s • w ∧ A w = (-s) • u + c • w := by
  have hnorm : ∀ y, ‖A y‖ = ‖y‖ := fun y => by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hA]
  -- the largest value `m` of `⟪y, A y⟫` on the unit sphere, at `u`
  obtain ⟨f₁, f₂, hf₁, -, -⟩ := exists_orthonormal_pair hE
  have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨f₁, by rw [mem_sphere_zero_iff_norm]; exact hf₁⟩
  have hcont : Continuous fun y : E => ⟪y, A y⟫ :=
    continuous_id.inner (LinearMap.continuous_of_finiteDimensional A)
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne hcont.continuousOn
  rw [mem_sphere_zero_iff_norm] at hu
  have hu2 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  obtain ⟨m, hm⟩ : ∃ m, m = ⟪u, A u⟫ := ⟨_, rfl⟩
  have hle : ∀ y, ⟪y, A y⟫ ≤ m * ‖y‖ ^ 2 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
      have hmem : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h := isMaxOn_iff.1 hmax _ hmem
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h
      rw [← hm] at h
      have e : ⟪y, A y⟫ = ‖y‖ ^ 2 * (‖y‖⁻¹ * (‖y‖⁻¹ * ⟪y, A y⟫)) := by
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left h (sq_nonneg ‖y‖)
      linarith
  -- at `u` the value does not change along the sphere: `⟪u, A w⟫ + ⟪w, A u⟫ = 0` for `w ⊥ u`
  have hstat : ∀ w, ⟪u, w⟫ = 0 → ⟪u, A w⟫ + ⟪w, A u⟫ = 0 := by
    intro w hw
    obtain ⟨b, hb⟩ : ∃ b, b = ⟪u, A w⟫ + ⟪w, A u⟫ := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D, D = m * ‖w‖ ^ 2 - ⟪w, A w⟫ := ⟨_, rfl⟩
    have key : ∀ t : ℝ, t * b ≤ t ^ 2 * D := by
      intro t
      have h := hle (u + t • w)
      have hn : ‖u + t • w‖ ^ 2 = 1 + t ^ 2 * ‖w‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
          real_inner_smul_right, hu2, real_inner_comm u w, hw, real_inner_self_eq_norm_sq]
        ring
      rw [hn, map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_right, ← hm] at h
      rw [hb, hD]
      nlinarith [h]
    obtain ⟨M, hM⟩ : ∃ M, M = |D| + 1 := ⟨_, rfl⟩
    have hM0 : 0 < M := by rw [hM]; positivity
    have hDM : D ≤ M - 1 := by rw [hM]; linarith [le_abs_self D]
    have h1 := key (b / (2 * M))
    have h2 : b ^ 2 * (2 * M ^ 2 + 2 * M) ≤ 0 := by
      have e1 : b / (2 * M) * b = b ^ 2 / (2 * M) := by ring
      have e2 : (b / (2 * M)) ^ 2 * D = b ^ 2 * D / (4 * M ^ 2) := by ring
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at h1
      nlinarith [mul_le_mul_of_nonneg_left hDM (by positivity : (0 : ℝ) ≤ b ^ 2 * (2 * M))]
    have h3 : b ^ 2 ≤ 0 := by
      by_contra h4
      push Not at h4
      have := mul_pos h4 (by positivity : (0 : ℝ) < 2 * M ^ 2 + 2 * M)
      linarith
    rw [← hb]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h3 (sq_nonneg b))
  -- `A` is onto, so `u = A z`, and `z + A u = 2m u`
  have hinj : Function.Injective A := by
    intro x y hxy
    have h0 : ‖A (x - y)‖ = 0 := by rw [map_sub, hxy, sub_self, norm_zero]
    rw [hnorm, norm_eq_zero, sub_eq_zero] at h0
    exact h0
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hinj) u
  have hzu : ⟪z, u⟫ = m := by rw [← hA z u, hz, hm]
  have hzAu : z + A u = (2 * m) • u := by
    obtain ⟨r, hr⟩ : ∃ r, r = z + A u - (2 * m) • u := ⟨_, rfl⟩
    have hur : ⟪u, r⟫ = 0 := by
      rw [hr, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_comm z u, hzu,
        ← hm, hu2]
      ring
    have h0 := hstat r hur
    have h1 : ⟪u, A r⟫ = ⟪z, r⟫ := by rw [← hz, hA]
    have hrr : ⟪r, r⟫ = 0 := by
      have e : ⟪r, r⟫ = ⟪z, r⟫ + ⟪A u, r⟫ - 2 * m * ⟪u, r⟫ := by
        nth_rewrite 1 [hr]
        rw [inner_sub_left, inner_add_left, real_inner_smul_left]
      rw [e, hur, real_inner_comm r (A u), ← h1]
      linarith
    have h2 : r = 0 := inner_self_eq_zero.1 hrr
    rw [hr, sub_eq_zero] at h2
    exact h2
  have hAAu : A (A u) = (2 * m) • A u - u := by
    have h := congrArg A hzAu
    rw [map_add, hz, map_smul] at h
    rw [← h]
    abel
  -- `−1 ≤ m < 1`
  have hm1 : m < 1 := by
    by_contra h
    push Not at h
    have h2 : ‖A u - u‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, hnorm, hu, real_inner_comm u (A u), ← hm, hu2]
      linarith
    have h3 : A u - u = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg (A u - u)])
    have h4 := hfix u (sub_eq_zero.1 h3)
    rw [h4, norm_zero] at hu
    norm_num at hu
  have hm_1 : -1 ≤ m := by
    have h := abs_real_inner_le_norm u (A u)
    rw [hnorm, hu, ← hm] at h
    linarith [neg_abs_le m]
  rcases eq_or_lt_of_le hm_1 with hmeq | hmgt
  · -- `m = −1`: `A = −1`, which turns every plane by `π`
    have hneg : ∀ y, A y = -y := by
      intro y
      have h1 := hle y
      rw [← hmeq] at h1
      have h2 : ‖A y + y‖ ^ 2 ≤ 0 := by
        rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
          real_inner_self_eq_norm_sq, hnorm, real_inner_self_eq_norm_sq, real_inner_comm y (A y)]
        linarith
      have h3 : A y + y = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg (A y + y)])
      exact eq_neg_of_add_eq_zero_left h3
    have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu; norm_num at hu
    obtain ⟨w, hw, huw⟩ := exists_unit_perp hE hu0
    refine ⟨u, w, hu, hw, huw, -1, 0, by norm_num, by norm_num, ?_, ?_⟩
    · rw [hneg]
      module
    · rw [hneg]
      module
  · -- `−1 < m < 1`: `A` turns the plane of `u` and `A u` by the angle with cosine `m`
    obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (1 - m ^ 2) := ⟨_, rfl⟩
    have hs2 : s ^ 2 = 1 - m ^ 2 := by rw [hsdef]; exact Real.sq_sqrt (by nlinarith)
    have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 (by nlinarith)
    have hd : ‖A u - m • u‖ = s := by
      have h : ‖A u - m • u‖ ^ 2 = s ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
          real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm, hu, real_inner_comm u (A u),
          ← hm, hu2, hs2]
        ring
      rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq hs0.le]
    refine ⟨u, s⁻¹ • (A u - m • u), hu, ?_, ?_, m, s, by linarith, hm1, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs0, hd, inv_mul_cancel₀ hs0.ne']
    · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, ← hm, hu2]
      ring
    · rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
      abel
    · rw [map_smul, map_sub, map_smul, hAAu]
      have e : -s = -(s⁻¹ * (1 - m ^ 2)) := by
        rw [← hs2]
        field_simp
      rw [e]
      module

/-- two angles in `[0, π)` whose difference has sine zero are equal -/
lemma eq_of_sin_sub_eq_zero {ψ ψ' : ℝ} (hψ : ψ ∈ Set.Ico 0 Real.pi) (hψ' : ψ' ∈ Set.Ico 0 Real.pi)
    (h : Real.sin (ψ - ψ') = 0) : ψ = ψ' := by
  have h1 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hψ.1, hψ.2, hψ'.1, hψ'.2])
    (by linarith [hψ.1, hψ.2, hψ'.1, hψ'.2])).1 h
  linarith

/-- **A plane that none of finitely many turns of `E` carries onto itself.**  Let finitely many
linear maps of `E`, of dimension four, keep the inner product, fix no vector but zero and differ
from `−1`.  Then some orthonormal pair `u, v` spans a plane that none of them carries onto itself:
for no map `A` among them and no `c, s` is `A u = c u + s v` and `A v = −s u + c v`.  With
`e₀, …, e₃` an orthonormal basis, the planes of `u(ψ) = cos ψ e₀ + sin ψ e₁` and `v = e₂`,
`0 ≤ ψ < π`, are infinitely many, and each map carries at most one of them onto itself.  For if `A`
carried two, `ψ ≠ ψ'`, then `A e₂ = −s u(ψ) + c e₂ = −s' u(ψ') + c' e₂` gives `c = c'` and
`s u(ψ) = s' u(ψ')`.  With `s ≠ 0` the unit vectors `u(ψ)` and `u(ψ')` are parallel, so `ψ = ψ'`.
With `s = 0`, `A e₂ = c e₂` with `c = −1`, as `c = 1` would fix `e₂`, and `A u(ψ) = −u(ψ)`,
`A u(ψ') = −u(ψ')`, so `cos ψ a + sin ψ d = 0 = cos ψ' a + sin ψ' d` with `a = A e₀ + e₀` and
`d = A e₁ + e₁`; as `ψ ≠ ψ'` this makes `a = d = 0`, so `A = −1` on `e₀, e₁, e₂`, and then on `e₃`
too, since `A e₃` is orthogonal to `A e₀, A e₁, A e₂` and `A e₃ = e₃` would fix `e₃`: `A = −1`. -/
lemma exists_plane_not_turned (b : OrthonormalBasis (Fin 4) ℝ E) {S : Set (E →ₗ[ℝ] E)}
    (hS : S.Finite) (hiso : ∀ A ∈ S, ∀ x y, ⟪A x, A y⟫ = ⟪x, y⟫)
    (hfix : ∀ A ∈ S, ∀ y, A y = y → y = 0) (hneg : ∀ A ∈ S, ∃ y, A y ≠ -y) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫ = 0 ∧
      ∀ A ∈ S, ∀ c s : ℝ, A u = c • u + s • v → A v = (-s) • u + c • v → False := by
  have hb : ∀ i j, ⟪b i, b j⟫ = if i = j then 1 else 0 := orthonormal_iff_ite.1 b.orthonormal
  have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hb1 : ∀ i, ⟪b i, b i⟫ = 1 := fun i => by rw [hb]; simp
  have hb0 : ∀ i j, i ≠ j → ⟪b i, b j⟫ = 0 := fun i j h => by rw [hb]; simp [h]
  -- the planes of `u ψ = cos ψ e₀ + sin ψ e₁` and `e₂`
  obtain ⟨u, hu⟩ : ∃ u : ℝ → E, u = fun ψ => Real.cos ψ • b 0 + Real.sin ψ • b 1 := ⟨_, rfl⟩
  have hu1 : ∀ ψ, ‖u ψ‖ = 1 := fun ψ => by
    have h := Crossing.norm_comb_sq (hb 0 1) (hbn 0) (hbn 1) (Real.cos ψ) (Real.sin ψ)
    rw [Real.cos_sq_add_sin_sq, one_pow, one_mul] at h
    rw [hu, ← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_one]
  have hu2 : ∀ ψ, ⟪u ψ, b 2⟫ = 0 := fun ψ => by
    rw [hu]
    simp [inner_add_left, real_inner_smul_left, hb]
  have huu : ∀ ψ ψ', ⟪u ψ, u ψ'⟫ = Real.cos (ψ - ψ') := fun ψ ψ' => by
    rw [hu, Real.cos_sub]
    simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hb]
    ring
  -- each map carries at most one of the planes onto itself
  have key : ∀ A ∈ S, {ψ ∈ Set.Ico 0 Real.pi | ∃ c s : ℝ,
      A (u ψ) = c • u ψ + s • b 2 ∧ A (b 2) = (-s) • u ψ + c • b 2}.Subsingleton := by
    rintro A hA ψ ⟨hψ, c, s, h1, h2⟩ ψ' ⟨hψ', c', s', h1', h2'⟩
    -- `c = c'` and `s u(ψ) = s' u(ψ')`
    have hc : c = c' := by
      have e := congrArg (fun x => ⟪x, b 2⟫) (h2.symm.trans h2')
      simp only [inner_add_left, real_inner_smul_left, hu2, hb1, mul_zero, zero_add, mul_one] at e
      exact e
    have hsu : s • u ψ = s' • u ψ' := by
      have e := h2.symm.trans h2'
      rw [hc] at e
      have e2 := add_right_cancel e
      rw [neg_smul, neg_smul, neg_inj] at e2
      exact e2
    by_contra hne
    have hsin : Real.sin (ψ - ψ') ≠ 0 := fun h => hne (eq_of_sin_sub_eq_zero hψ hψ' h)
    by_cases hs : s = 0
    · -- `s = 0`: `A e₂ = −e₂`, `A u(ψ) = −u(ψ)`, `A u(ψ') = −u(ψ')`
      have hs' : s' = 0 := by
        have e := congrArg (fun x => ⟪x, u ψ'⟫) hsu
        simp only [hs, zero_smul, inner_zero_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
          hu1, one_pow, mul_one] at e
        exact e.symm
      rw [hs, neg_zero, zero_smul, zero_add] at h2
      have hc1 : c = -1 := by
        have hn := hiso A hA (b 2) (b 2)
        rw [h2, real_inner_smul_left, real_inner_smul_right, hb1] at hn
        rcases mul_eq_zero.1 (show (c - 1) * (c + 1) = 0 by nlinarith) with h | h
        · exfalso
          rw [sub_eq_zero.1 h, one_smul] at h2
          have h0 := hbn 2
          rw [hfix A hA _ h2, norm_zero] at h0
          exact zero_ne_one h0
        · exact eq_neg_of_add_eq_zero_left h
      rw [hs, zero_smul, add_zero, hc1, neg_one_smul] at h1
      rw [hs', zero_smul, add_zero, ← hc, hc1, neg_one_smul] at h1'
      -- `cos ψ a + sin ψ d = 0` and `cos ψ' a + sin ψ' d = 0`
      obtain ⟨a, ha⟩ : ∃ a, a = A (b 0) + b 0 := ⟨_, rfl⟩
      obtain ⟨d, hd⟩ : ∃ d, d = A (b 1) + b 1 := ⟨_, rfl⟩
      have e1 : Real.cos ψ • a + Real.sin ψ • d = 0 := by
        have : Real.cos ψ • a + Real.sin ψ • d = A (u ψ) + u ψ := by
          rw [ha, hd, hu]
          simp only [map_add, map_smul]
          module
        rw [this, h1, neg_add_cancel]
      have e2 : Real.cos ψ' • a + Real.sin ψ' • d = 0 := by
        have : Real.cos ψ' • a + Real.sin ψ' • d = A (u ψ') + u ψ' := by
          rw [ha, hd, hu]
          simp only [map_add, map_smul]
          module
        rw [this, h1', neg_add_cancel]
      have ha0 : a = 0 := by
        have h3 : Real.sin (ψ - ψ') • a = Real.sin ψ • (Real.cos ψ' • a + Real.sin ψ' • d) -
            Real.sin ψ' • (Real.cos ψ • a + Real.sin ψ • d) := by
          rw [Real.sin_sub]
          module
        rw [e1, e2, smul_zero, smul_zero, sub_zero] at h3
        exact (smul_eq_zero.1 h3).resolve_left hsin
      have hd0 : d = 0 := by
        have h3 : Real.sin (ψ - ψ') • d = Real.cos ψ' • (Real.cos ψ • a + Real.sin ψ • d) -
            Real.cos ψ • (Real.cos ψ' • a + Real.sin ψ' • d) := by
          rw [Real.sin_sub]
          module
        rw [e1, e2, smul_zero, smul_zero, sub_zero] at h3
        exact (smul_eq_zero.1 h3).resolve_left hsin
      -- so `A = −1` on `e₀, e₁, e₂`, and then on `e₃`
      have hA0 : A (b 0) = -(b 0) := eq_neg_of_add_eq_zero_left (ha ▸ ha0)
      have hA1 : A (b 1) = -(b 1) := eq_neg_of_add_eq_zero_left (hd ▸ hd0)
      have hA2 : A (b 2) = -(b 2) := by rw [h2, hc1, neg_one_smul]
      have hA3 : A (b 3) = -(b 3) := by
        have h30 : ⟪b 0, A (b 3)⟫ = 0 := by
          have := hiso A hA (b 0) (b 3)
          rw [hb0 0 3 (by decide), hA0, inner_neg_left, neg_eq_zero] at this
          exact this
        have h31 : ⟪b 1, A (b 3)⟫ = 0 := by
          have := hiso A hA (b 1) (b 3)
          rw [hb0 1 3 (by decide), hA1, inner_neg_left, neg_eq_zero] at this
          exact this
        have h32 : ⟪b 2, A (b 3)⟫ = 0 := by
          have := hiso A hA (b 2) (b 3)
          rw [hb0 2 3 (by decide), hA2, inner_neg_left, neg_eq_zero] at this
          exact this
        have hsum := b.sum_repr' (A (b 3))
        rw [Fin.sum_univ_four, h30, h31, h32, zero_smul, zero_smul, zero_smul, zero_add, zero_add,
          zero_add] at hsum
        have hn := hiso A hA (b 3) (b 3)
        rw [hb1, ← hsum, real_inner_smul_left, real_inner_smul_right, hb1, mul_one] at hn
        rcases mul_eq_zero.1 (show (⟪b 3, A (b 3)⟫ - 1) * (⟪b 3, A (b 3)⟫ + 1) = 0 by nlinarith)
          with h | h
        · exfalso
          rw [sub_eq_zero.1 h, one_smul] at hsum
          have h0 := hbn 3
          rw [hfix A hA _ hsum.symm, norm_zero] at h0
          exact zero_ne_one h0
        · rw [← hsum, eq_neg_of_add_eq_zero_left h, neg_one_smul]
      obtain ⟨y, hy⟩ := hneg A hA
      apply hy
      rw [← b.sum_repr' y, map_sum, Fin.sum_univ_four, Fin.sum_univ_four]
      simp only [map_smul, hA0, hA1, hA2, hA3, smul_neg]
      abel
    · -- `s ≠ 0`: `u(ψ)` and `u(ψ')` are parallel
      have e1 := congrArg (fun x => ⟪x, u ψ'⟫) hsu
      have e2 := congrArg (fun x => ⟪x, u ψ⟫) hsu
      simp only [real_inner_smul_left, huu, sub_self, Real.cos_zero, mul_one] at e1 e2
      rw [← neg_sub ψ ψ', Real.cos_neg] at e2
      -- `s cos(ψ − ψ') = s'` and `s = s' cos(ψ − ψ')`
      have hcos : Real.cos (ψ - ψ') ^ 2 = 1 := by
        have h3 : s * (Real.cos (ψ - ψ') ^ 2 - 1) = 0 := by rw [← e1] at e2; linear_combination -e2
        have := (mul_eq_zero.1 h3).resolve_left hs
        linarith
      have := Real.sin_sq_add_cos_sq (ψ - ψ')
      exact hsin (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith))
  -- a plane that none carries onto itself
  have hBad : (⋃ A ∈ S, {ψ ∈ Set.Ico 0 Real.pi | ∃ c s : ℝ,
      A (u ψ) = c • u ψ + s • b 2 ∧ A (b 2) = (-s) • u ψ + c • b 2}).Finite :=
    hS.biUnion fun A hA => (key A hA).finite
  obtain ⟨ψ, hψ, hψ'⟩ := ((Set.Ico_infinite Real.pi_pos).sdiff hBad).nonempty
  refine ⟨u ψ, b 2, hu1 ψ, hbn 2, hu2 ψ, fun A hA c s h1 h2 => hψ' ?_⟩
  exact Set.mem_biUnion hA ⟨hψ, c, s, h1, h2⟩

end Rotation

end Quotients
