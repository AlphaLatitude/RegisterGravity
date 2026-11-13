import RegisterGravity.Geodesics

/-!
# One geodesic through two points, as one ring through two cells (Sec. II)

By the last sentence of Postulate 2 every largest ring is a closed geodesic of space, made of its
cells as segments of length `ℓ_c`; the files take it as a hypothesis, as a postulate.  It matches the register on pairs of cells (Sec. II): two
cells that are not opposite lie on exactly one largest ring (Postulate 2, `Horizon.unique_loop`),
and two points of space that are not antipodal lie on exactly one geodesic
(`geodesic_through_two`).  This file proves that fact of geometry in the space at an instant of
de Sitter space of radius `ρ`, the sphere of radius `ρ` of a real inner product space `E`: the
geodesics of that space run on its great circles (`Geodesic.IsGeodesic.greatCircle`), each closed,
of length `2πρ`, and two of its points that are neither equal nor antipodal lie on exactly one
great circle (`greatCircle_through`, `greatCircle_unique`).  That the space at an instant is the
three-sphere itself, and no quotient of it, the rings give (`Space.sphere_rings`).
-/

open RealInnerProductSpace Set

namespace TwoCells

/-! ### Great circles -/

section Circles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a b : E} {ρ : ℝ}

/-- A point `s a + t b` of the sphere of radius `ρ` lies on the great circle through `a` and `b`. -/
lemma mem_greatCircle_of_eq (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (hρ : 0 < ρ)
    {x : E} {s t : ℝ} (hx : x = s • a + t • b) (hn : ‖x‖ = ρ) : x ∈ Crossing.greatCircle a b := by
  refine ⟨s, t, ?_, hx⟩
  have h := Crossing.norm_comb_sq hab ha hb s t
  rw [← hx, hn] at h
  have hρ2 : ρ ^ 2 ≠ 0 := by positivity
  exact (mul_right_cancel₀ hρ2 (h.symm.trans (one_mul _).symm))

/-- The points of a great circle lie on the sphere of radius `ρ`. -/
lemma norm_of_mem_greatCircle (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (hρ : 0 < ρ)
    {x : E} (hx : x ∈ Crossing.greatCircle a b) : ‖x‖ = ρ := by
  obtain ⟨u, v, huv, rfl⟩ := hx
  have h := Crossing.norm_comb_sq hab ha hb u v
  rw [huv, one_mul] at h
  exact (sq_eq_sq₀ (norm_nonneg _) hρ.le).1 h

/-- **Two unit pairs with a vanishing determinant are equal or opposite**: if
`u₁² + v₁² = u₂² + v₂² = 1` and `u₁ v₂ − u₂ v₁ = 0`, then `(u₂, v₂) = ±(u₁, v₁)`. -/
lemma det_ne_zero {u₁ v₁ u₂ v₂ : ℝ} (h₁ : u₁ ^ 2 + v₁ ^ 2 = 1) (h₂ : u₂ ^ 2 + v₂ ^ 2 = 1)
    (hne : ¬ (u₂ = u₁ ∧ v₂ = v₁)) (hne' : ¬ (u₂ = -u₁ ∧ v₂ = -v₁)) : u₁ * v₂ - u₂ * v₁ ≠ 0 := by
  intro hD
  have hu : u₂ = (u₁ * u₂ + v₁ * v₂) * u₁ := by linear_combination (-u₂) * h₁ - v₁ * hD
  have hv : v₂ = (u₁ * u₂ + v₁ * v₂) * v₁ := by linear_combination u₁ * hD - v₂ * h₁
  obtain ⟨l, hl⟩ : ∃ l, l = u₁ * u₂ + v₁ * v₂ := ⟨_, rfl⟩
  rw [← hl] at hu hv
  have hl2 : l ^ 2 = 1 := by
    have e : u₂ ^ 2 + v₂ ^ 2 = l ^ 2 * (u₁ ^ 2 + v₁ ^ 2) := by
      rw [hu, hv]
      ring
    rw [h₂, h₁, mul_one] at e
    exact e.symm
  have hfac : (l - 1) * (l + 1) = 0 := by linear_combination hl2
  rcases mul_eq_zero.1 hfac with h | h
  · have h1 : l = 1 := by linarith
    exact hne ⟨by rw [hu, h1, one_mul], by rw [hv, h1, one_mul]⟩
  · have h1 : l = -1 := by linarith
    exact hne' ⟨by rw [hu, h1, neg_one_mul], by rw [hv, h1, neg_one_mul]⟩

/-- Two points of a great circle that are neither equal nor antipodal, `p = u₁ a + v₁ b` and
`q = u₂ a + v₂ b`, have `u₁ v₂ − u₂ v₁ ≠ 0`. -/
lemma det_ne_zero_of_mem {p q : E} {u₁ v₁ u₂ v₂ : ℝ} (h₁ : u₁ ^ 2 + v₁ ^ 2 = 1)
    (h₂ : u₂ ^ 2 + v₂ ^ 2 = 1) (hp : p = u₁ • a + v₁ • b) (hq : q = u₂ • a + v₂ • b)
    (hqp : q ≠ p) (hqp' : q ≠ -p) : u₁ * v₂ - u₂ * v₁ ≠ 0 :=
  det_ne_zero h₁ h₂ (fun ⟨e1, e2⟩ => hqp (by rw [hq, hp, e1, e2]))
    (fun ⟨e1, e2⟩ => hqp' (by rw [hq, hp, e1, e2]; module))

/-- **A great circle through two points**: two points of the sphere of radius `ρ` that are neither
equal nor antipodal lie on a great circle, the one through `p` and `ρ w/‖w‖`, with `w` the part of
`q` orthogonal to `p`. -/
theorem greatCircle_through (hρ : 0 < ρ) {p q : E} (hp : ‖p‖ = ρ) (hq : ‖q‖ = ρ) (hqp : q ≠ p)
    (hqp' : q ≠ -p) : ∃ a b : E, ⟪a, b⟫ = 0 ∧ ‖a‖ = ρ ∧ ‖b‖ = ρ ∧
      p ∈ Crossing.greatCircle a b ∧ q ∈ Crossing.greatCircle a b := by
  have hρ2 : ρ ^ 2 ≠ 0 := by positivity
  have hpp : ⟪p, p⟫ = ρ ^ 2 := by rw [real_inner_self_eq_norm_sq, hp]
  have hqq : ⟪q, q⟫ = ρ ^ 2 := by rw [real_inner_self_eq_norm_sq, hq]
  obtain ⟨s, hs⟩ : ∃ s, s = ⟪p, q⟫ / ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = q - s • p := ⟨_, rfl⟩
  have hpw : ⟪p, w⟫ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, hpp, hs, div_mul_cancel₀ _ hρ2, sub_self]
  have hqe : q = s • p + w := by
    rw [hw]
    abel
  have hww : ‖w‖ ^ 2 = ρ ^ 2 - s ^ 2 * ρ ^ 2 := by
    have e := hqq
    rw [hqe, real_inner_self_eq_norm_sq, norm_add_sq_real, real_inner_smul_left, hpw, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, hp] at e
    linarith
  have hw0 : ‖w‖ ≠ 0 := by
    intro h0
    have hs2 : (s - 1) * (s + 1) = 0 := by
      have e : s ^ 2 * ρ ^ 2 = 1 * ρ ^ 2 := by rw [h0] at hww; linarith
      have := mul_right_cancel₀ hρ2 e
      linear_combination this
    have hwz : w = 0 := norm_eq_zero.1 h0
    rw [hwz, add_zero] at hqe
    rcases mul_eq_zero.1 hs2 with h | h
    · exact hqp (by rw [hqe, show s = 1 by linarith, one_smul])
    · exact hqp' (by rw [hqe, show s = -1 by linarith, neg_one_smul])
  have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  refine ⟨p, (ρ / ‖w‖) • w, ?_, hp, ?_, ⟨1, 0, by norm_num, by simp⟩, ⟨s, ‖w‖ / ρ, ?_, ?_⟩⟩
  · rw [real_inner_smul_right, hpw, mul_zero]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ hwpos)]
    field_simp
  · rw [div_pow, hww]
    field_simp
    ring
  · rw [smul_smul, show ‖w‖ / ρ * (ρ / ‖w‖) = 1 by field_simp, one_smul, hqe]

/-- **A great circle through two points that are neither equal nor antipodal lies on any other
great circle through them**: its points are combinations of the two points, and so are the points
of the other.  With the converse, the two great circles are the same (`greatCircle_unique`). -/
theorem greatCircle_subset {a' b' : E} (hρ : 0 < ρ) (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ)
    (hb : ‖b‖ = ρ) (hab' : ⟪a', b'⟫ = 0) (ha' : ‖a'‖ = ρ) (hb' : ‖b'‖ = ρ) {p q : E}
    (hp : p ∈ Crossing.greatCircle a b) (hq : q ∈ Crossing.greatCircle a b)
    (hp' : p ∈ Crossing.greatCircle a' b') (hq' : q ∈ Crossing.greatCircle a' b')
    (hqp : q ≠ p) (hqp' : q ≠ -p) : Crossing.greatCircle a' b' ⊆ Crossing.greatCircle a b := by
  intro x hx
  have hxn := norm_of_mem_greatCircle hab' ha' hb' hρ hx
  obtain ⟨u, v, -, rfl⟩ := hx
  obtain ⟨u₁, v₁, h₁, hp1⟩ := hp'
  obtain ⟨u₂, v₂, h₂, hq1⟩ := hq'
  have hD := det_ne_zero_of_mem h₁ h₂ hp1 hq1 hqp hqp'
  obtain ⟨s₁, t₁, -, hp2⟩ := hp
  obtain ⟨s₂, t₂, -, hq2⟩ := hq
  have e : (u₁ * v₂ - u₂ * v₁) • (u • a' + v • b') =
      (u * v₂ - v * u₂) • p + (v * u₁ - u * v₁) • q := by
    rw [hp1, hq1]
    module
  have e' : u • a' + v • b' =
      (u₁ * v₂ - u₂ * v₁)⁻¹ • ((u * v₂ - v * u₂) • p + (v * u₁ - u * v₁) • q) := by
    rw [← e, smul_smul, inv_mul_cancel₀ hD, one_smul]
  refine mem_greatCircle_of_eq hab ha hb hρ
    (s := (u₁ * v₂ - u₂ * v₁)⁻¹ * ((u * v₂ - v * u₂) * s₁ + (v * u₁ - u * v₁) * s₂))
    (t := (u₁ * v₂ - u₂ * v₁)⁻¹ * ((u * v₂ - v * u₂) * t₁ + (v * u₁ - u * v₁) * t₂)) ?_ hxn
  rw [e', hp2, hq2]
  module

/-- **Only one great circle passes through two points that are neither equal nor antipodal.** -/
theorem greatCircle_unique {a' b' : E} (hρ : 0 < ρ) (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ)
    (hb : ‖b‖ = ρ) (hab' : ⟪a', b'⟫ = 0) (ha' : ‖a'‖ = ρ) (hb' : ‖b'‖ = ρ) {p q : E}
    (hp : p ∈ Crossing.greatCircle a b) (hq : q ∈ Crossing.greatCircle a b)
    (hp' : p ∈ Crossing.greatCircle a' b') (hq' : q ∈ Crossing.greatCircle a' b')
    (hqp : q ≠ p) (hqp' : q ≠ -p) : Crossing.greatCircle a' b' = Crossing.greatCircle a b :=
  Subset.antisymm (greatCircle_subset hρ hab ha hb hab' ha' hb' hp hq hp' hq' hqp hqp')
    (greatCircle_subset hρ hab' ha' hb' hab ha hb hp' hq' hp hq hqp hqp')

/-- The path in space of the great circle through `a` and `b` run at unit angular speed:
`θ ↦ cos θ · a + sin θ · b` runs through every point `u a + v b` with `u² + v² = 1` and no other. -/
lemma circleCurve_range :
    range (fun t => ((Geodesic.circleCurve a b 1).pos t).2) = Crossing.greatCircle a b := by
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨Real.cos (1 * θ), Real.sin (1 * θ), Real.cos_sq_add_sin_sq _, rfl⟩
  · rintro ⟨u, v, huv, rfl⟩
    obtain ⟨θ, hcos, hsin⟩ := Geodesic.exists_angle huv
    exact ⟨θ, by show Real.cos (1 * θ) • a + Real.sin (1 * θ) • b = _; rw [one_mul, hcos, hsin]⟩

/-- **Exactly one geodesic of space passes through two points that are neither equal nor
antipodal** (Sec. II).  In the space at an instant of de Sitter space of radius `ρ`, the sphere of
radius `ρ` of `E`, a geodesic runs on a great circle (`Geodesic.IsGeodesic.greatCircle`), and
exactly one great circle passes through the two points (`greatCircle_through`,
`greatCircle_unique`).  So there is such a geodesic, closed, of length `2πρ`
(`Geodesic.IsGeodesic.hasLength`), and any two have the same path. -/
theorem geodesic_through_two (hρ : 0 < ρ) {p q : E} (hp : ‖p‖ = ρ) (hq : ‖q‖ = ρ) (hqp : q ≠ p)
    (hqp' : q ≠ -p) :
    (∃ γ : Geodesic.Curve ℝ E, Geodesic.IsGeodesic (ρ ^ 2) γ ∧ Geodesic.IsSpacelike γ ∧
      Geodesic.InSpace γ ∧ Geodesic.HasLength γ (2 * Real.pi * ρ) ∧
      p ∈ range (fun t => (γ.pos t).2) ∧ q ∈ range (fun t => (γ.pos t).2)) ∧
    ∀ γ₁ γ₂ : Geodesic.Curve ℝ E,
      Geodesic.IsGeodesic (ρ ^ 2) γ₁ → Geodesic.IsSpacelike γ₁ → Geodesic.InSpace γ₁ →
      p ∈ range (fun t => (γ₁.pos t).2) → q ∈ range (fun t => (γ₁.pos t).2) →
      Geodesic.IsGeodesic (ρ ^ 2) γ₂ → Geodesic.IsSpacelike γ₂ → Geodesic.InSpace γ₂ →
      p ∈ range (fun t => (γ₂.pos t).2) → q ∈ range (fun t => (γ₂.pos t).2) →
      range (fun t => (γ₁.pos t).2) = range (fun t => (γ₂.pos t).2) := by
  constructor
  · obtain ⟨a, b, hab, ha, hb, hpm, hqm⟩ := greatCircle_through hρ hp hq hqp hqp'
    have hg := Geodesic.circleCurve_geodesic (ω := 1) hab ha hb
    have hs := Geodesic.circleCurve_spacelike (ω := 1) hab ha hb hρ one_ne_zero
    have hl := hg.hasLength (by positivity) hs
    rw [Real.sqrt_sq hρ.le] at hl
    refine ⟨Geodesic.circleCurve a b 1, hg, hs, Geodesic.circleCurve_inSpace, hl, ?_, ?_⟩
    · rw [circleCurve_range]
      exact hpm
    · rw [circleCurve_range]
      exact hqm
  · intro γ₁ γ₂ g₁ s₁ i₁ p₁ q₁ g₂ s₂ i₂ p₂ q₂
    obtain ⟨o₁, n₁, m₁, r₁⟩ := g₁.greatCircle hρ s₁ i₁
    obtain ⟨o₂, n₂, m₂, r₂⟩ := g₂.greatCircle hρ s₂ i₂
    rw [r₁] at p₁ q₁ ⊢
    rw [r₂] at p₂ q₂ ⊢
    exact (greatCircle_unique hρ o₂ n₂ m₂ o₁ n₁ m₁ p₂ q₂ p₁ q₁ hqp hqp')

end Circles

end TwoCells
