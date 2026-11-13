import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Archimedes' hat-box theorem in four dimensions (Sec. II, "Counting in the bulk")

Archimedes found that a zone of a sphere has the area of the band of the circumscribed cylinder
between the same two planes, so the area of a zone is proportional to its height.  The count of a
sphere's strings uses the four-dimensional counterpart: on the unit three-sphere, the points `ξ`
with `⟪a, ξ⟫² + ⟪b, ξ⟫² > k`, for orthonormal `a` and `b` and `0 ≤ k < 1`, take the fraction
`1 − k` of the sphere (`hatBox`).  These are the points within a given distance of the great circle
through `a` and `b`.

The proof evaluates no integral.  The measure that a Haar measure `μ` gives a set of the unit
sphere is the dimension of the space times the measure of the cone over the set, cut off at radius
one (`Measure.toSphere_apply'`), and the cone over the points above is the set of points `y` of the
unit ball with `k‖y‖² < ⟪a, y⟫² + ⟪b, y⟫²` (`cone_eq`).
Split the space into the plane of `a` and `b` and the plane orthogonal to it, so that a point is
`x + z`; the set is then `k(‖x‖² + ‖z‖²) < ‖x‖²` within `‖x‖² + ‖z‖² < 1` (`cone_measure`).  Its
measure is the integral over `z` of the measure of a ring of the first plane, `1 − ‖z‖²/(1 − k)`
times the unit disk (`annulus`), and the same for the ball with `k = 0` is `1 − ‖z‖²` times the unit
disk (`disk`).  The change of variable `z = √(1 − k) w` in the second plane turns the first
integral into `1 − k` times the second (`core`).  Two Haar measures differ by a constant factor
(`haar_ratio`), so the fraction found for the product of the two planes holds for `μ`.
-/

open MeasureTheory Metric Module
open scoped ENNReal

namespace HatBox

section Plane

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] (μ : Measure P) [μ.IsAddHaarMeasure]

/-- In a plane, the disk `‖x‖² < β` has `β` times the measure of the unit disk. -/
lemma disk (hP : finrank ℝ P = 2) (β : ℝ) :
    μ {x | ‖x‖ ^ 2 < β} = ENNReal.ofReal β * μ (ball 0 1) := by
  have : Nontrivial P := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  rcases le_or_gt β 0 with hβ | hβ
  · have e : {x : P | ‖x‖ ^ 2 < β} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans hβ (sq_nonneg _)
    rw [e, measure_empty, ENNReal.ofReal_eq_zero.2 hβ, zero_mul]
  · have e : {x : P | ‖x‖ ^ 2 < β} = ball 0 (Real.sqrt β) := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_ball, dist_zero_right]
      rw [Real.lt_sqrt (norm_nonneg x)]
    rw [e, Measure.addHaar_ball μ 0 (Real.sqrt_nonneg β), hP, Real.sq_sqrt hβ.le]

/-- In a plane, the ring `α < ‖x‖² < β` has `β − α` times the measure of the unit disk. -/
lemma annulus (hP : finrank ℝ P = 2) {α : ℝ} (hα : 0 ≤ α) (β : ℝ) :
    μ {x | α < ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < β} = ENNReal.ofReal (β - α) * μ (ball 0 1) := by
  rcases le_or_gt β α with hβ | hβ
  · have e : {x : P | α < ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < β} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h
      linarith
    rw [e, measure_empty, ENNReal.ofReal_eq_zero.2 (by linarith), zero_mul]
  · have hsub : {x : P | ‖x‖ ^ 2 ≤ α} ⊆ {x | ‖x‖ ^ 2 < β} := fun x hx =>
      lt_of_le_of_lt (show ‖x‖ ^ 2 ≤ α from hx) hβ
    have e : {x : P | α < ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < β} = {x | ‖x‖ ^ 2 < β} \ {x | ‖x‖ ^ 2 ≤ α} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le]
      exact and_comm
    have hc : {x : P | ‖x‖ ^ 2 ≤ α} = closedBall 0 (Real.sqrt α) := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_closedBall, dist_zero_right]
      rw [Real.le_sqrt (norm_nonneg x) hα]
    have hcm : μ {x : P | ‖x‖ ^ 2 ≤ α} = ENNReal.ofReal α * μ (ball 0 1) := by
      rw [hc, Measure.addHaar_closedBall μ 0 (Real.sqrt_nonneg α), hP, Real.sq_sqrt hα]
    have hfin : μ (ball (0 : P) 1) ≠ ∞ := measure_ball_lt_top.ne
    rw [e, measure_sdiff hsub (hc ▸ measurableSet_closedBall).nullMeasurableSet
      (by rw [hcm]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin), disk μ hP β, hcm,
      ← ENNReal.sub_mul (fun _ _ => hfin), ENNReal.ofReal_sub _ hα]

end Plane

section Product

section Sets

variable {P Q : Type*} [NormedAddCommGroup P] [NormedAddCommGroup Q]

/-- the points `(x, z)` with `‖x‖² + ‖z‖² < 1` -/
def ball2 : Set (P × Q) := {q | ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 < 1}

/-- the points of `ball2` with `k (‖x‖² + ‖z‖²) < ‖x‖²` -/
def cone (k : ℝ) : Set (P × Q) :=
  {q | ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 < 1 ∧ k * (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) < ‖q.1‖ ^ 2}

lemma slice_ball2 (z : Q) :
    (fun x : P => (x, z)) ⁻¹' ball2 = {x : P | ‖x‖ ^ 2 < 1 - ‖z‖ ^ 2} := by
  ext x
  simp only [ball2, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

lemma slice_cone {k : ℝ} (hk1 : k < 1) (z : Q) :
    (fun x : P => (x, z)) ⁻¹' cone k =
      {x : P | k * ‖z‖ ^ 2 / (1 - k) < ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < 1 - ‖z‖ ^ 2} := by
  have h1k : 0 < 1 - k := by linarith
  ext x
  simp only [cone, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [div_lt_iff₀ h1k]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

end Sets

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q] [MeasurableSpace Q] [BorelSpace Q]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma measurableSet_ball2 : MeasurableSet (ball2 : Set (P × Q)) :=
  (isOpen_lt (by fun_prop) continuous_const).measurableSet

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma measurableSet_cone (k : ℝ) : MeasurableSet (cone k : Set (P × Q)) := by
  have e : (cone k : Set (P × Q)) = {q : P × Q | ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 < 1} ∩
      {q : P × Q | k * (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) < ‖q.1‖ ^ 2} := rfl
  rw [e]
  exact ((isOpen_lt (by fun_prop) continuous_const).inter
    (isOpen_lt (by fun_prop) (by fun_prop))).measurableSet

variable (μ : Measure P) [μ.IsAddHaarMeasure] (ν : Measure Q) [ν.IsAddHaarMeasure]

/-- **The hat-box theorem in the product of two planes.**  In `P × Q`, two planes, the points of
`ball2` with `k (‖x‖² + ‖z‖²) < ‖x‖²` take the fraction `1 − k` of it.  Each slice at fixed `z` is
a ring of the plane `P`, of measure `1 − ‖z‖²/(1 − k)` times the unit disk (`annulus`); the slice
of `ball2` is a disk, of measure `1 − ‖z‖²` times it (`disk`); and the change of variable
`z = √(1 − k) w` in the plane `Q` turns the first into the second times `1 − k`. -/
theorem core (hP : finrank ℝ P = 2) (hQ : finrank ℝ Q = 2) {k : ℝ} (hk0 : 0 ≤ k)
    (hk1 : k < 1) :
    (μ.prod ν) (cone k) = ENNReal.ofReal (1 - k) * (μ.prod ν) ball2 := by
  have h1k : 0 < 1 - k := by linarith
  obtain ⟨t, ht2, htpos⟩ : ∃ t : ℝ, t ^ 2 = 1 - k ∧ 0 < t :=
    ⟨Real.sqrt (1 - k), Real.sq_sqrt h1k.le, Real.sqrt_pos.2 h1k⟩
  rw [Measure.prod_apply_symm (measurableSet_cone k), Measure.prod_apply_symm measurableSet_ball2]
  have e1 : ∀ z : Q, μ ((fun x : P => (x, z)) ⁻¹' cone k) =
      ENNReal.ofReal (1 - ‖t⁻¹ • z‖ ^ 2) * μ (ball 0 1) := fun z => by
    rw [slice_cone hk1, annulus μ hP (by positivity)]
    congr 2
    rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_pos htpos, inv_pow, ht2]
    field_simp
    ring
  have e2 : ∀ z : Q, μ ((fun x : P => (x, z)) ⁻¹' ball2) =
      ENNReal.ofReal (1 - ‖z‖ ^ 2) * μ (ball 0 1) := fun z => by
    rw [slice_ball2, disk μ hP]
  simp_rw [e1, e2]
  have hmeas : Measurable (fun w : Q => ENNReal.ofReal (1 - ‖w‖ ^ 2) * μ (ball 0 1)) := by
    fun_prop
  rw [← lintegral_map hmeas (measurable_const_smul t⁻¹),
    Measure.map_addHaar_smul ν (inv_ne_zero htpos.ne'), lintegral_smul_measure, hQ, smul_eq_mul]
  congr 2
  rw [inv_pow, inv_inv, abs_of_nonneg (sq_nonneg t), ht2]

end Product

/-- **Ratios of measures are the same for every Haar measure**: two additive Haar measures on a
finite-dimensional space differ by a constant factor (`Measure.addHaarMeasure_unique`), so a
relation `π A = t π B` for one holds for every other. -/
lemma haar_ratio {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] (m π : Measure G) [m.IsAddHaarMeasure]
    [π.IsAddHaarMeasure] {A B : Set G} {t : ℝ≥0∞} (h : π A = t * π B) : m A = t * m B := by
  let K₀ : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h0 : π K₀ ≠ 0 := (Measure.measure_pos_of_nonempty_interior π K₀.interior_nonempty).ne'
  have htop : π K₀ ≠ ∞ := K₀.isCompact.measure_lt_top.ne
  rw [Measure.addHaarMeasure_unique π K₀] at h
  rw [Measure.addHaarMeasure_unique m K₀]
  simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
  rw [mul_left_comm] at h
  rw [(ENNReal.mul_right_inj h0 htop).1 h, mul_left_comm]

section Space

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma comb_inner_norm {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ = 0) (u v : ℝ) :
    ⟪a, u • a + v • b⟫ = u ∧ ⟪b, u • a + v • b⟫ = v ∧ ‖u • a + v • b‖ ^ 2 = u ^ 2 + v ^ 2 := by
  have haa : ⟪a, a⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
  have hbb : ⟪b, b⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb, one_pow]
  have hba : ⟪b, a⟫ = 0 := by rw [real_inner_comm]; exact hab
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, haa, hab]
    ring
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hba, hbb]
    ring
  · rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      haa, hab, hba, hbb]
    ring

/-- The plane of two orthonormal vectors `a`, `b` has dimension two. -/
lemma plane_finrank {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ = 0) :
    finrank ℝ (Submodule.span ℝ (Set.range ![a, b])) = 2 := by
  have hli : LinearIndependent ℝ ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    obtain ⟨h1, h2, -⟩ := comb_inner_norm ha hb hab s t
    rw [h, inner_zero_right] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [finrank_span_eq_card hli, Fintype.card_fin]

/-- A vector of the plane of `a` and `b` has squared length `⟪a, x⟫² + ⟪b, x⟫²`. -/
lemma plane_norm {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ = 0) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range ![a, b])) :
    ‖x‖ ^ 2 = ⟪a, x⟫ ^ 2 + ⟪b, x⟫ ^ 2 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨h1, h2, h3⟩ := comb_inner_norm ha hb hab (c 0) (c 1)
  rw [h1, h2, h3]

open scoped Pointwise in
/-- The cone over a set of the unit sphere, cut off at radius one, for the set of directions `ξ`
with `k < ⟪a, ξ⟫² + ⟪b, ξ⟫²`: the points `y` of the unit ball with `k‖y‖² < ⟪a, y⟫² + ⟪b, y⟫²`. -/
lemma cone_eq (k : ℝ) (a b : E) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' {ξ : sphere (0 : E) 1 | k < ⟪a, (ξ : E)⟫ ^ 2 + ⟪b, (ξ : E)⟫ ^ 2}) =
      {y : E | ‖y‖ < 1 ∧ k * ‖y‖ ^ 2 < ⟪a, y⟫ ^ 2 + ⟪b, y⟫ ^ 2} := by
  ext y
  simp only [Set.mem_smul, Set.mem_image, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, _, ⟨ξ, hξ, rfl⟩, rfl⟩
    have hξ1 : ‖(ξ : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ξ.2
    have hn : ‖t • (ξ : E)‖ = t := by rw [norm_smul, hξ1, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
    refine ⟨by rw [hn]; exact ht1, ?_⟩
    rw [hn, real_inner_smul_right, real_inner_smul_right]
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith
  · rintro ⟨h1, h2⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at h2
    have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hξ : ‖y‖⁻¹ • y ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    refine ⟨‖y‖, ⟨hn, h1⟩, _, ⟨⟨_, hξ⟩, ?_, rfl⟩, ?_⟩
    · show k < ⟪a, ‖y‖⁻¹ • y⟫ ^ 2 + ⟪b, ‖y‖⁻¹ • y⟫ ^ 2
      rw [real_inner_smul_right, real_inner_smul_right, mul_pow, mul_pow, ← mul_add, inv_pow,
        lt_inv_mul_iff₀ (by positivity), mul_comm]
      exact h2
    · show ‖y‖ • ‖y‖⁻¹ • y = y
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **The hat-box theorem for the ball of a four-dimensional space.**  The points `y` of the unit
ball with `k‖y‖² < ⟪a, y⟫² + ⟪b, y⟫²`, for orthonormal `a`, `b`, take the fraction `1 − k` of it.
Split the space into the plane `K` of `a` and `b` and the plane `Kᗮ` orthogonal to it: a point is
`x + z`, with `‖y‖² = ‖x‖² + ‖z‖²` and `⟪a, y⟫² + ⟪b, y⟫² = ‖x‖²`, and `core` gives the fraction
for the product of the planes. -/
theorem cone_measure (hE : finrank ℝ E = 4) {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫ = 0) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    μ {y | ‖y‖ < 1 ∧ k * ‖y‖ ^ 2 < ⟪a, y⟫ ^ 2 + ⟪b, y⟫ ^ 2} =
      ENNReal.ofReal (1 - k) * μ (ball 0 1) := by
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range ![a, b])
  have hK : finrank ℝ K = 2 := plane_finrank ha hb hab
  have hKo : finrank ℝ Kᗮ = 2 := by
    have := Submodule.finrank_add_finrank_orthogonal K
    omega
  have hc : IsCompl K Kᗮ := Submodule.isCompl_orthogonal K
  let g : (K × Kᗮ) ≃ₗ[ℝ] E := Submodule.prodEquivOfIsCompl K Kᗮ hc
  let f : E ≃L[ℝ] K × Kᗮ := g.symm.toContinuousLinearEquiv
  have hf : ∀ y : E, ((f y).1 : E) + ((f y).2 : E) = y := fun y => by
    have e := g.apply_symm_apply y
    rwa [Submodule.coe_prodEquivOfIsCompl'] at e
  have horth : ∀ y : E, ⟪((f y).1 : E), ((f y).2 : E)⟫ = 0 := fun y =>
    Submodule.inner_right_of_mem_orthogonal (f y).1.2 (f y).2.2
  have hnorm : ∀ y : E, ‖y‖ ^ 2 = ‖(f y).1‖ ^ 2 + ‖(f y).2‖ ^ 2 := fun y => by
    conv_lhs => rw [← hf y]
    rw [norm_add_sq_real, horth y, mul_zero, add_zero]
    rfl
  have hplane : ∀ y : E, ⟪a, y⟫ ^ 2 + ⟪b, y⟫ ^ 2 = ‖(f y).1‖ ^ 2 := fun y => by
    have haK : a ∈ K := Submodule.subset_span ⟨0, rfl⟩
    have hbK : b ∈ K := Submodule.subset_span ⟨1, rfl⟩
    have e1 : ⟪a, y⟫ = ⟪a, ((f y).1 : E)⟫ := by
      conv_lhs => rw [← hf y]
      rw [inner_add_right, Submodule.inner_right_of_mem_orthogonal haK (f y).2.2, add_zero]
    have e2 : ⟪b, y⟫ = ⟪b, ((f y).1 : E)⟫ := by
      conv_lhs => rw [← hf y]
      rw [inner_add_right, Submodule.inner_right_of_mem_orthogonal hbK (f y).2.2, add_zero]
    rw [e1, e2, ← plane_norm ha hb hab (f y).1.2]
    rfl
  have e1 : {y : E | ‖y‖ < 1 ∧ k * ‖y‖ ^ 2 < ⟪a, y⟫ ^ 2 + ⟪b, y⟫ ^ 2} = f ⁻¹' cone k := by
    ext y
    simp only [cone, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← hnorm y, ← hplane y, sq_lt_one_iff₀ (norm_nonneg y)]
  have e2 : ball (0 : E) 1 = f ⁻¹' ball2 := by
    ext y
    simp only [ball2, Set.mem_preimage, Set.mem_ofPred_eq, mem_ball, dist_zero_right]
    rw [← hnorm y, sq_lt_one_iff₀ (norm_nonneg y)]
  rw [e1, e2, ← Measure.map_apply f.continuous.measurable (measurableSet_cone k),
    ← Measure.map_apply f.continuous.measurable measurableSet_ball2]
  exact haar_ratio (μ.map f) ((Measure.addHaar : Measure K).prod (Measure.addHaar : Measure Kᗮ))
    (core _ _ hK hKo hk0 hk1)

/-- **Archimedes' hat-box theorem in four dimensions** (Sec. II, "Counting in the bulk").  On the
unit sphere of a four-dimensional real inner product space, the points `ξ` with
`k < ⟪a, ξ⟫² + ⟪b, ξ⟫²`, for orthonormal `a`, `b` and `0 ≤ k < 1`, take the fraction `1 − k` of
the sphere, in the measure `μ.toSphere` that a Haar measure `μ` gives the sphere.  These are the
points within a given distance of the great circle through `a` and `b`; the fraction is linear in
`k`, as the area of a zone of a two-sphere is linear in its height. -/
theorem hatBox (hE : finrank ℝ E = 4) {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫ = 0) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    μ.toSphere {ξ : sphere (0 : E) 1 | k < ⟪a, (ξ : E)⟫ ^ 2 + ⟪b, (ξ : E)⟫ ^ 2} =
      ENNReal.ofReal (1 - k) * μ.toSphere Set.univ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hmeas : MeasurableSet {ξ : sphere (0 : E) 1 | k < ⟪a, (ξ : E)⟫ ^ 2 + ⟪b, (ξ : E)⟫ ^ 2} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  rw [Measure.toSphere_apply' μ hmeas, Measure.toSphere_apply_univ', cone_eq,
    cone_measure μ hE ha hb hab hk0 hk1, measure_sdiff_null (measure_singleton 0)]
  ring

end Space

end HatBox
