import RegisterGravity.Crossing

/-!
# The two receiving cells of a string (Sec. IV.C)

Formal counterpart of one sentence of Sec. IV.C: "Each lies on a largest ring, which enters the
sphere at one cell and leaves it at another, the string's two receiving cells, and runs on to the
horizon".

Without a mass the largest rings are great circles of the three-sphere of radius `R_Λ`
(`Crossing.lean`, `Geodesics.lean`), and a sphere about a point `p` of it is the set of its points
at the distance `s` from `p`.  A great circle crosses the sphere, having points inside it, exactly
when `(ρ² − s²/2)² < ⟪a, p⟫² + ⟪b, p⟫²` (`Crossing.crosses_iff`).  `Crossing.two_crossings` proves
that the circle then has exactly two points on the sphere's surface: the ring enters the sphere at
one and leaves it at the other.  A point `u a + v b` of the circle lies on the surface exactly
when `⟪a, p⟫ u + ⟪b, p⟫ v = ρ² − s²/2`, a line in the plane of `(u, v)` that cuts the unit circle
in two points when it passes nearer the origin than one.

The statement is of the points of the manifold.  That the two points are cells is Sec. II's "a
cell is a place on a ring".
-/

open MeasureTheory Metric Module Finset RealInnerProductSpace
open scoped ENNReal

namespace Crossing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ρ s : ℝ} {a b p : E}

/-- **A ring that crosses a sphere meets its surface at two points** (Sec. IV.C: "Each lies on a
largest ring, which enters the sphere at one cell and leaves it at another, the string's two
receiving cells").  Where the great circle through `a` and `b` crosses the sphere of the points at
distance `s` from `p` (`crosses_iff`), exactly two of its points lie on the sphere's surface, at
the distance `s` from `p`. -/
theorem two_crossings (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (hp : ‖p‖ = ρ)
    (hρ : 0 < ρ) (hcross : (ρ ^ 2 - s ^ 2 / 2) ^ 2 < ⟪a, p⟫ ^ 2 + ⟪b, p⟫ ^ 2) :
    ∃ x₁ x₂ : E, x₁ ∈ greatCircle a b ∧ x₂ ∈ greatCircle a b ∧ x₁ ≠ x₂ ∧
      ∀ x ∈ greatCircle a b, ‖x - p‖ ^ 2 = s ^ 2 ↔ x = x₁ ∨ x = x₂ := by
  obtain ⟨α, hα⟩ : ∃ α, ⟪a, p⟫ = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, ⟪b, p⟫ = β := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, ρ ^ 2 - s ^ 2 / 2 = c := ⟨_, rfl⟩
  rw [hα, hβ, hc] at hcross
  obtain ⟨n, hn⟩ : ∃ n, n = α ^ 2 + β ^ 2 := ⟨_, rfl⟩
  have hn0 : 0 < n := by rw [hn]; exact lt_of_le_of_lt (sq_nonneg c) hcross
  have hn' : n ≠ 0 := hn0.ne'
  obtain ⟨d, hd2, hdpos⟩ : ∃ d : ℝ, d ^ 2 = n - c ^ 2 ∧ 0 < d :=
    ⟨Real.sqrt (n - c ^ 2), Real.sq_sqrt (by rw [hn]; linarith),
      Real.sqrt_pos.2 (by rw [hn]; linarith)⟩
  have hcd : c ^ 2 + d ^ 2 = n := by linarith
  -- a point of the circle lies on the sphere's surface exactly when `α u + β v = c`
  have hon : ∀ {u v : ℝ}, u ^ 2 + v ^ 2 = 1 →
      (‖u • a + v • b - p‖ ^ 2 = s ^ 2 ↔ α * u + β * v = c) := by
    intro u v huv
    rw [dist_sq_comb hab ha hb hp huv, hα, hβ, ← hc]
    constructor <;> intro h <;> linarith
  -- the two points
  have h1 : ((c * α + d * β) / n) ^ 2 + ((c * β - d * α) / n) ^ 2 = 1 := by
    have e : (c * α + d * β) ^ 2 + (c * β - d * α) ^ 2 = (c ^ 2 + d ^ 2) * (α ^ 2 + β ^ 2) := by
      ring
    rw [div_pow, div_pow, ← add_div, e, hcd, ← hn]
    field_simp
  have h2 : ((c * α - d * β) / n) ^ 2 + ((c * β + d * α) / n) ^ 2 = 1 := by
    have e : (c * α - d * β) ^ 2 + (c * β + d * α) ^ 2 = (c ^ 2 + d ^ 2) * (α ^ 2 + β ^ 2) := by
      ring
    rw [div_pow, div_pow, ← add_div, e, hcd, ← hn]
    field_simp
  have hv1 : α * ((c * α + d * β) / n) + β * ((c * β - d * α) / n) = c := by
    field_simp
    rw [hn]
    ring
  have hv2 : α * ((c * α - d * β) / n) + β * ((c * β + d * α) / n) = c := by
    field_simp
    rw [hn]
    ring
  refine ⟨((c * α + d * β) / n) • a + ((c * β - d * α) / n) • b,
    ((c * α - d * β) / n) • a + ((c * β + d * α) / n) • b, ⟨_, _, h1, rfl⟩, ⟨_, _, h2, rfl⟩, ?_, ?_⟩
  · -- the two points differ
    intro h
    have h0 : ((c * α + d * β) / n - (c * α - d * β) / n) • a
        + ((c * β - d * α) / n - (c * β + d * α) / n) • b = 0 := by
      rw [sub_smul, sub_smul]
      rw [← sub_eq_zero] at h
      rw [← h]
      abel
    have hnorm := norm_comb_sq hab ha hb ((c * α + d * β) / n - (c * α - d * β) / n)
      ((c * β - d * α) / n - (c * β + d * α) / n)
    rw [h0, norm_zero] at hnorm
    have hsum : ((c * α + d * β) / n - (c * α - d * β) / n) ^ 2
        + ((c * β - d * α) / n - (c * β + d * α) / n) ^ 2 = 4 * d ^ 2 / n := by
      field_simp
      rw [hn]
      ring
    rw [hsum] at hnorm
    have hpos : 0 < 4 * d ^ 2 / n * ρ ^ 2 := by positivity
    rw [← hnorm] at hpos
    norm_num at hpos
  · rintro x ⟨u, v, huv, rfl⟩
    rw [hon huv]
    constructor
    · intro hval
      have hw : (β * u - α * v) ^ 2 = d ^ 2 := by
        have e : (β * u - α * v) ^ 2
            = (α ^ 2 + β ^ 2) * (u ^ 2 + v ^ 2) - (α * u + β * v) ^ 2 := by ring
        rw [e, huv, hval, mul_one, ← hn, hd2]
      have hu : u = (c * α + (β * u - α * v) * β) / n := by
        rw [eq_div_iff hn', hn, ← hval]
        ring
      have hv : v = (c * β - (β * u - α * v) * α) / n := by
        rw [eq_div_iff hn', hn, ← hval]
        ring
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hw with hwd | hwd
      · left
        rw [hwd] at hu hv
        rw [← hu, ← hv]
      · right
        rw [hwd] at hu hv
        have hu' : u = (c * α - d * β) / n := by rw [hu]; ring
        have hv' : v = (c * β + d * α) / n := by rw [hv]; ring
        rw [← hu', ← hv']
    · rintro (h | h)
      · -- the point is the first one
        have := (hon h1).2 hv1
        rw [← h] at this
        exact (hon huv).1 this
      · have := (hon h2).2 hv2
        rw [← h] at this
        exact (hon huv).1 this

end Crossing
