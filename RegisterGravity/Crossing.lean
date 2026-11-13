import RegisterGravity.HatBox
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The strings of a sphere, counted ring by ring (Sec. II, "Counting in the bulk")

Sec. II takes a sphere about a body to hold the strings that cross its surface, one for each
largest ring that crosses it (`Drawing.strings`).  Without a mass, the largest rings are great
circles of the three-sphere of radius `R_Λ`, the solution's space at an instant (Sec. IV.D).  This
file counts the rings that cross a sphere.

**When a ring crosses a sphere** (`crosses_iff`).  The files state the geometry for a real inner
product space `E`: the three-sphere is the sphere of radius `ρ` about the origin, a great circle
is the circle through two of its points `a` and `b` a quarter of the circle apart (`greatCircle`),
and the sphere about a point `p` of the three-sphere is the set of its points at distance `s`
from `p` in `E`, the chord; on the three-sphere its geodesic radius `χ` has
`s = 2ρ sin(χ/2ρ)`.  For a sphere no larger than a great sphere, `s² ≤ 2ρ²`, a great circle
crosses it, having points inside it, exactly when `⟪a, p⟫² + ⟪b, p⟫² > (ρ² − s²/2)²`, that is,
when `p` lies within a fixed distance of the circle.  A ring with a point inside a sphere no
larger than a great sphere also has a point outside, the antipode of that point, so it crosses the
sphere's surface; the files count a ring as crossing when it has a point inside (`Drawing.Crosses`), and
no declaration states this remark.

**The sphere is round** (`sphere_round`).  The points at distance `s` from `p` form a round sphere
of radius `r`, with `r² = s² − s⁴/4ρ²`, in the hyperplane through `(1 − s²/2ρ²) p` orthogonal to
`p`, which is three-dimensional when `E` is four-dimensional.  Its area is then `4πr²`, the area of
a round sphere, which the files do not compute, so `r` is its areal radius, the `r` of Eq. (N); in
terms of `χ`, `r = ρ sin(χ/ρ)`.

**The fraction of positions** (`crossing_fraction`).  Let the sphere's center be a point `ρξ` of
the three-sphere, with `ξ` on the unit sphere and no position preferred: `ξ` is weighted by the
measure `μ.toSphere` that a Haar measure `μ` of `E` gives the unit sphere.  A given ring crosses
the sphere for the fraction `(r/ρ)²` of the positions.  This is Archimedes' hat-box theorem in four
dimensions (`HatBox.hatBox`).

**The count** (`Drawing`, `Drawing.strings`, `Drawing.meanStrings_eq`).  With the largest rings
drawn as great circles of the three-sphere, a sphere holds the strings on the rings that cross
it.  Averaged over the sphere's position, it holds the number of rings times `(r/ρ)²`, whatever
the arrangement of the rings.  The count about a given position depends on the arrangement, which
the postulates do not fix; the average does not.  Turned about the center
by a linear isometry `g`, the drawing has about a point `p` the strings it had about `g⁻¹ p`
(`Drawing.strings_rotate`), and the sphere's measure is kept (`toSphere_preserving`); `Center.lean`
averages the count over the rotations `x ↦ qx` of the quaternions by unit quaternions, and carries
the average to any four-dimensional `E`; `Weighting.lean` shows that every weighting of the
rotations that prefers none gives the same average.
`Bridge.sphere_strings` puts in the register's count of rings and gives Eq. (N).  The rings are
drawn from the solution in `Geodesics.lean`: a largest ring is a closed geodesic of space
(Postulate 2), and the closed geodesics of the space at an instant of de Sitter space are its great
circles
(`Crossing.Drawing.ofRings`).  `Bridge.sphere_strings_model` shows that the hypotheses of the
count can be met together, so no theorem here holds vacuously.
-/

open MeasureTheory Metric Module Finset RealInnerProductSpace
open scoped ENNReal

namespace Crossing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A great circle** of the sphere of radius `ρ` about the origin, given by two of its points `a`
and `b` a quarter of the circle apart (`⟪a, b⟫ = 0`, `‖a‖ = ‖b‖ = ρ`): the points `u a + v b`
with `u² + v² = 1`. -/
def greatCircle (a b : E) : Set E := {x | ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ x = u • a + v • b}

lemma inner_comb (a b p : E) (u v : ℝ) :
    ⟪u • a + v • b, p⟫ = ⟪a, p⟫ * u + ⟪b, p⟫ * v := by
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  ring

lemma norm_comb_sq {a b : E} {ρ : ℝ} (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ)
    (u v : ℝ) : ‖u • a + v • b‖ ^ 2 = (u ^ 2 + v ^ 2) * ρ ^ 2 := by
  have h1 : ‖u • a‖ ^ 2 = u ^ 2 * ρ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha]
  have h2 : ‖v • b‖ ^ 2 = v ^ 2 * ρ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hb]
  have h3 : ⟪u • a, v • b⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hab]
    ring
  rw [norm_add_sq_real, h1, h2, h3]
  ring

variable {ρ s : ℝ} {a b p : E}

/-- On the sphere of radius `ρ` about the origin, the squared distance from a point `p` of it is
`2ρ² − 2⟪x, p⟫`: a point is nearer `p` when its inner product with `p` is larger. -/
lemma dist_sq_comb (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (hp : ‖p‖ = ρ) {u v : ℝ}
    (huv : u ^ 2 + v ^ 2 = 1) :
    ‖u • a + v • b - p‖ ^ 2 = 2 * ρ ^ 2 - 2 * (⟪a, p⟫ * u + ⟪b, p⟫ * v) := by
  rw [norm_sub_sq_real, norm_comb_sq hab ha hb, huv, inner_comb, hp]
  ring

/-- **When a great circle crosses a sphere** (Sec. II).  Let the sphere of the points at distance
`s` from a point `p` of the three-sphere be no larger than a great sphere, `s² ≤ 2ρ²`.  The great
circle through `a` and `b` has a point inside it exactly when
`(ρ² − s²/2)² < ⟪a, p⟫² + ⟪b, p⟫²`.  A point `u a + v b` of the circle lies inside when
`⟪a, p⟫ u + ⟪b, p⟫ v > ρ² − s²/2`, and the largest value of the left side on the circle is
`√(⟪a, p⟫² + ⟪b, p⟫²)`. -/
theorem crosses_iff (hab : ⟪a, b⟫ = 0) (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (hp : ‖p‖ = ρ)
    (hs0 : 0 ≤ s) (hs : s ^ 2 ≤ 2 * ρ ^ 2) :
    (∃ x ∈ greatCircle a b, ‖x - p‖ < s) ↔ (ρ ^ 2 - s ^ 2 / 2) ^ 2 < ⟪a, p⟫ ^ 2 + ⟪b, p⟫ ^ 2 := by
  obtain ⟨α, hα⟩ : ∃ α, ⟪a, p⟫ = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, ⟪b, p⟫ = β := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, ρ ^ 2 - s ^ 2 / 2 = c := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [← hc]; linarith
  have hd : ∀ {u v : ℝ}, u ^ 2 + v ^ 2 = 1 →
      ‖u • a + v • b - p‖ ^ 2 = s ^ 2 + 2 * (c - (α * u + β * v)) := by
    intro u v huv
    rw [dist_sq_comb hab ha hb hp huv, hα, hβ, ← hc]
    ring
  rw [hα, hβ, hc]
  constructor
  · rintro ⟨x, ⟨u, v, huv, rfl⟩, hin⟩
    have hlt : ‖u • a + v • b - p‖ ^ 2 < s ^ 2 :=
      (pow_lt_pow_iff_left₀ (norm_nonneg _) hs0 two_ne_zero).2 hin
    rw [hd huv] at hlt
    have hcs : c < α * u + β * v := by linarith
    have hcs2 : c ^ 2 < (α * u + β * v) ^ 2 := by nlinarith
    have hcs3 : (α * u + β * v) ^ 2 + (α * v - β * u) ^ 2 = α ^ 2 + β ^ 2 := by
      linear_combination (α ^ 2 + β ^ 2) * huv
    nlinarith [sq_nonneg (α * v - β * u)]
  · intro h
    have hA : 0 < α ^ 2 + β ^ 2 := lt_of_le_of_lt (sq_nonneg c) h
    obtain ⟨A, hA2, hApos⟩ : ∃ A : ℝ, A ^ 2 = α ^ 2 + β ^ 2 ∧ 0 < A :=
      ⟨Real.sqrt (α ^ 2 + β ^ 2), Real.sq_sqrt hA.le, Real.sqrt_pos.2 hA⟩
    have hcA : c < A := by nlinarith
    have hon : (α / A) ^ 2 + (β / A) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, ← hA2, div_self (pow_ne_zero 2 hApos.ne')]
    refine ⟨(α / A) • a + (β / A) • b, ⟨_, _, hon, rfl⟩, ?_⟩
    have hval : α * (α / A) + β * (β / A) = A := by
      field_simp
      linarith [hA2]
    have hlt : ‖(α / A) • a + (β / A) • b - p‖ ^ 2 < s ^ 2 := by
      rw [hd hon, hval]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hs0 hlt

/-- **The sphere about a point is round, of areal radius `r`** (Sec. II).  On the sphere of radius
`ρ ≠ 0` about the origin, the points at distance `s` from its point `p` are the points `κp + y`
with `y` orthogonal to `p` and `‖y‖ = r`, where `κ = 1 − s²/2ρ²` and `r² = s² − s⁴/4ρ²`: a round
sphere of radius `r` in the hyperplane through `κp` orthogonal to `p`, which is three-dimensional
when `E` is four-dimensional.  Its area is then `4πr²`, the area of a round sphere, which the files
do not compute. -/
theorem sphere_round (hρ : ρ ≠ 0) (hp : ‖p‖ = ρ) (hs0 : 0 ≤ s) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2)) :
    {x : E | ‖x‖ = ρ ∧ ‖x - p‖ = s} =
      {x | ∃ y : E, ⟪y, p⟫ = 0 ∧ ‖y‖ = r ∧ x = (1 - s ^ 2 / (2 * ρ ^ 2)) • p + y} := by
  have hρ0 : 0 ≤ ρ := hp ▸ norm_nonneg p
  have hpp : ⟪p, p⟫ = ρ ^ 2 := by rw [real_inner_self_eq_norm_sq, hp]
  obtain ⟨κ, hκ⟩ : ∃ κ, 1 - s ^ 2 / (2 * ρ ^ 2) = κ := ⟨_, rfl⟩
  have hκρ : κ * ρ ^ 2 = ρ ^ 2 - s ^ 2 / 2 := by
    rw [← hκ]
    field_simp
  have hr2 : r ^ 2 = ρ ^ 2 * (1 - κ ^ 2) := by
    rw [hr, ← hκ]
    field_simp
    ring
  rw [hκ]
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxs⟩
    have hxp : ⟪x, p⟫ = ρ ^ 2 - s ^ 2 / 2 := by
      have e := norm_sub_sq_real x p
      rw [hxs, hx, hp] at e
      linarith
    refine ⟨x - κ • p, ?_, ?_, by abel⟩
    · rw [inner_sub_left, real_inner_smul_left, hpp, hxp, ← hκρ]
      ring
    · have e : ‖x - κ • p‖ ^ 2 = r ^ 2 := by
        rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
          hx, hp, hxp, hr2, ← hκρ]
        ring
      exact (pow_left_inj₀ (norm_nonneg _) hr0 two_ne_zero).1 e
  · rintro ⟨y, hyp, hy, rfl⟩
    have hpy : ⟪κ • p, y⟫ = 0 := by
      rw [real_inner_smul_left, real_inner_comm, hyp, mul_zero]
    have hn : ‖κ • p‖ ^ 2 = κ ^ 2 * ρ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hp]
    constructor
    · have e : ‖κ • p + y‖ ^ 2 = ρ ^ 2 := by
        rw [norm_add_sq_real, hpy, hn, hy, hr2]
        ring
      exact (pow_left_inj₀ (norm_nonneg _) hρ0 two_ne_zero).1 e
    · have e : ‖κ • p + y - p‖ ^ 2 = s ^ 2 := by
        have e1 : κ • p + y - p = (κ - 1) • p + y := by
          rw [sub_smul, one_smul]
          abel
        have hpy' : ⟪(κ - 1) • p, y⟫ = 0 := by
          rw [real_inner_smul_left, real_inner_comm, hyp, mul_zero]
        rw [e1, norm_add_sq_real, hpy', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hp, hy, hr2]
        have : (κ - 1) * ρ ^ 2 = - (s ^ 2 / 2) := by linarith
        nlinarith
      exact (pow_left_inj₀ (norm_nonneg _) hs0 two_ne_zero).1 e

/-- **The largest rings drawn as great circles** of the sphere of radius `R` about the origin of
`E`: ring `i` is the great circle through `a i` and `b i` (`greatCircle`).  Without a mass, space
is a three-sphere (Sec. IV.D), and a largest ring is a closed geodesic of space (Postulate 2),
which on the three-sphere is a great circle. -/
structure Drawing (ι : Type*) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) where
  /-- a point of ring `i` -/
  a : ι → E
  /-- the point of ring `i` a quarter of the ring on from `a i` -/
  b : ι → E
  orth : ∀ i, ⟪a i, b i⟫ = 0
  norm_a : ∀ i, ‖a i‖ = R
  norm_b : ∀ i, ‖b i‖ = R

namespace Drawing

variable {ι : Type*}

/-- ring `i` crosses the sphere of the points at distance `s` from `p`: it has a point inside -/
def Crosses (D : Drawing ι E ρ) (p : E) (s : ℝ) (i : ι) : Prop :=
  ∃ x ∈ greatCircle (D.a i) (D.b i), ‖x - p‖ < s

/-- **Some of the rings, drawn as in `D`**: the rings `i` with `c i`, each the great circle it is in
`D` -/
def restrict (D : Drawing ι E ρ) (c : ι → Prop) : Drawing (Subtype c) E ρ where
  a i := D.a i
  b i := D.b i
  orth i := D.orth i
  norm_a i := D.norm_a i
  norm_b i := D.norm_b i

/-- **Where a ring crosses the sphere about a point**: the sphere about the point `ρξ`, with
`‖ξ‖ = 1`, no larger than a great sphere, is crossed by ring `i` exactly when
`(1 − s²/2ρ²)² < ⟪a i/ρ, ξ⟫² + ⟪b i/ρ, ξ⟫²` (`crosses_iff`). -/
lemma crosses_center (D : Drawing ι E ρ) (hρ : 0 < ρ) (hs0 : 0 ≤ s) (hs : s ^ 2 ≤ 2 * ρ ^ 2)
    {ξ : E} (hξ : ‖ξ‖ = 1) (i : ι) :
    D.Crosses (ρ • ξ) s i ↔
      (1 - s ^ 2 / (2 * ρ ^ 2)) ^ 2 < ⟪ρ⁻¹ • D.a i, ξ⟫ ^ 2 + ⟪ρ⁻¹ • D.b i, ξ⟫ ^ 2 := by
  have hp : ‖ρ • ξ‖ = ρ := by rw [norm_smul, hξ, mul_one, Real.norm_eq_abs, abs_of_pos hρ]
  unfold Crosses
  rw [crosses_iff (D.orth i) (D.norm_a i) (D.norm_b i) hp hs0 hs, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_left]
  have hρ4 : 0 < ρ ^ 4 := by positivity
  have e1 : (ρ ^ 2 - s ^ 2 / 2) ^ 2 = ρ ^ 4 * (1 - s ^ 2 / (2 * ρ ^ 2)) ^ 2 := by
    field_simp
  have e2 : (ρ * ⟪D.a i, ξ⟫) ^ 2 + (ρ * ⟪D.b i, ξ⟫) ^ 2 =
      ρ ^ 4 * ((ρ⁻¹ * ⟪D.a i, ξ⟫) ^ 2 + (ρ⁻¹ * ⟪D.b i, ξ⟫) ^ 2) := by
    field_simp
  rw [e1, e2, mul_lt_mul_iff_right₀ hρ4]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- the positions `ξ` of the unit sphere for which ring `i` crosses the sphere about `ρξ` -/
def crossers (D : Drawing ι E ρ) (s : ℝ) (i : ι) : Set (sphere (0 : E) 1) :=
  {ξ | D.Crosses (ρ • (ξ : E)) s i}

/-- **A ring crosses a sphere of areal radius `r` from the fraction `(r/ρ)²` of the positions**
(Sec. II).  Let the sphere's center be the point `ρξ` of the three-sphere, with no position
preferred: `ξ` is weighted by `μ.toSphere`.  For a sphere no larger than a great sphere,
`0 < s` and `s² ≤ 2ρ²`, of areal radius `r` (`sphere_round`; only `r²` enters here), the positions from which ring `i`
crosses it take the fraction `(r/ρ)²` of the sphere of positions.  This is Archimedes' hat-box
theorem in four dimensions (`HatBox.hatBox`), with `k = (1 − s²/2ρ²)²` and `1 − k = (r/ρ)²`. -/
theorem crossing_fraction (hE : finrank ℝ E = 4) (D : Drawing ι E ρ) (hρ : 0 < ρ) (hs0 : 0 < s)
    (hs : s ^ 2 ≤ 2 * ρ ^ 2) {r : ℝ} (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2)) (i : ι) :
    μ.toSphere (D.crossers s i) = ENNReal.ofReal ((r / ρ) ^ 2) * μ.toSphere Set.univ := by
  have hset : D.crossers s i = {ξ : sphere (0 : E) 1 | (1 - s ^ 2 / (2 * ρ ^ 2)) ^ 2 <
      ⟪ρ⁻¹ • D.a i, (ξ : E)⟫ ^ 2 + ⟪ρ⁻¹ • D.b i, (ξ : E)⟫ ^ 2} := by
    ext ξ
    exact D.crosses_center hρ hs0.le hs (mem_sphere_zero_iff_norm.1 ξ.2) i
  have hn : ∀ {v : E}, ‖v‖ = ρ → ‖ρ⁻¹ • v‖ = 1 := fun hv => by
    rw [norm_smul, hv, norm_inv, Real.norm_eq_abs, abs_of_pos hρ, inv_mul_cancel₀ hρ.ne']
  have horth : ⟪ρ⁻¹ • D.a i, ρ⁻¹ • D.b i⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, D.orth i, mul_zero, mul_zero]
  have hκ0 : 0 ≤ 1 - s ^ 2 / (2 * ρ ^ 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hs
  have hκ1 : 1 - s ^ 2 / (2 * ρ ^ 2) < 1 := by
    have : 0 < s ^ 2 / (2 * ρ ^ 2) := by positivity
    linarith
  have hk1 : (1 - s ^ 2 / (2 * ρ ^ 2)) ^ 2 < 1 := by nlinarith
  rw [hset, HatBox.hatBox μ hE (hn (D.norm_a i)) (hn (D.norm_b i)) horth (sq_nonneg _) hk1]
  congr 2
  rw [div_pow, hr]
  field_simp
  ring

variable [Fintype ι]

open Classical in
/-- **The strings a sphere holds**: one on each ring that crosses it, as Sec. II counts them. -/
noncomputable def strings (D : Drawing ι E ρ) (p : E) (s : ℝ) : ℕ :=
  (univ.filter (D.Crosses p s)).card

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- a sphere holds at most one string on each ring -/
lemma strings_le_card (D : Drawing ι E ρ) (p : E) (s : ℝ) : D.strings p s ≤ Fintype.card ι := by
  classical
  unfold strings
  exact (card_filter_le _ _).trans_eq card_univ

/-- **The strings of a sphere, averaged over its position**: the integral of `strings` over the
positions `ρξ` of the sphere's center, divided by the measure of the sphere of positions. -/
noncomputable def meanStrings (D : Drawing ι E ρ) (s : ℝ) : ℝ :=
  (∫ ξ, (D.strings (ρ • (ξ : E)) s : ℝ) ∂μ.toSphere) / μ.toSphere.real Set.univ

/-- **A sphere of areal radius `r` holds, on average, the number of rings times `(r/ρ)²`**
(Sec. II, "Counting in the bulk").  Each ring crosses it from the fraction `(r/ρ)²` of the
positions (`crossing_fraction`), and the strings of a sphere are a sum over the rings, so their
average over the sphere's position is the number of rings times `(r/ρ)²`, for every arrangement
of the rings as great circles.  The count about a given position depends on the arrangement; the
average does not.  `Bridge.sphere_strings` puts in the register's count of rings. -/
theorem meanStrings_eq (hE : finrank ℝ E = 4) (D : Drawing ι E ρ) (hρ : 0 < ρ) (hs0 : 0 < s)
    (hs : s ^ 2 ≤ 2 * ρ ^ 2) {r : ℝ} (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2)) :
    D.meanStrings μ s = Fintype.card ι * (r / ρ) ^ 2 := by
  classical
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hmeas : ∀ i, MeasurableSet (D.crossers s i) := fun i => by
    have hset : D.crossers s i = {ξ : sphere (0 : E) 1 | (1 - s ^ 2 / (2 * ρ ^ 2)) ^ 2 <
        ⟪ρ⁻¹ • D.a i, (ξ : E)⟫ ^ 2 + ⟪ρ⁻¹ • D.b i, (ξ : E)⟫ ^ 2} := by
      ext ξ
      exact D.crosses_center hρ hs0.le hs (mem_sphere_zero_iff_norm.1 ξ.2) i
    rw [hset]
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  -- the strings at a position are a sum over the rings
  have hsum : ∀ ξ : sphere (0 : E) 1, (D.strings (ρ • (ξ : E)) s : ℝ) =
      ∑ i, (D.crossers s i).indicator 1 ξ := fun ξ => by
    unfold strings
    rw [card_filter, Nat.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, crossers, Set.mem_ofPred_eq, Pi.one_apply]
    split_ifs <;> simp
  -- each ring contributes `(r/ρ)²` of the sphere of positions
  have hreal : ∀ i, μ.toSphere.real (D.crossers s i) = (r / ρ) ^ 2 * μ.toSphere.real Set.univ :=
    fun i => by
      rw [measureReal_def, crossing_fraction μ hE D hρ hs0 hs hr i, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (sq_nonneg _), measureReal_def]
  have hpos : 0 < μ.toSphere.real Set.univ := by
    have hne : (Set.univ : Set (sphere (0 : E) 1)).Nonempty := by
      have h1 : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
      obtain ⟨x, hx⟩ := h1
      exact ⟨⟨x, hx⟩, Set.mem_univ _⟩
    exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ hne).ne' (measure_ne_top _ _)
  unfold meanStrings
  simp_rw [hsum]
  rw [integral_finsetSum _ fun i _ => ?_]
  swap
  · exact (integrable_const (1 : ℝ)).indicator (hmeas i)
  simp_rw [integral_indicator_one (hmeas _), hreal]
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

end Drawing

/-! ### The drawing turned about the center

A rotation about the center of the three-sphere is a linear isometry of `E`.  It carries a great
circle to a great circle (`greatCircle_map`), the drawing to a drawing of the same rings
(`Drawing.rotate`), and the sphere's measure to itself (`toSphere_preserving`).  Turning the drawing
by `g` is moving the point by `g⁻¹` (`Drawing.strings_rotate`). -/

section Rotate

open scoped Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- a linear isometry `g` carries the great circle through `a` and `b` onto the great circle
through `g a` and `g b` -/
lemma greatCircle_map (g : E ≃ₗᵢ[ℝ] F) (a b : E) :
    greatCircle (g a) (g b) = g '' greatCircle a b := by
  ext x
  constructor
  · rintro ⟨u, v, huv, rfl⟩
    exact ⟨u • a + v • b, ⟨u, v, huv, rfl⟩, by simp⟩
  · rintro ⟨y, ⟨u, v, huv, rfl⟩, rfl⟩
    exact ⟨u, v, huv, by simp⟩

/-- the map of the unit sphere that a linear isometry `g` gives, a homeomorphism -/
def sphereEquiv (g : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  g.toHomeomorph.subtype fun x => by simp

@[simp] lemma sphereEquiv_coe (g : E ≃ₗᵢ[ℝ] E) (ξ : sphere (0 : E) 1) :
    ((sphereEquiv g ξ : sphere (0 : E) 1) : E) = g ξ := rfl

namespace Drawing

variable {ι : Type*}

/-- **The drawing carried by a linear isometry `g : E ≃ F`**: ring `i` is the great circle through
`g (a i)` and `g (b i)`.  With `F = E` and `g` a rotation about the center, it is the drawing turned
about the center; the rings are the same, and only their places change. -/
def rotate (D : Drawing ι E ρ) (g : E ≃ₗᵢ[ℝ] F) : Drawing ι F ρ where
  a i := g (D.a i)
  b i := g (D.b i)
  orth i := by rw [LinearIsometryEquiv.inner_map_map, D.orth i]
  norm_a i := by rw [LinearIsometryEquiv.norm_map, D.norm_a i]
  norm_b i := by rw [LinearIsometryEquiv.norm_map, D.norm_b i]

/-- a ring of the drawing carried by `g` crosses the sphere about `p` exactly when the ring of the
drawing crosses the sphere about `g⁻¹ p` -/
lemma crosses_rotate (D : Drawing ι E ρ) (g : E ≃ₗᵢ[ℝ] F) (p : F) (s : ℝ) (i : ι) :
    (D.rotate g).Crosses p s i ↔ D.Crosses (g.symm p) s i := by
  have hd : ∀ y, ‖g y - p‖ = ‖y - g.symm p‖ := fun y => by
    rw [← g.norm_map (y - g.symm p), map_sub, LinearIsometryEquiv.apply_symm_apply]
  change (∃ x ∈ greatCircle (g (D.a i)) (g (D.b i)), ‖x - p‖ < s) ↔
    ∃ x ∈ greatCircle (D.a i) (D.b i), ‖x - g.symm p‖ < s
  rw [greatCircle_map]
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, hx⟩
    exact ⟨y, hy, (hd y) ▸ hx⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, (hd y).symm ▸ hx⟩

variable [Fintype ι]

/-- **Turning the drawing by `g` is moving the point by `g⁻¹`**: the strings about `p` of the
drawing carried by `g` are those about `g⁻¹ p` of the drawing -/
lemma strings_rotate (D : Drawing ι E ρ) (g : E ≃ₗᵢ[ℝ] F) (p : F) (s : ℝ) :
    (D.rotate g).strings p s = D.strings (g.symm p) s := by
  classical
  unfold strings
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact D.crosses_rotate g p s i

end Drawing

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **A Haar measure is kept by every linear isometry** `g`: a linear map scales a Haar measure by
`|det g|⁻¹` (`Measure.map_linearMap_addHaar_eq_smul_addHaar`), and `g` carries the unit ball to
itself, so the factor is one -/
lemma map_isometry (g : E ≃ₗᵢ[ℝ] E) : Measure.map g μ = μ := by
  have hdet : LinearMap.det (g.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 :=
    g.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map g μ = Measure.map (g.toLinearEquiv : E →ₗ[ℝ] E) μ := rfl
  rw [hmap, Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet]
  have hball : Measure.map (g.toLinearEquiv : E →ₗ[ℝ] E) μ (ball 0 1) = μ (ball 0 1) := by
    rw [Measure.map_apply (g.toLinearEquiv : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable
      measurableSet_ball]
    congr 1
    ext x
    simp
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, Measure.smul_apply, smul_eq_mul]
    at hball
  have h0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have htop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [(ENNReal.mul_eq_right h0 htop).mp hball, one_smul]

/-- **The sphere's measure is kept by every linear isometry** `g` of `E`, such as a rotation about
the center: `μ.toSphere` gives a set of the unit sphere `dim E` times the measure that `μ` gives the
cone over it (`Measure.toSphere_apply'`), `g` carries the cone over a set to the cone over its
image, and `μ` is kept by `g` (`map_isometry`) -/
lemma toSphere_preserving (g : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereEquiv g) μ.toSphere μ.toSphere := by
  refine ⟨(sphereEquiv g).continuous.measurable, ?_⟩
  ext s hs
  have hpre : MeasurableSet (sphereEquiv g ⁻¹' s) := (sphereEquiv g).continuous.measurable hs
  rw [Measure.map_apply (sphereEquiv g).continuous.measurable hs, Measure.toSphere_apply' μ hpre,
    Measure.toSphere_apply' μ hs]
  congr 1
  have hset : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereEquiv g ⁻¹' s)) =
      g ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨ξ, hξ, rfl⟩, rfl⟩
      exact ⟨t, ht, g ξ, ⟨sphereEquiv g ξ, hξ, rfl⟩, by simp⟩
    · rintro ⟨t, ht, _, ⟨η, hη, rfl⟩, hx⟩
      refine ⟨t, ht, g.symm η, ⟨(sphereEquiv g).symm η, ?_, rfl⟩, ?_⟩
      · simpa using hη
      · rw [← LinearIsometryEquiv.map_smul, hx, LinearIsometryEquiv.symm_apply_apply]
  rw [hset]
  have : μ (g ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s))) =
      Measure.map g.toHomeomorph.toMeasurableEquiv μ (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    rw [MeasurableEquiv.map_apply]
    rfl
  rw [this, show (Measure.map g.toHomeomorph.toMeasurableEquiv μ) = Measure.map g μ from rfl,
    map_isometry μ g]

end Rotate

end Crossing
