import RegisterGravity.Center
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# No rotation of the drawing preferred: the rotations weighted alike (Sec. II, "Counting in the
bulk")

The drawing of the largest rings as great circles of the three-sphere is no part of the state
(Sec. II), so no rotation of it is preferred: the paper weights the rotations alike.  `Center.lean`
averages over the rotations `x ↦ qx` of `ℍ`, the unit quaternions `q` weighted by the unit sphere's
measure.  This file derives that weighting from the sentence: a weighting of the rotations that
prefers none, a probability measure `m` on the unit quaternions that following every rotation by a
fixed one leaves unchanged (`m.IsMulLeftInvariant`), is the unit sphere's measure, normalized
(`eq_toSphere_of_invariant`): the unit quaternions are a compact group, a measure on it that left
multiplication keeps is a multiple of its Haar measure (Mathlib's
`Measure.isMulInvariant_eq_smul_of_compactSpace`, the uniqueness of Haar measure), and the unit
sphere's measure is one (`toSphere_isMulLeftInvariant`, `toSphere_isHaarMeasure`).  So an average
over such a weighting is the average over the unit sphere's measure (`integral_normalized`), the one
`Center.lean` computes; `Main.sphere_strings` and `Main.observer_count` take the
sentence as their premise (`Sources.P1.no_rotation_preferred`) and reduce to `Center.lean` through
this file.

The premise can be met: the unit sphere's measure, normalized (`evenWeight`), has total one and is
unchanged when every rotation is followed by a fixed one (`weighting_model`).
-/
open MeasureTheory Metric Crossing Module Center
open scoped ENNReal NNReal Quaternion

namespace Weighting

section Quaternion

/-- left multiplication by a unit quaternion on the unit sphere is the rotation `x ↦ qx` -/
lemma mul_eq_sphereEquiv (q : sphere (0 : ℍ) 1) :
    (fun ξ : sphere (0 : ℍ) 1 => q * ξ) = sphereEquiv (leftRot q) := by
  funext ξ
  exact Subtype.ext rfl

variable [MeasurableSpace ℍ] [BorelSpace ℍ] (μ : Measure ℍ) [μ.IsAddHaarMeasure]

/-- the unit sphere's measure is kept by every rotation `x ↦ qx` (`Crossing.toSphere_preserving`) -/
instance toSphere_isMulLeftInvariant : μ.toSphere.IsMulLeftInvariant where
  map_mul_left_eq_self q := by
    rw [mul_eq_sphereEquiv]
    exact (toSphere_preserving μ (leftRot q)).map_eq

/-- the unit sphere's measure is a Haar measure of the unit quaternions: finite, kept by left
multiplication, and positive on open sets -/
instance toSphere_isHaarMeasure : μ.toSphere.IsHaarMeasure := {}

/-- **A probability measure on the unit three-sphere that every rotation `x ↦ qx` keeps is the unit
sphere's measure, normalized** (Sec. II).  The unit quaternions form a compact group, and a measure
on it that left multiplication keeps is a multiple of the unit sphere's measure, a Haar measure of
the group (`Measure.isMulInvariant_eq_smul_of_compactSpace`); the total `1` fixes the multiple. -/
theorem eq_toSphere_of_invariant (m : Measure (sphere (0 : ℍ) 1)) [IsProbabilityMeasure m]
    [m.IsMulLeftInvariant] : m = (μ.toSphere Set.univ)⁻¹ • μ.toSphere := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace m μ.toSphere
  have h1 : (m.haarScalarFactor μ.toSphere : ℝ≥0∞) * μ.toSphere Set.univ = 1 := by
    have := congrArg (fun ν : Measure (sphere (0 : ℍ) 1) => ν Set.univ) h
    simp only [measure_univ, Measure.smul_apply] at this
    rw [this]
    rfl
  have h2 : (m.haarScalarFactor μ.toSphere : ℝ≥0∞) = (μ.toSphere Set.univ)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left h1
  conv_lhs => rw [h]
  ext t ht
  rw [Measure.smul_apply, Measure.smul_apply, ← h2]
  rfl

omit [BorelSpace ℍ] [μ.IsAddHaarMeasure] in
/-- the average of a function over the unit sphere's measure, normalized -/
lemma integral_normalized (f : sphere (0 : ℍ) 1 → ℝ) :
    ∫ ξ, f ξ ∂((μ.toSphere Set.univ)⁻¹ • μ.toSphere) =
      (∫ ξ, f ξ ∂μ.toSphere) / μ.toSphere.real Set.univ := by
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, measureReal_def, div_eq_inv_mul]

end Quaternion

section Even

variable [MeasurableSpace ℍ] [BorelSpace ℍ]

/-- **The even weighting of the unit quaternions**: the unit sphere's measure, normalized -/
noncomputable def evenWeight : Measure (sphere (0 : ℍ) 1) :=
  ((Measure.addHaar : Measure ℍ).toSphere Set.univ)⁻¹ • (Measure.addHaar : Measure ℍ).toSphere

/-- the even weighting has total weight one -/
instance evenWeight_isProbabilityMeasure :
    IsProbabilityMeasure (evenWeight : Measure (sphere (0 : ℍ) 1)) := ⟨by
  rw [evenWeight, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.2 (Measure.toSphere_ne_zero _))
    (measure_ne_top _ _)⟩

/-- the even weighting is unchanged when every rotation is followed by a fixed one: the rotation
`x ↦ qx` keeps the unit sphere's measure (`toSphere_isMulLeftInvariant`) -/
instance evenWeight_isMulLeftInvariant :
    (evenWeight : Measure (sphere (0 : ℍ) 1)).IsMulLeftInvariant := by
  unfold evenWeight
  infer_instance

/-- **The premise that no rotation is preferred can be met**: the unit sphere's measure,
normalized, is a weighting of the rotations of total one that following every rotation by a fixed
one does not change. -/
theorem weighting_model :
    IsProbabilityMeasure (evenWeight : Measure (sphere (0 : ℍ) 1)) ∧
    (evenWeight : Measure (sphere (0 : ℍ) 1)).IsMulLeftInvariant :=
  ⟨inferInstance, inferInstance⟩

end Even

end Weighting
