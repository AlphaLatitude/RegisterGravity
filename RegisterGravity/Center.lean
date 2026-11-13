import RegisterGravity.Bridge
import Mathlib.Analysis.Quaternion

/-!
# The drawing made from the center of the three-sphere (Sec. II, "Counting in the bulk")

The largest rings are drawn as great circles of the three-sphere of radius `ρ`, each the section of
the three-sphere by a plane through its center.  Made from that center, the drawing singles out no
point of space: a rotation about the center keeps the center, carries the
drawing to a drawing of the same rings (`Crossing.Drawing.rotate`), and the rotations carry any
point to any other.  The postulates fix how many rings there are, not which great circle each one
is, and every physical law and quantity is defined by qubits (Postulate 1), so the drawing is no
part of the state, and no law prefers one rotation of it to another.  The count about a body
depends only on the strings, not on the drawing: this is Postulate 1's first sentence (the thesis
of the paper).  With every rotation weighted alike, the count is defined as its average over the
rotations, a value that does not depend on the drawing (Sec. II).  The files prove the average;
taking it as the count is where the thesis enters, a definition and not a theorem.
This file weights the rotations `x ↦ qx` by the unit sphere's measure; `Weighting.lean` derives
that weighting from the sentence, since a weighting that prefers no rotation is the unit sphere's
measure, normalized.

The space that holds the three-sphere is first taken to be the quaternions `ℍ`, a four-dimensional
real inner product space, so that the rotations `x ↦ qx` by the unit quaternions `q` (`leftRot`)
are at hand.  Any
four-dimensional real inner product space `E`, such as that of `Geodesics.lean`, is isometric to
`ℍ` (`exists_isometry_quaternion`), and an isometry `φ : E ≃ ℍ` carries these rotations to the
rotations `x ↦ φ⁻¹(qφ(x))` of `E` about its center (`rotOf`).

`strings_rotation_mean`: for every drawing and every point `p` of the three-sphere, the strings of a
sphere no larger than a great sphere, of areal radius `r`, about `p`, averaged over the rotations
`x ↦ qx` with `q` weighted by the measure of the unit sphere, are the number of rings times
`(r/ρ)²`, exactly.  Turning the drawing by `q` is moving the point by `q⁻¹`
(`Crossing.Drawing.strings_rotate`), and `q ↦ q⁻¹p/ρ` keeps the unit sphere's measure (`starRight`,
`Crossing.toSphere_preserving`), so the average over the rotations is the average over positions of
`Crossing.Drawing.meanStrings_eq`.  For one drawing the count about a
point depends on the point; averaged over the rotations `x ↦ qx` it does not.
`sphere_strings_centered` puts in the register's count of rings: the average is the chain's
`N_s(r)` times `1 − 2/L + 4/L²` about every point, and `sphere_strings_centered_model` shows that
its hypotheses can be met together.  `strings_rotation_mean_of` and `sphere_strings_centered_of`
carry both to any four-dimensional `E`, averaging over the rotations `x ↦ φ⁻¹(qφ(x))`, and
`sphere_strings_of_rings_centered` applies them to the drawing of the rings as closed geodesics of
space (`Crossing.Drawing.ofRings`), with `sphere_strings_of_rings_centered_model`.
`observer_strings_mean` gives the count of an observer at a cell, his `L/2` rings taken where the
drawing places them and the others turned: the average, plus the number of his rings that cross
the sphere, less `(L/2)(r/ρ)²`.
-/

open MeasureTheory Metric Module RealInnerProductSpace
open scoped Quaternion

namespace Center

open Crossing Quaternion

variable {ρ s : ℝ}

/-- a unit quaternion's conjugate times the quaternion is one -/
lemma star_mul_unit (q : sphere (0 : ℍ) 1) : star (q : ℍ) * q = 1 := by
  have hq : ‖(q : ℍ)‖ = 1 := mem_sphere_zero_iff_norm.1 q.2
  rw [star_mul_self, normSq_eq_norm_mul_self, hq, mul_one]
  rfl

/-- a unit quaternion times its conjugate is one -/
lemma mul_star_unit (q : sphere (0 : ℍ) 1) : (q : ℍ) * star (q : ℍ) = 1 := by
  have hq : ‖(q : ℍ)‖ = 1 := mem_sphere_zero_iff_norm.1 q.2
  rw [self_mul_star, normSq_eq_norm_mul_self, hq, mul_one]
  rfl

/-- **A rotation about the center**: left multiplication by a unit quaternion `q`, `x ↦ qx`, a
linear isometry of `ℍ` with inverse `x ↦ q̄x` -/
noncomputable def leftRot (q : sphere (0 : ℍ) 1) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun x := (q : ℍ) * x
  invFun x := star (q : ℍ) * x
  map_add' x y := mul_add _ x y
  map_smul' c x := mul_smul_comm c (q : ℍ) x
  left_inv x := by simp only; rw [← mul_assoc, star_mul_unit, one_mul]
  right_inv x := by simp only; rw [← mul_assoc, mul_star_unit, one_mul]
  norm_map' x := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [norm_mul, mem_sphere_zero_iff_norm.1 q.2, one_mul]

@[simp] lemma leftRot_symm_apply (q : sphere (0 : ℍ) 1) (x : ℍ) :
    (leftRot q).symm x = star (q : ℍ) * x := rfl

/-- the map `x ↦ x̄ξ₀`, a linear isometry of `ℍ`, which carries a unit quaternion `q` to `q⁻¹ξ₀` -/
noncomputable def starRight (ξ₀ : sphere (0 : ℍ) 1) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun x := star x * (ξ₀ : ℍ)
  invFun y := star (y * star (ξ₀ : ℍ))
  map_add' x y := by simp only [star_add, add_mul]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [Quaternion.star_smul, smul_mul_assoc]
  left_inv x := by
    simp only
    rw [mul_assoc, mul_star_unit, mul_one, star_star]
  right_inv y := by
    simp only
    rw [star_star, mul_assoc, star_mul_unit, mul_one]
  norm_map' x := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [norm_mul, Quaternion.norm_star, mem_sphere_zero_iff_norm.1 ξ₀.2, mul_one]

/-! ### Any four-dimensional space

The space that holds the three-sphere is any four-dimensional real inner product space `E`, such as
that of `Geodesics.lean`.  A linear isometry `φ : E ≃ ℍ` exists (`exists_isometry_quaternion`), and
it carries the rotations `x ↦ qx` of `ℍ` to rotations of `E` about its center,
`x ↦ φ⁻¹(qφ(x))` (`rotOf`). -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A four-dimensional real inner product space is isometric to `ℍ`**: an orthonormal basis of
each, indexed alike, gives the isometry -/
lemma exists_isometry_quaternion [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4) :
    Nonempty (E ≃ₗᵢ[ℝ] ℍ) :=
  ⟨((stdOrthonormalBasis ℝ E).reindex
      (finCongr (hE.trans Quaternion.finrank_eq_four.symm))).repr.trans
    (stdOrthonormalBasis ℝ ℍ).repr.symm⟩

/-- **A rotation of `E` about the center**: the rotation `x ↦ qx` of `ℍ` carried to `E` by a linear
isometry `φ : E ≃ ℍ`, `x ↦ φ⁻¹(qφ(x))` -/
noncomputable def rotOf (φ : E ≃ₗᵢ[ℝ] ℍ) (q : sphere (0 : ℍ) 1) : E ≃ₗᵢ[ℝ] E :=
  (φ.trans (leftRot q)).trans φ.symm

lemma rotOf_symm_apply (φ : E ≃ₗᵢ[ℝ] ℍ) (q : sphere (0 : ℍ) 1) (x : E) :
    (rotOf φ q).symm x = φ.symm ((leftRot q).symm (φ x)) := rfl

end General

section Mean

variable [MeasurableSpace ℍ] [BorelSpace ℍ] (μ : Measure ℍ) [μ.IsAddHaarMeasure]

/-- **The strings about any point, averaged over the rotations `x ↦ qx` of the drawing about the
center, are the number of rings times `(r/ρ)²`** (Sec. II, "Counting in the bulk").  For every
drawing `D` of the rings as great circles of the three-sphere of radius `ρ` in `ℍ`, every point
`ρξ₀` of it, and every sphere no larger than a great sphere, of areal radius `r`, the strings of the
sphere about `ρξ₀` in the drawing turned by `x ↦ qx`, averaged over the unit quaternions `q` in the
measure `μ.toSphere`, are the number of rings times `(r/ρ)²`.  The point is any point and the
drawing any drawing.  The drawing turned by `q` has about `ρξ₀` the strings that `D` has about
`ρq̄ξ₀` (`Crossing.Drawing.strings_rotate`), and `q ↦ q̄ξ₀` keeps the unit sphere's measure
(`Crossing.toSphere_preserving`), so the average is `D.meanStrings` (`meanStrings_eq`). -/
theorem strings_rotation_mean {ι : Type*} [Fintype ι] (D : Drawing ι ℍ ρ) (hρ : 0 < ρ)
    (hs0 : 0 < s) (hs : s ^ 2 ≤ 2 * ρ ^ 2) {r : ℝ} (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2))
    (ξ₀ : sphere (0 : ℍ) 1) :
    (∫ q, ((D.rotate (leftRot q)).strings (ρ • (ξ₀ : ℍ)) s : ℝ) ∂μ.toSphere) /
      μ.toSphere.real Set.univ = Fintype.card ι * (r / ρ) ^ 2 := by
  have h1 : ∀ q : sphere (0 : ℍ) 1, ((D.rotate (leftRot q)).strings (ρ • (ξ₀ : ℍ)) s : ℝ) =
      (fun ξ : sphere (0 : ℍ) 1 => (D.strings (ρ • (ξ : ℍ)) s : ℝ))
        (sphereEquiv (starRight ξ₀) q) := fun q => by
    simp only [Drawing.strings_rotate, leftRot_symm_apply, sphereEquiv_coe]
    congr 2
    change star (q : ℍ) * (ρ • (ξ₀ : ℍ)) = ρ • (star (q : ℍ) * (ξ₀ : ℍ))
    rw [mul_smul_comm]
  have key := (toSphere_preserving μ (starRight ξ₀)).integral_comp
    (sphereEquiv (starRight ξ₀)).measurableEmbedding
    (fun ξ : sphere (0 : ℍ) 1 => (D.strings (ρ • (ξ : ℍ)) s : ℝ))
  simp_rw [h1]
  rw [key]
  exact Drawing.meanStrings_eq μ Quaternion.finrank_eq_four D hρ hs0 hs hr

/-- **The strings of a sphere that an observer counts** (Sec. II, after Eq. (N)).  Let `B` be the
observer's cell.  His rings, the `L/2` through `B` (`Horizon.two_mul_card_through`), are taken where
the drawing `D` places them; the other rings are turned about the center, `x ↦ qx`, with `q`
weighted by `μ.toSphere` as for the whole drawing.  His count, the strings on his rings in `D` plus
the average of the strings on the other rings over the turning, is the average of the whole drawing
over the turning (`strings_rotation_mean`), plus the number of his rings that cross the sphere,
less `(L/2)(r/ρ)²`: in the average each ring has the weight `(r/ρ)²`.  At most all `L/2` of his
rings cross (`Crossing.Drawing.strings_le_card`). -/
theorem observer_strings_mean {L : ℕ} (H : Horizon L) (hL : 4 ≤ L) (D : Drawing H.Loop ℍ ρ)
    (B : H.Cell) (hρ : 0 < ρ) (hs0 : 0 < s) (hs : s ^ 2 ≤ 2 * ρ ^ 2) {r : ℝ}
    (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2)) (ξ₀ : sphere (0 : ℍ) 1) :
    ((D.restrict (· ∈ H.through B)).strings (ρ • (ξ₀ : ℍ)) s : ℝ) +
        (∫ q, (((D.restrict (· ∉ H.through B)).rotate (leftRot q)).strings (ρ • (ξ₀ : ℍ)) s : ℝ)
          ∂μ.toSphere) / μ.toSphere.real Set.univ =
      (∫ q, ((D.rotate (leftRot q)).strings (ρ • (ξ₀ : ℍ)) s : ℝ) ∂μ.toSphere) /
          μ.toSphere.real Set.univ +
        (D.restrict (· ∈ H.through B)).strings (ρ • (ξ₀ : ℍ)) s - L / 2 * (r / ρ) ^ 2 ∧
    ((D.restrict (· ∈ H.through B)).strings (ρ • (ξ₀ : ℍ)) s : ℝ) ≤ L / 2 := by
  classical
  rw [strings_rotation_mean μ (D.restrict (· ∉ H.through B)) hρ hs0 hs hr ξ₀,
    strings_rotation_mean μ D hρ hs0 hs hr ξ₀]
  have hc1 : Fintype.card {l // l ∈ H.through B} = (H.through B).card := Fintype.card_coe _
  have hc0 : Fintype.card {l // l ∉ H.through B} = (H.through B)ᶜ.card := by
    rw [Fintype.card_subtype, Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.compl_eq_univ_sdiff]
  have hc2 : Fintype.card {l // l ∉ H.through B} + (H.through B).card = Fintype.card H.Loop := by
    rw [hc0, Finset.card_compl]
    have := Finset.card_le_univ (H.through B)
    omega
  have h2 := H.two_mul_card_through hL B
  have hle := (D.restrict (· ∈ H.through B)).strings_le_card (ρ • (ξ₀ : ℍ)) s
  rw [hc1] at hle
  have hc2' : (Fintype.card {l // l ∉ H.through B} : ℝ) + (H.through B).card =
      Fintype.card H.Loop := by exact_mod_cast hc2
  have h2' : 2 * ((H.through B).card : ℝ) = L := by exact_mod_cast h2
  have hle' : ((D.restrict (· ∈ H.through B)).strings (ρ • (ξ₀ : ℍ)) s : ℝ) ≤
      (H.through B).card := by exact_mod_cast hle
  refine ⟨?_, by linarith⟩
  linear_combination (r / ρ) ^ 2 * hc2' - (r / ρ) ^ 2 / 2 * h2'

/-- **The strings of a sphere about any point, with the drawing made from the center** (Sec. II,
"Counting in the bulk").  With the register's count of rings (`Register.Bridge.counts_exact`), the
average of `strings_rotation_mean` over the rotations `x ↦ qx` of the drawing is the
chain's `N_s(r) = (L²/4)(r/R_Λ)²`, Eq. (N), times `1 − 2/L + 4/L²`, about every point of the
three-sphere of radius `R_Λ`, for every drawing of the rings (`Register.Bridge.sphere_strings`). -/
theorem sphere_strings_centered {L : ℕ} (H : Horizon L) (R : Register.Reg) (hL : 4 ≤ L)
    (hRL : R.L = L) (D : Drawing H.Loop ℍ R.RL) {s r : ℝ} (hs0 : 0 < s)
    (hs : s ^ 2 ≤ 2 * R.RL ^ 2) (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * R.RL ^ 2))
    (ξ₀ : sphere (0 : ℍ) 1) :
    (∫ q, ((D.rotate (leftRot q)).strings (R.RL • (ξ₀ : ℍ)) s : ℝ) ∂μ.toSphere) /
      μ.toSphere.real Set.univ = R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  rw [strings_rotation_mean μ D R.RL_pos hs0 hs hr ξ₀,
    ← D.meanStrings_eq μ Quaternion.finrank_eq_four R.RL_pos hs0 hs hr]
  exact (Register.Bridge.sphere_strings H R hL hRL μ Quaternion.finrank_eq_four D hs0 hs hr).1

/-- **The strings about any point, averaged over the rotations of the drawing, in any
four-dimensional space** (Sec. II, "Counting in the bulk").  For every drawing `D` of the rings as
great circles of the three-sphere of radius `ρ` in a four-dimensional real inner product space `E`,
every linear isometry `φ : E ≃ ℍ`, every point `ρξ₀` of the three-sphere, and every sphere no
larger than a great sphere, of areal radius `r`, the strings of the sphere about `ρξ₀` in the
drawing turned by `x ↦ φ⁻¹(qφ(x))`, averaged over the unit quaternions `q` in the measure
`μ.toSphere`, are the number of rings times `(r/ρ)²`.  The drawing turned by `rotOf φ q` has about
`ρξ₀` the strings that the drawing carried to `ℍ` by `φ`, turned by `x ↦ qx`, has about `ρφ(ξ₀)`
(`Crossing.Drawing.strings_rotate`), so `strings_rotation_mean` gives the average. -/
theorem strings_rotation_mean_of {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E ≃ₗᵢ[ℝ] ℍ) {ι : Type*} [Fintype ι] (D : Drawing ι E ρ) (hρ : 0 < ρ) (hs0 : 0 < s)
    (hs : s ^ 2 ≤ 2 * ρ ^ 2) {r : ℝ} (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2))
    (ξ₀ : sphere (0 : E) 1) :
    (∫ q, ((D.rotate (rotOf φ q)).strings (ρ • (ξ₀ : E)) s : ℝ) ∂μ.toSphere) /
      μ.toSphere.real Set.univ = Fintype.card ι * (r / ρ) ^ 2 := by
  obtain ⟨ξ₁, hξ₁⟩ : ∃ ξ₁ : sphere (0 : ℍ) 1, (ξ₁ : ℍ) = φ ξ₀ := ⟨⟨φ ξ₀, by simp⟩, rfl⟩
  have h : ∀ q : sphere (0 : ℍ) 1, ((D.rotate (rotOf φ q)).strings (ρ • (ξ₀ : E)) s : ℝ) =
      (((D.rotate φ).rotate (leftRot q)).strings (ρ • (ξ₁ : ℍ)) s : ℝ) := fun q => by
    rw [Drawing.strings_rotate, Drawing.strings_rotate, Drawing.strings_rotate, rotOf_symm_apply,
      LinearIsometryEquiv.map_smul, hξ₁]
  simp_rw [h]
  exact strings_rotation_mean μ (D.rotate φ) hρ hs0 hs hr ξ₁

/-- **The strings of a sphere about any point, in any four-dimensional space** (Sec. II, "Counting
in the bulk").  With the register's count of rings, the average of `strings_rotation_mean_of` over
the rotations `x ↦ φ⁻¹(qφ(x))` of a drawing in a four-dimensional real inner product space `E` is
the chain's `N_s(r)` times `1 − 2/L + 4/L²`, about every point of the three-sphere of radius `R_Λ`,
for every drawing of the rings (`sphere_strings_centered` for the drawing carried to `ℍ`). -/
theorem sphere_strings_centered_of {L : ℕ} (H : Horizon L) (R : Register.Reg) (hL : 4 ≤ L)
    (hRL : R.L = L) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E ≃ₗᵢ[ℝ] ℍ) (D : Drawing H.Loop E R.RL) {s r : ℝ} (hs0 : 0 < s)
    (hs : s ^ 2 ≤ 2 * R.RL ^ 2) (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * R.RL ^ 2))
    (ξ₀ : sphere (0 : E) 1) :
    (∫ q, ((D.rotate (rotOf φ q)).strings (R.RL • (ξ₀ : E)) s : ℝ) ∂μ.toSphere) /
      μ.toSphere.real Set.univ = R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  obtain ⟨ξ₁, -⟩ : ∃ ξ₁ : sphere (0 : ℍ) 1, (ξ₁ : ℍ) = φ ξ₀ := ⟨⟨φ ξ₀, by simp⟩, rfl⟩
  rw [strings_rotation_mean_of μ φ D R.RL_pos hs0 hs hr ξ₀,
    ← strings_rotation_mean μ (D.rotate φ) R.RL_pos hs0 hs hr ξ₁]
  exact sphere_strings_centered μ H R hL hRL (D.rotate φ) hs0 hs hr ξ₁

/-- **The strings of a sphere about any point, with the rings as closed geodesics of space**
(Secs. II and IV.D).  Let every largest ring of `H`, of length `Lℓ_c`, be a closed spacelike
geodesic of the space at an instant of de Sitter space of radius `ρ`, in a four-dimensional real
inner product space `E` (the hypotheses of `Register.Bridge.sphere_strings_of_rings`), and let
`φ : E ≃ ℍ` be a linear isometry (`exists_isometry_quaternion`).  Then `ρ = R_Λ`, and the strings of
a sphere of areal radius `r` about any point of the three-sphere, in the drawing of the rings
(`Crossing.Drawing.ofRings`) turned by `x ↦ φ⁻¹(qφ(x))` and averaged over the unit quaternions
`q`, are `N_s(r)(1 − 2/L + 4/L²)`. -/
theorem sphere_strings_of_rings_centered {L : ℕ} (H : Horizon L) (R : Register.Reg) (hL : 4 ≤ L)
    (hRL : R.L = L) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4)
    (φ : E ≃ₗᵢ[ℝ] ℍ) {ρ : ℝ} (hρ : 0 < ρ) (γ : H.Loop → Geodesic.Curve ℝ E)
    (hgeo : ∀ l, Geodesic.IsGeodesic (ρ ^ 2) (γ l)) (hsp : ∀ l, Geodesic.IsSpacelike (γ l))
    (hin : ∀ l, Geodesic.InSpace (γ l)) (hlen : ∀ l, Geodesic.HasLength (γ l) (R.L * R.ℓc))
    {s r : ℝ} (hs0 : 0 < s) (hs : s ^ 2 ≤ 2 * ρ ^ 2) (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2))
    (ξ₀ : sphere (0 : E) 1) :
    ρ = R.RL ∧
    (∫ q, (((Drawing.ofRings hρ γ hgeo hsp hin).rotate (rotOf φ q)).strings (ρ • (ξ₀ : E)) s : ℝ)
        ∂μ.toSphere) / μ.toSphere.real Set.univ = R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hρeq := (Register.Bridge.sphere_strings_of_rings H R hL hRL Measure.addHaar hE hρ γ hgeo
    hsp hin hlen hs0 hs hr).1
  refine ⟨hρeq, ?_⟩
  subst hρeq
  exact sphere_strings_centered_of μ H R hL hRL φ _ hs0 hs hr ξ₀

end Mean

section Model

noncomputable local instance : MeasurableSpace ℍ := borel ℍ

local instance : BorelSpace ℍ := ⟨rfl⟩

/-- **The hypotheses of `sphere_strings_centered` can be met together**, so it does not hold
vacuously: the Fano model's rings (`Horizon.fano`, `L = 6`), the register `Register.Bridge.regSix`
with the same `L` and the real `π`, `ℍ` with its Borel sets and a Haar measure, every ring the great
circle through `R_Λ` and `R_Λ i`, the sphere at distance `s = R_Λ`, and its center at the point
`R_Λ`.  The average it returns is positive. -/
theorem sphere_strings_centered_model :
    ∃ D : Drawing Horizon.fano.Loop ℍ Register.Bridge.regSix.RL,
      0 < (∫ q, ((D.rotate (leftRot q)).strings
          (Register.Bridge.regSix.RL • (((⟨1, by simp⟩ : sphere (0 : ℍ) 1)) : ℍ))
          Register.Bridge.regSix.RL : ℝ) ∂(Measure.addHaar : Measure ℍ).toSphere) /
        (Measure.addHaar : Measure ℍ).toSphere.real Set.univ := by
  have hRL := Register.Bridge.regSix.RL_pos
  have hI : ‖(⟨0, 1, 0, 0⟩ : ℍ)‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, Quaternion.inner_self]
    simp [normSq_def']
  let D : Drawing Horizon.fano.Loop ℍ Register.Bridge.regSix.RL :=
    { a := fun _ => Register.Bridge.regSix.RL • (1 : ℍ)
      b := fun _ => Register.Bridge.regSix.RL • (⟨0, 1, 0, 0⟩ : ℍ)
      orth := fun _ => by
        rw [real_inner_smul_left, real_inner_smul_right, inner_def]
        simp
      norm_a := fun _ => by rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos hRL]
      norm_b := fun _ => by rw [norm_smul, hI, mul_one, Real.norm_eq_abs, abs_of_pos hRL] }
  refine ⟨D, ?_⟩
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : (Register.Bridge.regSix.RL * (Real.sqrt 3 / 2)) ^ 2 =
      Register.Bridge.regSix.RL ^ 2 -
        Register.Bridge.regSix.RL ^ 4 / (4 * Register.Bridge.regSix.RL ^ 2) := by
    field_simp
    nlinarith [h3]
  have hs : Register.Bridge.regSix.RL ^ 2 ≤ 2 * Register.Bridge.regSix.RL ^ 2 := by nlinarith
  rw [sphere_strings_centered Measure.addHaar Horizon.fano Register.Bridge.regSix (by norm_num)
    (by simp [Register.Bridge.regSix]) D hRL hs hr _, Register.Reg.bulk_counts]
  unfold Register.Reg.n
  have hpi := Register.Bridge.regSix.pi_pos
  have hl := Register.Bridge.regSix.ℓc_pos
  have hc : (0 : ℝ) < 1 - 2 / Register.Bridge.regSix.L + 4 / Register.Bridge.regSix.L ^ 2 := by
    simp only [Register.Bridge.regSix]
    norm_num
  have hr0 : 0 < Register.Bridge.regSix.RL * (Real.sqrt 3 / 2) := by positivity
  positivity

/-- **The hypotheses of `sphere_strings_of_rings_centered` can be met together**, so it does not
hold vacuously: the Fano model's rings (`Horizon.fano`, `L = 6`), the register
`Register.Bridge.regSix` with the same `L` and the real `π`, the Euclidean space `ℝ⁴`, every ring
the great circle through `R_Λ e₀` and `R_Λ e₁` of the space at an instant of de Sitter space of
radius `R_Λ` (`Geodesic.circleCurve`), each of length `Lℓ_c`, a linear isometry `φ : ℝ⁴ ≃ ℍ`
(`exists_isometry_quaternion`), the sphere at distance `s = R_Λ`, and its center at `R_Λ e₀`.  The
average it returns is positive. -/
theorem sphere_strings_of_rings_centered_model :
    ∃ (γ : Horizon.fano.Loop → Geodesic.Curve ℝ (EuclideanSpace ℝ (Fin 4)))
      (hgeo : ∀ l, Geodesic.IsGeodesic (Register.Bridge.regSix.RL ^ 2) (γ l))
      (hsp : ∀ l, Geodesic.IsSpacelike (γ l)) (hin : ∀ l, Geodesic.InSpace (γ l))
      (φ : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] ℍ),
      (∀ l, Geodesic.HasLength (γ l) (Register.Bridge.regSix.L * Register.Bridge.regSix.ℓc)) ∧
      0 < (∫ q, (((Drawing.ofRings Register.Bridge.regSix.RL_pos γ hgeo hsp hin).rotate
            (rotOf φ q)).strings (Register.Bridge.regSix.RL •
              ((⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩ :
                sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : EuclideanSpace ℝ (Fin 4)))
            Register.Bridge.regSix.RL : ℝ) ∂(Measure.addHaar : Measure ℍ).toSphere) /
        (Measure.addHaar : Measure ℍ).toSphere.real Set.univ := by
  have hRL := Register.Bridge.regSix.RL_pos
  have hab : ⟪Register.Bridge.regSix.RL • EuclideanSpace.single (0 : Fin 4) (1 : ℝ),
      Register.Bridge.regSix.RL • EuclideanSpace.single (1 : Fin 4) (1 : ℝ)⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_left]
    simp
  have hn : ∀ j : Fin 4, ‖Register.Bridge.regSix.RL • EuclideanSpace.single j (1 : ℝ)‖ =
      Register.Bridge.regSix.RL := fun j => by
    simp [norm_smul, abs_of_pos hRL]
  have hgeo := Geodesic.circleCurve_geodesic (ω := 1) hab (hn 0) (hn 1)
  have hsp := Geodesic.circleCurve_spacelike (ω := 1) hab (hn 0) (hn 1) hRL one_ne_zero
  have hlen : Geodesic.HasLength
      (Geodesic.circleCurve (Register.Bridge.regSix.RL • EuclideanSpace.single (0 : Fin 4) (1 : ℝ))
        (Register.Bridge.regSix.RL • EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) 1)
      (Register.Bridge.regSix.L * Register.Bridge.regSix.ℓc) := by
    have h := hgeo.hasLength (by positivity) hsp
    have e : 2 * Real.pi * Real.sqrt (Register.Bridge.regSix.RL ^ 2) =
        Register.Bridge.regSix.L * Register.Bridge.regSix.ℓc := by
      rw [Real.sqrt_sq hRL.le]
      unfold Register.Reg.RL
      simp only [Register.Bridge.regSix, Register.Reg.pi_def]
      field_simp
    rwa [e] at h
  obtain ⟨φ⟩ := exists_isometry_quaternion (E := EuclideanSpace ℝ (Fin 4)) (by simp)
  refine ⟨fun _ => _, fun _ => hgeo, fun _ => hsp, fun _ => Geodesic.circleCurve_inSpace, φ,
    fun _ => hlen, ?_⟩
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : (Register.Bridge.regSix.RL * (Real.sqrt 3 / 2)) ^ 2 =
      Register.Bridge.regSix.RL ^ 2 -
        Register.Bridge.regSix.RL ^ 4 / (4 * Register.Bridge.regSix.RL ^ 2) := by
    field_simp
    nlinarith [h3]
  have hs : Register.Bridge.regSix.RL ^ 2 ≤ 2 * Register.Bridge.regSix.RL ^ 2 := by nlinarith
  rw [(sphere_strings_of_rings_centered Measure.addHaar Horizon.fano Register.Bridge.regSix
    (by norm_num) (by simp [Register.Bridge.regSix]) (by simp) φ hRL _ (fun _ => hgeo)
    (fun _ => hsp) (fun _ => Geodesic.circleCurve_inSpace) (fun _ => hlen) hRL hs hr _).2,
    Register.Reg.bulk_counts]
  unfold Register.Reg.n
  have hpi := Register.Bridge.regSix.pi_pos
  have hl := Register.Bridge.regSix.ℓc_pos
  have hc : (0 : ℝ) < 1 - 2 / Register.Bridge.regSix.L + 4 / Register.Bridge.regSix.L ^ 2 := by
    simp only [Register.Bridge.regSix]
    norm_num
  have hr0 : 0 < Register.Bridge.regSix.RL * (Real.sqrt 3 / 2) := by positivity
  positivity

end Model

end Center
