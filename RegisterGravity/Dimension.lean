import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# The dimension of space from the incidence of the rings (Sec. II)

The paper's sentences after Eq. (ident): "By the symmetry of space a largest ring can run through
a cell in any direction, so every great circle of that sphere is one. Any two largest rings share a
cell (Postulate 2), which great circles of a sphere of three or more dimensions need not. So the
sphere is a two-sphere, and space has three dimensions."

A sphere about a point of a `d`-dimensional space is the unit sphere of a `d`-dimensional real
vector space `V`, and a great circle of it is its intersection with a plane through the origin, a
two-dimensional subspace of `V`.  Two great circles meet exactly when their planes share a line,
that is, when the planes' intersection is not `⊥`.  So the sentences are a statement about the
two-dimensional subspaces of `V`, and it follows from the dimension formula
`finrank (P ⊔ Q) + finrank (P ⊓ Q) = finrank P + finrank Q`:

* `planes_meet`: if `finrank V ≤ 3`, any two planes through the origin share a line (any two great
  circles of a two-sphere meet).
* `disjoint_planes_exist`: if `finrank V ≥ 4`, two planes through the origin can share only the
  origin (two great circles of a sphere of three or more dimensions can miss each other).
* `dimension_three`: if any two planes through the origin share a line, and there are two distinct
  planes, then `finrank V = 3`.

The hypotheses of `dimension_three` are the paper's premises as stated: the incidence clause of
Postulate 2, read on every great circle of the sphere by the symmetry of space, and "no ring holds
every cell", which gives a second ring.  Nothing else enters; the space is any finite-dimensional
real vector space.
-/

open Module Submodule

namespace Register.Dimension

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Any two great circles of a two-sphere meet.**  In a space of dimension at most `3`, two planes
through the origin share a line: their intersection is not `⊥`. -/
theorem planes_meet (h : finrank ℝ V ≤ 3) (P Q : Submodule ℝ V)
    (hP : finrank ℝ P = 2) (hQ : finrank ℝ Q = 2) : P ⊓ Q ≠ ⊥ := by
  intro hbot
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have h2 : finrank ℝ ↥(P ⊓ Q) = 0 := by rw [hbot]; exact finrank_bot ℝ V
  have h3 : finrank ℝ ↥(P ⊔ Q) ≤ finrank ℝ V := Submodule.finrank_le _
  omega

/-- **Great circles of a sphere of three or more dimensions can miss each other.**  In a space of
dimension at least `4`, two planes through the origin can share only the origin. -/
theorem disjoint_planes_exist (h : 4 ≤ finrank ℝ V) :
    ∃ P Q : Submodule ℝ V, finrank ℝ P = 2 ∧ finrank ℝ Q = 2 ∧ P ⊓ Q = ⊥ := by
  let b := Module.finBasis ℝ V
  let f : Fin 2 → Fin (finrank ℝ V) := fun i => ⟨i.1, by omega⟩
  let g : Fin 2 → Fin (finrank ℝ V) := fun i => ⟨i.1 + 2, by omega⟩
  have hf : Function.Injective f := by
    intro i j hij; exact Fin.ext (by simpa [f] using congrArg Fin.val hij)
  have hg : Function.Injective g := by
    intro i j hij
    have := congrArg Fin.val hij
    simp only [g] at this
    exact Fin.ext (by omega)
  have hdisj : Disjoint (Set.range f) (Set.range g) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp only [f, g] at this
    omega
  refine ⟨span ℝ (Set.range (b ∘ f)), span ℝ (Set.range (b ∘ g)), ?_, ?_, ?_⟩
  · rw [finrank_span_eq_card (b.linearIndependent.comp f hf)]; simp
  · rw [finrank_span_eq_card (b.linearIndependent.comp g hg)]; simp
  · rw [Set.range_comp, Set.range_comp]
    exact disjoint_iff.mp (b.linearIndependent.disjoint_span_image hdisj)

/-- **Space has three dimensions** (Sec. II).  If any two planes through the origin share a line
(Postulate 2's incidence clause, read on every great circle of the sphere by the symmetry of
space) and there are two distinct planes (no ring holds every cell), the space has dimension
exactly `3`. -/
theorem dimension_three
    (hmeet : ∀ P Q : Submodule ℝ V, finrank ℝ P = 2 → finrank ℝ Q = 2 → P ⊓ Q ≠ ⊥)
    (htwo : ∃ P Q : Submodule ℝ V, finrank ℝ P = 2 ∧ finrank ℝ Q = 2 ∧ P ≠ Q) :
    finrank ℝ V = 3 := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := htwo
  have hle : finrank ℝ V ≤ 3 := by
    by_contra hlt
    obtain ⟨P', Q', hP', hQ', hbot⟩ := disjoint_planes_exist (V := V) (by omega)
    exact hmeet P' Q' hP' hQ' hbot
  have hge : 3 ≤ finrank ℝ V := by
    by_contra hlt
    have hPle : finrank ℝ P ≤ finrank ℝ V := Submodule.finrank_le P
    have hV : finrank ℝ V = 2 := by omega
    have hPtop : P = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hP, hV])
    have hQtop : Q = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hQ, hV])
    exact hPQ (hPtop.trans hQtop.symm)
  omega

end Register.Dimension
