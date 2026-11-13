import RegisterGravity.DiffSet

/-!
# The axioms of `Horizon` and `Positions` have a model

A theorem proved from contradictory axioms would hold vacuously, so the axioms of `Horizon L` and of
its cyclic order need a model.  The files give one with `L = 6`, the smallest `L` at which the
register is a projective plane in Mathlib's sense (`Projective.lean`; at `L = 4` a doubled
triangle meets the clauses): the Fano plane, the projective plane of
order `2 = L/2 − 1`, with each point doubled into a cell and its opposite; it is an incidence
structure, not a drawing, and like every finite projective plane of order at least 2 it has no
drawing with straight lines or great circles (`Horizon.lean`).  The lines are taken in Singer's
form, `{k, k + 1, k + 3}` mod 7, and each ring runs through its three points on one side and back
through them on the other, so that the opposite of a cell lies three steps, half the ring, on.
Every clause is checked by `decide`, and the counts of `Horizon.counts` come out as
`14 = L²/2 − L + 2` cells and `7 = L²/4 − L/2 + 1` rings.

The model has the maps of the clause of Postulate 2 that no cell differs from another
(`fano_homogeneous`): the Singer cycle
`p ↦ p + t` and the swap of sides are symmetries (`fanoSym`), and together they carry any cell to
any other.  `DiffSet.lean` and `Singer.lean`
give the same construction for every prime-power order.
-/

open Finset

namespace Horizon

/-- The seven lines of the Fano plane on the points `0, …, 6`, in Singer's form: the line `k` is
`{k, k + 1, k + 3}`, added mod 7. -/
def fanoLines (k : Fin 7) : Finset (Fin 7) := {k, k + 1, k + 3}

/-- **A horizon with `L = 6`**: cells are (point, side), the opposite flips the side, and a largest
ring is a Fano line with both sides of each of its three points. -/
def fano : Horizon 6 where
  Cell := Fin 7 × Bool
  Loop := Fin 7
  opp x := (x.1, !x.2)
  cells l := fanoLines l ×ˢ univ
  opp_opp := by decide
  opp_ne := by decide
  card_cells := by decide
  opp_mem := by decide
  exists_loop := by decide
  unique_loop := by decide
  loops_meet := by decide
  misses := by decide
  exists_ring := ⟨0⟩

/-- the place of the point `p` on the line `k`: `0`, `1` or `2` for `k`, `k + 1`, `k + 3` -/
def fanoIdx (k p : Fin 7) : ZMod 6 := if p = k then 0 else if p = k + 1 then 1 else 2

/-- **Positions on the Fano horizon**: the ring `k` runs through `k`, `k + 1`, `k + 3` on one side,
at the positions `0, 1, 2`, and back through them on the other, at `3, 4, 5`; the opposite of a
cell lies three steps, half the ring, on. -/
def fanoPositions : fano.Positions where
  pos k x := fanoIdx k x.1 + (if x.2 then 3 else 0)
  pos_inj := by decide
  pos_opp := by decide

lemma fano_mem_shift (t : Fin 7) (f : Bool) (l : Fin 7) (x : Fin 7 × Bool) :
    x ∈ fanoLines l ×ˢ (univ : Finset Bool) ↔ (x.1 + t, xor x.2 f) ∈ fanoLines (l + t) ×ˢ univ := by
  revert t f l x
  decide

/-- **The Singer cycle and the swap of sides**: `p ↦ p + t` on the points, `k ↦ k + t` on the
lines, and every side flipped or not; each is a symmetry of the model. -/
def fanoSym (t : Fin 7) (f : Bool) : fano.Symmetry where
  cellMap := ((Equiv.addRight t).prodCongr (xorEquiv f) : Fin 7 × Bool ≃ Fin 7 × Bool)
  loopMap := (Equiv.addRight t : Fin 7 ≃ Fin 7)
  mem_iff l x := fano_mem_shift t f l x

/-- **The model has the maps of the clause of Postulate 2 that no cell differs from another**: the
Singer cycle and the swap of sides carry any cell to any other. -/
theorem fano_homogeneous : fano.Homogeneous := by
  intro x y
  refine ⟨fanoSym (y.1 - x.1) (xor x.2 y.2), ?_⟩
  show (x.1 + (y.1 - x.1), xor x.2 (xor x.2 y.2)) = y
  refine Prod.ext ?_ ?_
  · show x.1 + (y.1 - x.1) = y.1
    abel
  · show xor x.2 (xor x.2 y.2) = y.2
    cases x.2 <;> cases y.2 <;> rfl

end Horizon
