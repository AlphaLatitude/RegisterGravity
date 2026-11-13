import RegisterGravity.RouteB

/-!
# No cell differs from another (Postulate 2)

After its four clauses on cells and rings, Postulate 2 says: "No cell differs from another: some map
of the cells that keeps the largest rings carries any cell to any other and leaves every law
unchanged.  No law depends on the direction in which a ring passes through a cell.  Every largest
ring is a closed geodesic of space, made of its cells as segments of length `ℓ_c`."  This file
concerns the first of these clauses.  A
**symmetry** of a register is a map of the cells onto themselves, with a map of the largest rings,
that keeps which cells lie on which ring (`Symmetry`).

The clause has two parts.  The first, that some symmetry carries any cell to any other, is a
property of the register, `Horizon.Homogeneous`; `Models.lean`, `DiffSet.lean` and `Singer.lean`
build registers that have it, for every prime-power order.  The second, that the symmetry leaves
every law unchanged, concerns the laws.  `Symmetry.lean` states the laws as functions of the
register, of the crossing of a ring with a cell, and takes the whole clause as its hypothesis
`hsym`; with the clause on directions it derives the symmetry of space (Sec. II): every law is the
same at every place and in every direction of the space the rings describe, whatever the drawing
(`Symmetry.laws_same`, `Symmetry.lawAt_same`).

Until v18-40 the clause also asked that the map keep the positions of the cells along the rings up
to one common shift, and the structure carried that as a field; no theorem used it, and the paper
(-6-38-27) drops the words.
-/

open Finset

namespace Horizon

variable {L : ℕ} (H : Horizon L)

/-- **A symmetry of the register**: a map of the cells onto themselves, with a map of the largest
rings, that keeps which cells lie on which ring. -/
structure Symmetry where
  /-- where each cell goes -/
  cellMap : H.Cell ≃ H.Cell
  /-- where each ring goes -/
  loopMap : H.Loop ≃ H.Loop
  /-- a cell lies on a ring exactly when its image lies on the ring's image -/
  mem_iff : ∀ l x, x ∈ H.cells l ↔ cellMap x ∈ H.cells (loopMap l)

/-- **The register's part of the clause of Postulate 2 that no cell differs from another**: some
symmetry of the register carries any cell to any other. -/
def Homogeneous : Prop := ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y

end Horizon
