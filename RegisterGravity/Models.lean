import RegisterGravity.Projective

/-!
# The axioms of `Horizon` have a model

A theorem proved from contradictory axioms would hold vacuously, so the axioms of `Horizon L` need
a model.  The smallest is `L = 6`: the Fano plane, the projective plane of order `2 = L/2 − 1`,
with each point doubled into a cell and its opposite.  Every axiom is checked by `decide`, and the
counts of `Horizon.counts` come out as `14 = L²/2 − L + 2` cells and `7 = L²/4 − L/2 + 1` rings.
-/

open Finset

namespace Horizon

/-- The seven lines of the Fano plane on the points `0, …, 6`. -/
def fanoLines : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

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
  two_loops := by decide

/-- The counts of Eq. (counts) for the model: `14` cells, `7` rings, `ρ = 3` rings per cell. -/
theorem fano_counts :
    Fintype.card fano.Cell = 14 ∧ Fintype.card fano.Loop = 7 ∧
    2 * Fintype.card fano.Cell + 2 * 6 = 6 ^ 2 + 4 ∧
    4 * Fintype.card fano.Loop + 2 * 6 = 6 ^ 2 + 4 := by
  have h := fano.counts (by norm_num)
  refine ⟨by decide, by decide, h.2.1, h.2.2.1⟩

/-- The model is a projective plane of order `2 = L/2 − 1`. -/
theorem fano_order : fano.order (by norm_num) = 2 := by
  have h := fano.two_mul_order_add_one (by norm_num)
  omega

end Horizon
