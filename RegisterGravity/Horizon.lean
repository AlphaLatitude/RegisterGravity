import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# The count of the horizon

Formal counterpart of Sec. II, "The count", of *Gravitation from Hilbert-Space Granularity*,
Eq. (counts):

  ρ = L/2 largest rings through every cell,
  C = 2 + ρ(L − 2) = L²/2 − L + 2 cells,
  R = Cρ/L = L²/4 − L/2 + 1 largest rings,
  C = 2R.

## What is assumed

`Horizon L` packages exactly what the paper's argument uses:

* Postulate 2, first clause: every cell `x` has one opposite `opp x` (an involution without fixed
  points), and the opposite lies on every largest ring through `x` (`opp_mem`).
* Postulate 2, second clause: two cells that are not opposite lie on exactly one largest ring
  (`exists_loop`, `unique_loop`).
* Postulate 2, third clause: any two largest rings share a cell (`loops_meet`).
* Postulate 2, fourth clause: no ring holds every cell (`misses`), in the paper's words.
* Every largest ring has `L` cells (`card_cells`), and the register has a largest ring
  (`exists_ring`), as Sec. II's definition of `L` presumes; so it has two different largest rings
  (`two_loops`), the one it has and the ring through a cell it misses and one of its cells.
* The cells and the rings are finite types (`fintypeCell`, `fintypeLoop`, with decidable equality
  for computation).  This is data the clauses force, not a premise: `finite_of_clauses` proves
  from the clauses, with the `L` cells of each largest ring, a largest ring present and `4 ≤ L`,
  that the cells and the rings are finite
  (`finite_cell_and_loop` for a register), and any two enumerations of a finite type give the
  same `Fintype`.

The clause of Postulate 2 that no cell differs from another concerns the laws as well, so its part
on the register is stated in `Homogeneous.lean`; the count does not use it, nor the clause on
directions, nor the last sentence, that every largest ring is a closed geodesic of space, made of
its cells as segments of length `ℓ_c`.

The theorems below take `4 ≤ L` (a largest ring has at least two opposite pairs), which the fourth
clause gives (`four_le`).  Nothing else is assumed: no metric, no area, no Bekenstein–Hawking, and
no drawing of the register in space.  For `L ≥ 6` none exists that puts every cell at one point of
the three-sphere and every largest ring on a great circle through the points of its cells, by the
Sylvester–Gallai theorem [P. Erdős, Problem 4065, Amer. Math. Monthly 50, 65 (1943); R. Steinberg,
solution, ibid. 51, 169 (1944)], which the files do not prove.  Any two rings share a cell, and
great circles of the three-sphere that meet in pairs pass through one pair of antipodal points or
lie on one great two-sphere; no cell lies on every ring, since `L/2` rings pass through a cell; and
with a cell and its opposite as a point and a largest ring as a line, the register is a finite
projective plane (`Projective.lean`), whose every line holds `L/2 ≥ 3` points, while a finite set of
points of the real projective plane, not all on one line, always determines a line through exactly
two of them.  Neither the paper nor the files draw it so: both show which rings
share a cell only for the rings through the observer's cell (Sec. II, "What the manifold
contributes"; `Space.RingsDrawn`), and `Crossing.Drawing` draws the rings alone, as great circles,
without the places of their cells.  The count is
an incidence structure; what joins it to the horizon's area is that every ring has half its cells
inside any observer's horizon (`RouteB.lean`, `Bridge.horizon_entropy_count`), so every ring
crosses it; the horizon counts them all, since its thermal state is a state of the strings alone,
the thesis of the paper (`Bridge.horizonEntropy`, `Bridge.horizon_counts_every_ring`), and a ring's
share of its area
(`Chain.ringShare`) is the area over the count.  The proof follows the paper: a largest ring
`E` that misses a cell `P` (`exists_loop_not_mem`, by the paper's construction, from a cell off a
ring, `misses`), then `ρ = L/2` by
counting the pairs of `E` (`two_mul_card_through`), then `C` and `R`.  That `L` is even follows
here from `ρ = L/2` (`even_L`), and in `RouteB.lean` from the opposite lying halfway around
(`Positions.even_of_halfway`), which is the paper's reason.
-/

open Finset

/-- The horizon of the register: a finite set of cells with an opposite map, and the largest
rings (`Loop`s) of `L` cells on it. -/
structure Horizon (L : ℕ) where
  /-- the cells of the horizon -/
  Cell : Type
  /-- the largest rings on the horizon -/
  Loop : Type
  [fintypeCell : Fintype Cell]
  [fintypeLoop : Fintype Loop]
  [decEqCell : DecidableEq Cell]
  [decEqLoop : DecidableEq Loop]
  /-- the opposite of a cell -/
  opp : Cell → Cell
  /-- the cells of a largest ring -/
  cells : Loop → Finset Cell
  /-- the opposite of the opposite is the cell itself -/
  opp_opp : ∀ x, opp (opp x) = x
  /-- no cell is its own opposite -/
  opp_ne : ∀ x, opp x ≠ x
  /-- every largest ring has `L` cells -/
  card_cells : ∀ l, (cells l).card = L
  /-- Postulate 2, first clause: the opposite lies on every largest ring through the cell -/
  opp_mem : ∀ l x, x ∈ cells l → opp x ∈ cells l
  /-- Postulate 2, second clause (existence): two cells not opposite lie on a largest ring -/
  exists_loop : ∀ x y, y ≠ x → y ≠ opp x → ∃ l, x ∈ cells l ∧ y ∈ cells l
  /-- Postulate 2, second clause (uniqueness): two cells not opposite lie on one largest ring -/
  unique_loop : ∀ x y l₁ l₂, y ≠ x → y ≠ opp x →
    x ∈ cells l₁ → y ∈ cells l₁ → x ∈ cells l₂ → y ∈ cells l₂ → l₁ = l₂
  /-- Postulate 2, third clause: any two largest rings share a cell -/
  loops_meet : ∀ l₁ l₂, ∃ x, x ∈ cells l₁ ∧ x ∈ cells l₂
  /-- Postulate 2, fourth clause: no ring holds every cell -/
  misses : ∀ l, ∃ x, x ∉ cells l
  /-- the register has a largest ring, whose `L` cells define `L` (Sec. II) -/
  exists_ring : Nonempty Loop

namespace Horizon

attribute [instance] Horizon.fintypeCell Horizon.fintypeLoop Horizon.decEqCell Horizon.decEqLoop

variable {L : ℕ} (H : Horizon L)

lemma opp_mem_iff (l : H.Loop) (x : H.Cell) : H.opp x ∈ H.cells l ↔ x ∈ H.cells l := by
  constructor
  · intro h
    have := H.opp_mem l _ h
    rwa [H.opp_opp] at this
  · exact H.opp_mem l x

lemma ne_opp_symm {x y : H.Cell} (h : y ≠ H.opp x) : x ≠ H.opp y := by
  intro hx
  apply h
  rw [hx, H.opp_opp]

/-- Two distinct largest rings share exactly one opposite pair. -/
lemma inter_eq_pair {l₁ l₂ : H.Loop} (h : l₁ ≠ l₂) :
    ∃ x, H.cells l₁ ∩ H.cells l₂ = {x, H.opp x} := by
  obtain ⟨x, hx₁, hx₂⟩ := H.loops_meet l₁ l₂
  refine ⟨x, ?_⟩
  ext y
  simp only [mem_inter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hy₁, hy₂⟩
    by_contra hy
    push Not at hy
    exact h (H.unique_loop x y l₁ l₂ hy.1 hy.2 hx₁ hy₁ hx₂ hy₂)
  · rintro (rfl | rfl)
    · exact ⟨hx₁, hx₂⟩
    · exact ⟨H.opp_mem _ _ hx₁, H.opp_mem _ _ hx₂⟩

/-- The largest rings through a cell. -/
def through (x : H.Cell) : Finset H.Loop := univ.filter (fun l => x ∈ H.cells l)

lemma mem_through {x : H.Cell} {l : H.Loop} : l ∈ H.through x ↔ x ∈ H.cells l := by
  simp [through]

/-- A cell of a largest ring that lies outside a given pair (needs `4 ≤ L`). -/
lemma exists_mem_notMem_pair (hL : 4 ≤ L) (l : H.Loop) (a b : H.Cell) :
    ∃ y ∈ H.cells l, y ≠ a ∧ y ≠ b := by
  have hlt : ({a, b} : Finset H.Cell).card < (H.cells l).card := by
    rw [H.card_cells]
    exact lt_of_le_of_lt card_le_two (by omega)
  obtain ⟨y, hy, hy'⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨y, hy, ?_, ?_⟩
  · intro h; apply hy'; simp [h]
  · intro h; apply hy'; simp [h]

/-- **The register has two different largest rings.**  A largest ring `l₀` (`exists_ring`) misses a
cell `x` (the fourth clause) and holds a cell `y` (the third clause, `l₀` with itself); `x` and `y`
are not opposite, since the opposite of `y` lies on `l₀`, so the largest ring through them holds
`x` and is not `l₀`. -/
theorem two_loops : ∃ l₁ l₂ : H.Loop, l₁ ≠ l₂ := by
  obtain ⟨l₀⟩ := H.exists_ring
  obtain ⟨x, hx⟩ := H.misses l₀
  obtain ⟨y, hy, -⟩ := H.loops_meet l₀ l₀
  have hxy : x ≠ y := fun h => hx (h ▸ hy)
  have hxo : x ≠ H.opp y := fun h => hx (h ▸ H.opp_mem l₀ y hy)
  obtain ⟨l, -, hxl⟩ := H.exists_loop y x hxy hxo
  exact ⟨l, l₀, fun h => hx (h ▸ hxl)⟩

/-- A largest ring through a given cell (needs `4 ≤ L`): join the cell to a cell of any largest
ring outside its pair. -/
lemma exists_loop_mem (hL : 4 ≤ L) (P : H.Cell) : ∃ A : H.Loop, P ∈ H.cells A := by
  obtain ⟨l₁, -, -⟩ := H.two_loops
  obtain ⟨y, -, hyP, hyP'⟩ := H.exists_mem_notMem_pair hL l₁ P (H.opp P)
  obtain ⟨A, hPA, -⟩ := H.exists_loop P y hyP hyP'
  exact ⟨A, hPA⟩

/-- **The clauses force the cells and the rings to be finite** (Sec. II, "The count"), stated over
the clauses, with the `L` cells of each largest ring (`card_cells`), a largest ring present
(`exists_ring`) and `4 ≤ L`, and with no finiteness assumed, so that the fields `fintypeCell` and `fintypeLoop`
of `Horizon` are seen to carry no premise: a `Fintype` is a finite type with an enumeration chosen,
and any two enumerations give the same `Fintype`.  Take two different rings (below).
The second has a cell `P` off the first, `E`, since two rings share at most a cell and its opposite
(the second clause) and a ring has `L ≥ 4` cells; the opposite of `P` is off `E` too (the first
clause).  Every other cell `x` lies with `P` on one ring (the second clause), which meets `E` (the
third clause) at a cell `e`, neither `P` nor its opposite; so that ring is the ring through `P` and
`e`, and the cells are `P`, its opposite, and the cells of the rings through `P` and each of the `L`
cells of `E`: finitely many.  A ring is fixed by two of its cells not opposite (the second clause), so the
rings inject into the pairs of cells.  The two different rings are a ring and the ring through a
cell it misses (the fourth clause) and one of its cells, as in `two_loops`. -/
theorem finite_of_clauses {Cell Loop : Type} (opp : Cell → Cell) (cells : Loop → Finset Cell)
    (opp_opp : ∀ x, opp (opp x) = x)
    (card_cells : ∀ l, (cells l).card = L) (opp_mem : ∀ l x, x ∈ cells l → opp x ∈ cells l)
    (exists_loop : ∀ x y, y ≠ x → y ≠ opp x → ∃ l, x ∈ cells l ∧ y ∈ cells l)
    (unique_loop : ∀ x y l₁ l₂, y ≠ x → y ≠ opp x →
      x ∈ cells l₁ → y ∈ cells l₁ → x ∈ cells l₂ → y ∈ cells l₂ → l₁ = l₂)
    (loops_meet : ∀ l₁ l₂, ∃ x, x ∈ cells l₁ ∧ x ∈ cells l₂)
    (exists_ring : Nonempty Loop) (misses : ∀ l, ∃ x, x ∉ cells l) (hL : 4 ≤ L) :
    Finite Cell ∧ Finite Loop := by
  classical
  have two_loops : ∃ l₁ l₂ : Loop, l₁ ≠ l₂ := by
    obtain ⟨l₀⟩ := exists_ring
    obtain ⟨x, hx⟩ := misses l₀
    obtain ⟨y, hy, -⟩ := loops_meet l₀ l₀
    have hxy : x ≠ y := fun h => hx (h ▸ hy)
    have hxo : x ≠ opp y := fun h => hx (h ▸ opp_mem l₀ y hy)
    obtain ⟨l, -, hxl⟩ := exists_loop y x hxy hxo
    exact ⟨l, l₀, fun h => hx (h ▸ hxl)⟩
  have nonempty : ∀ l, (cells l).Nonempty := fun l => by
    rw [← card_pos, card_cells]; omega
  -- a third cell on any ring, neither a given cell nor its opposite
  have third : ∀ l, ∀ x ∈ cells l, ∃ y ∈ cells l, y ≠ x ∧ y ≠ opp x := by
    intro l x hx
    have h1 := pred_card_le_card_erase (s := cells l) (a := x)
    have h2 := pred_card_le_card_erase (s := (cells l).erase x) (a := opp x)
    rw [card_cells] at h1
    have hpos : 0 < (((cells l).erase x).erase (opp x)).card := by omega
    obtain ⟨y, hy⟩ := card_pos.1 hpos
    rw [mem_erase, mem_erase] at hy
    exact ⟨y, hy.2.2, hy.2.1, hy.1⟩
  obtain ⟨E, l₂, hne⟩ := two_loops
  -- a cell `P` of the second ring off `E`
  obtain ⟨P, -, hPE⟩ : ∃ P ∈ cells l₂, P ∉ cells E := by
    by_contra hall
    push Not at hall
    have hsub : cells l₂ ⊆ cells E := fun P hP => hall P hP
    have heq : cells l₂ = cells E :=
      eq_of_subset_of_card_le hsub (by rw [card_cells, card_cells])
    obtain ⟨x, hx⟩ := nonempty l₂
    obtain ⟨y, hy, hyx, hyo⟩ := third l₂ x hx
    exact hne (unique_loop x y E l₂ hyx hyo (heq ▸ hx) (heq ▸ hy) hx hy)
  have hoPE : opp P ∉ cells E := fun h => hPE (opp_opp P ▸ opp_mem E (opp P) h)
  -- the ring through `P` and each cell of `E`
  have hring : ∀ e ∈ cells E, ∃ l, P ∈ cells l ∧ e ∈ cells l := fun e he =>
    exists_loop P e (fun h => hPE (h ▸ he)) (fun h => hoPE (h ▸ he))
  have : Nonempty Loop := ⟨E⟩
  choose! ring hring using hring
  let S : Finset Cell := {P, opp P} ∪ (cells E).biUnion fun e => cells (ring e)
  have hS : ∀ x, x ∈ S := by
    intro x
    by_cases hxP : x = P
    · simp [S, hxP]
    by_cases hxo : x = opp P
    · simp [S, hxo]
    obtain ⟨l, hPl, hxl⟩ := exists_loop P x hxP hxo
    obtain ⟨e, hel, heE⟩ := loops_meet l E
    have heP : e ≠ P := fun h => hPE (h ▸ heE)
    have heo : e ≠ opp P := fun h => hoPE (h ▸ heE)
    have hl : l = ring e :=
      unique_loop P e l (ring e) heP heo hPl hel (hring e heE).1 (hring e heE).2
    simp only [S, mem_union, mem_biUnion]
    exact Or.inr ⟨e, heE, hl ▸ hxl⟩
  have hCell : Finite Cell :=
    Finite.of_injective (fun x : Cell => (⟨x, hS x⟩ : S)) fun x y h => congrArg Subtype.val h
  -- a ring is fixed by two of its cells not opposite
  have hpair : ∀ l : Loop, ∃ p : Cell × Cell,
      p.1 ∈ cells l ∧ p.2 ∈ cells l ∧ p.2 ≠ p.1 ∧ p.2 ≠ opp p.1 := by
    intro l
    obtain ⟨x, hx⟩ := nonempty l
    obtain ⟨y, hy, hyx, hyo⟩ := third l x hx
    exact ⟨(x, y), hx, hy, hyx, hyo⟩
  choose pair hpair using hpair
  have hLoop : Finite Loop := by
    have := hCell
    refine Finite.of_injective pair fun l l' h => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hpair l
    obtain ⟨h1', h2', -, -⟩ := hpair l'
    rw [h] at h1 h2 h3 h4
    exact unique_loop (pair l').1 (pair l').2 l l' h3 h4 h1 h2 h1' h2'
  exact ⟨hCell, hLoop⟩

/-- **A register's cells and rings are finite by its clauses** (`finite_of_clauses`), so the
finiteness that `Horizon` carries as data is forced and not assumed. -/
theorem finite_cell_and_loop (hL : 4 ≤ L) : Finite H.Cell ∧ Finite H.Loop :=
  finite_of_clauses H.opp H.cells H.opp_opp H.card_cells H.opp_mem H.exists_loop H.unique_loop
    H.loops_meet H.exists_ring H.misses hL

/-- **Postulate 2 forces `L ≥ 4`** (Sec. II, "The count").  Let a largest ring `l₀` miss a cell `x`,
as the fourth clause in the paper's words says it does.  `l₀` holds a cell `y` (the third clause,
with `l₀` itself) and its opposite, which differs from `y`; `x` is neither, so `x` and `y` are not
opposite, and the largest ring through them holds `x`, `y` and the opposite of `y`: `L ≥ 3`.  With
`L = 3` the opposite of `x` would be a fourth cell of that ring, since it is not `x`, and it is not
`y` or the opposite of `y`, whose opposites are not `x`.  So `L ≥ 4`, which the count uses for a cell
`S` of `A` other than `P` and `P′`.  Two different rings alone would admit `L = 2` (two rings on
the same opposite pair); the clause in the paper's words does not. -/
theorem four_le_of_misses (l₀ : H.Loop) (x : H.Cell) (hx : x ∉ H.cells l₀) : 4 ≤ L := by
  obtain ⟨y, hy, -⟩ := H.loops_meet l₀ l₀
  have hy' : H.opp y ∈ H.cells l₀ := H.opp_mem l₀ y hy
  have hxy : x ≠ y := fun h => hx (h ▸ hy)
  have hxy' : x ≠ H.opp y := fun h => hx (h ▸ hy')
  obtain ⟨m, hym, hxm⟩ := H.exists_loop y x hxy hxy'
  have hym' : H.opp y ∈ H.cells m := H.opp_mem m y hym
  have hsub : ({x, y, H.opp y} : Finset H.Cell) ⊆ H.cells m := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hxm
    · exact hym
    · exact hym'
  have h3 : ({x, y, H.opp y} : Finset H.Cell).card = 3 := by
    rw [card_insert_of_notMem, card_pair (H.opp_ne y).symm]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hxy, hxy'⟩
  have hle := card_le_card hsub
  rw [h3, H.card_cells] at hle
  -- `L = 3` is impossible: the opposite of `x` would be a fourth cell
  by_contra hlt
  have hL3 : L = 3 := by omega
  have heq : ({x, y, H.opp y} : Finset H.Cell) = H.cells m :=
    eq_of_subset_of_card_le hsub (by rw [h3, H.card_cells, hL3])
  have hox : H.opp x ∈ H.cells m := H.opp_mem m x hxm
  rw [← heq] at hox
  simp only [mem_insert, mem_singleton] at hox
  rcases hox with h | h | h
  · exact H.opp_ne x h
  · apply hxy'
    rw [← h, H.opp_opp]
  · apply hxy
    have := congrArg H.opp h
    rwa [H.opp_opp, H.opp_opp] at this

include H in
/-- **Every register has `L ≥ 4`**: it has a largest ring (`exists_ring`), which misses a cell
(`misses`), and `four_le_of_misses` applies. -/
theorem four_le : 4 ≤ L := by
  obtain ⟨l₀⟩ := H.exists_ring
  obtain ⟨x, hx⟩ := H.misses l₀
  exact H.four_le_of_misses l₀ x hx

/-- **A largest ring that misses a given cell** (Sec. II, the paper's construction).  Take a
largest ring `A` through `P` and a cell `Q` off it (`misses`).  With `S` a cell of `A`
other than `P` and its opposite, `Q` and `S` are not opposite, since the opposite of `S` lies on
`A`, so one largest ring `E` passes through both.  It misses `P`, since the one ring through `P`
and `S` is `A`, which does not hold `Q`.  The paper adds that `E` misses the opposite of `P` as
well, since the opposite of that cell is `P`; that step is `opp_mem_iff`, taken in
`two_mul_card_through`. -/
lemma exists_loop_not_mem (hL : 4 ≤ L) (P : H.Cell) : ∃ E : H.Loop, P ∉ H.cells E := by
  obtain ⟨A, hPA⟩ := H.exists_loop_mem hL P
  obtain ⟨Q, hQ⟩ := H.misses A
  obtain ⟨S, hSA, hSP, hSP'⟩ := H.exists_mem_notMem_pair hL A P (H.opp P)
  have hQS : Q ≠ S := fun h => hQ (h ▸ hSA)
  have hQS' : Q ≠ H.opp S := fun h => hQ (h ▸ H.opp_mem A S hSA)
  obtain ⟨E, hSE, hQE⟩ := H.exists_loop S Q hQS hQS'
  refine ⟨E, fun hPE => hQ ?_⟩
  -- `E` holds `S` and `P`, which are not opposite, so `E` is `A`
  have hE : E = A := H.unique_loop S P E A (Ne.symm hSP) (H.ne_opp_symm hSP') hSE hPE hSA hPA
  exact hE ▸ hQE

/-- **`ρ = L/2`** (Sec. II): twice the number of largest rings through any cell is `L`.  The ring
`E` that misses `P` (`exists_loop_not_mem`) misses the opposite of `P` as well (`opp_mem_iff`).
Each ring through `P` meets `E` in one opposite pair, and each cell of `E`, being neither `P` nor
its opposite, lies on exactly one ring through `P`; counting the pairs (ring through `P`, cell of
`E` on it) both ways gives `2ρ = L`. -/
theorem two_mul_card_through (hL : 4 ≤ L) (P : H.Cell) : 2 * (H.through P).card = L := by
  obtain ⟨E, hPE⟩ := H.exists_loop_not_mem hL P
  have hP'E : H.opp P ∉ H.cells E := fun h => hPE ((H.opp_mem_iff E P).1 h)
  -- double count the pairs (ring through `P`, cell of `E` on it)
  have key : ∑ l ∈ H.through P, ((H.cells E).filter (fun y => y ∈ H.cells l)).card
      = ∑ y ∈ H.cells E, ((H.through P).filter (fun l => y ∈ H.cells l)).card := by
    simp only [card_filter]
    exact sum_comm
  -- each ring through `P` meets `E` in one opposite pair
  have hleft : ∀ l ∈ H.through P, ((H.cells E).filter (fun y => y ∈ H.cells l)).card = 2 := by
    intro l hl
    rw [mem_through] at hl
    have hne : E ≠ l := fun h => hPE (h ▸ hl)
    obtain ⟨x, hx⟩ := H.inter_eq_pair hne
    rw [filter_mem_eq_inter, hx, card_pair (H.opp_ne x).symm]
  -- each cell of `E` lies on exactly one ring through `P`
  have hright : ∀ y ∈ H.cells E, ((H.through P).filter (fun l => y ∈ H.cells l)).card = 1 := by
    intro y hy
    have hyP : y ≠ P := fun h => hPE (h ▸ hy)
    have hyP' : y ≠ H.opp P := fun h => hP'E (h ▸ hy)
    obtain ⟨l, hPl, hyl⟩ := H.exists_loop P y hyP hyP'
    rw [card_eq_one]
    refine ⟨l, ?_⟩
    ext m
    simp only [mem_filter, mem_through, mem_singleton]
    constructor
    · rintro ⟨hPm, hym⟩
      exact H.unique_loop P y m l hyP hyP' hPm hym hPl hyl
    · rintro rfl
      exact ⟨hPl, hyl⟩
  rw [sum_congr rfl hleft, sum_congr rfl hright] at key
  simp only [sum_const, smul_eq_mul, mul_one, H.card_cells] at key
  omega

/-- `C = 2 + ρ(L − 2)`: the rings through `P` cut the cells other than `P` and its opposite
into disjoint sets of `L − 2`. -/
theorem card_cell_eq (P : H.Cell) :
    Fintype.card H.Cell = 2 + (H.through P).card * (L - 2) := by
  set S : Finset H.Cell := {P, H.opp P} with hS
  have hSc : S.card = 2 := card_pair (H.opp_ne P).symm
  have hmemS : ∀ y, y ∈ S ↔ y = P ∨ y = H.opp P := by
    intro y; simp [hS]
  have hcover : (univ : Finset H.Cell) = S ∪ (H.through P).biUnion (fun l => H.cells l \ S) := by
    ext y
    simp only [mem_univ, true_iff, mem_union, mem_biUnion, mem_sdiff, mem_through]
    by_cases hy : y ∈ S
    · exact Or.inl hy
    · right
      rw [hmemS] at hy
      push Not at hy
      obtain ⟨l, hPl, hyl⟩ := H.exists_loop P y hy.1 hy.2
      refine ⟨l, hPl, hyl, ?_⟩
      rw [hmemS]; push Not; exact hy
  have hdisj : Disjoint S ((H.through P).biUnion (fun l => H.cells l \ S)) := by
    rw [disjoint_biUnion_right]
    intro l _
    exact disjoint_sdiff
  have hpair : ((H.through P : Finset H.Loop) : Set H.Loop).PairwiseDisjoint
      (fun l => H.cells l \ S) := by
    intro l₁ hl₁ l₂ hl₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy₁ hy₂
    rw [mem_sdiff] at hy₁ hy₂
    have hy := hy₁.2
    rw [hmemS] at hy
    push Not at hy
    exact hne (H.unique_loop P y l₁ l₂ hy.1 hy.2 ((H.mem_through).1 (mem_coe.1 hl₁)) hy₁.1
      ((H.mem_through).1 (mem_coe.1 hl₂)) hy₂.1)
  have hcard : ∀ l ∈ H.through P, (H.cells l \ S).card = L - 2 := by
    intro l hl
    rw [card_sdiff_of_subset, H.card_cells, hSc]
    intro y hy
    rw [hmemS] at hy
    rcases hy with rfl | rfl
    · exact (H.mem_through).1 hl
    · exact H.opp_mem _ _ ((H.mem_through).1 hl)
  rw [← card_univ, hcover, card_union_of_disjoint hdisj, hSc, card_biUnion hpair,
    sum_congr rfl hcard, sum_const, smul_eq_mul]

/-- `C = 2R`: counting incidences (cell, ring through it) in both orders. -/
theorem card_cell_eq_two_mul_card_loop (hL : 4 ≤ L) :
    Fintype.card H.Cell = 2 * Fintype.card H.Loop := by
  have key : ∑ l : H.Loop, (H.cells l).card = ∑ x : H.Cell, (H.through x).card := by
    have h1 : ∀ l : H.Loop,
        (H.cells l).card = ∑ x : H.Cell, if x ∈ H.cells l then 1 else 0 := by
      intro l
      rw [← card_filter, filter_mem_eq_inter, univ_inter]
    have h2 : ∀ x : H.Cell,
        (H.through x).card = ∑ l : H.Loop, if x ∈ H.cells l then 1 else 0 := by
      intro x
      rw [through, card_filter]
    simp only [h1, h2]
    exact sum_comm
  have hR : ∑ l : H.Loop, (H.cells l).card = Fintype.card H.Loop * L := by
    simp only [H.card_cells, sum_const, card_univ, smul_eq_mul]
  have hC : 2 * ∑ x : H.Cell, (H.through x).card = Fintype.card H.Cell * L := by
    rw [mul_sum]
    simp only [H.two_mul_card_through hL, sum_const, card_univ, smul_eq_mul]
  have hLpos : 0 < L := by omega
  have : 2 * Fintype.card H.Loop * L = Fintype.card H.Cell * L := by
    rw [mul_assoc, ← hR, key, hC]
  exact (Nat.eq_of_mul_eq_mul_right hLpos this).symm

/-- A cell exists (a largest ring has `L ≥ 4` cells). -/
lemma exists_cell (hL : 4 ≤ L) : Nonempty H.Cell := by
  obtain ⟨l, -, -⟩ := H.two_loops
  have : (H.cells l).Nonempty := by
    rw [← card_pos, H.card_cells]; omega
  obtain ⟨P, -⟩ := this
  exact ⟨P⟩

/-- **Eq. (counts) of the paper.**  With `ρ = L/2` rings through every cell,
`2C = L² − 2L + 4` (that is, `C = L²/2 − L + 2` cells), `4R = L² − 2L + 4` (that is,
`R = L²/4 − L/2 + 1` largest rings), and `C = 2R`. -/
theorem counts (hL : 4 ≤ L) :
    (∀ P : H.Cell, 2 * (H.through P).card = L) ∧
    2 * Fintype.card H.Cell + 2 * L = L ^ 2 + 4 ∧
    4 * Fintype.card H.Loop + 2 * L = L ^ 2 + 4 ∧
    Fintype.card H.Cell = 2 * Fintype.card H.Loop := by
  obtain ⟨P⟩ := H.exists_cell hL
  have hρ := H.two_mul_card_through hL P
  have hC := H.card_cell_eq P
  have hCR := H.card_cell_eq_two_mul_card_loop hL
  have h2 : 2 ≤ L := by omega
  refine ⟨H.two_mul_card_through hL, ?_, ?_, hCR⟩
  · zify [h2] at hρ hC ⊢
    linear_combination 2 * hC + ((L : ℤ) - 2) * hρ
  · zify [h2] at hρ hC hCR ⊢
    linear_combination 2 * hC + ((L : ℤ) - 2) * hρ - 2 * hCR

include H in
/-- `L` is even: a consequence, not an assumption. -/
theorem even_L (hL : 4 ≤ L) : Even L := by
  obtain ⟨P⟩ := H.exists_cell hL
  exact ⟨(H.through P).card, by have := H.two_mul_card_through hL P; omega⟩

end Horizon
