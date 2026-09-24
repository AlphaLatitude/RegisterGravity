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

Formal counterpart of Sec. II, "The count", of *Gravitation from Hilbert-Space Granularity*
(paper v11), Eq. (counts):

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
* Postulate 1, the joint reading: the qubits of two largest rings can be read jointly at one cell,
  so any two largest rings share a cell (`loops_meet`).
* Every largest ring has `L` cells (`card_cells`), and the horizon is not a single ring
  (`two_loops`).

The theorems below need `4 ≤ L` (a largest ring has at least two opposite pairs).  Nothing else is
assumed: no metric, no area, no Bekenstein–Hawking.
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
  /-- Postulate 1, joint reading: any two largest rings share a cell -/
  loops_meet : ∀ l₁ l₂, ∃ x, x ∈ cells l₁ ∧ x ∈ cells l₂
  /-- the horizon is a sphere of rings and not a single ring -/
  two_loops : ∃ l₁ l₂ : Loop, l₁ ≠ l₂

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

/-- A largest ring that does not pass through a given cell. -/
lemma exists_loop_not_mem (hL : 4 ≤ L) (P : H.Cell) : ∃ E : H.Loop, P ∉ H.cells E := by
  obtain ⟨l₁, l₂, hne⟩ := H.two_loops
  by_cases h₁ : P ∈ H.cells l₁
  · by_cases h₂ : P ∈ H.cells l₂
    · -- `P` lies in the pair the two rings share; build a third ring avoiding it
      obtain ⟨x, hx⟩ := H.inter_eq_pair hne
      have hpair : H.cells l₁ ∩ H.cells l₂ = {P, H.opp P} := by
        have hP : P ∈ ({x, H.opp x} : Finset H.Cell) := by
          rw [← hx]; exact mem_inter.2 ⟨h₁, h₂⟩
        rw [hx]
        simp only [mem_insert, mem_singleton] at hP
        rcases hP with rfl | rfl
        · rfl
        · ext z; simp only [mem_insert, mem_singleton, H.opp_opp]; tauto
      obtain ⟨y, hy₁, hyP, hyP'⟩ := H.exists_mem_notMem_pair hL l₁ P (H.opp P)
      obtain ⟨z, hz₂, hzP, hzP'⟩ := H.exists_mem_notMem_pair hL l₂ P (H.opp P)
      have hy₂ : y ∉ H.cells l₂ := by
        intro hy₂
        have : y ∈ H.cells l₁ ∩ H.cells l₂ := mem_inter.2 ⟨hy₁, hy₂⟩
        rw [hpair] at this
        simp only [mem_insert, mem_singleton] at this
        tauto
      have hz₁ : z ∉ H.cells l₁ := by
        intro hz₁
        have : z ∈ H.cells l₁ ∩ H.cells l₂ := mem_inter.2 ⟨hz₁, hz₂⟩
        rw [hpair] at this
        simp only [mem_insert, mem_singleton] at this
        tauto
      have hzy : z ≠ y := fun h => hz₁ (h ▸ hy₁)
      have hzy' : z ≠ H.opp y := fun h => hz₁ (h ▸ H.opp_mem _ _ hy₁)
      obtain ⟨E, hyE, hzE⟩ := H.exists_loop y z hzy hzy'
      refine ⟨E, fun hPE => ?_⟩
      have hPy : P ≠ H.opp y := H.ne_opp_symm hyP'
      have hE : E = l₁ := H.unique_loop y P E l₁ (Ne.symm hyP) hPy hyE hPE hy₁ h₁
      exact hz₁ (hE ▸ hzE)
    · exact ⟨l₂, h₂⟩
  · exact ⟨l₁, h₁⟩

/-- `ρ = L/2`: twice the number of largest rings through any cell is `L`. -/
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
