import RegisterGravity.Capacity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The pairing of strings measured jointly (Sec. IV.A)

Formal counterpart of the sentences of Sec. IV.A on what the register holds for a state of
several qubits, and of the overlap bound above the ceiling.

A joint measurement is one measurement, so its possible outcomes are the positions, the same on
every string of the qubits it measures, and the outcome at a position is the bits there
(Postulate 1, Sec. IV.A).  A *pairing* is a function `e` from the positions, the cells of the type
`Cell`, to the joint outcomes: `e x` is the joint outcome at the position `x`.  Each position is
one possible outcome among the ring's (`Sources.P1.ring_bits_alike`), and the probability of a set
of outcomes is the sum of theirs, so the probability of a joint outcome is the share of the
positions that show it, `freq e k` (`Main.joint_frequency` states this from the premise).  What
follows is counting.  The number of the positions is the number of the ring's cells, written `L`
in the comments: it is `L` on a largest ring, and a result of `Main.lean` that needs the bound
takes it as a premise.

* `freq_multiple`: every joint frequency that a pairing shows is a multiple of `1/L`.
* `shown_le_cells`: "no pairing of `L` positions shows more than `L` joint outcomes".
* `sum_freq`: the frequencies of a pairing sum to one.
* `shown_exactly_iff`: a pairing shows every joint outcome with its probability exactly when
  every probability is a multiple of `1/L` and the multiples sum to `L`.
* `jointPhase`, `state_of_strings`: "Where a pairing shows every joint outcome with its frequency,
  the strings in that pairing, with their blocks' phases, are the state".  A state whose
  probabilities are the frequencies of `N` strings read in step is, up to its global phase, those
  frequencies with one phase on each block of each string.
* `pairing_misses`: where more than `L` joint outcomes occur, every pairing gives one of them the
  frequency zero, so the pairing is approximate ("even where the joint outcomes of its physical
  qubits outnumber `L`").
* `product_multiple_iff`, `product_not_shown`: "two qubits prepared apart, with the fractions
  `m₁/L` and `m₂/L`, have the joint frequency `m₁m₂/L²` for the outcome `(1,1)`, a multiple of
  `1/L` only when `L` divides `m₁m₂`".
* `most_products_not_shown`: "Most product states are not held exactly": for a first qubit in a
  superposition, the fractions of a second one for which `L` does not divide `m₁m₂` outnumber
  those for which it does.
* `pairing_within_one_cell`: two strings, each fixed, have a pairing that shows the outcome
  `(1,1)` within one cell of the product of their fractions, `1/L` in frequency, and exactly
  where `L` divides `m₁m₂` ("held with its strings exact and its pairing approximate").  A
  pairing of two strings is a one-to-one map `π` of the positions: the cell `x` of the first is
  read with the cell `π x` of the second.  Each string is a fixed set of cells, so it keeps its
  bits where they are, its fraction and its cyclic position, in every pairing; the map `π` alone
  varies.
* `pairing_not_fixed`: the strings do not fix the pairing: two strings, each in a superposition,
  have two pairings that show the outcome `(1,1)` at different numbers of positions ("the
  postulates do not say which pairing").
* `strings_in_step`: `N` strings read in step show joint frequencies that are multiples of `1/L`
  and sum to one, and the frequency of `1` on each string is that string's own fraction, in every
  pairing ("`N` exact strings read in step, in some pairing, with a phase on each block").  Here
  `bits i x` is the bit that the string `i` shows at the position `x` of the pairing: the string
  as the pairing reads it.
* `blockOf`, `freq_chain`: "the probability of a joint outcome is the product, string by string,
  of the frequencies of its bits on its blocks".
* `BlockPhase`, `block_resolution`: a block of `r` cells holds a conditional probability that
  is a multiple of `1/r` and a phase that is one of `r` cyclic positions (Secs. IV.A and V).
* `sample_outcomes_le`: a sample of `n` shots shows at most `n` outcomes.
* `overlap_le`: a state that gives the outcomes outside a set the probability zero overlaps
  another state by at most the probability that the other gives the outcomes of the set
  (Sec. IV.A: "its overlap with the random state is at most the probability that the random state
  gives the outcomes that remain").  `Main.overlap_bound` states it for what the register holds.

As in `Capacity.lean`, the bit `true` is the outcome `1` and `false` the outcome `−1`, and a string
is given by its bits, or by the set of its cells that read `1`.
-/

open Finset

namespace Register
namespace Pairing

variable {Cell : Type*} [Fintype Cell]

/-- **The frequency of a joint outcome in a pairing** (Sec. IV.A): the share of the positions `x`
at which the pairing `e` shows the joint outcome `k`, their number over the number `L` of the
positions. -/
noncomputable def freq {K : Type*} [DecidableEq K] (e : Cell → K) (k : K) : ℝ :=
  ((univ.filter (fun x => e x = k)).card : ℝ) / Fintype.card Cell

/-- **Every joint frequency is a multiple of `1/L`** (Sec. IV.A): a pairing of `L` positions shows
a joint outcome at `n` of them, with `n ≤ L`, so with the frequency `n/L`. -/
theorem freq_multiple {K : Type*} [DecidableEq K] (e : Cell → K) (k : K) :
    ∃ n : ℕ, n ≤ Fintype.card Cell ∧ freq e k = n / Fintype.card Cell :=
  ⟨_, card_le_univ _, rfl⟩

lemma freq_nonneg {K : Type*} [DecidableEq K] (e : Cell → K) (k : K) : 0 ≤ freq e k := by
  unfold freq
  positivity

/-- **No pairing of `L` positions shows more than `L` joint outcomes** (Sec. IV.A, in these
words): the joint outcomes with a frequency above zero are at most as many as the positions. -/
theorem shown_le_cells {K : Type*} [DecidableEq K] [Fintype K] (e : Cell → K) :
    (univ.filter (fun k => 0 < freq e k)).card ≤ Fintype.card Cell := by
  classical
  have hsub : univ.filter (fun k => 0 < freq e k) ⊆ (univ : Finset Cell).image e := by
    intro k hk
    rw [mem_filter] at hk
    have hpos : (0 : ℝ) < ((univ.filter (fun x => e x = k)).card : ℝ) := by
      by_contra h
      have h0 : ((univ.filter (fun x => e x = k)).card : ℝ) = 0 :=
        le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
      have : freq e k = 0 := by unfold freq; rw [h0, zero_div]
      exact absurd hk.2 (by rw [this]; exact lt_irrefl _)
    have hpos' : 0 < (univ.filter (fun x => e x = k)).card := by exact_mod_cast hpos
    obtain ⟨x, hx⟩ := card_pos.1 hpos'
    exact mem_image.2 ⟨x, mem_univ x, (mem_filter.1 hx).2⟩
  calc (univ.filter (fun k => 0 < freq e k)).card ≤ ((univ : Finset Cell).image e).card :=
        card_le_card hsub
    _ ≤ (univ : Finset Cell).card := card_image_le
    _ = Fintype.card Cell := card_univ

/-- the positions, counted by the joint outcome that each shows, are `L` in all -/
lemma sum_card_fibers {K : Type*} [DecidableEq K] [Fintype K] (e : Cell → K) :
    ∑ k, (univ.filter (fun x => e x = k)).card = Fintype.card Cell := by
  rw [← card_univ (α := Cell)]
  exact (card_eq_sum_card_fiberwise (f := e) (s := univ) (t := univ) (fun x _ => mem_univ _)).symm

/-- **The frequencies of a pairing sum to one**: every position shows one joint outcome. -/
theorem sum_freq {K : Type*} [DecidableEq K] [Fintype K] (e : Cell → K)
    (hL : 0 < Fintype.card Cell) : ∑ k, freq e k = 1 := by
  unfold freq
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_card_fibers e]
  exact div_self (by exact_mod_cast hL.ne')

/-- **Which states a pairing shows exactly** (Sec. IV.A: "Where a pairing shows every joint
outcome with its frequency").  Some pairing of the `L` positions shows every joint outcome `k`
with the probability `p k` exactly when every `p k` is a multiple `n k / L` of `1/L` and the
multiples sum to `L`.  The statement is of the frequencies; `state_of_strings` adds the blocks'
phases. -/
theorem shown_exactly_iff {K : Type*} [DecidableEq K] [Fintype K] (p : K → ℝ) :
    (∃ e : Cell → K, ∀ k, freq e k = p k) ↔
      ∃ n : K → ℕ, (∀ k, p k = n k / Fintype.card Cell) ∧ ∑ k, n k = Fintype.card Cell := by
  classical
  constructor
  · rintro ⟨e, he⟩
    exact ⟨fun k => (univ.filter (fun x => e x = k)).card, fun k => (he k).symm, sum_card_fibers e⟩
  · rintro ⟨n, hn, hsum⟩
    have hcard : Fintype.card (Σ k, Fin (n k)) = Fintype.card Cell := by
      rw [Fintype.card_sigma]
      simpa using hsum
    let φ : (Σ k, Fin (n k)) ≃ Cell := Fintype.equivOfCardEq hcard
    refine ⟨fun x => (φ.symm x).1, fun k => ?_⟩
    have hfib : (univ.filter (fun x => (φ.symm x).1 = k)).card = n k := by
      have h1 : univ.filter (fun x => (φ.symm x).1 = k) =
          (univ : Finset (Fin (n k))).image (fun i => φ ⟨k, i⟩) := by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_image]
        constructor
        · intro hx
          rcases hs : φ.symm x with ⟨k', i⟩
          rw [hs] at hx
          subst hx
          exact ⟨i, by rw [← hs, Equiv.apply_symm_apply]⟩
        · rintro ⟨i, rfl⟩
          rw [Equiv.symm_apply_apply]
      rw [h1, card_image_of_injective _ (fun i j hij => by
        have := φ.injective hij
        simpa using this), card_univ, Fintype.card_fin]
    unfold freq
    rw [hfib, hn k]

/-- **A state with more than `L` joint outcomes is not shown exactly** (Sec. IV.A: the encoded
state "is held with its strings exact and its pairing approximate, as a product state is, even
where the joint outcomes of its physical qubits outnumber `L`").  Where more than `L` joint
outcomes occur, with `p k > 0`, every pairing of the `L` positions gives one of them the frequency
zero. -/
theorem pairing_misses {K : Type*} [DecidableEq K] [Fintype K] (p : K → ℝ)
    (hmore : Fintype.card Cell < (univ.filter (fun k => 0 < p k)).card) (e : Cell → K) :
    ∃ k, 0 < p k ∧ freq e k = 0 := by
  by_contra hno
  push Not at hno
  have hsub : univ.filter (fun k => 0 < p k) ⊆ univ.filter (fun k => 0 < freq e k) := by
    intro k hk
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_le_of_ne (freq_nonneg e k) (Ne.symm (hno k hk.2))⟩
  exact absurd ((card_le_card hsub).trans (shown_le_cells e)) (not_le.2 hmore)

/-- **The product of two fractions is a multiple of `1/L` only when `L` divides `m₁m₂`**
(Sec. IV.A): `(m₁/L)(m₂/L) = n/L` for a whole number `n` exactly when `L` divides `m₁m₂`. -/
theorem product_multiple_iff (L m₁ m₂ : ℕ) (hL : 0 < L) :
    (∃ n : ℕ, ((m₁ : ℝ) / L) * (m₂ / L) = n / L) ↔ L ∣ m₁ * m₂ := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h1 : (m₁ : ℝ) / L * (m₂ / L) = (m₁ * m₂) / (L * L) := by ring
  have h2 : ∀ n : ℕ, (n : ℝ) / L = (n * L) / (L * L) := fun n => by field_simp
  constructor
  · rintro ⟨n, hn⟩
    rw [h1, h2 n, div_left_inj' (mul_ne_zero hL' hL')] at hn
    have hnat : m₁ * m₂ = n * L := by exact_mod_cast hn
    exact ⟨n, by rw [hnat, mul_comm]⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [h1, h2 n, div_left_inj' (mul_ne_zero hL' hL')]
    have hnat : m₁ * m₂ = n * L := by rw [hn, mul_comm]
    exact_mod_cast hnat

/-- **Two qubits prepared apart** (Sec. IV.A: "two qubits prepared apart, with the fractions
`m₁/L` and `m₂/L`, have the joint frequency `m₁m₂/L²` for the outcome `(1,1)`, a multiple of
`1/L` only when `L` divides `m₁m₂`").  `A` and `B` are the cells where the two strings read `1`,
and in the pairing `π` the cell `x` of the first string is read with the cell `π x` of the second,
so the positions that show the outcome `(1,1)` are the cells `x` of `A` with `π x` in `B`.  If
their share is the product of the strings' fractions, then `L` divides `m₁m₂`. -/
theorem product_not_shown [DecidableEq Cell] (A B : Finset Cell) (π : Equiv.Perm Cell)
    (hL : 0 < Fintype.card Cell)
    (hprod : ((A.filter (fun x => π x ∈ B)).card : ℝ) / Fintype.card Cell
      = ((A.card : ℝ) / Fintype.card Cell) * (B.card / Fintype.card Cell)) :
    Fintype.card Cell ∣ A.card * B.card :=
  (product_multiple_iff _ _ _ hL).1 ⟨(A.filter (fun x => π x ∈ B)).card, hprod.symm⟩

/-- **Most product states are not held exactly** (Sec. IV.A, in these words).  For a first qubit
in a superposition, `0 < m₁ < L`, the fractions `m₂/L` of a second one, `0 < m₂ < L`, for which
`L` does not divide `m₁m₂` outnumber those for which it does: if `L` divides `m₁m₂` it does not
divide `m₁(m₂ + 1)`. -/
theorem most_products_not_shown (L m₁ : ℕ) (h0 : 0 < m₁) (h1 : m₁ < L) :
    ((Ioo 0 L).filter (fun m₂ => L ∣ m₁ * m₂)).card <
      ((Ioo 0 L).filter (fun m₂ => ¬ L ∣ m₁ * m₂)).card := by
  have hnd : ¬ L ∣ m₁ := fun h => absurd (Nat.le_of_dvd h0 h) (not_le.2 h1)
  have hinj : Set.InjOn (fun m : ℕ => m + 1)
      (((Ioo 0 L).filter (fun m₂ => L ∣ m₁ * m₂) : Finset ℕ) : Set ℕ) :=
    fun a _ b _ h => Nat.succ_injective h
  have hsub : ((Ioo 0 L).filter (fun m₂ => L ∣ m₁ * m₂)).image (fun m : ℕ => m + 1) ⊂
      (Ioo 0 L).filter (fun m₂ => ¬ L ∣ m₁ * m₂) := by
    rw [ssubset_iff_of_subset]
    · refine ⟨1, ?_, ?_⟩
      · rw [mem_filter, mem_Ioo]
        exact ⟨⟨Nat.one_pos, by omega⟩, by simpa using hnd⟩
      · intro h
        obtain ⟨m, hm, hm1⟩ := mem_image.1 h
        rw [mem_filter, mem_Ioo] at hm
        omega
    · intro y hy
      obtain ⟨m, hm, rfl⟩ := mem_image.1 hy
      rw [mem_filter, mem_Ioo] at hm
      obtain ⟨⟨hm0, hmL⟩, hdvd⟩ := hm
      have hnd' : ¬ L ∣ m₁ * (m + 1) := by
        intro h
        apply hnd
        have hexp : m₁ * (m + 1) = m₁ * m + m₁ := by ring
        rw [hexp] at h
        exact (Nat.dvd_add_right hdvd).1 h
      rw [mem_filter, mem_Ioo]
      refine ⟨⟨Nat.succ_pos m, ?_⟩, hnd'⟩
      rcases Nat.lt_or_ge (m + 1) L with h | h
      · exact h
      · exfalso
        have hm : m + 1 = L := by omega
        exact hnd' (by rw [hm]; exact Nat.dvd_mul_left L m₁)
  calc ((Ioo 0 L).filter (fun m₂ => L ∣ m₁ * m₂)).card
      = (((Ioo 0 L).filter (fun m₂ => L ∣ m₁ * m₂)).image (fun m : ℕ => m + 1)).card :=
        (card_image_of_injOn hinj).symm
    _ < ((Ioo 0 L).filter (fun m₂ => ¬ L ∣ m₁ * m₂)).card := card_lt_card hsub

/-- a string read through a pairing keeps its fraction: the positions `x` whose partner `π x`
reads `1` are as many as the cells of the second string that read `1` -/
lemma card_paired [DecidableEq Cell] (B : Finset Cell) (π : Equiv.Perm Cell) :
    (univ.filter (fun x => π x ∈ B)).card = B.card := by
  have h : univ.filter (fun x => π x ∈ B) = B.image π.symm := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      exact ⟨π x, hx, π.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [π.apply_symm_apply]
  rw [h, card_image_of_injective _ π.symm.injective]

/-- two strings, each with its cells that read `1` fixed, can be paired so that any number `k` of
positions between `m₁ + m₂ − L` and the smaller of `m₁` and `m₂` shows the outcome `(1,1)` -/
lemma exists_pairing_with_count [DecidableEq Cell] (A B : Finset Cell) (k : ℕ)
    (hk₁ : k ≤ A.card) (hk₂ : k ≤ B.card) (hk : A.card + B.card ≤ Fintype.card Cell + k) :
    ∃ π : Equiv.Perm Cell, (A.filter (fun x => π x ∈ B)).card = k := by
  obtain ⟨C, hCA, hC⟩ := exists_subset_card_eq (s := A) (n := k) hk₁
  have hcompl : B.card - k ≤ (univ \ A).card := by
    rw [card_sdiff_of_subset (subset_univ A), card_univ]
    omega
  obtain ⟨D, hDA, hD⟩ := exists_subset_card_eq (s := univ \ A) (n := B.card - k) hcompl
  have hdisj : Disjoint C D := by
    rw [disjoint_left]
    intro x hxC hxD
    exact (mem_sdiff.1 (hDA hxD)).2 (hCA hxC)
  have hcard : (C ∪ D).card = B.card := by
    rw [card_union_of_disjoint hdisj, hC, hD]
    omega
  -- a one-to-one map of the positions that carries `C ∪ D` onto `B`
  let e : {x // x ∈ C ∪ D} ≃ {x // x ∈ B} := Finset.equivOfCardEq hcard
  refine ⟨e.extendSubtype, ?_⟩
  have hmem : ∀ x, e.extendSubtype x ∈ B ↔ x ∈ C ∪ D := by
    intro x
    constructor
    · intro hx
      by_contra hno
      exact e.extendSubtype_not_mem x hno hx
    · intro hx
      exact e.extendSubtype_mem x hx
  have hint : A.filter (fun x => e.extendSubtype x ∈ B) = C := by
    ext x
    simp only [mem_filter, hmem, mem_union]
    constructor
    · rintro ⟨hxA, hxC | hxD⟩
      · exact hxC
      · exact absurd hxA (mem_sdiff.1 (hDA hxD)).2
    · intro hxC
      exact ⟨hCA hxC, Or.inl hxC⟩
  rw [hint, hC]

/-- **Strings exact, pairing approximate** (Sec. IV.A: "Postulate 1 fixes each string exactly, its
fraction and position, and the pairing only up to its `L` positions; such a state is held with
its strings exact and its pairing approximate").  `A` and `B` are the cells where two strings read
`1`, each string fixed, with the fractions `m₁/L` and `m₂/L`.  There is a pairing `π` of their
positions in which the positions that show the outcome `(1,1)` number `m₁m₂/L` rounded down.
Their share lies within `1/L`, one cell, of the product of the fractions, and it is the product
where `L` divides `m₁m₂`. -/
theorem pairing_within_one_cell [DecidableEq Cell] (A B : Finset Cell)
    (hL : 0 < Fintype.card Cell) :
    ∃ π : Equiv.Perm Cell,
      |((A.filter (fun x => π x ∈ B)).card : ℝ) / Fintype.card Cell
        - ((A.card : ℝ) / Fintype.card Cell) * (B.card / Fintype.card Cell)|
          < 1 / Fintype.card Cell ∧
      (Fintype.card Cell ∣ A.card * B.card →
        ((A.filter (fun x => π x ∈ B)).card : ℝ) / Fintype.card Cell
          = ((A.card : ℝ) / Fintype.card Cell) * (B.card / Fintype.card Cell)) := by
  obtain ⟨L, hLdef⟩ : ∃ L, L = Fintype.card Cell := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = A.card := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂, m₂ = B.card := ⟨_, rfl⟩
  have h₁ : m₁ ≤ L := by rw [hm₁, hLdef]; exact card_le_univ A
  have h₂ : m₂ ≤ L := by rw [hm₂, hLdef]; exact card_le_univ B
  have hL' : 0 < L := by rw [hLdef]; exact hL
  have hdm := Nat.div_add_mod (m₁ * m₂) L
  have hmod : m₁ * m₂ % L < L := Nat.mod_lt _ hL'
  have hk₁ : m₁ * m₂ / L ≤ m₁ := by
    apply Nat.div_le_of_le_mul
    calc m₁ * m₂ ≤ m₁ * L := Nat.mul_le_mul_left _ h₂
      _ = L * m₁ := Nat.mul_comm _ _
  have hk₂ : m₁ * m₂ / L ≤ m₂ := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right _ h₁
  have hk : m₁ + m₂ ≤ L + m₁ * m₂ / L := by
    -- `(L − m₁)(L − m₂) ≥ 0`
    have h3 : L * (m₁ + m₂) ≤ L * L + m₁ * m₂ := by
      have hz : (0 : ℤ) ≤ ((L : ℤ) - m₁) * ((L : ℤ) - m₂) :=
        mul_nonneg (sub_nonneg.2 (by exact_mod_cast h₁)) (sub_nonneg.2 (by exact_mod_cast h₂))
      have hz' : (L : ℤ) * (m₁ + m₂) ≤ L * L + m₁ * m₂ := by nlinarith
      exact_mod_cast hz'
    by_contra hcon
    push Not at hcon
    have h4 : L * (L + m₁ * m₂ / L + 1) ≤ L * (m₁ + m₂) := Nat.mul_le_mul_left _ hcon
    nlinarith [hdm, hmod]
  obtain ⟨π, hπ⟩ := exists_pairing_with_count A B (m₁ * m₂ / L)
    (by rw [← hm₁]; exact hk₁) (by rw [← hm₂]; exact hk₂) (by rw [← hm₁, ← hm₂, ← hLdef]; exact hk)
  refine ⟨π, ?_, ?_⟩
  · rw [hπ, ← hm₁, ← hm₂, ← hLdef]
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL'
    have hcast : ((m₁ : ℝ) * m₂) = L * ((m₁ * m₂ / L : ℕ) : ℝ) + ((m₁ * m₂ % L : ℕ) : ℝ) := by
      exact_mod_cast hdm.symm
    have hmodr : ((m₁ * m₂ % L : ℕ) : ℝ) < L := by exact_mod_cast hmod
    have hmod0 : (0 : ℝ) ≤ ((m₁ * m₂ % L : ℕ) : ℝ) := Nat.cast_nonneg _
    have heq : ((m₁ * m₂ / L : ℕ) : ℝ) / L - (m₁ : ℝ) / L * (m₂ / L)
        = - (((m₁ * m₂ % L : ℕ) : ℝ) / (L * L)) := by
      have : (m₁ : ℝ) / L * (m₂ / L) = ((m₁ : ℝ) * m₂) / (L * L) := by ring
      rw [this, hcast]
      field_simp
      ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg hmod0 (mul_pos hLr hLr).le)]
    rw [div_lt_div_iff₀ (mul_pos hLr hLr) hLr]
    nlinarith [mul_pos hLr hLr]
  · intro hdvd
    rw [← hm₁, ← hm₂, ← hLdef] at hdvd
    rw [hπ, ← hm₁, ← hm₂, ← hLdef]
    have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL'.ne'
    have hex : m₁ * m₂ = L * (m₁ * m₂ / L) := (Nat.mul_div_cancel' hdvd).symm
    have hcast : ((m₁ : ℝ) * m₂) = L * ((m₁ * m₂ / L : ℕ) : ℝ) := by exact_mod_cast hex
    have : (m₁ : ℝ) / L * (m₂ / L) = ((m₁ : ℝ) * m₂) / (L * L) := by ring
    rw [this, hcast]
    field_simp

/-- **The strings do not fix the pairing** (Sec. IV.A: "Postulate 1 fixes each string exactly,
its fraction and position, and the pairing only up to its `L` positions", and "the postulates do
not say which pairing").  Two strings, each in a superposition, `0 < m₁, m₂ < L`, are the fixed
sets `A` and `B` of the cells where they read `1`: each keeps its bits where they are, so its
fraction and its cyclic position.  They have two pairings that show the outcome `(1,1)` at
different numbers of positions. -/
theorem pairing_not_fixed [DecidableEq Cell] (A B : Finset Cell) (hA0 : 0 < A.card)
    (hB0 : 0 < B.card) (hA : A.card < Fintype.card Cell) (hB : B.card < Fintype.card Cell) :
    ∃ π π' : Equiv.Perm Cell,
      (A.filter (fun x => π x ∈ B)).card ≠ (A.filter (fun x => π' x ∈ B)).card := by
  obtain ⟨π, hπ⟩ := exists_pairing_with_count A B (min A.card B.card)
    (min_le_left _ _) (min_le_right _ _) (by omega)
  obtain ⟨π', hπ'⟩ := exists_pairing_with_count A B (min A.card B.card - 1)
    (by omega) (by omega) (by omega)
  refine ⟨π, π', ?_⟩
  rw [hπ, hπ']
  omega

/-- **The pairing of `N` strings read in step** (Sec. IV.A): at each position, the bits of the
`N` strings there (`Capacity.jointOutcome` is the same for the earlier strings alone).  `bits i x`
is the bit that the string `i` shows at the position `x` of the pairing, the string as the
pairing reads it; with two strings and the pairing `π` of `pairing_within_one_cell`, it is the
bit of the second string at its cell `π x`. -/
def inStep {N : ℕ} (bits : Fin N → Cell → Bool) (x : Cell) : Fin N → Bool := fun i => bits i x

/-- **`N` exact strings read in step** (Sec. IV.A: "The register therefore holds, at any `N`,
something definite in kind: `N` exact strings read in step, in some pairing, with a phase on each
block").  Whatever the bits of the `N` strings, the pairing that they make shows every joint
outcome with a frequency that is a multiple of `1/L`, the frequencies sum to one, and the
frequency of the outcome `1` on the string `i` is that string's own fraction of 1s, so every
string is exact in every pairing.  The phase on each block is one of the block's cyclic
positions (`BlockPhase`); `state_of_strings` gives the state from the frequencies and the blocks'
phases. -/
theorem strings_in_step {N : ℕ} (bits : Fin N → Cell → Bool) (hL : 0 < Fintype.card Cell) :
    (∀ σ, ∃ n : ℕ, freq (inStep bits) σ = n / Fintype.card Cell) ∧
      ∑ σ, freq (inStep bits) σ = 1 ∧
      ∀ i, ∑ σ ∈ univ.filter (fun σ : Fin N → Bool => σ i = true), freq (inStep bits) σ
        = Capacity.frac (bits i) univ := by
  classical
  refine ⟨fun σ => ?_, sum_freq (inStep bits) hL, fun i => ?_⟩
  · obtain ⟨n, -, hn⟩ := freq_multiple (inStep bits) σ
    exact ⟨n, hn⟩
  · have hfib := card_eq_sum_card_fiberwise (f := inStep bits)
      (s := univ.filter (fun x => bits i x = true))
      (t := univ.filter (fun σ : Fin N → Bool => σ i = true))
      (fun x hx => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2⟩)
    have hsame : ∀ σ ∈ univ.filter (fun σ : Fin N → Bool => σ i = true),
        ((univ.filter (fun x => bits i x = true)).filter (fun x => inStep bits x = σ)).card
          = (univ.filter (fun x => inStep bits x = σ)).card := by
      intro σ hσ
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun hx => hx.2
      · intro hx
        refine ⟨?_, hx⟩
        have := (mem_filter.1 hσ).2
        rw [← hx] at this
        exact this
    rw [sum_congr rfl hsame] at hfib
    unfold freq Capacity.frac
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hfib, card_univ]

/-- **The block of a string for a joint outcome of the earlier strings** (Sec. IV.A: "The cells of
a later string whose bits are paired with one joint outcome of the earlier qubits form a block of
the string").  The positions at which the first `i` strings show the bits of `σ`: the block of
the string `i` that is paired with the joint outcome of the earlier strings in `σ`. -/
def blockOf {N : ℕ} (bits : Fin N → Cell → Bool) (σ : Fin N → Bool) (i : ℕ) : Finset Cell :=
  univ.filter (fun x => ∀ j : Fin N, j.val < i → bits j x = σ j)

/-- the next block is the part of a block on which the block's own string reads its bit of `σ` -/
lemma blockOf_succ {N : ℕ} (bits : Fin N → Cell → Bool) (σ : Fin N → Bool) (i : Fin N) :
    blockOf bits σ (i.val + 1) = (blockOf bits σ i.val).filter (fun x => bits i x = σ i) := by
  ext x
  simp only [blockOf, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h i (Nat.lt_succ_self _)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact h1 j h
    · have hji : j = i := Fin.ext h
      rw [hji]
      exact h2

/-- **The probability of a joint outcome is the product of the frequencies of its bits on its
blocks** (Sec. IV.A: "the probability of a joint outcome is the product, string by string, of the
frequencies of its bits on its blocks").  For a joint outcome `σ` that some position shows, its
frequency in the pairing of `N` strings read in step is the product, over the strings `i`, of
the frequency of the bit `σ i` on the block of the string `i`: the share of the block's cells at
which the string reads that bit.  Those cells are the next string's block (`blockOf_succ`), so
the product telescopes. -/
theorem freq_chain {N : ℕ} (bits : Fin N → Cell → Bool) (σ : Fin N → Bool)
    (hσ : 0 < freq (inStep bits) σ) :
    freq (inStep bits) σ
      = ∏ i : Fin N, (((blockOf bits σ i.val).filter (fun x => bits i x = σ i)).card : ℝ)
          / (blockOf bits σ i.val).card := by
  classical
  -- the first block is all the cells, and the last the positions that show `σ`
  have h0 : blockOf bits σ 0 = univ := by
    ext x
    simp [blockOf]
  have hN : blockOf bits σ N = univ.filter (fun x => inStep bits x = σ) := by
    ext x
    simp only [blockOf, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      funext j
      exact h j j.isLt
    · intro h j _
      rw [← h]
      rfl
  have hpos : 0 < (univ.filter (fun x => inStep bits x = σ)).card := by
    by_contra hno
    have hz : (univ.filter (fun x => inStep bits x = σ)).card = 0 := Nat.eq_zero_of_not_pos hno
    unfold freq at hσ
    rw [hz] at hσ
    simp at hσ
  -- the blocks nest, so none is empty
  have hmono : ∀ k, 0 < (blockOf bits σ k).card := by
    intro k
    refine lt_of_lt_of_le hpos (card_le_card ?_)
    rw [← hN]
    intro x hx
    simp only [blockOf, mem_filter, mem_univ, true_and] at hx ⊢
    exact fun j _ => hx j j.isLt
  -- the product telescopes
  have htel : ∀ n, ∏ k ∈ range n,
      ((blockOf bits σ (k + 1)).card : ℝ) / (blockOf bits σ k).card
        = ((blockOf bits σ n).card : ℝ) / (blockOf bits σ 0).card := by
    intro n
    have hne0 : ((blockOf bits σ 0).card : ℝ) ≠ 0 := by exact_mod_cast (hmono 0).ne'
    induction n with
    | zero => rw [prod_range_zero, div_self hne0]
    | succ n ih =>
      have hne : ((blockOf bits σ n).card : ℝ) ≠ 0 := by exact_mod_cast (hmono n).ne'
      rw [prod_range_succ, ih]
      field_simp
  have hstep : ∀ i : Fin N,
      (((blockOf bits σ i.val).filter (fun x => bits i x = σ i)).card : ℝ)
          / (blockOf bits σ i.val).card
        = ((blockOf bits σ (i.val + 1)).card : ℝ) / (blockOf bits σ i.val).card := by
    intro i
    rw [blockOf_succ]
  rw [Finset.prod_congr rfl (fun i _ => hstep i),
    Fin.prod_univ_eq_prod_range
      (fun k => ((blockOf bits σ (k + 1)).card : ℝ) / (blockOf bits σ k).card) N,
    htel N, hN, h0, card_univ]
  rfl

/-- **The phases a block can hold** (Sec. IV.A: a later string "has a phase for each joint outcome
of the earlier ones: a cyclic permutation, in a reference arrangement, of its bits paired with
that outcome").  A block of `r` cells has `r` cyclic arrangements of its bits, so its phase is one
of `r` cyclic positions (Postulate 1: "the string's cyclic position on its ring is the qubit's
phase"). -/
abbrev BlockPhase {Cell : Type*} (B : Finset Cell) : Type := Fin B.card

/-- **What a block holds, and how finely** (Sec. IV.A: "A block holds the conditional state of its
joint outcome"; Sec. V: "A block of `r` cells resolves the last qubit's conditional probability
and phase to one part in `r`").  The fraction of 1s on a block of `r` cells, the conditional
probability that the block holds, is a multiple `k/r` of one part in `r`, and the block's phase is
one of `r` cyclic positions. -/
theorem block_resolution {Cell : Type*} (b : Cell → Bool) (B : Finset Cell) :
    (∃ k : ℕ, k ≤ B.card ∧ Capacity.frac b B = k / B.card) ∧
      Fintype.card (BlockPhase B) = B.card :=
  ⟨⟨_, card_filter_le _ _, rfl⟩, Fintype.card_fin _⟩

/-- the reading that agrees with `σ` on the strings before the `i`-th and reads `1` from it on -/
def before {N : ℕ} (i : ℕ) (σ : Fin N → Bool) : Fin N → Bool :=
  fun j => if j.val < i then σ j else true

/-- **The phase of a joint outcome, from the blocks' phases** (Sec. IV.A: "The block's phase
(above) is the later qubit's phase given that outcome").  `φ i τ` is the phase on the block of the
string `i` that is paired with the joint outcome of the earlier strings in `τ`: the phase of the
qubit `i` given that outcome, which its amplitude carries where it reads `−1`.  The phase of the
joint outcome `σ` is the sum of these over the strings that read `−1` in `σ`; the block of the
string `i` is read off the earlier bits of `σ` alone (`before`). -/
noncomputable def jointPhase {N : ℕ} (φ : Fin N → (Fin N → Bool) → ℝ) (σ : Fin N → Bool) : ℝ :=
  ∑ i : Fin N, if σ i then 0 else φ i (before i.val σ)

/-- **The strings in a pairing, with their blocks' phases, are the state** (Sec. IV.A: "Where a
pairing shows every joint outcome with its frequency, the strings in that pairing, with their
blocks' phases, are the state").  `ψ` is a state of `N` qubits, and the `N` strings read in step
show every joint outcome with its frequency: `freq (inStep bits) σ = |ψ_σ|²`.  Then there are a
phase on each block of each string (`φ`) and a global phase `γ`, which is hidden (Postulate 1),
such that the amplitude of every joint outcome is the square root of its frequency times the
phase that the blocks give it (`jointPhase`).  A block of `r` cells holds one of `r` phases
(`block_resolution`); the phases here are real numbers. -/
theorem state_of_strings {N : ℕ} (bits : Fin N → Cell → Bool) (ψ : (Fin N → Bool) → ℂ)
    (h : ∀ σ, freq (inStep bits) σ = ‖ψ σ‖ ^ 2) :
    ∃ (γ : ℝ) (φ : Fin N → (Fin N → Bool) → ℝ), ∀ σ,
      ψ σ = Complex.exp ((γ : ℂ) * Complex.I) *
        ((Real.sqrt (freq (inStep bits) σ) : ℂ) *
          Complex.exp ((jointPhase φ σ : ℂ) * Complex.I)) := by
  classical
  -- the phase of each amplitude
  obtain ⟨θ, hθ⟩ : ∃ θ : (Fin N → Bool) → ℝ, ∀ σ, θ σ = Complex.arg (ψ σ) := ⟨_, fun _ => rfl⟩
  refine ⟨θ (fun _ => true),
    fun i τ => θ (Function.update τ i false) - θ (Function.update τ i true), fun σ => ?_⟩
  -- the blocks' phases sum to the phase of `σ` less that of the outcome that reads `1` throughout
  have hstep : ∀ i : Fin N,
      (if σ i then 0 else θ (Function.update (before i.val σ) i false)
        - θ (Function.update (before i.val σ) i true))
        = θ (before (i.val + 1) σ) - θ (before i.val σ) := by
    intro i
    have htrue : Function.update (before i.val σ) i true = before i.val σ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [before]
      · rw [Function.update_of_ne hj]
    have hnext : before (i.val + 1) σ = Function.update (before i.val σ) i (σ i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [before]
      · rw [Function.update_of_ne hj]
        have hne : j.val ≠ i.val := fun hv => hj (Fin.ext hv)
        unfold before
        by_cases hlt : j.val < i.val
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
    cases hσi : σ i
    · rw [hnext, hσi, htrue]
      simp
    · rw [hnext, hσi, htrue]
      simp
  have hsum : jointPhase (fun i τ => θ (Function.update τ i false)
      - θ (Function.update τ i true)) σ = θ σ - θ (fun _ => true) := by
    unfold jointPhase
    rw [Finset.sum_congr rfl (fun i _ => hstep i),
      Fin.sum_univ_eq_sum_range (fun k => θ (before (k + 1) σ) - θ (before k σ)) N,
      Finset.sum_range_sub (fun k => θ (before k σ)) N]
    have hN : before N σ = σ := by
      funext j
      simp [before, j.isLt]
    have h0 : before 0 σ = fun _ => true := by
      funext j
      simp [before]
    rw [hN, h0]
  rw [hsum, h σ, Real.sqrt_sq (norm_nonneg _), ← mul_assoc, mul_comm (Complex.exp _) _,
    mul_assoc, ← Complex.exp_add]
  have harg : ((θ (fun _ => true) : ℝ) : ℂ) * Complex.I
      + ((θ σ - θ (fun _ => true) : ℝ) : ℂ) * Complex.I = (Complex.arg (ψ σ) : ℂ) * Complex.I := by
    rw [hθ σ]
    push_cast
    ring
  rw [harg, Complex.norm_mul_exp_arg_mul_I]

/-- **A sample of `n` shots shows at most `n` outcomes** (Sec. IV.A: "No sample shows which
outcomes are missing, since a million shots on `205` qubits see at most a million of their
`2^205` outcomes"; `Numerics.shots_fraction` gives the fraction). -/
theorem sample_outcomes_le {K : Type*} [DecidableEq K] (n : ℕ) (s : Fin n → K) :
    (univ.image s).card ≤ n :=
  card_image_le.trans (by rw [card_univ, Fintype.card_fin])

/-- **The overlap bound** (Sec. IV.A: "What the register holds instead gives the missing outcomes
probability zero, so its overlap with the random state is at most the probability that the random
state gives the outcomes that remain").  A state `φ`, with probabilities that sum to at most one,
that vanishes on the outcomes outside a set `S` overlaps any state `ψ` by at most the probability
that `ψ` gives the outcomes of `S`: `|⟨ψ|φ⟩|² ≤ ∑_{k ∈ S} |ψ_k|²`, by the Cauchy–Schwarz
inequality on `S`. -/
theorem overlap_le {K : Type*} [Fintype K] [DecidableEq K] (φ ψ : K → ℂ) (S : Finset K)
    (hφ : ∀ k, k ∉ S → φ k = 0) (hnorm : ∑ k, ‖φ k‖ ^ 2 ≤ 1) :
    ‖∑ k, (starRingEnd ℂ) (ψ k) * φ k‖ ^ 2 ≤ ∑ k ∈ S, ‖ψ k‖ ^ 2 := by
  have hS : ∑ k, (starRingEnd ℂ) (ψ k) * φ k = ∑ k ∈ S, (starRingEnd ℂ) (ψ k) * φ k := by
    symm
    apply sum_subset (subset_univ S)
    intro k _ hk
    rw [hφ k hk, mul_zero]
  have h1 : ‖∑ k ∈ S, (starRingEnd ℂ) (ψ k) * φ k‖ ≤ ∑ k ∈ S, ‖ψ k‖ * ‖φ k‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
    rw [norm_mul, RCLike.norm_conj]
  have h2 : (∑ k ∈ S, ‖ψ k‖ * ‖φ k‖) ^ 2 ≤ (∑ k ∈ S, ‖ψ k‖ ^ 2) * ∑ k ∈ S, ‖φ k‖ ^ 2 :=
    sum_mul_sq_le_sq_mul_sq S _ _
  have h3 : ∑ k ∈ S, ‖φ k‖ ^ 2 ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ S) fun k _ _ => by positivity).trans hnorm
  have h4 : (0 : ℝ) ≤ ∑ k ∈ S, ‖ψ k‖ ^ 2 := sum_nonneg fun k _ => by positivity
  calc ‖∑ k, (starRingEnd ℂ) (ψ k) * φ k‖ ^ 2
      = ‖∑ k ∈ S, (starRingEnd ℂ) (ψ k) * φ k‖ ^ 2 := by rw [hS]
    _ ≤ (∑ k ∈ S, ‖ψ k‖ * ‖φ k‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) h1
    _ ≤ (∑ k ∈ S, ‖ψ k‖ ^ 2) * ∑ k ∈ S, ‖φ k‖ ^ 2 := h2
    _ ≤ (∑ k ∈ S, ‖ψ k‖ ^ 2) * 1 := mul_le_mul_of_nonneg_left h3 h4
    _ = ∑ k ∈ S, ‖ψ k‖ ^ 2 := mul_one _

end Pairing
end Register
