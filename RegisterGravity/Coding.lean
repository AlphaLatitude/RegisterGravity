import RegisterGravity.Capacity
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The coding step for logical qubits (Sec. IV.A)

Sec. IV.A finds the ceiling for logical qubits, `2^(N+1) ≤ L`, from a step of coding theory.  A
logical qubit is a two-level system that comes with its logical measurement, so it has a string
(Postulate 1), and its bit is read from the bits of the physical qubits that realize it, whose
strings must have room for its conditional states as well.  This file proves the coding step, for
one code block and for `N` logical qubits each in its own block, and the count that gives the
ceiling.

The physical bits are words `x` of `n` bits (`Word n`, bits in `ZMod 2`).  In a
Calderbank–Shor–Steane code the logical states are equal-weight superpositions of the words in two
cosets of a linear code: the logical `0` of an additive subgroup `C₀`, the logical `1` of `v + C₀`,
with `v ∉ C₀`.  Measured with the logical weights `q 0` and `q 1`, every word of `C₀` comes with the
weight `q 0`, every word of `v + C₀` with `q 1`, and no other word occurs (`weight`: the words'
probabilities are the squares of the code state's amplitudes, Eqs. (qubit) and (raqm) of the paper); a
conditional probability is a ratio of sums of these weights.  Conditional states are counted by their
probabilities, as the cases below are.

* `css_conditional`: a physical bit `j`, given the bits on any set `P` of positions, such as the
  earlier physical bits of its block, reads `1` with the probability `0` or `1` (fixed), `1/2`
  (balanced), `q 1/(q 0 + q 1)` (equal to the logical bit) or `q 0/(q 0 + q 1)` (opposite to it).
  Whether it is balanced depends on `P` alone, not on how `P` reads (`css_conditional_cases`): it is
  when a word of `C₀` that vanishes on `P`, a word of the kernel, has bit `j` set.  The words of a
  coset that agree on `P` are none, or as many as the kernel (`card_agreeing`); bit `j` is balanced
  on them when a word of the kernel has it set (`bits_balanced`), and the same on all of them
  otherwise (`bits_constant`).
* `repetition_conditional`: in a repetition code, whose logical states are the single words `0` and
  `1⋯1`, only the fixed and the equal case occur.
* `LineCode`: a code whose logical bit is the parity of a line `S` of physical bits, `0` on `C₀` and
  `1` at `v`, with a last bit `j` of the line that the code does not fix, as in the surface code.
  The last bit is the logical bit plus the parity of the rest of the line (`LineCode.bit_eq`).  Where
  every reading of the rest of the line occurs in both cosets (`LineCode.Match`), the last bit, given
  the rest of the line, is the logical bit or its opposite: it reads `1` with the probability
  `q 1/(q 0 + q 1)` when the rest reads `0` and `q 0/(q 0 + q 1)` when it reads `1`
  (`LineCode.bitGiven_rest`, the two cases `caseProb`).  Given the parity of the rest alone, this
  holds in every line code (`LineCode.lastGivenRest_eq`).  The surface code of every distance `d`
  is such a code and meets `LineCode.Match` (`surfaceCode`, `surfaceCode_match`): the checks along
  its top row read `1` on adjacent pairs of the row, so the rest of the row takes every pattern in
  both cosets.
* `N` logical qubits (`jointWeight`): the blocks are read in order, the physical bits of the first
  `N − 1` logical qubits reading a word `w`, which gives their joint outcome `κ w`, and then positions
  of the last block.  Given `w`, the last block is a code state with the logical weights of the
  outcome `κ w` (`jointBitGiven_eq`), so a physical bit, given all the earlier physical bits, is
  fixed, balanced, or equal or opposite to the logical bit (`css_conditional_joint`; for the last
  bit of a line, given the rest of the line, `LineCode.jointBitGiven_rest`).  A physical
  string then has, for each outcome of the earlier logical qubits, at most two conditional states
  strictly between `0` and `1`, the logical bit's probability and its complement, or `1/2` alone: up
  to `2^N` in all, twice as many as a logical string (`card_condStates_le`); in a repetition code at
  most `2^(N−1)`, as many as a logical string (`card_condStates_repetition`).  The last bit of a line
  in a code that meets `LineCode.Match` has exactly `2^N` where every outcome occurs with the last
  logical bit uncertain given it and these probabilities differ, as in a random state
  (`LineCode.card_lineStates`).
* The ceiling.  Sec. IV.A tests whether each string has room for the different conditional states
  of its qubit.  In this file the block of a conditional state is the set of cells whose outcome
  has that state: the paper's blocks, one for each joint outcome, of the outcomes that have the
  state, taken together.  A block holds a conditional state
  when its share of 1s is the state.  It shows a conditional state strictly between `0` and `1`
  when its share lies strictly between `0` and `1`, as it does when it holds the state.  A string
  that shows each such state on the state's block has two cells for each
  (`two_mul_card_states_le`).  It shows them when each occurs with either value of the bit, and a
  state that occurs with a value is at a cell with that value.  These are the two hypotheses of
  the results of `Main.lean` on codes (`shows_of_outcomes`), and two cells for each state meet
  both (`two_cells_each_model`).
  Where the equal and the opposite case both occur for every outcome of the earlier logical qubits,
  and the `2^N` probabilities differ, the string has `2^N` such states, so `2^(N+1) ≤ L`
  (`ceiling_both_cases`); for the last bit of a line, in a code that meets `LineCode.Match`, both
  occur (`ceiling_line_code`), and `Numerics.logical_ceiling_cos` gives `203` logical qubits.
  `ceiling_line_code_model` shows that the hypotheses can be met together, for two logical qubits in
  the two-bit line code `lineTwo`.
-/

open Finset

namespace Register
namespace Coding

variable {n : ℕ}

/-! ### Words and parities -/

/-- a word of `n` physical bits -/
abbrev Word (n : ℕ) := Fin n → ZMod 2

/-- the parity of the bits of a word on a set `S` of positions -/
def parity (S : Finset (Fin n)) (x : Word n) : ZMod 2 := ∑ i ∈ S, x i

lemma parity_add (S : Finset (Fin n)) (x y : Word n) :
    parity S (x + y) = parity S x + parity S y := by
  simp [parity, sum_add_distrib]

lemma parity_neg (S : Finset (Fin n)) (x : Word n) : parity S (-x) = -parity S x := by
  simp only [parity, Pi.neg_apply, Finset.sum_neg_distrib]

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_not_eq_iff : ∀ a s : ZMod 2, ¬ a = s ↔ a = s + 1 := by decide

lemma zmod2_eq_zero_of_add_one : ∀ {a : ZMod 2}, a + 1 = 1 → a = 0 := by decide

lemma zmod2_eq_zero_of_ne_one : ∀ {a : ZMod 2}, ¬ a = 1 → a = 0 := by decide

lemma zmod2_zero_or_one : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide

lemma word_add_self (c : Word n) : c + c = 0 := by
  funext i
  exact zmod2_add_self (c i)

/-! ### A code of two cosets -/

section TwoCosets

variable (C₀ : AddSubgroup (Word n)) (v : Word n)

open Classical in
/-- **The measured words of a logical state** (Sec. IV.A): with the logical weights `q 0` and
`q 1`, the logical states being equal-weight superpositions of the words of `C₀` and of `v + C₀`,
a measurement of the physical qubits returns a word of `C₀` with the weight `q 0`, a word of
`v + C₀` with the weight `q 1`, and no other word.  The two cosets are disjoint in a code of one
logical qubit, `v ∉ C₀`; the theorems below hold for every `v`.  The common
factor `1/|C₀|` is left out, since only ratios of these weights are used. -/
noncomputable def weight (q : ZMod 2 → ℝ) (x : Word n) : ℝ :=
  (if x ∈ C₀ then q 0 else 0) + (if x - v ∈ C₀ then q 1 else 0)

open Classical in
/-- **The probability that physical bit `j` reads `1`, given the bits on the positions `P`**, there
reading as in `u`: the weight of the words that agree with `u` on `P` and have bit `j` set, over the
weight of the words that agree with `u` on `P` -/
noncomputable def bitGiven (q : ZMod 2 → ℝ) (P : Finset (Fin n)) (u : Word n) (j : Fin n) : ℝ :=
  (∑ x ∈ univ.filter (fun x => (∀ i ∈ P, x i = u i) ∧ x j = 1), weight C₀ v q x) /
    ∑ x ∈ univ.filter (fun x => ∀ i ∈ P, x i = u i), weight C₀ v q x

open Classical in
/-- the words of the coset `t + C₀` that agree with `u` on `P` -/
noncomputable def agreeing (P : Finset (Fin n)) (u t : Word n) : Finset (Word n) :=
  univ.filter (fun x => x - t ∈ C₀ ∧ ∀ i ∈ P, x i = u i)

open Classical in
/-- the kernel: the words of `C₀` that vanish on `P` -/
noncomputable def kernel (P : Finset (Fin n)) : Finset (Word n) :=
  univ.filter (fun c => c ∈ C₀ ∧ ∀ i ∈ P, c i = 0)

/-- **The words of a coset that agree on `P` are none, or as many as the kernel**: subtracting one
of them carries them onto the kernel -/
lemma card_agreeing {P : Finset (Fin n)} {u t x₀ : Word n} (hx₀ : x₀ ∈ agreeing C₀ P u t) :
    (agreeing C₀ P u t).card = (kernel C₀ P).card := by
  classical
  simp only [agreeing, mem_filter, mem_univ, true_and] at hx₀
  apply Finset.card_nbij' (· - x₀) (· + x₀)
  · intro x hx
    simp only [agreeing, kernel, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    refine ⟨?_, fun i hi => ?_⟩
    · have : x - x₀ = (x - t) - (x₀ - t) := by ring
      rw [this]
      exact C₀.sub_mem hx.1 hx₀.1
    · simp [hx.2 i hi, hx₀.2 i hi]
  · intro c hc
    simp only [agreeing, kernel, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
    refine ⟨?_, fun i hi => ?_⟩
    · have : c + x₀ - t = c + (x₀ - t) := by ring
      rw [this]
      exact C₀.add_mem hc.1 hx₀.1
    · simp [hc.2 i hi, hx₀.2 i hi]
  · intro x _
    simp
  · intro c _
    simp

/-- **Where some word of the kernel has bit `j` set, half the agreeing words do**: adding it keeps
the coset and the bits on `P` and flips bit `j` -/
lemma bits_balanced {P : Finset (Fin n)} {u t k : Word n} {j : Fin n} (hk : k ∈ kernel C₀ P)
    (hkj : k j = 1) :
    2 * ((agreeing C₀ P u t).filter (fun x => x j = 1)).card = (agreeing C₀ P u t).card := by
  classical
  simp only [kernel, mem_filter, mem_univ, true_and] at hk
  have hsplit := Finset.card_filter_add_card_filter_not (s := agreeing C₀ P u t)
    (fun x => x j = 1)
  have hflip : ((agreeing C₀ P u t).filter (fun x => x j = 1)).card =
      ((agreeing C₀ P u t).filter (fun x => ¬ x j = 1)).card := by
    apply Finset.card_nbij' (· + k) (· + k)
    · intro x hx
      simp only [agreeing, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        at hx ⊢
      refine ⟨⟨?_, fun i hi => ?_⟩, ?_⟩
      · have : x + k - t = (x - t) + k := by ring
        rw [this]
        exact C₀.add_mem hx.1.1 hk.1
      · simp [hx.1.2 i hi, hk.2 i hi]
      · simp only [Pi.add_apply, hx.2, hkj]
        decide
    · intro x hx
      simp only [agreeing, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        at hx ⊢
      refine ⟨⟨?_, fun i hi => ?_⟩, ?_⟩
      · have : x + k - t = (x - t) + k := by ring
        rw [this]
        exact C₀.add_mem hx.1.1 hk.1
      · simp [hx.1.2 i hi, hk.2 i hi]
      · simp only [Pi.add_apply, hkj]
        rw [(zmod2_not_eq_iff (x j) 1).1 hx.2]
        decide
    · intro x _
      simp only
      rw [add_assoc, word_add_self, add_zero]
    · intro x _
      simp only
      rw [add_assoc, word_add_self, add_zero]
  omega

/-- **Where no word of the kernel has bit `j` set, bit `j` is the same on all the agreeing words**:
two of them differ by a word of the kernel -/
lemma bits_constant {P : Finset (Fin n)} {u t : Word n} {j : Fin n}
    (hK : ∀ k ∈ kernel C₀ P, k j = 0) :
    (agreeing C₀ P u t).filter (fun x => x j = 1) = ∅ ∨
      (agreeing C₀ P u t).filter (fun x => x j = 1) = agreeing C₀ P u t := by
  classical
  by_cases h : ∃ x ∈ agreeing C₀ P u t, x j = 1
  · right
    obtain ⟨x₀, hx₀, hx₀j⟩ := h
    apply Finset.filter_true_of_mem
    intro x hx
    simp only [agreeing, mem_filter, mem_univ, true_and] at hx hx₀
    have hk : x - x₀ ∈ kernel C₀ P := by
      simp only [kernel, mem_filter, mem_univ, true_and]
      refine ⟨?_, fun i hi => ?_⟩
      · have : x - x₀ = (x - t) - (x₀ - t) := by ring
        rw [this]
        exact C₀.sub_mem hx.1 hx₀.1
      · simp [hx.2 i hi, hx₀.2 i hi]
    have := hK _ hk
    simp only [Pi.sub_apply, hx₀j] at this
    exact sub_eq_zero.1 this
  · left
    push Not at h
    apply Finset.filter_false_of_mem
    intro x hx
    exact h x hx

/-- the ratio of the weights in every case that `card_agreeing` and `bits_constant` leave -/
lemma ratio_cases {q0 q1 m A0 Av B0 Bv : ℝ} (hm : m ≠ 0) (hA0 : A0 = 0 ∨ A0 = m)
    (hAv : Av = 0 ∨ Av = m) (hB0 : B0 = 0 ∨ B0 = A0) (hBv : Bv = 0 ∨ Bv = Av) :
    (q0 * B0 + q1 * Bv) / (q0 * A0 + q1 * Av) = 0 ∨
    (q0 * B0 + q1 * Bv) / (q0 * A0 + q1 * Av) = 1 ∨
    (q0 * B0 + q1 * Bv) / (q0 * A0 + q1 * Av) = q1 / (q0 + q1) ∨
    (q0 * B0 + q1 * Bv) / (q0 * A0 + q1 * Av) = q0 / (q0 + q1) := by
  rcases hB0 with hB0 | hB0 <;> rcases hBv with hBv | hBv <;> rw [hB0, hBv]
  · left; simp
  · rcases hA0 with hA0 | hA0 <;> rcases hAv with hAv | hAv <;> rw [hA0, hAv]
    · left; simp
    · rw [mul_zero, zero_add]
      by_cases h : q1 * m = 0
      · left; simp [h]
      · right; left; exact div_self h
    · left; simp
    · right; right; left
      rw [mul_zero, zero_add, ← add_mul, mul_div_mul_right _ _ hm]
  · rcases hA0 with hA0 | hA0 <;> rcases hAv with hAv | hAv <;> rw [hA0, hAv]
    · left; simp
    · left; simp
    · rw [mul_zero, add_zero]
      by_cases h : q0 * m = 0
      · left; simp [h]
      · right; left; exact div_self h
    · right; right; right
      rw [mul_zero, add_zero, ← add_mul, mul_div_mul_right _ _ hm]
  · by_cases h : q0 * A0 + q1 * Av = 0
    · left; simp [h]
    · right; left; exact div_self h

/-- the ratio of the weights when half the agreeing words of each coset have the bit set -/
lemma ratio_half {q0 q1 A0 Av B0 Bv : ℝ} (h0 : 2 * B0 = A0) (hv : 2 * Bv = Av) :
    (q0 * B0 + q1 * Bv) / (q0 * A0 + q1 * Av) = 0 ∨
    (q0 * B0 + q1 * Bv) / (q0 * A0 + q1 * Av) = 1 / 2 := by
  by_cases h : q0 * A0 + q1 * Av = 0
  · left; simp [h]
  · right
    rw [div_eq_iff h, ← h0, ← hv]
    ring

open Classical in
/-- a sum of weights: `q 0` times the words of `C₀`, plus `q 1` times the words of `v + C₀` -/
lemma sum_weight (q : ZMod 2 → ℝ) (F : Finset (Word n)) :
    ∑ x ∈ F, weight C₀ v q x =
      q 0 * (F.filter (fun x => x ∈ C₀)).card + q 1 * (F.filter (fun x => x - v ∈ C₀)).card := by
  unfold weight
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
  simp only [sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  ring

open Classical in
lemma filter_agreeing (P : Finset (Fin n)) (u t : Word n) :
    (univ.filter (fun x => ∀ i ∈ P, x i = u i)).filter (fun x => x - t ∈ C₀) =
      agreeing C₀ P u t := by
  ext x
  simp only [agreeing, mem_filter, mem_univ, true_and]
  tauto

open Classical in
lemma filter_agreeing_bit (P : Finset (Fin n)) (u t : Word n) (j : Fin n) :
    (univ.filter (fun x => (∀ i ∈ P, x i = u i) ∧ x j = 1)).filter (fun x => x - t ∈ C₀) =
      (agreeing C₀ P u t).filter (fun x => x j = 1) := by
  ext x
  simp only [agreeing, mem_filter, mem_univ, true_and]
  tauto

/-- `bitGiven` as a ratio of counts: the agreeing words of each coset with bit `j` set, weighted, over
the agreeing words of each coset, weighted -/
lemma bitGiven_counts (q : ZMod 2 → ℝ) (P : Finset (Fin n)) (u : Word n) (j : Fin n) :
    bitGiven C₀ v q P u j =
      (q 0 * ((agreeing C₀ P u 0).filter (fun x => x j = 1)).card +
        q 1 * ((agreeing C₀ P u v).filter (fun x => x j = 1)).card) /
      (q 0 * (agreeing C₀ P u 0).card + q 1 * (agreeing C₀ P u v).card) := by
  classical
  unfold bitGiven
  rw [sum_weight, sum_weight]
  have e1 : (univ.filter (fun x => ∀ i ∈ P, x i = u i)).filter (fun x => x ∈ C₀) =
      agreeing C₀ P u 0 := by
    rw [← filter_agreeing C₀ P u 0]
    simp
  have e3 : (univ.filter (fun x => (∀ i ∈ P, x i = u i) ∧ x j = 1)).filter (fun x => x ∈ C₀) =
      (agreeing C₀ P u 0).filter (fun x => x j = 1) := by
    rw [← filter_agreeing_bit C₀ P u 0 j]
    simp
  rw [e1, filter_agreeing C₀ P u v, e3, filter_agreeing_bit C₀ P u v j]

/-- **Whether a physical bit is balanced depends on the kernel alone, not on how the other bits
read** (Sec. IV.A).  For a set `P` of positions and a bit `j`: if a word of the kernel has bit `j`
set, bit `j`, given any reading of `P`, reads `1` with the probability `1/2` (or `0`, for a reading
whose total `weight` is zero); if not, with the probability `0` or `1`, or the logical bit's
probability `q 1/(q 0 + q 1)`, or its complement `q 0/(q 0 + q 1)`, which are `1/2` too when
`q 0 = q 1`.  With `P` the earlier physical bits, a bit has as its conditional states strictly
between `0` and `1` either `1/2` alone or at most the logical bit's probability and its
complement. -/
theorem css_conditional_cases (q : ZMod 2 → ℝ) (P : Finset (Fin n)) (j : Fin n) :
    ((∃ k ∈ kernel C₀ P, k j = 1) →
      ∀ u, bitGiven C₀ v q P u j = 0 ∨ bitGiven C₀ v q P u j = 1 / 2) ∧
    ((¬ ∃ k ∈ kernel C₀ P, k j = 1) →
      ∀ u, bitGiven C₀ v q P u j = 0 ∨ bitGiven C₀ v q P u j = 1 ∨
        bitGiven C₀ v q P u j = q 1 / (q 0 + q 1) ∨
        bitGiven C₀ v q P u j = q 0 / (q 0 + q 1)) := by
  classical
  refine ⟨fun hK u => ?_, fun hK u => ?_⟩
  · obtain ⟨k, hk, hkj⟩ := hK
    have h0 : (2 : ℝ) * ((agreeing C₀ P u 0).filter (fun x => x j = 1)).card =
        (agreeing C₀ P u 0).card := by exact_mod_cast bits_balanced C₀ hk hkj
    have hv : (2 : ℝ) * ((agreeing C₀ P u v).filter (fun x => x j = 1)).card =
        (agreeing C₀ P u v).card := by exact_mod_cast bits_balanced C₀ hk hkj
    rw [bitGiven_counts]
    exact ratio_half h0 hv
  · push Not at hK
    have hK' : ∀ k ∈ kernel C₀ P, k j = 0 := fun k hk => zmod2_eq_zero_of_ne_one (hK k hk)
    have hA : ∀ t, ((agreeing C₀ P u t).card : ℝ) = 0 ∨
        ((agreeing C₀ P u t).card : ℝ) = (kernel C₀ P).card := fun t => by
      by_cases hne : (agreeing C₀ P u t).Nonempty
      · right
        obtain ⟨x₀, hx₀⟩ := hne
        exact_mod_cast card_agreeing C₀ hx₀
      · left
        rw [Finset.not_nonempty_iff_eq_empty.1 hne]
        simp
    have hm : ((kernel C₀ P).card : ℝ) ≠ 0 := by
      have h0 : (0 : Word n) ∈ kernel C₀ P := by simp [kernel]
      exact_mod_cast (Finset.card_pos.2 ⟨0, h0⟩).ne'
    have hB : ∀ t, (((agreeing C₀ P u t).filter (fun x => x j = 1)).card : ℝ) = 0 ∨
        (((agreeing C₀ P u t).filter (fun x => x j = 1)).card : ℝ) =
          (agreeing C₀ P u t).card := fun t => by
      rcases bits_constant C₀ (u := u) (t := t) hK' with h | h
      · left
        rw [h]
        simp
      · right
        rw [h]
    rw [bitGiven_counts]
    exact ratio_cases hm (hA 0) (hA v) (hB 0) (hB v)

/-- **In a Calderbank–Shor–Steane code a physical bit, given the earlier physical bits, is fixed,
balanced, or equal or opposite to the logical bit** (Sec. IV.A), for one code block
(`css_conditional_joint` for `N` logical qubits).  For the logical states the equal-weight
superpositions of the words of `C₀` and of `v + C₀`, with the logical weights `q 0` and `q 1`, and
for any set `P` of positions read as in `u`, bit `j` reads `1` with the probability `0` or `1`,
`1/2`, `q 1/(q 0 + q 1)`, or `q 0/(q 0 + q 1)` (`css_conditional_cases`).  The agreeing words of
each coset are none or as many as the kernel (`card_agreeing`); if a word of the kernel has bit `j`
set, bit `j` is balanced on both cosets (`bits_balanced`); if not, it is the same on all the
agreeing words of each coset (`bits_constant`), so the probability is `0` or `1`, or, where both
cosets have agreeing words, the logical bit's probability or its complement. -/
theorem css_conditional (q : ZMod 2 → ℝ) (P : Finset (Fin n)) (u : Word n) (j : Fin n) :
    bitGiven C₀ v q P u j = 0 ∨ bitGiven C₀ v q P u j = 1 ∨ bitGiven C₀ v q P u j = 1 / 2 ∨
      bitGiven C₀ v q P u j = q 1 / (q 0 + q 1) ∨ bitGiven C₀ v q P u j = q 0 / (q 0 + q 1) := by
  by_cases hK : ∃ k ∈ kernel C₀ P, k j = 1
  · rcases (css_conditional_cases C₀ v q P j).1 hK u with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases (css_conditional_cases C₀ v q P j).2 hK u with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **In a repetition code only the fixed and the equal case occur** (Sec. IV.A): with the logical
states the single words `0` and `1⋯1`, `C₀ = {0}` and `v = 1⋯1`, a physical bit, given the bits on
any set of positions, reads `1` with the probability `0` or `1`, or `q 1/(q 0 + q 1)`, that of the
logical bit. -/
theorem repetition_conditional (q : ZMod 2 → ℝ) (P : Finset (Fin n)) (u : Word n) (j : Fin n) :
    bitGiven ⊥ (fun _ => 1) q P u j = 0 ∨ bitGiven ⊥ (fun _ => 1) q P u j = 1 ∨
      bitGiven ⊥ (fun _ => 1) q P u j = q 1 / (q 0 + q 1) := by
  classical
  unfold bitGiven
  rw [sum_weight, sum_weight]
  set a : ℝ := ((((univ : Finset (Word n)).filter (fun x => ∀ i ∈ P, x i = u i)).filter
    (fun x => x ∈ (⊥ : AddSubgroup (Word n)))).card : ℝ)
  set b : ℝ := ((((univ : Finset (Word n)).filter (fun x => ∀ i ∈ P, x i = u i)).filter
    (fun x => x - (fun _ => (1 : ZMod 2)) ∈ (⊥ : AddSubgroup (Word n)))).card : ℝ)
  have h0 : ((univ.filter (fun x : Word n => (∀ i ∈ P, x i = u i) ∧ x j = 1)).filter
      (fun x => x ∈ (⊥ : AddSubgroup (Word n)))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hx0
    rw [AddSubgroup.mem_bot] at hx0
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [hx0] at hx
    exact absurd hx.2 (by simp)
  have h1 : ((univ.filter (fun x : Word n => (∀ i ∈ P, x i = u i) ∧ x j = 1)).filter
      (fun x => x - (fun _ => (1 : ZMod 2)) ∈ (⊥ : AddSubgroup (Word n)))).card = b := by
    congr 2
    ext x
    simp only [mem_filter, mem_univ, true_and, AddSubgroup.mem_bot, sub_eq_zero]
    constructor
    · rintro ⟨⟨hP, -⟩, hx⟩
      exact ⟨hP, hx⟩
    · rintro ⟨hP, hx⟩
      refine ⟨⟨hP, ?_⟩, hx⟩
      rw [hx]
  rw [h0, h1, Nat.cast_zero, mul_zero, zero_add]
  have ha : a = 0 ∨ a = 1 := by
    have : (((univ : Finset (Word n)).filter (fun x => ∀ i ∈ P, x i = u i)).filter
        (fun x => x ∈ (⊥ : AddSubgroup (Word n)))).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      simp only [mem_filter, AddSubgroup.mem_bot] at hx hy
      rw [hx.2, hy.2]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
    · left; simp only [a, h, Nat.cast_zero]
    · right; simp only [a, h, Nat.cast_one]
  have hb : b = 0 ∨ b = 1 := by
    have : (((univ : Finset (Word n)).filter (fun x => ∀ i ∈ P, x i = u i)).filter
        (fun x => x - (fun _ => (1 : ZMod 2)) ∈ (⊥ : AddSubgroup (Word n)))).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      simp only [mem_filter, AddSubgroup.mem_bot, sub_eq_zero] at hx hy
      rw [hx.2, hy.2]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
    · left; simp only [b, h, Nat.cast_zero]
    · right; simp only [b, h, Nat.cast_one]
  rcases hb with hb | hb <;> rw [hb]
  · left; simp
  · rcases ha with ha | ha <;> rw [ha]
    · rw [mul_zero, zero_add, mul_one]
      by_cases hq : q 1 = 0
      · left; simp [hq]
      · right; left; exact div_self hq
    · right; right
      rw [mul_one, mul_one]

end TwoCosets

/-- **The equal and the opposite case** (Sec. IV.A): the probability that a physical bit reads `1`
when it equals the logical bit (`t = 0`), `q 1/(q 0 + q 1)`, and when it is the logical bit's
opposite (`t = 1`), `q 0/(q 0 + q 1)` -/
noncomputable def caseProb (q : ZMod 2 → ℝ) (t : ZMod 2) : ℝ :=
  (if t = 0 then q 1 else q 0) / (q 0 + q 1)

/-- with both logical weights positive, both cases lie strictly between `0` and `1` -/
lemma caseProb_pos_lt_one {q : ZMod 2 → ℝ} (hq : ∀ t, 0 < q t) (t : ZMod 2) :
    0 < caseProb q t ∧ caseProb q t < 1 := by
  have h0 := hq 0
  have h1 := hq 1
  unfold caseProb
  split_ifs
  · exact ⟨div_pos h1 (add_pos h0 h1), (div_lt_one (add_pos h0 h1)).2 (by linarith)⟩
  · exact ⟨div_pos h0 (add_pos h0 h1), (div_lt_one (add_pos h0 h1)).2 (by linarith)⟩

/-! ### A logical bit read as the parity of a line -/

/-- **A logical qubit read as the parity of a line** (Sec. IV.A): the words of the logical `0` form
an additive subgroup `C₀`, those of the logical `1` its coset `v + C₀`; the logical bit is the
parity of a line `S` of physical bits, `0` on `C₀` (`hC`) and `1` at `v` (`hv`); and the last bit
`j` of the line (`hj`) is not fixed by the code: some word of `C₀` has it set (`hfree`).  The
surface code is such a code, its logical bit the parity of a line of physical bits across the
lattice (`surfaceCode`, at every distance). -/
structure LineCode (n : ℕ) where
  /-- the words of the logical `0` -/
  C₀ : AddSubgroup (Word n)
  /-- a word of the logical `1` -/
  v : Word n
  /-- the line -/
  S : Finset (Fin n)
  /-- its last bit -/
  j : Fin n
  hj : j ∈ S
  hC : ∀ c ∈ C₀, parity S c = 0
  hv : parity S v = 1
  hfree : ∃ c ∈ C₀, c j = 1

namespace LineCode

variable (code : LineCode n)

/-- the parity of the rest of the line, its bits other than the last -/
def rest (x : Word n) : ZMod 2 := parity (code.S.erase code.j) x

/-- **The last bit of the line is the line's parity plus that of the rest** -/
lemma bit_eq (x : Word n) : x code.j = parity code.S x + code.rest x := by
  unfold rest parity
  rw [← Finset.add_sum_erase _ _ code.hj, add_assoc, zmod2_add_self, add_zero]

lemma rest_add (x y : Word n) : code.rest (x + y) = code.rest x + code.rest y :=
  parity_add _ x y

/-- a word of `C₀` whose last bit of the line is `1` has the rest of the line `1` -/
lemma rest_flip : ∃ c ∈ code.C₀, code.rest c = 1 := by
  obtain ⟨c, hc, hcj⟩ := code.hfree
  refine ⟨c, hc, ?_⟩
  have := code.bit_eq c
  rw [hcj, code.hC c hc, zero_add] at this
  exact this.symm

open Classical in
/-- the words of the coset `t + C₀` -/
noncomputable def coset (t : Word n) : Finset (Word n) :=
  univ.filter (fun x => x - t ∈ code.C₀)

open Classical in
/-- the words of the coset `t + C₀` whose rest of the line is `s` -/
noncomputable def cosetRest (t : Word n) (s : ZMod 2) : Finset (Word n) :=
  univ.filter (fun x => x - t ∈ code.C₀ ∧ code.rest x = s)

/-- **As many words of a coset have the rest of the line `s` as `s + 1`**: adding a word of `C₀`
whose rest is `1` (`rest_flip`) keeps the coset and flips the rest -/
theorem card_cosetRest (t : Word n) (s : ZMod 2) :
    (code.cosetRest t s).card = (code.cosetRest t (s + 1)).card := by
  classical
  obtain ⟨c, hc, hrc⟩ := code.rest_flip
  apply Finset.card_nbij' (· + c) (· + c)
  · intro x hx
    simp only [cosetRest, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    refine ⟨?_, ?_⟩
    · have : x + c - t = (x - t) + c := by ring
      rw [this]
      exact code.C₀.add_mem hx.1 hc
    · rw [code.rest_add, hx.2, hrc]
  · intro x hx
    simp only [cosetRest, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    refine ⟨?_, ?_⟩
    · have : x + c - t = (x - t) + c := by ring
      rw [this]
      exact code.C₀.add_mem hx.1 hc
    · rw [code.rest_add, hx.2, hrc, add_assoc, zmod2_add_self, add_zero]
  · intro x _
    simp only
    rw [add_assoc, word_add_self, add_zero]
  · intro x _
    simp only
    rw [add_assoc, word_add_self, add_zero]

/-- every coset of `C₀` has as many words as `C₀` -/
lemma card_coset (t : Word n) : (code.coset t).card = (code.coset 0).card := by
  classical
  apply Finset.card_nbij' (· - t) (· + t)
  · intro x hx
    simp only [coset, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    simpa using hx
  · intro x hx
    simp only [coset, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    simpa using hx
  · intro x _
    simp
  · intro x _
    simp

/-- **Half the words of every coset have each parity of the rest of the line** -/
lemma two_mul_card_cosetRest (t : Word n) (s : ZMod 2) :
    2 * (code.cosetRest t s).card = (code.coset 0).card := by
  classical
  rw [← code.card_coset t]
  have hsplit := Finset.card_filter_add_card_filter_not (s := code.coset t)
    (fun x => code.rest x = s)
  have h1 : (code.coset t).filter (fun x => code.rest x = s) = code.cosetRest t s := by
    ext x
    simp [coset, cosetRest]
  have h2 : (code.coset t).filter (fun x => ¬ code.rest x = s) = code.cosetRest t (s + 1) := by
    ext x
    simp only [coset, cosetRest, mem_filter, mem_univ, true_and]
    rw [zmod2_not_eq_iff]
  rw [h1, h2, ← code.card_cosetRest t s] at hsplit
  omega

/-- `C₀` has at least two words: `0`, and a word whose last bit of the line is `1` -/
lemma two_le_card_coset : 2 ≤ (code.coset 0).card := by
  classical
  obtain ⟨c, hc, hcj⟩ := code.hfree
  have h0 : (0 : Word n) ∈ code.coset 0 := by simp [coset]
  have hc' : c ∈ code.coset 0 := by simp [coset, hc]
  have hne : c ≠ 0 := by
    intro h
    rw [h] at hcj
    simp at hcj
  exact Finset.one_lt_card.2 ⟨c, hc', 0, h0, hne⟩

open Classical in
/-- **The probability that the last bit of the line reads `1`, given that the rest reads `s`**, for
the logical weights `q` (`weight`) -/
noncomputable def lastGivenRest (q : ZMod 2 → ℝ) (s : ZMod 2) : ℝ :=
  (∑ x ∈ univ.filter (fun x => code.rest x = s ∧ x code.j = 1), weight code.C₀ code.v q x) /
    ∑ x ∈ univ.filter (fun x => code.rest x = s), weight code.C₀ code.v q x

/-- on `C₀` the last bit of the line is the rest of it -/
lemma bit_of_mem {x : Word n} (hx : x ∈ code.C₀) : x code.j = code.rest x := by
  rw [code.bit_eq x, code.hC x hx, zero_add]

/-- on `v + C₀` the last bit of the line is the rest of it plus one -/
lemma bit_of_mem_v {x : Word n} (hx : x - code.v ∈ code.C₀) : x code.j = code.rest x + 1 := by
  have hp : parity code.S x = 1 := by
    have : x = (x - code.v) + code.v := by ring
    rw [this, parity_add, code.hC _ hx, code.hv, zero_add]
  rw [code.bit_eq x, hp, add_comm]

open Classical in
lemma filter_rest (t : Word n) (s : ZMod 2) :
    (univ.filter (fun x => code.rest x = s)).filter (fun x => x - t ∈ code.C₀) =
      code.cosetRest t s := by
  ext x
  simp only [cosetRest, mem_filter, mem_univ, true_and]
  tauto

open Classical in
lemma filter_rest_zero (s : ZMod 2) :
    (univ.filter (fun x => code.rest x = s)).filter (fun x => x ∈ code.C₀) =
      code.cosetRest 0 s := by
  rw [← code.filter_rest 0 s]
  simp

open Classical in
/-- on `C₀` the last bit of the line reads `1` exactly when the rest does -/
lemma filter_last_zero (s : ZMod 2) :
    (univ.filter (fun x => code.rest x = s ∧ x code.j = 1)).filter (fun x => x ∈ code.C₀) =
      if s = 1 then code.cosetRest 0 s else ∅ := by
  ext x
  simp only [cosetRest, mem_filter, mem_univ, true_and, sub_zero]
  split_ifs with hs
  · simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, -⟩, hx⟩
      exact ⟨hx, hr⟩
    · rintro ⟨hx, hr⟩
      exact ⟨⟨hr, by rw [code.bit_of_mem hx, hr, hs]⟩, hx⟩
  · simp only [Finset.notMem_empty, iff_false, not_and]
    intro ⟨hr, hj⟩ hx
    rw [code.bit_of_mem hx, hr] at hj
    exact hs hj

open Classical in
/-- on `v + C₀` the last bit of the line reads `1` exactly when the rest reads `0` -/
lemma filter_last_v (s : ZMod 2) :
    (univ.filter (fun x => code.rest x = s ∧ x code.j = 1)).filter
        (fun x => x - code.v ∈ code.C₀) =
      if s = 0 then code.cosetRest code.v s else ∅ := by
  ext x
  simp only [cosetRest, mem_filter, mem_univ, true_and]
  split_ifs with hs
  · simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, -⟩, hx⟩
      exact ⟨hx, hr⟩
    · rintro ⟨hx, hr⟩
      exact ⟨⟨hr, by rw [code.bit_of_mem_v hx, hr, hs, zero_add]⟩, hx⟩
  · simp only [Finset.notMem_empty, iff_false, not_and]
    intro ⟨hr, hj⟩ hx
    rw [code.bit_of_mem_v hx, hr] at hj
    exact hs (zmod2_eq_zero_of_add_one hj)

/-- **Given the parity of the rest of the line, its last bit is the logical bit or its opposite**
(Sec. IV.A), in every line code.  When the rest reads `0` the last bit equals the logical bit, and
reads `1` with the probability `q 1/(q 0 + q 1)`; when the rest reads `1` it is the opposite, and
reads `1` with the probability `q 0/(q 0 + q 1)` (`caseProb`).  The last bit is the logical bit plus
the rest (`bit_eq`), and half the words of each coset have each parity of the rest
(`two_mul_card_cosetRest`), so the parity of the rest tells nothing about the logical bit. -/
theorem lastGivenRest_eq (q : ZMod 2 → ℝ) (s : ZMod 2) :
    code.lastGivenRest q s = caseProb q s := by
  classical
  unfold caseProb
  have hc : (0 : ℝ) < (code.coset 0).card := by
    have := code.two_le_card_coset
    exact_mod_cast (show 0 < (code.coset 0).card by omega)
  have hc2 : ((code.coset 0).card : ℝ) / 2 ≠ 0 := by positivity
  have hm : ∀ t, ((code.cosetRest t s).card : ℝ) = (code.coset 0).card / 2 := fun t => by
    have h := code.two_mul_card_cosetRest t s
    have h' : (2 : ℝ) * (code.cosetRest t s).card = (code.coset 0).card := by exact_mod_cast h
    linarith
  unfold lastGivenRest
  rw [sum_weight, sum_weight, code.filter_last_zero, code.filter_last_v,
    code.filter_rest_zero, code.filter_rest code.v, hm 0, hm code.v]
  rcases zmod2_zero_or_one s with rfl | rfl
  · simp only [ite_true, show ¬ (0 : ZMod 2) = 1 by decide, ite_false, Finset.card_empty,
      Nat.cast_zero, mul_zero, zero_add, hm code.v]
    rw [← add_mul, mul_div_mul_right _ _ hc2]
  · simp only [ite_true, show ¬ (1 : ZMod 2) = 0 by decide, ite_false, Finset.card_empty,
      Nat.cast_zero, mul_zero, add_zero, hm 0]
    rw [← add_mul, mul_div_mul_right _ _ hc2]

/-- **Every reading of the rest of the line occurs in both cosets**: for each word `u`, some word of
`C₀` and some word of `v + C₀` agree with `u` on the rest of the line.  The surface code meets it at
every distance (`surfaceCode_match`): its `X` checks set every pattern of the rest of the line. -/
def Match : Prop :=
  ∀ u : Word n, (∃ x ∈ code.C₀, ∀ i ∈ code.S.erase code.j, x i = u i) ∧
    (∃ x, x - code.v ∈ code.C₀ ∧ ∀ i ∈ code.S.erase code.j, x i = u i)

/-- the rest of the line reads each parity on some word -/
lemma exists_rest (s : ZMod 2) : ∃ u : Word n, code.rest u = s := by
  rcases zmod2_zero_or_one s with rfl | rfl
  · exact ⟨0, by simp [rest, parity]⟩
  · obtain ⟨c, -, hc⟩ := code.rest_flip
    exact ⟨c, hc⟩

/-- **Given the rest of the line, its last bit is the logical bit or its opposite** (Sec. IV.A).
Where every reading of the rest of the line occurs in both cosets (`Match`), the last bit, given the
rest of the line read as in `u`, reads `1` with the probability `caseProb q (code.rest u)`: the
logical bit's when the rest reads `0`, its complement when it reads `1`.  The agreeing words of each
coset are as many as the kernel (`card_agreeing`); on those of `C₀` the last bit is the parity of
the rest, and on those of `v + C₀` the opposite (`bit_of_mem`, `bit_of_mem_v`). -/
theorem bitGiven_rest (hm : code.Match) (q : ZMod 2 → ℝ) (u : Word n) :
    bitGiven code.C₀ code.v q (code.S.erase code.j) u code.j = caseProb q (code.rest u) := by
  classical
  obtain ⟨⟨x₀, hx₀, hx₀u⟩, ⟨x₁, hx₁, hx₁u⟩⟩ := hm u
  have hA0 : x₀ ∈ agreeing code.C₀ (code.S.erase code.j) u 0 := by
    simp only [agreeing, mem_filter, mem_univ, true_and, sub_zero]
    exact ⟨hx₀, hx₀u⟩
  have hAv : x₁ ∈ agreeing code.C₀ (code.S.erase code.j) u code.v := by
    simp only [agreeing, mem_filter, mem_univ, true_and]
    exact ⟨hx₁, hx₁u⟩
  have hc0 := card_agreeing code.C₀ hA0
  have hcv := card_agreeing code.C₀ hAv
  have hrest : ∀ x : Word n, (∀ i ∈ code.S.erase code.j, x i = u i) →
      code.rest x = code.rest u := fun x hx => by
    unfold rest parity
    exact Finset.sum_congr rfl hx
  have hbit0 : ∀ x ∈ agreeing code.C₀ (code.S.erase code.j) u 0, x code.j = code.rest u := by
    intro x hx
    simp only [agreeing, mem_filter, mem_univ, true_and, sub_zero] at hx
    rw [code.bit_of_mem hx.1, hrest x hx.2]
  have hbitv : ∀ x ∈ agreeing code.C₀ (code.S.erase code.j) u code.v,
      x code.j = code.rest u + 1 := by
    intro x hx
    simp only [agreeing, mem_filter, mem_univ, true_and] at hx
    rw [code.bit_of_mem_v hx.1, hrest x hx.2]
  have hk0 : ((kernel code.C₀ (code.S.erase code.j)).card : ℝ) ≠ 0 := by
    have h0 : (0 : Word n) ∈ kernel code.C₀ (code.S.erase code.j) := by simp [kernel]
    exact_mod_cast (Finset.card_pos.2 ⟨0, h0⟩).ne'
  rw [bitGiven_counts]
  unfold caseProb
  rcases zmod2_zero_or_one (code.rest u) with hr | hr
  · have hf0 : (agreeing code.C₀ (code.S.erase code.j) u 0).filter (fun x => x code.j = 1) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x hx
      rw [hbit0 x hx, hr]
      decide
    have hfv : (agreeing code.C₀ (code.S.erase code.j) u code.v).filter (fun x => x code.j = 1) =
        agreeing code.C₀ (code.S.erase code.j) u code.v := by
      apply Finset.filter_true_of_mem
      intro x hx
      rw [hbitv x hx, hr]
      decide
    rw [hf0, hfv, hr, Finset.card_empty, Nat.cast_zero, hc0, hcv]
    simp only [ite_true, mul_zero, zero_add]
    rw [← add_mul, mul_div_mul_right _ _ hk0]
  · have hf0 : (agreeing code.C₀ (code.S.erase code.j) u 0).filter (fun x => x code.j = 1) =
        agreeing code.C₀ (code.S.erase code.j) u 0 := by
      apply Finset.filter_true_of_mem
      intro x hx
      rw [hbit0 x hx, hr]
    have hfv : (agreeing code.C₀ (code.S.erase code.j) u code.v).filter
        (fun x => x code.j = 1) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x hx
      rw [hbitv x hx, hr]
      decide
    rw [hf0, hfv, hr, Finset.card_empty, Nat.cast_zero, hc0, hcv]
    simp only [show ¬ (1 : ZMod 2) = 0 by decide, ite_false, mul_zero, add_zero]
    rw [← add_mul, mul_div_mul_right _ _ hk0]

end LineCode

/-! ### Several logical qubits -/

section Joint

variable (C₀ : AddSubgroup (Word n)) (v : Word n) {K W : Type*}

/-- **The weight of a joint reading of `N` logical qubits** (Sec. IV.A).  The physical bits of the
first `N − 1` logical qubits read `w`, which gives their joint outcome `κ w`, with the weight `g w`;
the block of the last logical qubit reads `x`.  With `p k t` the weight of the joint outcome `k` of
the first `N − 1` logical qubits and `t` of the last, the joint reading has the weight
`g w · weight (p (κ w)) x`: for the state `∑ α_{k,t} |k⟩_L |t⟩_L`, with `p k t = |α_{k,t}|²` and
`g w = |⟨w|κ w⟩_L|²`, the logical states of different outcomes having no word in common, this is
the probability of the reading, the factor `1/|C₀|` left out.  The blocks are read in order: the
earlier blocks in full, then positions of the last. -/
noncomputable def jointWeight (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ) (w : W)
    (x : Word n) : ℝ :=
  g w * weight C₀ v (p (κ w)) x

open Classical in
/-- **The probability that physical bit `j` of the last block reads `1`, given the earlier blocks
and the bits on the positions `P` of the last**, the earlier blocks reading `w` and the positions
`P` reading as in `u` -/
noncomputable def jointBitGiven (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ) (P : Finset (Fin n))
    (w : W) (u : Word n) (j : Fin n) : ℝ :=
  (∑ x ∈ univ.filter (fun x => (∀ i ∈ P, x i = u i) ∧ x j = 1), jointWeight C₀ v p κ g w x) /
    ∑ x ∈ univ.filter (fun x => ∀ i ∈ P, x i = u i), jointWeight C₀ v p κ g w x

/-- **Given the earlier blocks, the last block is a code state with the logical weights of their
outcome** (Sec. IV.A): where the earlier blocks' reading `w` occurs (`g w ≠ 0`), a physical bit of
the last block reads `1` with the probability `bitGiven` of the weights `p (κ w)`. -/
theorem jointBitGiven_eq (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ) (P : Finset (Fin n))
    (w : W) (u : Word n) (j : Fin n) (hg : g w ≠ 0) :
    jointBitGiven C₀ v p κ g P w u j = bitGiven C₀ v (p (κ w)) P u j := by
  unfold jointBitGiven bitGiven jointWeight
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ hg]

/-- **A physical bit, given the earlier physical bits, is fixed, balanced, or equal or opposite to
the logical bit** (Sec. IV.A), for `N` logical qubits: given the reading `w` of the earlier blocks
and `u` of the positions `P` of its own, a physical bit of the last block reads `1` with the
probability `0` or `1`, `1/2`, or the last logical bit's probability given the outcome `κ w` of the
earlier logical qubits, or its complement (`jointBitGiven_eq`, `css_conditional`). -/
theorem css_conditional_joint (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ) (P : Finset (Fin n))
    (w : W) (u : Word n) (j : Fin n) :
    jointBitGiven C₀ v p κ g P w u j = 0 ∨ jointBitGiven C₀ v p κ g P w u j = 1 ∨
      jointBitGiven C₀ v p κ g P w u j = 1 / 2 ∨
      jointBitGiven C₀ v p κ g P w u j = p (κ w) 1 / (p (κ w) 0 + p (κ w) 1) ∨
      jointBitGiven C₀ v p κ g P w u j = p (κ w) 0 / (p (κ w) 0 + p (κ w) 1) := by
  by_cases hg : g w = 0
  · left
    simp [jointBitGiven, jointWeight, hg]
  · rw [jointBitGiven_eq C₀ v p κ g P w u j hg]
    exact css_conditional C₀ v (p (κ w)) P u j

/-- **The conditional states of a physical bit** (Sec. IV.A): its probabilities of reading `1`,
strictly between `0` and `1`, given each reading `w` of the earlier blocks and `u` of the positions
`P` of its own block.  The fixed states, `0` and `1`, are left out: a block of one cell can hold
them, and holds nothing else (`Capacity.one_cell_block`). -/
noncomputable def condStates [Fintype W] (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ)
    (P : Finset (Fin n)) (j : Fin n) : Finset ℝ :=
  ((univ : Finset (W × Word n)).image (fun wu => jointBitGiven C₀ v p κ g P wu.1 wu.2 j)).filter
    (fun r => 0 < r ∧ r < 1)

/-- **A physical string has up to `2^N` conditional states to hold** (Sec. IV.A): for each joint
outcome `k` of the first `N − 1` logical qubits, at most two, the last logical bit's probability
given `k` and its complement, or `1/2` alone (`css_conditional_cases`); so at most
`2 · 2^(N−1) = 2^N`, twice as many as the `2^(N−1)` of a logical string. -/
theorem card_condStates_le [Fintype K] [Fintype W] (N : ℕ) (hN : 1 ≤ N)
    (hK : Fintype.card K = 2 ^ (N - 1)) (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ)
    (P : Finset (Fin n)) (j : Fin n) :
    (condStates C₀ v p κ g P j).card ≤ 2 ^ N := by
  classical
  let T : K → Finset ℝ := fun k =>
    if ∃ c ∈ kernel C₀ P, c j = 1 then {1 / 2}
    else {p k 1 / (p k 0 + p k 1), p k 0 / (p k 0 + p k 1)}
  have hsub : condStates C₀ v p κ g P j ⊆ univ.biUnion T := by
    intro r hr
    simp only [condStates, mem_filter, mem_image, mem_univ, true_and] at hr
    obtain ⟨⟨⟨w, u⟩, rfl⟩, h0, h1⟩ := hr
    simp only [mem_biUnion, mem_univ, true_and]
    refine ⟨κ w, ?_⟩
    by_cases hg : g w = 0
    · exfalso
      simp [jointBitGiven, jointWeight, hg] at h0
    rw [jointBitGiven_eq C₀ v p κ g P w u j hg] at h0 h1 ⊢
    simp only [T]
    split_ifs with hK'
    · rcases (css_conditional_cases C₀ v (p (κ w)) P j).1 hK' u with h | h
      · rw [h] at h0
        exact absurd h0 (lt_irrefl 0)
      · rw [h]
        exact mem_singleton_self _
    · rcases (css_conditional_cases C₀ v (p (κ w)) P j).2 hK' u with h | h | h | h
      · rw [h] at h0
        exact absurd h0 (lt_irrefl 0)
      · rw [h] at h1
        exact absurd h1 (lt_irrefl 1)
      · rw [h]
        simp
      · rw [h]
        simp
  have hT : ∀ k, (T k).card ≤ 2 := by
    intro k
    simp only [T]
    split_ifs
    · simp
    · exact (card_insert_le _ _).trans (by simp)
  calc (condStates C₀ v p κ g P j).card ≤ (univ.biUnion T).card := card_le_card hsub
    _ ≤ ∑ k, (T k).card := card_biUnion_le
    _ ≤ ∑ _k : K, 2 := sum_le_sum fun k _ => hT k
    _ = 2 ^ N := by
      rw [sum_const, card_univ, hK, smul_eq_mul, ← pow_succ]
      congr 1
      omega

/-- **In a repetition code a physical string has no more conditional states than a logical
string** (Sec. IV.A): only the fixed and the equal case occur (`repetition_conditional`), so at most
one for each joint outcome of the first `N − 1` logical qubits, `2^(N−1)` in all. -/
theorem card_condStates_repetition [Fintype K] [Fintype W] (N : ℕ)
    (hK : Fintype.card K = 2 ^ (N - 1)) (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ)
    (P : Finset (Fin n)) (j : Fin n) :
    (condStates ⊥ (fun _ => 1) p κ g P j).card ≤ 2 ^ (N - 1) := by
  classical
  let T : K → Finset ℝ := fun k => {p k 1 / (p k 0 + p k 1)}
  have hsub : condStates ⊥ (fun _ => 1) p κ g P j ⊆ univ.biUnion T := by
    intro r hr
    simp only [condStates, mem_filter, mem_image, mem_univ, true_and] at hr
    obtain ⟨⟨⟨w, u⟩, rfl⟩, h0, h1⟩ := hr
    simp only [mem_biUnion, mem_univ, true_and]
    refine ⟨κ w, ?_⟩
    by_cases hg : g w = 0
    · exfalso
      simp [jointBitGiven, jointWeight, hg] at h0
    rw [jointBitGiven_eq _ _ p κ g P w u j hg] at h0 h1 ⊢
    rcases repetition_conditional (p (κ w)) P u j with h | h | h
    · rw [h] at h0
      exact absurd h0 (lt_irrefl 0)
    · rw [h] at h1
      exact absurd h1 (lt_irrefl 1)
    · rw [h]
      exact mem_singleton_self _
  calc (condStates ⊥ (fun _ => 1) p κ g P j).card ≤ (univ.biUnion T).card := card_le_card hsub
    _ ≤ ∑ k, (T k).card := card_biUnion_le
    _ = 2 ^ (N - 1) := by simp [T, hK]

/-- **Given the earlier blocks and the rest of the line, the last bit of the line is the last
logical bit or its opposite** (Sec. IV.A), for `N` logical qubits: where every reading of the rest of
the line occurs in both cosets (`LineCode.Match`) and the earlier blocks' reading `w` occurs, the last
bit reads `1` with the probability `caseProb (p (κ w)) (code.rest u)` (`jointBitGiven_eq`,
`LineCode.bitGiven_rest`). -/
theorem LineCode.jointBitGiven_rest (code : LineCode n) (hm : code.Match) (p : K → ZMod 2 → ℝ)
    (κ : W → K) (g : W → ℝ) (w : W) (u : Word n) (hg : g w ≠ 0) :
    jointBitGiven code.C₀ code.v p κ g (code.S.erase code.j) w u code.j =
      caseProb (p (κ w)) (code.rest u) := by
  rw [jointBitGiven_eq _ _ p κ g _ w u _ hg, code.bitGiven_rest hm]

/-- **The last bit of a line has `2^N` conditional states to hold** (Sec. IV.A): where every reading
of the rest of the line occurs in both cosets (`LineCode.Match`), every outcome `k` of the earlier
logical qubits occurs (`hg`) with the last logical bit uncertain given it (`hp`), and the `2^N`
probabilities `caseProb (p k) s` differ (`hdist`), as in a random state, the last bit of the line,
given the earlier blocks and the rest of the line, has these `2^N` probabilities as its conditional
states strictly between `0` and `1`, the most that `card_condStates_le` allows. -/
theorem LineCode.card_lineStates [Fintype K] [Fintype W] (code : LineCode n) (hm : code.Match)
    (N : ℕ) (hN : 1 ≤ N) (hK : Fintype.card K = 2 ^ (N - 1)) (p : K → ZMod 2 → ℝ)
    (hp : ∀ k t, 0 < p k t) (κ : W → K) (g : W → ℝ) (hg : ∀ k, ∃ w, κ w = k ∧ g w ≠ 0)
    (hdist : Function.Injective (fun σ : K × ZMod 2 => caseProb (p σ.1) σ.2)) :
    (condStates code.C₀ code.v p κ g (code.S.erase code.j) code.j).card = 2 ^ N := by
  apply le_antisymm (card_condStates_le code.C₀ code.v N hN hK p κ g _ _)
  have hsub : univ.image (fun σ : K × ZMod 2 => caseProb (p σ.1) σ.2) ⊆
      condStates code.C₀ code.v p κ g (code.S.erase code.j) code.j := by
    intro r hr
    obtain ⟨σ, -, rfl⟩ := mem_image.1 hr
    obtain ⟨w, hw, hgw⟩ := hg σ.1
    obtain ⟨u, hu⟩ := code.exists_rest σ.2
    refine mem_filter.2 ⟨mem_image.2 ⟨(w, u), mem_univ _, ?_⟩, caseProb_pos_lt_one (hp σ.1) σ.2⟩
    rw [code.jointBitGiven_rest hm p κ g w u hgw, hw, hu]
  calc 2 ^ N = (univ.image (fun σ : K × ZMod 2 => caseProb (p σ.1) σ.2)).card := by
        rw [card_image_of_injective _ hdist, card_univ, Fintype.card_prod, hK, ZMod.card,
          ← pow_succ]
        congr 1
        omega
    _ ≤ _ := card_le_card hsub

end Joint

/-! ### The ceiling -/

/-- **A string needs two cells for each of its conditional states strictly between `0` and `1`**
(Sec. IV.A, the test: whether each string has room for the different conditional states of its
qubit).  Each cell of the string is paired with an outcome `λ` of the earlier bits (`e`), with the
conditional state `c λ`, the probability that the string's bit is `1` given `λ`.  The block of a
conditional state `r` is the set of cells whose outcome has that state (`Capacity.block e c r`):
the paper's blocks of the outcomes that have the state, taken together.  The bits are the possible
outcomes of one measurement, and the cells of a block are the possible outcomes given the
condition that names it (Postulate 1).  The hypothesis `hshare` is that, for every conditional
state strictly between `0` and `1`, the share of 1s on its block lies strictly between `0` and `1`
too: the block shows the state.  A block that holds the state, with the share `r`, shows it, and
the count uses only that the block has both values of the bit.  The results of `Main.lean` on
codes derive `hshare` from a premise and a condition (`shows_of_outcomes`, below).  A block that
shows its state has both values, so it has two cells (`Capacity.two_le_card_of_frac`).  The
blocks of different states are disjoint (`Capacity.disjoint_blocks`), so the string has two cells
for each state. -/
theorem two_mul_card_states_le {Λ Cell : Type*} [Fintype Λ] [Fintype Cell] [DecidableEq Cell]
    (c : Λ → ℝ)
    (e : Cell → Λ) (b : Cell → Bool)
    (hshare : ∀ r ∈ univ.image c, 0 < r → r < 1 →
      0 < Capacity.frac b (Capacity.block e c r) ∧ Capacity.frac b (Capacity.block e c r) < 1) :
    2 * ((univ.image c).filter (fun r => 0 < r ∧ r < 1)).card ≤ Fintype.card Cell := by
  set T := (univ.image c).filter (fun r => 0 < r ∧ r < 1) with hT
  have hdisj : (T : Set ℝ).PairwiseDisjoint (fun r => Capacity.block e c r) :=
    fun r _ r' _ hrr' => Capacity.disjoint_blocks e c hrr'
  have h2 : ∀ r ∈ T, 2 ≤ (Capacity.block e c r).card := by
    intro r hr
    rw [hT, mem_filter] at hr
    have h := hshare r hr.1 hr.2.1 hr.2.2
    exact (Capacity.two_le_card_of_frac b _ h.1 h.2).1
  calc 2 * T.card = ∑ _r ∈ T, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ r ∈ T, (Capacity.block e c r).card := sum_le_sum h2
    _ = (T.biUnion (fun r => Capacity.block e c r)).card := (card_biUnion hdisj).symm
    _ ≤ (univ : Finset Cell).card := card_le_card (subset_univ _)
    _ = Fintype.card Cell := card_univ

/-- **Where each conditional state strictly between `0` and `1` occurs with either value of the
bit, the string shows each on its block**: the hypothesis `hshare` of `two_mul_card_states_le`,
from the two hypotheses of the results of `Main.lean` on codes.  `pr r v` is the probability, in
the state that the register holds, that the earlier bits read some `ρ` with the conditional state
`c ρ = r` and the string's bit is `v`.  Every conditional state strictly between `0` and `1`
occurs with either value of the bit (`hcond`, the condition
`Sources.Condition.conditional_states`).  A conditional state that occurs with a value of the bit
is at a cell with that value (`hout`, the premise `Sources.P1.outcomes_at_positions`, taken with
the conditional state as the outcome that a cell is paired with).  So the block of each such
state has a cell that reads `1` and a cell that reads `−1` (`Capacity.outcomes_iff_cells`), and
its share of 1s lies strictly between `0` and `1` (`Capacity.frac_pos_lt_one`).  The statement
says nothing else of `pr`: it occurs only in `hcond` and `hout`. -/
lemma shows_of_outcomes {Λ Cell : Type*} [Fintype Λ] [Fintype Cell] {c : Λ → ℝ} (e : Cell → Λ)
    (b : Cell → Bool) (pr : ℝ → Bool → ℝ)
    (hcond : ∀ ρ, 0 < c ρ → c ρ < 1 → 0 < pr (c ρ) true ∧ 0 < pr (c ρ) false)
    (hout : ∀ r v, 0 < pr r v → ∃ x, c (e x) = r ∧ b x = v) :
    ∀ r ∈ univ.image c, 0 < r → r < 1 →
      0 < Capacity.frac b (Capacity.block e c r) ∧ Capacity.frac b (Capacity.block e c r) < 1 := by
  intro r hr h0 h1
  obtain ⟨ρ, -, rfl⟩ := mem_image.1 hr
  obtain ⟨⟨x, hx, hbx⟩, ⟨y, hy, hby⟩⟩ :=
    (Capacity.outcomes_iff_cells (fun x => c (e x)) b {r | ∃ ρ, c ρ = r ∧ 0 < r ∧ r < 1}).1
      ⟨pr, fun r hr => by
        obtain ⟨ρ, rfl, h0, h1⟩ := hr
        exact hcond ρ h0 h1, hout⟩ (c ρ) ⟨ρ, rfl, h0, h1⟩
  exact Capacity.frac_pos_lt_one b _ (mem_filter.2 ⟨mem_univ x, hx⟩) hbx
    (mem_filter.2 ⟨mem_univ y, hy⟩) hby

/-- **Two cells for each conditional state are enough**: the two hypotheses of `shows_of_outcomes`
can be met together, with no more cells than `two_mul_card_states_le` counts.  Take any
assignment `c` of conditional states to the readings.  There is a string with exactly two cells
for each conditional state strictly between `0` and `1`, with a pairing `e` of its cells with
readings, bits `b` and weights `pr`.  On it every such state occurs with either value of the
bit, and a state that occurs with a value is at a cell with that value.  The two statements are
`Sources.P1.outcomes_at_positions pr (fun x => c (e x)) b` and
`Sources.Condition.conditional_states pr c` written out, since `Sources.lean` stands after this
file.  So the two hypotheses ask no more cells than the room that the results of `Main.lean` on
codes conclude.  The statement says only that the two hypotheses can be met with that number of
cells.  The proof builds the model with weights `0` and `1`, not the probabilities of a state,
and with one cell of either bit on each block, so that a block of the model shows its state and
holds it only if the state is `1/2`. -/
theorem two_cells_each_model {Λ : Type*} [Fintype Λ] (c : Λ → ℝ) :
    ∃ (Cell : Type) (_ : Fintype Cell) (e : Cell → Λ) (b : Cell → Bool) (pr : ℝ → Bool → ℝ),
      (∀ r v, 0 < pr r v → ∃ x, c (e x) = r ∧ b x = v) ∧
      (∀ ρ, 0 < c ρ → c ρ < 1 → 0 < pr (c ρ) true ∧ 0 < pr (c ρ) false) ∧
      Fintype.card Cell = 2 * ((univ.image c).filter (fun r => 0 < r ∧ r < 1)).card := by
  classical
  set T := (univ.image c).filter (fun r => 0 < r ∧ r < 1) with hT
  have hsel : ∀ r : T, ∃ ρ, c ρ = r.1 := fun r => by
    obtain ⟨ρ, -, h⟩ := mem_image.1 (mem_filter.1 r.2).1
    exact ⟨ρ, h⟩
  choose sel hsel using hsel
  refine ⟨T × Bool, inferInstance, fun x => sel x.1, fun x => x.2,
    fun r _ => if r ∈ T then 1 else 0, ?_, ?_, ?_⟩
  · intro r v h
    have hr : r ∈ T := by
      by_contra hr
      simp [hr] at h
    exact ⟨(⟨r, hr⟩, v), hsel ⟨r, hr⟩, rfl⟩
  · intro ρ h0 h1
    have hρ : c ρ ∈ T := mem_filter.2 ⟨mem_image.2 ⟨ρ, mem_univ _, rfl⟩, h0, h1⟩
    simp [hρ]
  · rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, mul_comm]

/-- **Where the equal and the opposite case both occur, the ceiling is `2^(N+1) ≤ L`**
(Sec. IV.A).  Take `N` logical qubits, each in its own block of a Calderbank–Shor–Steane code, with
`K` the joint outcomes of the first `N − 1`, `2^(N−1)` of them, and the joint weights of
`jointWeight`; in a random state every outcome `k` occurs with the last logical bit uncertain given
it (`hp`).  Take a physical bit `j` of the last block and the positions `P` of its block read before
it.  If, for every `k`, both the equal and the opposite case occur, some reading of the earlier bits
giving bit `j` the probability `caseProb (p k) 0` and some `caseProb (p k) 1` (`hboth`), and these
`2^N` probabilities differ (`hdist`), as in a random state, then bit `j` has `2^N` conditional
states strictly between `0` and `1` at least.  If its string, of `L` cells each reading the earlier
blocks and the positions `P` (`e`), shows each of them on its block, the share of 1s there
strictly between `0` and `1` (`hshare`, which the results of `Main.lean` derive from Postulate
1), `2^(N+1) ≤ L` (`two_mul_card_states_le`). -/
theorem ceiling_both_cases {K W Cell : Type*} [Fintype K] [Fintype W] [Fintype Cell]
    [DecidableEq Cell] (N L : ℕ) (hN : 1 ≤ N) (hL : Fintype.card Cell = L) (hK : Fintype.card K = 2 ^ (N - 1))
    (C₀ : AddSubgroup (Word n)) (v : Word n) (P : Finset (Fin n)) (j : Fin n)
    (p : K → ZMod 2 → ℝ) (hp : ∀ k t, 0 < p k t) (κ : W → K) (g : W → ℝ)
    (hboth : ∀ σ : K × ZMod 2, ∃ wu : W × Word n,
      jointBitGiven C₀ v p κ g P wu.1 wu.2 j = caseProb (p σ.1) σ.2)
    (hdist : Function.Injective (fun σ : K × ZMod 2 => caseProb (p σ.1) σ.2))
    (e : Cell → W × Word n) (b : Cell → Bool)
    (hshare : ∀ r ∈ univ.image (fun wu : W × Word n => jointBitGiven C₀ v p κ g P wu.1 wu.2 j),
      0 < r → r < 1 →
      0 < Capacity.frac b
          (Capacity.block e (fun wu => jointBitGiven C₀ v p κ g P wu.1 wu.2 j) r) ∧
        Capacity.frac b
          (Capacity.block e (fun wu => jointBitGiven C₀ v p κ g P wu.1 wu.2 j) r) < 1) :
    2 ^ (N + 1) ≤ L := by
  have hcount := two_mul_card_states_le _ e b hshare
  have hsub : univ.image (fun σ : K × ZMod 2 => caseProb (p σ.1) σ.2) ⊆
      (univ.image (fun wu : W × Word n => jointBitGiven C₀ v p κ g P wu.1 wu.2 j)).filter
        (fun r => 0 < r ∧ r < 1) := by
    intro r hr
    obtain ⟨σ, -, rfl⟩ := mem_image.1 hr
    obtain ⟨wu, hwu⟩ := hboth σ
    exact mem_filter.2 ⟨mem_image.2 ⟨wu, mem_univ _, hwu⟩, caseProb_pos_lt_one (hp σ.1) σ.2⟩
  have hcard : (univ.image (fun σ : K × ZMod 2 => caseProb (p σ.1) σ.2)).card = 2 ^ N := by
    rw [card_image_of_injective _ hdist, card_univ, Fintype.card_prod, hK, ZMod.card, ← pow_succ]
    congr 1
    omega
  have hle := card_le_card hsub
  rw [hcard] at hle
  rw [← hL, pow_succ, mul_comm]
  exact (Nat.mul_le_mul_left 2 hle).trans hcount

/-- **The ceiling for logical qubits read as the parity of a line** (Sec. IV.A): `ceiling_both_cases`
for the last bit of a line, with the rest of the line read before it.  Where every reading of the
rest occurs in both cosets (`LineCode.Match`), as in the surface code (`surfaceCode_match`), the
last bit, given the earlier blocks and the rest of the line, is the last logical bit when the rest
reads `0` and its opposite when it reads `1` (`LineCode.jointBitGiven_rest`), so both cases occur for
every outcome `k`, each of which occurs (`hg`).  Where the `2^N` probabilities differ (`hdist`), as
in a random state, and the string shows each conditional state on its block, the share of 1s
there strictly between `0` and `1` (`hshare`), `2^(N+1) ≤ L`. -/
theorem ceiling_line_code {K W Cell : Type*} [Fintype K] [Fintype W] [Fintype Cell]
    [DecidableEq Cell] (N L : ℕ) (hN : 1 ≤ N) (hL : Fintype.card Cell = L) (hK : Fintype.card K = 2 ^ (N - 1))
    (code : LineCode n) (hm : code.Match) (p : K → ZMod 2 → ℝ) (hp : ∀ k t, 0 < p k t)
    (κ : W → K) (g : W → ℝ) (hg : ∀ k, ∃ w, κ w = k ∧ g w ≠ 0)
    (hdist : Function.Injective (fun σ : K × ZMod 2 => caseProb (p σ.1) σ.2))
    (e : Cell → W × Word n) (b : Cell → Bool)
    (hshare : ∀ r ∈ univ.image (fun wu : W × Word n =>
        jointBitGiven code.C₀ code.v p κ g (code.S.erase code.j) wu.1 wu.2 code.j),
      0 < r → r < 1 →
      0 < Capacity.frac b (Capacity.block e (fun wu =>
          jointBitGiven code.C₀ code.v p κ g (code.S.erase code.j) wu.1 wu.2 code.j) r) ∧
        Capacity.frac b (Capacity.block e (fun wu =>
          jointBitGiven code.C₀ code.v p κ g (code.S.erase code.j) wu.1 wu.2 code.j) r) < 1) :
    2 ^ (N + 1) ≤ L :=
  ceiling_both_cases N L hN hL hK code.C₀ code.v _ code.j p hp κ g
    (fun σ => by
      obtain ⟨w, hw, hgw⟩ := hg σ.1
      obtain ⟨u, hu⟩ := code.exists_rest σ.2
      exact ⟨(w, u), by rw [code.jointBitGiven_rest hm p κ g w u hgw, hw, hu]⟩)
    hdist e b hshare

/-! ### Codes and models -/

/-- **The two-bit line code**: the logical `0` the words `00` and `11`, the logical `1` the words
`10` and `01`, the logical bit the parity of both bits, the second bit not fixed by the code -/
def lineTwo : LineCode 2 where
  C₀ := AddSubgroup.zmultiples (fun _ => 1)
  v := fun i => if i = 0 then 1 else 0
  S := univ
  j := 1
  hj := mem_univ _
  hC := by
    intro c hc
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hc
    simp only [parity, Pi.smul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [two_nsmul, zmod2_add_self]
  hv := by
    simp [parity, Finset.sum_ite_eq']
  hfree := ⟨fun _ => 1, AddSubgroup.mem_zmultiples _, rfl⟩


/-- **The two-bit line code meets `LineCode.Match`**: the rest of its line is its first bit, which
reads `0` on `00` and on `01` and `1` on `11` and on `10` -/
lemma lineTwo_match : lineTwo.Match := by
  intro u
  have hS : lineTwo.S.erase lineTwo.j = {0} := by decide
  rw [hS]
  simp only [Finset.mem_singleton, forall_eq]
  rcases zmod2_zero_or_one (u 0) with h | h
  · refine ⟨⟨0, zero_mem _, by rw [h]; rfl⟩, ⟨fun i => if i = 0 then 0 else 1, ?_, by rw [h]; rfl⟩⟩
    have hx : (fun i : Fin 2 => if i = 0 then (0 : ZMod 2) else 1) - lineTwo.v = fun _ => 1 := by
      funext i
      fin_cases i <;> decide
    rw [hx]
    exact AddSubgroup.mem_zmultiples _
  · refine ⟨⟨fun _ => 1, AddSubgroup.mem_zmultiples _, by rw [h]⟩, ⟨lineTwo.v, by simp, ?_⟩⟩
    rw [h]
    decide

/-! ### The surface code at every distance -/

/-- the word of `m` bits that reads `1` at the positions numbered by `s` and `0` elsewhere -/
def wordAt (m : ℕ) (s : Finset ℕ) : Word m := fun i => if i.val ∈ s then 1 else 0

namespace Surface

variable (d : ℕ)

/-- the plaquette with its top left corner in row `r` and column `c`, the qubits numbered `r d + c`
row by row -/
def plaq (r c : ℕ) : Finset ℕ :=
  {r * d + c, r * d + c + 1, (r + 1) * d + c, (r + 1) * d + c + 1}

/-- the check of the top boundary at column `c` -/
def top (c : ℕ) : Finset ℕ := {c, c + 1}

/-- the check of the bottom boundary at column `c` -/
def bot (c : ℕ) : Finset ℕ := {(d - 1) * d + c, (d - 1) * d + c + 1}

/-- the `X` checks of the rotated surface code on `d × d` qubits: the plaquettes at `(r, c)` with
`r + c` odd, the top checks at the even columns, and the bottom checks at the columns `c` with
`d + c` even, the odd columns for odd `d` -/
def xChecks : Set (Word (d * d)) :=
  {w | ∃ r c, r < d - 1 ∧ c < d - 1 ∧ (r + c) % 2 = 1 ∧ w = wordAt (d * d) (plaq d r c)} ∪
  {w | ∃ c, c < d - 1 ∧ c % 2 = 0 ∧ w = wordAt (d * d) (top c)} ∪
  {w | ∃ c, c < d - 1 ∧ (d + c) % 2 = 0 ∧ w = wordAt (d * d) (bot d c)}

/-- the check that reads `1` on the bits `c` and `c + 1` of the top row: the top check at an even
column, the plaquette of the first row at an odd one -/
def rowCheck (c : ℕ) : Word (d * d) :=
  wordAt (d * d) (if c % 2 = 0 then top c else plaq d 0 c)

/-- the logical `X`, on the left column -/
def logicalX : Word (d * d) := wordAt (d * d) ((range d).image (· * d))

/-- the top row, on which the logical `Z` acts -/
def row : Finset (Fin (d * d)) := univ.filter (fun i => i.val < d)

lemma rowCheck_mem {c : ℕ} (hc : c < d - 1) : rowCheck d c ∈ xChecks d := by
  unfold rowCheck
  split_ifs with h
  · exact Or.inl (Or.inr ⟨c, hc, h, rfl⟩)
  · exact Or.inl (Or.inl ⟨0, c, by omega, hc, by omega, rfl⟩)

lemma rowCheck_apply {c : ℕ} (i : Fin (d * d)) (hi : i.val < d) :
    rowCheck d c i = if i.val = c ∨ i.val = c + 1 then 1 else 0 := by
  have hmem : i.val ∈ (if c % 2 = 0 then top c else plaq d 0 c) ↔
      (i.val = c ∨ i.val = c + 1) := by
    split_ifs
    · simp [top]
    · simp only [plaq, Finset.mem_insert, Finset.mem_singleton, zero_mul, zero_add, one_mul]
      omega
  unfold rowCheck wordAt
  simp only [hmem]

/-- the parity of a word on the top row: the number of its positions below `d`, mod 2 -/
lemma parity_row (s : Finset ℕ) :
    parity (row d) (wordAt (d * d) s) = ((s.filter (· < d)).card : ZMod 2) := by
  classical
  unfold parity wordAt row
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_filter]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact ⟨hi.2, hi.1⟩
  · intro i _ i' _ h
    exact Fin.ext h
  · intro m hm
    simp only [mem_filter] at hm
    exact ⟨⟨m, lt_of_lt_of_le hm.2 (Nat.le_mul_self d)⟩, by simp [hm.1, hm.2], rfl⟩

/-- every `X` check meets the top row in an even number of qubits: two for the top checks and the
plaquettes of the first row, none for the others -/
lemma parity_row_xCheck (hd : 2 ≤ d) {w : Word (d * d)} (hw : w ∈ xChecks d) :
    parity (row d) w = 0 := by
  rcases hw with (⟨r, c, hr, hc, hodd, rfl⟩ | ⟨c, hc, heven, rfl⟩) | ⟨c, hc, hodd, rfl⟩
  · rw [parity_row]
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · have hf : (plaq d 0 c).filter (· < d) = {c, c + 1} := by
        ext m
        simp only [plaq, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, zero_mul,
          zero_add, one_mul]
        omega
      rw [hf, Finset.card_pair (by omega)]
      decide
    · have h1 : d ≤ r * d := Nat.le_mul_of_pos_left d hr0
      have h2 : (r + 1) * d = r * d + d := by ring
      have hf : (plaq d r c).filter (· < d) = ∅ := by
        apply Finset.filter_false_of_mem
        intro m hm
        simp only [plaq, Finset.mem_insert, Finset.mem_singleton] at hm
        omega
      rw [hf, Finset.card_empty, Nat.cast_zero]
  · rw [parity_row]
    have hf : (top c).filter (· < d) = {c, c + 1} := by
      ext m
      simp only [top, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hf, Finset.card_pair (by omega)]
    decide
  · rw [parity_row]
    have h1 : d ≤ (d - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    have hf : (bot d c).filter (· < d) = ∅ := by
      apply Finset.filter_false_of_mem
      intro m hm
      simp only [bot, Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    rw [hf, Finset.card_empty, Nat.cast_zero]

/-- the logical `X` meets the top row in one qubit, the corner -/
lemma parity_row_logicalX (hd : 2 ≤ d) : parity (row d) (logicalX d) = 1 := by
  unfold logicalX
  rw [parity_row]
  have hf : ((range d).image (· * d)).filter (· < d) = {0} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hlt⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp
      · have := Nat.le_mul_of_pos_left d hr0
        omega
    · rintro rfl
      exact ⟨⟨0, by omega, by simp⟩, by omega⟩
  rw [hf, Finset.card_singleton, Nat.cast_one]

end Surface

/-- **The surface code of distance `d`** (Sec. IV.A), for every `d ≥ 2`: the rotated surface code on
`d × d` physical qubits, numbered row by row.  The words of the logical `0` are those its `X`
checks generate; the logical `1` is their coset by the logical `X`, on the left column; the logical
bit is the parity of the top row, on which the logical `Z` acts, since every `X` check meets the
row evenly and the logical `X` meets it once; and the check at column `d − 2` sets the last bit of
the row, so the code does not fix it. -/
def surfaceCode (d : ℕ) (hd : 2 ≤ d) : LineCode (d * d) where
  C₀ := AddSubgroup.closure (Surface.xChecks d)
  v := Surface.logicalX d
  S := Surface.row d
  j := ⟨d - 1, lt_of_lt_of_le (by omega) (Nat.le_mul_self d)⟩
  hj := by simp only [Surface.row, mem_filter, mem_univ, true_and]; omega
  hC := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem w hw => exact Surface.parity_row_xCheck d hd hw
    | zero => simp [parity]
    | add x y _ _ hx hy => rw [parity_add, hx, hy, add_zero]
    | neg x _ hx => rw [parity_neg, hx, neg_zero]
  hv := Surface.parity_row_logicalX d hd
  hfree := ⟨Surface.rowCheck d (d - 2),
    AddSubgroup.subset_closure (Surface.rowCheck_mem d (by omega)), by
      rw [Surface.rowCheck_apply d _ (by simp only; omega)]
      simp only
      split_ifs with h
      · rfl
      · exact absurd (Or.inr (by omega)) h⟩

/-- **Every reading of the rest of the row occurs in both cosets of the surface code**, at every
distance (`LineCode.Match`): the checks along the row read `1` on its bits `c` and `c + 1`, so,
adding them from the left, `C₀` has every pattern of the first `k` bits of the row, for each
`k ≤ d − 1`; and `v + C₀` has every pattern too, `v` being added to a word of `C₀`. -/
theorem surfaceCode_match (d : ℕ) (hd : 2 ≤ d) : (surfaceCode d hd).Match := by
  have key : ∀ k, k ≤ d - 1 → ∀ u : Word (d * d),
      ∃ x ∈ (surfaceCode d hd).C₀, ∀ i : Fin (d * d), i.val < k → x i = u i := by
    intro k
    induction k with
    | zero => exact fun _ u => ⟨0, zero_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk u
      obtain ⟨x, hx, hxu⟩ := ih (by omega) u
      have hkd : k < d := by omega
      let ik : Fin (d * d) := ⟨k, lt_of_lt_of_le hkd (Nat.le_mul_self d)⟩
      by_cases hxk : x ik = u ik
      · refine ⟨x, hx, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact hxu i h
        · have : i = ik := Fin.ext h
          rw [this]
          exact hxk
      · refine ⟨x + Surface.rowCheck d k,
          add_mem hx (AddSubgroup.subset_closure (Surface.rowCheck_mem d (by omega))),
          fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · rw [Pi.add_apply, Surface.rowCheck_apply d i (by omega), hxu i h]
          split_ifs with h'
          · omega
          · rw [add_zero]
        · have hi' : i = ik := Fin.ext h
          rw [hi', Pi.add_apply, Surface.rowCheck_apply d ik (by simp only [ik]; omega)]
          simp only [ik, true_or, ite_true]
          rw [(zmod2_not_eq_iff _ _).1 hxk, add_assoc, zmod2_add_self, add_zero]
  have hrest : ∀ i : Fin (d * d), i ∈ (surfaceCode d hd).S.erase (surfaceCode d hd).j →
      i.val < d - 1 := by
    intro i hi
    simp only [surfaceCode, Surface.row, Finset.mem_erase, mem_filter, mem_univ, true_and,
      ne_eq, Fin.ext_iff] at hi
    omega
  intro u
  obtain ⟨x, hx, hxu⟩ := key (d - 1) le_rfl u
  obtain ⟨y, hy, hyu⟩ := key (d - 1) le_rfl (u - (surfaceCode d hd).v)
  refine ⟨⟨x, hx, fun i hi => hxu i (hrest i hi)⟩,
    ⟨(surfaceCode d hd).v + y, by rw [add_sub_cancel_left]; exact hy, fun i hi => ?_⟩⟩
  rw [Pi.add_apply, hyu i (hrest i hi), Pi.sub_apply, add_sub_cancel]

/-- the logical weights of the model: `2/3` and `1/3` for the outcome `0` of the first logical
qubit, `3/4` and `1/4` for its outcome `1` -/
noncomputable def modelWeights (k t : ZMod 2) : ℝ :=
  if k = 0 then (if t = 0 then 2 / 3 else 1 / 3) else (if t = 0 then 3 / 4 else 1 / 4)

/-- **The hypotheses of `ceiling_line_code` can be met together**, so it does not hold vacuously:
two logical qubits, each in the two-bit line code `lineTwo`, which meets `LineCode.Match`
(`lineTwo_match`, `hm`); the logical weights `modelWeights`, all positive (`hp`); the first block's
four words, which occur with the weight `1` and give its logical bit as their parity, so that each
outcome occurs (`hg`); the four probabilities `caseProb`, `1/3`, `2/3`, `1/4` and `3/4`, all
different (`hdist`); and a string of `14` cells, three reading each outcome with the probability
`1/3` or `2/3` and four each with `1/4` or `3/4`, so that each conditional state's block has that
state as its fraction, strictly between `0` and `1`, which gives `hshare`.  The theorem itself is
applied, and returns `2³ ≤ 14`. -/
theorem ceiling_line_code_model :
    lineTwo.Match ∧ (∀ k t, 0 < modelWeights k t) ∧
    (∀ k : ZMod 2, ∃ w : Word 2, parity univ w = k ∧ (fun _ => (1 : ℝ)) w ≠ 0) ∧
    Function.Injective (fun σ : ZMod 2 × ZMod 2 => caseProb (modelWeights σ.1) σ.2) ∧
    ∃ (e : Fin 14 → Word 2 × Word 2) (b : Fin 14 → Bool),
      (∀ k s : ZMod 2, Capacity.frac b (Capacity.block e (fun wu =>
          jointBitGiven lineTwo.C₀ lineTwo.v modelWeights (parity univ) (fun _ => 1)
            (lineTwo.S.erase lineTwo.j) wu.1 wu.2 lineTwo.j) (caseProb (modelWeights k) s)) =
        caseProb (modelWeights k) s) ∧ 2 ^ (2 + 1) ≤ 14 := by
  have hcv : ∀ wu : Word 2 × Word 2,
      jointBitGiven lineTwo.C₀ lineTwo.v modelWeights (parity univ) (fun _ => 1)
        (lineTwo.S.erase lineTwo.j) wu.1 wu.2 lineTwo.j =
      caseProb (modelWeights (parity univ wu.1)) (lineTwo.rest wu.2) := fun wu =>
    lineTwo.jointBitGiven_rest lineTwo_match modelWeights (parity univ) (fun _ => 1) wu.1 wu.2
      one_ne_zero
  have hdist : Function.Injective
      (fun σ : ZMod 2 × ZMod 2 => caseProb (modelWeights σ.1) σ.2) := by
    intro σ τ h
    obtain ⟨k, s⟩ := σ
    obtain ⟨k', s'⟩ := τ
    simp only at h
    rcases zmod2_zero_or_one k with rfl | rfl <;> rcases zmod2_zero_or_one s with rfl | rfl <;>
      rcases zmod2_zero_or_one k' with rfl | rfl <;> rcases zmod2_zero_or_one s' with rfl | rfl <;>
      first | rfl | (exfalso; norm_num [caseProb, modelWeights] at h)
  let e0 : Word 2 := fun i => if i = 0 then 1 else 0
  let e : Fin 14 → Word 2 × Word 2 := fun x =>
    (if x.val < 6 then 0 else e0, if x.val < 3 ∨ (6 ≤ x.val ∧ x.val < 10) then 0 else e0)
  let b : Fin 14 → Bool := fun x =>
    decide (x.val = 0 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 6 ∨ x.val = 10 ∨ x.val = 11 ∨ x.val = 12)
  have hblock : ∀ k s : ZMod 2, Capacity.block e (fun wu =>
      jointBitGiven lineTwo.C₀ lineTwo.v modelWeights (parity univ) (fun _ => 1)
        (lineTwo.S.erase lineTwo.j) wu.1 wu.2 lineTwo.j) (caseProb (modelWeights k) s) =
      univ.filter (fun x => (parity univ (e x).1, lineTwo.rest (e x).2) = (k, s)) := by
    intro k s
    ext x
    simp only [Capacity.block, mem_filter, mem_univ, true_and, hcv]
    constructor
    · intro h
      exact @hdist (parity univ (e x).1, lineTwo.rest (e x).2) (k, s) h
    · intro h
      rw [Prod.mk.injEq] at h
      rw [h.1, h.2]
  have hmain : ∀ k s : ZMod 2, Capacity.frac b (Capacity.block e (fun wu =>
      jointBitGiven lineTwo.C₀ lineTwo.v modelWeights (parity univ) (fun _ => 1)
        (lineTwo.S.erase lineTwo.j) wu.1 wu.2 lineTwo.j) (caseProb (modelWeights k) s)) =
      caseProb (modelWeights k) s := by
    intro k s
    rw [hblock]
    unfold Capacity.frac
    rcases zmod2_zero_or_one k with rfl | rfl <;> rcases zmod2_zero_or_one s with rfl | rfl
    · rw [show univ.filter (fun x => (parity univ (e x).1, lineTwo.rest (e x).2) = (0, 0)) =
          ({0, 1, 2} : Finset (Fin 14)) by decide,
        show (({0, 1, 2} : Finset (Fin 14)).filter (fun x => b x = true)).card = 1 by decide,
        show ({0, 1, 2} : Finset (Fin 14)).card = 3 by decide]
      norm_num [caseProb, modelWeights]
    · rw [show univ.filter (fun x => (parity univ (e x).1, lineTwo.rest (e x).2) = (0, 1)) =
          ({3, 4, 5} : Finset (Fin 14)) by decide,
        show (({3, 4, 5} : Finset (Fin 14)).filter (fun x => b x = true)).card = 2 by decide,
        show ({3, 4, 5} : Finset (Fin 14)).card = 3 by decide]
      norm_num [caseProb, modelWeights]
    · rw [show univ.filter (fun x => (parity univ (e x).1, lineTwo.rest (e x).2) = (1, 0)) =
          ({6, 7, 8, 9} : Finset (Fin 14)) by decide,
        show (({6, 7, 8, 9} : Finset (Fin 14)).filter (fun x => b x = true)).card = 1 by decide,
        show ({6, 7, 8, 9} : Finset (Fin 14)).card = 4 by decide]
      norm_num [caseProb, modelWeights]
    · rw [show univ.filter (fun x => (parity univ (e x).1, lineTwo.rest (e x).2) = (1, 1)) =
          ({10, 11, 12, 13} : Finset (Fin 14)) by decide,
        show (({10, 11, 12, 13} : Finset (Fin 14)).filter (fun x => b x = true)).card = 3 by
          decide,
        show ({10, 11, 12, 13} : Finset (Fin 14)).card = 4 by decide]
      norm_num [caseProb, modelWeights]
  have hp : ∀ k t, 0 < modelWeights k t := by
    intro k t
    unfold modelWeights
    split_ifs <;> norm_num
  have hg : ∀ k : ZMod 2, ∃ w : Word 2, parity univ w = k ∧ (fun _ => (1 : ℝ)) w ≠ 0 := by
    intro k
    refine ⟨fun i => if i = 0 then k else 0, ?_, one_ne_zero⟩
    simp only [parity]
    rw [Finset.sum_ite_eq']
    simp
  refine ⟨lineTwo_match, hp, hg, hdist, e, b, hmain,
    ceiling_line_code 2 14 (by norm_num) (by simp) (by rw [ZMod.card]; norm_num)
    lineTwo lineTwo_match modelWeights hp (parity univ) (fun _ => 1) hg hdist e b
    fun r hr _ _ => ?_⟩
  simp only [mem_image, mem_univ, true_and] at hr
  obtain ⟨wu, rfl⟩ := hr
  rw [hcv wu, hmain _ _]
  exact caseProb_pos_lt_one (hp _) _

end Coding
end Register
