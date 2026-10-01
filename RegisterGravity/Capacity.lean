import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The qubit ceiling (Sec. IV.A, and the remarks of Sec. V)

Formal counterpart of the paragraph of Sec. IV.A that derives the bound `2^N ≤ L`, and of the
remarks of Sec. V on how soft the bound is and on Palmer's bit count.

When a state is measured jointly (Postulate 1), the strings are read together bit by bit, so every
bit of a later string is paired with one outcome of the earlier qubits; this pairing is how the
paper reads "measured jointly", a joint measurement being one measurement whose possible outcomes
are the bits of the strings measured, paired position by position (the fifth reading of Sec. III,
which is Palmer's: `N` correlated strings of `L` bits with one permutation applied to all of them),
and it needs no shared cell.  The paper's *block* (Sec. IV.A) is the set of cells of a later string
whose bits are paired with one joint outcome of the earlier qubits; blocks of different outcomes
are disjoint, and the fraction of 1s on a block is the probability of the outcome 1 given the
block's joint outcome, since every probability is a frequency over the bits.  Here `e` gives the
joint outcome that the earlier qubits show at each cell of the later string, and the blocks are
indexed through a map `s` from outcomes to labels: `block e s σ` is the set of cells whose outcome
has the label `σ`.  With `s` the identity, the blocks are the paper's, one per joint outcome
(`ceiling_by_outcome`); with `s` injective, still one per outcome (`block_of_injective`, and the
general `ceiling`); with `s` constant, all outcomes share one block, the whole string
(`product_state`), a coarser grouping than the paper's.

* `two_le_card_of_frac`: a block whose fraction lies strictly between 0 and 1 needs at least two
  cells, one reading 1 and one reading 0.
* `ceiling`: when each of the `2^(N−1)` joint outcomes of the first `N − 1` qubits occurs, with
  the last qubit's bit given it at a probability strictly between 0 and 1, the last string, of
  `L` cells, needs `2^(N−1)` blocks of at least two cells, so `2^N ≤ L`.  A random state is such a
  state, and so is a product state of `N` qubits each in a superposition (Sec. IV.A): the bound
  holds for every state in which all `2^N` joint outcomes occur.  `ceiling_by_outcome` is the
  theorem with the paper's blocks, `s` the identity on outcomes.
* `ceiling_soft`: if each block needs `r` cells, `2^(N−1) r ≤ L`, that is `2^N ≤ 2L/r`: the
  ceiling falls by `log₂(r/2)` (Sec. V: `202`, `200` and `199` for `r = 10`, `30` and `100` at
  `L_cos`, `Numerics.soft_ceilings`).
* `nmax_iff`: when `2^N₀ ≤ L < 2^(N₀+1)`, `2^N ≤ L` exactly when `N ≤ N₀`, so `N_max = N₀`.
* `palmer_threshold`: Palmer's bit count `2^(N+1) − 2 ≤ NL` holds exactly for `N ≤ N₀` once it
  holds at `N₀ ≥ 1` and fails at `N₀ + 1`.
-/

open Finset

namespace Register
namespace Capacity

variable {Cell : Type*}

/-- the fraction of 1s of the bits `b` on a block `B` of cells -/
noncomputable def frac (b : Cell → Bool) (B : Finset Cell) : ℝ :=
  ((B.filter (fun x => b x = true)).card : ℝ) / B.card

/-- **A block whose fraction lies strictly between 0 and 1 needs at least two cells, one reading 1
and one reading 0.** -/
theorem two_le_card_of_frac (b : Cell → Bool) (B : Finset Cell)
    (h0 : 0 < frac b B) (h1 : frac b B < 1) :
    2 ≤ B.card ∧ (∃ x ∈ B, b x = true) ∧ (∃ y ∈ B, b y = false) := by
  unfold frac at h0 h1
  set a := (B.filter (fun x => b x = true)).card with ha
  -- the block is not empty, and it holds a 1
  have hn : (0 : ℝ) < B.card := by
    rcases (div_pos_iff.1 h0) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (not_lt.2 (Nat.cast_nonneg _))
  have hapos : (0 : ℝ) < a := by
    rcases (div_pos_iff.1 h0) with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h (not_lt.2 hn.le)
  have hone : ∃ x ∈ B, b x = true := by
    have : 0 < a := by exact_mod_cast hapos
    obtain ⟨x, hx⟩ := Finset.card_pos.1 this
    rw [mem_filter] at hx
    exact ⟨x, hx.1, hx.2⟩
  -- and it holds a 0: else every cell reads 1 and the fraction is 1
  have hzero : ∃ y ∈ B, b y = false := by
    by_contra hno
    push Not at hno
    have hall : B.filter (fun x => b x = true) = B := by
      apply Finset.filter_true_of_mem
      intro y hy
      have := hno y hy
      simpa using this
    rw [ha, hall, div_self hn.ne'] at h1
    exact lt_irrefl _ h1
  obtain ⟨x, hxB, hx⟩ := hone
  obtain ⟨y, hyB, hy⟩ := hzero
  have hxy : x ≠ y := by
    rintro rfl
    rw [hx] at hy
    exact Bool.noConfusion hy
  exact ⟨Finset.one_lt_card.2 ⟨x, hxB, y, hyB, hxy⟩, ⟨x, hxB, hx⟩, ⟨y, hyB, hy⟩⟩

/-- **A block of one cell** has the fraction 0 or 1 (Sec. IV.A, Sec. V): a state of the
Greenberger–Horne–Zeilinger type needs only blocks of fraction 0 or 1, one cell each, and a string
of `L` blocks of one cell uses all its bits with every fraction 0 or 1. -/
theorem one_cell_block (b : Cell → Bool) (B : Finset Cell) (h : B.card = 1) :
    frac b B = 0 ∨ frac b B = 1 := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h
  unfold frac
  cases hb : b x <;> simp [Finset.filter_singleton, hb]

variable [Fintype Cell]

/-- the block with the label `σ`: the cells of the later string on which the earlier qubits show
an outcome (`e`) whose label (`s`) is `σ`; with `s` the identity it is the paper's block of the
joint outcome `σ` -/
def block {K S : Type*} [DecidableEq S] (e : Cell → K) (s : K → S) (σ : S) : Finset Cell :=
  univ.filter (fun x => s (e x) = σ)

/-- Different labels have disjoint blocks. -/
lemma disjoint_blocks {K S : Type*} [DecidableEq S] (e : Cell → K) (s : K → S) {σ τ : S}
    (h : σ ≠ τ) : Disjoint (block e s σ) (block e s τ) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [block, mem_filter, mem_univ, true_and] at hx hx'
  exact h (hx.symm.trans hx')

/-- When the labels of different outcomes differ, the block of an outcome's label is the set of
cells that show that outcome, the paper's block. -/
lemma block_of_injective {K S : Type*} [DecidableEq K] [DecidableEq S] (e : Cell → K) (s : K → S)
    (hs : Function.Injective s) (k : K) : block e s (s k) = univ.filter (fun x => e x = k) := by
  ext x
  simp only [block, mem_filter, mem_univ, true_and]
  exact hs.eq_iff

/-- **Blocks by conditional state, not the paper's blocks.**  When every joint outcome carries the
same label `σ`, as when all of them leave the later qubit in one state, the block of that label
is the whole string.  This is not the paper's definition of a block (Sec. IV.A), which indexes
blocks by joint outcome: under the paper's definition a product state of superposed qubits has a
block for each of the `2^(N−1)` joint outcomes, each with a fraction strictly between 0 and 1, and
needs `2^N ≤ L` like a random state (`ceiling_by_outcome`). -/
theorem product_state {K S : Type*} [DecidableEq S] (e : Cell → K) (s : K → S) (σ : S)
    (h : ∀ k, s k = σ) : block e s σ = univ := by
  ext x
  simp [block, h]

/-- **The ceiling if each block needs `r` cells** (Sec. V): `2^(N−1)` joint outcomes that leave the
later qubit in different states, each state with a block of at least `r` cells, in a string of `L`
cells give `2^(N−1) r ≤ L`, that is `2^N ≤ 2L/r`, and the ceiling falls by `log₂(r/2)`. -/
theorem ceiling_soft {S : Type*} [DecidableEq S] (N L r : ℕ) (hL : Fintype.card Cell = L)
    (e : Cell → Fin (2 ^ (N - 1))) (s : Fin (2 ^ (N - 1)) → S) (hs : Function.Injective s)
    (hr : ∀ k, r ≤ (block e s (s k)).card) :
    2 ^ (N - 1) * r ≤ L := by
  classical
  have hdisj : ((univ : Finset (Fin (2 ^ (N - 1)))) : Set (Fin (2 ^ (N - 1)))).PairwiseDisjoint
      (fun k => block e s (s k)) := by
    intro k _ k' _ hkk'
    exact disjoint_blocks e s (hs.ne hkk')
  have hcard := card_le_card (subset_univ ((univ : Finset (Fin (2 ^ (N - 1)))).biUnion
    (fun k => block e s (s k))))
  rw [card_biUnion hdisj, card_univ, hL] at hcard
  have h := card_nsmul_le_sum (univ : Finset (Fin (2 ^ (N - 1)))) (fun k => (block e s (s k)).card)
    r (fun k _ => hr k)
  simp only [card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-- **The ceiling**, Eq. (nmax) (Sec. IV.A).  Read a state of `N` qubits jointly; let `e` give the
joint outcome of the first `N − 1` qubits that each cell of the last string shows, `s` an injective
labeling of the outcomes, and `b` the last string's bits.  When each of the `2^(N−1)` joint
outcomes occurs with the last qubit's bit given it at a probability strictly between 0 and 1, as
in a random state and in a product state of superposed qubits, each block has a fraction of 1s
strictly between 0 and 1.  Each block then needs at least two cells, and the string of `L` cells
has room for them only if `2^N ≤ L`. -/
theorem ceiling {S : Type*} [DecidableEq S] (N L : ℕ) (hN : 1 ≤ N) (hL : Fintype.card Cell = L)
    (e : Cell → Fin (2 ^ (N - 1))) (s : Fin (2 ^ (N - 1)) → S) (hs : Function.Injective s)
    (b : Cell → Bool)
    (hrandom : ∀ k, 0 < frac b (block e s (s k)) ∧ frac b (block e s (s k)) < 1) :
    2 ^ N ≤ L := by
  have h := ceiling_soft N L 2 hL e s hs
    (fun k => (two_le_card_of_frac b (block e s (s k)) (hrandom k).1 (hrandom k).2).1)
  have e2 : 2 ^ (N - 1) * 2 = 2 ^ N := by
    rw [← pow_succ]
    congr 1
    omega
  rwa [e2] at h

/-- **The ceiling with the paper's blocks** (Sec. IV.A): the blocks are indexed by joint outcome
(`s` the identity), `block e id k` being the cells of the last string paired with the outcome
`k`.  When every joint outcome occurs with the last qubit's bit given it at a probability strictly
between 0 and 1, `2^N ≤ L`.  A random state is such a state; so is a product state of `N` qubits
each in a superposition, whose `2^(N−1)` conditional probabilities all equal the last qubit's own:
the bound holds for every state in which all `2^N` joint outcomes occur, and what singles out the
random state is that only there is the excess observable (Sec. IV.A). -/
theorem ceiling_by_outcome (N L : ℕ) (hN : 1 ≤ N) (hL : Fintype.card Cell = L)
    (e : Cell → Fin (2 ^ (N - 1))) (b : Cell → Bool)
    (hall : ∀ k, 0 < frac b (block e id k) ∧ frac b (block e id k) < 1) :
    2 ^ N ≤ L :=
  ceiling N L hN hL e id Function.injective_id b hall

/-- **The largest `N` with `2^N ≤ L`**: when `2^N₀ ≤ L < 2^(N₀+1)`, `2^N ≤ L` exactly when
`N ≤ N₀`, so `N_max = ⌊log₂ L⌋ = N₀`. -/
theorem nmax_iff {L : ℝ} (N₀ : ℕ) (h1 : (2 : ℝ) ^ N₀ ≤ L) (h2 : L < 2 ^ (N₀ + 1)) (N : ℕ) :
    (2 : ℝ) ^ N ≤ L ↔ N ≤ N₀ := by
  constructor
  · intro h
    by_contra hN
    have : (2 : ℝ) ^ (N₀ + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  · intro hN
    have : (2 : ℝ) ^ N ≤ 2 ^ N₀ := pow_le_pow_right₀ (by norm_num) hN
    linarith

/-- The step of Palmer's bit count: with `u(N) = 2^(N+1) − 2 − NL`, `u(N+1) ≥ 2u(N) + 2` for
`N ≥ 1`. -/
lemma palmer_step (L : ℝ) (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N) :
    2 * ((2 : ℝ) ^ (N + 1) - 2 - N * L) + 2 ≤ (2 : ℝ) ^ (N + 1 + 1) - 2 - ((N + 1 : ℕ) : ℝ) * L := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have e : (2 : ℝ) ^ (N + 1 + 1) = 2 * 2 ^ (N + 1) := by ring
  rw [e]
  push_cast
  nlinarith

/-- **Palmer's bit count** `2^(N+1) − 2 ≤ NL` (Sec. V): if it holds at `N₀ ≥ 1` and fails at
`N₀ + 1`, it holds exactly for `N ≤ N₀`.  Above `N₀` doubling keeps it failing, and below `N₀`
halving keeps it holding (`palmer_step`). -/
theorem palmer_threshold (L : ℝ) (hL : 0 < L) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hyes : (2 : ℝ) ^ (N₀ + 1) - 2 ≤ N₀ * L)
    (hno : ((N₀ + 1 : ℕ) : ℝ) * L < 2 ^ (N₀ + 1 + 1) - 2) (N : ℕ) :
    (2 : ℝ) ^ (N + 1) - 2 ≤ N * L ↔ N ≤ N₀ := by
  -- above `N₀` it fails
  have up : ∀ k : ℕ, ((N₀ + 1 + k : ℕ) : ℝ) * L < 2 ^ (N₀ + 1 + k + 1) - 2 := by
    intro k
    induction k with
    | zero => simpa using hno
    | succ k ih =>
      have hs := palmer_step L hL (N₀ + 1 + k) (by omega)
      have e : N₀ + 1 + (k + 1) = N₀ + 1 + k + 1 := by ring
      rw [e]
      linarith
  -- at and below `N₀`, down to `1`, it holds
  have down : ∀ k N : ℕ, N + k = N₀ → 1 ≤ N → (2 : ℝ) ^ (N + 1) - 2 ≤ N * L := by
    intro k
    induction k with
    | zero => intro N hN _; rw [add_zero] at hN; rw [hN]; exact hyes
    | succ k ih =>
      intro N hN h1
      have hnext := ih (N + 1) (by omega) (by omega)
      have hs := palmer_step L hL N h1
      push_cast at hnext hs
      linarith
  constructor
  · intro h
    by_contra hN
    obtain ⟨k, rfl⟩ : ∃ k, N = N₀ + 1 + k := ⟨N - (N₀ + 1), by omega⟩
    have := up k
    linarith
  · intro hN
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; norm_num
    · exact down (N₀ - N) N (by omega) h0

end Capacity
end Register
