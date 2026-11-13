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

The bits are the possible outcomes of one measurement of the qubit (Postulate 1): each cell's bit
is one possible outcome among the `L`, so the outcome is the bit of a cell of a set `A` with the
probability `|A|/L` (`share_read`, from the hypothesis `halike`: each cell's bit is the outcome
with the probability `1/L`), and the probability of an outcome is its share of the bits.  When a
state is measured jointly (Postulate 1), the possible outcomes are the positions, each one among
`L`, the same on every string of the qubits it measures, since the shift is one translation on
every string and keeps them in step; the outcome at a position is the bits there.  So every
position of a later string is paired with one outcome of the earlier qubits, their bits there
(`jointOutcome`); this is Palmer's state of `N` qubits, `N` correlated strings of `L` bits with one
permutation applied to all of them, and it needs no shared cell.  The paper's *block* (Sec. IV.A)
is the set of cells of a later string whose bits are paired with one joint outcome of the earlier
qubits; blocks of different outcomes are disjoint, and the fraction of 1s on a block is the
probability of the outcome 1 given the block's joint outcome, its share of the possible outcomes
that show that joint outcome (`block_fraction_read`).  The general
theorems take the pairing as a function `e` from the cells of the later string to the joint
outcomes, and index the blocks through a map `s` from outcomes to labels: `block e s σ` is the set
of cells whose outcome has the label `σ`.  With `s` the identity, the blocks are the paper's, one
per joint outcome (`ceiling_by_outcome`); with `s` injective, still one per outcome (the general
`ceiling`); with `s` constant, all outcomes would share one block, the whole string, a coarser
grouping than the paper's: the test of Sec. IV.A,
which rests on whether each string has room for the different conditional states of its qubit,
its states given the outcomes of the earlier qubits, counts in this way when it says "In a product
state each string has one conditional state to hold, on all its cells" (a block holds the conditional
state of its joint outcome, and blocks of different outcomes may hold the same one).  The paper's
Sec. IV.A also derives the limit for a linear cluster state followed by one layer of generic
single-qubit rotations, whose last qubit has a different conditional state for each joint outcome of
the earlier ones (`Cluster.chain_card`); for generic rotations every block's fraction lies strictly
between 0 and 1, so that state is a case of `ceiling_by_outcome` as a random state is.  `ceiling_in_step` is the
bound with the pairing the strings supply, `e` the bits of the earlier strings at each position.

* `two_le_card_of_frac`: a block whose fraction lies strictly between 0 and 1 needs at least two
  cells, one reading 1 and one reading −1 (the bit `false` here).
* `frac_pos_lt_one`: conversely, a block with a cell reading 1 and a cell reading −1 has a
  fraction strictly between 0 and 1.  The ceilings of `Main.lean` come to the fractions this way,
  from a joint outcome that occurs being the outcome at a position.
* `outcomes_iff_cells`: what that premise and a condition on `pr` ask together.  Each outcome of
  a set has a cell of either bit exactly when some `pr` meets both the premise and the condition
  that each outcome of the set occurs with either value of the bit.
* `ceiling`: when each of the `2^(N−1)` joint outcomes of the first `N − 1` qubits occurs, with
  the last qubit's bit given it at a probability strictly between 0 and 1, the last string, of
  `L` cells, needs `2^(N−1)` blocks of at least two cells, so `2^N ≤ L`.  A random state is such a
  state, and so is a product state of `N` qubits each in a superposition (Sec. IV.A): the bound
  holds for every state in which all `2^N` joint outcomes occur.  `ceiling_by_outcome` is the
  theorem with the paper's blocks, `s` the identity on outcomes.
* `ceiling_logical`: a string with `2^N` blocks, each with a fraction strictly between 0 and 1,
  needs `2^(N+1) ≤ L`.  Sec. IV.A finds up to that many conditional states on the fullest physical
  string of `N` logical qubits, and that many in the surface code; that no physical string has
  more, with the blocks read in order, is a step of coding theory that `Coding.lean` proves, with
  the same count for blocks by
  conditional state (`Coding.ceiling_line_code`, `Coding.card_condStates_le`);
  `Numerics.logical_ceiling_cos` gives the `203` logical qubits that follow.
* `ceiling_soft`: if each block needs `r` cells, `2^(N−1) r ≤ L`, that is `N ≤ log₂(2L/r)`
  (Sec. V: `202`, `200` and `199` for `r = 10`, `30` and `100` at `L_cos`,
  `Numerics.soft_ceilings`).
* `ceiling_in_step`: the same bound for `N` strings read in step, the pairing being their bits at
  each position (`jointOutcome`).
* `share_read`: with each cell's bit one possible outcome among `L` (Postulate 1), the outcome is
  the bit of a cell of a set `A` with the probability `|A|/L`, the set's share of the cells.
* `condProb`, `block_fraction_read`: the probability that the outcome is `1`, given that it is
  the bit of a cell of a block (`condProb`), is the block's fraction of 1s, so a block's fraction
  is the conditional probability that the ceiling theorems of this file take it to be.
  `Main.block_fraction` states it from Postulate 1's premise for the cells
  (`Sources.P1.ring_bits_alike`).  The ceilings of `Main.lean` do not take those equal weights.
  They take that a joint outcome that occurs is the outcome at a position
  (`Sources.P1.outcomes_at_positions`) and that no ring has more than `L` cells
  (`Sources.P1.ring_cells`).
* `one_cell_block`: a block of one cell has the fraction 0 or 1, as a state of the
  Greenberger–Horne–Zeilinger type needs (Secs. IV.A and V).
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
and one reading −1** (the bit `false` here). -/
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

/-- A block with a cell that reads 1 and a cell that reads −1 has a fraction of 1s strictly
between 0 and 1: the converse of `two_le_card_of_frac`. -/
lemma frac_pos_lt_one (b : Cell → Bool) (B : Finset Cell) {x y : Cell} (hx : x ∈ B)
    (hbx : b x = true) (hy : y ∈ B) (hby : b y = false) : 0 < frac b B ∧ frac b B < 1 := by
  have hB : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
  have hpos : 0 < (B.filter (fun z => b z = true)).card :=
    Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hx, hbx⟩⟩
  have hlt : (B.filter (fun z => b z = true)).card < B.card :=
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨y, hy, by simp [hby]⟩)
  unfold frac
  exact ⟨div_pos (by exact_mod_cast hpos) hB, (div_lt_one hB).2 (by exact_mod_cast hlt)⟩

/-- **What the premise and a condition on `pr` ask together.**  The ceilings and the results on
codes of `Main.lean` take a function `pr` in two hypotheses.  One is a condition: each outcome
`k` of a set `A` occurs with either value of the bit, `pr k v > 0`.  The other is the premise
`Sources.P1.outcomes_at_positions`: an outcome that occurs with a value of the bit is at a cell
with that value.  Some `pr` meets the two exactly when each outcome of `A` has a cell of either
bit.  In those results `pr` occurs in these two hypotheses only, so no statement says that it is
the probabilities of a state.  The docstrings read it as the probabilities of the state that the
register holds. -/
lemma outcomes_iff_cells {K : Type*} (e : Cell → K) (b : Cell → Bool) (A : Set K) :
    (∃ pr : K → Bool → ℝ, (∀ k ∈ A, 0 < pr k true ∧ 0 < pr k false) ∧
      (∀ k v, 0 < pr k v → ∃ x, e x = k ∧ b x = v)) ↔
    ∀ k ∈ A, (∃ x, e x = k ∧ b x = true) ∧ (∃ y, e y = k ∧ b y = false) := by
  classical
  constructor
  · rintro ⟨pr, hA, hout⟩ k hk
    exact ⟨hout k true (hA k hk).1, hout k false (hA k hk).2⟩
  · intro h
    refine ⟨fun k v => if ∃ x, e x = k ∧ b x = v then 1 else 0, fun k hk => ?_, fun k v hkv => ?_⟩
    · simp [(h k hk).1, (h k hk).2]
    · by_contra hno
      simp [hno] at hkv

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

/-- **The ceiling if each block needs `r` cells** (Sec. V): a block of `r` cells resolves the last
qubit's conditional probability and phase to one part in `r`.  With `2^(N−1)` joint outcomes of
the earlier qubits, each with a block of at least `r` cells, a string of `L` cells gives
`2^(N−1) r ≤ L`, that is `N ≤ log₂(2L/r)`. -/
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

/-- **The ceiling**, Eq. (nmax) (Sec. IV.A).  Measure a state of `N` qubits jointly; let `e` give
the joint outcome of the first `N − 1` qubits that each cell of the last string shows, `s` an
injective labeling of the outcomes, and `b` the last string's bits.  When each of the `2^(N−1)`
joint outcomes occurs with the last qubit's bit given it at a probability strictly between 0 and 1,
as in a random state and in a product state of superposed qubits, each block has a fraction of 1s
strictly between 0 and 1.  Each block then needs at least two cells, and the string of `L` cells has
room for them only if `2^N ≤ L`. -/
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
the bound holds for every state in which all `2^N` joint outcomes occur.  No sample shows which
outcomes are missing (Sec. IV.A); what sets the random state apart is that its last qubit has a
different conditional state for each joint outcome of the others, so that its string has too few
cells to hold them all once `2^N > L`, where a product state's string has one conditional state to
hold.  A linear cluster state followed by one layer of generic single-qubit rotations has as many
conditional states as a random state (`Cluster.chain_card`), and the paper derives the same limit
for it (Sec. IV.A). -/
theorem ceiling_by_outcome (N L : ℕ) (hN : 1 ≤ N) (hL : Fintype.card Cell = L)
    (e : Cell → Fin (2 ^ (N - 1))) (b : Cell → Bool)
    (hall : ∀ k, 0 < frac b (block e id k) ∧ frac b (block e id k) < 1) :
    2 ^ N ≤ L :=
  ceiling N L hN hL e id Function.injective_id b hall

/-- **The ceiling for logical qubits** (Sec. IV.A).  A string whose cells fall into `2^N` blocks,
each with a fraction of 1s strictly between 0 and 1, needs two cells for each block, so
`2^(N+1) ≤ L` (`ceiling_by_outcome` at `N + 1`).  In a Calderbank–Shor–Steane code a physical bit,
given the earlier physical bits, is fixed, balanced, or equal or opposite to the logical bit.  Where
the equal and the opposite case both occur, as for the last bit of a line in the surface code, the
fullest physical string of a random state of `N` logical qubits has a conditional state for each
joint outcome of the earlier logical qubits and each case, `2^N` in all, twice as many as a logical
string, each held on a block of its own, and no physical string has more conditional states to hold,
which the files prove with the blocks read in order.
`Coding.lean` proves that step (`Coding.css_conditional_joint`, `Coding.LineCode.jointBitGiven_rest`,
`Coding.card_condStates_le`, `Coding.LineCode.card_lineStates`) and the count with blocks by
conditional state (`Coding.two_mul_card_states_le`, `Coding.ceiling_both_cases`,
`Coding.ceiling_line_code`); `Numerics.logical_ceiling_cos` gives `203` logical qubits at
`L_cos`. -/
theorem ceiling_logical (N L : ℕ) (hL : Fintype.card Cell = L)
    (e : Cell → Fin (2 ^ N)) (b : Cell → Bool)
    (hall : ∀ k, 0 < frac b (block e id k) ∧ frac b (block e id k) < 1) :
    2 ^ (N + 1) ≤ L :=
  ceiling_by_outcome (N + 1) L (by omega) hL e b hall

/-- **Strings read in step** (Sec. IV.A, how "measured jointly" is read).  A joint measurement is
one measurement, so its possible outcomes are the positions, each one among the `L`, the same on
every string of the qubits it measures, since the shift carries every string one cell per tick and
keeps them in step (Postulate 1); the outcome at a position is the bits there.  So the joint outcome of the first `N − 1` qubits that a position `x` of the last string shows is
their bits at `x`.  Here `bits i` is the string of the `i`-th qubit, indexed by the common
positions. -/
def jointOutcome {N : ℕ} (bits : Fin N → Cell → Bool) (x : Cell) : Fin (N - 1) → Bool :=
  fun i => bits (Fin.castLE (Nat.sub_le N 1) i) x

/-- **The ceiling for strings read in step** (Sec. IV.A), Eq. (nmax).  With the pairing of
`jointOutcome`, the bits of the strings at one position, the block of a joint outcome `ω` is the
set of positions at which the first `N − 1` strings show `ω`.  When every `ω` occurs with the last
qubit's bit given it at a probability strictly between 0 and 1, `2^N ≤ L`: `ceiling_by_outcome`
with the pairing supplied by the strings, no function chosen. -/
theorem ceiling_in_step (N L : ℕ) (hN : 1 ≤ N) (hL : Fintype.card Cell = L)
    (bits : Fin N → Cell → Bool)
    (hall : ∀ ω : Fin (N - 1) → Bool,
      0 < frac (bits ⟨N - 1, by omega⟩) (univ.filter (fun x => jointOutcome bits x = ω)) ∧
      frac (bits ⟨N - 1, by omega⟩) (univ.filter (fun x => jointOutcome bits x = ω)) < 1) :
    2 ^ N ≤ L := by
  have hcard : Fintype.card (Fin (N - 1) → Bool) = 2 ^ (N - 1) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  let φ : (Fin (N - 1) → Bool) ≃ Fin (2 ^ (N - 1)) := Fintype.equivFinOfCardEq hcard
  refine ceiling_by_outcome N L hN hL (fun x => φ (jointOutcome bits x)) (bits ⟨N - 1, by omega⟩)
    (fun k => ?_)
  have hb : block (fun x => φ (jointOutcome bits x)) id k
      = univ.filter (fun x => jointOutcome bits x = φ.symm k) := by
    ext x
    simp only [block, mem_filter, mem_univ, true_and, id, ← Equiv.eq_symm_apply]
  rw [hb]
  exact hall (φ.symm k)

/-- **The outcome is the bit of a cell of a set with the probability of the set's share of the
cells** (Secs. IV.A, IV.C): each cell's bit is one possible outcome among the `L` (Postulate 1,
`halike`), so the outcome is the bit of a cell of `A` with the probability `|A|/L`. -/
theorem share_read (q : Cell → ℝ) (halike : ∀ x, q x = 1 / Fintype.card Cell)
    (A : Finset Cell) : ∑ x ∈ A, q x = A.card / Fintype.card Cell := by
  rw [sum_congr rfl (fun x _ => halike x), sum_const, nsmul_eq_mul]
  ring

/-- **The probability of the outcome `1` given a block** (Sec. IV.A): with `q x` the probability
that the outcome is the bit of the cell `x`, the probability that the outcome is the bit of a cell
of the block `B` that reads `1`, over the probability that it is the bit of a cell of `B`. -/
noncomputable def condProb (q : Cell → ℝ) (b : Cell → Bool) (B : Finset Cell) : ℝ :=
  (∑ x ∈ B.filter (fun x => b x = true), q x) / (∑ x ∈ B, q x)

/-- **A block's fraction is a conditional probability** (Sec. IV.A).  With each cell's bit one
possible outcome among the `L` (`share_read`), the outcome is the bit of a cell of a set `B` with
the probability `|B|/L`, and of a cell of `B` with the bit `1` with the probability of the cells of
`B` that show `1`.  So, given that it is the bit of a cell of `B`, it is `1` with the probability
`frac b B`, the fraction of 1s on `B` (for an empty block both sides are `0`, by Lean's
`x/0 = 0`, and the probability given the block is not defined).  For the block of a
joint outcome this is the probability of the last qubit's outcome `1` given that joint outcome,
which the ceiling theorems take as the block's fraction (`frac` in `hrandom` and `hall`; `hshare`
of the theorems of `Coding.lean`). -/
theorem block_fraction_read (q : Cell → ℝ)
    (halike : ∀ x, q x = 1 / Fintype.card Cell) (b : Cell → Bool) (B : Finset Cell) :
    condProb q b B = frac b B := by
  unfold condProb
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp [frac]
  rw [share_read q halike, share_read q halike]
  have hc : (Fintype.card Cell : ℝ) ≠ 0 := by
    obtain ⟨x, -⟩ := hB
    have : 0 < Fintype.card Cell := Fintype.card_pos_iff.2 ⟨x⟩
    exact_mod_cast this.ne'
  have hB' : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  unfold frac
  field_simp

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
