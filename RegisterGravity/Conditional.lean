import RegisterGravity.Capacity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# How many conditional states a string has to hold (Sec. IV.A)

Formal counterpart of the paragraph of Sec. IV.A that begins "The test therefore rests on
something else: whether each string has room for the different conditional states of its qubit,
its states given the outcomes of the earlier qubits".  The paragraph counts the conditional
states in four cases, and each count is a theorem here.  No premise of `Sources.lean` enters:
the theorems are statements of the amplitudes that quantum mechanics gives these states, and of
what a block of a string can hold.

A reading `x : Fin N → Bool` gives the bit of each of the `N` qubits along the polar axis `Z`,
with `true` the outcome `1` and `false` the outcome `−1`, as in `Capacity.lean`.  A state is given
by its amplitude at each reading, written as a product of one factor for each qubit: the factor
of a qubit is its amplitude at its own bit given the bits of the earlier qubits.  The conditional
state of a qubit at a reading is its factor at each of its two bits (`condState`).  One
definition serves all four cases: in a stabilizer measurement the measured qubit is read after
all the others, its factor is the amplitude of the measurement's outcome (`stabAmp`), and its
conditional state is `stabState` times a sign that its two bits share (`stabState_spec`).

* `card_product_states_le_one`: "In a product state each string has one conditional state to
  hold, on all its cells".  The factor of a qubit of a product state is the qubit's own
  amplitude, whatever the earlier qubits read.
* `clusterSign`, `clusterSign_eq`: the cluster state of a graph on the qubits.  Each qubit starts
  in the equal superposition of its two bits, and a controlled-`Z` gate on each pair of neighbors
  changes the sign of the amplitude where both read `−1`.  Its amplitude at `x` is `2^{−N/2}` times
  the sign `clusterSign adj x`, a product of one factor for each qubit (`factor`).
* `factor_depends`: "In a cluster state a qubit's state depends on the earlier qubits only through
  the product of the bits of its neighbors among them".
* `card_cluster_states_le_two`: "Its string has at most two conditional states to hold, one for
  each value of that product, at every `N`".
* `stabAmp`, `stabState`, `stabState_spec`, `stabilizer_bit`, `card_stab_states_le_two`: a
  stabilizer measurement reads one qubit along `X` and its neighbors along the polar axis `Z`.
  "That qubit's bit is then the product of its neighbors' bits, and its string again has two
  conditional states to hold".  Here the measured qubit is read after the others, so its
  conditional state is its two amplitudes along `X` given the bits of all the others.
* `card_states_by_count`: "A state in which each qubit's state depends on the earlier qubits only
  through how many of them read `−1` gives a string at most `N` conditional states to hold".
* `two_cells_fit`: "each string has room for them, two cells for each, at any `N` up to `L/2`".
* `product_one_state`: a product state gives the last qubit one conditional state, by its
  amplitudes, so its conditional states do not all differ.  Its strings are not conditioned,
  however many of them one joint measurement reads.
* `room_holds`: "Each conditional state can then have a block with a cell reading `1` and a cell
  reading `−1`, so the bound on the return (below) does not apply to a state of these kinds".
* `stab_prob`, `stabilizer_held`: "In a stabilizer measurement each conditional state is a fixed
  bit, which a block of any size holds exactly, and a block that holds it shows at every position
  the product of the neighbors' bits, as quantum mechanics predicts, at every `N`".

The room that conditional states take on a string is counted in `Capacity.lean` and
`Coding.lean`: two cells for each conditional state that is a superposition
(`Coding.two_mul_card_states_le`), and that many cells are enough
(`Coding.two_cells_each_model`).
-/

open Finset

namespace Register
namespace Conditional

/-- a bit as a number: `1` for the bit `true`, and `−1` for the bit `false` -/
def pm (v : Bool) : ℤ := if v then 1 else -1

lemma pm_true : pm true = 1 := rfl

lemma pm_false : pm false = -1 := rfl

/-- a product of bits is `1` or `−1` -/
lemma prod_pm_cases {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    ∏ j ∈ s, pm (f j) = 1 ∨ ∏ j ∈ s, pm (f j) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl prod_empty
  | insert a s ha ih =>
    rw [prod_insert ha]
    rcases ih with h | h <;> rw [h] <;> cases f a <;> simp [pm]

variable {N : ℕ}

/-- **The conditional state of a qubit** (Sec. IV.A: "the different conditional states of its
qubit, its states given the outcomes of the earlier qubits").  `φ k x` is the factor of the qubit
`k` in the amplitude of a state at the reading `x`, the amplitude being the product of the
qubits' factors: the amplitude of the qubit `k` at its bit `x k` given the bits of the earlier
qubits.  The conditional state of the qubit `k` at the reading `x` is its factor at each of its
two bits. -/
def condState {α : Type*} (φ : Fin N → (Fin N → Bool) → α) (k : Fin N) (x : Fin N → Bool) :
    Bool → α :=
  fun v => φ k (Function.update x k v)

/-- **One conditional state in a product state** (Sec. IV.A: "In a product state each string has
one conditional state to hold, on all its cells").  In a product state the amplitude at the
reading `x` is the product of the qubits' own amplitudes, `∏ k, a k (x k)`, so the factor of the
qubit `k` is its own amplitude `a k (x k)`, whatever the other qubits read.  Over all the
readings its conditional state takes one value. -/
theorem card_product_states_le_one {α : Type*} [DecidableEq α] (a : Fin N → Bool → α)
    (k : Fin N) :
    (univ.image (condState (fun k x => a k (x k)) k)).card ≤ 1 := by
  have hsub : univ.image (condState (fun k x => a k (x k)) k) ⊆ {a k} := by
    intro f hf
    obtain ⟨x, -, rfl⟩ := mem_image.1 hf
    rw [mem_singleton]
    funext v
    show a k (Function.update x k v k) = a k v
    rw [Function.update_self]
  exact (card_le_card hsub).trans (card_singleton _).le

/-- the product of the bits of the neighbors of the qubit `k` among the earlier qubits; `adj j k`
says that the qubits `j < k` are neighbors -/
def earlierProd (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (x : Fin N → Bool) : ℤ :=
  ∏ j ∈ univ.filter (fun j => j < k ∧ adj j k), pm (x j)

/-- the factor of the qubit `k` in the amplitude of a cluster state: `1` where the qubit reads
`1`, and the product of the bits of its earlier neighbors where it reads `−1` -/
def factor (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N) (x : Fin N → Bool) : ℤ :=
  if x k then 1 else earlierProd adj k x

/-- **The cluster state** of the graph `adj`: its amplitude at the reading `x`, without the common
factor `2^{−N/2}`, as the product of one factor for each qubit -/
def clusterSign (adj : Fin N → Fin N → Prop) [DecidableRel adj] (x : Fin N → Bool) : ℤ :=
  ∏ k, factor adj k x

/-- **The amplitude of a cluster state**: the product of the qubits' factors is the sign that the
controlled-`Z` gates give, `−1` for each pair of neighbors that both read `−1`. -/
theorem clusterSign_eq (adj : Fin N → Fin N → Prop) [DecidableRel adj] (x : Fin N → Bool) :
    clusterSign adj x = ∏ k, ∏ j ∈ univ.filter (fun j => j < k ∧ adj j k),
      (if x j = false ∧ x k = false then (-1 : ℤ) else 1) := by
  unfold clusterSign
  refine prod_congr rfl fun k _ => ?_
  unfold factor earlierProd
  cases hk : x k
  · simp only [Bool.false_eq_true, ite_false, and_true]
    refine prod_congr rfl fun j _ => ?_
    cases x j <;> simp [pm]
  · simp

/-- **A qubit of a cluster state, given the earlier qubits** (Sec. IV.A: "In a cluster state a
qubit's state depends on the earlier qubits only through the product of the bits of its neighbors
among them").  The factor of the qubit `k` is the same at two readings that agree in the bit of
`k` and in the product of the bits of its earlier neighbors. -/
theorem factor_depends (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (x y : Fin N → Bool) (hk : x k = y k) (h : earlierProd adj k x = earlierProd adj k y) :
    factor adj k x = factor adj k y := by
  unfold factor
  rw [hk, h]

/-- the product of the bits of the earlier neighbors of `k` does not read the bit of `k` -/
lemma earlierProd_update (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (x : Fin N → Bool) (v : Bool) :
    earlierProd adj k (Function.update x k v) = earlierProd adj k x := by
  unfold earlierProd
  refine prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (ne_of_lt (mem_filter.1 hj).2.1)]

/-- the conditional state of a qubit of a cluster state: `1` at the bit `1`, and the product of
the bits of its earlier neighbors at the bit `−1` -/
lemma condState_factor (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (x : Fin N → Bool) :
    condState (factor adj) k x = fun v => if v then 1 else earlierProd adj k x := by
  funext v
  unfold condState factor
  rw [Function.update_self, earlierProd_update]

/-- **Two conditional states in a cluster state** (Sec. IV.A: "Its string has at most two
conditional states to hold, one for each value of that product, at every `N`").  Over all the
readings, the conditional state of the qubit `k` takes at most two values, for every number `N`
of qubits and every graph. -/
theorem card_cluster_states_le_two (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N) :
    (univ.image (condState (factor adj) k)).card ≤ 2 := by
  have hsub : univ.image (condState (factor adj) k) ⊆
      ({1, -1} : Finset ℤ).image (fun s : ℤ => fun v : Bool => if v then 1 else s) := by
    intro f hf
    obtain ⟨x, -, rfl⟩ := mem_image.1 hf
    rw [condState_factor]
    apply mem_image.2
    rcases prod_pm_cases (univ.filter (fun j => j < k ∧ adj j k)) x with h | h
    · exact ⟨1, by simp, by simp [earlierProd, h]⟩
    · exact ⟨-1, by simp, by simp [earlierProd, h]⟩
  exact (card_le_card hsub).trans (card_image_le.trans (card_insert_le _ _))

/-- the product of the bits of all the neighbors of the qubit `k`, earlier and later -/
def nbrProd (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N) (x : Fin N → Bool) : ℤ :=
  ∏ j ∈ univ.filter (fun j => (j < k ∧ adj j k) ∨ (k < j ∧ adj k j)), pm (x j)

/-- the amplitude of a cluster state where the qubit `k` reads `−1` is the amplitude where it
reads `1`, times the product of the bits of its neighbors -/
lemma clusterSign_flip (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (x : Fin N → Bool) :
    clusterSign adj (Function.update x k false)
      = clusterSign adj (Function.update x k true) * nbrProd adj k x := by
  classical
  have hfac : ∀ m, factor adj m (Function.update x k false)
      = factor adj m (Function.update x k true) *
        (if m = k then earlierProd adj k x else if k < m ∧ adj k m then pm (x m) else 1) := by
    intro m
    by_cases hmk : m = k
    · subst hmk
      simp [factor, earlierProd_update]
    · have hxf : Function.update x k false m = x m := Function.update_of_ne hmk _ _
      have hxt : Function.update x k true m = x m := Function.update_of_ne hmk _ _
      simp only [factor, hxf, hxt, ite_eq_right hmk]
      cases hxm : x m
      · simp only [Bool.false_eq_true, ite_false]
        by_cases hkm : k < m ∧ adj k m
        · rw [ite_eq_left hkm]
          have hkmem : k ∈ univ.filter (fun j => j < m ∧ adj j m) :=
            mem_filter.2 ⟨mem_univ _, hkm⟩
          unfold earlierProd
          rw [← mul_prod_erase _ _ hkmem, ← mul_prod_erase _ _ hkmem]
          have hrest : ∏ j ∈ (univ.filter (fun j => j < m ∧ adj j m)).erase k,
                pm (Function.update x k false j)
              = ∏ j ∈ (univ.filter (fun j => j < m ∧ adj j m)).erase k,
                pm (Function.update x k true j) :=
            prod_congr rfl fun j hj => by
              rw [Function.update_of_ne (ne_of_mem_erase hj),
                Function.update_of_ne (ne_of_mem_erase hj)]
          rw [hrest, Function.update_self, Function.update_self, pm_true, pm_false]
          ring
        · rw [ite_eq_right hkm, mul_one]
          unfold earlierProd
          refine prod_congr rfl fun j hj => ?_
          have hjk : j ≠ k := by
            rintro rfl
            exact hkm (mem_filter.1 hj).2
          rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
      · simp [pm]
  unfold clusterSign
  rw [prod_congr rfl (fun m _ => hfac m), prod_mul_distrib]
  congr 1
  rw [← mul_prod_erase univ _ (mem_univ k), ite_eq_left rfl]
  have hrest : ∏ m ∈ univ.erase k,
        (if m = k then earlierProd adj k x else if k < m ∧ adj k m then pm (x m) else 1)
      = ∏ m ∈ univ.filter (fun m => k < m ∧ adj k m), pm (x m) := by
    rw [prod_filter, ← mul_prod_erase univ (fun m => if k < m ∧ adj k m then pm (x m) else 1)
      (mem_univ k), ite_eq_right (fun h => lt_irrefl k h.1), one_mul]
    refine prod_congr rfl fun m hm => ?_
    rw [ite_eq_right (ne_of_mem_erase hm)]
  rw [hrest]
  unfold nbrProd earlierProd
  rw [filter_or, prod_union]
  rw [disjoint_filter]
  intro j _ h1 h2
  exact lt_asymm h1.1 h2.1

/-- **The amplitude of a stabilizer measurement's outcome** (Sec. IV.A: "A stabilizer measurement
reads one qubit along `X`, an axis in the equatorial plane of the Bloch sphere, and its neighbors
along the polar axis `Z`").  At the reading `y` the measured qubit `k` shows the bit `y k` along
`X`, and every other qubit shows its bit along `Z`.  The amplitude of that outcome, without the
factor `2^{−(N+1)/2}`, is the amplitude of the cluster state where `k` reads `1` along `Z` plus
`y k` times its amplitude where `k` reads `−1`. -/
def stabAmp (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N) (y : Fin N → Bool) : ℤ :=
  clusterSign adj (Function.update y k true)
    + pm (y k) * clusterSign adj (Function.update y k false)

/-- the conditional state of the qubit `k` that a stabilizer measurement reads along `X`, at the
reading `x` of the other qubits along `Z`, without the sign that its two amplitudes share
(`stabState_spec`): `1 + s P` at the bit `s`, with `P` the product of its neighbors' bits -/
def stabState (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N) (x : Fin N → Bool) :
    Bool → ℤ :=
  fun s => 1 + pm s * nbrProd adj k x

/-- **The conditional state in a stabilizer measurement.**  The measured qubit is read after the
others, so its conditional state, `condState` as in the other cases, is its two amplitudes given
the bits of all the others.  It is one sign, the same at both bits, times `stabState`. -/
theorem stabState_spec (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (x : Fin N → Bool) :
    condState (fun _ => stabAmp adj k) k x
      = fun s => clusterSign adj (Function.update x k true) * stabState adj k x s := by
  funext s
  show stabAmp adj k (Function.update x k s)
      = clusterSign adj (Function.update x k true) * stabState adj k x s
  unfold stabAmp stabState
  rw [Function.update_idem, Function.update_idem, Function.update_self, clusterSign_flip]
  ring

/-- **A stabilizer measurement's bit** (Sec. IV.A: "That qubit's bit is then the product of its
neighbors' bits").  Where the amplitude of the outcome `y` does not vanish, the bit that the
measured qubit shows along `X` is the product of the bits of its neighbors. -/
theorem stabilizer_bit (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (y : Fin N → Bool) (hamp : stabAmp adj k y ≠ 0) : pm (y k) = nbrProd adj k y := by
  have h : stabAmp adj k (Function.update y k (y k))
      = clusterSign adj (Function.update y k true) * stabState adj k y (y k) :=
    congrFun (stabState_spec adj k y) (y k)
  rw [Function.update_eq_self] at h
  have hst : (1 : ℤ) + pm (y k) * nbrProd adj k y ≠ 0 := by
    intro h0
    apply hamp
    rw [h]
    show clusterSign adj (Function.update y k true) * (1 + pm (y k) * nbrProd adj k y) = 0
    rw [h0, mul_zero]
  rcases prod_pm_cases (univ.filter (fun j => (j < k ∧ adj j k) ∨ (k < j ∧ adj k j))) y
    with hP | hP
  · have hP' : nbrProd adj k y = 1 := hP
    rw [hP'] at hst ⊢
    cases hs : y k
    · rw [hs] at hst
      exact absurd (by simp [pm] : (1 : ℤ) + pm false * 1 = 0) hst
    · rfl
  · have hP' : nbrProd adj k y = -1 := hP
    rw [hP'] at hst ⊢
    cases hs : y k
    · rfl
    · rw [hs] at hst
      exact absurd (by simp [pm] : (1 : ℤ) + pm true * -1 = 0) hst

/-- **Two conditional states in a stabilizer measurement** (Sec. IV.A: "and its string again has
two conditional states to hold").  Over all the readings of the other qubits, the conditional
state of the measured qubit takes at most two values, one for each value of the product of its
neighbors' bits, at every `N`. -/
theorem card_stab_states_le_two (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N) :
    (univ.image (stabState adj k)).card ≤ 2 := by
  have hsub : univ.image (stabState adj k) ⊆
      ({1, -1} : Finset ℤ).image (fun P : ℤ => fun s : Bool => 1 + pm s * P) := by
    intro f hf
    obtain ⟨x, -, rfl⟩ := mem_image.1 hf
    apply mem_image.2
    rcases prod_pm_cases (univ.filter (fun j => (j < k ∧ adj j k) ∨ (k < j ∧ adj k j))) x
      with h | h
    · exact ⟨1, by simp, by unfold stabState nbrProd; rw [h]⟩
    · exact ⟨-1, by simp, by unfold stabState nbrProd; rw [h]⟩
  exact (card_le_card hsub).trans (card_image_le.trans (card_insert_le _ _))

/-- **The probability of a stabilizer measurement's bit.**  Given the reading `σ` of the other
qubits, quantum mechanics gives the outcome `1` of the measured qubit the share of the
conditional state's weight at that bit.  It is `1` where the product of the neighbors' bits is
`1`, and `0` where it is `−1`: the conditional state is a fixed bit. -/
theorem stab_prob (adj : Fin N → Fin N → Prop) [DecidableRel adj] (k : Fin N)
    (σ : Fin N → Bool) :
    ((stabState adj k σ true : ℤ) : ℝ) ^ 2
        / (((stabState adj k σ true : ℤ) : ℝ) ^ 2 + ((stabState adj k σ false : ℤ) : ℝ) ^ 2)
      = if nbrProd adj k σ = 1 then 1 else 0 := by
  unfold stabState
  rcases prod_pm_cases (univ.filter (fun j => (j < k ∧ adj j k) ∨ (k < j ∧ adj k j))) σ
    with h | h
  · have h' : nbrProd adj k σ = 1 := h
    rw [h']
    norm_num [pm]
  · have h' : nbrProd adj k σ = -1 := h
    rw [h']
    norm_num [pm]

/-- the number of the qubits before `k` that read `−1` -/
def earlierMinus (k : Fin N) (x : Fin N → Bool) : ℕ :=
  (univ.filter (fun j => j < k ∧ x j = false)).card

/-- **At most `N` conditional states by the count of `−1`** (Sec. IV.A: "A state in which each
qubit's state depends on the earlier qubits only through how many of them read `−1` gives a
string at most `N` conditional states to hold").  The conditional state of the qubit `k` is
`g n` where `n` of the earlier qubits read `−1` (`hφ`).  Over all the readings it takes at most
`N` values, since fewer than `N` qubits stand before `k`. -/
theorem card_states_by_count {α : Type*} [DecidableEq α] (φ : Fin N → (Fin N → Bool) → α)
    (k : Fin N) (g : ℕ → Bool → α) (hφ : ∀ x, condState φ k x = g (earlierMinus k x)) :
    (univ.image (condState φ k)).card ≤ N := by
  have hle : ∀ x : Fin N → Bool, earlierMinus k x ≤ k.val := by
    intro x
    unfold earlierMinus
    calc (univ.filter (fun j => j < k ∧ x j = false)).card ≤ (Iio k).card :=
          card_le_card fun j hj => mem_Iio.2 (mem_filter.1 hj).2.1
      _ = k.val := Fin.card_Iio k
  have hsub : univ.image (condState φ k) ⊆ (range (k.val + 1)).image g := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := mem_image.1 hv
    exact mem_image.2 ⟨_, mem_range.2 (Nat.lt_succ_of_le (hle x)), (hφ x).symm⟩
  calc (univ.image (condState φ k)).card
      ≤ ((range (k.val + 1)).image g).card := card_le_card hsub
    _ ≤ (range (k.val + 1)).card := card_image_le
    _ = k.val + 1 := card_range _
    _ ≤ N := k.isLt

/-- **Two cells for each conditional state fit at any `N` up to `L/2`** (Sec. IV.A: "each string
has room for them, two cells for each, at any `N` up to `L/2`").  A string with at most `N`
conditional states to hold, as in each of the cases above where `N ≥ 2`, takes at most `2N` cells
at two cells for each (`Coding.two_cells_each_model`), and a ring of `L` cells has them where
`2N ≤ L`. -/
theorem two_cells_fit {α : Type*} [DecidableEq α] (φ : Fin N → (Fin N → Bool) → α) (k : Fin N)
    (L : ℕ) (hcount : (univ.image (condState φ k)).card ≤ N) (hN : 2 * N ≤ L) :
    2 * (univ.image (condState φ k)).card ≤ L :=
  (Nat.mul_le_mul_left 2 hcount).trans hN

/-- **One conditional state in a product state, by its amplitudes** (Sec. IV.A: "In a product
state each string has one conditional state to hold, on all its cells").  In a product state the
amplitude at the joint outcome `k` of the other qubits and the bit `w` of the last qubit is
`α k * β w`.  The first part: two joint outcomes of the other qubits that occur, `α j ≠ 0` and
`α k ≠ 0`, give the last qubit one conditional state, its amplitudes given `j` being those given
`k` times `α j / α k`, a factor that is not zero.  The second part: where two different joint
outcomes of the other qubits occur, it is not the case that every joint outcome has a
conditional state of its own (`Sources.Condition.all_differ` fails), so `Main.overlap_bound`
gives no bound for a product state.  A joint outcome is not a conditioned outcome: one joint
measurement of the strings of a product state shows a joint outcome at each position, and the
strings are not thereby conditioned, since the last qubit has its one conditional state given
every joint outcome of the others that occurs. -/
theorem product_one_state {K : Type*} (α : K → ℂ) (β : Bool → ℂ) (j k : K) (hj : α j ≠ 0)
    (hk : α k ≠ 0) :
    (∃ c : ℂ, c ≠ 0 ∧ ∀ w, α j * β w = c * (α k * β w)) ∧
    (j ≠ k → ¬ ∀ j' k' : K,
      (∃ c : ℂ, c ≠ 0 ∧ ∀ w, α j' * β w = c * (α k' * β w)) → j' = k') := by
  have hone : ∃ c : ℂ, c ≠ 0 ∧ ∀ w, α j * β w = c * (α k * β w) :=
    ⟨α j / α k, div_ne_zero hj hk, fun w => by rw [← mul_assoc, div_mul_cancel₀ _ hk]⟩
  exact ⟨hone, fun hjk hall => hjk (hall j k hone)⟩

/-- **With room for its conditional states, a string can hold each of them with either bit**
(Sec. IV.A: "Each conditional state can then have a block with a cell reading `1` and a cell
reading `−1`, so the bound on the return (below) does not apply to a state of these kinds").
`χ k` stands for the conditional state of one qubit given the joint outcome `k` of the other
qubits: joint outcomes with one label give the qubit one conditional state.  The qubit's string
has two cells for each label (`hroom`, the conclusion of `two_cells_fit`).  Then there are a
pairing `e`, which gives the joint outcome of the other qubits at each position, and bits `b` on
the string, with two properties.  The first: every conditional state has either bit `v` at a
cell whose block holds it.  The second: whatever state `held` the register holds, a conditional
state that occurs with a bit, the probabilities `|held (k, v)|²` of the joint outcomes `k` that
give the state summing to more than zero, has that bit at a cell whose block holds it.  The
second property is Postulate 1's premise as `Main.overlap_bound` and `Main.return_bound` take it
(`Sources.P1.outcomes_at_positions`, by conditioned outcome).  So where the string has room, the
premise does not keep the register from holding any state, the state that the circuit calls for
included, even where the joint outcomes of that state outnumber the cells, and the bound of
`Main.overlap_bound` does not follow for it.  A product state in which every joint outcome of
the other qubits occurs is the case of one label: two cells are room enough at every `N`. -/
theorem room_holds {Cell K T : Type*} [Fintype Cell] [Fintype K] [Nonempty K] [DecidableEq T]
    (χ : K → T) (hroom : 2 * (univ.image χ).card ≤ Fintype.card Cell) :
    ∃ (e : Cell → K) (b : Cell → Bool),
      (∀ k v, ∃ x, χ (e x) = χ k ∧ b x = v) ∧
      ∀ (held : K × Bool → ℂ) (s : T) (v : Bool),
        0 < ∑ k ∈ univ.filter (fun k => χ k = s), ‖held (k, v)‖ ^ 2 →
          ∃ x, χ (e x) = s ∧ b x = v := by
  obtain ⟨U, hU⟩ : ∃ U : Finset T, U = univ.image χ := ⟨_, rfl⟩
  have hcard : Fintype.card (↥U × Bool) ≤ Fintype.card Cell := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, mul_comm, hU]
    exact hroom
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hrep : ∀ t : ↥U, ∃ k, χ k = t.1 := fun t => by
    obtain ⟨k, -, hk⟩ := mem_image.1 ((Finset.ext_iff.1 hU _).1 t.2)
    exact ⟨k, hk⟩
  choose rep hrep using hrep
  obtain ⟨e, he⟩ : ∃ e : Cell → K,
      e = Function.extend (⇑ι) (fun p => rep p.1) (fun _ => Classical.arbitrary K) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Cell → Bool,
      b = Function.extend (⇑ι) (fun p => p.2) (fun _ => true) := ⟨_, rfl⟩
  have hfirst : ∀ k v, ∃ x, χ (e x) = χ k ∧ b x = v := fun k v => by
    have hk : χ k ∈ U := (Finset.ext_iff.1 hU _).2 (mem_image_of_mem χ (mem_univ k))
    refine ⟨ι (⟨χ k, hk⟩, v), ?_, ?_⟩
    · rw [he, ι.injective.extend_apply]
      exact hrep _
    · rw [hb, ι.injective.extend_apply]
  refine ⟨e, b, hfirst, fun held s v hpos => ?_⟩
  obtain ⟨k, hk, -⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨x, hx, hbx⟩ := hfirst k v
  exact ⟨x, hx.trans (mem_filter.1 hk).2, hbx⟩

/-- **A block holds a stabilizer measurement's bit exactly, and shows the product of the
neighbors' bits** (Sec. IV.A: "In a stabilizer measurement each conditional state is a fixed bit,
which a block of any size holds exactly, and a block that holds it shows at every position the
product of the neighbors' bits, as quantum mechanics predicts, at every `N`").  `σ` is the
reading of the qubits other than the measured qubit `k`, and `B` a block of the measured qubit's
string, of any number of cells.  The conditional state of the measured qubit given `σ` gives the
outcome `1` the probability `1` or `0` (`stab_prob`): it is a fixed bit.  The first part: some
bits on the block have that probability as their fraction of 1s, with no rounding, so a block of
any size holds the conditional state exactly.  The second part: on a block that holds it, the
fraction of 1s being that probability, the bit at every position is the product of the bits of
the measured qubit's neighbors, so the stabilizer, the product of the two, reads `1` there, at
every `N`. -/
theorem stabilizer_held {Cell : Type*} (adj : Fin N → Fin N → Prop) [DecidableRel adj]
    (k : Fin N) (σ : Fin N → Bool) (B : Finset Cell) (hne : B.Nonempty) :
    (∃ b : Cell → Bool, Capacity.frac b B
        = ((stabState adj k σ true : ℤ) : ℝ) ^ 2
          / (((stabState adj k σ true : ℤ) : ℝ) ^ 2
            + ((stabState adj k σ false : ℤ) : ℝ) ^ 2)) ∧
    ∀ b : Cell → Bool, Capacity.frac b B
        = ((stabState adj k σ true : ℤ) : ℝ) ^ 2
          / (((stabState adj k σ true : ℤ) : ℝ) ^ 2
            + ((stabState adj k σ false : ℤ) : ℝ) ^ 2) →
      ∀ x ∈ B, pm (b x) * nbrProd adj k σ = 1 := by
  have hcard : (B.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.2 hne).ne'
  rw [stab_prob]
  by_cases h : nbrProd adj k σ = 1
  · rw [ite_eq_left h]
    refine ⟨⟨fun _ => true, ?_⟩, fun b hb x hx => ?_⟩
    · unfold Capacity.frac
      rw [filter_true_of_mem (fun _ _ => rfl), div_self hcard]
    · have hcardeq : (B.filter (fun x => b x = true)).card = B.card := by
        unfold Capacity.frac at hb
        rw [div_eq_one_iff_eq hcard] at hb
        exact_mod_cast hb
      have hall : B.filter (fun x => b x = true) = B :=
        eq_of_subset_of_card_le (filter_subset _ _) hcardeq.ge
      have hbx : b x = true := by
        have hx' : x ∈ B.filter (fun x => b x = true) := by rw [hall]; exact hx
        exact (mem_filter.1 hx').2
      rw [hbx, h]
      norm_num [pm]
  · rw [ite_eq_right h]
    have hm : nbrProd adj k σ = -1 := by
      rcases prod_pm_cases (univ.filter (fun j => (j < k ∧ adj j k) ∨ (k < j ∧ adj k j))) σ
        with h1 | h1
      · exact absurd h1 h
      · exact h1
    refine ⟨⟨fun _ => false, ?_⟩, fun b hb x hx => ?_⟩
    · unfold Capacity.frac
      rw [filter_false_of_mem (fun _ _ => Bool.false_ne_true), card_empty, Nat.cast_zero,
        zero_div]
    · have hz : (B.filter (fun x => b x = true)).card = 0 := by
        unfold Capacity.frac at hb
        rcases div_eq_zero_iff.1 hb with h0 | h0
        · exact_mod_cast h0
        · exact absurd h0 hcard
      have hbx : b x = false := by
        cases hv : b x
        · rfl
        · have hx' : x ∈ B.filter (fun x => b x = true) := mem_filter.2 ⟨hx, hv⟩
          rw [card_eq_zero.1 hz] at hx'
          exact absurd hx' (Finset.notMem_empty x)
      rw [hbx, hm]
      norm_num [pm]

end Conditional
end Register
