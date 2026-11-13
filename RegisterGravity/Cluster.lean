import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A linear cluster state with one layer of rotations (Sec. IV.A)

The paper's Sec. IV.A derives that a linear cluster state followed by one layer of generic
single-qubit rotations reaches the ceiling as a random state does: with the first `N − 1` qubits
measured in the computational basis, the ratio of the last qubit's two amplitudes is

  `r_N = (1 − t r_{N−1}) / (1 + t r_{N−1})`,

where `r_{N−1}` is the same ratio for qubit `N − 1` given the outcomes before it, and `t` is one
of two numbers, `t₀` or `−1/conj t₀`, fixed by the rotation of qubit `N − 1` and its outcome.  The
recursion is the paper's derivation from `|C_N⟩ = (|C_{N−1}⟩|0⟩ + Z_{N−1}|C_{N−1}⟩|1⟩)/√2`; this
file takes it as the definition `moebius` and proves what the paper claims of it:

* each map is one to one where it is defined (`moebius_injOn`);
* the two maps give one value only from two earlier values in the ratio `t₀/t₁ = −|t₀|²`
  (`moebius_collision`, `ratio_eq_neg_normSq`), a negative real number;
* so a step doubles the number of distinct values when `t₀` avoids finitely many conditions
  (`step_card`), and every value stays away from `0` (`step_ne_zero`), the probability of the
  last qubit's outcome strictly between `0` and `1`;
* hence `N − 1` such steps from `r₁ = 1` give `2^(N−1)` distinct nonzero values (`chain_card`):
  the last qubit has a different conditional state, with a probability strictly between `0` and
  `1`, for each joint outcome of the `N − 1` measured qubits.  That every such probability lies
  strictly between `0` and `1` is what `Capacity.lean`'s `ceiling_by_outcome` asks of a state that
  the ceiling binds; the different conditional states are what sets the state apart from a product
  state.
-/

open Finset ComplexConjugate

namespace Register.Cluster

/-- The map of one measured qubit on the amplitude ratio of the next: `z ↦ (1 − t z)/(1 + t z)`. -/
noncomputable def moebius (t z : ℂ) : ℂ := (1 - t * z) / (1 + t * z)

/-- The second number of a rotation, `t₁ = −1/conj t₀` (the two columns of a unitary). -/
noncomputable def tOne (t₀ : ℂ) : ℂ := -1 / conj t₀

lemma tOne_ne_zero {t₀ : ℂ} (h : t₀ ≠ 0) : tOne t₀ ≠ 0 := by
  unfold tOne
  have : conj t₀ ≠ 0 := by
    intro h'
    apply h
    simpa using congrArg conj h'
  exact div_ne_zero (by norm_num) this

/-- `t₀ / t₁ = −|t₀|²`: the collision ratio is a negative real number. -/
lemma ratio_eq_neg_normSq (t₀ : ℂ) : t₀ / tOne t₀ = -(Complex.normSq t₀ : ℂ) := by
  unfold tOne
  rw [div_div_eq_mul_div, div_neg, div_one, Complex.mul_conj]

/-- The map is one to one on the values where its denominator does not vanish. -/
lemma moebius_injOn (t : ℂ) (ht : t ≠ 0) :
    Set.InjOn (moebius t) {z | 1 + t * z ≠ 0} := by
  intro z hz w hw hzw
  have hz' : 1 + t * z ≠ 0 := hz
  have hw' : 1 + t * w ≠ 0 := hw
  unfold moebius at hzw
  rw [div_eq_div_iff hz' hw'] at hzw
  have : t * (w - z) = 0 := by linear_combination hzw / 2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h ht
  · linear_combination -h

/-- Two steps collide, `M_{t₀} z = M_{t₁} z'`, only if `z' = (t₀/t₁) z`. -/
lemma moebius_collision (t₀ t₁ z z' : ℂ) (h₁ : 1 + t₀ * z ≠ 0) (h₂ : 1 + t₁ * z' ≠ 0)
    (ht₁ : t₁ ≠ 0) (h : moebius t₀ z = moebius t₁ z') : z' = t₀ / t₁ * z := by
  unfold moebius at h
  rw [div_eq_div_iff h₁ h₂] at h
  have : t₁ * z' = t₀ * z := by linear_combination h / 2
  rw [div_mul_eq_mul_div, eq_div_iff ht₁]
  linear_combination this

/-- A value stays away from `0` unless `z = 1/t`, and away from `∞` unless `z = −1/t`. -/
lemma moebius_ne_zero (t z : ℂ) (hnum : 1 - t * z ≠ 0) (hden : 1 + t * z ≠ 0) :
    moebius t z ≠ 0 := by
  unfold moebius
  exact div_ne_zero hnum hden

/-- The conditions a step asks of `t₀` on a finite set `S` of earlier values: no denominator or
numerator of either map vanishes on `S`, and no two values of `S` are in the ratio `t₀/t₁`.
Each of the first four excludes one value of `t₀` for each nonzero element of `S`, and the last
excludes, for each pair, one value of `|t₀|²`, a circle of `t₀`: what is excluded has measure zero,
which is what the paper's "generic rotations" means. -/
structure Generic (t₀ : ℂ) (S : Finset ℂ) : Prop where
  /-- the rotation is not the identity's column, `t₀ ≠ 0` -/
  ne : t₀ ≠ 0
  /-- the first map's denominator does not vanish on `S` -/
  den₀ : ∀ z ∈ S, 1 + t₀ * z ≠ 0
  /-- the first map's numerator does not vanish on `S` -/
  num₀ : ∀ z ∈ S, 1 - t₀ * z ≠ 0
  /-- the second map's denominator does not vanish on `S` -/
  den₁ : ∀ z ∈ S, 1 + tOne t₀ * z ≠ 0
  /-- the second map's numerator does not vanish on `S` -/
  num₁ : ∀ z ∈ S, 1 - tOne t₀ * z ≠ 0
  /-- no two values of `S` are in the collision ratio `t₀/t₁ = −|t₀|²` -/
  noCollision : ∀ z ∈ S, ∀ z' ∈ S, z' ≠ t₀ / tOne t₀ * z

/-- One measured qubit: the values after the step, one for each earlier value and each outcome. -/
noncomputable def step (t₀ : ℂ) (S : Finset ℂ) : Finset ℂ :=
  S.image (moebius t₀) ∪ S.image (moebius (tOne t₀))

/-- Every value after a generic step is nonzero. -/
lemma step_ne_zero {t₀ : ℂ} {S : Finset ℂ} (hg : Generic t₀ S) : ∀ w ∈ step t₀ S, w ≠ 0 := by
  intro w hw
  unfold step at hw
  rcases Finset.mem_union.mp hw with h | h
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    exact moebius_ne_zero _ _ (hg.num₀ z hz) (hg.den₀ z hz)
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    exact moebius_ne_zero _ _ (hg.num₁ z hz) (hg.den₁ z hz)

/-- **A generic step doubles the number of distinct values** (Sec. IV.A). -/
lemma step_card {t₀ : ℂ} {S : Finset ℂ} (hg : Generic t₀ S) : (step t₀ S).card = 2 * S.card := by
  unfold step
  have h₀ : (S.image (moebius t₀)).card = S.card :=
    Finset.card_image_of_injOn
      (fun z hz w hw h => moebius_injOn t₀ hg.ne (hg.den₀ z hz) (hg.den₀ w hw) h)
  have h₁ : (S.image (moebius (tOne t₀))).card = S.card :=
    Finset.card_image_of_injOn
      (fun z hz w hw h => moebius_injOn _ (tOne_ne_zero hg.ne) (hg.den₁ z hz) (hg.den₁ w hw) h)
  have hdisj : Disjoint (S.image (moebius t₀)) (S.image (moebius (tOne t₀))) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨z', hz', hzz'⟩ := Finset.mem_image.mp hw'
    have := moebius_collision t₀ (tOne t₀) z z' (hg.den₀ z hz) (hg.den₁ z' hz')
      (tOne_ne_zero hg.ne) hzz'.symm
    exact hg.noCollision z hz z' hz' this
  rw [Finset.card_union_of_disjoint hdisj, h₀, h₁]
  ring

/-- `n` generic steps from `r₁ = 1`: the values after step `k` are those of `step` applied `k`
times, each step with its own `t₀`. -/
noncomputable def chain : (ts : List ℂ) → Finset ℂ
  | [] => {1}
  | t :: ts => step t (chain ts)

/-- A list of rotations is generic when each step is generic on the values before it. -/
def GenericChain : (ts : List ℂ) → Prop
  | [] => True
  | t :: ts => Generic t (chain ts) ∧ GenericChain ts

/-- **The paper's claim** (Sec. IV.A): `n` generic steps give `2^n` distinct values, all nonzero,
so the last qubit has a different conditional state, with a probability strictly between `0` and
`1`, for each of the `2^n` joint outcomes of the `n` measured qubits. -/
theorem chain_card : ∀ (ts : List ℂ), GenericChain ts →
    (chain ts).card = 2 ^ ts.length ∧ ∀ w ∈ chain ts, w ≠ 0
  | [], _ => by
      refine ⟨by simp [chain], ?_⟩
      intro w hw
      simp [chain] at hw
      subst hw
      norm_num
  | t :: ts, h => by
      obtain ⟨hg, hrest⟩ := h
      obtain ⟨hcard, _⟩ := chain_card ts hrest
      refine ⟨?_, step_ne_zero hg⟩
      simp only [chain, List.length_cons]
      rw [step_card hg, hcard]
      ring

end Register.Cluster
