import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Pi

/-!
# The entropy of independent strings adds (known mathematics)

Sec. II gives a horizon's entropy as one bit for each string.  A horizon's entropy is the entropy
of its thermal state (thermodynamics, Sec. III).  That state is a state of the strings and of
nothing else: this is Postulate 1, every physical law and quantity defined by qubits and a state a
linear combination of outcomes of its qubits, so that the register is all there is to describe
(the thesis of the paper, Postulate 1's first sentence).  Between
interactions the strings are free, so their thermal state is a product of one distribution per
string (Sec. II).  This file proves the piece of mathematics that then gives the sum: the Shannon
entropy of a product of independent two-outcome distributions is the sum of their binary entropies
(`shannon_jointProb`).  `Bridge.horizonEntropy` is the Shannon entropy of a horizon's state, and
`Bridge.horizon_entropy` applies this file to it.

The second part derives the thermal distribution itself, as mathematics: of all distributions on a
finite set of distinguishable configurations with a given mean energy, the Gibbs distribution has
the most entropy (`shannon_le_shannon_gibbs`, by Gibbs' inequality).  On a free string's two
senses, which have one energy, it is `1/2, 1/2` at every temperature (`gibbs_two_equal`): the
string holds one bit, whatever its one energy.
-/

open Finset

namespace Register.Entropy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the probability of the sense `b` of the string on ring `l`, `p l` for the sense `true` -/
def senseProb (p : ι → ℝ) (l : ι) (b : Bool) : ℝ := if b then p l else 1 - p l

/-- the joint distribution of the strings' senses, the strings independent -/
def jointProb (p : ι → ℝ) (ω : ι → Bool) : ℝ := ∏ l, senseProb p l (ω l)

/-- the Shannon entropy of a distribution on a finite set, in nats -/
noncomputable def shannon {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) : ℝ := ∑ ω, Real.negMulLog (P ω)

omit [Fintype ι] [DecidableEq ι] in
lemma sum_senseProb (p : ι → ℝ) (l : ι) : ∑ b, senseProb p l b = 1 := by
  simp [senseProb]

/-- a sum over all joint senses of a product of one factor per ring is the product of the sums
(`Finset.prod_univ_sum`) -/
lemma sum_prod_senses (r : ι → Bool → ℝ) :
    ∑ ω : ι → Bool, ∏ l, r l (ω l) = ∏ l, ∑ b, r l b := by
  rw [prod_univ_sum (fun _ => (univ : Finset Bool)) r, Fintype.piFinset_univ]

/-- the mean of a function of one ring's sense under the joint distribution is its mean under that
ring's own distribution -/
lemma sum_jointProb_mul (p : ι → ℝ) (l₀ : ι) (g : Bool → ℝ) :
    ∑ ω : ι → Bool, jointProb p ω * g (ω l₀) = ∑ b, senseProb p l₀ b * g b := by
  let r : ι → Bool → ℝ := fun l b => if l = l₀ then senseProb p l b * g b else senseProb p l b
  have h1 : ∀ ω : ι → Bool, jointProb p ω * g (ω l₀) = ∏ l, r l (ω l) := by
    intro ω
    unfold jointProb
    rw [← mul_prod_erase univ (fun l => senseProb p l (ω l)) (mem_univ l₀),
      ← mul_prod_erase univ (fun l => r l (ω l)) (mem_univ l₀)]
    have h2 : ∏ x ∈ univ.erase l₀, r x (ω x) = ∏ x ∈ univ.erase l₀, senseProb p x (ω x) :=
      prod_congr rfl fun x hx => by simp [r, (mem_erase.1 hx).1]
    simp only [r, ite_true, h2]
    ring
  simp_rw [h1]
  rw [sum_prod_senses]
  rw [← mul_prod_erase univ (fun l => ∑ b, r l b) (mem_univ l₀)]
  have h3 : ∏ x ∈ univ.erase l₀, ∑ b, r x b = 1 := by
    apply prod_eq_one
    intro x hx
    simp only [r, (mem_erase.1 hx).1, ite_false]
    exact sum_senseProb p x
  simp only [r, ite_true, h3, mul_one]

/-- the probability that the string on ring `l` has the sense `b`, under the joint distribution `P`
of all the strings' senses -/
def marginal (P : (ι → Bool) → ℝ) (l : ι) (b : Bool) : ℝ :=
  ∑ ω : ι → Bool, if ω l = b then P ω else 0

/-- the probability that the strings other than the one on ring `l` have the senses of `ω`, the
string on `l` having either sense -/
def othersProb (P : (ι → Bool) → ℝ) (l : ι) (ω : ι → Bool) : ℝ :=
  ∑ b : Bool, P (Function.update ω l b)

/-- **The correlation of a string with the other strings**: the joint distribution of the strings'
senses less the product of the string's own distribution and that of the others.  It is zero at
every joint sense exactly when the string's sense is independent of the others'. -/
def correlation (P : (ι → Bool) → ℝ) (l : ι) (ω : ι → Bool) : ℝ :=
  P ω - marginal P l (ω l) * othersProb P l ω

/-- **Free strings are uncorrelated**: under the joint distribution of independent strings
(`jointProb`), each string's own distribution is its factor, the others' is the product of
theirs, and every string's correlation with the others is zero. -/
theorem correlation_jointProb (p : ι → ℝ) (l : ι) (ω : ι → Bool) :
    correlation (jointProb p) l ω = 0 := by
  -- the string's own distribution
  have hm : marginal (jointProb p) l (ω l) = senseProb p l (ω l) := by
    have h := sum_jointProb_mul p l (fun b => if b = ω l then (1 : ℝ) else 0)
    simp only [mul_ite, mul_one, mul_zero] at h
    unfold marginal
    rw [h]
    simp
  -- the others' distribution
  have ho : othersProb (jointProb p) l ω = ∏ k ∈ univ.erase l, senseProb p k (ω k) := by
    unfold othersProb jointProb
    have e : ∀ b, ∏ k, senseProb p k (Function.update ω l b k) =
        senseProb p l b * ∏ k ∈ univ.erase l, senseProb p k (ω k) := by
      intro b
      rw [← mul_prod_erase univ (fun k => senseProb p k (Function.update ω l b k)) (mem_univ l),
        Function.update_self]
      congr 1
      exact prod_congr rfl fun k hk => by rw [Function.update_of_ne (mem_erase.1 hk).1]
    simp_rw [e]
    rw [← sum_mul, sum_senseProb, one_mul]
  unfold correlation
  rw [hm, ho]
  unfold jointProb
  rw [← mul_prod_erase univ (fun k => senseProb p k (ω k)) (mem_univ l), sub_self]

/-- **The entropy of independent strings adds** (known mathematics): the Shannon entropy of the
joint distribution of the strings' senses, the strings independent, is the sum of the binary
entropies of the strings.  The identity holds for any real weights `p l`; for `0 ≤ p l ≤ 1` the
joint distribution is a probability distribution. -/
theorem shannon_jointProb (p : ι → ℝ) :
    shannon (jointProb p) = ∑ l, Real.binEntropy (p l) := by
  -- the entropy of each joint sense splits over the rings
  have hsplit : ∀ ω : ι → Bool, Real.negMulLog (jointProb p ω) =
      ∑ l, jointProb p ω * (-Real.log (senseProb p l (ω l))) := by
    intro ω
    by_cases h0 : ∀ l, senseProb p l (ω l) ≠ 0
    · unfold jointProb Real.negMulLog
      rw [Real.log_prod (fun l _ => h0 l), mul_sum]
      exact sum_congr rfl fun l _ => by ring
    · push Not at h0
      obtain ⟨l, hl⟩ := h0
      have hz : jointProb p ω = 0 := by
        unfold jointProb
        exact prod_eq_zero (mem_univ l) hl
      simp [hz]
  unfold shannon
  simp_rw [hsplit]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_jointProb_mul p l (fun b => -Real.log (senseProb p l b))]
  rw [Fintype.sum_bool]
  simp only [senseProb, Bool.false_eq_true, ite_true, ite_false]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold Real.negMulLog
  ring

/-! ### The thermal distribution derived: the distribution of most entropy over the
distinguishable configurations (thermodynamics as mathematics; Sec. IV.E) -/

/-- **The Gibbs distribution** on a finite set `Ω` of distinguishable configurations with energies
`E`, at the inverse temperature `β`: `e^{−βE}` over its sum. -/
noncomputable def gibbs {Ω : Type*} [Fintype Ω] (E : Ω → ℝ) (β : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-β * E ω) / ∑ ω', Real.exp (-β * E ω')

/-- the sum of the Boltzmann factors is positive -/
lemma sum_exp_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) (β : ℝ) :
    0 < ∑ ω, Real.exp (-β * E ω) :=
  sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/-- every configuration has positive weight -/
lemma gibbs_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) (β : ℝ) (ω : Ω) :
    0 < gibbs E β ω :=
  div_pos (Real.exp_pos _) (sum_exp_pos E β)

/-- the Gibbs distribution sums to one -/
lemma sum_gibbs {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) (β : ℝ) :
    ∑ ω, gibbs E β ω = 1 := by
  unfold gibbs
  rw [← sum_div, div_self (sum_exp_pos E β).ne']

/-- the logarithm of a Gibbs weight -/
lemma log_gibbs {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) (β : ℝ) (ω : Ω) :
    Real.log (gibbs E β ω) = -β * E ω - Real.log (∑ ω', Real.exp (-β * E ω')) := by
  unfold gibbs
  rw [Real.log_div (Real.exp_pos _).ne' (sum_exp_pos E β).ne', Real.log_exp]

/-- **Gibbs' inequality**, one configuration at a time: for `0 ≤ p` and `0 < q`,
`−p log p + p log q ≤ q − p`. -/
lemma negMulLog_add_mul_log_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p + p * Real.log q ≤ q - p := by
  rcases hp.lt_or_eq with hp' | rfl
  · unfold Real.negMulLog
    have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp')
    rw [Real.log_div hq.ne' hp'.ne'] at h1
    have h2 : p * (Real.log q - Real.log p) ≤ p * (q / p - 1) :=
      mul_le_mul_of_nonneg_left h1 hp'.le
    have h3 : p * (q / p - 1) = q - p := by field_simp
    rw [h3] at h2
    linarith
  · simp [Real.negMulLog]; exact hq.le

/-- **Of all distributions on the distinguishable configurations with a given mean energy, the
Gibbs distribution has the most entropy** (thermodynamics as mathematics; Sec. IV.E).  Let
`P` be a distribution on `Ω` whose mean energy is that of the Gibbs distribution at `β`.  Then the
Shannon entropy of `P` is at most that of the Gibbs distribution: by Gibbs' inequality
(`negMulLog_add_mul_log_le`), `−Σ P log P ≤ −Σ P log g`, and `−log g = βE + log Z` is linear in
the energy, so the right side is `β` times the mean energy plus `log Z`, which is the entropy of
`g` itself.  So the thermal state of a system in equilibrium at a temperature, the Gibbs state, is
the distribution of most entropy over its distinguishable configurations at its mean energy, and
nothing else: this is what "Thermodynamics distributes a system over its distinguishable
configurations" says (Sec. IV.E).
For a free string the distinguishable configurations are the two outcomes of its qubit, its two
senses, with one energy (`hsense` of `Qubit.Tick`), and the Gibbs distribution on them is
`1/2, 1/2` (`Qubit.Tick.state_eq`): one bit, and the string's one energy, at every temperature.  The
hidden global phase is no configuration, since no law depends on it (Postulate 1), so it carries
neither entropy nor a distribution. -/
theorem shannon_le_shannon_gibbs {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) (β : ℝ)
    (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hPsum : ∑ ω, P ω = 1)
    (hmean : ∑ ω, P ω * E ω = ∑ ω, gibbs E β ω * E ω) :
    shannon P ≤ shannon (gibbs E β) := by
  set Z := ∑ ω', Real.exp (-β * E ω') with hZ
  -- Gibbs' inequality, summed
  have hG : ∑ ω, (Real.negMulLog (P ω) + P ω * Real.log (gibbs E β ω)) ≤ 0 := by
    calc ∑ ω, (Real.negMulLog (P ω) + P ω * Real.log (gibbs E β ω))
        ≤ ∑ ω, (gibbs E β ω - P ω) :=
          sum_le_sum fun ω _ => negMulLog_add_mul_log_le (hP ω) (gibbs_pos E β ω)
      _ = 0 := by rw [sum_sub_distrib, sum_gibbs, hPsum, sub_self]
  -- `−Σ P log g = β ⟨E⟩_P + log Z`
  have hlin : ∀ Q : Ω → ℝ, ∑ ω, Q ω = 1 →
      -∑ ω, Q ω * Real.log (gibbs E β ω) = β * ∑ ω, Q ω * E ω + Real.log Z := by
    intro Q hQ
    simp_rw [log_gibbs]
    rw [← hZ]
    have : ∑ ω, Q ω * (-β * E ω - Real.log Z) = -β * ∑ ω, Q ω * E ω - Real.log Z * ∑ ω, Q ω := by
      rw [mul_sum, mul_sum]
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun ω _ => by ring
    rw [this, hQ]
    ring
  -- the entropy of the Gibbs distribution is `β ⟨E⟩_g + log Z`
  have hg : shannon (gibbs E β) = β * ∑ ω, gibbs E β ω * E ω + Real.log Z := by
    rw [← hlin _ (sum_gibbs E β)]
    unfold shannon Real.negMulLog
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun ω _ => by ring
  have hP' : shannon P ≤ -∑ ω, P ω * Real.log (gibbs E β ω) := by
    unfold shannon
    rw [sum_add_distrib] at hG
    linarith
  rw [hlin P hPsum, hmean, ← hg] at hP'
  exact hP'

/-- **Two distinguishable configurations of one energy are weighted alike at every temperature**
(Secs. II and IV.E): the Gibbs distribution on a free string's two senses, which have one energy
(`hsense` of `Qubit.Tick`), is `1/2, 1/2`, whatever `β`; so the string holds one bit, whatever its
one energy (`Qubit.Tick.state_eq` is the same statement for
the qubit's density matrix). -/
theorem gibbs_two_equal (E : Bool → ℝ) (β : ℝ) (hE : E true = E false) (b : Bool) :
    gibbs E β b = 1 / 2 := by
  unfold gibbs
  rw [Fintype.sum_bool, hE]
  have h : 0 < Real.exp (-β * E false) := Real.exp_pos _
  have key : Real.exp (-β * E false) / (Real.exp (-β * E false) + Real.exp (-β * E false)) =
      1 / 2 := by
    field_simp
    ring
  cases b
  · exact key
  · rw [hE]; exact key

end Register.Entropy
