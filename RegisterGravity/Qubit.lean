import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The qubit of a free string (Secs. II and IV.E)

Postulate 1 makes quantum mechanics granular: a string is one qubit, and its state is given up to a
global phase.  This file holds the small part of the quantum mechanics of one qubit that the paper
uses, so that the steps below are theorems and not premises argued in words.  What it takes of
quantum mechanics is in the words of the postulates and of Sec. II's definitions: a state is a
linear combination of outcomes of its
qubits (Postulate 1), so a qubit's states are the vectors over its two outcomes and a tick is a
linear map on them (`Vec`, `Op`); the bits are the possible outcomes of one measurement, so the
probability of an outcome is its share of the bits (Postulate 1; with Eqs. (qubit) and (raqm), `stringState`); and
the tick of a state of energy `E` is the factor `e^{−iEt_c/ℏ}`, by Sec. II's definition of energy
(`Sources.P1.string_energies`, a premise of `Main.string_energy`, not a definition of this file:
the strings' mean energy comes from the Gibbs distribution at the horizon's temperature,
Sec. IV.E, and the definition then gives the factor of a tick of that energy, `e^{−i/L}`).  That a tick is a linear map
on the states (`Op`) is Sec. II's "The tick is linear, since a state is a linear combination of
outcomes (Postulate 1)", with the qubit a two-level quantum system by Sec. II's definition; it is
what carries one factor from the two senses to every superposition of them.  `L ≠ 0` is assumed where a ring's
length enters a bound (`[NeZero L]`).

**The two outcomes, and what a free tick does** (the paper's Sec. II, "The entropy"; these are the
paper's statements, and the fields below take of them only what they say): the shift of
Postulate 1 is a translation along the ring, and a translation along a ring can go two ways, with
the ring or against it, the two senses.  Reading which sense a string has is a measurement with two
values, and the string's bits are its possible outcomes: by the definition of the bit values, `e₁`
is the outcome `1`, the string of all 1s, the sense with the ring, and `e₂` the outcome `−1`, the
string of all −1s, the sense against it (the register paper's doublet).  A string
is one qubit (Postulate 1), two outcomes and a phase, its cyclic position being the phase: it has
no further states; a moving string's further states, its momentum, are the register paper's larger
model and are not used here.  A string with `m` 1s is a superposition of the two
senses, `m/L` the probability of the first (Eq. (raqm)), and its cyclic position, the qubit's phase
(Postulate 1), is the relative phase of the two.  A string of one sense has the same bit on every
cell, so the shift leaves it as it is up to its global phase, and that phase changes alike in
either sense (`hsense`, the sentence as written): no bit moves, and the one thing that changes
from tick to tick is the global phase common to both senses (`Tick.phase_unique`).  Read instead
as a pattern of bits that the tick moves one cell, "the string's cyclic position on its ring is the
qubit's phase" would turn the phase by one cell per tick, `U ∝ diag(1, e^{2πi/L})`, the tick of earlier
versions, which `hsense` excludes.

* `Tick`: the free tick on the qubit, one sentence of the paper taken once, in its words.
  Sec. II: "A string of one sense has the same bit on every cell, so the shift leaves it as it is,
  up to its global phase (Postulate 1), and that phase changes alike in either sense, since no law
  depends on the ring's direction (Postulate 2)": the tick keeps each of the two strings of one
  sense up to one and the same phase (`hsense`).  A global phase is a factor `e^{iγ}` on all the
  amplitudes (Sec. II's definition), so the factor has modulus one: the field says of it what the
  sentence says, and no more.
* `Tick.phase_unique`: the tick is a linear map on the states (quantum mechanics; a state is a
  linear combination of the outcomes, Postulate 1), so with one factor on both senses it is
  diagonal in them (`eq_diagonal_of_keeps`) with that factor on both, `U = c • 1`.  The energy is
  then the same for every state of the string, so it adds no state (Sec. IV.E), and no relative
  phase of the two senses turns under the free tick.
* `Tick.norm_scalar`: the factor is a phase, `‖c‖ = 1`, the phase of `hsense`.
* `Tick.ofPhase`: the tick of factor `e^{−iθ}` on every state, for any angle `θ`; it meets
  `hsense`, so the free tick of a string of any energy exists (`Reg.string_tick` gives the factor
  of a string of energy `k_BT_dS`, `e^{−i/L}`, from Sec. II's definition of energy).  The tick fixes its
  factor and nothing more: a phase is defined only up to whole turns, so the factor alone does not
  fix an energy, and the files fix none; the strings' mean energy comes from the Gibbs
  distribution at the horizon's temperature (Sec. IV.E, `Carriers.string_energy`).
* `Tick.factor`, `Tick.factor_eq`, `Tick.energy`, `Tick.energy_eq`: the tick multiplies the string
  of each sense by a factor (`Tick.mulVec_e₁`, `Tick.mulVec_e₂`), and the two factors are one
  (`hsense`).  Sec. II defines the energy of a state by the factor of its tick, "A state that one
  tick multiplies by `e^{−iΔ}` has energy `ℏΔ/t_c`", so the energy of a string of one
  sense is a function `En` of its factor, which every statement leaves open.  One factor is then
  one energy: the two senses of a free string have one energy, whatever `En` is.
* `thermal_of_equal`, `bornProb_thermal`, `entropy_thermal`: the thermal state of a qubit whose two
  basis states have one energy is half the identity, whatever the temperature.  It gives either
  outcome of any measurement the probability `1/2` (the Born rule, `bornProb`; `prob` reads the
  same probability off the diagonal), and its entropy is one bit, `ln 2`: the sense bit of Sec. II
  is the qubit's bit, one and the same.
* `Tick.state`, `Tick.state_eq`, `Tick.bornProb_state`, `Tick.prob_state`, `Tick.entropy_state`:
  the thermal state of a free string is the Gibbs state over its two senses, each at its energy.
  The definition does not put the two energies equal: `Tick.state_eq` derives from
  `Tick.energy_eq` that the state is half the identity, so that the string holds one bit
  (`Main.string_one_bit`).  `Solution.state_same` carries this state in the state at a crossing,
  and `Bridge.horizon_entropy` sums the bit over the strings.
* `stringState`, `share_stringState`, `expected_share`, `half_bits_thermal`: the state of a string
  with `m` 1s and the relative phase `2πn/L`, Eq. (qubit), with the share of the bits as the
  probability of the outcome `1` (Postulate 1; Eq. (raqm)); the probability of `1` in it is `m/L`; under any
  mixture of strings the expected share is the Born probability of `1` in its density matrix; so
  half the bits of a string in the horizon's thermal state are 1s, on average (Sec. II), since that
  state is half the identity.  `half_bits_model` meets the hypothesis.
-/

open Matrix

namespace Register.Qubit

/-! ### The qubit's space, its two senses, and the tick on it -/

/-- a vector of the qubit's two-dimensional space -/
abbrev Vec := Fin 2 → ℂ
/-- an operator on it -/
abbrev Op := Matrix (Fin 2) (Fin 2) ℂ

/-- the basis state of the outcome `1`: the string of all 1s, the sense with the ring -/
def e₁ : Vec := ![1, 0]
/-- the basis state of the outcome `-1`: the string of all −1s, the sense against the ring -/
def e₂ : Vec := ![0, 1]

/-- **A map that keeps both senses up to a factor is diagonal in them** (linear algebra): its
columns are its values on `e₁` and `e₂`. -/
theorem eq_diagonal_of_keeps (T : Op) (c₁ c₂ : ℂ) (h₁ : T *ᵥ e₁ = c₁ • e₁)
    (h₂ : T *ᵥ e₂ = c₂ • e₂) : T = Matrix.diagonal ![c₁, c₂] := by
  have a0 := congrFun h₁ 0
  have a1 := congrFun h₁ 1
  have b0 := congrFun h₂ 0
  have b1 := congrFun h₂ 1
  simp [e₁, e₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1 b0 b1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, a0, a1, b0, b1]

/-- **The free tick on a string's qubit** (Secs. II and IV.E), for a string on a ring of `L` cells:
`U` is the tick, a linear map on the qubit's states (Sec. II: a state is a linear combination of
outcomes, Postulate 1, so the tick is linear).  One sentence of the paper is taken, once, in its words.  Sec. II: "A string of
one sense has the same bit on every cell, so the shift leaves it as it is, up to its global phase
(Postulate 1), and that phase changes alike in either sense, since no law depends on the ring's
direction (Postulate 2)."  The strings of one sense are the strings of all 1s and of all −1s, the
two outcomes (Sec. II, by the definition of the bit values), so the tick keeps each of them up to a
global phase, a factor `e^{iγ}` on all the amplitudes (Sec. II's definition of the global phase),
and the phase is the same for both (`hsense`).  Nothing else is assumed: that the tick is one
factor on every state (`Tick.phase_unique`) follows.  A reversal of a bit's sense is a change of a
bit, so it is an interaction (Postulate 1) and no part of a free tick. -/
structure Tick (L : ℕ) where
  /-- the tick -/
  U : Op
  /-- the tick keeps each string of one sense, the string of all 1s and the string of all −1s, up
  to one and the same phase, a factor of modulus one (Sec. II: the shift leaves a string of one
  sense as it is up to its global phase, Postulate 1, and that phase changes alike in either sense,
  Postulate 2) -/
  hsense : ∃ c : ℂ, ‖c‖ = 1 ∧ U *ᵥ e₁ = c • e₁ ∧ U *ᵥ e₂ = c • e₂

variable {L : ℕ}

/-- a map with one factor on both senses is that factor times the identity
(`eq_diagonal_of_keeps`) -/
theorem eq_smul_one_of_keeps (T : Op) (c : ℂ) (h₁ : T *ᵥ e₁ = c • e₁) (h₂ : T *ᵥ e₂ = c • e₂) :
    T = c • (1 : Op) := by
  rw [eq_diagonal_of_keeps T c c h₁ h₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- **The tick's factor is one for all the string's states** (Sec. IV.E): one factor on both senses
(`hsense`), and the tick is a linear map on the states (quantum mechanics; a state is a linear
combination of the outcomes, Postulate 1), so it is diagonal in the senses (`eq_diagonal_of_keeps`)
with one entry, `U = c • 1`.  This is the whole of a free string's energy: no relative phase of the
two senses turns under the free tick. -/
theorem Tick.phase_unique (T : Tick L) : ∃ c : ℂ, T.U = c • (1 : Op) := by
  obtain ⟨c, -, h₁, h₂⟩ := T.hsense
  exact ⟨c, eq_smul_one_of_keeps T.U c h₁ h₂⟩

/-- the factor of the tick, `U = c • 1` (`phase_unique`) -/
noncomputable def Tick.scalar (T : Tick L) : ℂ := Classical.choose T.phase_unique

/-- the tick is its factor times the identity -/
theorem Tick.scalar_spec (T : Tick L) : T.U = T.scalar • (1 : Op) :=
  Classical.choose_spec T.phase_unique

/-- the factor of a tick is the one it multiplies every state by -/
theorem Tick.scalar_eq (T : Tick L) (c : ℂ) (h : T.U = c • (1 : Op)) : T.scalar = c := by
  have hs := T.scalar_spec
  rw [h] at hs
  have h00 := congrFun (congrFun hs 0) 0
  simpa using h00.symm

/-- **The tick's factor is a phase**: its modulus is one, the modulus of the global phase of
`hsense`.  So the tick is unitary, as the tick of quantum mechanics is. -/
theorem Tick.norm_scalar (T : Tick L) : ‖T.scalar‖ = 1 := by
  obtain ⟨c, hc, h₁, h₂⟩ := T.hsense
  rw [T.scalar_eq c (eq_smul_one_of_keeps T.U c h₁ h₂)]
  exact hc

/-- **The tick of factor `e^{−iθ}`**: that factor on every state is the tick of a free string, for
any angle `θ`.  It keeps each string of one sense up to that one factor, a phase (`hsense`). -/
noncomputable def Tick.ofPhase (θ : ℝ) : Tick L where
  U := Complex.exp (-(θ : ℂ) * Complex.I) • (1 : Op)
  hsense := ⟨Complex.exp (-(θ : ℂ) * Complex.I),
    by simpa using Complex.norm_exp_ofReal_mul_I (-θ),
    by rw [Matrix.smul_mulVec, Matrix.one_mulVec], by rw [Matrix.smul_mulVec, Matrix.one_mulVec]⟩

/-! ### The thermal state of a free string, the Born rule and the bit -/

/-- the Boltzmann weight of the first of two states, of energies `E₁` and `E₂`, at the inverse
temperature `β` (thermodynamics) -/
noncomputable def weight (β E₁ E₂ : ℝ) : ℝ :=
  Real.exp (-(β * E₁)) / (Real.exp (-(β * E₁)) + Real.exp (-(β * E₂)))

/-- **The thermal state** `e^{−βH}/Z` of a qubit whose basis states `e₁`, `e₂` have the energies
`E₁`, `E₂` (thermodynamics): diagonal in that basis, with the Boltzmann weights. -/
noncomputable def thermal (β E₁ E₂ : ℝ) : Op :=
  Matrix.diagonal ![(weight β E₁ E₂ : ℂ), (weight β E₂ E₁ : ℂ)]

/-- **Equal energies, equal weights**: with `E₁ = E₂` each weight is `1/2`. -/
lemma weight_of_equal (β E : ℝ) : weight β E E = 1 / 2 := by
  unfold weight
  have h := Real.exp_pos (-(β * E))
  field_simp
  ring

/-- **The thermal state of a qubit whose two states have one energy is half the identity**, at every
temperature: `e^{−βH}/Z` with `H` a multiple of the identity.  A free string is such a qubit, its
two senses having one energy (`Tick.energy_eq`, from `hsense`). -/
theorem thermal_of_equal (β E : ℝ) : thermal β E E = (1 / 2 : ℂ) • (1 : Op) := by
  unfold thermal
  rw [weight_of_equal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- the probability of the outcome `v`, a unit vector, in the state `ρ`: `⟨v, ρ v⟩`, the square of
the outcome's amplitude for a pure state and the average for a mixture.  For a string's state
(`stringState`) it is the string's share of the bits (`share_stringState`), as Postulate 1 says. -/
noncomputable def bornProb (ρ : Op) (v : Vec) : ℝ := (star v ⬝ᵥ ρ *ᵥ v).re

/-- the basis state `e₁` is a unit vector -/
lemma e₁_unit : star e₁ ⬝ᵥ e₁ = 1 := by
  simp [e₁, dotProduct, Fin.sum_univ_two]

/-- **Half the identity gives every outcome the probability `1/2`**: for a unit vector `v`,
`⟨v, v/2⟩ = 1/2`. -/
theorem bornProb_half (v : Vec) (hv : star v ⬝ᵥ v = 1) :
    bornProb ((1 / 2 : ℂ) • (1 : Op)) v = 1 / 2 := by
  unfold bornProb
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hv]
  norm_num

/-- **A free string reads a `1` with the probability `1/2`**: its thermal state is half the identity
(`thermal_of_equal`), and the Born rule gives the outcome `e₁` the probability `1/2`
(`bornProb_half`). -/
theorem bornProb_thermal (β E : ℝ) : bornProb (thermal β E E) e₁ = 1 / 2 := by
  rw [thermal_of_equal]
  exact bornProb_half e₁ e₁_unit

/-- the probability of the basis outcome `i` in the state `ρ`: the diagonal entry `ρ i i`, the
Born probability of the basis vector -/
noncomputable def prob (ρ : Op) (i : Fin 2) : ℝ := (ρ i i).re

/-- the thermal state of a qubit whose two states have one energy gives each basis outcome the
probability `1/2` -/
theorem prob_thermal (β E : ℝ) (i : Fin 2) : prob (thermal β E E) i = 1 / 2 := by
  rw [thermal_of_equal]
  fin_cases i <;> simp [prob]

/-- the entropy of a state diagonal in the basis, with the weight `p` on `e₁`: the binary entropy
`−p ln p − (1 − p) ln (1 − p)`, the von Neumann entropy of `diag(p, 1 − p)` -/
noncomputable def entropy (p : ℝ) : ℝ := Real.binEntropy p

/-- **A free string holds one bit** (Sec. II, "The entropy"): the thermal state of a qubit whose two
states have one energy has the weight `1/2` on each, and the entropy `ln 2`, the most a state
diagonal in the senses can hold (`Real.binEntropy_le_log_two`).  The two states are the two senses,
so this bit is the sense bit of Sec. II. -/
theorem entropy_thermal (β E : ℝ) :
    entropy (prob (thermal β E E) 0) = Real.log 2 ∧ ∀ p, entropy p ≤ Real.log 2 := by
  refine ⟨?_, fun p => Real.binEntropy_le_log_two⟩
  rw [prob_thermal, entropy, one_div, Real.binEntropy_two_inv]

/-! ### The thermal state of a free string -/

/-- **The factor by which the tick multiplies the string of one sense**: `true` is the sense with
the ring, the string of all 1s, `e₁`, and `false` the sense against it, the string of all −1s,
`e₂` (`Tick.mulVec_e₁`, `Tick.mulVec_e₂`). -/
def Tick.factor (T : Tick L) (s : Bool) : ℂ := if s then T.U 0 0 else T.U 1 1

/-- the tick multiplies the string of all 1s by its factor -/
theorem Tick.mulVec_e₁ (T : Tick L) : T.U *ᵥ e₁ = T.factor true • e₁ := by
  obtain ⟨c, hc⟩ := T.phase_unique
  simp [Tick.factor, hc, Matrix.smul_mulVec]

/-- the tick multiplies the string of all −1s by its factor -/
theorem Tick.mulVec_e₂ (T : Tick L) : T.U *ᵥ e₂ = T.factor false • e₂ := by
  obtain ⟨c, hc⟩ := T.phase_unique
  simp [Tick.factor, hc, Matrix.smul_mulVec]

/-- **The two senses have one factor** (Sec. II: "that phase changes alike in either sense, since
no law depends on the ring's direction (Postulate 2)"; `hsense`, through `phase_unique`). -/
theorem Tick.factor_eq (T : Tick L) : T.factor true = T.factor false := by
  obtain ⟨c, hc⟩ := T.phase_unique
  simp [Tick.factor, hc]

/-- **The energy of a string of one sense**: the energy of the factor by which the tick multiplies
it.  Sec. II defines the energy of a state by that factor, "A state that one tick multiplies by
`e^{−iΔ}` has energy `ℏΔ/t_c`, as in quantum mechanics", so the
energy is a function `En` of the factor.  A factor fixes `Δ` only up to whole turns, and `En` is
that function for whatever choice of the turn: nothing below depends on the choice. -/
def Tick.energy (T : Tick L) (En : ℂ → ℝ) (s : Bool) : ℝ := En (T.factor s)

/-- **The two senses of a free string have one energy** (Secs. II and IV.E): one factor
(`factor_eq`), so one energy, whatever function of the factor the energy is. -/
theorem Tick.energy_eq (T : Tick L) (En : ℂ → ℝ) : T.energy En true = T.energy En false :=
  congrArg En T.factor_eq

/-- **The thermal state of a free string** at the inverse temperature `β` (thermodynamics): the
Gibbs state `e^{−βH}/Z` over the string's two senses, each at its energy, the energy `En` of the
factor by which the tick multiplies it (`Tick.energy`).  That the two energies are one is not put
in here: `Tick.state_eq` derives it from `hsense`.  The strings' energies differ from string to
string with their factors; their mean, `k_BT_dS`, is `Carriers.string_energy`. -/
noncomputable def Tick.state (T : Tick L) (β : ℝ) (En : ℂ → ℝ) : Op :=
  thermal β (T.energy En true) (T.energy En false)

/-- **A free string's thermal state is half the identity**, at every temperature: its two senses
have one energy (`energy_eq`, from `hsense`), so the Gibbs state weights them equally
(`thermal_of_equal`). -/
theorem Tick.state_eq (T : Tick L) (β : ℝ) (En : ℂ → ℝ) :
    T.state β En = (1 / 2 : ℂ) • (1 : Op) := by
  unfold Tick.state
  rw [T.energy_eq En]
  exact thermal_of_equal _ _

/-- **A free string reads a `1` with the probability `1/2`**: the Born rule in its thermal state.
With `expected_share` it gives `half_bits_thermal`. -/
theorem Tick.bornProb_state (T : Tick L) (β : ℝ) (En : ℂ → ℝ) :
    bornProb (T.state β En) e₁ = 1 / 2 := by
  unfold Tick.state
  rw [T.energy_eq En]
  exact bornProb_thermal _ _

/-- each basis outcome has the probability `1/2` in a free string's thermal state: each sense -/
theorem Tick.prob_state (T : Tick L) (β : ℝ) (En : ℂ → ℝ) (i : Fin 2) :
    prob (T.state β En) i = 1 / 2 := by
  unfold Tick.state
  rw [T.energy_eq En]
  exact prob_thermal _ _ i

/-- **A free string holds one bit** (Sec. II, "The entropy"): the entropy of its thermal state,
read on the two senses, is `ln 2`, since the senses have one energy (`energy_eq`,
`entropy_thermal`). -/
theorem Tick.entropy_state (T : Tick L) (β : ℝ) (En : ℂ → ℝ) :
    entropy (prob (T.state β En) 0) = Real.log 2 := by
  unfold Tick.state
  rw [T.energy_eq En]
  exact (entropy_thermal _ _).1

/-! ### The state of a string, Eq. (qubit), and its share of 1s, Eq. (raqm) -/

/-- **The state of a string with `m` ones and the relative phase `2πn/L`**, Eq. (qubit) of the paper
(a unit vector for `m ≤ L`):
the probability of the outcome `1`, the first sense, is its share of the bits, `m/L` (Postulate 1:
the bits are the possible outcomes of one measurement of the qubit), the amplitude of an outcome is
the square root of its probability (Eq. (qubit)), and the string's cyclic position is the qubit's
phase, `2πn/L`, the relative phase of the two senses (Postulate 1; Eq. (raqm)).  Every state is a
linear combination of the outcomes (Postulate 1), here of `e₁` and `e₂`. -/
noncomputable def stringState (L m n : ℕ) : Vec :=
  ![(Real.sqrt (m / L) : ℂ),
    Complex.exp (2 * Real.pi * Complex.I * n / L) * (Real.sqrt (1 - m / L) : ℂ)]

/-- the projector `|v⟩⟨v|` onto a state, the density matrix of the pure state `v` -/
noncomputable def proj (v : Vec) : Op := Matrix.vecMulVec v (star v)

/-- the Born probability of `e₁` in a pure state is the squared modulus of its first amplitude -/
theorem bornProb_proj (v : Vec) : bornProb (proj v) e₁ = Complex.normSq (v 0) := by
  unfold bornProb proj
  simp [e₁, mulVec, dotProduct, Fin.sum_univ_two, vecMulVec, Complex.normSq_apply]

/-- **The probability of the outcome `1` in a string's state is its share of the bits**, `m/L`
(Postulate 1 with Eq. (raqm)): the square of the amplitude is the share it is the square root of. -/
theorem share_stringState (L m n : ℕ) : bornProb (proj (stringState L m n)) e₁ = m / L := by
  rw [bornProb_proj]
  simp only [stringState, Matrix.cons_val_zero]
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]

/-- **Under a mixture of strings, the expected share of 1s is the Born probability of `1` in the
mixture's density matrix**: the probability of `1` is linear in the state, and in each string's
state it is the string's share (`share_stringState`). -/
theorem expected_share {S : Type*} [Fintype S] (L : ℕ) (m n : S → ℕ) (p : S → ℝ) (ρ : Op)
    (hρ : ρ = ∑ s, (p s : ℂ) • proj (stringState L (m s) (n s))) :
    ∑ s, p s * (m s / L) = bornProb ρ e₁ := by
  subst hρ
  unfold bornProb
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have h := share_stringState L (m s) (n s)
  unfold bornProb at h
  rw [h]

/-- **Half the bits of a string in the thermal state are 1s** (Sec. II, "The entropy"), on
average over the thermal mixture: a free string's thermal state is half the identity
(`Tick.state_eq`), whose Born probability of `1` is `1/2` (`Tick.bornProb_state`), so a mixture of
strings `p` that realizes it (`hρ`) has the expected share of 1s `1/2` (`expected_share`); the
theorem says nothing about which strings realize it (`half_bits_model` is one mixture).  This is
the `hones` that `Solution.state_same` took from `hborn` until 19 October, now a theorem. -/
theorem half_bits_thermal {S : Type*} [Fintype S] (T : Tick L) (β : ℝ) (En : ℂ → ℝ)
    (m n : S → ℕ) (p : S → ℝ)
    (hρ : T.state β En = ∑ s, (p s : ℂ) • proj (stringState L (m s) (n s))) :
    ∑ s, p s * (m s / L) = 1 / 2 := by
  rw [expected_share L m n p _ hρ, T.bornProb_state]

/-- the hypothesis of `half_bits_thermal` can be met: the equal mixture of the all-1 string and
the all-−1 string, the two senses, is half the identity -/
theorem half_bits_model [NeZero L] (T : Tick L) (β : ℝ) (En : ℂ → ℝ) :
    T.state β En = ∑ s : Fin 2, ((1 / 2 : ℝ) : ℂ) • proj (stringState L (![L, 0] s) 0) := by
  rw [T.state_eq]
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : Real.sqrt L ≠ 0 := Real.sqrt_ne_zero'.2 hL
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, proj, vecMulVec, stringState]
  rw [div_self (by exact_mod_cast hs)]
  norm_num

end Register.Qubit
