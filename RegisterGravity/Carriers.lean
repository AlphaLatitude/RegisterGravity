import RegisterGravity.Chain
import RegisterGravity.Capacity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# The galactic law from the strings that carry the body's information (Sec. IV.C)

Formal counterpart of Sec. IV.C of *Gravitation from Hilbert-Space Granularity*: the share of a
body's energy among the strings that carry its information, the amplitude of that share, the
threshold of a string, and the law that follows, with its scale `a₀`.  As in `Chain.lean`,
each physical input is a named hypothesis of the theorems that use it, and nothing is declared as
an axiom; `Sources.lean` names each input by its source, and `Main.lean` states the results with
those names.

* `Law.share_of_equipartition`: by Postulate 1 a body's energy is held by strings, a string that
  does not carry the body's information holds none of the body's energy, and equipartition gives
  the mean share of the strings that carry it; so the energy is the number of carriers times
  their mean share, whatever each of them holds.
* `Reg.newton_share`, Eq. (newton) at `g_N`: with Jacobson's `G` and `I1` for the Unruh
  temperature `T_N` of `g_N = GM/r²`, the body's energy is two Landauer energies at `T_N` per
  string of the sphere on average.
* `Reg.share_acceleration`, Eq. (share): with the body's energy held by the fraction `b` of the
  sphere's strings at two Landauer energies each on average, against Eq. (newton) at `g_N`, the
  acceleration is `g_N/b`.
* `Law.gibbsMean_eq`, Eq. (mean), and `Reg.string_energy`: the strings' energies are spread at
  the horizon's temperature and do not change (`hGibbs`), so their mean is the mean of the Gibbs
  distribution over energies from zero up, the horizon's thermal energy `k_BT_dS`; on a ladder of
  equal steps the mean lies within one step of it (`Law.gibbsLadder_eq`,
  `Law.gibbsLadder_within_step`).
* `Reg.fill_fraction`, Eqs. (E), (u) and (f): the body's energy per string, two Landauer energies
  at the Unruh temperature of `g_N`, counted in units of the matter a string holds on average,
  `u = (1 − ln 2)k_BT_dS`,
  is `f = g_N/a₀` with `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`.
* The amplitude of the body's share (Sec. IV.C), derived from the count of bits where one string
  can hold the share.  The mass energy that a measurement finds in cells adds over them, and the
  bit of each cell holds the same, so a set of cells holds the number of its cells times what
  one cell's bit holds (`Law.mass_empty`, `Law.mass_counts_bits`).  Where all the bits
  of a string together hold the matter `u`, a set of `m` of its `n` cells holds `(m/n)u`
  (`Law.mass_of_cells`).
  A share `E ≤ u` fills whole bits: a set of cells whose bits hold at most the share and, with
  one bit more, more than the share (`Law.fills_exists`).  Each cell's bit is one possible
  outcome among the ring's, so the probability `p` of those bits is a whole number of bits over
  `n` with `E/u − 1/n < p ≤ E/u`, and `p = E/u` where some set of cells holds the share exactly
  (`Law.filled_bits`, `Law.bits_of_share`).  The amplitude of the share is the square root of
  that probability, and for a share larger than `u` it is `√(E/u)`, the paper's definition of
  `h` on the same scale, taken as a condition (`Law.share_amplitude`).  The paper's `h = √(E/u)`
  is the leading order in `1/n`:
  the exact amplitude falls short of it by at most `1/√n`, and by at most `1/(n√(E/u))` where
  the share is at least one bit; where the share is below one bit the exact amplitude is zero
  (`Law.share_leading_order`).  `Law.share_bits_model` shows that the hypotheses can hold at
  once, for every share.
* The rule by which a string carries the body's information (Sec. IV.C), derived, for every turn
  of the string's phase per tick.  Each tick adds to a string the amplitude `ε = h/L` of the
  body's share, and a free tick turns the global phase of a string of energy `E` by
  `Δ = Et_c/ℏ`.  `Law.keepsPhase Δ ε` names the condition that the string's phase holds against
  the share.  The condition is the same after a whole turn more (`Law.keepsPhase_add_turns`).
  For `0 < ε < 1` and every `Δ` it holds exactly when `cos Δ > 0` and `|sin Δ| ≤ ε`
  (`Law.steady_phase_all_turns`, with `Law.steady_phase_iff` for `|Δ| < π/2`), that is, when
  `Δ` lies within `arcsin ε` of a whole number of turns (`Law.steady_phase_iff_turns`).  So the
  strings whose phase holds are those of energy at most `E_thr = (ℏ/t_c) arcsin(h/L)`, the first
  range, and those of energy within `E_thr` of `2πkℏ/t_c` for a whole number `k ≥ 1`, the ranges
  about the whole turns (`Law.phase_ranges`, `Reg.phase_all_turns`).  The first range's
  threshold lies between `h k_BT_dS` and `h k_BT_dS/√(1 − (h/L)²)` (`Law.arcsin_bounds`,
  `Law.exponent_bounds`, `Reg.threshold_bounds`).  The rule takes the carriers' fraction `b` as
  the fraction that a distribution of the strings' energies gives to the strings whose phase
  holds, whatever distribution has the fractions of the spread above each energy.  A
  distribution with the Gibbs fractions exists (`Law.gibbs_measure_exists`), and every such
  distribution gives a range of energies the difference of the fractions above its two ends
  (`Law.measure_Icc_of_above`).  The ranges are separate, and their fractions add up
  (`Law.range_fractions`, `Law.whole_turns_sum`) to
  `b = (1 − e^{−L arcsin(h/L)})(1 + (e^{L arcsin(h/L)} + 1)/(e^{2πL} − 1))`
  (`Law.phase_fraction`, `Reg.fraction_above_turn`, `Reg.carriers_fraction`), so the rule holds
  exactly when `b` is that number (`Reg.carriers_rule_iff`).  The first range holds the fraction
  `1 − e^{−L arcsin(h/L)}`, between `1 − e^{−h}` and `1 − e^{−h/√(1 − (h/L)²)}`
  (`Law.first_range_bounds`), and the ranges about the whole turns hold a positive fraction
  below `e^{−3πL/2}` (`Law.whole_turns_bounds`).  So `b` exceeds `1 − e^{−h}`, Eq. (b), its
  leading order in `1/L`, by at most the fraction `(h/L)² + 5e^{−3πL/2}` of it for `h ≤ L/2` and
  `L ≥ 1` (`Law.fraction_bounds`, `Law.fraction_leading_order`, with
  `Law.first_range_leading_order` and `Law.whole_turns_le`), and `Law.law_bounds` gives the
  bounds on `a = g_N/b`.  `Reg.carriers_model` shows that the hypotheses of the rule can hold at
  once.
* The law with the exact amplitude of whole bits (Sec. IV.C).  The carriers' exact fraction `b`
  increases with the amplitude `h` (`Law.carriers_fraction_mono`), and `1 − e^{−t}` is concave
  in `t` and vanishes at `t = 0` (`Law.one_sub_exp_concave`).  With the amplitude of whole bits
  on a string of `L` bits, `0 < h < L` and `f − 1/L < h² ≤ f`, the acceleration `a = g_N/b` is
  at least `1 − (√f/L)² − 5e^{−3πL/2}` times the value `g_N/(1 − e^{−√f})` of Eq. (law) where
  `√f ≤ L/2`, at most that value over `√(1 − 1/(L·f))` where `f > 1/L`, and at most
  `1 + 1/(L·f)` times it where `f ≥ 2/L` (`Law.law_whole_bits`, with
  `Law.inv_sqrt_one_sub_le`).
* The phase of a unit state under one tick (Sec. IV.C), at every phase `φ`.  A state of unit
  amplitude at the phase `φ` is turned by `Δ`, and the amplitude `ε` is added at the phase zero.
  The new state has the component `cos Δ + ε cos φ` along the old direction and
  `sin Δ − ε sin φ` across it (`Law.tick_components`, `Law.tick_turn`, `Law.tick_polar`).  The
  tick keeps the phase `φ` exactly when the component across vanishes and the component along
  is positive (`Law.keepsPhaseAt`, `Law.keepsPhaseAt_iff`, `Law.keepsPhase_iff_kept`).  Where
  `ε < |sin Δ|` the component across has the sign of `sin Δ` at every phase, so the phase moves
  in one sense at every tick (`Law.phase_slips`).  Where `|sin Δ| < ε` and `cos Δ > 0` the kept
  phases are `φ₀ = arcsin(sin Δ/ε)` and `π − φ₀` up to whole turns (`Law.kept_phases`), and from
  every other phase the phase moves toward `φ₀` and away from `π − φ₀` (`Law.phase_drawn`).  The
  phase after the tick, taken nearest to the phase before (`Law.tickPhase`), does not pass `φ₀`
  (`Law.tick_between`), the repeated tick converges to `φ₀` (`Law.tick_converges`), and a small
  gap shrinks per tick by the factor `cos Δ/(cos Δ + ε cos φ₀)` (`Law.tick_contracts`).
* `Reg.law`, Eq. (law), at leading order in `1/L`: with the threshold exponential with mean one in
  amplitude (`hME`: the string's slip per tick against the turn per tick `h/L`, the leading order
  of `arcsin(h/L)`, exponential with mean one by the Gibbs spread, `Law.gibbsAbove_eq` and
  `Reg.threshold_from_spread`), the fraction of carriers is `b = 1 − e^{−√f}`,
  and `a = g_N/(1 − e^{−√(g_N/a₀)})`.
* `Reg.law_scale_mean`: a threshold of mean `μ` would give the scale `μ²a₀`.
* `Reg.a0_depends_on_product` and `Reg.Lambda_from_a0`: only the product `Lℓ_c` enters `a₀`, and
  with `Λ = 3/R_Λ²` the scale gives `Λ = 12(ln 2)²a₀²/((1 − ln 2)²c⁴)` (Secs. IV.C and V).
* `Law.classical_limit`: a classical share, the probability `b = f` in place of the amplitude,
  would give `a = a₀` and rotation speeds rising as `√r`; flat rotation curves therefore support
  Postulate 1.
* `Reg.scale_over_time`: with Jacobson's `G`, `a₀` is a fixed fraction of the Planck acceleration
  `√(c⁷/ℏG)`; the same formula with another `G'` gives twice the scale only if `G' = G/4`.
* `Law.near_limit`, `Law.deep_limit` and `Law.tully_fisher`, Eqs. (deep) and (btfr): near the
  body `a = g_N(1 + e^{−h}) + g_N e^{−2h}/(1 − e^{−h})`, so Newton's law returns exponentially;
  far from it `a` lies within `a₀h³` of `√(a₀g_N) + g_N/2` for `h ≤ 1/2`; and on a circular orbit
  in the deep regime `v⁴ = a₀GM`.
* The frame of the law (Sec. IV.C): the sphere's temperature is the Unruh temperature of a proper
  acceleration, which a uniform external field does not change, so the law holds in the body's
  freely falling frame and a uniform external field adds nothing.  `Main.frame_of_law` states
  it: a field leaves the proper acceleration as it is exactly where it is a common acceleration
  of the body and of free fall at the observer's place, and under such a field the acceleration,
  the temperature of the sphere, the share and Eq. (law) stand as without it.  That the law is
  read for the proper acceleration, and that a uniform external field is such a common
  acceleration, are the paper's (the author's decision of 9 November 2026, after the quadrupole
  computation of `scripts/cassini.py`), and the two-body law is not derived.
* `Reg.radial_acceleration_relation`: the law chained from its inputs, each a named hypothesis,
  and `Reg.hypotheses_consistent`, which shows that the hypotheses can hold at once.

Up to v18-69 the files took the amplitude `h = √f` of the body's share, `h = √(E/u)`, as one
premise (`Sources.P1.share_amplitude`).  The exact amplitude is derived for `f ≤ 1`
(`Law.share_amplitude`, `Main.share_amplitude`): the count sets the matter `u`, the mean over
all strings, on all the bits of the one string on which the count is made, the bits of one whole qubit, so the
body's mean share fills whole bits of that string, and the amplitude of the share is the square
root of the probability of those bits.  The count is made for that mean; it does not say that
each string holds `u`, nor that a string that carries the body's information does.  For `f ≤ 1` that amplitude is `√f` to leading order in
`1/L`, in units of one whole qubit, a step (`Sources.Approx.share_amplitude`,
`Law.share_leading_order`, `Main.share_leading_order`), and `Law.law_whole_bits` and
`Main.law_whole_bits` bound what the step to `√f` changes in the law.  For `f > 1` the amplitude
`√f` is the paper's definition of `h` on the same scale, which the files take as a condition
(`Sources.Condition.same_scale`).  `Main.fill_fraction`, `Main.galactic_law`, `Main.law_bounds`
and `Main.scale_mean` take the step and the condition.  In
`Reg.law` the amplitude is the argument of the threshold's survival function (`hb`).  At leading
order in `1/L` the fraction `b` of carriers is the probability that a string's threshold lies
below `h`, and so the fraction of the sphere's strings that carry the body's information.
-/

open Real Finset

namespace Register

namespace Law

/-- **The share of a body's energy** (Sec. IV.C), in finite form.  The body is all the mass inside
the sphere, so a string's share is of that total, not of each star within it.  The body's energy
`E` is held by the strings `S` of the sphere (`hsum`; by Postulate 1 all the mass and light of the
universe consists of strings); where a string does not carry the body's information, its two
receiving cells, the cells where its ring crosses the sphere, keep the state they have without the
body, and the string holds none of the body's Landauer energies there (`hoff`).  The share `ε`
is the carriers' mean share: their shares add up to `|C| ε` (`hmean`), as equipartition gives it.
No carrier need hold the mean.  Then `E = |C| ε`: the energy is held by the carriers alone, and
it is the number of carriers times their mean share. -/
theorem share_of_equipartition {ι : Type*} (S C : Finset ι) (hCS : C ⊆ S) (e : ι → ℝ) (E ε : ℝ)
    (hsum : ∑ i ∈ S, e i = E) (hoff : ∀ i ∈ S, i ∉ C → e i = 0)
    (hmean : ∑ i ∈ C, e i = (C.card : ℝ) * ε) :
    E = (C.card : ℝ) * ε := by
  rw [← hsum, ← Finset.sum_subset hCS hoff, hmean]

/-- `e^{−h} < 1` for `h > 0`. -/
lemma exp_neg_lt_one {h : ℝ} (hh : 0 < h) : Real.exp (-h) < 1 := by
  have := Real.exp_lt_exp.2 (show -h < 0 by linarith)
  rwa [Real.exp_zero] at this

/-- Mathlib's Taylor bound for `exp`, with three terms: for `0 ≤ h ≤ 1`,
`e^{−h}` lies within `2h³/9` of `1 − h + h²/2`. -/
lemma exp_neg_taylor {h : ℝ} (hh : 0 ≤ h) (h1 : h ≤ 1) :
    1 - h + h ^ 2 / 2 - 2 / 9 * h ^ 3 ≤ Real.exp (-h) ∧
      Real.exp (-h) ≤ 1 - h + h ^ 2 / 2 + 2 / 9 * h ^ 3 := by
  have hx : |(-h)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hh]; exact h1
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, (-h) ^ m / (m.factorial : ℝ) = 1 - h + h ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one,
      Nat.cast_ofNat, pow_zero, pow_one, div_one]
    ring
  have hc : |(-h)| ^ 3 * ((Nat.succ 3 : ℕ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) : ℝ)
      = 2 / 9 * h ^ 3 := by
    rw [abs_neg, abs_of_nonneg hh, show Nat.succ 3 = 4 from rfl, show Nat.factorial 3 = 6 from rfl]
    push_cast
    ring
  rw [hs, hc] at hb
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  constructor <;> linarith

/-! ### The amplitude of a body's share, from the count of bits (Sec. IV.C) -/

/-- **The empty set of cells holds no mass energy** (Sec. IV.C).  `held S` is the mass energy
that a measurement on the manifold finds in the cells of `S`, and it adds over sets of cells
with no cell in common (`hadd`, `Sources.P1.mass_in_bits`).  The empty set has no cell in common
with itself, so it holds twice what it holds, which is nothing.  Sec. IV.C: "The measurement finds the bits in those cells and nothing else (Postulate 1), so mass energy is
counted in bits: cells without such bits show no mass." -/
theorem mass_empty {Cell : Type*} [DecidableEq Cell] (held : Finset Cell → ℝ)
    (hadd : ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T) :
    held ∅ = 0 := by
  have h := hadd ∅ ∅ disjoint_bot_left
  rw [Finset.union_self] at h
  linarith

/-- **Mass energy counts the bits** (Sec. IV.C).  The mass energy that a measurement finds in
cells adds over them (`hadd`, `Sources.P1.mass_in_bits`), and the bit of each cell holds the
same (`hcell`, `Sources.P2.cells_hold_alike`).  So a set `S` of cells holds the number of its
cells times what the bit of one cell `x` holds, whichever cell `x` is.  The proof adds the cells
of `S` one after another.  Sec. IV.C: "No cell differs from another (Postulate 2), so every bit counts the same." -/
theorem mass_counts_bits {Cell : Type*} [DecidableEq Cell] (held : Finset Cell → ℝ)
    (hadd : ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T)
    (hcell : ∀ x y : Cell, held {x} = held {y}) (S : Finset Cell) (x : Cell) :
    held S = S.card * held {x} := by
  induction S using Finset.induction_on with
  | empty => rw [mass_empty held hadd, Finset.card_empty, Nat.cast_zero, zero_mul]
  | insert a s ha ih =>
    rw [Finset.insert_eq, hadd _ _ (Finset.disjoint_singleton_left.2 ha), ih, hcell a x,
      ← Finset.insert_eq, Finset.card_insert_of_notMem ha]
    push_cast
    ring

/-- **What a set of a string's cells holds** (Sec. IV.C).  With the count of `mass_counts_bits`,
and with all the string's cells together holding the matter `u` (`hall`,
`Sources.P1.string_matter_in_bits`), for a ring that is not empty: the bit of each of its `n`
cells holds `u/n`, so a set of `m` cells holds `(m/n)u`, its share of the cells
times `u`.  Sec. IV.C: "The strings hold the matter `u` per string on average, on the `L` bits of one whole qubit, so for `f ≤ 1` the
mean share of the body, `E = fu`, fills the fraction `f` of a string's bits, to within one bit." -/
theorem mass_of_cells {Cell : Type*} [Fintype Cell] [DecidableEq Cell] [Nonempty Cell]
    (held : Finset Cell → ℝ)
    (hadd : ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T)
    (hcell : ∀ x y : Cell, held {x} = held {y}) (u : ℝ) (hall : held univ = u)
    (S : Finset Cell) :
    held S = (S.card / Fintype.card Cell) * u := by
  obtain ⟨x⟩ := ‹Nonempty Cell›
  have hL : (Fintype.card Cell : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 := mass_counts_bits held hadd hcell univ x
  rw [hall, Finset.card_univ] at h1
  rw [mass_counts_bits held hadd hcell S x, h1]
  field_simp

/-- **A set of cells that holds a share exactly: its fraction, its probability and its
amplitude** (Sec. IV.C).  A set `S` of the string's cells holds the share `E`, no more and no
less (`hS`), and all the string's cells together hold the matter `u ≠ 0` (`hall`).  The first part: by
`mass_of_cells` the set is the fraction `E/u` of the string's cells, so the share is that
fraction of the string's bits, and it is a whole number of bits, the number of the cells of
`S`.  The second part: each cell's bit is one possible outcome among the ring's (`halike`,
`Sources.P1.ring_bits_alike`), so the probability that the outcome is the bit of a cell of `S`
is the set's share of the cells (`Capacity.share_read`), which is `E/u`.  The third part: the
square root of that probability, the amplitude of those bits, is `√(E/u)`. -/
theorem bits_of_share {Cell : Type*} [Fintype Cell] [DecidableEq Cell] [Nonempty Cell]
    (held : Finset Cell → ℝ) (read : Cell → ℝ) (E u : ℝ) (hu : u ≠ 0)
    (hadd : ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T)
    (hcell : ∀ x y : Cell, held {x} = held {y}) (hall : held univ = u)
    (halike : ∀ x, read x = 1 / Fintype.card Cell) (S : Finset Cell) (hS : held S = E) :
    (S.card : ℝ) / Fintype.card Cell = E / u ∧ ∑ x ∈ S, read x = E / u ∧
      Real.sqrt (∑ x ∈ S, read x) = Real.sqrt (E / u) := by
  have hfrac : (S.card : ℝ) / Fintype.card Cell = E / u := by
    rw [← hS, mass_of_cells held hadd hcell u hall S, mul_div_assoc, div_self hu, mul_one]
  have hprob : ∑ x ∈ S, read x = E / u := by
    rw [Capacity.share_read read halike S, hfrac]
  exact ⟨hfrac, hprob, by rw [hprob]⟩

/-- **The bits that a share fills** (Sec. IV.C).  All the string's cells together hold the
matter `u > 0` (`hall`), and the share is one that the string can hold, `E ≤ u`.  The share fills a set `S`
of the string's cells and not one cell more: the bits of `S` hold at most the share (`hS`), and
with the bit of any further cell they would hold more than the share (`hnext`; the two are the
first part of `Sources.P1.share_bits`).  Each cell's bit is one possible outcome among the
ring's (`halike`, `Sources.P1.ring_bits_alike`).  The first part: the probability `p` that the
outcome is the bit of a cell of `S` is the set's share of the cells, a whole number of bits over
the number `n` of the ring's cells (`Capacity.share_read`).  The second and third parts: that
probability lies less than one bit below the fraction `E/u`, `E/u − 1/n < p ≤ E/u`
(`mass_of_cells`).  The fourth part: where some set of cells holds the share exactly, so that
the share is a whole number of bits, `p = E/u` (`bits_of_share`).  Sec. IV.C: "The strings hold the matter `u` per string on average, on the `L` bits of one whole qubit, so for `f ≤ 1` the
mean share of the body, `E = fu`, fills the fraction `f` of a string's bits, to within one bit." -/
theorem filled_bits {Cell : Type*} [Fintype Cell] [DecidableEq Cell] [Nonempty Cell]
    (held : Finset Cell → ℝ) (read : Cell → ℝ) (E u : ℝ) (hu : 0 < u) (hEu : E ≤ u)
    (hadd : ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T)
    (hcell : ∀ x y : Cell, held {x} = held {y}) (hall : held univ = u)
    (halike : ∀ x, read x = 1 / Fintype.card Cell) (S : Finset Cell)
    (hS : held S ≤ E) (hnext : ∀ x, x ∉ S → E < held (insert x S)) :
    ∑ x ∈ S, read x = S.card / Fintype.card Cell ∧
    E / u - 1 / Fintype.card Cell < ∑ x ∈ S, read x ∧ ∑ x ∈ S, read x ≤ E / u ∧
    ((∃ T : Finset Cell, held T = E) → ∑ x ∈ S, read x = E / u) := by
  have hn : (0 : ℝ) < Fintype.card Cell := by exact_mod_cast Fintype.card_pos
  have hp : ∑ x ∈ S, read x = S.card / Fintype.card Cell := Capacity.share_read read halike S
  have hheld := mass_of_cells held hadd hcell u hall
  -- the set holds at most the share
  have hle : (S.card : ℝ) / Fintype.card Cell ≤ E / u := by
    rw [le_div_iff₀ hu, ← hheld S]
    exact hS
  -- one bit more would hold more than the share
  have hlt : E / u - 1 / Fintype.card Cell < (S.card : ℝ) / Fintype.card Cell := by
    by_cases hall' : ∀ x, x ∈ S
    · have hSuniv : S = univ := Finset.eq_univ_iff_forall.2 hall'
      rw [hSuniv, Finset.card_univ, div_self hn.ne']
      have h1 : E / u ≤ 1 := (div_le_one hu).2 hEu
      have h2 : (0 : ℝ) < 1 / Fintype.card Cell := by positivity
      linarith
    · push Not at hall'
      obtain ⟨x, hx⟩ := hall'
      have h1 := hnext x hx
      rw [hheld (insert x S), Finset.card_insert_of_notMem hx] at h1
      have h2 : E / u < ((S.card + 1 : ℕ) : ℝ) / Fintype.card Cell := by
        rw [div_lt_iff₀ hu]
        exact h1
      push_cast at h2
      have h3 : ((S.card : ℝ) + 1) / Fintype.card Cell
          = (S.card : ℝ) / Fintype.card Cell + 1 / Fintype.card Cell := by ring
      linarith
  refine ⟨hp, by rw [hp]; exact hlt, by rw [hp]; exact hle, ?_⟩
  rintro ⟨T, hT⟩
  -- a set that holds the share exactly has as many cells
  have hfrac := (bits_of_share held read E u hu.ne' hadd hcell hall halike T hT).1
  rw [hp, ← hfrac]
  rw [← hfrac] at hle hlt
  have h1 : (S.card : ℝ) ≤ T.card := by
    have := (div_le_div_iff_of_pos_right hn).1 hle
    exact this
  have h2 : (T.card : ℝ) - 1 < S.card := by
    have h3 : ((T.card : ℝ) - 1) / Fintype.card Cell < (S.card : ℝ) / Fintype.card Cell := by
      rw [sub_div]; exact hlt
    exact (div_lt_div_iff_of_pos_right hn).1 h3
  have h4 : S.card ≤ T.card := by exact_mod_cast h1
  have h5 : T.card < S.card + 1 := by
    have : (T.card : ℝ) < (S.card : ℝ) + 1 := by linarith
    exact_mod_cast this
  have h6 : S.card = T.card := by omega
  rw [h6]

/-- **Every share that one string can hold fills a set of cells and not one more**
(Sec. IV.C).  With mass energy counted in bits (`hadd`, `hcell`) and all the string's cells together
holding the matter `u > 0` (`hall`), for every share `0 ≤ E ≤ u` there is a set of cells whose
bits hold at most the share and, with the bit of any further cell, more than the share: a set
of `⌊nE/u⌋` of the ring's `n` cells, the whole bits that the share fills.  So the first part of
`Sources.P1.share_bits` can be met for every such share.  Sec. IV.C: "The strings hold the matter `u` per string on average, on the `L` bits of one whole qubit, so for `f ≤ 1` the
mean share of the body, `E = fu`, fills the fraction `f` of a string's bits, to within one bit." -/
theorem fills_exists {Cell : Type*} [Fintype Cell] [DecidableEq Cell] [Nonempty Cell]
    (held : Finset Cell → ℝ) (E u : ℝ) (hu : 0 < u) (hE : 0 ≤ E) (hEu : E ≤ u)
    (hadd : ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T)
    (hcell : ∀ x y : Cell, held {x} = held {y}) (hall : held univ = u) :
    ∃ S : Finset Cell, held S ≤ E ∧ ∀ x, x ∉ S → E < held (insert x S) := by
  have hn : (0 : ℝ) < Fintype.card Cell := by exact_mod_cast Fintype.card_pos
  have hheld := mass_of_cells held hadd hcell u hall
  have hf0 : 0 ≤ (Fintype.card Cell : ℝ) * (E / u) := by positivity
  have hf1 : (Fintype.card Cell : ℝ) * (E / u) ≤ Fintype.card Cell := by
    have : E / u ≤ 1 := (div_le_one hu).2 hEu
    nlinarith
  -- the whole bits that the share fills
  have hm : ⌊(Fintype.card Cell : ℝ) * (E / u)⌋₊ ≤ (univ : Finset Cell).card := by
    rw [Finset.card_univ]
    exact Nat.floor_le_of_le hf1
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq hm
  refine ⟨S, ?_, fun x hx => ?_⟩
  · rw [hheld S, hS]
    have h1 := Nat.floor_le hf0
    have h2 : (⌊(Fintype.card Cell : ℝ) * (E / u)⌋₊ : ℝ) / Fintype.card Cell ≤ E / u := by
      rw [div_le_iff₀ hn]; linarith
    rw [le_div_iff₀ hu] at h2
    exact h2
  · rw [hheld (insert x S), Finset.card_insert_of_notMem hx, hS]
    have h1 := Nat.lt_floor_add_one ((Fintype.card Cell : ℝ) * (E / u))
    have h2 : E / u < ((⌊(Fintype.card Cell : ℝ) * (E / u)⌋₊ + 1 : ℕ) : ℝ) / Fintype.card Cell := by
      rw [lt_div_iff₀ hn]; push_cast; linarith
    rw [div_lt_iff₀ hu] at h2
    exact h2

/-- **The exact amplitude of a body's share** (Sec. IV.C), in the form in which
`Main.share_amplitude` states it from the sources.  The first part, for a share that one string
can hold, `0 ≤ E ≤ u`: the share fills a set of the string's cells and not one more, and `h` is
the amplitude of their bits (`hbits`, `Sources.P1.share_bits`).  So `h` is not negative, `h²` is
a whole number of bits over the number `n` of the ring's cells, and `E/u − 1/n < h² ≤ E/u`
(`filled_bits`).  The second part, for a larger share, `E > u`: `h = √(E/u)`, the paper's
definition of `h` on the same scale, a condition (`hscale`, `Sources.Condition.same_scale`), and
no count of bits.
`share_leading_order` bounds the step from this amplitude to `√(E/u)`.  Up to v18-69 the files
took `h = √(E/u)` as one premise, `Sources.P1.share_amplitude`. -/
theorem share_amplitude {Cell : Type*} [Fintype Cell] [DecidableEq Cell] [Nonempty Cell]
    (held : Finset Cell → ℝ) (read : Cell → ℝ) (E u h : ℝ) (hu : 0 < u) (hE : 0 ≤ E)
    (hadd : ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T)
    (hcell : ∀ x y : Cell, held {x} = held {y}) (hall : held univ = u)
    (halike : ∀ x, read x = 1 / Fintype.card Cell)
    (hbits : 0 ≤ E → E ≤ u → ∃ S : Finset Cell, held S ≤ E ∧
      (∀ x, x ∉ S → E < held (insert x S)) ∧ h = Real.sqrt (∑ x ∈ S, read x))
    (hscale : u < E → h = Real.sqrt (E / u)) :
    (E ≤ u → 0 ≤ h ∧ (∃ m : ℕ, h ^ 2 = m / Fintype.card Cell) ∧
      E / u - 1 / Fintype.card Cell < h ^ 2 ∧ h ^ 2 ≤ E / u) ∧
    (u < E → h = Real.sqrt (E / u)) := by
  refine ⟨fun hEu => ?_, hscale⟩
  obtain ⟨S, hS, hnext, hh⟩ := hbits hE hEu
  obtain ⟨hp, hlo, hhi, -⟩ :=
    filled_bits held read E u hu hEu hadd hcell hall halike S hS hnext
  have hp0 : 0 ≤ ∑ x ∈ S, read x := by rw [hp]; positivity
  have hsq : h ^ 2 = ∑ x ∈ S, read x := by rw [hh, Real.sq_sqrt hp0]
  exact ⟨by rw [hh]; exact Real.sqrt_nonneg _, ⟨S.card, by rw [hsq, hp]⟩, by rw [hsq]; exact hlo,
    by rw [hsq]; exact hhi⟩

/-- **The amplitude of a share at leading order** (Sec. IV.C): what the step from the exact
amplitude to `√f` changes, with `f = E/u`.  Let `h` be the amplitude of whole bits on a string of
`n` bits: `h ≥ 0`, `h²` a whole number of bits over `n`, and `f − 1/n < h² ≤ f` (`hexact`, the
first part of `share_amplitude`).  The first and second parts: `√f` is at least `h` and exceeds
it by at most `1/√n`, since `(√f − h)² ≤ f − h² < 1/n`.  The third part: where the share is at
least one bit, `f ≥ 1/n`, `√f` exceeds `h` by at most `1/(n√f)`, since
`√f − h = (f − h²)/(√f + h)`.  The fourth part: where the share is a whole number of bits,
`f = k/n`, the two are equal.  The fifth part: where the share is below one bit, `f < 1/n`, it
fills no bit and `h = 0`, so there the step puts `√f` for the amplitude zero.  The hypothesis
has `n ≥ 1`: for `n = 0` it would read `f < h² ≤ f`.  Sec. IV.C: the mean share of the body fills the fraction `f` of a string's bits "to within one
bit".  Data availability: "The three steps at leading order, the count's density, the share's amplitude,
and the carriers' fraction, are named as such, with their errors bounded in the files." -/
theorem share_leading_order (n : ℕ) (f h : ℝ)
    (hexact : 0 ≤ h ∧ (∃ m : ℕ, h ^ 2 = m / n) ∧ f - 1 / n < h ^ 2 ∧ h ^ 2 ≤ f) :
    0 ≤ Real.sqrt f - h ∧ Real.sqrt f - h ≤ 1 / Real.sqrt n ∧
    (1 / n ≤ f → Real.sqrt f - h ≤ 1 / (n * Real.sqrt f)) ∧
    ((∃ k : ℕ, f = k / n) → h = Real.sqrt f) ∧ (f < 1 / n → h = 0) := by
  obtain ⟨hh0, ⟨m, hm⟩, hlo, hhi⟩ := hexact
  have hf0 : 0 ≤ f := le_trans (sq_nonneg h) hhi
  have ha0 : 0 ≤ Real.sqrt f := Real.sqrt_nonneg f
  have ha2 : Real.sqrt f ^ 2 = f := Real.sq_sqrt hf0
  -- `h ≤ √f`
  have hle : h ≤ Real.sqrt f := Real.le_sqrt_of_sq_le hhi
  -- the number of the cells is not zero: else `f < h² ≤ f`
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero, div_zero, sub_zero] at hlo
      linarith
    · exact h0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  -- `(√f − h)² ≤ (√f − h)(√f + h) = f − h² < 1/n`
  have hgap : Real.sqrt f ^ 2 - h ^ 2 < 1 / n := by rw [ha2]; linarith
  refine ⟨by linarith, ?_, fun h1 => ?_, ?_, fun hlt => ?_⟩
  · have h2 : (Real.sqrt f - h) ^ 2 ≤ 1 / n := by nlinarith
    have h3 : Real.sqrt f - h ≤ Real.sqrt (1 / n) := Real.le_sqrt_of_sq_le h2
    rwa [Real.sqrt_div' 1 hn'.le, Real.sqrt_one] at h3
  · -- `√f − h = (f − h²)/(√f + h) ≤ (1/n)/√f`
    have hf : 0 < f := lt_of_lt_of_le (by positivity) h1
    have ha : 0 < Real.sqrt f := Real.sqrt_pos.2 hf
    rw [le_div_iff₀ (by positivity)]
    have h2 : (Real.sqrt f - h) * Real.sqrt f ≤ Real.sqrt f ^ 2 - h ^ 2 := by nlinarith
    have h3 : (Real.sqrt f - h) * (n * Real.sqrt f) = n * ((Real.sqrt f - h) * Real.sqrt f) := by
      ring
    rw [h3]
    have h4 : (n : ℝ) * (Real.sqrt f ^ 2 - h ^ 2) < 1 := by
      have := mul_lt_mul_of_pos_left hgap hn'
      rwa [mul_one_div_cancel hn'.ne'] at this
    nlinarith
  · rintro ⟨k, hk⟩
    -- `k − 1 < m ≤ k`, so `m = k`
    rw [hm, hk] at hhi
    rw [hm, hk] at hlo
    have h1 : (m : ℝ) ≤ k := (div_le_div_iff_of_pos_right hn').1 hhi
    have h2 : (k : ℝ) - 1 < m := by
      have h3 : ((k : ℝ) - 1) / n < (m : ℝ) / n := by rw [sub_div]; exact hlo
      exact (div_lt_div_iff_of_pos_right hn').1 h3
    have h4 : m ≤ k := by exact_mod_cast h1
    have h5 : k < m + 1 := by
      have : (k : ℝ) < (m : ℝ) + 1 := by linarith
      exact_mod_cast this
    have h6 : m = k := by omega
    have h7 : h ^ 2 = f := by rw [hm, hk, h6]
    rw [← h7, Real.sqrt_sq hh0]
  · -- `m/n = h² ≤ f < 1/n`, so `m = 0`
    have h1 : (m : ℝ) / n < 1 / n := by rw [← hm]; linarith
    have h2 : (m : ℝ) < 1 := (div_lt_div_iff_of_pos_right hn').1 h1
    have h3 : m = 0 := by
      have : m < 1 := by exact_mod_cast h2
      omega
    rw [h3, Nat.cast_zero, zero_div] at hm
    exact (pow_eq_zero_iff two_ne_zero).1 hm

/-- **The hypotheses of the share's amplitude can hold at once** (Sec. IV.C), on a ring of
`n ≥ 1` cells, for every matter `u > 0` and every share `E`.  There are a count `held` of the
mass energy in cells that adds over them, with the bit of each cell holding the same and all the
cells holding `u`; probabilities `read` of the bits, alike; and an amplitude `h`, such that for
`0 ≤ E ≤ u` the share fills a set of cells and not one more, with `h` the amplitude of its bits
(`fills_exists`), and for `E > u` the amplitude is `√(E/u)`.  So `Main.share_amplitude` does not
hold vacuously, at any share. -/
theorem share_bits_model (n : ℕ) (hn : 0 < n) (E u : ℝ) (hu : 0 < u) :
    ∃ (held : Finset (Fin n) → ℝ) (read : Fin n → ℝ) (h : ℝ),
      (∀ S T : Finset (Fin n), Disjoint S T → held (S ∪ T) = held S + held T) ∧
      (∀ x y : Fin n, held {x} = held {y}) ∧ held univ = u ∧
      (∀ x, read x = 1 / Fintype.card (Fin n)) ∧
      (0 ≤ E → E ≤ u → ∃ S : Finset (Fin n), held S ≤ E ∧
        (∀ x, x ∉ S → E < held (insert x S)) ∧ h = Real.sqrt (∑ x ∈ S, read x)) ∧
      (u < E → h = Real.sqrt (E / u)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- the count: each of the `n` cells holds `u/n`
  have hadd : ∀ S T : Finset (Fin n), Disjoint S T →
      ((S ∪ T).card : ℝ) / n * u = (S.card : ℝ) / n * u + (T.card : ℝ) / n * u := by
    intro A B hAB
    rw [Finset.card_union_of_disjoint hAB]
    push_cast
    ring
  have hcell : ∀ x y : Fin n,
      (({x} : Finset (Fin n)).card : ℝ) / n * u = (({y} : Finset (Fin n)).card : ℝ) / n * u := by
    intro x y
    rw [Finset.card_singleton, Finset.card_singleton]
  have hall : ((univ : Finset (Fin n)).card : ℝ) / n * u = u := by
    rw [Finset.card_univ, Fintype.card_fin, div_self hn', one_mul]
  by_cases hcase : 0 ≤ E ∧ E ≤ u
  · -- a share that the string can hold: the amplitude of the bits that it fills
    obtain ⟨S, hS, hnext⟩ :=
      fills_exists (fun T : Finset (Fin n) => (T.card : ℝ) / n * u) E u hu hcase.1 hcase.2
        hadd hcell hall
    exact ⟨fun T => (T.card : ℝ) / n * u, fun _ => 1 / Fintype.card (Fin n),
      Real.sqrt (∑ x ∈ S, (fun _ : Fin n => (1 : ℝ) / Fintype.card (Fin n)) x), hadd, hcell, hall,
      fun _ => rfl, fun _ _ => ⟨S, hS, hnext, rfl⟩, fun hlt => absurd hcase.2 (not_le.2 hlt)⟩
  · -- a larger share, or none: the scale
    exact ⟨fun T => (T.card : ℝ) / n * u, fun _ => 1 / Fintype.card (Fin n), Real.sqrt (E / u),
      hadd, hcell, hall, fun _ => rfl, fun h0 h1 => absurd ⟨h0, h1⟩ hcase, fun _ => rfl⟩

/-! ### The Gibbs mean of the strings' energies (Sec. IV.E) -/

/-- **The Gibbs mean of an energy that runs from zero up** (Sec. IV.E, Eq. (mean)): with the
weight `e^{−E/θ}` on the energy `E ≥ 0`, `θ = k_BT` the thermal energy, the mean energy is
`∫₀^∞ E e^{−E/θ} dE / ∫₀^∞ e^{−E/θ} dE`. -/
noncomputable def gibbsMean (θ : ℝ) : ℝ :=
  (∫ E in Set.Ioi (0 : ℝ), E * Real.exp (-E / θ)) /
    (∫ E in Set.Ioi (0 : ℝ), Real.exp (-E / θ))

/-- **The Gibbs mean is the thermal energy** (Sec. IV.E, Eq. (mean)): the two integrals are `θ²`
and `θ`, so `⟨E⟩ = θ = k_BT`. -/
theorem gibbsMean_eq (θ : ℝ) (hθ : 0 < θ) : gibbsMean θ = θ := by
  have hr : (0 : ℝ) < 1 / θ := by positivity
  have hG2 : Real.Gamma 2 = 1 := by
    have h := Real.Gamma_add_one (s := 1) one_ne_zero
    rw [Real.Gamma_one, mul_one] at h
    have h2 : (1 : ℝ) + 1 = 2 := by norm_num
    rwa [h2] at h
  -- the weights' sum: `∫₀^∞ e^{−E/θ} dE = θ`
  have h0 : ∫ E in Set.Ioi (0 : ℝ), Real.exp (-E / θ) = θ := by
    have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1 / θ) one_pos hr
    rw [Real.Gamma_one, mul_one, Real.rpow_one, one_div_one_div] at key
    have hcongr : ∫ E in Set.Ioi (0 : ℝ), Real.exp (-E / θ)
        = ∫ t in Set.Ioi (0 : ℝ), t ^ ((1 : ℝ) - 1) * Real.exp (-(1 / θ * t)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun E _ => ?_)
      show Real.exp (-E / θ) = E ^ ((1 : ℝ) - 1) * Real.exp (-(1 / θ * E))
      rw [sub_self, Real.rpow_zero, one_mul]
      congr 1
      ring
    rw [hcongr]
    exact key
  -- the weighted energies' sum: `∫₀^∞ E e^{−E/θ} dE = θ²`
  have h1 : ∫ E in Set.Ioi (0 : ℝ), E * Real.exp (-E / θ) = θ ^ 2 := by
    have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 / θ) two_pos hr
    rw [hG2, mul_one, one_div_one_div, Real.rpow_two] at key
    have hcongr : ∫ E in Set.Ioi (0 : ℝ), E * Real.exp (-E / θ)
        = ∫ t in Set.Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(1 / θ * t)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun E _ => ?_)
      show E * Real.exp (-E / θ) = E ^ ((2 : ℝ) - 1) * Real.exp (-(1 / θ * E))
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      congr 2
      ring
    rw [hcongr]
    exact key
  unfold gibbsMean
  rw [h0, h1]
  field_simp

/-- **The Gibbs fraction above an energy** (Secs. IV.C and IV.E): with the weight `e^{−E/θ}` on the
energy `E ≥ 0`, `θ = k_BT` the thermal energy, the fraction of the weight on the energies above
`x` is `∫ₓ^∞ e^{−E/θ} dE / ∫₀^∞ e^{−E/θ} dE`. -/
noncomputable def gibbsAbove (θ x : ℝ) : ℝ :=
  (∫ E in Set.Ioi x, Real.exp (-E / θ)) / (∫ E in Set.Ioi (0 : ℝ), Real.exp (-E / θ))

/-- **The Gibbs fraction above `x` is `e^{−x/θ}`** (Sec. IV.C): the two integrals are `θe^{−x/θ}`
and `θ`.  For the energies that enter the rule of Sec. IV.C, the energies `E_s`, at
`θ = k_BT_dS`, this is the fraction `e^{−x}` above `x k_BT_dS` (`Reg.threshold_from_spread`).
Sec. IV.C: "Apart from the body's energy, the strings of the sphere are like all other strings, so the energies `E_s` are spread over them at the horizon's temperature
(Sec. IV.E), by the principle of maximum entropy, the fraction `e^{−x}` of them above
`x k_BT_dS`."  "So the fraction `e^{−h}` of the strings have `E_s > h k_BT_dS`, and those
strings miss the body." -/
theorem gibbsAbove_eq (θ x : ℝ) (hθ : 0 < θ) : gibbsAbove θ x = Real.exp (-x / θ) := by
  have hθ' := hθ.ne'
  have ha : -1 / θ < 0 := by rw [neg_div]; exact neg_neg_of_pos (by positivity)
  -- the weight above `y`: `∫_y^∞ e^{−E/θ} dE = θe^{−y/θ}`
  have hI : ∀ y : ℝ, ∫ E in Set.Ioi y, Real.exp (-E / θ) = θ * Real.exp (-y / θ) := by
    intro y
    have key := integral_exp_mul_Ioi ha y
    have hcongr : (fun E : ℝ => Real.exp (-E / θ)) = fun E => Real.exp (-1 / θ * E) := by
      funext E
      congr 1
      ring
    rw [hcongr, key]
    field_simp
  unfold gibbsAbove
  rw [hI x, hI 0, neg_zero, zero_div, Real.exp_zero, mul_one]
  field_simp

/-- **The phase holds under one tick** (Sec. IV.C): the condition of `steady_phase_all_turns`,
named.  A state of one qubit has unit amplitude and the phase `φ`, counted from the phase of a
second state.  A tick turns it by `Δ` and adds to it the amplitude `ε` of the second state, at
that fixed phase.  The condition is that for some `φ` the sum has the phase `φ` again, with some
positive amplitude `r`: the tick leaves that phase unchanged.  For a string, `Δ = Et_c/ℏ` is the
turn of a free tick at the string's energy `E`, and `ε = h/L` is the amplitude that a tick adds
of a body's share (`Sources.P1.carriers_hold_phase`, `Sources.P1.share_in_parts`).  The
condition is the same at `Δ` and at `Δ + 2π`, a whole turn being no turn
(`keepsPhase_add_turns`).  For `0 < ε < 1` it holds exactly when `Δ` lies within `arcsin ε` of a
whole number of turns (`steady_phase_all_turns`, `steady_phase_iff_turns`).  The condition is the
same at `Δ` and at `−Δ` (`keepsPhase_neg`), so it does not depend on the sense of the turn. -/
def keepsPhase (Δ ε : ℝ) : Prop :=
  ∃ φ r : ℝ, 0 < r ∧ Real.cos (φ + Δ) + ε = r * Real.cos φ ∧ Real.sin (φ + Δ) = r * Real.sin φ

/-- **A steady phase under one tick, for `|Δ| < π/2`** (Sec. IV.C).  A state of one qubit with
unit amplitude and the phase `φ`, counted from the phase of a second state, is turned by `Δ` in a
tick, with `|Δ| < π/2`, and the amplitude `ε > 0` of the second state is added to it at that
fixed phase.  The sum has the phase `φ` again, with some positive amplitude `r`, for some `φ`
(`keepsPhase`) exactly when `|sin Δ| ≤ ε`: the added amplitude can undo the turn of one tick when
the turn is small enough, and not otherwise.  `steady_phase_all_turns` gives the condition for
every `Δ`, where `ε < 1`. -/
theorem steady_phase_iff (Δ ε : ℝ) (hε : 0 < ε) (hΔ : |Δ| < Real.pi / 2) :
    keepsPhase Δ ε ↔ |Real.sin Δ| ≤ ε := by
  unfold keepsPhase
  constructor
  · rintro ⟨φ, r, _, hc, hs⟩
    -- `sin(φ + Δ)cos φ − (cos(φ + Δ) + ε)sin φ = r sin φ cos φ − r cos φ sin φ = 0`
    have h0 : Real.sin (φ + Δ) * Real.cos φ - (Real.cos (φ + Δ) + ε) * Real.sin φ = 0 := by
      rw [hs, hc]; ring
    -- and by the addition formulas it is `sin Δ − ε sin φ`
    have hΔs : Real.sin Δ = ε * Real.sin φ := by
      rw [Real.sin_add, Real.cos_add] at h0
      have hp := Real.sin_sq_add_cos_sq φ
      linear_combination h0 - Real.sin Δ * hp
    rw [hΔs, abs_mul, abs_of_pos hε]
    calc ε * |Real.sin φ| ≤ ε * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one φ) hε.le
      _ = ε := mul_one ε
  · intro h
    have hq : |Real.sin Δ / ε| ≤ 1 := by
      rw [abs_div, abs_of_pos hε, div_le_one hε]; exact h
    obtain ⟨hq1, hq2⟩ := abs_le.mp hq
    -- the phase `φ = arcsin(sin Δ/ε)`, with `cos φ ≥ 0`
    set φ := Real.arcsin (Real.sin Δ / ε)
    have hsφ : Real.sin φ = Real.sin Δ / ε := Real.sin_arcsin hq1 hq2
    have hcφ : 0 ≤ Real.cos φ := Real.cos_arcsin_nonneg _
    have hΔ' := abs_lt.mp hΔ
    have hcΔ : 0 < Real.cos Δ := Real.cos_pos_of_mem_Ioo ⟨hΔ'.1, hΔ'.2⟩
    have hsΔ : Real.sin Δ = ε * Real.sin φ := by rw [hsφ]; field_simp
    have hp := Real.sin_sq_add_cos_sq φ
    -- the amplitude `r = cos Δ + ε cos φ > 0`
    refine ⟨φ, Real.cos Δ + ε * Real.cos φ, by positivity, ?_, ?_⟩
    · rw [Real.cos_add]
      linear_combination (-(Real.sin φ)) * hsΔ - ε * hp
    · rw [Real.sin_add]
      linear_combination Real.cos φ * hsΔ

/-- **A whole turn more leaves the condition as it is** (Sec. IV.C).  For every integer `k`, the
tick that turns the phase by `Δ + 2πk` leaves a phase unchanged (`keepsPhase`) exactly when
the tick that turns it by `Δ` does: the condition takes `Δ` through `cos(φ + Δ)` and
`sin(φ + Δ)` alone, which have the period `2π`.  So a string whose free tick turns its phase by
`Δ` and some whole turns holds its phase against a share exactly when a string of the turn `Δ`
does. -/
theorem keepsPhase_add_turns (Δ ε : ℝ) (k : ℤ) :
    keepsPhase (Δ + 2 * Real.pi * k) ε ↔ keepsPhase Δ ε := by
  have hc : ∀ φ : ℝ, Real.cos (φ + (Δ + 2 * Real.pi * k)) = Real.cos (φ + Δ) := by
    intro φ
    rw [← add_assoc, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_int_mul_two_pi _ k
  have hs : ∀ φ : ℝ, Real.sin (φ + (Δ + 2 * Real.pi * k)) = Real.sin (φ + Δ) := by
    intro φ
    rw [← add_assoc, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    exact Real.sin_add_int_mul_two_pi _ k
  unfold keepsPhase
  simp only [hc, hs]

/-- **What a steady phase requires, at every turn** (Sec. IV.C).  For an added amplitude
`0 < ε ≤ 1` and every turn `Δ`, a tick that leaves a phase unchanged (`keepsPhase`) has
`cos Δ > 0` and `|sin Δ| ≤ ε`.  With the phase `φ` and the amplitude `r > 0` of the condition,
its two equations give `sin Δ = ε sin φ`, which bounds the sine, and `cos Δ + ε cos φ = r`.  If
`cos Δ ≤ 0`, the second gives `ε cos φ > −cos Δ ≥ 0`, so `ε² cos² φ > cos² Δ`, and with the
first `ε² > cos² Δ + sin² Δ = 1`, which `ε ≤ 1` excludes. -/
theorem steady_phase_requires (Δ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (h : keepsPhase Δ ε) :
    0 < Real.cos Δ ∧ |Real.sin Δ| ≤ ε := by
  obtain ⟨φ, r, hr, hc, hs⟩ := h
  rw [Real.cos_add] at hc
  rw [Real.sin_add] at hs
  have hp := Real.sin_sq_add_cos_sq φ
  have hq := Real.sin_sq_add_cos_sq Δ
  -- `sin Δ = ε sin φ` and `cos Δ + ε cos φ = r`
  have hΔs : Real.sin Δ = ε * Real.sin φ := by
    linear_combination Real.cos φ * hs - Real.sin φ * hc - Real.sin Δ * hp
  have hΔc : Real.cos Δ + ε * Real.cos φ = r := by
    linear_combination Real.cos φ * hc + Real.sin φ * hs - (Real.cos Δ - r) * hp
  constructor
  · by_contra hneg
    push Not at hneg
    -- `ε cos φ > −cos Δ ≥ 0`, so `ε² cos² φ > cos² Δ`, and `ε² > cos² Δ + sin² Δ = 1`
    have h1 : -Real.cos Δ < ε * Real.cos φ := by linarith
    have h2 : Real.cos Δ ^ 2 < (ε * Real.cos φ) ^ 2 := by nlinarith
    have h3 : (ε * Real.cos φ) ^ 2 + (ε * Real.sin φ) ^ 2 = ε ^ 2 := by
      linear_combination ε ^ 2 * hp
    have h4 : ε ^ 2 ≤ 1 := by nlinarith
    rw [hΔs] at hq
    linarith
  · rw [hΔs, abs_mul, abs_of_pos hε]
    calc ε * |Real.sin φ| ≤ ε * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one φ) hε.le
      _ = ε := mul_one ε

/-- **Within `arcsin ε` of a whole number of turns** (Sec. IV.C), trigonometry.  For `ε < 1` and
every `Δ`, `cos Δ > 0` and `|sin Δ| ≤ ε` hold exactly when `|Δ − 2πk| ≤ arcsin ε` for some
integer `k`.  From the left, the angle `β = arcsin(sin Δ)` has the sine and the cosine of `Δ`, so
`Δ = β + 2πk` for an integer `k`, and `|β| ≤ arcsin ε`, since the arcsine is monotone and
odd.  From the right, `Δ − 2πk` has the sine and the cosine of `Δ` and lies within
`arcsin ε < π/2` of zero, where the cosine is positive and the sine is monotone. -/
theorem near_whole_turn_iff (Δ ε : ℝ) (hε1 : ε < 1) :
    (0 < Real.cos Δ ∧ |Real.sin Δ| ≤ ε) ↔ ∃ k : ℤ, |Δ - 2 * Real.pi * k| ≤ Real.arcsin ε := by
  have ha1 : Real.arcsin ε < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hε1
  constructor
  · rintro ⟨hcos, hsin⟩
    obtain ⟨hs1, hs2⟩ := abs_le.mp hsin
    -- the angle `β = arcsin(sin Δ)` has the cosine and the sine of `Δ`
    have hsβ : Real.sin (Real.arcsin (Real.sin Δ)) = Real.sin Δ :=
      Real.sin_arcsin (Real.neg_one_le_sin Δ) (Real.sin_le_one Δ)
    have hcβ : Real.cos (Real.arcsin (Real.sin Δ)) = Real.cos Δ := by
      rw [Real.cos_arcsin, ← Real.abs_cos_eq_sqrt_one_sub_sin_sq, abs_of_pos hcos]
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1
      (Real.Angle.cos_sin_inj hcβ.symm hsβ.symm)
    refine ⟨k, ?_⟩
    rw [← hk, sub_sub_cancel, abs_le]
    constructor
    · rw [← Real.arcsin_neg]
      exact Real.arcsin_le_arcsin hs1
    · exact Real.arcsin_le_arcsin hs2
  · rintro ⟨k, hk⟩
    obtain ⟨h1, h2⟩ := abs_le.mp hk
    have hcos : Real.cos Δ = Real.cos (Δ - 2 * Real.pi * k) := by
      rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
      exact (Real.cos_sub_int_mul_two_pi _ k).symm
    have hsin : Real.sin Δ = Real.sin (Δ - 2 * Real.pi * k) := by
      rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
      exact (Real.sin_sub_int_mul_two_pi _ k).symm
    rw [hcos, hsin]
    refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩, abs_le.mpr ⟨?_, ?_⟩⟩
    · have h3 : Real.arcsin (-ε) ≤ Δ - 2 * Real.pi * k := by rw [Real.arcsin_neg]; exact h1
      exact (Real.arcsin_le_iff_le_sin' ⟨by linarith, by linarith⟩).1 h3
    · exact (Real.le_arcsin_iff_sin_le' ⟨by linarith, by linarith⟩).1 h2

/-- **A steady phase under one tick, for every turn** (Sec. IV.C).  A state of one qubit with
unit amplitude and the phase `φ`, counted from the phase of a second state, is turned by `Δ` in a
tick, and the amplitude `ε` of the second state, `0 < ε < 1`, is added to it at that fixed
phase.  For every real `Δ`, the sum has the phase `φ` again, with some positive amplitude, for
some `φ` (`keepsPhase`) exactly when `cos Δ > 0` and `|sin Δ| ≤ ε`.  No range of `Δ` is
supposed.  The condition requires the two inequalities (`steady_phase_requires`).  Conversely,
with the two, `Δ` lies within `arcsin ε < π/2` of `2πk` for an integer `k`
(`near_whole_turn_iff`), so `steady_phase_iff` gives the condition for `Δ − 2πk`, and whole
turns leave it as it is (`keepsPhase_add_turns`).  With `near_whole_turn_iff` it gives the
sentence of Sec. IV.C that `steady_phase_iff_turns` states, at `ε = h/L`. -/
theorem steady_phase_all_turns (Δ ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    keepsPhase Δ ε ↔ 0 < Real.cos Δ ∧ |Real.sin Δ| ≤ ε := by
  constructor
  · exact steady_phase_requires Δ ε hε hε1.le
  · intro h
    obtain ⟨k, hk⟩ := (near_whole_turn_iff Δ ε hε1).1 h
    have ha1 : Real.arcsin ε < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hε1
    -- `Δ − 2πk` lies within `arcsin ε < π/2` of zero, where `steady_phase_iff` applies
    have hq : |Δ - 2 * Real.pi * k| < Real.pi / 2 := lt_of_le_of_lt hk ha1
    have hsin : Real.sin (Δ - 2 * Real.pi * k) = Real.sin Δ := by
      rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
      exact Real.sin_sub_int_mul_two_pi _ k
    have h1 : keepsPhase (Δ - 2 * Real.pi * k) ε :=
      (steady_phase_iff _ ε hε hq).2 (by rw [hsin]; exact h.2)
    have h2 := (keepsPhase_add_turns (Δ - 2 * Real.pi * k) ε k).2 h1
    rwa [sub_add_cancel] at h2

/-- **The steady phase as ranges of the turn** (Sec. IV.C).  For an added amplitude `0 < ε < 1`
and every turn `Δ`, the tick leaves a phase unchanged (`keepsPhase`) exactly when `Δ` lies
within `arcsin ε` of a whole number of turns: `|Δ − 2πk| ≤ arcsin ε` for some integer `k`
(`steady_phase_all_turns`, `near_whole_turn_iff`).  These are the two sentences of Sec. IV.C,
"Consider a state of unit amplitude that a tick turns by `Δ` against the body's phase, and to
which the tick adds the smaller amplitude `h/L` at the body's phase.  It has a phase against the
body's that the tick leaves unchanged exactly when `Δ` is within `arcsin(h/L)` of a whole number
of turns, as the Lean files prove."  The paper states it with `ε = h/L`.  The statement proves the equivalence for a turn `Δ` and an amplitude added at a fixed phase.  `keepsAgainstBody_iff` and `keepsAgainstBody_either` read the tick against the body's phase as that case, with `Δ` the slip of the string against the body. -/
theorem steady_phase_iff_turns (Δ ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    keepsPhase Δ ε ↔ ∃ k : ℤ, |Δ - 2 * Real.pi * k| ≤ Real.arcsin ε :=
  (steady_phase_all_turns Δ ε hε hε1).trans (near_whole_turn_iff Δ ε hε1)

/-- **The steady phase for a turn from zero up** (Sec. IV.C).  For `0 < ε < 1` and a turn
`Δ ≥ 0`, the tick leaves a phase unchanged (`keepsPhase`) exactly when `|Δ − 2πk| ≤ arcsin ε`
for some `k = 0, 1, 2, …`: a turn `Δ ≥ 0` within `arcsin ε < π/2` of `2πk` has `k ≥ 0`
(`steady_phase_iff_turns`). -/
theorem steady_phase_iff_turns_nat (Δ ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hΔ : 0 ≤ Δ) :
    keepsPhase Δ ε ↔ ∃ k : ℕ, |Δ - 2 * Real.pi * k| ≤ Real.arcsin ε := by
  rw [steady_phase_iff_turns Δ ε hε hε1]
  have ha1 : Real.arcsin ε < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hε1
  constructor
  · rintro ⟨k, hk⟩
    -- a turn `Δ ≥ 0` within less than `π/2` of `2πk` has `k ≥ 0`
    have hk0 : 0 ≤ k := by
      by_contra hneg
      push Not at hneg
      have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
      have h1 := (abs_le.mp hk).2
      nlinarith [Real.pi_pos]
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    exact ⟨n, by simpa using hk⟩
  · rintro ⟨n, hn⟩
    exact ⟨(n : ℤ), by simpa using hn⟩

/-- **The energies at which the phase holds** (Sec. IV.C).  A free tick turns the global phase
of a string of energy `E ≥ 0` by `E/u`, with `u > 0` the energy of a string that a tick turns by one
radian (`u = ℏ/t_c`, by Sec. II's definition of energy), and it adds the amplitude `ε`,
`0 < ε < 1`.  The string's phase holds (`keepsPhase`) exactly when `E ≤ u arcsin ε`, the first
range, or `u(2πk − arcsin ε) ≤ E ≤ u(2πk + arcsin ε)` for a whole number `k ≥ 1`, written
`k + 1` with `k = 0, 1, 2, …`: the ranges about the whole turns
(`steady_phase_iff_turns_nat`). -/
theorem phase_ranges (u ε E : ℝ) (hu : 0 < u) (hε : 0 < ε) (hε1 : ε < 1) (hE : 0 ≤ E) :
    keepsPhase (E / u) ε ↔
      E ≤ u * Real.arcsin ε ∨
      ∃ k : ℕ, u * (2 * Real.pi * (k + 1) - Real.arcsin ε) ≤ E ∧
        E ≤ u * (2 * Real.pi * (k + 1) + Real.arcsin ε) := by
  have hΔ : 0 ≤ E / u := div_nonneg hE hu.le
  rw [steady_phase_iff_turns_nat (E / u) ε hε hε1 hΔ]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨h1, h2⟩ := abs_le.mp hn
    cases n with
    | zero =>
      left
      rw [Nat.cast_zero, mul_zero, sub_zero, div_le_iff₀ hu] at h2
      linarith
    | succ k =>
      right
      rw [Nat.cast_succ] at h1 h2
      refine ⟨k, ?_, ?_⟩
      · have h3 : 2 * Real.pi * ((k : ℝ) + 1) - Real.arcsin ε ≤ E / u := by linarith
        rw [le_div_iff₀ hu] at h3
        linarith
      · have h3 : E / u ≤ 2 * Real.pi * ((k : ℝ) + 1) + Real.arcsin ε := by linarith
        rw [div_le_iff₀ hu] at h3
        linarith
  · rintro (h | ⟨k, h1, h2⟩)
    · refine ⟨0, ?_⟩
      rw [Nat.cast_zero, mul_zero, sub_zero, abs_of_nonneg hΔ, div_le_iff₀ hu]
      linarith
    · refine ⟨k + 1, ?_⟩
      rw [Nat.cast_succ, abs_le]
      constructor
      · have h3 : 2 * Real.pi * ((k : ℝ) + 1) - Real.arcsin ε ≤ E / u := by
          rw [le_div_iff₀ hu]
          linarith
        linarith
      · have h3 : E / u ≤ 2 * Real.pi * ((k : ℝ) + 1) + Real.arcsin ε := by
          rw [div_le_iff₀ hu]
          linarith
        linarith

open MeasureTheory in
/-- **The fraction of the strings in a range of energies, from the fractions above an energy**
(Sec. IV.C).  `μ` is a distribution of the strings' energies, a probability measure on the real
line, and `above x` is the fraction that it gives to the energies above `x`, for every `x ≥ 0`
(`htail`).  With `above` continuous and `above 0 = 1`, the energies from `a` to `c`,
`0 ≤ a ≤ c`, both ends included, have the fraction `above a − above c`.  The energies from `a`
up, `a` included, have the fraction `above a`: for `a > 0` it is at most the fraction above
every smaller energy, which tends to `above a`, and for `a = 0` it is at most one.  So no single
energy `a ≥ 0` has a positive fraction.  The energies from `a` to `c` are those from `a` up
without those above `c`. -/
theorem measure_Icc_of_above (μ : Measure ℝ) [IsProbabilityMeasure μ] (above : ℝ → ℝ)
    (hcont : Continuous above) (h0 : above 0 = 1)
    (htail : ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) (a c : ℝ) (ha : 0 ≤ a)
    (hac : a ≤ c) : (μ (Set.Icc a c)).toReal = above a - above c := by
  have hfin : ∀ s : Set ℝ, μ s ≠ ⊤ := fun s => measure_ne_top μ s
  -- the energies from `a` up, `a` included, have the fraction `above a`
  have hIci : (μ (Set.Ici a)).toReal = above a := by
    apply le_antisymm
    · rcases ha.eq_or_lt with rfl | hpos
      · rw [h0]
        exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      · have hlim : Filter.Tendsto above (nhdsWithin a (Set.Iio a)) (nhds (above a)) :=
          (hcont.tendsto a).mono_left nhdsWithin_le_nhds
        refine ge_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsLT hpos] with x hx
        rw [← htail x hx.1.le]
        exact ENNReal.toReal_mono (hfin _) (measure_mono (Set.Ici_subset_Ioi.2 hx.2))
    · rw [← htail a ha]
      exact ENNReal.toReal_mono (hfin _) (measure_mono Set.Ioi_subset_Ici_self)
  rw [← Set.Ici_sdiff_Ioi, measure_sdiff (Set.Ioi_subset_Ici hac)
    measurableSet_Ioi.nullMeasurableSet (hfin _),
    ENNReal.toReal_sub_of_le (measure_mono (Set.Ioi_subset_Ici hac)) (hfin _), hIci,
    htail c (ha.trans hac)]

open MeasureTheory in
/-- **A distribution with the Gibbs fractions exists** (Sec. IV.C).  For a thermal energy
`θ > 0` there is a probability measure on the real line, a distribution of energies, that gives
the energies above `x` the Gibbs fraction `gibbsAbove θ x`, which is `e^{−x/θ}`
(`gibbsAbove_eq`), for every `x ≥ 0`.  It is the Stieltjes measure of the distribution function
`1 − e^{−x/θ}` for `x ≥ 0`, and `0` below.  So a rule that is stated for every distribution with
these fractions, as `Sources.P1.carriers_hold_phase` is, is stated for at least one. -/
theorem gibbs_measure_exists (θ : ℝ) (hθ : 0 < θ) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = gibbsAbove θ x := by
  -- the distribution function `F(x) = 1 − e^{−x/θ}` for `x ≥ 0`, and `0` below
  let F : StieltjesFunction ℝ :=
    { toFun := fun x => 1 - Real.exp (-(max x 0) / θ)
      mono' := by
        intro x y hxy
        have h1 : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
        have h2 : -(max y 0) / θ ≤ -(max x 0) / θ :=
          div_le_div_of_nonneg_right (neg_le_neg h1) hθ.le
        have h3 := Real.exp_le_exp.2 h2
        show 1 - Real.exp (-(max x 0) / θ) ≤ 1 - Real.exp (-(max y 0) / θ)
        linarith
      right_continuous' := fun x => by
        have hc : Continuous fun x : ℝ => 1 - Real.exp (-(max x 0) / θ) := by fun_prop
        exact hc.continuousWithinAt }
  have hF : ∀ x : ℝ, F x = 1 - Real.exp (-(max x 0) / θ) := fun _ => rfl
  have hbot : Filter.Tendsto F Filter.atBot (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with x hx
    rw [hF, max_eq_right hx, neg_zero, zero_div, Real.exp_zero, sub_self]
  have htop : Filter.Tendsto F Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun x : ℝ => Real.exp (-(x / θ))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.atTop_div_const hθ)
    have h2 : Filter.Tendsto (fun x : ℝ => 1 - Real.exp (-(x / θ))) Filter.atTop
        (nhds (1 - 0)) := tendsto_const_nhds.sub h1
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    rw [hF, max_eq_left hx, neg_div]
  refine ⟨F.measure, F.isProbabilityMeasure hbot htop, fun x hx => ?_⟩
  rw [F.measure_Ioi htop x, gibbsAbove_eq θ x hθ, hF, max_eq_left hx, sub_sub_cancel,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- **The ranges about the whole turns, summed** (Sec. IV.C).  For `L > 0` the numbers
`e^{−L(2π(k+1) − α)} − e^{−L(2π(k+1) + α)}`, `k = 0, 1, 2, …`, sum to
`(e^{Lα} − e^{−Lα})/(e^{2πL} − 1)`: the `k`-th is `(e^{Lα} − e^{−Lα})q^{k+1}` with
`q = e^{−2πL}`, and the series is geometric.  In `range_fractions` the `k`-th number is the
fraction of the strings in the range about the whole turn `2π(k + 1)`. -/
theorem whole_turns_sum (L α : ℝ) (hL : 0 < L) :
    HasSum (fun k : ℕ => Real.exp (-(L * (2 * Real.pi * (k + 1) - α))) -
        Real.exp (-(L * (2 * Real.pi * (k + 1) + α))))
      ((Real.exp (L * α) - Real.exp (-(L * α))) / (Real.exp (2 * Real.pi * L) - 1)) := by
  have hpos : 0 < 2 * Real.pi * L := by positivity
  have hq0 : 0 < Real.exp (-(2 * Real.pi * L)) := Real.exp_pos _
  have hq1 : Real.exp (-(2 * Real.pi * L)) < 1 := exp_neg_lt_one hpos
  -- each term is `(e^{Lα} − e^{−Lα}) q^{k+1}` with `q = e^{−2πL}`
  have hterm : (fun k : ℕ => Real.exp (-(L * (2 * Real.pi * (k + 1) - α))) -
      Real.exp (-(L * (2 * Real.pi * (k + 1) + α)))) = fun k : ℕ =>
      (Real.exp (L * α) - Real.exp (-(L * α))) * Real.exp (-(2 * Real.pi * L)) *
        Real.exp (-(2 * Real.pi * L)) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, sub_mul, sub_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    congr 2 <;> ring
  -- the geometric series: `q/(1 − q) = 1/(e^{2πL} − 1)`
  have hQ : Real.exp (-(2 * Real.pi * L)) * Real.exp (2 * Real.pi * L) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : 1 - Real.exp (-(2 * Real.pi * L)) ≠ 0 := by linarith
  have h2 : Real.exp (2 * Real.pi * L) - 1 ≠ 0 := by
    have := Real.add_one_lt_exp hpos.ne'
    linarith
  have h3 : Real.exp (-(2 * Real.pi * L)) * (1 - Real.exp (-(2 * Real.pi * L)))⁻¹ =
      (Real.exp (2 * Real.pi * L) - 1)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div, div_eq_div_iff h1 h2]
    linear_combination hQ
  have hsum := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left
    ((Real.exp (L * α) - Real.exp (-(L * α))) * Real.exp (-(2 * Real.pi * L)))
  have hval : (Real.exp (L * α) - Real.exp (-(L * α))) * Real.exp (-(2 * Real.pi * L)) *
      (1 - Real.exp (-(2 * Real.pi * L)))⁻¹ =
      (Real.exp (L * α) - Real.exp (-(L * α))) / (Real.exp (2 * Real.pi * L) - 1) := by
    rw [show (Real.exp (L * α) - Real.exp (-(L * α))) * Real.exp (-(2 * Real.pi * L)) *
      (1 - Real.exp (-(2 * Real.pi * L)))⁻¹ = (Real.exp (L * α) - Real.exp (-(L * α))) *
      (Real.exp (-(2 * Real.pi * L)) * (1 - Real.exp (-(2 * Real.pi * L)))⁻¹) from
      mul_assoc _ _ _, h3, div_eq_mul_inv]
  rw [hterm, ← hval]
  exact hsum

open MeasureTheory in
/-- **The fractions of the strings in the ranges of the turn** (Sec. IV.C).  `μ` is a
distribution of the strings' energies, a probability measure, and `u > 0` is the energy of a
string that a free tick turns by one radian.  The strings that a free tick turns by more than
`x` radians, those of energy above `ux`, are the fraction `e^{−Lx}`, for every `x ≥ 0`
(`htail`), with `L > 0`.  Let `α = arcsin ε` with `0 < ε < 1`.  The first part: the first range,
the energies from `0` to `uα`, holds the fraction `1 − e^{−Lα}` of the strings.  The second
part: the range about the whole turn `2π(k + 1)`, the energies from `u(2π(k + 1) − α)` to
`u(2π(k + 1) + α)`, holds the fraction `e^{−L(2π(k+1) − α)} − e^{−L(2π(k+1) + α)}`, for
`k = 0, 1, 2, …` (`measure_Icc_of_above`).  The third part: the ranges about the whole turns
hold the fraction `(e^{Lα} − e^{−Lα})/(e^{2πL} − 1)` together.  They are separate, since
`α < π/2`, so their fractions add up (`whole_turns_sum`). -/
theorem range_fractions (u L ε : ℝ) (hu : 0 < u) (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (htail : ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi (u * x))).toReal = Real.exp (-(L * x))) :
    (μ (Set.Icc 0 (u * Real.arcsin ε))).toReal = 1 - Real.exp (-(L * Real.arcsin ε)) ∧
    (∀ k : ℕ, (μ (Set.Icc (u * (2 * Real.pi * (k + 1) - Real.arcsin ε))
        (u * (2 * Real.pi * (k + 1) + Real.arcsin ε)))).toReal =
        Real.exp (-(L * (2 * Real.pi * (k + 1) - Real.arcsin ε))) -
          Real.exp (-(L * (2 * Real.pi * (k + 1) + Real.arcsin ε)))) ∧
    (μ (⋃ k : ℕ, Set.Icc (u * (2 * Real.pi * (k + 1) - Real.arcsin ε))
        (u * (2 * Real.pi * (k + 1) + Real.arcsin ε)))).toReal =
      (Real.exp (L * Real.arcsin ε) - Real.exp (-(L * Real.arcsin ε))) /
        (Real.exp (2 * Real.pi * L) - 1) := by
  have hα0 : 0 ≤ Real.arcsin ε := Real.arcsin_nonneg.2 hε.le
  have hα1 : Real.arcsin ε < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hε1
  have hpi := Real.pi_pos
  -- the fraction of the strings above an energy `y ≥ 0` is `e^{−Ly/u}`, continuous in `y`
  have hcont : Continuous fun y : ℝ => Real.exp (-(L * (y / u))) := by fun_prop
  have htail' : ∀ y : ℝ, 0 ≤ y →
      (μ (Set.Ioi y)).toReal = (fun y : ℝ => Real.exp (-(L * (y / u)))) y := by
    intro y hy
    have h1 := htail (y / u) (div_nonneg hy hu.le)
    rwa [mul_div_cancel₀ y hu.ne'] at h1
  -- the strings whose turn lies from `a` to `c`, `0 ≤ a ≤ c`, are the fraction
  -- `e^{−La} − e^{−Lc}`
  have hrange : ∀ a c : ℝ, 0 ≤ a → a ≤ c →
      (μ (Set.Icc (u * a) (u * c))).toReal = Real.exp (-(L * a)) - Real.exp (-(L * c)) := by
    intro a c ha hac
    have h1 := measure_Icc_of_above μ _ hcont (by simp) htail' (u * a) (u * c)
      (mul_nonneg hu.le ha) (mul_le_mul_of_nonneg_left hac hu.le)
    simp only [mul_div_cancel_left₀ _ hu.ne'] at h1
    exact h1
  -- the first range
  have hI : (μ (Set.Icc 0 (u * Real.arcsin ε))).toReal =
      1 - Real.exp (-(L * Real.arcsin ε)) := by
    have h1 := hrange 0 _ le_rfl hα0
    simp only [mul_zero, neg_zero, Real.exp_zero] at h1
    exact h1
  -- the range about the whole turn `2π(k + 1)`
  have hk : ∀ k : ℕ, (μ (Set.Icc (u * (2 * Real.pi * (k + 1) - Real.arcsin ε))
      (u * (2 * Real.pi * (k + 1) + Real.arcsin ε)))).toReal =
      Real.exp (-(L * (2 * Real.pi * (k + 1) - Real.arcsin ε))) -
        Real.exp (-(L * (2 * Real.pi * (k + 1) + Real.arcsin ε))) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact hrange _ _ (by nlinarith) (by linarith)
  -- the ranges about the whole turns are separate, since `arcsin ε < π/2`
  have hpair : Pairwise (Function.onFun Disjoint fun k : ℕ =>
      Set.Icc (u * (2 * Real.pi * (k + 1) - Real.arcsin ε))
        (u * (2 * Real.pi * (k + 1) + Real.arcsin ε))) := by
    rw [pairwise_disjoint_on]
    intro m n hmn
    rw [Set.disjoint_left]
    intro E hm hn
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
    have h1 : u * (2 * Real.pi * (n + 1) - Real.arcsin ε) ≤
        u * (2 * Real.pi * (m + 1) + Real.arcsin ε) := hn.1.trans hm.2
    have h2 := le_of_mul_le_mul_left h1 hu
    nlinarith
  refine ⟨hI, hk, ?_⟩
  -- their fractions add up
  rw [measure_iUnion hpair (fun k => measurableSet_Icc),
    ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ _), tsum_congr hk]
  exact (whole_turns_sum L (Real.arcsin ε) hL).tsum_eq

open MeasureTheory in
/-- **The fraction of the strings whose phase holds, over every turn** (Sec. IV.C).  `μ` is a
distribution of the strings' energies, a probability measure, and `u > 0` is the energy of a
string that a free tick turns by one radian.  The strings that a free tick turns by more than
`x` radians, those of energy above `ux`, are the fraction `e^{−Lx}`, for every `x ≥ 0`
(`htail`), with `L > 0`.  Each tick adds the amplitude `ε`, `0 < ε < 1`.  Then the strings of
energy `E ≥ 0` whose phase holds (`keepsPhase (E/u) ε`) are the fraction
`(1 − e^{−Lα})(1 + (e^{Lα} + 1)/(e^{2πL} − 1))` of the strings, with `α = arcsin ε`.  They are
the strings of the first range, `E ≤ uα`, and of the ranges about the whole turns,
`u(2πk − α) ≤ E ≤ u(2πk + α)` with `k ≥ 1` (`phase_ranges`).  The first range is separate from
the others, since `α < π/2`.  It holds the fraction `1 − e^{−Lα}`, and the ranges about the
whole turns hold `(e^{Lα} − e^{−Lα})/(e^{2πL} − 1)` together (`range_fractions`), which is
`(1 − e^{−Lα})(e^{Lα} + 1)/(e^{2πL} − 1)`. -/
theorem phase_fraction (u L ε : ℝ) (hu : 0 < u) (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (htail : ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi (u * x))).toReal = Real.exp (-(L * x))) :
    (μ {E : ℝ | 0 ≤ E ∧ keepsPhase (E / u) ε}).toReal =
      (1 - Real.exp (-(L * Real.arcsin ε))) *
        (1 + (Real.exp (L * Real.arcsin ε) + 1) / (Real.exp (2 * Real.pi * L) - 1)) := by
  have hα1 : Real.arcsin ε < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hε1
  have hpi := Real.pi_pos
  obtain ⟨hI, -, hB⟩ := range_fractions u L ε hu hL hε hε1 μ htail
  -- the strings whose phase holds: the first range and the ranges about the whole turns
  have hset : {E : ℝ | 0 ≤ E ∧ keepsPhase (E / u) ε} =
      Set.Icc 0 (u * Real.arcsin ε) ∪
        ⋃ k : ℕ, Set.Icc (u * (2 * Real.pi * (k + 1) - Real.arcsin ε))
          (u * (2 * Real.pi * (k + 1) + Real.arcsin ε)) := by
    ext E
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Icc, Set.mem_iUnion]
    constructor
    · rintro ⟨hE, hk⟩
      rcases (phase_ranges u ε E hu hε hε1 hE).1 hk with h | ⟨k, h1, h2⟩
      · exact Or.inl ⟨hE, h⟩
      · exact Or.inr ⟨k, h1, h2⟩
    · rintro (⟨hE, h⟩ | ⟨k, h1, h2⟩)
      · exact ⟨hE, (phase_ranges u ε E hu hε hε1 hE).2 (Or.inl h)⟩
      · have hE : 0 ≤ E := by
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have : 0 ≤ u * (2 * Real.pi * (k + 1) - Real.arcsin ε) :=
            mul_nonneg hu.le (by nlinarith)
          linarith
        exact ⟨hE, (phase_ranges u ε E hu hε hε1 hE).2 (Or.inr ⟨k, h1, h2⟩)⟩
  -- the first range is separate from the ranges about the whole turns, since `arcsin ε < π/2`
  have hdisj : Disjoint (Set.Icc 0 (u * Real.arcsin ε))
      (⋃ k : ℕ, Set.Icc (u * (2 * Real.pi * (k + 1) - Real.arcsin ε))
          (u * (2 * Real.pi * (k + 1) + Real.arcsin ε))) := by
    rw [Set.disjoint_left]
    intro E hE hE'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hE'
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : u * (2 * Real.pi * (k + 1) - Real.arcsin ε) ≤ u * Real.arcsin ε :=
      hk.1.trans hE.2
    have h2 := le_of_mul_le_mul_left h1 hu
    nlinarith
  rw [hset, measure_union hdisj (MeasurableSet.iUnion fun k => measurableSet_Icc),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hI, hB]
  have hx : Real.exp (-(L * Real.arcsin ε)) * Real.exp (L * Real.arcsin ε) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : (1 - Real.exp (-(L * Real.arcsin ε))) * (Real.exp (L * Real.arcsin ε) + 1) =
      Real.exp (L * Real.arcsin ε) - Real.exp (-(L * Real.arcsin ε)) := by
    linear_combination -hx
  rw [← h2]
  ring

/-- **The arcsine between its argument and the tangent** (Sec. IV.C): for `0 ≤ y < 1`,
`y ≤ arcsin y ≤ y/√(1 − y²)`.  With `x = arcsin y`, in `[0, π/2)`, these are `sin x ≤ x` and
`x ≤ tan x`, with `tan(arcsin y) = y/√(1 − y²)`. -/
theorem arcsin_bounds (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    y ≤ Real.arcsin y ∧ Real.arcsin y ≤ y / Real.sqrt (1 - y ^ 2) := by
  have ha0 : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.2 hy0
  have ha1 : Real.arcsin y < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hy1
  constructor
  · have h := Real.sin_le ha0
    rwa [Real.sin_arcsin (by linarith) hy1.le] at h
  · have h := Real.le_tan ha0 ha1
    rwa [Real.tan_arcsin] at h

/-- **The exponent of the first range between its bounds** (Sec. IV.C): for `0 ≤ h < L`,
`h ≤ L arcsin(h/L) ≤ h/√(1 − (h/L)²)`, by `arcsin_bounds` at `y = h/L`, times `L`.  The number
`L arcsin(h/L)` is the first range's threshold in units of the horizon's thermal energy
(`Reg.threshold_bounds`), and `h` is its leading order in `1/L`. -/
theorem exponent_bounds (L h : ℝ) (hL : 0 < L) (hh0 : 0 ≤ h) (hhL : h < L) :
    h ≤ L * Real.arcsin (h / L) ∧
    L * Real.arcsin (h / L) ≤ h / Real.sqrt (1 - (h / L) ^ 2) := by
  have hy0 : 0 ≤ h / L := div_nonneg hh0 hL.le
  have hy1 : h / L < 1 := (div_lt_one hL).2 hhL
  obtain ⟨h1, h2⟩ := arcsin_bounds (h / L) hy0 hy1
  constructor
  · calc h = L * (h / L) := by field_simp
      _ ≤ L * Real.arcsin (h / L) := mul_le_mul_of_nonneg_left h1 hL.le
  · calc L * Real.arcsin (h / L)
        ≤ L * (h / L / Real.sqrt (1 - (h / L) ^ 2)) := mul_le_mul_of_nonneg_left h2 hL.le
      _ = h / Real.sqrt (1 - (h / L) ^ 2) := by
          rw [← mul_div_assoc, mul_div_cancel₀ h hL.ne']

/-- **The first range's fraction between its bounds** (Sec. IV.C): for `0 ≤ h < L`, the number
`1 − e^{−L arcsin(h/L)}`, the fraction of the strings in the first range (`range_fractions`), is
at least `1 − e^{−h}`, Eq. (b), and at most `1 − e^{−h/√(1 − (h/L)²)}` (`exponent_bounds`). -/
theorem first_range_bounds (L h : ℝ) (hL : 0 < L) (hh0 : 0 ≤ h) (hhL : h < L) :
    1 - Real.exp (-h) ≤ 1 - Real.exp (-(L * Real.arcsin (h / L))) ∧
    1 - Real.exp (-(L * Real.arcsin (h / L))) ≤
      1 - Real.exp (-(h / Real.sqrt (1 - (h / L) ^ 2))) := by
  obtain ⟨h1, h2⟩ := exponent_bounds L h hL hh0 hhL
  constructor
  · have := Real.exp_le_exp.2 (neg_le_neg h1)
    linarith
  · have := Real.exp_le_exp.2 (neg_le_neg h2)
    linarith

/-- `1/√(1 − y²) ≤ 1 + y²` for `0 ≤ y ≤ 1/2`: the square of `(1 + y²)√(1 − y²)` is
`1 + y²(1 − y² − y⁴) ≥ 1`. -/
lemma inv_sqrt_le (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    1 / Real.sqrt (1 - y ^ 2) ≤ 1 + y ^ 2 := by
  have hy2 : y ^ 2 ≤ 1 / 4 := by nlinarith
  have hpos : 0 < 1 - y ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.2 hpos
  have hsq : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hpos.le
  rw [div_le_iff₀ hs]
  by_contra hlt
  push Not at hlt
  have h0 : 0 ≤ (1 + y ^ 2) * Real.sqrt (1 - y ^ 2) := by positivity
  have h1 : ((1 + y ^ 2) * Real.sqrt (1 - y ^ 2)) ^ 2 < 1 := pow_lt_one₀ h0 hlt two_ne_zero
  rw [mul_pow, hsq] at h1
  have h2 : (1 + y ^ 2) ^ 2 * (1 - y ^ 2) - 1 = y ^ 2 * (1 - y ^ 2 - y ^ 2 * y ^ 2) := by ring
  have h3 : 0 ≤ y ^ 2 * (1 - y ^ 2 - y ^ 2 * y ^ 2) :=
    mul_nonneg (sq_nonneg y) (by nlinarith [sq_nonneg y])
  linarith

/-- **The first range's fraction to leading order in `1/L`** (Sec. IV.C, Eq. (b)).  For
`0 ≤ h ≤ L/2` the number `1 − e^{−L arcsin(h/L)}`, the fraction of the strings in the first
range (`range_fractions`), is at least `1 − e^{−h}`, and it exceeds `1 − e^{−h}` by at most the
fraction `(h/L)²` of it, and by at most `h(h/L)²`.  The excess is
`e^{−h} − e^{−L arcsin(h/L)}`, which the statement bounds.  The exponent exceeds `h` by at most
`h(h/L)²` (`exponent_bounds`, `inv_sqrt_le`), and `1 − e^{−t} ≤ t`, so the excess is at most
`e^{−h} h (h/L)²`; and `h e^{−h} ≤ 1 − e^{−h}`, since `h + 1 ≤ e^h`. -/
theorem first_range_leading_order (L h : ℝ) (hL : 0 < L) (hh0 : 0 ≤ h) (hhL : h ≤ L / 2) :
    0 ≤ Real.exp (-h) - Real.exp (-(L * Real.arcsin (h / L))) ∧
    Real.exp (-h) - Real.exp (-(L * Real.arcsin (h / L))) ≤
      (h / L) ^ 2 * (1 - Real.exp (-h)) ∧
    Real.exp (-h) - Real.exp (-(L * Real.arcsin (h / L))) ≤ h * (h / L) ^ 2 := by
  have hlt : h < L := by linarith
  have hy0 : 0 ≤ h / L := div_nonneg hh0 hL.le
  have hy : h / L ≤ 1 / 2 := by rw [div_le_iff₀ hL]; linarith
  obtain ⟨h1, h2⟩ := exponent_bounds L h hL hh0 hlt
  have hinv := inv_sqrt_le (h / L) hy0 hy
  -- the exponent exceeds `h` by at most `h (h/L)²`
  have hA : L * Real.arcsin (h / L) - h ≤ h * (h / L) ^ 2 := by
    have : h / Real.sqrt (1 - (h / L) ^ 2) ≤ h * (1 + (h / L) ^ 2) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinv hh0
    linarith
  have he : 0 < Real.exp (-h) := Real.exp_pos _
  -- `e^{−A} = e^{−h} e^{−(A − h)} ≥ e^{−h} (1 − (A − h))`
  have hsplit : Real.exp (-(L * Real.arcsin (h / L))) =
      Real.exp (-h) * Real.exp (-(L * Real.arcsin (h / L) - h)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlow := Real.one_sub_le_exp_neg (L * Real.arcsin (h / L) - h)
  have hdiff : Real.exp (-h) - Real.exp (-(L * Real.arcsin (h / L))) ≤
      Real.exp (-h) * (h * (h / L) ^ 2) := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hlow he.le
    have := mul_le_mul_of_nonneg_left hA he.le
    nlinarith
  -- `h e^{−h} ≤ 1 − e^{−h}`, from `h + 1 ≤ e^h`
  have hexp : h * Real.exp (-h) ≤ 1 - Real.exp (-h) := by
    have h3 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp h) he.le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
    linarith
  have hsq : 0 ≤ (h / L) ^ 2 := sq_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · have := Real.exp_le_exp.2 (neg_le_neg h1)
    linarith
  · calc Real.exp (-h) - Real.exp (-(L * Real.arcsin (h / L)))
        ≤ Real.exp (-h) * (h * (h / L) ^ 2) := hdiff
      _ = (h / L) ^ 2 * (h * Real.exp (-h)) := by ring
      _ ≤ (h / L) ^ 2 * (1 - Real.exp (-h)) := mul_le_mul_of_nonneg_left hexp hsq
  · have hle1 : Real.exp (-h) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)
    calc Real.exp (-h) - Real.exp (-(L * Real.arcsin (h / L)))
        ≤ Real.exp (-h) * (h * (h / L) ^ 2) := hdiff
      _ ≤ 1 * (h * (h / L) ^ 2) :=
          mul_le_mul_of_nonneg_right hle1 (mul_nonneg hh0 hsq)
      _ = h * (h / L) ^ 2 := one_mul _

/-- `(e^A + 1)/(e^{2πL} − 1) ≤ 4e^{−3πL/2}` for `0 ≤ A ≤ πL/2` and `L ≥ 1`, with
`e^{2πL} − 1 > 0`: `e^A + 1 ≤ 2e^{πL/2}`, `e^{πL/2} = e^{−3πL/2} e^{2πL}`, and
`e^{2πL} ≤ 2(e^{2πL} − 1)`, since `e^{2πL} ≥ 2`. -/
lemma whole_turns_le (L A : ℝ) (hL : 1 ≤ L) (hA0 : 0 ≤ A) (hA : A ≤ Real.pi / 2 * L) :
    0 < Real.exp (2 * Real.pi * L) - 1 ∧
    (Real.exp A + 1) / (Real.exp (2 * Real.pi * L) - 1) ≤
      4 * Real.exp (-(3 * Real.pi / 2 * L)) := by
  have hpi := Real.two_le_pi
  -- `e^{2πL} ≥ 2`
  have hQ2 : 2 ≤ Real.exp (2 * Real.pi * L) := by
    have h1 : (1 : ℝ) ≤ 2 * Real.pi * L := by nlinarith
    have h2 := Real.add_one_le_exp (2 * Real.pi * L)
    linarith
  have hQ1 : 0 < Real.exp (2 * Real.pi * L) - 1 := by linarith
  -- `e^A ≤ e^{πL/2} = e^{−3πL/2} e^{2πL}`, and `e^{2πL} ≤ 2(e^{2πL} − 1)`
  have h3 : Real.exp A ≤ Real.exp (Real.pi / 2 * L) := Real.exp_le_exp.2 hA
  have h4 : Real.exp (Real.pi / 2 * L) =
      Real.exp (-(3 * Real.pi / 2 * L)) * Real.exp (2 * Real.pi * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5 : 0 < Real.exp (-(3 * Real.pi / 2 * L)) := Real.exp_pos _
  have h6 : 1 ≤ Real.exp A := Real.one_le_exp hA0
  have h7 : Real.exp A ≤ 2 * Real.exp (-(3 * Real.pi / 2 * L)) *
      (Real.exp (2 * Real.pi * L) - 1) := by
    nlinarith [mul_nonneg h5.le (sub_nonneg.2 hQ2)]
  refine ⟨hQ1, ?_⟩
  rw [div_le_iff₀ hQ1]
  linarith

/-- **The strings near one or more whole turns** (Sec. IV.C).  The carriers are the fraction
`b = (1 − e^{−A})(1 + (e^{A} + 1)/(e^{2πL} − 1))`, with `A = L arcsin(h/L)` (`hb`,
`phase_fraction`), and `L > 0`, `h > 0`.  Then the excess of `b` over the first range's
fraction `1 − e^{−A}` is `(e^{A} − e^{−A})/(e^{2πL} − 1)`, the fraction of the strings in the
ranges about the whole turns (`range_fractions`).  It is positive, and it is below
`e^{−3πL/2}`: `A ≤ πL/2`, so `e^{A} − e^{−A} ≤ e^{πL/2} − e^{−πL/2}`, which is below
`e^{πL/2} − e^{−3πL/2} = e^{−3πL/2}(e^{2πL} − 1)`. -/
theorem whole_turns_bounds (L h b : ℝ) (hL : 0 < L) (hh0 : 0 < h)
    (hb : b = (1 - Real.exp (-(L * Real.arcsin (h / L)))) *
      (1 + (Real.exp (L * Real.arcsin (h / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1))) :
    b - (1 - Real.exp (-(L * Real.arcsin (h / L)))) =
      (Real.exp (L * Real.arcsin (h / L)) - Real.exp (-(L * Real.arcsin (h / L)))) /
        (Real.exp (2 * Real.pi * L) - 1) ∧
    0 < b - (1 - Real.exp (-(L * Real.arcsin (h / L)))) ∧
    b - (1 - Real.exp (-(L * Real.arcsin (h / L)))) < Real.exp (-(3 * Real.pi / 2 * L)) := by
  have hpi := Real.pi_pos
  have hy0 : 0 < h / L := div_pos hh0 hL
  have hA0 : 0 < L * Real.arcsin (h / L) := mul_pos hL (Real.arcsin_pos.2 hy0)
  have hA : L * Real.arcsin (h / L) ≤ Real.pi / 2 * L := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.arcsin_le_pi_div_two _) hL.le
  have hQ1 : 0 < Real.exp (2 * Real.pi * L) - 1 := by
    have h1 : 0 < 2 * Real.pi * L := by positivity
    have h2 := Real.add_one_lt_exp h1.ne'
    linarith
  have hx : Real.exp (-(L * Real.arcsin (h / L))) * Real.exp (L * Real.arcsin (h / L)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hem1 : Real.exp (-(L * Real.arcsin (h / L))) < 1 := exp_neg_lt_one hA0
  have hep1 : 1 < Real.exp (L * Real.arcsin (h / L)) := Real.one_lt_exp_iff.2 hA0
  have e : b - (1 - Real.exp (-(L * Real.arcsin (h / L)))) =
      (Real.exp (L * Real.arcsin (h / L)) - Real.exp (-(L * Real.arcsin (h / L)))) /
        (Real.exp (2 * Real.pi * L) - 1) := by
    have h2 : (1 - Real.exp (-(L * Real.arcsin (h / L)))) *
        (Real.exp (L * Real.arcsin (h / L)) + 1) =
        Real.exp (L * Real.arcsin (h / L)) - Real.exp (-(L * Real.arcsin (h / L))) := by
      linear_combination -hx
    rw [hb, ← h2]
    ring
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    exact div_pos (by linarith) hQ1
  · rw [e, div_lt_iff₀ hQ1]
    -- `e^A − e^{−A} ≤ e^{πL/2} − e^{−πL/2} < e^{πL/2} − e^{−3πL/2} = e^{−3πL/2}(e^{2πL} − 1)`
    have h1 : Real.exp (L * Real.arcsin (h / L)) ≤ Real.exp (Real.pi / 2 * L) :=
      Real.exp_le_exp.2 hA
    have h2 : Real.exp (-(Real.pi / 2 * L)) ≤ Real.exp (-(L * Real.arcsin (h / L))) :=
      Real.exp_le_exp.2 (neg_le_neg hA)
    have h3 : Real.exp (-(3 * Real.pi / 2 * L)) < Real.exp (-(Real.pi / 2 * L)) :=
      Real.exp_lt_exp.2 (by nlinarith [mul_pos hpi hL])
    have h4 : Real.exp (Real.pi / 2 * L) =
        Real.exp (-(3 * Real.pi / 2 * L)) * Real.exp (2 * Real.pi * L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linarith

/-- **The carriers' fraction between its bounds** (Sec. IV.C).  The carriers are the fraction
`b = (1 − e^{−A})(1 + (e^{A} + 1)/(e^{2πL} − 1))`, with `A = L arcsin(h/L)` (`hb`,
`phase_fraction`), and `L ≥ 1`, `0 ≤ h < L`.  Then `b` is at least `1 − e^{−h}`, Eq. (b), and
at most `(1 − e^{−h/√(1 − (h/L)²)})(1 + 4e^{−3πL/2})`.  The first factor of `b` lies between
`1 − e^{−h}` and `1 − e^{−h/√(1 − (h/L)²)}` (`first_range_bounds`), and the second between `1`
and `1 + 4e^{−3πL/2}` (`whole_turns_le`). -/
theorem fraction_bounds (L h b : ℝ) (hL : 1 ≤ L) (hh0 : 0 ≤ h) (hhL : h < L)
    (hb : b = (1 - Real.exp (-(L * Real.arcsin (h / L)))) *
      (1 + (Real.exp (L * Real.arcsin (h / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1))) :
    1 - Real.exp (-h) ≤ b ∧
    b ≤ (1 - Real.exp (-(h / Real.sqrt (1 - (h / L) ^ 2)))) *
      (1 + 4 * Real.exp (-(3 * Real.pi / 2 * L))) := by
  have hL0 : 0 < L := by linarith
  have hy0 : 0 ≤ h / L := div_nonneg hh0 hL0.le
  have hA0 : 0 ≤ L * Real.arcsin (h / L) := mul_nonneg hL0.le (Real.arcsin_nonneg.2 hy0)
  have hA : L * Real.arcsin (h / L) ≤ Real.pi / 2 * L := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.arcsin_le_pi_div_two _) hL0.le
  obtain ⟨hQ1, ht⟩ := whole_turns_le L _ hL hA0 hA
  obtain ⟨h1, h2⟩ := first_range_bounds L h hL0 hh0 hhL
  -- the first factor `b₀ ≥ 0`, and the second `1 + t` with `0 ≤ t ≤ 4e^{−3πL/2}`
  have hb0 : 0 ≤ 1 - Real.exp (-(L * Real.arcsin (h / L))) := by
    have : Real.exp (-(L * Real.arcsin (h / L))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by linarith)
    linarith
  have ht0 : 0 ≤ (Real.exp (L * Real.arcsin (h / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1) :=
    div_nonneg (by positivity) hQ1.le
  constructor
  · rw [hb]
    nlinarith [mul_nonneg hb0 ht0]
  · rw [hb]
    exact mul_le_mul h2 (by linarith) (by linarith) (le_trans hb0 h2)

/-- **The carriers' fraction to leading order in `1/L`** (Sec. IV.C, Eq. (b)).  The carriers
are the fraction `b = (1 − e^{−A})(1 + (e^{A} + 1)/(e^{2πL} − 1))`, with `A = L arcsin(h/L)`
(`hb`, `phase_fraction`), and `L ≥ 1`, `0 ≤ h ≤ L/2`.  Then `b` is at least `1 − e^{−h}`, and
it exceeds `1 − e^{−h}` by at most the fraction `(h/L)² + 5e^{−3πL/2}` of it, and by at most
`h((h/L)² + 5e^{−3πL/2})`.  The first factor of `b` is at most `(1 + (h/L)²)(1 − e^{−h})`
(`first_range_leading_order`) and the second at most `1 + 4e^{−3πL/2}` (`whole_turns_le`), with
`4(1 + (h/L)²) ≤ 5` for `h ≤ L/2`; and `1 − e^{−h} ≤ h`. -/
theorem fraction_leading_order (L h b : ℝ) (hL : 1 ≤ L) (hh0 : 0 ≤ h) (hhL : h ≤ L / 2)
    (hb : b = (1 - Real.exp (-(L * Real.arcsin (h / L)))) *
      (1 + (Real.exp (L * Real.arcsin (h / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1))) :
    0 ≤ b - (1 - Real.exp (-h)) ∧
    b - (1 - Real.exp (-h)) ≤
      ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L))) * (1 - Real.exp (-h)) ∧
    b - (1 - Real.exp (-h)) ≤ h * ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L))) := by
  have hL0 : 0 < L := by linarith
  have hy0 : 0 ≤ h / L := div_nonneg hh0 hL0.le
  have hy : h / L ≤ 1 / 2 := by rw [div_le_iff₀ hL0]; linarith
  have hy2 : (h / L) ^ 2 ≤ 1 / 4 := by nlinarith
  have hA0 : 0 ≤ L * Real.arcsin (h / L) := mul_nonneg hL0.le (Real.arcsin_nonneg.2 hy0)
  have hA : L * Real.arcsin (h / L) ≤ Real.pi / 2 * L := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.arcsin_le_pi_div_two _) hL0.le
  obtain ⟨hQ1, ht⟩ := whole_turns_le L _ hL hA0 hA
  obtain ⟨h1, h2, -⟩ := first_range_leading_order L h hL0 hh0 hhL
  have hE : 0 < Real.exp (-(3 * Real.pi / 2 * L)) := Real.exp_pos _
  have ht0 : 0 ≤ (Real.exp (L * Real.arcsin (h / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1) :=
    div_nonneg (by positivity) hQ1.le
  -- `c = 1 − e^{−h}`, with `0 ≤ c ≤ h`
  have hc0 : 0 ≤ 1 - Real.exp (-h) := by
    have : Real.exp (-h) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by linarith)
    linarith
  have hch : 1 - Real.exp (-h) ≤ h := by
    have := Real.add_one_le_exp (-h)
    linarith
  -- the first factor: `c ≤ b₀ ≤ (1 + (h/L)²) c`
  have hb1 : 1 - Real.exp (-h) ≤ 1 - Real.exp (-(L * Real.arcsin (h / L))) := by linarith
  have hb2 : 1 - Real.exp (-(L * Real.arcsin (h / L))) ≤
      (1 + (h / L) ^ 2) * (1 - Real.exp (-h)) := by linarith
  have hsq : 0 ≤ (h / L) ^ 2 := sq_nonneg _
  have hrel : b - (1 - Real.exp (-h)) ≤
      ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L))) * (1 - Real.exp (-h)) := by
    -- `b ≤ (1 + (h/L)²)(1 + 4e^{−3πL/2}) c ≤ (1 + (h/L)² + 5e^{−3πL/2}) c`
    have h3 : b ≤ (1 + (h / L) ^ 2) * (1 - Real.exp (-h)) *
        (1 + 4 * Real.exp (-(3 * Real.pi / 2 * L))) := by
      rw [hb]
      exact mul_le_mul hb2 (by linarith) (by linarith) (by positivity)
    nlinarith [mul_nonneg hc0 hE.le,
      mul_nonneg (mul_nonneg hc0 hE.le) (by linarith : (0 : ℝ) ≤ 1 / 4 - (h / L) ^ 2)]
  refine ⟨?_, hrel, ?_⟩
  · rw [hb]
    nlinarith [mul_nonneg (le_trans hc0 hb1) ht0]
  · calc b - (1 - Real.exp (-h))
        ≤ ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L))) * (1 - Real.exp (-h)) := hrel
      _ ≤ ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L))) * h :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ = h * ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L))) := mul_comm _ _

/-- **The law with the carriers' exact fraction, between its bounds** (Sec. IV.C).  The
carriers are the fraction `b = (1 − e^{−A})(1 + (e^{A} + 1)/(e^{2πL} − 1))`, with
`A = L arcsin(h/L)` (`hb`, `phase_fraction`), `L ≥ 1` and `0 < h < L`, and the acceleration is
`a = g_N/b` (`hab`, Eq. (share)).  Then the acceleration is at most `g_N/(1 − e^{−h})`, the
value of Eq. (law), and at least `g_N/((1 − e^{−h/√(1 − (h/L)²)})(1 + 4e^{−3πL/2}))`
(`fraction_bounds`).  Where `h ≤ L/2` it falls short of the value of Eq. (law) by at most the
fraction `(h/L)² + 5e^{−3πL/2}` of it (`fraction_leading_order`). -/
theorem law_bounds (gN L h a b : ℝ) (hgN : 0 < gN) (hL : 1 ≤ L) (hh0 : 0 < h) (hhL : h < L)
    (hb : b = (1 - Real.exp (-(L * Real.arcsin (h / L)))) *
      (1 + (Real.exp (L * Real.arcsin (h / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1)))
    (hab : a = gN / b) :
    gN / ((1 - Real.exp (-(h / Real.sqrt (1 - (h / L) ^ 2)))) *
      (1 + 4 * Real.exp (-(3 * Real.pi / 2 * L)))) ≤ a ∧
    a ≤ gN / (1 - Real.exp (-h)) ∧
    (h / L ≤ 1 / 2 →
      (1 - (h / L) ^ 2 - 5 * Real.exp (-(3 * Real.pi / 2 * L))) * (gN / (1 - Real.exp (-h))) ≤
        a) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hb1, hb2⟩ := fraction_bounds L h b hL hh0.le hhL hb
  have hc0 : 0 < 1 - Real.exp (-h) := by linarith [exp_neg_lt_one hh0]
  have hbpos : 0 < b := lt_of_lt_of_le hc0 hb1
  have hE : 0 < Real.exp (-(3 * Real.pi / 2 * L)) := Real.exp_pos _
  refine ⟨?_, ?_, fun hhalf => ?_⟩
  · rw [hab]
    exact div_le_div_of_nonneg_left hgN.le hbpos hb2
  · rw [hab]
    exact div_le_div_of_nonneg_left hgN.le hc0 hb1
  · have hhL2 : h ≤ L / 2 := by
      rw [div_le_iff₀ hL0] at hhalf
      linarith
    obtain ⟨-, hrel, -⟩ := fraction_leading_order L h b hL hh0.le hhL2 hb
    -- `b ≤ (1 + s)(1 − e^{−h})` with `s = (h/L)² + 5e^{−3πL/2}`, and `(1 − s)(1 + s) ≤ 1`
    have hb3 : b ≤ (1 + ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L)))) *
        (1 - Real.exp (-h)) := by linarith
    have hden : 0 < (1 + ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L)))) *
        (1 - Real.exp (-h)) := by positivity
    calc (1 - (h / L) ^ 2 - 5 * Real.exp (-(3 * Real.pi / 2 * L))) * (gN / (1 - Real.exp (-h)))
        ≤ gN / ((1 + ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L)))) *
            (1 - Real.exp (-h))) := by
          rw [le_div_iff₀ hden]
          have e : (1 - (h / L) ^ 2 - 5 * Real.exp (-(3 * Real.pi / 2 * L))) *
              (gN / (1 - Real.exp (-h))) *
              ((1 + ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L)))) *
                (1 - Real.exp (-h))) =
              (1 - ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L))) ^ 2) * gN := by
            field_simp
            ring
          rw [e]
          nlinarith [sq_nonneg ((h / L) ^ 2 + 5 * Real.exp (-(3 * Real.pi / 2 * L)))]
      _ ≤ gN / b := div_le_div_of_nonneg_left hgN.le hbpos hb3
      _ = a := hab.symm

/-- **The carriers' fraction increases with the amplitude of the share** (Sec. IV.C).  The
carriers are the fraction `b(h) = (1 − e^{−A})(1 + (e^{A} + 1)/(e^{2πL} − 1))` of the strings,
with `A = L arcsin(h/L)` (`phase_fraction`), and `L > 0`.  The first part: for `0 ≤ h₁ ≤ h₂`,
`b(h₁) ≤ b(h₂)`.  The second part: for `h₁ < h₂ ≤ L`, `b(h₁) < b(h₂)`.  The exponent `A`
increases with `h`, as the arcsine does, and both factors of `b` increase with `A`; the first
factor is not negative for `A ≥ 0`, and the second is positive.  Lean's arcsine stays at `π/2`
beyond `1`, so the first part needs no bound on `h₂`, and the second part has `h₂ ≤ L`.
`law_whole_bits` takes the first part at the amplitude of whole bits and at `√f`.
Sec. IV.C: the mean share of the body fills the fraction `f` of a string's bits "to within one
bit".  Data availability: "The three steps at leading order, the count's density, the share's amplitude,
and the carriers' fraction, are named as such, with their errors bounded in the files." -/
theorem carriers_fraction_mono (L h₁ h₂ : ℝ) (hL : 0 < L) (h0 : 0 ≤ h₁) (h12 : h₁ ≤ h₂) :
    (1 - Real.exp (-(L * Real.arcsin (h₁ / L)))) *
        (1 + (Real.exp (L * Real.arcsin (h₁ / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1)) ≤
      (1 - Real.exp (-(L * Real.arcsin (h₂ / L)))) *
        (1 + (Real.exp (L * Real.arcsin (h₂ / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1)) ∧
    (h₁ < h₂ → h₂ ≤ L →
      (1 - Real.exp (-(L * Real.arcsin (h₁ / L)))) *
          (1 + (Real.exp (L * Real.arcsin (h₁ / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1)) <
        (1 - Real.exp (-(L * Real.arcsin (h₂ / L)))) *
          (1 + (Real.exp (L * Real.arcsin (h₂ / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1))) := by
  have hQ : 0 < Real.exp (2 * Real.pi * L) - 1 := by
    have h1 : 0 < 2 * Real.pi * L := by positivity
    have h2 := Real.add_one_lt_exp h1.ne'
    linarith
  -- the second factor is positive at every exponent
  have hsec : ∀ s : ℝ, 0 < 1 + (Real.exp s + 1) / (Real.exp (2 * Real.pi * L) - 1) := by
    intro s
    have := div_pos (by positivity : 0 < Real.exp s + 1) hQ
    linarith
  -- both factors increase with the exponent, from zero up
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      (1 - Real.exp (-s)) * (1 + (Real.exp s + 1) / (Real.exp (2 * Real.pi * L) - 1)) ≤
          (1 - Real.exp (-t)) * (1 + (Real.exp t + 1) / (Real.exp (2 * Real.pi * L) - 1)) ∧
        (s < t →
          (1 - Real.exp (-s)) * (1 + (Real.exp s + 1) / (Real.exp (2 * Real.pi * L) - 1)) <
            (1 - Real.exp (-t)) * (1 + (Real.exp t + 1) / (Real.exp (2 * Real.pi * L) - 1))) := by
    intro s t hs hst
    have h1 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.2 (neg_le_neg hst)
    have h2 : Real.exp s ≤ Real.exp t := Real.exp_le_exp.2 hst
    have h3 : Real.exp (-t) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 : (Real.exp s + 1) / (Real.exp (2 * Real.pi * L) - 1) ≤
        (Real.exp t + 1) / (Real.exp (2 * Real.pi * L) - 1) :=
      (div_le_div_iff_of_pos_right hQ).2 (by linarith)
    refine ⟨mul_le_mul (by linarith) (by linarith) (hsec s).le (by linarith), fun hlt => ?_⟩
    have h5 : Real.exp (-t) < Real.exp (-s) := Real.exp_lt_exp.2 (neg_lt_neg hlt)
    exact mul_lt_mul (by linarith) (by linarith) (hsec s) (by linarith)
  have hy1 : 0 ≤ h₁ / L := div_nonneg h0 hL.le
  have hs0 : 0 ≤ L * Real.arcsin (h₁ / L) := mul_nonneg hL.le (Real.arcsin_nonneg.2 hy1)
  have hdiv : h₁ / L ≤ h₂ / L := (div_le_div_iff_of_pos_right hL).2 h12
  have hst : L * Real.arcsin (h₁ / L) ≤ L * Real.arcsin (h₂ / L) :=
    mul_le_mul_of_nonneg_left (Real.monotone_arcsin hdiv) hL.le
  refine ⟨(key _ _ hs0 hst).1, fun hlt hle => (key _ _ hs0 hst).2 ?_⟩
  -- the arcsine increases strictly up to `1`
  have hy2 : h₂ / L ≤ 1 := (div_le_one hL).2 hle
  have hdiv' : h₁ / L < h₂ / L := (div_lt_div_iff_of_pos_right hL).2 hlt
  have hstrict : Real.arcsin (h₁ / L) < Real.arcsin (h₂ / L) :=
    Real.strictMonoOn_arcsin ⟨by linarith, by linarith⟩ ⟨by linarith, hy2⟩ hdiv'
  exact mul_lt_mul_of_pos_left hstrict hL

/-- **The concavity of `1 − e^{−t}`** (Sec. IV.C): for `x > 0` and `0 ≤ y ≤ x`,
`(y/x)(1 − e^{−x}) ≤ 1 − e^{−y}`.  The function `t ↦ 1 − e^{−t}` is concave and vanishes at
`t = 0`, so its value at a point `y` between `0` and `x` is at least the fraction `y/x` of its
value at `x`.  The proof is the convexity of the exponential (`convexOn_exp`) at the points
`−x` and `0`, with the weights `y/x` and `1 − y/x`.  `law_whole_bits` takes it at `x = √f` and
`y = √(f − 1/L)`.
Sec. IV.C: the mean share of the body fills the fraction `f` of a string's bits "to within one
bit".  Data availability: "The three steps at leading order, the count's density, the share's amplitude,
and the carriers' fraction, are named as such, with their errors bounded in the files." -/
theorem one_sub_exp_concave (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    y / x * (1 - Real.exp (-x)) ≤ 1 - Real.exp (-y) := by
  have ht0 : 0 ≤ y / x := div_nonneg hy hx.le
  have ht1 : y / x ≤ 1 := (div_le_one hx).2 hyx
  -- `e^{−y} ≤ (y/x) e^{−x} + (1 − y/x) e^0`
  have hc := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (0 : ℝ)) ht0 (sub_nonneg.2 ht1)
    (by ring : y / x + (1 - y / x) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
  have e : y / x * -x = -y := by field_simp
  rw [e] at hc
  linarith

/-- `1/√(1 − x) ≤ 1 + x` for `0 ≤ x ≤ 1/2`: the square of `(1 + x)√(1 − x)` is
`1 + x(1 − x − x²) ≥ 1`.
Sec. IV.C: the mean share of the body fills the fraction `f` of a string's bits "to within one
bit".  Data availability: "The three steps at leading order, the count's density, the share's amplitude,
and the carriers' fraction, are named as such, with their errors bounded in the files." -/
lemma inv_sqrt_one_sub_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    1 / Real.sqrt (1 - x) ≤ 1 + x := by
  have hpos : 0 < 1 - x := by linarith
  have hs : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 hpos
  have hsq : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt hpos.le
  rw [div_le_iff₀ hs]
  by_contra hlt
  push Not at hlt
  have h0 : 0 ≤ (1 + x) * Real.sqrt (1 - x) := by positivity
  have h1 : ((1 + x) * Real.sqrt (1 - x)) ^ 2 < 1 := pow_lt_one₀ h0 hlt two_ne_zero
  rw [mul_pow, hsq] at h1
  have h2 : (1 + x) ^ 2 * (1 - x) - 1 = x * (1 - x - x ^ 2) := by ring
  have h3 : 0 ≤ x * (1 - x - x ^ 2) := mul_nonneg hx0 (by nlinarith)
  linarith

/-- **The law with the amplitude of whole bits, between its bounds** (Sec. IV.C).  The carriers
are the fraction `b = (1 − e^{−A})(1 + (e^{A} + 1)/(e^{2πL} − 1))`, with `A = L arcsin(h/L)`
(`hb`, `phase_fraction`), `L ≥ 1` and `0 < h < L`, and the acceleration is `a = g_N/b` (`hab`,
Eq. (share)).  The amplitude `h` is that of whole bits on a string of `L` bits: `h²` is at most
the fraction `f` and less than one bit below it, `f − 1/L < h² ≤ f` (`hlo`, `hhi`; the first
part of `share_amplitude` at `n = L`), where Eq. (law) takes `h = √f`.  The first part: where
`√f ≤ L/2`, the acceleration is at least `1 − (√f/L)² − 5e^{−3πL/2}` times the value
`g_N/(1 − e^{−√f})` of Eq. (law).  The fraction increases with `h` (`carriers_fraction_mono`)
and `h ≤ √f`, so `a` is at least the acceleration with the fraction at `√f`, which
`law_bounds` bounds.  The second part: where `f > 1/L`, the acceleration is at most the value
of Eq. (law) over `√(1 − 1/(L·f))`.  The fraction is at least `1 − e^{−h}`
(`fraction_bounds`), `h` exceeds `y = √(f − 1/L)`, and `1 − e^{−y} ≥ (y/√f)(1 − e^{−√f})`
(`one_sub_exp_concave`), with `y/√f = √(1 − 1/(L·f))`.  The third part: where `f ≥ 2/L`, the
acceleration is at most `1 + 1/(L·f)` times the value of Eq. (law) (`inv_sqrt_one_sub_le`).
Sec. IV.C: the mean share of the body fills the fraction `f` of a string's bits "to within one
bit".  Data availability: "The three steps at leading order, the count's density, the share's amplitude,
and the carriers' fraction, are named as such, with their errors bounded in the files." -/
theorem law_whole_bits (gN L f h a b : ℝ) (hgN : 0 < gN) (hL : 1 ≤ L) (hh0 : 0 < h) (hhL : h < L)
    (hlo : f - 1 / L < h ^ 2) (hhi : h ^ 2 ≤ f)
    (hb : b = (1 - Real.exp (-(L * Real.arcsin (h / L)))) *
      (1 + (Real.exp (L * Real.arcsin (h / L)) + 1) / (Real.exp (2 * Real.pi * L) - 1)))
    (hab : a = gN / b) :
    (Real.sqrt f / L ≤ 1 / 2 →
      (1 - (Real.sqrt f / L) ^ 2 - 5 * Real.exp (-(3 * Real.pi / 2 * L))) *
        (gN / (1 - Real.exp (-Real.sqrt f))) ≤ a) ∧
    (1 / L < f → a ≤ gN / (1 - Real.exp (-Real.sqrt f)) / Real.sqrt (1 - 1 / (L * f))) ∧
    (2 / L ≤ f → a ≤ (1 + 1 / (L * f)) * (gN / (1 - Real.exp (-Real.sqrt f)))) := by
  have hL0 : 0 < L := by linarith
  have hf : 0 < f := lt_of_lt_of_le (by positivity) hhi
  have hx : 0 < Real.sqrt f := Real.sqrt_pos.2 hf
  -- the amplitude of whole bits is at most `√f`
  have hle : h ≤ Real.sqrt f := Real.le_sqrt_of_sq_le hhi
  obtain ⟨hb1, -⟩ := fraction_bounds L h b hL hh0.le hhL hb
  have hc0 : 0 < 1 - Real.exp (-h) := by linarith [exp_neg_lt_one hh0]
  have hbpos : 0 < b := lt_of_lt_of_le hc0 hb1
  have hcx : 0 < 1 - Real.exp (-Real.sqrt f) := by linarith [exp_neg_lt_one hx]
  -- the lower bound: the fraction at `h` is at most the fraction at `√f`
  have hlow : Real.sqrt f / L ≤ 1 / 2 →
      (1 - (Real.sqrt f / L) ^ 2 - 5 * Real.exp (-(3 * Real.pi / 2 * L))) *
        (gN / (1 - Real.exp (-Real.sqrt f))) ≤ a := by
    intro hhalf
    have hxL : Real.sqrt f < L := by
      rw [div_le_iff₀ hL0] at hhalf
      linarith
    have hmono := (carriers_fraction_mono L h (Real.sqrt f) hL0 hh0.le hle).1
    rw [← hb] at hmono
    obtain ⟨-, -, h3⟩ := law_bounds gN L (Real.sqrt f) _ _ hgN hL hx hxL rfl rfl
    calc (1 - (Real.sqrt f / L) ^ 2 - 5 * Real.exp (-(3 * Real.pi / 2 * L))) *
          (gN / (1 - Real.exp (-Real.sqrt f)))
        ≤ gN / ((1 - Real.exp (-(L * Real.arcsin (Real.sqrt f / L)))) *
            (1 + (Real.exp (L * Real.arcsin (Real.sqrt f / L)) + 1) /
              (Real.exp (2 * Real.pi * L) - 1))) := h3 hhalf
      _ ≤ gN / b := div_le_div_of_nonneg_left hgN.le hbpos hmono
      _ = a := hab.symm
  -- the upper bound: `h` exceeds `√(f − 1/L)`, and `1 − e^{−t}` is concave
  have hup : 1 / L < f →
      a ≤ gN / (1 - Real.exp (-Real.sqrt f)) / Real.sqrt (1 - 1 / (L * f)) := by
    intro h1
    have hd : 0 < f - 1 / L := by linarith
    have hy : 0 < Real.sqrt (f - 1 / L) := Real.sqrt_pos.2 hd
    have hyh : Real.sqrt (f - 1 / L) < h := (Real.sqrt_lt' hh0).2 hlo
    have hyx : Real.sqrt (f - 1 / L) ≤ Real.sqrt f :=
      Real.sqrt_le_sqrt (by linarith [one_div_pos.2 hL0])
    -- `√(1 − 1/(L·f)) = √(f − 1/L)/√f`
    have hr : Real.sqrt (1 - 1 / (L * f)) = Real.sqrt (f - 1 / L) / Real.sqrt f := by
      rw [← Real.sqrt_div hd.le]
      congr 1
      field_simp
    have hconc := one_sub_exp_concave (Real.sqrt f) (Real.sqrt (f - 1 / L)) hx hy.le hyx
    have h2 : 1 - Real.exp (-Real.sqrt (f - 1 / L)) ≤ 1 - Real.exp (-h) := by
      have := Real.exp_le_exp.2 (neg_le_neg hyh.le)
      linarith
    have hden : 0 < Real.sqrt (f - 1 / L) / Real.sqrt f * (1 - Real.exp (-Real.sqrt f)) :=
      mul_pos (div_pos hy hx) hcx
    have hb2 : Real.sqrt (f - 1 / L) / Real.sqrt f * (1 - Real.exp (-Real.sqrt f)) ≤ b := by
      linarith
    rw [hab, hr, div_div, mul_comm (1 - Real.exp (-Real.sqrt f))]
    exact div_le_div_of_nonneg_left hgN.le hden hb2
  refine ⟨hlow, hup, fun h2 => ?_⟩
  -- the plainer form: `1/√(1 − t) ≤ 1 + t` at `t = 1/(L·f) ≤ 1/2`
  have h1 : 1 / L < f := lt_of_lt_of_le (by rw [div_lt_div_iff_of_pos_right hL0]; norm_num) h2
  have ht0 : 0 ≤ 1 / (L * f) := by positivity
  have ht : 1 / (L * f) ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0] at h2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hinv := inv_sqrt_one_sub_le (1 / (L * f)) ht0 ht
  have halaw : 0 < gN / (1 - Real.exp (-Real.sqrt f)) := div_pos hgN hcx
  calc a ≤ gN / (1 - Real.exp (-Real.sqrt f)) / Real.sqrt (1 - 1 / (L * f)) := hup h1
    _ = gN / (1 - Real.exp (-Real.sqrt f)) * (1 / Real.sqrt (1 - 1 / (L * f))) := by
        rw [div_eq_mul_one_div]
    _ ≤ gN / (1 - Real.exp (-Real.sqrt f)) * (1 + 1 / (L * f)) :=
        mul_le_mul_of_nonneg_left hinv halaw.le
    _ = (1 + 1 / (L * f)) * (gN / (1 - Real.exp (-Real.sqrt f))) := mul_comm _ _

/-- The Gibbs mean on a ladder of equal steps `ε`: the mean of the energies `nε`,
`n = 0, 1, 2, …`, with the weights `e^{−nε/θ}`. -/
noncomputable def gibbsLadder (ε θ : ℝ) : ℝ :=
  (∑' n : ℕ, ((n : ℝ) * ε) * Real.exp (-((n : ℝ) * ε) / θ)) /
    (∑' n : ℕ, Real.exp (-((n : ℝ) * ε) / θ))

/-- **The Gibbs mean on a ladder** (Sec. IV.E): `⟨E⟩ = ε/(e^{ε/θ} − 1)`, by the geometric
series. -/
theorem gibbsLadder_eq (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ) :
    gibbsLadder ε θ = ε / (Real.exp (ε / θ) - 1) := by
  -- the weights are the powers of `r = e^{−ε/θ} < 1`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.exp (-ε / θ) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have : 0 < ε / θ := div_pos hε hθ
    rw [neg_div]
    linarith
  have hterm : ∀ n : ℕ, Real.exp (-((n : ℝ) * ε) / θ) = r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0.le]; exact hr1
  have hden : ∑' n : ℕ, Real.exp (-((n : ℝ) * ε) / θ) = (1 - r)⁻¹ := by
    simp_rw [hterm]
    exact tsum_geometric_of_lt_one hr0.le hr1
  have hnum : ∑' n : ℕ, ((n : ℝ) * ε) * Real.exp (-((n : ℝ) * ε) / θ)
      = ε * (r / (1 - r) ^ 2) := by
    simp_rw [hterm]
    rw [← tsum_coe_mul_geometric_of_norm_lt_one hnorm, ← tsum_mul_left]
    exact tsum_congr (fun n => by ring)
  have hexp : Real.exp (ε / θ) = r⁻¹ := by
    rw [hr, ← Real.exp_neg]
    congr 1
    ring
  have h1r : 0 < 1 - r := by linarith
  have h1r' := h1r.ne'
  have hr0' := hr0.ne'
  have hinv : r⁻¹ - 1 = (1 - r) / r := by field_simp
  unfold gibbsLadder
  rw [hden, hnum, hexp, hinv]
  field_simp

/-- **A step changes the mean by less than the step** (Sec. IV.E): on a ladder of equal steps `ε`
the Gibbs mean lies within one step below the thermal energy, `θ − ε < ⟨E⟩ < θ`. -/
theorem gibbsLadder_within_step (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ) :
    θ - ε < gibbsLadder ε θ ∧ gibbsLadder ε θ < θ := by
  rw [gibbsLadder_eq ε θ hε hθ]
  have hθ' := hθ.ne'
  have hx : 0 < ε / θ := div_pos hε hθ
  have hup : ε / θ + 1 < Real.exp (ε / θ) := Real.add_one_lt_exp hx.ne'
  have hlow : 1 - ε / θ < Real.exp (-(ε / θ)) := Real.one_sub_lt_exp_neg hx.ne'
  have hd : 0 < Real.exp (ε / θ) - 1 := by linarith
  have hεθ : θ * (ε / θ) = ε := by field_simp
  constructor
  · -- `(θ − ε)(e^x − 1) < ε` with `x = ε/θ`, from `(1 − x)e^x < 1`
    rw [lt_div_iff₀ hd]
    have h1 : (1 - ε / θ) * Real.exp (ε / θ) < 1 := by
      have h := mul_lt_mul_of_pos_right hlow (Real.exp_pos (ε / θ))
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    have h2 : (θ - ε) * (Real.exp (ε / θ) - 1)
        = θ * ((1 - ε / θ) * Real.exp (ε / θ) - 1) + ε := by
      field_simp
      ring
    rw [h2]
    have h3 : θ * ((1 - ε / θ) * Real.exp (ε / θ) - 1) < 0 :=
      mul_neg_of_pos_of_neg hθ (by linarith)
    linarith
  · -- `ε < θ(e^x − 1)`, from `x + 1 < e^x`
    rw [div_lt_iff₀ hd]
    have h := mul_lt_mul_of_pos_left (show ε / θ < Real.exp (ε / θ) - 1 by linarith) hθ
    rwa [hεθ] at h

/-! ### The phase of a unit state under one tick (Sec. IV.C) -/

/-- **The new state along and across the old direction** (Sec. IV.C).  A state of unit amplitude
at the phase `φ`, counted from the phase of an added amplitude, has the components `cos φ` and
`sin φ`.  A tick turns it by `Δ` and adds the amplitude `ε` at the phase zero, so the new state
has the components `cos(φ + Δ) + ε` and `sin(φ + Δ)`.  The first part: its component along the
old direction `(cos φ, sin φ)` is `cos Δ + ε cos φ`.  The second part: its component across the
old direction, along `(−sin φ, cos φ)`, is `sin Δ − ε sin φ`.  The third part: the square of its
length is `1 + 2ε cos(φ + Δ) + ε²`.  The three hold for every real `φ`, `Δ` and `ε`.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tick_components (φ Δ ε : ℝ) :
    (Real.cos (φ + Δ) + ε) * Real.cos φ + Real.sin (φ + Δ) * Real.sin φ
      = Real.cos Δ + ε * Real.cos φ ∧
    Real.sin (φ + Δ) * Real.cos φ - (Real.cos (φ + Δ) + ε) * Real.sin φ
      = Real.sin Δ - ε * Real.sin φ ∧
    (Real.cos (φ + Δ) + ε) ^ 2 + Real.sin (φ + Δ) ^ 2
      = 1 + 2 * ε * Real.cos (φ + Δ) + ε ^ 2 := by
  have hp := Real.sin_sq_add_cos_sq φ
  have hq := Real.sin_sq_add_cos_sq (φ + Δ)
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.cos_add, Real.sin_add]
    linear_combination Real.cos Δ * hp
  · rw [Real.cos_add, Real.sin_add]
    linear_combination Real.sin Δ * hp
  · linear_combination hq

/-- **The change of the phase in one tick** (Sec. IV.C).  Let the new state of
`tick_components` have the amplitude `r` and the phase `ψ`: `cos(φ + Δ) + ε = r cos ψ` and
`sin(φ + Δ) = r sin ψ` (`hc`, `hs`).  Then `r sin(ψ − φ) = sin Δ − ε sin φ` and
`r cos(ψ − φ) = cos Δ + ε cos φ`: the change `ψ − φ` of the phase is the angle of the new state
from the old direction.  And `r² = 1 + 2ε cos(φ + Δ) + ε²`.  The statement holds for every
amplitude and phase of the new state, with no condition on `r`, `Δ` or `ε`.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tick_turn (φ Δ ε r ψ : ℝ) (hc : Real.cos (φ + Δ) + ε = r * Real.cos ψ)
    (hs : Real.sin (φ + Δ) = r * Real.sin ψ) :
    r * Real.sin (ψ - φ) = Real.sin Δ - ε * Real.sin φ ∧
    r * Real.cos (ψ - φ) = Real.cos Δ + ε * Real.cos φ ∧
    r ^ 2 = 1 + 2 * ε * Real.cos (φ + Δ) + ε ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := tick_components φ Δ ε
  have hp := Real.sin_sq_add_cos_sq ψ
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.sin_sub, ← h2, hc, hs]; ring
  · rw [Real.cos_sub, ← h1, hc, hs]; ring
  · rw [← h3, hc, hs]
    linear_combination (-(r ^ 2)) * hp

/-- **The new state has an amplitude and a phase** (Sec. IV.C).  For an added amplitude
`0 < ε < 1` and every `φ` and `Δ`, the new state of `tick_components` has an amplitude `r > 0`
and a phase `ψ`, with the equations of `tick_turn`, and `1 − ε ≤ r ≤ 1 + ε`.  The new state is
not zero, so it has a phase.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tick_polar (φ Δ ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ r ψ : ℝ, 0 < r ∧ Real.cos (φ + Δ) + ε = r * Real.cos ψ ∧
      Real.sin (φ + Δ) = r * Real.sin ψ ∧
      r * Real.sin (ψ - φ) = Real.sin Δ - ε * Real.sin φ ∧
      r * Real.cos (ψ - φ) = Real.cos Δ + ε * Real.cos φ ∧
      r ^ 2 = 1 + 2 * ε * Real.cos (φ + Δ) + ε ^ 2 ∧ 1 - ε ≤ r ∧ r ≤ 1 + ε := by
  -- the new state as a complex number, its modulus and its argument
  set z : ℂ := ⟨Real.cos (φ + Δ) + ε, Real.sin (φ + Δ)⟩ with hz
  have hc : Real.cos (φ + Δ) + ε = ‖z‖ * Real.cos (Complex.arg z) :=
    (Complex.norm_mul_cos_arg z).symm
  have hs : Real.sin (φ + Δ) = ‖z‖ * Real.sin (Complex.arg z) :=
    (Complex.norm_mul_sin_arg z).symm
  obtain ⟨h1, h2, h3⟩ := tick_turn φ Δ ε ‖z‖ (Complex.arg z) hc hs
  have hcos1 := Real.cos_le_one (φ + Δ)
  have hcos2 := Real.neg_one_le_cos (φ + Δ)
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hlo : (1 - ε) ^ 2 ≤ ‖z‖ ^ 2 := by rw [h3]; nlinarith
  have hhi : ‖z‖ ^ 2 ≤ (1 + ε) ^ 2 := by rw [h3]; nlinarith
  have hr1 : 1 - ε ≤ ‖z‖ := by nlinarith
  have hr2 : ‖z‖ ≤ 1 + ε := by nlinarith
  exact ⟨‖z‖, Complex.arg z, by linarith, hc, hs, h1, h2, h3, hr1, hr2⟩

/-- **The tick keeps the phase `φ`** (Sec. IV.C): the new state of `tick_components` is a
positive multiple of the old direction `(cos φ, sin φ)`.  `keepsPhase Δ ε` says that the tick
keeps some phase.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
def keepsPhaseAt (Δ ε φ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Real.cos (φ + Δ) + ε = r * Real.cos φ ∧ Real.sin (φ + Δ) = r * Real.sin φ

/-- **When the tick keeps a phase** (Sec. IV.C).  For every `φ`, `Δ` and `ε`, the tick keeps
the phase `φ` (`keepsPhaseAt`) exactly when the new state has no component across the old
direction, `sin Δ = ε sin φ`, and a positive component along it, `0 < cos Δ + ε cos φ`
(`tick_components`).
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem keepsPhaseAt_iff (Δ ε φ : ℝ) :
    keepsPhaseAt Δ ε φ ↔
      Real.sin Δ = ε * Real.sin φ ∧ 0 < Real.cos Δ + ε * Real.cos φ := by
  obtain ⟨h1, h2, -⟩ := tick_components φ Δ ε
  have hp := Real.sin_sq_add_cos_sq φ
  constructor
  · rintro ⟨r, hr, hc, hs⟩
    obtain ⟨t1, t2, -⟩ := tick_turn φ Δ ε r φ hc hs
    rw [sub_self, Real.sin_zero, mul_zero] at t1
    rw [sub_self, Real.cos_zero, mul_one] at t2
    exact ⟨by linarith, by rw [← t2]; exact hr⟩
  · rintro ⟨hsin, hpos⟩
    refine ⟨Real.cos Δ + ε * Real.cos φ, hpos, ?_, ?_⟩
    · rw [Real.cos_add]
      linear_combination (-(Real.sin φ)) * hsin - ε * hp
    · rw [Real.sin_add]
      linear_combination Real.cos φ * hsin

/-- **The kept phases and the condition of `steady_phase_all_turns`** (Sec. IV.C).  The first
part: the tick keeps some phase (`keepsPhase`) exactly when it keeps the phase `φ` for some `φ`
(`keepsPhaseAt`); the two say the same by definition.  The second part, for `0 < ε < 1`: some
`φ` has `sin Δ = ε sin φ` and `0 < cos Δ + ε cos φ` exactly when `cos Δ > 0` and `|sin Δ| ≤ ε`
(`keepsPhaseAt_iff` with `steady_phase_all_turns`).
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem keepsPhase_iff_kept (Δ ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (keepsPhase Δ ε ↔ ∃ φ, keepsPhaseAt Δ ε φ) ∧
    ((∃ φ, Real.sin Δ = ε * Real.sin φ ∧ 0 < Real.cos Δ + ε * Real.cos φ) ↔
      0 < Real.cos Δ ∧ |Real.sin Δ| ≤ ε) := by
  have h1 : keepsPhase Δ ε ↔ ∃ φ, keepsPhaseAt Δ ε φ := Iff.rfl
  refine ⟨h1, ?_⟩
  rw [← steady_phase_all_turns Δ ε hε hε1, h1]
  exact exists_congr fun φ => (keepsPhaseAt_iff Δ ε φ).symm

/-- **Where the added amplitude is smaller than the size of the sine of the turn, the phase moves in one sense at every tick** (Sec. IV.C).  Let the
added amplitude be smaller than the size of the sine of the turn, `0 < ε < |sin Δ|`, and let `φ` be any
phase.  The first and second parts: the component of the new state across the old direction,
`sin Δ − ε sin φ`, is not zero and has the sign of `sin Δ`.  The third part: the tick does not
keep the phase `φ`.  The fourth part: for every amplitude `r > 0` and phase `ψ` of the new
state, `sin(ψ − φ)` has the sign of `sin Δ` (`tick_turn`).  So the phase moves in the same sense
at every tick, whatever the phase is.  The turns within `arcsin ε` of an odd number of half turns, where `|sin Δ| ≤ ε` and `cos Δ < 0`, are outside the range of `steady_phase_all_turns` and not under this statement: there the tick keeps no phase either (`keepsPhase_iff_kept`), and no statement gives the sense in which the phase moves.  Of the sentence of Sec. IV.C quoted below, the files prove that the tick keeps no phase at any turn outside the range (`keepsPhase_iff_kept`), and that the phase moves in the same sense at every tick where `ε < |sin Δ|`.  `Main.phase_under_tick` states it for a string of the
register, with `Δ = Et_c/ℏ` and `ε = h/L` (`Reg.phase_under_tick`).
Sec. IV.C: "Where the slip per tick is larger, the global phase slips at every tick and the string takes
no phase from the body." -/
theorem phase_slips (Δ ε : ℝ) (hε : 0 < ε) (hout : ε < |Real.sin Δ|) (φ : ℝ) :
    Real.sin Δ - ε * Real.sin φ ≠ 0 ∧
    0 < Real.sin Δ * (Real.sin Δ - ε * Real.sin φ) ∧ ¬ keepsPhaseAt Δ ε φ ∧
    ∀ r ψ : ℝ, 0 < r → Real.cos (φ + Δ) + ε = r * Real.cos ψ →
      Real.sin (φ + Δ) = r * Real.sin ψ → 0 < Real.sin Δ * Real.sin (ψ - φ) := by
  have hb : |ε * Real.sin φ| ≤ ε := by
    rw [abs_mul, abs_of_pos hε]
    calc ε * |Real.sin φ| ≤ ε * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one φ) hε.le
      _ = ε := mul_one ε
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  -- the component across has the sign of `sin Δ`
  have hsign : 0 < Real.sin Δ * (Real.sin Δ - ε * Real.sin φ) := by
    rcases lt_abs.1 hout with h | h
    · exact mul_pos (by linarith) (by linarith)
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hne : Real.sin Δ - ε * Real.sin φ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsign
    exact lt_irrefl 0 hsign
  refine ⟨hne, hsign, fun hk => ?_, fun r ψ hr hc hs => ?_⟩
  · exact hne (by rw [((keepsPhaseAt_iff Δ ε φ).1 hk).1]; ring)
  · obtain ⟨t1, -, -⟩ := tick_turn φ Δ ε r ψ hc hs
    have h2 : Real.sin Δ * (r * Real.sin (ψ - φ)) = r * (Real.sin Δ * Real.sin (ψ - φ)) := by ring
    rw [← t1, h2] at hsign
    exact pos_of_mul_pos_right hsign hr.le

/-- **The kept phase inside the range** (Sec. IV.C).  For `0 < ε < 1`, `|sin Δ| < ε` and
`cos Δ > 0`, the phase `φ₀ = arcsin(sin Δ/ε)` has `sin Δ = ε sin φ₀`, lies strictly between
`−π/2` and `π/2`, so that `cos φ₀ > 0`, and `ε cos φ₀ < cos Δ`, since
`cos² Δ − ε² cos² φ₀ = 1 − ε² > 0`.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
lemma kept_phase_bounds (Δ ε φ₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hin : |Real.sin Δ| < ε)
    (hcos : 0 < Real.cos Δ) (hφ₀ : φ₀ = Real.arcsin (Real.sin Δ / ε)) :
    Real.sin Δ = ε * Real.sin φ₀ ∧ -(Real.pi / 2) < φ₀ ∧ φ₀ < Real.pi / 2 ∧
    0 < Real.cos φ₀ ∧ ε * Real.cos φ₀ < Real.cos Δ := by
  obtain ⟨hin1, hin2⟩ := abs_lt.mp hin
  have hq1 : -1 < Real.sin Δ / ε := by rw [lt_div_iff₀ hε]; linarith
  have hq2 : Real.sin Δ / ε < 1 := by rw [div_lt_one hε]; exact hin2
  have hs : Real.sin φ₀ = Real.sin Δ / ε := by rw [hφ₀]; exact Real.sin_arcsin hq1.le hq2.le
  have hlo : -(Real.pi / 2) < φ₀ := by rw [hφ₀]; exact Real.neg_pi_div_two_lt_arcsin.2 hq1
  have hhi : φ₀ < Real.pi / 2 := by rw [hφ₀]; exact Real.arcsin_lt_pi_div_two.2 hq2
  have hc : 0 < Real.cos φ₀ := Real.cos_pos_of_mem_Ioo ⟨hlo, hhi⟩
  have hsΔ : Real.sin Δ = ε * Real.sin φ₀ := by rw [hs]; field_simp
  have hp := Real.sin_sq_add_cos_sq φ₀
  have hq := Real.sin_sq_add_cos_sq Δ
  -- `cos² Δ = 1 − ε² sin² φ₀ > ε² cos² φ₀`
  have h1 : (ε * Real.cos φ₀) ^ 2 < Real.cos Δ ^ 2 := by
    have h2 : Real.cos Δ ^ 2 - (ε * Real.cos φ₀) ^ 2 = 1 - ε ^ 2 := by
      rw [hsΔ] at hq
      linear_combination hq - ε ^ 2 * hp
    have h3 : 0 < 1 - ε ^ 2 := by nlinarith
    linarith
  have h4 : ε * Real.cos φ₀ < Real.cos Δ := by
    have := abs_lt_of_sq_lt_sq' h1 hcos.le
    exact this.2
  exact ⟨hsΔ, hlo, hhi, hc, h4⟩

/-- **The kept phases inside the range** (Sec. IV.C).  For `0 < ε < 1`, `|sin Δ| < ε` and
`cos Δ > 0`, with `φ₀ = arcsin(sin Δ/ε)`: the tick keeps the phase `φ` (`keepsPhaseAt`) exactly
when `φ` is `φ₀` or `π − φ₀` up to whole turns.
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem kept_phases (Δ ε φ₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hin : |Real.sin Δ| < ε)
    (hcos : 0 < Real.cos Δ) (hφ₀ : φ₀ = Real.arcsin (Real.sin Δ / ε)) (φ : ℝ) :
    keepsPhaseAt Δ ε φ ↔
      ∃ k : ℤ, φ = φ₀ + 2 * Real.pi * k ∨ φ = Real.pi - φ₀ + 2 * Real.pi * k := by
  obtain ⟨hsΔ, -, -, hc, hlt⟩ := kept_phase_bounds Δ ε φ₀ hε hε1 hin hcos hφ₀
  rw [keepsPhaseAt_iff]
  constructor
  · rintro ⟨hs, -⟩
    -- `sin φ = sin φ₀`
    have h1 : Real.sin φ₀ = Real.sin φ := by
      have : ε * Real.sin φ₀ = ε * Real.sin φ := by rw [← hsΔ, hs]
      exact mul_left_cancel₀ hε.ne' this
    obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.1 h1
    · exact ⟨k, Or.inl (by rw [hk]; ring)⟩
    · exact ⟨k, Or.inr (by rw [hk]; ring)⟩
  · rintro ⟨k, hk | hk⟩
    · have hs : Real.sin φ = Real.sin φ₀ := by
        rw [hk, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
        exact Real.sin_add_int_mul_two_pi _ k
      have hcφ : Real.cos φ = Real.cos φ₀ := by
        rw [hk, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
        exact Real.cos_add_int_mul_two_pi _ k
      rw [hs, hcφ]
      exact ⟨hsΔ, by nlinarith⟩
    · have hs : Real.sin φ = Real.sin φ₀ := by
        rw [hk, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring,
          Real.sin_add_int_mul_two_pi, Real.sin_pi_sub]
      have hcφ : Real.cos φ = -Real.cos φ₀ := by
        rw [hk, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring,
          Real.cos_add_int_mul_two_pi, Real.cos_pi_sub]
      rw [hs, hcφ]
      exact ⟨hsΔ, by nlinarith⟩

/-- **Inside the range the phase moves toward one kept phase and away from the other**
(Sec. IV.C).  For `0 < ε < 1`, `|sin Δ| < ε` and `cos Δ > 0`, with `φ₀ = arcsin(sin Δ/ε)`, and
any phase `φ`.  The first part: the component of the new state across the old direction is
`sin Δ − ε sin φ = ε(sin φ₀ − sin φ)`.  The second and third parts: it is positive where
`sin φ < sin φ₀` and negative where `sin φ > sin φ₀`, and by `tick_turn` the phase then moves
forward and backward.  The fourth and fifth parts say where: it is positive for `φ` strictly
between `−π − φ₀` and `φ₀`, and negative for `φ` strictly between `φ₀` and `π − φ₀`.  The two
ranges and the two kept phases `φ₀` and `π − φ₀` make up one whole turn, so from every phase
other than those two the phase moves toward `φ₀` and away from `π − φ₀`.
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem phase_drawn (Δ ε φ₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hin : |Real.sin Δ| < ε)
    (hcos : 0 < Real.cos Δ) (hφ₀ : φ₀ = Real.arcsin (Real.sin Δ / ε)) (φ : ℝ) :
    Real.sin Δ - ε * Real.sin φ = ε * (Real.sin φ₀ - Real.sin φ) ∧
    (Real.sin φ < Real.sin φ₀ → 0 < Real.sin Δ - ε * Real.sin φ) ∧
    (Real.sin φ₀ < Real.sin φ → Real.sin Δ - ε * Real.sin φ < 0) ∧
    (-Real.pi - φ₀ < φ → φ < φ₀ → 0 < Real.sin Δ - ε * Real.sin φ) ∧
    (φ₀ < φ → φ < Real.pi - φ₀ → Real.sin Δ - ε * Real.sin φ < 0) := by
  obtain ⟨hsΔ, hlo, hhi, -, -⟩ := kept_phase_bounds Δ ε φ₀ hε hε1 hin hcos hφ₀
  have hid : Real.sin Δ - ε * Real.sin φ = ε * (Real.sin φ₀ - Real.sin φ) := by rw [hsΔ]; ring
  have hfwd : Real.sin φ < Real.sin φ₀ → 0 < Real.sin Δ - ε * Real.sin φ := by
    intro h
    rw [hid]
    exact mul_pos hε (by linarith)
  have hbwd : Real.sin φ₀ < Real.sin φ → Real.sin Δ - ε * Real.sin φ < 0 := by
    intro h
    rw [hid]
    exact mul_neg_of_pos_of_neg hε (by linarith)
  refine ⟨hid, hfwd, hbwd, fun h1 h2 => hfwd ?_, fun h1 h2 => hbwd ?_⟩
  · -- `sin φ₀ − sin φ = 2 sin((φ₀ − φ)/2) cos((φ₀ + φ)/2) > 0`
    have h3 : 0 < Real.sin ((φ₀ - φ) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have h4 : 0 < Real.cos ((φ₀ + φ) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have h5 := Real.sin_sub_sin φ₀ φ
    have h6 : 0 < 2 * Real.sin ((φ₀ - φ) / 2) * Real.cos ((φ₀ + φ) / 2) := by positivity
    linarith
  · -- `sin φ − sin φ₀ = 2 sin((φ − φ₀)/2) cos((φ + φ₀)/2) > 0`
    have h3 : 0 < Real.sin ((φ - φ₀) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have h4 : 0 < Real.cos ((φ + φ₀) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have h5 := Real.sin_sub_sin φ φ₀
    have h6 : 0 < 2 * Real.sin ((φ - φ₀) / 2) * Real.cos ((φ + φ₀) / 2) := by positivity
    linarith

/-- **The phase after one tick, the nearest to the phase before** (Sec. IV.C): the phase before,
`φ`, plus the angle of the new state from the old direction, taken between `−π` and `π`, with
`π` included.  The angle is the argument of the complex number whose real part is the component
of the new state along the old direction and whose imaginary part is the component across it
(`tick_components`).
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
noncomputable def tickPhase (Δ ε φ : ℝ) : ℝ :=
  φ + Complex.arg ⟨Real.cos Δ + ε * Real.cos φ, Real.sin Δ - ε * Real.sin φ⟩

/-- **`tickPhase` is a phase of the new state, within half a turn of the phase before**
(Sec. IV.C).  For `0 < ε < 1` and every `φ` and `Δ`: the new state of `tick_components` has a
positive amplitude `r` and the phase `tickPhase Δ ε φ`, and
`−π < tickPhase Δ ε φ − φ ≤ π`.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tickPhase_spec (Δ ε φ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ r : ℝ, 0 < r ∧ Real.cos (φ + Δ) + ε = r * Real.cos (tickPhase Δ ε φ) ∧
      Real.sin (φ + Δ) = r * Real.sin (tickPhase Δ ε φ)) ∧
    -Real.pi < tickPhase Δ ε φ - φ ∧ tickPhase Δ ε φ - φ ≤ Real.pi := by
  set w : ℂ := ⟨Real.cos Δ + ε * Real.cos φ, Real.sin Δ - ε * Real.sin φ⟩ with hw
  have hT : tickPhase Δ ε φ = φ + Complex.arg w := rfl
  have hc : ‖w‖ * Real.cos (Complex.arg w) = Real.cos Δ + ε * Real.cos φ :=
    Complex.norm_mul_cos_arg w
  have hs : ‖w‖ * Real.sin (Complex.arg w) = Real.sin Δ - ε * Real.sin φ :=
    Complex.norm_mul_sin_arg w
  have hp := Real.sin_sq_add_cos_sq φ
  have hq := Real.sin_sq_add_cos_sq (Complex.arg w)
  -- the length of the new state is at least `1 − ε`
  have hn2 : ‖w‖ ^ 2 = 1 + 2 * ε * Real.cos (φ + Δ) + ε ^ 2 := by
    have h1 : ‖w‖ ^ 2 = (Real.cos Δ + ε * Real.cos φ) ^ 2 + (Real.sin Δ - ε * Real.sin φ) ^ 2 := by
      rw [← hc, ← hs]
      linear_combination (-(‖w‖ ^ 2)) * hq
    rw [h1, Real.cos_add]
    have hd := Real.sin_sq_add_cos_sq Δ
    linear_combination hd + ε ^ 2 * hp
  have hr0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hcos2 := Real.neg_one_le_cos (φ + Δ)
  have hr : 0 < ‖w‖ := by nlinarith
  refine ⟨⟨‖w‖, hr, ?_, ?_⟩, ?_, ?_⟩
  · rw [hT, Real.cos_add, Real.cos_add]
    linear_combination (-(Real.cos φ)) * hc + Real.sin φ * hs - ε * hp
  · rw [hT, Real.sin_add, Real.sin_add]
    linear_combination (-(Real.sin φ)) * hc - Real.cos φ * hs
  · rw [hT, add_sub_cancel_left]
    exact Complex.neg_pi_lt_arg w
  · rw [hT, add_sub_cancel_left]
    exact Complex.arg_le_pi w

/-- **The phase after the tick at the kept phase** (Sec. IV.C).  For `0 < ε < 1`,
`|sin Δ| < ε` and `cos Δ > 0`, with `φ₀ = arcsin(sin Δ/ε)`: `tickPhase Δ ε φ₀ = φ₀`.
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tickPhase_kept (Δ ε φ₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hin : |Real.sin Δ| < ε)
    (hcos : 0 < Real.cos Δ) (hφ₀ : φ₀ = Real.arcsin (Real.sin Δ / ε)) :
    tickPhase Δ ε φ₀ = φ₀ := by
  obtain ⟨hsΔ, -, -, hc, -⟩ := kept_phase_bounds Δ ε φ₀ hε hε1 hin hcos hφ₀
  have h0 : Complex.arg ⟨Real.cos Δ + ε * Real.cos φ₀, Real.sin Δ - ε * Real.sin φ₀⟩ = 0 := by
    rw [Complex.arg_eq_zero_iff]
    exact ⟨by show 0 ≤ Real.cos Δ + ε * Real.cos φ₀; positivity,
      by show Real.sin Δ - ε * Real.sin φ₀ = 0; rw [hsΔ]; ring⟩
  unfold tickPhase
  rw [h0, add_zero]

/-- **The phase does not pass the kept phase** (Sec. IV.C).  For `0 < ε < 1`, `|sin Δ| < ε` and
`cos Δ > 0`, with `φ₀ = arcsin(sin Δ/ε)`.  The first part: for a phase `φ` strictly between `φ₀`
and `π − φ₀`, the phase after the tick (`tickPhase`) lies strictly between `φ₀` and `φ`.  The
second part: for `φ` strictly between `−π − φ₀` and `φ₀`, it lies strictly between `φ` and
`φ₀`.  So from every phase strictly between `−π − φ₀` and `π − φ₀`, other than `φ₀`, one tick
brings the phase nearer to `φ₀` and not beyond it.
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tick_between (Δ ε φ₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hin : |Real.sin Δ| < ε)
    (hcos : 0 < Real.cos Δ) (hφ₀ : φ₀ = Real.arcsin (Real.sin Δ / ε)) (φ : ℝ) :
    (φ₀ < φ → φ < Real.pi - φ₀ → φ₀ < tickPhase Δ ε φ ∧ tickPhase Δ ε φ < φ) ∧
    (-Real.pi - φ₀ < φ → φ < φ₀ → φ < tickPhase Δ ε φ ∧ tickPhase Δ ε φ < φ₀) := by
  obtain ⟨hsΔ, hlo, hhi, hc0, hlt⟩ := kept_phase_bounds Δ ε φ₀ hε hε1 hin hcos hφ₀
  obtain ⟨-, -, -, hfwd, hbwd⟩ := phase_drawn Δ ε φ₀ hε hε1 hin hcos hφ₀ φ
  obtain ⟨⟨r, hr, hc, hs⟩, hg1, hg2⟩ := tickPhase_spec Δ ε φ hε hε1
  set ψ := tickPhase Δ ε φ with hψ
  have hgdef : ψ - φ = Complex.arg ⟨Real.cos Δ + ε * Real.cos φ, Real.sin Δ - ε * Real.sin φ⟩ := by
    rw [hψ]; unfold tickPhase; ring
  -- the new state against the kept direction: `r sin(ψ − φ₀) = sin(φ − φ₀ + Δ) − sin Δ`
  have hkey : r * Real.sin (ψ - φ₀) = Real.sin (φ - φ₀ + Δ) - Real.sin Δ := by
    have h1 : Real.sin (φ - φ₀ + Δ) = Real.sin (φ + Δ) * Real.cos φ₀
        - Real.cos (φ + Δ) * Real.sin φ₀ := by
      rw [show φ - φ₀ + Δ = φ + Δ - φ₀ by ring, Real.sin_sub]
    rw [Real.sin_sub, h1, hsΔ]
    linear_combination (-(Real.cos φ₀)) * hs + Real.sin φ₀ * hc
  constructor
  · intro h1 h2
    -- the phase moves backward, by less than half a turn
    have hB : Real.sin Δ - ε * Real.sin φ < 0 := hbwd h1 h2
    have hg : ψ - φ < 0 := by rw [hgdef]; exact Complex.arg_neg_iff.2 hB
    refine ⟨?_, by linarith⟩
    by_contra hcon
    push Not at hcon
    -- else `ψ − φ₀` lies in `(−π, 0]`, where the sine is not positive
    have hsin : Real.sin (ψ - φ₀) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    have hd1 : 0 < (φ - φ₀) / 2 := by linarith
    have hd2 : (φ - φ₀) / 2 < Real.pi / 2 := by linarith
    have h3 : 0 < Real.sin ((φ - φ₀) / 2) := Real.sin_pos_of_pos_of_lt_pi hd1 (by linarith)
    have h4 : 0 < Real.cos ((φ - φ₀) / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hd2⟩
    have h5 : 0 < Real.cos (φ₀ + (φ - φ₀) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    -- `cos(Δ + δ/2) > ε cos(φ₀ + δ/2) > 0`
    have h6 : 0 < Real.cos (Δ + (φ - φ₀) / 2) := by
      rw [Real.cos_add] at h5 ⊢
      have h7 : ε * Real.cos φ₀ * Real.cos ((φ - φ₀) / 2)
          < Real.cos Δ * Real.cos ((φ - φ₀) / 2) := mul_lt_mul_of_pos_right hlt h4
      have h8 : 0 < ε * (Real.cos φ₀ * Real.cos ((φ - φ₀) / 2)
          - Real.sin φ₀ * Real.sin ((φ - φ₀) / 2)) := mul_pos hε h5
      rw [hsΔ]
      nlinarith
    have h9 := Real.sin_sub_sin (φ - φ₀ + Δ) Δ
    rw [show (φ - φ₀ + Δ - Δ) / 2 = (φ - φ₀) / 2 by ring,
      show (φ - φ₀ + Δ + Δ) / 2 = Δ + (φ - φ₀) / 2 by ring] at h9
    have h10 : 0 < r * Real.sin (ψ - φ₀) := by
      rw [hkey, h9]; positivity
    have h11 : r * Real.sin (ψ - φ₀) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le hsin
    linarith
  · intro h1 h2
    -- the phase moves forward, by at most half a turn
    have hB : 0 < Real.sin Δ - ε * Real.sin φ := hfwd h1 h2
    have hg : 0 < ψ - φ := by
      rw [hgdef]
      have h3 : 0 ≤ Complex.arg ⟨Real.cos Δ + ε * Real.cos φ, Real.sin Δ - ε * Real.sin φ⟩ :=
        Complex.arg_nonneg_iff.2 hB.le
      rcases h3.lt_or_eq with h4 | h4
      · exact h4
      · exact absurd (Complex.arg_eq_zero_iff.1 h4.symm).2 hB.ne'
    refine ⟨by linarith, ?_⟩
    by_contra hcon
    push Not at hcon
    -- else `ψ − φ₀` lies in `[0, π)`, where the sine is not negative
    have hsin : 0 ≤ Real.sin (ψ - φ₀) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hd1 : 0 < (φ₀ - φ) / 2 := by linarith
    have hd2 : (φ₀ - φ) / 2 ≤ Real.pi / 2 := by linarith
    have h3 : 0 < Real.sin ((φ₀ - φ) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hd1 (by linarith [Real.pi_pos])
    have h4 : 0 ≤ Real.cos ((φ₀ - φ) / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hd2⟩
    have h5 : 0 < Real.cos (φ₀ - (φ₀ - φ) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    -- `cos(Δ − δ/2) ≥ ε cos(φ₀ − δ/2) > 0`
    have h6 : 0 < Real.cos (Δ - (φ₀ - φ) / 2) := by
      rw [Real.cos_sub] at h5 ⊢
      have h7 : ε * Real.cos φ₀ * Real.cos ((φ₀ - φ) / 2)
          ≤ Real.cos Δ * Real.cos ((φ₀ - φ) / 2) := mul_le_mul_of_nonneg_right hlt.le h4
      have h8 : 0 < ε * (Real.cos φ₀ * Real.cos ((φ₀ - φ) / 2)
          + Real.sin φ₀ * Real.sin ((φ₀ - φ) / 2)) := mul_pos hε h5
      rw [hsΔ]
      nlinarith
    have h9 := Real.sin_sub_sin Δ (φ - φ₀ + Δ)
    rw [show (Δ - (φ - φ₀ + Δ)) / 2 = (φ₀ - φ) / 2 by ring,
      show (Δ + (φ - φ₀ + Δ)) / 2 = Δ - (φ₀ - φ) / 2 by ring] at h9
    have h10 : r * Real.sin (ψ - φ₀) < 0 := by
      have h12 : 0 < 2 * Real.sin ((φ₀ - φ) / 2) * Real.cos (Δ - (φ₀ - φ) / 2) := by positivity
      rw [hkey]; linarith
    have h11 : 0 ≤ r * Real.sin (ψ - φ₀) := mul_nonneg hr.le hsin
    linarith

open Filter Topology in
/-- A map of the real line that carries each point of an interval toward the interval's lower
end without passing it, and is continuous at each point of the interval, has iterates that
converge to that end from every point of the interval.  The iterates fall and stay above the
end, so they converge, and the map leaves their limit in place, which it does to no point of the
interval.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
lemma iterate_tendsto_lower (T : ℝ → ℝ) (a b : ℝ)
    (hT : ∀ x, a < x → x < b → a < T x ∧ T x < x)
    (hcont : ∀ x, a < x → x < b → ContinuousAt T x) (x₀ : ℝ) (h1 : a < x₀) (h2 : x₀ < b) :
    Tendsto (fun k => T^[k] x₀) atTop (𝓝 a) := by
  -- the iterates stay above `a` and do not rise
  have hinv : ∀ k, a < T^[k] x₀ ∧ T^[k] x₀ ≤ x₀ := by
    intro k
    induction k with
    | zero => exact ⟨h1, le_refl _⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨t1, t2⟩ := hT _ ih.1 (lt_of_le_of_lt ih.2 h2)
      exact ⟨t1, le_trans t2.le ih.2⟩
  have hanti : Antitone (fun k => T^[k] x₀) := by
    apply antitone_nat_of_succ_le
    intro k
    show T^[k + 1] x₀ ≤ T^[k] x₀
    rw [Function.iterate_succ_apply']
    exact (hT _ (hinv k).1 (lt_of_le_of_lt (hinv k).2 h2)).2.le
  have hbdd : BddBelow (Set.range (fun k => T^[k] x₀)) :=
    ⟨a, by rintro _ ⟨k, rfl⟩; exact (hinv k).1.le⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  -- the limit is a point that the map leaves in place, so it is `a`
  have hle : a ≤ ⨅ k, T^[k] x₀ := le_ciInf fun k => (hinv k).1.le
  have hub : (⨅ k, T^[k] x₀) ≤ x₀ := ciInf_le hbdd 0
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have hc := hcont _ hlt (lt_of_le_of_lt hub h2)
    have h3 : Tendsto (fun k => T (T^[k] x₀)) atTop (𝓝 (T (⨅ k, T^[k] x₀))) := hc.tendsto.comp hlim
    have h4 : Tendsto (fun k => T^[k + 1] x₀) atTop (𝓝 (⨅ k, T^[k] x₀)) :=
      hlim.comp (tendsto_add_atTop_nat 1)
    have h5 : (fun k => T^[k + 1] x₀) = fun k => T (T^[k] x₀) := by
      funext k
      exact Function.iterate_succ_apply' T k x₀
    rw [h5] at h4
    have h6 := tendsto_nhds_unique h3 h4
    have h7 := (hT _ hlt (lt_of_le_of_lt hub h2)).2
    linarith
  · rw [heq]
    exact hlim

open Filter Topology in
/-- The statement of `iterate_tendsto_lower` for a map that carries each point of an interval
toward the interval's upper end without passing it: the iterates converge to the upper end.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
lemma iterate_tendsto_upper (T : ℝ → ℝ) (c a : ℝ)
    (hT : ∀ x, c < x → x < a → x < T x ∧ T x < a)
    (hcont : ∀ x, c < x → x < a → ContinuousAt T x) (x₀ : ℝ) (h1 : c < x₀) (h2 : x₀ < a) :
    Tendsto (fun k => T^[k] x₀) atTop (𝓝 a) := by
  -- the map `y ↦ −T(−y)` carries each point between `−a` and `−c` toward `−a`
  have h := iterate_tendsto_lower (fun y => -T (-y)) (-a) (-c)
    (fun y hy1 hy2 => by
      obtain ⟨t1, t2⟩ := hT (-y) (by linarith) (by linarith)
      exact ⟨by linarith, by linarith⟩)
    (fun y hy1 hy2 => by
      have hc := hcont (-y) (by linarith) (by linarith)
      exact (ContinuousAt.comp (f := fun y : ℝ => -y) hc continuous_neg.continuousAt).neg)
    (-x₀) (by linarith) (by linarith)
  have hiter : ∀ k, (fun y => -T (-y))^[k] (-x₀) = -(T^[k] x₀) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, neg_neg, Function.iterate_succ_apply']
  simp only [hiter] at h
  have h' := h.neg
  simpa using h'

/-- **The phase after the tick is continuous in the phase before** (Sec. IV.C), at every phase
`φ` where the new state has a positive component along the old direction or a component across
it that is not zero: there the new state is not opposite to the old direction.
Sec. IV.C, the sentence that the statements of this block prove: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
lemma tickPhase_continuousAt (Δ ε φ : ℝ)
    (h : 0 < Real.cos Δ + ε * Real.cos φ ∨ Real.sin Δ - ε * Real.sin φ ≠ 0) :
    ContinuousAt (tickPhase Δ ε) φ := by
  have hw : ContinuousAt (fun x : ℝ =>
      (⟨Real.cos Δ + ε * Real.cos x, Real.sin Δ - ε * Real.sin x⟩ : ℂ)) φ := by
    have he : (fun x : ℝ => (⟨Real.cos Δ + ε * Real.cos x, Real.sin Δ - ε * Real.sin x⟩ : ℂ))
        = fun x : ℝ => ((Real.cos Δ + ε * Real.cos x : ℝ) : ℂ)
          + ((Real.sin Δ - ε * Real.sin x : ℝ) : ℂ) * Complex.I := by
      funext x
      exact Complex.mk_eq_add_mul_I _ _
    rw [he]
    fun_prop
  have harg : ContinuousAt (fun x : ℝ => Complex.arg
      (⟨Real.cos Δ + ε * Real.cos x, Real.sin Δ - ε * Real.sin x⟩ : ℂ)) φ :=
    ContinuousAt.comp (g := Complex.arg)
      (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 h)) hw
  exact continuousAt_id.add harg

open Filter Topology in
/-- **The repeated tick converges to the kept phase** (Sec. IV.C).  For `0 < ε < 1`,
`|sin Δ| < ε` and `cos Δ > 0`, with `φ₀ = arcsin(sin Δ/ε)`: from every phase `φ` strictly
between `−π − φ₀` and `π − φ₀`, the phases after one tick, two ticks and so on
(`tickPhase`, repeated) converge to `φ₀`.  Each tick brings the phase nearer to `φ₀` without
passing it (`tick_between`), and the only phase of that range that the tick keeps is `φ₀`.
`Main.phase_under_tick` states it for a string of the register, with `Δ = Et_c/ℏ` and
`ε = h/L` (`Reg.phase_under_tick`).
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tick_converges (Δ ε φ₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hin : |Real.sin Δ| < ε)
    (hcos : 0 < Real.cos Δ) (hφ₀ : φ₀ = Real.arcsin (Real.sin Δ / ε)) (φ : ℝ)
    (h1 : -Real.pi - φ₀ < φ) (h2 : φ < Real.pi - φ₀) :
    Tendsto (fun k => (tickPhase Δ ε)^[k] φ) atTop (𝓝 φ₀) := by
  rcases lt_trichotomy φ φ₀ with hlt | heq | hgt
  · exact iterate_tendsto_upper (tickPhase Δ ε) (-Real.pi - φ₀) φ₀
      (fun x hx1 hx2 => (tick_between Δ ε φ₀ hε hε1 hin hcos hφ₀ x).2 hx1 hx2)
      (fun x hx1 hx2 => tickPhase_continuousAt Δ ε x
        (Or.inr ((phase_drawn Δ ε φ₀ hε hε1 hin hcos hφ₀ x).2.2.2.1 hx1 hx2).ne')) φ h1 hlt
  · rw [heq]
    have hfix : ∀ k, (tickPhase Δ ε)^[k] φ₀ = φ₀ := fun k =>
      Function.iterate_fixed (tickPhase_kept Δ ε φ₀ hε hε1 hin hcos hφ₀) k
    simp only [hfix]
    exact tendsto_const_nhds
  · exact iterate_tendsto_lower (tickPhase Δ ε) φ₀ (Real.pi - φ₀)
      (fun x hx1 hx2 => (tick_between Δ ε φ₀ hε hε1 hin hcos hφ₀ x).1 hx1 hx2)
      (fun x hx1 hx2 => tickPhase_continuousAt Δ ε x
        (Or.inr ((phase_drawn Δ ε φ₀ hε hε1 hin hcos hφ₀ x).2.2.2.2 hx1 hx2).ne)) φ hgt h2

/-- **The factor by which a small gap shrinks per tick** (Sec. IV.C).  For `0 < ε < 1`,
`|sin Δ| < ε` and `cos Δ > 0`, with `φ₀ = arcsin(sin Δ/ε)`: at `φ₀` the phase after the tick
(`tickPhase`) has the derivative `cos Δ/(cos Δ + ε cos φ₀)` with respect to the phase before,
and that factor lies strictly between `0` and `1`.  So a small gap between the phase and `φ₀`
shrinks by that factor in one tick, to first order in the gap.
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove." -/
theorem tick_contracts (Δ ε φ₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hin : |Real.sin Δ| < ε)
    (hcos : 0 < Real.cos Δ) (hφ₀ : φ₀ = Real.arcsin (Real.sin Δ / ε)) :
    HasDerivAt (tickPhase Δ ε) (Real.cos Δ / (Real.cos Δ + ε * Real.cos φ₀)) φ₀ ∧
    0 < Real.cos Δ / (Real.cos Δ + ε * Real.cos φ₀) ∧
    Real.cos Δ / (Real.cos Δ + ε * Real.cos φ₀) < 1 := by
  obtain ⟨hsΔ, -, -, hc0, -⟩ := kept_phase_bounds Δ ε φ₀ hε hε1 hin hcos hφ₀
  have hr0 : 0 < Real.cos Δ + ε * Real.cos φ₀ := by positivity
  refine ⟨?_, div_pos hcos hr0, (div_lt_one hr0).2 (by nlinarith)⟩
  -- the new state along and across the old direction, as a complex number
  set w : ℝ → ℂ := fun x => ((Real.cos Δ + ε * Real.cos x : ℝ) : ℂ)
    + ((Real.sin Δ - ε * Real.sin x : ℝ) : ℂ) * Complex.I with hw
  have hT : tickPhase Δ ε = fun x => x + (Complex.log (w x)).im := by
    funext x
    rw [Complex.log_im]
    unfold tickPhase
    rw [Complex.mk_eq_add_mul_I]
  have hA : HasDerivAt (fun x : ℝ => Real.cos Δ + ε * Real.cos x) (ε * -Real.sin φ₀) φ₀ :=
    ((Real.hasDerivAt_cos φ₀).const_mul ε).const_add (Real.cos Δ)
  have hB : HasDerivAt (fun x : ℝ => Real.sin Δ - ε * Real.sin x) (-(ε * Real.cos φ₀)) φ₀ :=
    ((Real.hasDerivAt_sin φ₀).const_mul ε).const_sub (Real.sin Δ)
  have hw' : HasDerivAt w (((ε * -Real.sin φ₀ : ℝ) : ℂ)
      + ((-(ε * Real.cos φ₀) : ℝ) : ℂ) * Complex.I) φ₀ :=
    hA.ofReal_comp.add (hB.ofReal_comp.mul_const Complex.I)
  -- at the kept phase the new state lies along the old direction
  have hwφ : w φ₀ = ((Real.cos Δ + ε * Real.cos φ₀ : ℝ) : ℂ) := by
    simp only [hw]
    rw [hsΔ, sub_self, Complex.ofReal_zero, zero_mul, add_zero]
  have hmem : w φ₀ ∈ Complex.slitPlane := by
    rw [hwφ, Complex.mem_slitPlane_iff]
    exact Or.inl (by rw [Complex.ofReal_re]; exact hr0)
  have hlog := hw'.clog_real hmem
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt φ₀ hlog
  have hsum := (hasDerivAt_id φ₀).add him
  have hfun : (fun x : ℝ => x + (Complex.log (w x)).im)
      = id + ⇑Complex.imCLM ∘ fun t => Complex.log (w t) := by
    funext x
    rfl
  -- the derivative: `1 − ε cos φ₀/(cos Δ + ε cos φ₀)`
  have hval : Real.cos Δ / (Real.cos Δ + ε * Real.cos φ₀)
      = 1 + Complex.imCLM ((((ε * -Real.sin φ₀ : ℝ) : ℂ)
        + ((-(ε * Real.cos φ₀) : ℝ) : ℂ) * Complex.I) / w φ₀) := by
    rw [hwφ]
    simp only [Complex.imCLM_apply, Complex.div_ofReal_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add,
      add_zero]
    field_simp
    ring
  rw [hT, hfun, hval]
  exact hsum

/-- **The body's change drops out of the tick** (Sec. IV.C).  A string's global phase `φ` is
changed in a tick by `Δs + Δb`, the body's phase `θ` by `Δb`, and the tick adds to the string the
amplitude `ε` at the body's phase after the tick, `θ + Δb`.  `Δb` is the change of the body's
phase in the tick, of any size and either sense.  The new state
of the string has the amplitude `r` and the phase `ψ` exactly when the same state, turned back by
`θ + Δb`, has the amplitude `r` and the phase `ψ − (θ + Δb)`: then the phase against the body,
`φ − θ`, is changed by `Δs` alone, and the amplitude `ε` is added at the phase zero, as in
`tick_components`.  The two sides are one vector equation, the right one turned back by the
angle `θ + Δb`.  The statement holds for every real `φ`, `θ`, `Δs`, `Δb`, `ε`, `r` and `ψ`.
Sec. IV.C: "Whether the string keeps the body's phase depends on how its own global phase moves
against the body's."  "The body's energy on the string changes the string's phase and the body's
together, so the two part only by what the rest of the string's energy `E_s` does: `E_st_c/ℏ`
per tick, whichever way it turns the phase." -/
theorem tick_against_body (φ θ Δs Δb ε r ψ : ℝ) :
    (Real.cos (φ + (Δs + Δb)) + ε * Real.cos (θ + Δb) = r * Real.cos ψ ∧
      Real.sin (φ + (Δs + Δb)) + ε * Real.sin (θ + Δb) = r * Real.sin ψ) ↔
    (Real.cos (φ - θ + Δs) + ε = r * Real.cos (ψ - (θ + Δb)) ∧
      Real.sin (φ - θ + Δs) = r * Real.sin (ψ - (θ + Δb))) := by
  have hx : φ - θ + Δs = φ + (Δs + Δb) - (θ + Δb) := by ring
  have hp := Real.sin_sq_add_cos_sq (θ + Δb)
  rw [hx]
  simp only [Real.cos_sub, Real.sin_sub]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · linear_combination Real.cos (θ + Δb) * h1 + Real.sin (θ + Δb) * h2 - ε * hp
    · linear_combination Real.cos (θ + Δb) * h2 - Real.sin (θ + Δb) * h1
  · rintro ⟨g1, g2⟩
    constructor
    · linear_combination Real.cos (θ + Δb) * g1 - Real.sin (θ + Δb) * g2
        - (Real.cos (φ + (Δs + Δb)) - r * Real.cos ψ) * hp
    · linear_combination Real.sin (θ + Δb) * g1 + Real.cos (θ + Δb) * g2
        - (Real.sin (φ + (Δs + Δb)) - r * Real.sin ψ) * hp

/-- **The phase against the body under the tick** (Sec. IV.C), the reading of
`tick_against_body`.  The first part, the free case: without the share the phase against the
body moves by `Δs` per tick, `(φ + (Δs + Δb)) − (θ + Δb) = (φ − θ) + Δs`, and by nothing when
`Δs = 0`.  The second part: the tick leaves the string's phase against the body unchanged, the
new phase being `φ + Δb` with a positive amplitude `r`, exactly when the tick of `keepsPhaseAt`
with the turn `Δs` and the amplitude `ε` keeps the phase `φ − θ`.  The third part: some phase
against the body is kept exactly when `keepsPhase Δs ε`.  The three hold for every `θ` and
every change `Δb` of the body's phase in the tick, of any size and either sense: `Δb` does not
enter.
Sec. IV.C: "The body's energy on the string changes the string's phase and the body's together,
so the two part only by what the rest of the string's energy `E_s` does: `E_st_c/ℏ` per tick,
whichever way it turns the phase."  "A string that held the body's energy alone would not slip." -/
theorem kept_against_body (θ Δs Δb ε : ℝ) :
    (∀ φ : ℝ, (φ + (Δs + Δb)) - (θ + Δb) = (φ - θ) + Δs ∧
      (Δs = 0 → (φ + (Δs + Δb)) - (θ + Δb) = φ - θ)) ∧
    (∀ φ : ℝ, (∃ r : ℝ, 0 < r ∧
        Real.cos (φ + (Δs + Δb)) + ε * Real.cos (θ + Δb) = r * Real.cos (φ + Δb) ∧
        Real.sin (φ + (Δs + Δb)) + ε * Real.sin (θ + Δb) = r * Real.sin (φ + Δb)) ↔
      keepsPhaseAt Δs ε (φ - θ)) ∧
    ((∃ φ r : ℝ, 0 < r ∧
        Real.cos (φ + (Δs + Δb)) + ε * Real.cos (θ + Δb) = r * Real.cos (φ + Δb) ∧
        Real.sin (φ + (Δs + Δb)) + ε * Real.sin (θ + Δb) = r * Real.sin (φ + Δb)) ↔
      keepsPhase Δs ε) := by
  have hkept : ∀ φ : ℝ, (∃ r : ℝ, 0 < r ∧
      Real.cos (φ + (Δs + Δb)) + ε * Real.cos (θ + Δb) = r * Real.cos (φ + Δb) ∧
      Real.sin (φ + (Δs + Δb)) + ε * Real.sin (θ + Δb) = r * Real.sin (φ + Δb)) ↔
      keepsPhaseAt Δs ε (φ - θ) := by
    intro φ
    have hψ : φ + Δb - (θ + Δb) = φ - θ := by ring
    unfold keepsPhaseAt
    refine exists_congr fun r => and_congr_right fun _ => ?_
    rw [tick_against_body φ θ Δs Δb ε r (φ + Δb), hψ]
  refine ⟨fun φ => ⟨by ring, fun h0 => by rw [h0]; ring⟩, hkept, ?_⟩
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨r, hr⟩ := (hkept φ).1 hφ
    exact ⟨φ - θ, r, hr⟩
  · rintro ⟨φ₁, r, hr⟩
    refine ⟨φ₁ + θ, (hkept (φ₁ + θ)).2 ?_⟩
    rw [add_sub_cancel_right]
    exact ⟨r, hr⟩

/-- **The tick keeps the string's phase against the body's** (Sec. IV.C).  `Δ` is the whole
change of the string's phase in the tick, `Δb` the change of the body's phase in the same tick,
of any size and either sense, `θ` the body's phase and `ε` the amplitude
of the body's share that one tick adds, at the body's phase after the tick.  The condition is
that for some phase `φ` of the string the tick leaves the phase against the body unchanged: the
string's state of unit amplitude and phase `φ`, turned by `Δ` and with the amplitude `ε` added
at the phase `θ + Δb`, has the phase `φ + Δb` with some positive amplitude `r`.
`keepsAgainstBody_iff` reads it as `keepsPhase` at the slip `Δ − Δb`, and
`keepsAgainstBody_either` as `keepsPhase` at `Δs` where `Δ` is `Δb + Δs` or `Δb − Δs`. -/
def keepsAgainstBody (Δ Δb ε θ : ℝ) : Prop :=
  ∃ φ r : ℝ, 0 < r ∧
    Real.cos (φ + Δ) + ε * Real.cos (θ + Δb) = r * Real.cos (φ + Δb) ∧
    Real.sin (φ + Δ) + ε * Real.sin (θ + Δb) = r * Real.sin (φ + Δb)

/-- **The phase against the body is kept exactly when the slip keeps a phase** (Sec. IV.C).  For
every `Δs`, `Δb`, `ε` and `θ`, the tick with the string's whole change `Δs + Δb` and the body's
change `Δb` keeps the string's phase against the body's (`keepsAgainstBody`) exactly when
`keepsPhase Δs ε` holds: the third part of `kept_against_body`.  The body's change `Δb`, of any
size and either sense, and the body's phase `θ` do not enter.
Sec. IV.C: "Whether the string keeps the body's phase depends on how its own global phase moves
against the body's."  "The body's energy on the string changes the string's phase and the body's
together, so the two part only by what the rest of the string's energy `E_s` does: `E_st_c/ℏ`
per tick, whichever way it turns the phase." -/
theorem keepsAgainstBody_iff (Δs Δb ε θ : ℝ) :
    keepsAgainstBody (Δs + Δb) Δb ε θ ↔ keepsPhase Δs ε :=
  (kept_against_body θ Δs Δb ε).2.2

/-- **A kept phase in mirror image** (Sec. IV.C).  For every `Δ`, `ε` and `φ`, the tick with the
turn `−Δ` keeps the phase `φ` (`keepsPhaseAt`) exactly when the tick with the turn `Δ` keeps the
mirror phase `−φ`: the cosine of the sum is the same, and its sine changes sign on both sides. -/
theorem keepsPhaseAt_neg (Δ ε φ : ℝ) : keepsPhaseAt (-Δ) ε φ ↔ keepsPhaseAt Δ ε (-φ) := by
  unfold keepsPhaseAt
  have e : -φ + Δ = -(φ + -Δ) := by ring
  refine exists_congr fun r => and_congr_right fun _ => ?_
  rw [e, Real.cos_neg, Real.sin_neg, Real.cos_neg, Real.sin_neg]
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨hc, by linarith⟩
  · rintro ⟨hc, hs⟩
    exact ⟨hc, by linarith⟩

/-- **The condition is the same for a turn in either sense** (Sec. IV.C).  For every `Δ` and `ε`,
the tick with the turn `−Δ` keeps some phase (`keepsPhase`) exactly when the tick with the turn
`Δ` keeps some phase: a phase kept by the one is the mirror image of a phase kept by the other
(`keepsPhaseAt_neg`). -/
theorem keepsPhase_neg (Δ ε : ℝ) : keepsPhase (-Δ) ε ↔ keepsPhase Δ ε := by
  constructor
  · rintro ⟨φ, r, hr⟩
    obtain ⟨r', hr'⟩ := (keepsPhaseAt_neg Δ ε φ).1 ⟨r, hr⟩
    exact ⟨-φ, r', hr'⟩
  · rintro ⟨φ, r, hr⟩
    have h1 : keepsPhaseAt Δ ε (-(-φ)) := by rw [neg_neg]; exact ⟨r, hr⟩
    obtain ⟨r', hr'⟩ := (keepsPhaseAt_neg Δ ε (-φ)).2 h1
    exact ⟨-φ, r', hr'⟩

/-- **The phase against the body, whichever way the string's own turn goes** (Sec. IV.C).  For
every `Δ`, `Δs`, `Δb`, `ε` and `θ` such that the string's whole change `Δ` is the body's change
`Δb` and `Δs` in one sense or the other, `Δ = Δb + Δs` or `Δ = Δb − Δs`, the tick keeps the
string's phase against the body's (`keepsAgainstBody`) exactly when `keepsPhase Δs ε` holds,
whatever `Δb` and `θ` are (`keepsAgainstBody_iff`, `keepsPhase_neg`).
Sec. IV.C: "The body's energy on the string changes the string's phase and the body's together,
so the two part only by what the rest of the string's energy `E_s` does: `E_st_c/ℏ` per tick,
whichever way it turns the phase." -/
theorem keepsAgainstBody_either (Δ Δs Δb ε θ : ℝ) (h : Δ = Δb + Δs ∨ Δ = Δb - Δs) :
    keepsAgainstBody Δ Δb ε θ ↔ keepsPhase Δs ε := by
  rcases h with h | h
  · rw [h, add_comm]
    exact keepsAgainstBody_iff Δs Δb ε θ
  · rw [h, show Δb - Δs = -Δs + Δb by ring]
    exact (keepsAgainstBody_iff (-Δs) Δb ε θ).trans (keepsPhase_neg Δs ε)

/-- **One tick, read against the body** (Sec. IV.C).  For `0 < ε < 1` and every `φ`, `θ`, `Δs`
and `Δb`: the tick that changes the string's phase `φ` by `Δs + Δb` and the body's phase `θ` by
`Δb`, and adds to the string the amplitude `ε` at the body's phase after the tick, gives a state
of positive amplitude `r` whose phase is `tickPhase Δs ε (φ − θ)` against the body's new phase
`θ + Δb`.  So one tick takes the string's phase against the body from `φ − θ` to
`tickPhase Δs ε (φ − θ)`, whatever the body's change `Δb` is (`tickPhase_spec`,
`tick_against_body`).
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave
unchanged, as the Lean files also prove." -/
theorem tickPhase_against_body (φ θ Δs Δb ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ r : ℝ, 0 < r ∧
      Real.cos (φ + (Δs + Δb)) + ε * Real.cos (θ + Δb) =
        r * Real.cos (tickPhase Δs ε (φ - θ) + (θ + Δb)) ∧
      Real.sin (φ + (Δs + Δb)) + ε * Real.sin (θ + Δb) =
        r * Real.sin (tickPhase Δs ε (φ - θ) + (θ + Δb)) := by
  obtain ⟨⟨r, hr, hc, hs⟩, -, -⟩ := tickPhase_spec Δs ε (φ - θ) hε hε1
  refine ⟨r, hr, (tick_against_body φ θ Δs Δb ε r (tickPhase Δs ε (φ - θ) + (θ + Δb))).2 ?_⟩
  rw [add_sub_cancel_right]
  exact ⟨hc, hs⟩

/-- **The phase against the body under the ticks, whatever the body's changes are** (Sec. IV.C).
For `0 < ε < 1`, the slip `Δs` is the same at every tick, and `Δb 0, Δb 1, …` is any sequence of
the body's changes, of any size and either sense.  Before tick `k` the body's phase is
`θ₀ + Δb 0 + … + Δb (k−1)`, and the string's phase against it is the `k`-th iterate of
`tickPhase Δs ε` at `ψ₀`.  Tick `k` changes the string's phase by `Δs + Δb k` and the body's by
`Δb k`, and adds to the string the amplitude `ε` at the body's phase after the tick.  The new
state has a positive amplitude, and its phase against the body's new phase is the `(k+1)`-th
iterate (`tickPhase_against_body`).  So the phase against the body follows the repeated tick of
the slip alone, and what the files prove of that repeated tick (`phase_slips`,
`tick_converges`) holds for the string's phase against the body, whatever the body's changes
are.  As in `tick_converges`, the repeated tick takes the phase that one tick gives as the phase
before the next, at unit amplitude each time.
Sec. IV.C: "Where it is smaller, the ticks draw the global phase to a phase that they leave
unchanged, as the Lean files also prove." -/
theorem ticks_against_body (Δs ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (Δb : ℕ → ℝ) (θ₀ ψ₀ : ℝ)
    (k : ℕ) :
    ∃ r : ℝ, 0 < r ∧
      Real.cos (((tickPhase Δs ε)^[k] ψ₀ + (θ₀ + ∑ i ∈ Finset.range k, Δb i)) + (Δs + Δb k)) +
          ε * Real.cos ((θ₀ + ∑ i ∈ Finset.range k, Δb i) + Δb k) =
        r * Real.cos ((tickPhase Δs ε)^[k + 1] ψ₀ + (θ₀ + ∑ i ∈ Finset.range (k + 1), Δb i)) ∧
      Real.sin (((tickPhase Δs ε)^[k] ψ₀ + (θ₀ + ∑ i ∈ Finset.range k, Δb i)) + (Δs + Δb k)) +
          ε * Real.sin ((θ₀ + ∑ i ∈ Finset.range k, Δb i) + Δb k) =
        r * Real.sin ((tickPhase Δs ε)^[k + 1] ψ₀ + (θ₀ + ∑ i ∈ Finset.range (k + 1), Δb i)) := by
  obtain ⟨r, hr, hc, hs⟩ := tickPhase_against_body
    ((tickPhase Δs ε)^[k] ψ₀ + (θ₀ + ∑ i ∈ Finset.range k, Δb i))
    (θ₀ + ∑ i ∈ Finset.range k, Δb i) Δs (Δb k) ε hε hε1
  rw [add_sub_cancel_right] at hc hs
  refine ⟨r, hr, ?_, ?_⟩
  · rw [Function.iterate_succ_apply', Finset.sum_range_succ, ← add_assoc θ₀]
    exact hc
  · rw [Function.iterate_succ_apply', Finset.sum_range_succ, ← add_assoc θ₀]
    exact hs

end Law

namespace Reg

variable (R : Reg)

/-- `ln 2 < 1`, since `2 < e`. -/
theorem ln2_lt_one : R.ln2 < 1 := by
  have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
  rw [R.ln2_def]; linarith

/-- **The scale**, Eq. (f): `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`. -/
noncomputable def a0 : ℝ := (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * R.RL)

lemma a0_pos : 0 < R.a0 := by
  reg_facts R
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hRL := R.RL_pos
  unfold a0
  exact div_pos (mul_pos hm (by positivity)) (by positivity)

/-- **Only the product `Lℓ_c` enters `a₀`**: `a₀ = (1 − ln 2)πc²/(ln 2 · Lℓ_c)` with
`R_Λ = Lℓ_c/2π`, so pinning `ℓ_c` pins only the ratio of `R_Λ` to `L` (Table II). -/
theorem a0_depends_on_product : R.a0 = (1 - R.ln2) * R.pi * R.c ^ 2 / (R.ln2 * (R.L * R.ℓc)) := by
  reg_facts R
  unfold a0 RL
  field_simp

/-- **Eq. (newton) at `g_N`**: with Jacobson's `G` and `I1` for the Unruh temperature `T_N` of
`g_N = GM/r²`, the body's energy is two Landauer energies at `T_N` per string of the sphere on
average, `Mc² = 2N_s k_BT_N ln 2` (`Reg.newton` gives the same with the pull of the solution). -/
theorem newton_share (G M r T : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I1 : R.kB * T = R.ℏ / (R.La (G * M / r ^ 2) * R.tc)) :
    M * R.c ^ 2 = 2 * R.Ns r * (R.kB * T * R.ln2) := by
  reg_facts R
  have hr' := hr.ne'
  have hG := (R.G_eq G hJ).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * M / r ^ 2 := by positivity
  have hT := R.T_Unruh _ T hgN I1
  rw [show 2 * R.Ns r * (R.kB * T * R.ln2) = 2 * R.Ns r * (R.kB * T) * R.ln2 by ring, hT,
    R.bulk_counts r, hG]
  unfold n
  field_simp

/-- **Eq. (share): fewer carriers, the same energy, a higher temperature.**  The body's energy is
two Landauer energies at the Unruh temperature `T_N` of `g_N` per string of the sphere's `N_s`
strings on average (`hN`, Eq. (newton) at `g_N`, `newton_share`), and it is held by the fraction
`b` of them at the temperature `T_a` of the acceleration `a`, two Landauer energies each on average
(`hS`, the body's
energy held by the carriers, `Law.share_of_equipartition`).  With `I1` for both temperatures,
`a = g_N/b`. -/
theorem share_acceleration (M Ns b TN Ta gN a : ℝ) (hNs : 0 < Ns) (hb : 0 < b) (hgN : 0 < gN)
    (ha : 0 < a)
    (hN : M * R.c ^ 2 = 2 * Ns * (R.kB * TN * R.ln2))
    (hS : M * R.c ^ 2 = 2 * (b * Ns) * (R.kB * Ta * R.ln2))
    (I1N : R.kB * TN = R.ℏ / (R.La gN * R.tc)) (I1a : R.kB * Ta = R.ℏ / (R.La a * R.tc)) :
    a = gN / b := by
  reg_facts R
  have h1 := R.T_Unruh gN TN hgN I1N
  have h2 := R.T_Unruh a Ta ha I1a
  have e := hN.symm.trans hS
  rw [h1, h2] at e
  have hK : 0 < 2 * Ns * (R.ℏ / (2 * R.pi * R.c) * R.ln2) := by positivity
  have e1 : 2 * Ns * (R.ℏ * gN / (2 * R.pi * R.c) * R.ln2)
      = gN * (2 * Ns * (R.ℏ / (2 * R.pi * R.c) * R.ln2)) := by ring
  have e2 : 2 * (b * Ns) * (R.ℏ * a / (2 * R.pi * R.c) * R.ln2)
      = (b * a) * (2 * Ns * (R.ℏ / (2 * R.pi * R.c) * R.ln2)) := by ring
  have key : gN = b * a := by
    apply mul_right_cancel₀ hK.ne'
    rw [← e1, ← e2]
    exact e
  rw [key, mul_comm b a, mul_div_assoc, div_self hb.ne', mul_one]

/-- **The strings' mean energy from the Gibbs distribution** (Sec. IV.E).  A string's energy is
the same for all its states and differs from string to string with the mass the string holds, from
zero up.  The strings' energies are spread at the horizon's temperature and do not change
(`hGibbs`, thermodynamics), so their mean `ε_s` is the mean of the Gibbs distribution at that
temperature, which is the thermal energy (`Law.gibbsMean_eq`).  The horizon's period is the lap
(`I1`), so `ε_s = k_BT_dS = ℏ/(Lt_c)`: on average a string's global phase decreases by one
radian in a lap. -/
theorem string_energy (εs T : ℝ) (hGibbs : εs = Law.gibbsMean (R.kB * T))
    (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) : εs = R.kB * T := by
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have hpos : 0 < R.kB * T := by rw [I1]; positivity
  rw [hGibbs, Law.gibbsMean_eq _ hpos]

/-- **What reaches a string**, Eqs. (E), (u) and (f).  The body's energy per string, two Landauer
energies at the Unruh temperature `T_N` of `g_N` (`I1N`), counted in units of the matter a string
holds on average, `u = (1 − ln 2)ε_s`, with the strings' mean energy `ε_s = k_BT_dS` (`hεs`, from
`string_energy`) and the
Gibbons–Hawking temperature (`I1dS`), is `f = g_N/a₀`. -/
theorem fill_fraction (gN TN TdS εs : ℝ) (hgN : 0 < gN)
    (I1N : R.kB * TN = R.ℏ / (R.La gN * R.tc)) (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (hεs : εs = R.kB * TdS) :
    2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs) = gN / R.a0 := by
  reg_facts R
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hm' := hm.ne'
  have hRL := R.RL_pos.ne'
  have h1 := R.T_Unruh gN TN hgN I1N
  have h2 := (R.T_dS TdS I1dS).2
  rw [hεs, h2, show 2 * R.kB * TN * R.ln2 = 2 * (R.kB * TN) * R.ln2 by ring, h1]
  unfold a0
  field_simp

/-- **The threshold from the strings' energies** (Sec. IV.C).  With the strings' energies spread at
the horizon's temperature (`hspread`: `above y` is the fraction of the strings whose energy
exceeds `y`), and with the horizon's thermal energy `k_BT_dS = ℏ/(Lt_c)` (`I1dS`), the fraction
of the strings whose energy exceeds `x k_BT_dS` is `e^{−x}`.  A free tick turns the global phase
of a string of energy `E` by `Et_c/ℏ`, and a share of amplitude `h` adds the amplitude `h/L` per
tick.  The strings whose phase holds against the share are those of energy at most the threshold
`(ℏ/t_c) arcsin(h/L)` and those in the ranges about the whole turns (`phase_all_turns`).  The
threshold is `hℏ/(Lt_c)` to leading order in `1/L` (`threshold_bounds`), and the ranges about
the whole turns hold a fraction of the strings below `e^{−3πL/2}` (`Law.whole_turns_bounds`).
At that order, with `x = h`, the strings whose energy exceeds the threshold are the fraction
`e^{−h}`: the threshold, in units of the amplitude of one whole qubit, is exponential with mean
one.  The energies that enter the rule are the energies `E_s`, the rest of each string's energy
beyond the body's, which set the slip against the body (`Main.slip_against_body`).
Sec. IV.C: "Apart from the body's energy, the strings of the sphere are like all other strings, so the energies `E_s` are spread over them at the horizon's temperature
(Sec. IV.E), by the principle of maximum entropy, the fraction `e^{−x}` of them above
`x k_BT_dS`."  "So the fraction `e^{−h}` of the strings have `E_s > h k_BT_dS`, and those
strings miss the body."  `fraction_above_turn` states the spread in turns per tick, as the exact
fraction takes it. -/
theorem threshold_from_spread (TdS : ℝ) (above : ℝ → ℝ)
    (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (hspread : ∀ y, 0 ≤ y → above y = Law.gibbsAbove (R.kB * TdS) y) :
    ∀ x, 0 ≤ x → above (x * (R.ℏ / (R.L * R.tc))) = Real.exp (-x) := by
  intro x hx
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have hθ : 0 < R.ℏ / (R.L * R.tc) := by positivity
  rw [hspread _ (mul_nonneg hx hθ.le), I1dS, Law.gibbsAbove_eq _ _ hθ, neg_div,
    mul_div_cancel_right₀ _ hθ.ne']

/-- **The strings whose phase holds, in energies** (Sec. IV.C).  A free tick turns the global
phase of a string of energy `E ≥ 0` by `Δ = Et_c/ℏ` (Sec. II's definition of energy), and it
adds to the string the amplitude `ε` of a body's share, `0 < ε < 1`.  The first part: the
string's phase holds (`Law.keepsPhase`) exactly when the turn lies within `arcsin ε` of a whole
number of turns, `|Et_c/ℏ − 2πk| ≤ arcsin ε` for some `k = 0, 1, 2, …`
(`Law.steady_phase_iff_turns_nat`).  The second part says it in energies (`Law.phase_ranges`):
`E ≤ (ℏ/t_c) arcsin ε`, the first range, with the threshold `E_thr = (ℏ/t_c) arcsin ε`, or `E`
within `E_thr` of `2πkℏ/t_c` for a whole number `k ≥ 1`, written `k + 1`. -/
theorem phase_all_turns (ε E : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hE : 0 ≤ E) :
    (Law.keepsPhase (E * R.tc / R.ℏ) ε ↔
      ∃ k : ℕ, |E * R.tc / R.ℏ - 2 * Real.pi * k| ≤ Real.arcsin ε) ∧
    (Law.keepsPhase (E * R.tc / R.ℏ) ε ↔
      E ≤ R.ℏ / R.tc * Real.arcsin ε ∨
      ∃ k : ℕ, R.ℏ / R.tc * (2 * Real.pi * (k + 1) - Real.arcsin ε) ≤ E ∧
        E ≤ R.ℏ / R.tc * (2 * Real.pi * (k + 1) + Real.arcsin ε)) := by
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have hu : 0 < R.ℏ / R.tc := by positivity
  have hΔ0 : 0 ≤ E * R.tc / R.ℏ := by positivity
  refine ⟨Law.steady_phase_iff_turns_nat _ ε hε hε1 hΔ0, ?_⟩
  have h := Law.phase_ranges (R.ℏ / R.tc) ε E hu hε hε1 hE
  rwa [div_div_eq_mul_div] at h

open Filter Topology in
/-- **The tick's action on the phase of a string of the register** (Sec. IV.C).  A free tick
turns the global phase of a string of energy `E` by `Δ = Et_c/ℏ` (Sec. II's definition of
energy), and it adds to the string the amplitude `h/L` of a share of amplitude `h`, `0 < h < L`.
The first part: where the added amplitude is smaller than the size of the sine of the turn, `h/L < |sin Δ|`, the tick keeps no phase
(`Law.keepsPhaseAt`), and for every phase `φ` the phase after the tick (`Law.tickPhase`)
differs from `φ` by an angle whose sine has the sign of `sin Δ` (`Law.phase_slips`,
`Law.tickPhase_spec`).  So the phase moves in the same sense at every tick.  The second part,
inside the range: where `|sin Δ| < h/L` and `cos Δ > 0`, the tick keeps the phase
`φ₀ = arcsin(L sin Δ/h)` (`Law.kept_phases`), and from every phase strictly between `−π − φ₀`
and `π − φ₀` the repeated tick converges to `φ₀` (`Law.tick_converges`).  Neither part treats the edge of the range,
`|sin Δ| = h/L` with `cos Δ > 0`, where the tick keeps a phase
(`Law.steady_phase_all_turns`, `Law.keepsPhase_iff_kept`) and no convergence is stated, or the turns within `arcsin(h/L)` of an odd number of half turns, where `|sin Δ| ≤ h/L` and `cos Δ < 0`.  At the turns within `arcsin(h/L)` of an odd number of half turns, which are outside the range, the tick keeps no phase either (`Law.keepsPhase_iff_kept`), and no statement gives the sense in which the phase moves.  Of the first sentence quoted below, the files prove that the tick keeps no phase at any turn outside the range, and that the phase moves in the same sense at every tick where `h/L < |sin Δ|`. Sec. IV.C: "Where the slip per tick is larger, the global phase slips at every tick and the
string takes no phase from the body."  "Where it is smaller, the ticks draw the global phase to
a phase that they leave unchanged, as the Lean files also prove." -/
theorem phase_under_tick (h : ℝ) (hh0 : 0 < h) (hhL : h < R.L) (E : ℝ) :
    (h / R.L < |Real.sin (E * R.tc / R.ℏ)| →
      ∀ φ : ℝ, ¬ Law.keepsPhaseAt (E * R.tc / R.ℏ) (h / R.L) φ ∧
        0 < Real.sin (E * R.tc / R.ℏ) *
          Real.sin (Law.tickPhase (E * R.tc / R.ℏ) (h / R.L) φ - φ)) ∧
    (|Real.sin (E * R.tc / R.ℏ)| < h / R.L → 0 < Real.cos (E * R.tc / R.ℏ) →
      ∃ φ₀ : ℝ, Law.keepsPhaseAt (E * R.tc / R.ℏ) (h / R.L) φ₀ ∧
        ∀ φ : ℝ, -Real.pi - φ₀ < φ → φ < Real.pi - φ₀ →
          Tendsto (fun k => (Law.tickPhase (E * R.tc / R.ℏ) (h / R.L))^[k] φ) atTop (𝓝 φ₀)) := by
  have hL := R.L_pos
  have hε : 0 < h / R.L := div_pos hh0 hL
  have hε1 : h / R.L < 1 := by rw [div_lt_one hL]; exact hhL
  refine ⟨fun hout φ => ?_, fun hin hcos => ?_⟩
  · obtain ⟨-, -, hnk, hturn⟩ := Law.phase_slips _ _ hε hout φ
    obtain ⟨⟨r, hr, hc, hs⟩, -, -⟩ := Law.tickPhase_spec (E * R.tc / R.ℏ) (h / R.L) φ hε hε1
    exact ⟨hnk, hturn r _ hr hc hs⟩
  · set φ₀ := Real.arcsin (Real.sin (E * R.tc / R.ℏ) / (h / R.L)) with hφ₀
    refine ⟨φ₀, ?_, fun φ h1 h2 => Law.tick_converges _ _ φ₀ hε hε1 hin hcos hφ₀ φ h1 h2⟩
    exact (Law.kept_phases _ _ φ₀ hε hε1 hin hcos hφ₀ φ₀).2 ⟨0, Or.inl (by push_cast; ring)⟩

/-- **The spread of the strings' energies, in turns per tick** (Sec. IV.C).  With the strings'
energies spread at the horizon's temperature (`hspread`) and `k_BT_dS = ℏ/(Lt_c)` (`I1dS`), the
strings whose energy exceeds `(ℏ/t_c)x`, those that a free tick turns by more than `x` radians,
are the fraction `e^{−Lx}` of the strings, for every `x ≥ 0` (`threshold_from_spread` at
`Lx`). -/
theorem fraction_above_turn (TdS : ℝ) (above : ℝ → ℝ)
    (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (hspread : ∀ y, 0 ≤ y → above y = Law.gibbsAbove (R.kB * TdS) y) :
    ∀ x, 0 ≤ x → above (R.ℏ / R.tc * x) = Real.exp (-(R.L * x)) := by
  intro x hx
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have e : R.ℏ / R.tc * x = R.L * x * (R.ℏ / (R.L * R.tc)) := by field_simp
  rw [e]
  exact R.threshold_from_spread TdS above I1dS hspread _ (mul_nonneg R.L_pos.le hx)

open MeasureTheory in
/-- **The carriers' fraction from the spread, over every turn** (Sec. IV.C).  `μ` is a
distribution of the strings' energies, a probability measure, with the fraction `above x` of the
strings above each energy `x ≥ 0` (`hμ`), and the energies are spread at the horizon's
temperature (`hspread`), with `k_BT_dS = ℏ/(Lt_c)` (`I1dS`).  Each tick adds the amplitude `ε`,
`0 < ε < 1`.  Then the strings of energy `E ≥ 0` whose phase holds, at the turn `Et_c/ℏ` of
their free tick, are the fraction
`(1 − e^{−L arcsin ε})(1 + (e^{L arcsin ε} + 1)/(e^{2πL} − 1))` of the strings
(`Law.phase_fraction` with `u = ℏ/t_c`, `fraction_above_turn`). -/
theorem carriers_fraction (TdS ε : ℝ) (above : ℝ → ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (hspread : ∀ y, 0 ≤ y → above y = Law.gibbsAbove (R.kB * TdS) y)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) :
    (μ {E : ℝ | 0 ≤ E ∧ Law.keepsPhase (E * R.tc / R.ℏ) ε}).toReal =
      (1 - Real.exp (-(R.L * Real.arcsin ε))) *
        (1 + (Real.exp (R.L * Real.arcsin ε) + 1) / (Real.exp (2 * Real.pi * R.L) - 1)) := by
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have hu : 0 < R.ℏ / R.tc := by positivity
  have hset : {E : ℝ | 0 ≤ E ∧ Law.keepsPhase (E * R.tc / R.ℏ) ε} =
      {E : ℝ | 0 ≤ E ∧ Law.keepsPhase (E / (R.ℏ / R.tc)) ε} := by
    ext E
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, div_div_eq_mul_div]
  rw [hset]
  refine Law.phase_fraction (R.ℏ / R.tc) R.L ε hu R.L_pos hε hε1 μ (fun x hx => ?_)
  rw [hμ _ (mul_nonneg hu.le hx)]
  exact R.fraction_above_turn TdS above I1dS hspread x hx

open MeasureTheory in
/-- **The rule of the phase fixes the carriers' fraction** (Sec. IV.C).  The rule has the form
of `Sources.P1.carriers_hold_phase` with the condition of the slip, `Law.keepsPhase`, in place of
the condition against the body, which `Law.keepsAgainstBody_either` shows to be the same,
whichever way the string's own turn goes.  Whatever distribution `μ` of the strings' energies, a
probability measure, has the fraction `above x` of the strings above each energy `x ≥ 0`, `b` is
the fraction that `μ` gives to the strings of energy `E ≥ 0` whose phase holds against the
amplitude `ε` that a tick adds (`Law.keepsPhase`).  The phase is taken at the turn `Et_c/ℏ` of
the string's free tick, whatever that turn is.  With the energies spread at the horizon's
temperature (`hspread`), `k_BT_dS = ℏ/(Lt_c)` (`I1dS`) and `0 < ε < 1`, the rule holds exactly
when `b = (1 − e^{−L arcsin ε})(1 + (e^{L arcsin ε} + 1)/(e^{2πL} − 1))`.  A distribution with
these fractions exists (`Law.gibbs_measure_exists`), so the rule fixes `b`; and every such
distribution gives the strings whose phase holds that fraction (`carriers_fraction`), so the
rule can be met. -/
theorem carriers_rule_iff (TdS b ε : ℝ) (above : ℝ → ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (hspread : ∀ y, 0 ≤ y → above y = Law.gibbsAbove (R.kB * TdS) y) :
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) →
      b = (μ {E : ℝ | 0 ≤ E ∧ Law.keepsPhase (E * R.tc / R.ℏ) ε}).toReal) ↔
    b = (1 - Real.exp (-(R.L * Real.arcsin ε))) *
      (1 + (Real.exp (R.L * Real.arcsin ε) + 1) / (Real.exp (2 * Real.pi * R.L) - 1)) := by
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have hθ : 0 < R.kB * TdS := by rw [I1dS]; positivity
  constructor
  · intro hrule
    -- a distribution with the fractions `above` exists, and the rule gives `b` for it
    obtain ⟨μ, hμ, hμtail⟩ := Law.gibbs_measure_exists (R.kB * TdS) hθ
    have hμ' : ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x := fun x hx => by
      rw [hμtail x hx, hspread x hx]
    rw [hrule μ hμ', R.carriers_fraction TdS ε above hε hε1 I1dS hspread μ hμ']
  · intro hb μ _ hμ
    rw [hb, R.carriers_fraction TdS ε above hε hε1 I1dS hspread μ hμ]

/-- **The first range's threshold between its bounds** (Sec. IV.C).  With the horizon's thermal
energy `k_BT_dS = ℏ/(Lt_c)` (`I1dS`) and `0 ≤ h < L`, the threshold
`E_thr = (ℏ/t_c) arcsin(h/L)` lies between `h k_BT_dS` and `h k_BT_dS/√(1 − (h/L)²)`
(`Law.exponent_bounds`): it is `h k_BT_dS` to leading order in `1/L`.  The threshold is the
upper end of the first range of the energies at which a string's phase holds against a share of
amplitude `h` (`phase_all_turns`). -/
theorem threshold_bounds (TdS h : ℝ) (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc)) (hh0 : 0 ≤ h)
    (hhL : h < R.L) :
    h * (R.kB * TdS) ≤ R.ℏ / R.tc * Real.arcsin (h / R.L) ∧
    R.ℏ / R.tc * Real.arcsin (h / R.L) ≤
      h * (R.kB * TdS) / Real.sqrt (1 - (h / R.L) ^ 2) := by
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have hθ : 0 < R.ℏ / (R.L * R.tc) := by positivity
  obtain ⟨h1, h2⟩ := Law.exponent_bounds R.L h R.L_pos hh0 hhL
  have e : R.ℏ / R.tc * Real.arcsin (h / R.L) =
      R.L * Real.arcsin (h / R.L) * (R.ℏ / (R.L * R.tc)) := by field_simp
  rw [I1dS, e]
  constructor
  · exact mul_le_mul_of_nonneg_right h1 hθ.le
  · calc R.L * Real.arcsin (h / R.L) * (R.ℏ / (R.L * R.tc))
        ≤ h / Real.sqrt (1 - (h / R.L) ^ 2) * (R.ℏ / (R.L * R.tc)) :=
          mul_le_mul_of_nonneg_right h2 hθ.le
      _ = h * (R.ℏ / (R.L * R.tc)) / Real.sqrt (1 - (h / R.L) ^ 2) := by ring

open MeasureTheory in
/-- **The hypotheses of the carrying rule can hold at once** (Sec. IV.C), for every register,
every amplitude `0 < h < L` of a body's share, every change `Δb` of the body's phase in a tick,
every phase `θ` of the body and every choice `back` of the strings whose own turn goes the other
way: there are an amplitude `ε` per tick with `Lε = h` (the share's `L` equal parts,
`Sources.P1.share_in_parts`), a temperature with `k_BT_dS = ℏ/(Lt_c)`, and a spread of the
strings' energies at that temperature with its mean (`Sources.Thermo.energies_thermal`).  There
is a change of the global phase per free tick for every string, `turn E_s = Δb − E_st_c/ℏ` where
`back E_s` holds and `turn E_s = Δb + E_st_c/ℏ` where it does not, so that `turn` meets
`Sources.P1.phase_with_body`.  There are also a distribution of the energies, a probability
measure, with the fractions of that spread above each energy (`Law.gibbs_measure_exists`), and a
fraction `b` that meets the rule of the phase against the body for every such distribution
(`Sources.P1.carriers_hold_phase`, by `Law.keepsAgainstBody_either` and `carriers_rule_iff`).  So
`Main.carriers_exact` does not hold vacuously, and the rule, which is stated for every
distribution with those fractions, is stated for at least one. -/
theorem carriers_model (h : ℝ) (hh0 : 0 < h) (hhL : h < R.L) (Δb θ : ℝ) (back : ℝ → Bool) :
    ∃ (ε b TdS εs : ℝ) (above : ℝ → ℝ) (turn : ℝ → ℝ),
      R.L * ε = h ∧ R.kB * TdS = R.ℏ / (R.L * R.tc) ∧ εs = Law.gibbsMean (R.kB * TdS) ∧
      (∀ y, 0 ≤ y → above y = Law.gibbsAbove (R.kB * TdS) y) ∧
      (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
        ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) ∧
      (∀ Es : ℝ, turn Es = if back Es then Δb - Es * R.tc / R.ℏ else Δb + Es * R.tc / R.ℏ) ∧
      (∀ Es : ℝ, turn Es = Δb + Es * R.tc / R.ℏ ∨ turn Es = Δb - Es * R.tc / R.ℏ) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
        (∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) →
        b = (μ {Es : ℝ | 0 ≤ Es ∧ Law.keepsAgainstBody (turn Es) Δb ε θ}).toReal := by
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have htc' := htc.ne'
  have hε0 : 0 < h / R.L := div_pos hh0 R.L_pos
  have hε1 : h / R.L < 1 := (div_lt_one R.L_pos).2 hhL
  obtain ⟨TdS, hTdS⟩ : ∃ T : ℝ, T = R.ℏ / (R.L * R.tc) / R.kB := ⟨_, rfl⟩
  have I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc) := by rw [hTdS]; field_simp
  have hθ : 0 < R.kB * TdS := by rw [I1dS]; positivity
  -- each string's own turn goes in the sense that `back` chooses
  set turn : ℝ → ℝ := fun Es => if back Es then Δb - Es * R.tc / R.ℏ else Δb + Es * R.tc / R.ℏ
    with hturn
  have hwith : ∀ Es : ℝ, turn Es = Δb + Es * R.tc / R.ℏ ∨ turn Es = Δb - Es * R.tc / R.ℏ := by
    intro Es
    by_cases hb : back Es = true
    · right; simp [hturn, hb]
    · left; simp [hturn, hb]
  -- the condition against the body is the condition of the slip alone
  have hset : {Es : ℝ | 0 ≤ Es ∧ Law.keepsAgainstBody (turn Es) Δb (h / R.L) θ} =
      {E : ℝ | 0 ≤ E ∧ Law.keepsPhase (E * R.tc / R.ℏ) (h / R.L)} := by
    ext Es
    simp only [Set.mem_ofPred_eq,
      Law.keepsAgainstBody_either (turn Es) (Es * R.tc / R.ℏ) Δb (h / R.L) θ (hwith Es)]
  refine ⟨h / R.L, (1 - Real.exp (-(R.L * Real.arcsin (h / R.L)))) *
      (1 + (Real.exp (R.L * Real.arcsin (h / R.L)) + 1) / (Real.exp (2 * Real.pi * R.L) - 1)),
    TdS, Law.gibbsMean (R.kB * TdS), fun y => Law.gibbsAbove (R.kB * TdS) y,
    turn, by field_simp, I1dS,
    rfl, fun _ _ => rfl, Law.gibbs_measure_exists (R.kB * TdS) hθ, fun _ => rfl, hwith, ?_⟩
  intro μ _ hμ
  rw [hset]
  exact (R.carriers_rule_iff TdS _ (h / R.L) (fun y => Law.gibbsAbove (R.kB * TdS) y) hε0 hε1
    I1dS (fun _ _ => rfl)).2 rfl μ hμ

/-- **The law**, Eq. (law), at leading order in `1/L`.  The threshold's survival function is
`e^{−x}` (`hME`: the string's slip per tick against the turn per tick, with the Gibbs spread,
`threshold_from_spread`), so the strings whose threshold
lies below the amplitude `√(g_N/a₀)` are the fraction `b = 1 − e^{−√(g_N/a₀)}` (`hb`, Eq. (b),
the leading order of the exact fraction, `Law.fraction_leading_order`), and with
`a = g_N/b` (`share_acceleration`) the relation follows.  `Law.law_bounds` gives the bounds on
`a` with the exact fraction. -/
theorem law (gN a b : ℝ) (surv : ℝ → ℝ) (hME : ∀ x, 0 ≤ x → surv x = Real.exp (-x))
    (hb : b = 1 - surv (Real.sqrt (gN / R.a0))) (hab : a = gN / b) :
    a = gN / (1 - Real.exp (-Real.sqrt (gN / R.a0))) := by
  rw [hab, hb, hME _ (Real.sqrt_nonneg _)]

/-- **The scale goes as the square of the threshold's mean** (Sec. IV.C).  Were the threshold
exponential with mean `μ` instead of one qubit (`hME`), the law would keep its form with the scale
`μ²a₀`; so the measured scale fixes `μ` (`Numerics.threshold_mean_from_data`). -/
theorem law_scale_mean (gN a b μ : ℝ) (hμ : 0 < μ) (surv : ℝ → ℝ)
    (hME : ∀ x, 0 ≤ x → surv x = Real.exp (-x / μ))
    (hb : b = 1 - surv (Real.sqrt (gN / R.a0))) (hab : a = gN / b) :
    a = gN / (1 - Real.exp (-Real.sqrt (gN / (μ ^ 2 * R.a0)))) := by
  have hs : Real.sqrt (gN / (μ ^ 2 * R.a0)) = Real.sqrt (gN / R.a0) / μ := by
    rw [show gN / (μ ^ 2 * R.a0) = gN / R.a0 / μ ^ 2 by rw [div_div, mul_comm],
      Real.sqrt_div' _ (sq_nonneg μ), Real.sqrt_sq hμ.le]
  rw [hab, hb, hME _ (Real.sqrt_nonneg _), hs, neg_div]

/-- **The scale and `Λ` at every epoch** (Sec. VI, item 5).  With Jacobson's `G` (`hJ`, which
gives `G = c³ℓ_c²/(πℏ ln 2)`, `Reg.G_eq`) and `Λ = 3/R_Λ²` (`hΛ`), the scale is a fixed fraction of
the Planck acceleration, `a₀ = (1 − ln 2)√π/((ln 2)^{3/2} L) · √(c⁷/ℏG)`, and
`Λ = 12πc³/(L²ℏG ln 2)`.  The same formula with another value `G'` of Newton's constant gives twice
the scale only if `G' = G/4`.  Lean has no epochs: the paper applies the formula at every epoch
with that epoch's `G`, since `L` and the split of a string's mean energy do not change and the units
fix `c` and `ℏ`. -/
theorem scale_over_time (G Λ : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hΛ : Λ = 3 / R.RL ^ 2) :
    R.a0 = (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
        Real.sqrt (R.c ^ 7 / (R.ℏ * G)) ∧
    Λ = 12 * R.pi * R.c ^ 3 / (R.L ^ 2 * R.ℏ * G * R.ln2) ∧
    ∀ G' : ℝ, 0 < G' →
      (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
        Real.sqrt (R.c ^ 7 / (R.ℏ * G')) = 2 * R.a0 → G' = G / 4 := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hsp : Real.sqrt R.pi ^ 2 = R.pi := Real.sq_sqrt R.pi_pos.le
  have hsl : Real.sqrt R.ln2 ^ 2 = R.ln2 := Real.sq_sqrt R.ln2_pos.le
  have hs0 : 0 < Real.sqrt R.pi := Real.sqrt_pos.mpr R.pi_pos
  have ht0 : 0 < Real.sqrt R.ln2 := Real.sqrt_pos.mpr R.ln2_pos
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hkey : R.c ^ 7 / (R.ℏ * G) =
      (Real.sqrt R.pi * Real.sqrt R.ln2 * R.c ^ 2 / R.ℓc) ^ 2 := by
    rw [hG, div_pow, mul_pow, mul_pow, hsp, hsl]
    field_simp
  have hsqrt : Real.sqrt (R.c ^ 7 / (R.ℏ * G)) =
      Real.sqrt R.pi * Real.sqrt R.ln2 * R.c ^ 2 / R.ℓc := by
    rw [hkey, Real.sqrt_sq (by positivity)]
  have ha0 : R.a0 = (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
      Real.sqrt (R.c ^ 7 / (R.ℏ * G)) := by
    rw [hsqrt]
    unfold a0 RL
    have e : (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
        (Real.sqrt R.pi * Real.sqrt R.ln2 * R.c ^ 2 / R.ℓc)
        = (1 - R.ln2) * (Real.sqrt R.pi ^ 2) * R.c ^ 2 / (R.ln2 * R.L * R.ℓc) := by
      field_simp
    rw [e, hsp]
    field_simp
  refine ⟨ha0, ?_, ?_⟩
  · rw [hΛ, hG]
    unfold RL
    field_simp
    ring
  · intro G' hG' h
    rw [ha0] at h
    have hK : 0 < (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) := by
      positivity
    have h2 : Real.sqrt (R.c ^ 7 / (R.ℏ * G')) = 2 * Real.sqrt (R.c ^ 7 / (R.ℏ * G)) := by
      have := h
      rw [mul_left_comm] at this
      exact mul_left_cancel₀ hK.ne' this
    have h3 : R.c ^ 7 / (R.ℏ * G') = 4 * (R.c ^ 7 / (R.ℏ * G)) := by
      have e1 := Real.sq_sqrt (show 0 ≤ R.c ^ 7 / (R.ℏ * G') by positivity)
      have e2 := Real.sq_sqrt (show 0 ≤ R.c ^ 7 / (R.ℏ * G) by positivity)
      rw [← e1, ← e2, h2]
      ring
    field_simp at h3
    have hc7 : 0 < R.c ^ 7 := by positivity
    nlinarith [h3, hc7, R.ℏ_pos, hG', hGpos, mul_pos hc7 R.ℏ_pos]

/-- **`Λ` from the scale** (Sec. V): `R_Λ = (1 − ln 2)c²/(2 ln 2 a₀)`, so with `Λ = 3/R_Λ²`,
`Λ = 12(ln 2)² a₀²/((1 − ln 2)² c⁴)`: the coincidence of the two scales is a fixed relation. -/
theorem Lambda_from_a0 (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.RL = (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * R.a0) ∧
    Λ = 12 * R.ln2 ^ 2 * R.a0 ^ 2 / ((1 - R.ln2) ^ 2 * R.c ^ 4) := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hm' := hm.ne'
  constructor
  · unfold a0; field_simp
  · rw [(R.deSitter G Λ).1 hdS]
    unfold a0
    field_simp
    ring

end Reg

namespace Law

/-- **Near the body** (Sec. IV.C).  With `x = e^{−h}`, `a/g_N − 1 = x/(1 − x)`, which exceeds `x`,
and `a − g_N(1 + x) = g_N x²/(1 − x)`: `a = g_N[1 + e^{−h} + O(e^{−2h})]`, so Newton's law returns
exponentially. -/
theorem near_limit (gN h : ℝ) (hgN : 0 < gN) (hh : 0 < h) :
    gN / (1 - Real.exp (-h)) - gN = gN * (Real.exp (-h) / (1 - Real.exp (-h))) ∧
    gN * Real.exp (-h) < gN / (1 - Real.exp (-h)) - gN ∧
    gN / (1 - Real.exp (-h)) - gN * (1 + Real.exp (-h)) =
      gN * Real.exp (-h) ^ 2 / (1 - Real.exp (-h)) := by
  have hx0 : 0 < Real.exp (-h) := Real.exp_pos _
  have hx1 := exp_neg_lt_one hh
  have h1x : 0 < 1 - Real.exp (-h) := by linarith
  have h1x' := h1x.ne'
  have e : gN / (1 - Real.exp (-h)) - gN = gN * (Real.exp (-h) / (1 - Real.exp (-h))) := by
    rw [mul_div_assoc', eq_div_iff h1x', sub_mul, div_mul_cancel₀ gN h1x']
    ring
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    apply mul_lt_mul_of_pos_left _ hgN
    rw [lt_div_iff₀ h1x]
    nlinarith [mul_pos hx0 hx0]
  · rw [eq_div_iff h1x', sub_mul, div_mul_cancel₀ gN h1x']
    ring

/-- **Far from the body**, Eq. (deep).  With `g_N = a₀h²`, so that `√(a₀g_N) = a₀h` and
`g_N/2 = a₀h²/2`, and `0 < h ≤ 1/2`, the acceleration `a = a₀h²/(1 − e^{−h})` lies within
`a₀h³ = g_N^{3/2}/√a₀` of `√(a₀g_N) + g_N/2`: the deep law `a → √(a₀g_N)`, with the next term
`g_N/2`. -/
theorem deep_limit (a0 h : ℝ) (ha0 : 0 < a0) (hh : 0 < h) (hh2 : h ≤ 1 / 2) :
    a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3 ≤ a0 * h ^ 2 / (1 - Real.exp (-h)) ∧
    a0 * h ^ 2 / (1 - Real.exp (-h)) ≤ a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3 := by
  obtain ⟨t1, t2⟩ := exp_neg_taylor hh.le (by linarith)
  have hD : 0 < 1 - Real.exp (-h) := by linarith [exp_neg_lt_one hh]
  have hh4 : 0 < a0 * h ^ 4 := by positivity
  constructor
  · rw [le_div_iff₀ hD]
    have hc : 0 ≤ a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3 := by
      have : 0 ≤ 1 + h / 2 - h ^ 2 := by nlinarith
      have e : a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3 = a0 * h * (1 + h / 2 - h ^ 2) := by ring
      rw [e]; positivity
    have key : a0 * h ^ 2 - (a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3) *
        (h - h ^ 2 / 2 + 2 / 9 * h ^ 3) = a0 * h ^ 4 * (37 / 36 - 11 / 18 * h + 2 / 9 * h ^ 2) := by
      ring
    have hq : 0 < 37 / 36 - 11 / 18 * h + 2 / 9 * h ^ 2 := by nlinarith
    calc (a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3) * (1 - Real.exp (-h))
        ≤ (a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3) * (h - h ^ 2 / 2 + 2 / 9 * h ^ 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
      _ ≤ a0 * h ^ 2 := by nlinarith [mul_pos hh4 hq]
  · rw [div_le_iff₀ hD]
    have key : (a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3) * (h - h ^ 2 / 2 - 2 / 9 * h ^ 3) -
        a0 * h ^ 2 = a0 * h ^ 4 * (19 / 36 - 11 / 18 * h - 2 / 9 * h ^ 2) := by
      ring
    have hq : 0 < 19 / 36 - 11 / 18 * h - 2 / 9 * h ^ 2 := by nlinarith
    calc a0 * h ^ 2
        ≤ (a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3) * (h - h ^ 2 / 2 - 2 / 9 * h ^ 3) := by
          nlinarith [mul_pos hh4 hq]
      _ ≤ (a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3) * (1 - Real.exp (-h)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **A classical share** (Sec. IV.C).  If a string's share of the body were classical, the string
would hold a record of the body with the probability `f = g_N/a₀` (`hb`), in place of the
amplitude.  Far from the body, where `f ≤ 1`, the carriers would be the fraction `b = f`, and
`a = g_N/b = a₀`.  On a circular orbit `v² = ar = a₀r`, so rotation speeds would rise as `√r`.
Flat rotation curves therefore support Postulate 1. -/
theorem classical_limit (a0 gN a b r v : ℝ) (hgN : 0 < gN) (hb : b = gN / a0)
    (hab : a = gN / b) (hv : v ^ 2 = a * r) : a = a0 ∧ v ^ 2 = a0 * r := by
  have ha : a = a0 := by
    rw [hab, hb, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hgN.ne', mul_one]
  exact ⟨ha, by rw [hv, ha]⟩

/-- **The baryonic Tully–Fisher relation**, Eq. (btfr): in the deep regime, `a = √(a₀g_N)` with
`g_N = GM/r²`, a circular orbit, `v² = ar`, has `v⁴ = a₀GM` at every radius: the rotation curve is
flat. -/
theorem tully_fisher (a0 G M r v : ℝ) (ha0 : 0 < a0) (hG : 0 < G) (hM : 0 < M) (hr : 0 < r)
    (hv : v ^ 2 = Real.sqrt (a0 * (G * M / r ^ 2)) * r) : v ^ 4 = a0 * G * M := by
  have hr' := hr.ne'
  have e : v ^ 4 = (v ^ 2) ^ 2 := by ring
  rw [e, hv, mul_pow, Real.sq_sqrt (by positivity), mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero 2 hr')]
  ring

end Law

namespace Reg

variable (R : Reg)

/-- **The radial acceleration relation from its inputs** (Sec. IV.C), at leading order in `1/L`,
chained into one statement whose hypotheses are exactly the inputs, each named:
* `hJ`, thermodynamics, Jacobson: Einstein's equations with `G = c³k_B/4ℏη`;
* `hdS`, the constant of the solution without a mass, the horizon at `R_Λ` (Sec. IV.D);
* `I1dS`, `I1N`, `I1a`, thermodynamics, the temperature of a horizon from its period: the
  cosmological horizon, whose period is a largest ring's lap, and the Unruh horizons of `g_N` and
  of `a`;
* `hGibbs`, thermodynamics: the strings' energies are spread at the horizon's temperature and do
  not change, so their mean `ε_s` is the mean of the Gibbs distribution at that temperature;
* `hME`, with Postulate 1's unit: a string's threshold, its slip per tick against the turn per
  tick `h/L`, has the survival function `e^{−x}`, exponential with mean one qubit by the Gibbs
  spread of the strings' energies (`threshold_from_spread`);
* `hb`, Postulate 1 with the probability rule of Sec. IV.A: a string that carries the body's
  information is one of its qubits, so the body's share at a string enters as the amplitude
  `√(E/u)`, in units of the matter a string holds on average: for `E ≤ u` the leading order in
  `1/L` of the exact amplitude, which `Main.share_amplitude` derives from the count of the bits
  that the share fills (`Sources.Approx.share_amplitude`, `Law.share_amplitude`,
  `Law.share_leading_order`), and for `E > u` the condition of the same scale
  (`Sources.Condition.same_scale`); a
  string carries that information when its phase holds against the share, that is, to leading
  order in `1/L`, when the amplitude exceeds the string's threshold, so the carriers are the
  fraction `b` of the strings whose threshold lies below it (`Sources.Approx.carriers_leading`).
  The exact rule is derived from the change of a string's phase with the body's, the share's
  parts per tick and the rule of the phase (`Sources.P1.phase_with_body`,
  `Sources.P1.share_in_parts`, `Sources.P1.carriers_hold_phase`; `Law.keepsAgainstBody_either`,
  `carriers_rule_iff`, `carriers_fraction`), and `Law.fraction_leading_order` bounds the step to leading order;
* `hcar`, `hNcar`, Postulate 1 with equipartition: the body's energy, with `M` all the mass inside
  the sphere, is held by the carriers alone, `ε_c` each on average (`Law.share_of_equipartition`
  gives the sum in finite form, whatever each carrier holds), and the carriers are the fraction
  `b` of the sphere's `N_s` strings;
* `hκ`, `hκN`, equipartition: the mean share of the strings that hold a body's energy is
  proportional to their temperature, `κT`, with one `κ` for every string; the carriers are at
  the sphere's temperature `T_a`, and Newton's mean share, Eq. (E), is the mean share of the
  sphere's strings at the Unruh temperature of `g_N`.  With Eq. (newton) this gives
  `κ = 2k_B ln 2`, two Landauer energies per string on average, and so Eq. (share).
The conclusion is the law with the derived scale, `a = g_N/(1 − e^{−√(g_N/a₀)})` with
`a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)` and `R_Λ = √(3/Λ)`; Newton's mean share, Eq. (newton) at `g_N`;
and `κ = 2k_B ln 2`. -/
theorem radial_acceleration_relation
    (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0)
    (TdS : ℝ) (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (εs : ℝ) (hGibbs : εs = Law.gibbsMean (R.kB * TdS))
    (M r : ℝ) (hM : 0 < M) (hr : 0 < r)
    (TN : ℝ) (I1N : R.kB * TN = R.ℏ / (R.La (G * M / r ^ 2) * R.tc))
    (a Ta : ℝ) (ha : 0 < a) (I1a : R.kB * Ta = R.ℏ / (R.La a * R.tc))
    (surv : ℝ → ℝ) (hME : ∀ x, 0 ≤ x → surv x = Real.exp (-x))
    (b : ℝ) (hb : b = 1 - surv (Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs))))
    (Ncar εc κ : ℝ) (hcar : M * R.c ^ 2 = Ncar * εc) (hNcar : Ncar = b * R.Ns r)
    (hκ : εc = κ * Ta) (hκN : M * R.c ^ 2 = R.Ns r * (κ * TN)) :
    a = (G * M / r ^ 2) / (1 - Real.exp (-Real.sqrt ((G * M / r ^ 2) / R.a0))) ∧
    R.a0 = (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * Real.sqrt (3 / Λ)) ∧
    M * R.c ^ 2 = 2 * R.Ns r * (R.kB * TN * R.ln2) ∧ κ = 2 * R.kB * R.ln2 := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * M / r ^ 2 := by positivity
  -- Eq. (newton) at `g_N`: Newton's mean share
  have hN := R.newton_share G M r TN hr hM hJ I1N
  have hNs : 0 < R.Ns r := by rw [R.bulk_counts r]; unfold n; positivity
  -- equipartition with Eq. (newton): the mean share is two Landauer energies at the temperature
  have hTN : 0 < R.kB * TN := by rw [R.T_Unruh _ TN hgN I1N]; positivity
  have hTN' : TN ≠ 0 := by
    intro h
    rw [h, mul_zero] at hTN
    exact lt_irrefl 0 hTN
  have hκv : κ = 2 * R.kB * R.ln2 := by
    have e : R.Ns r * (κ * TN) = R.Ns r * (2 * R.kB * R.ln2 * TN) := by
      rw [← hκN, hN]
      ring
    exact mul_right_cancel₀ hTN' (mul_left_cancel₀ hNs.ne' e)
  -- Eq. (share): the carriers alone hold the body's energy, two Landauer energies each on average
  have hK : M * R.c ^ 2 = 2 * (b * R.Ns r) * (R.kB * Ta * R.ln2) := by
    rw [hcar, hNcar, hκ, hκv]
    ring
  -- the Gibbs mean at the horizon's temperature is `k_BT_dS`
  have hεs : εs = R.kB * TdS := R.string_energy εs TdS hGibbs I1dS
  -- Eqs. (E), (u), (f): the body's energy per string, in units of the matter a string holds on
  -- average, is `g_N/a₀`
  have hf := R.fill_fraction (G * M / r ^ 2) TN TdS εs hgN I1N I1dS hεs
  have ha0 := R.a0_pos
  have hh : 0 < Real.sqrt ((G * M / r ^ 2) / R.a0) := Real.sqrt_pos.2 (by positivity)
  -- Eq. (b): the carriers are the fraction `1 − e^{−h}`
  have hb' : b = 1 - Real.exp (-Real.sqrt ((G * M / r ^ 2) / R.a0)) := by
    rw [hb, hf, hME _ (Real.sqrt_nonneg _)]
  have hbpos : 0 < b := by rw [hb']; linarith [Law.exp_neg_lt_one hh]
  -- Eq. (share): `a = g_N/b`
  have hab := R.share_acceleration M (R.Ns r) b TN Ta (G * M / r ^ 2) a hNs hbpos hgN ha hN hK
    I1N I1a
  refine ⟨?_, ?_, hN, hκv⟩
  · rw [hab, hb']
  · have hΛ := (R.deSitter G Λ).1 hdS
    have hRL := R.RL_pos
    have e : Real.sqrt (3 / Λ) = R.RL := by
      rw [hΛ, show 3 / (3 / R.RL ^ 2) = R.RL ^ 2 by field_simp, Real.sqrt_sq hRL.le]
    rw [e]
    rfl

/-- **The hypotheses are consistent** for every register: there are a `G`, a `Λ`, temperatures, a
body, a threshold and an acceleration that meet all of them at once, so that
`radial_acceleration_relation` does not hold vacuously.  (`Numerics.reg_jacobson` shows that the
measured `G` meets `hJ` for the register of the measured constants.) -/
theorem hypotheses_consistent :
    ∃ (G Λ TdS εs TN a Ta b Ncar εc κ : ℝ) (surv : ℝ → ℝ),
      G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) ∧ R.fSdS G 0 Λ R.RL = 0 ∧
      R.kB * TdS = R.ℏ / (R.L * R.tc) ∧ εs = Law.gibbsMean (R.kB * TdS) ∧
      R.kB * TN = R.ℏ / (R.La (G * 1 / 1 ^ 2) * R.tc) ∧ 0 < a ∧
      R.kB * Ta = R.ℏ / (R.La a * R.tc) ∧ (∀ x, 0 ≤ x → surv x = Real.exp (-x)) ∧
      b = 1 - surv (Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs))) ∧
      1 * R.c ^ 2 = Ncar * εc ∧ Ncar = b * R.Ns 1 ∧ εc = κ * Ta ∧
      1 * R.c ^ 2 = R.Ns 1 * (κ * TN) := by
  reg_facts R
  have hRL := R.RL_pos
  have hRL' := hRL.ne'
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have htc' := htc.ne'
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  -- Jacobson's `G`
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) := ⟨_, rfl⟩
  have hG := (R.G_eq G hGdef).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * 1 / 1 ^ 2 := by positivity
  -- the constant whose horizon is at `R_Λ`
  have hdS : R.fSdS G 0 (3 / R.RL ^ 2) R.RL = 0 := (R.deSitter G _).2 rfl
  -- the temperatures, as `I1` gives them
  obtain ⟨TdS, hTdS⟩ : ∃ T : ℝ, T = R.ℏ / (R.L * R.tc) / R.kB := ⟨_, rfl⟩
  have I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc) := by rw [hTdS]; field_simp
  have hεs0 : 0 < R.kB * TdS := by rw [I1dS]; positivity
  obtain ⟨TN, hTN⟩ : ∃ T : ℝ, T = R.ℏ / (R.La (G * 1 / 1 ^ 2) * R.tc) / R.kB := ⟨_, rfl⟩
  have hLa : 0 < R.La (G * 1 / 1 ^ 2) := by unfold Reg.La; positivity
  have hLa' := hLa.ne'
  have I1N : R.kB * TN = R.ℏ / (R.La (G * 1 / 1 ^ 2) * R.tc) := by rw [hTN]; field_simp
  have hTN0 : 0 < R.kB * TN := by rw [I1N]; positivity
  -- the carriers, and the acceleration `g_N/b`
  have harg : 0 < 2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * (R.kB * TdS)) := by
    rw [show 2 * R.kB * TN * R.ln2 = 2 * (R.kB * TN) * R.ln2 by ring]
    exact div_pos (by positivity) (mul_pos hm hεs0)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ,
      b = 1 - Real.exp (-Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * (R.kB * TdS)))) :=
    ⟨_, rfl⟩
  have hbpos : 0 < b := by rw [hbdef]; linarith [Law.exp_neg_lt_one (Real.sqrt_pos.2 harg)]
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = G * 1 / 1 ^ 2 / b := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; positivity
  obtain ⟨Ta, hTa⟩ : ∃ T : ℝ, T = R.ℏ / (R.La a * R.tc) / R.kB := ⟨_, rfl⟩
  have hLaa : 0 < R.La a := by unfold Reg.La; positivity
  have hLaa' := hLaa.ne'
  have I1a : R.kB * Ta = R.ℏ / (R.La a * R.tc) := by rw [hTa]; field_simp
  -- Eq. (newton) at `g_N`, and the Unruh temperatures of `g_N` and of `a = g_N/b`
  have hN := R.newton_share G 1 1 TN one_pos one_pos hGdef I1N
  have h1 := R.T_Unruh _ TN hgN I1N
  have h2 := R.T_Unruh a Ta ha I1a
  have hb' := hbpos.ne'
  refine ⟨G, 3 / R.RL ^ 2, TdS, R.kB * TdS, TN, a, Ta, b, b * R.Ns 1,
    2 * R.kB * R.ln2 * Ta, 2 * R.kB * R.ln2, fun x => Real.exp (-x), hGdef, hdS, I1dS,
    (Law.gibbsMean_eq _ hεs0).symm, I1N, ha, I1a, fun _ _ => rfl, hbdef, ?_, rfl, rfl, ?_⟩
  -- the carriers hold the body's energy, two Landauer energies each on average at `T_a = T_N/b`
  · show 1 * R.c ^ 2 = b * R.Ns 1 * (2 * R.kB * R.ln2 * Ta)
    rw [show b * R.Ns 1 * (2 * R.kB * R.ln2 * Ta) = 2 * (b * R.Ns 1) * (R.kB * Ta * R.ln2) by
      ring]
    rw [hN, h1, h2, hadef]
    field_simp
  -- Newton's mean share, two Landauer energies per string at `T_N` on average
  · show 1 * R.c ^ 2 = R.Ns 1 * (2 * R.kB * R.ln2 * TN)
    rw [hN]
    ring

end Reg

end Register
