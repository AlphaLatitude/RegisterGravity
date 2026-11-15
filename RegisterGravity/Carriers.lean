import RegisterGravity.Chain
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
  each string that carries it the same share; so the energy is the number of carriers times that
  share.
* `Reg.newton_share`, Eq. (newton) at `g_N`: with Jacobson's `G` and `I1` for the Unruh
  temperature `T_N` of `g_N = GM/r²`, the body's energy is two Landauer energies at `T_N` for each
  string of the sphere.
* `Reg.share_acceleration`, Eq. (share): with the body's energy held by the fraction `b` of the
  sphere's strings at two Landauer energies each, against Eq. (newton) at `g_N`, the acceleration
  is `g_N/b`.
* `Law.gibbsMean_eq`, Eq. (mean), and `Reg.string_energy`: the strings' energies are spread at
  the horizon's temperature and do not change (`hGibbs`), so their mean is the mean of the Gibbs
  distribution over energies from zero up, the horizon's thermal energy `k_BT_dS`; on a ladder of
  equal steps the mean lies within one step of it (`Law.gibbsLadder_eq`,
  `Law.gibbsLadder_within_step`).
* `Reg.fill_fraction`, Eqs. (E), (u) and (f): the body's energy per string, two Landauer energies
  at the Unruh temperature of `g_N`, counted in units of the matter a string holds on average,
  `u = (1 − ln 2)k_BT_dS`,
  is `f = g_N/a₀` with `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`.
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

The amplitude `h = √f` is an application of Postulate 1 that Sec. IV.C makes
(`Sources.P1.share_amplitude`): a string that carries the body's information is one of its qubits,
so its share of the body is the fraction `f` of a whole qubit, and the amplitude of that share is
`√f`, in units of one whole qubit.  In `Reg.law` it is the argument of the threshold's survival
function (`hb`).  At leading order in `1/L` the fraction `b` of carriers is the probability that
a string's threshold lies below `h`, and so the fraction of the sphere's strings that carry the
body's information.
-/

open Real Finset

namespace Register

namespace Law

/-- **The share of a body's energy** (Sec. IV.C), in finite form.  The body is all the mass inside
the sphere, so a string's share is of that total, not of each star within it.  The body's energy
`E` is held by the strings `S` of the sphere (`hsum`; by Postulate 1 all the mass and light of the
universe consists of strings); where a string does not carry the body's information, its two
receiving cells, the cells where its ring crosses the sphere, keep the state they have without the
body, and the string holds none of the body's Landauer energies there (`hoff`); and equipartition
gives each carrier the same share `ε`
(`heq`).  Then `E = |C| ε`: the energy is held by the carriers alone. -/
theorem share_of_equipartition {ι : Type*} (S C : Finset ι) (hCS : C ⊆ S) (e : ι → ℝ) (E ε : ℝ)
    (hsum : ∑ i ∈ S, e i = E) (hoff : ∀ i ∈ S, i ∉ C → e i = 0) (heq : ∀ i ∈ C, e i = ε) :
    E = (C.card : ℝ) * ε := by
  rw [← hsum, ← Finset.sum_subset hCS hoff, Finset.sum_congr rfl heq, Finset.sum_const,
    nsmul_eq_mul]

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
and `θ`. -/
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
whole number of turns (`steady_phase_all_turns`, `steady_phase_iff_turns`). -/
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
(`steady_phase_all_turns`, `near_whole_turn_iff`).  This is the sentence of Sec. IV.C,
"A state of unit amplitude that a tick turns by `Δ`, and to which the tick adds the smaller
amplitude `h/L` at a fixed phase, has a phase that the tick leaves unchanged exactly when `Δ` is
within `arcsin(h/L)` of a whole number of turns, as the Lean files prove."  The
paper states it with `ε = h/L`. -/
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
`g_N = GM/r²`, the body's energy is two Landauer energies at `T_N` for each string of the sphere,
`Mc² = 2N_s k_BT_N ln 2` (`Reg.newton` gives the same with the pull of the solution). -/
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
two Landauer energies at the Unruh temperature `T_N` of `g_N` for each of the sphere's `N_s`
strings (`hN`, Eq. (newton) at `g_N`, `newton_share`), and it is held by the fraction `b` of them
at the temperature `T_a` of the acceleration `a`, two Landauer energies each (`hS`, the body's
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
one.  `fraction_above_turn` states the spread in turns per tick, as the exact fraction takes
it. -/
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
of `Sources.P1.carriers_hold_phase`.  Whatever distribution `μ` of the strings' energies, a
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
/-- **The hypotheses of the carrying rule can hold at once** (Sec. IV.C), for every register and
every amplitude `0 < h < L` of a body's share: there are an amplitude `ε` per tick with `Lε = h`
(the share's `L` equal parts, `Sources.P1.share_in_parts`), a temperature with
`k_BT_dS = ℏ/(Lt_c)`, and a spread of the strings' energies at that temperature with its mean
(`Sources.Thermo.energies_thermal`).  There are also a distribution of the energies, a
probability measure, with the fractions of that spread above each energy
(`Law.gibbs_measure_exists`), and a fraction `b` that meets the rule of the phase for every such
distribution (`Sources.P1.carriers_hold_phase`, by `carriers_rule_iff`).  So
`Main.carriers_exact` does not hold vacuously, and the rule, which is stated for every
distribution with those fractions, is stated for at least one. -/
theorem carriers_model (h : ℝ) (hh0 : 0 < h) (hhL : h < R.L) :
    ∃ (ε b TdS εs : ℝ) (above : ℝ → ℝ),
      R.L * ε = h ∧ R.kB * TdS = R.ℏ / (R.L * R.tc) ∧ εs = Law.gibbsMean (R.kB * TdS) ∧
      (∀ y, 0 ≤ y → above y = Law.gibbsAbove (R.kB * TdS) y) ∧
      (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
        ∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
        (∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) →
        b = (μ {E : ℝ | 0 ≤ E ∧ Law.keepsPhase (E * R.tc / R.ℏ) ε}).toReal := by
  reg_facts R
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have htc' := htc.ne'
  have hε0 : 0 < h / R.L := div_pos hh0 R.L_pos
  have hε1 : h / R.L < 1 := (div_lt_one R.L_pos).2 hhL
  obtain ⟨TdS, hTdS⟩ : ∃ T : ℝ, T = R.ℏ / (R.L * R.tc) / R.kB := ⟨_, rfl⟩
  have I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc) := by rw [hTdS]; field_simp
  have hθ : 0 < R.kB * TdS := by rw [I1dS]; positivity
  refine ⟨h / R.L, (1 - Real.exp (-(R.L * Real.arcsin (h / R.L)))) *
      (1 + (Real.exp (R.L * Real.arcsin (h / R.L)) + 1) / (Real.exp (2 * Real.pi * R.L) - 1)),
    TdS, Law.gibbsMean (R.kB * TdS), fun y => Law.gibbsAbove (R.kB * TdS) y, by field_simp, I1dS,
    rfl, fun _ _ => rfl, Law.gibbs_measure_exists (R.kB * TdS) hθ, ?_⟩
  exact (R.carriers_rule_iff TdS _ (h / R.L) (fun y => Law.gibbsAbove (R.kB * TdS) y) hε0 hε1
    I1dS (fun _ _ => rfl)).2 rfl

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
  `√(E/u)`, in units of the matter a string holds on average (`Sources.P1.share_amplitude`); a
  string carries that information when its phase holds against the share, that is, to leading
  order in `1/L`, when the amplitude exceeds the string's threshold, so the carriers are the
  fraction `b` of the strings whose threshold lies below it (`Sources.Approx.carriers_leading`).
  The exact rule is derived from the share's parts per tick and the rule of the phase
  (`Sources.P1.share_in_parts`, `Sources.P1.carriers_hold_phase`; `carriers_rule_iff`,
  `carriers_fraction`), and `Law.fraction_leading_order` bounds the step to leading order;
* `hcar`, `hNcar`, Postulate 1 with equipartition: the body's energy, with `M` all the mass inside
  the sphere, is held by the carriers alone, in equal shares (`Law.share_of_equipartition` gives
  this in finite form), and the carriers are the fraction `b` of the sphere's `N_s` strings;
* `hκ`, `hκN`, equipartition: a string's share is proportional to its temperature, `κT`, with one
  `κ` for every string; the carriers are at the sphere's temperature `T_a`, and Newton's equal
  share, Eq. (E), is that of every string at the Unruh temperature of `g_N`.  With Eq. (newton)
  this gives `κ = 2k_B ln 2`, two Landauer energies per string, and so Eq. (share).
The conclusion is the law with the derived scale, `a = g_N/(1 − e^{−√(g_N/a₀)})` with
`a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)` and `R_Λ = √(3/Λ)`; Newton's equal share, Eq. (newton) at `g_N`;
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
  -- Eq. (newton) at `g_N`: Newton's equal share
  have hN := R.newton_share G M r TN hr hM hJ I1N
  have hNs : 0 < R.Ns r := by rw [R.bulk_counts r]; unfold n; positivity
  -- equipartition with Eq. (newton): a string's share is two Landauer energies at its temperature
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
  -- Eq. (share): the carriers alone hold the body's energy, two Landauer energies each
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
  -- the carriers hold the body's energy, two Landauer energies each at `T_a = T_N/b`
  · show 1 * R.c ^ 2 = b * R.Ns 1 * (2 * R.kB * R.ln2 * Ta)
    rw [show b * R.Ns 1 * (2 * R.kB * R.ln2 * Ta) = 2 * (b * R.Ns 1) * (R.kB * Ta * R.ln2) by
      ring]
    rw [hN, h1, h2, hadef]
    field_simp
  -- Newton's equal share, two Landauer energies per string at `T_N`
  · show 1 * R.c ^ 2 = R.Ns 1 * (2 * R.kB * R.ln2 * TN)
    rw [hN]
    ring

end Reg

end Register
