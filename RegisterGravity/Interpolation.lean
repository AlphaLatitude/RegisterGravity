import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Milgrom's simple interpolating function against Eq. (law) (Sec. IV.C)

Formal counterpart of one sentence of Sec. IV.C: "Other functions fit the data too; Milgrom's
simple interpolating function differs from Eq. (law) by at most `5%` at every acceleration, so the
data test the form at about that level".

Eq. (law) gives the acceleration `a = g_N/(1 − e^{−√(g_N/a₀)})` about a mass with Newton's field
`g_N` (`law`).  Milgrom's simple interpolating function `μ(x) = x/(1 + x)` gives the acceleration
`a` with `a μ(a/a₀) = g_N`, whose positive root is `(g_N + √(g_N² + 4g_Na₀))/2` (`simple`,
`simple_root`).  With one scale `a₀` in both, `simple_within` proves

  `law ≤ simple ≤ (21/20) law`  for every `g_N > 0`,

so the simple function never lies below Eq. (law) and exceeds it by at most `5%`.  The largest
excess, `4.7%`, is at `g_N ≈ 7a₀`; the files prove the bound `5%` and not that number.

The proof.  Put `s = √(g_N/a₀)` and `w = (s + √(s² + 4))/2`, so that `w ≥ 1`, `s = w − 1/w` and
the simple function is `a₀ s w`, while Eq. (law) is `a₀ s² e^s/(e^s − 1)`.  The two bounds are
then `w² ≤ e^{w − 1/w}` (`sq_le_exp`) and `(21 − w²) e^{w − 1/w} ≤ 20 w²` (`exp_le_of_one_le`).
The first holds since `w − 1/w − 2 ln w` vanishes at `1` and has the derivative `(1 − 1/w)²`.
The second is `0 ≤ hfun w` for `hfun w = ln(20w²) − ln(21 − w²) − w + 1/w` where `w² < 21`
(`hfun_nonneg`).  The derivative of `hfun` has the sign of the quartic
`w⁴ − 20w² + 42w − 21`, which is nonnegative on `[1, 1.84]`, nonpositive on `[1.85, 2.71]` and
nonnegative from `2.73` on, so `hfun` rises from `hfun 1 = 0`, falls, and rises again; on the
two short intervals between, and at the points `2.71` and `2.73`, two bounds on the exponential
give `0 ≤ hfun` directly (`exp_bound_left`, `exp_bound_right`, `hfun_direct`).
-/

open Set

namespace Register
namespace Interpolation

/-! ### `w² ≤ e^{w − 1/w}` for `w ≥ 1` -/

/-- the derivative of `w − 1/w − 2 ln w` -/
lemma hasDerivAt_F (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun w : ℝ => w - w⁻¹ - 2 * Real.log w) (1 - -(w ^ 2)⁻¹ - 2 * w⁻¹) w :=
  ((hasDerivAt_id' w).sub (hasDerivAt_inv hw.ne')).sub
    ((Real.hasDerivAt_log hw.ne').const_mul 2)

/-- `2 ln w ≤ w − 1/w` for `w ≥ 1`: the difference vanishes at `1` and has the derivative
`(1 − 1/w)²` -/
lemma two_log_le (w : ℝ) (hw : 1 ≤ w) : 2 * Real.log w ≤ w - w⁻¹ := by
  have hmono : MonotoneOn (fun w : ℝ => w - w⁻¹ - 2 * Real.log w) (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun w => 1 - -(w ^ 2)⁻¹ - 2 * w⁻¹)
    · intro x hx
      exact (hasDerivAt_F x (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hasDerivAt_F x (lt_trans one_pos hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans one_pos hx
      have hsq : 1 - -(x ^ 2)⁻¹ - 2 * x⁻¹ = (1 - x⁻¹) ^ 2 := by
        field_simp
        ring
      rw [hsq]
      positivity
  have h := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hw) hw
  have h1 : (1 : ℝ) - 1⁻¹ - 2 * Real.log 1 = 0 := by simp
  change (1 : ℝ) - 1⁻¹ - 2 * Real.log 1 ≤ w - w⁻¹ - 2 * Real.log w at h
  linarith

/-- **`w² ≤ e^{w − 1/w}` for `w ≥ 1`**: the bound that puts Eq. (law) below the simple function. -/
theorem sq_le_exp (w : ℝ) (hw : 1 ≤ w) : w ^ 2 ≤ Real.exp (w - w⁻¹) := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  rw [← Real.log_le_iff_le_exp (by positivity), Real.log_pow]
  have := two_log_le w hw
  push_cast
  linarith

/-! ### `(21 − w²) e^{w − 1/w} ≤ 20 w²` for `w ≥ 1` -/

/-- `ln(20w²) − ln(21 − w²) − w + 1/w` -/
noncomputable def hfun (w : ℝ) : ℝ :=
  Real.log (20 * w ^ 2) - Real.log (21 - w ^ 2) - w + w⁻¹

/-- `hfun` vanishes at `1` -/
lemma hfun_one : hfun 1 = 0 := by
  unfold hfun
  norm_num

/-- the derivative of `hfun` where `0 < w` and `w² < 21`: the quartic `w⁴ − 20w² + 42w − 21` over
`w²(21 − w²)` -/
lemma hasDerivAt_hfun (w : ℝ) (hw : 0 < w) (hw2 : w ^ 2 < 21) :
    HasDerivAt hfun ((w ^ 4 - 20 * w ^ 2 + 42 * w - 21) / (w ^ 2 * (21 - w ^ 2))) w := by
  have hne : (21 : ℝ) - w ^ 2 ≠ 0 := (sub_pos.2 hw2).ne'
  have h1 : HasDerivAt (fun w : ℝ => 20 * w ^ 2) (20 * (2 * w)) w := by
    simpa using ((hasDerivAt_pow 2 w).const_mul (20 : ℝ))
  have h2 : HasDerivAt (fun w : ℝ => 21 - w ^ 2) (-(2 * w)) w := by
    simpa using ((hasDerivAt_pow 2 w).const_sub (21 : ℝ))
  have h := ((h1.log (by positivity)).sub (h2.log hne)).sub (hasDerivAt_id' w)
  have h' := h.add (hasDerivAt_inv hw.ne')
  have heq : (20 * (2 * w)) / (20 * w ^ 2) - (-(2 * w)) / (21 - w ^ 2) - 1 + -(w ^ 2)⁻¹
      = (w ^ 4 - 20 * w ^ 2 + 42 * w - 21) / (w ^ 2 * (21 - w ^ 2)) := by
    field_simp
    ring
  rw [← heq]
  exact h'

/-- `hfun` rises on an interval on which the quartic is nonnegative -/
lemma hfun_monotoneOn (a b : ℝ) (ha : 0 < a) (hb : b ^ 2 < 21)
    (hp : ∀ x, a ≤ x → x ≤ b → 0 ≤ x ^ 4 - 20 * x ^ 2 + 42 * x - 21) :
    MonotoneOn hfun (Icc a b) := by
  have hdom : ∀ x ∈ Icc a b, 0 < x ∧ x ^ 2 < 21 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact ⟨hx0, by nlinarith [hx.2]⟩
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (f' := fun w => (w ^ 4 - 20 * w ^ 2 + 42 * w - 21) / (w ^ 2 * (21 - w ^ 2)))
  · intro x hx
    exact (hasDerivAt_hfun x (hdom x hx).1 (hdom x hx).2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (hasDerivAt_hfun x (hdom x hx').1 (hdom x hx').2).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have h21 : 0 < 21 - x ^ 2 := sub_pos.2 (hdom x hx').2
    exact div_nonneg (hp x hx'.1 hx'.2) (mul_nonneg (sq_nonneg x) h21.le)

/-- `hfun` falls on an interval on which the quartic is nonpositive -/
lemma hfun_antitoneOn (a b : ℝ) (ha : 0 < a) (hb : b ^ 2 < 21)
    (hp : ∀ x, a ≤ x → x ≤ b → x ^ 4 - 20 * x ^ 2 + 42 * x - 21 ≤ 0) :
    AntitoneOn hfun (Icc a b) := by
  have hdom : ∀ x ∈ Icc a b, 0 < x ∧ x ^ 2 < 21 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact ⟨hx0, by nlinarith [hx.2]⟩
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (f' := fun w => (w ^ 4 - 20 * w ^ 2 + 42 * w - 21) / (w ^ 2 * (21 - w ^ 2)))
  · intro x hx
    exact (hasDerivAt_hfun x (hdom x hx).1 (hdom x hx).2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (hasDerivAt_hfun x (hdom x hx').1 (hdom x hx').2).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have h21 : 0 < 21 - x ^ 2 := sub_pos.2 (hdom x hx').2
    exact div_nonpos_of_nonpos_of_nonneg (hp x hx'.1 hx'.2) (mul_nonneg (sq_nonneg x) h21.le)

/-- the quartic is nonnegative on `[1, 1.84]` -/
lemma quartic_nonneg_left (w : ℝ) (h1 : 1 ≤ w) (h2 : w ≤ 46 / 25) :
    0 ≤ w ^ 4 - 20 * w ^ 2 + 42 * w - 21 := by
  have hq : 0 ≤ 8609 / 625 - 71 / 25 * w - w ^ 2 := by nlinarith
  have hprod := mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) hq
  nlinarith [hprod]

/-- the quartic is nonpositive on `[1.85, 2.71]` -/
lemma quartic_nonpos_mid (w : ℝ) (h1 : 37 / 20 ≤ w) (h2 : w ≤ 271 / 100) :
    w ^ 4 - 20 * w ^ 2 + 42 * w - 21 ≤ 0 := by
  have hq : 0 ≤ w ^ 2 + 114 / 25 * w - 42199 / 10000 := by nlinarith
  have hprod := mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) hq
  nlinarith [hprod]

/-- the quartic is nonnegative from `2.73` on -/
lemma quartic_nonneg_right (w : ℝ) (h1 : 273 / 100 ≤ w) :
    0 ≤ w ^ 4 - 20 * w ^ 2 + 42 * w - 21 := by
  have ht : 0 ≤ w - 273 / 100 := sub_nonneg.2 h1
  have hexp : w ^ 4 - 20 * w ^ 2 + 42 * w - 21
      = (w - 273 / 100) ^ 4 + 273 / 25 * (w - 273 / 100) ^ 3
        + 123587 / 5000 * (w - 273 / 100) ^ 2 + 3546417 / 250000 * (w - 273 / 100)
        + 14771841 / 100000000 := by ring
  rw [hexp]
  positivity

/-- `e^{1.85 − 1/1.85} ≤ 20·1.84²/(21 − 1.84²)` -/
lemma exp_bound_left :
    Real.exp (37 / 20 - (37 / 20 : ℝ)⁻¹) ≤ 20 * (46 / 25) ^ 2 / (21 - (46 / 25) ^ 2) := by
  have hx : (37 / 20 - (37 / 20 : ℝ)⁻¹) ≤ 1 + 31 / 100 := by norm_num
  have h1 : Real.exp (37 / 20 - (37 / 20 : ℝ)⁻¹) ≤ Real.exp 1 * Real.exp (31 / 100) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 hx
  have q : Real.exp (31 / 100) ≤ (∑ i ∈ Finset.range 4, (31 / 100 : ℝ) ^ i / (Nat.factorial i)) +
      (31 / 100 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) :=
    Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
  have q' : Real.exp (31 / 100) ≤ 13635 / 10000 := by
    refine q.trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have e2 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp (31 / 100 : ℝ) := Real.exp_pos _
  have hprod : Real.exp 1 * Real.exp (31 / 100) ≤ 2.7182818286 * (13635 / 10000) :=
    mul_le_mul e2.le q' hpos.le (by norm_num)
  refine h1.trans (hprod.trans ?_)
  norm_num

/-- `e^{2.73 − 1/2.73} ≤ 20·2.71²/(21 − 2.71²)` -/
lemma exp_bound_right :
    Real.exp (273 / 100 - (273 / 100 : ℝ)⁻¹) ≤ 20 * (271 / 100) ^ 2 / (21 - (271 / 100) ^ 2) := by
  have hx : (273 / 100 - (273 / 100 : ℝ)⁻¹) ≤ 1 + 1 + 364 / 1000 := by norm_num
  have h1 : Real.exp (273 / 100 - (273 / 100 : ℝ)⁻¹)
      ≤ Real.exp 1 * Real.exp 1 * Real.exp (364 / 1000) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 hx
  have q : Real.exp (364 / 1000) ≤
      (∑ i ∈ Finset.range 4, (364 / 1000 : ℝ) ^ i / (Nat.factorial i)) +
      (364 / 1000 : ℝ) ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) :=
    Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
  have q' : Real.exp (364 / 1000) ≤ 14393 / 10000 := by
    refine q.trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have e2 := Real.exp_one_lt_d9
  have e0 : 0 < Real.exp 1 := Real.exp_pos _
  have hpos : 0 < Real.exp (364 / 1000 : ℝ) := Real.exp_pos _
  have hee : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul e2.le e2.le e0.le (by norm_num)
  have hprod : Real.exp 1 * Real.exp 1 * Real.exp (364 / 1000)
      ≤ 2.7182818286 * 2.7182818286 * (14393 / 10000) :=
    mul_le_mul hee q' hpos.le (by norm_num)
  refine h1.trans (hprod.trans ?_)
  norm_num

/-- on a short interval `[a, b]`, `0 ≤ hfun` follows from one bound on the exponential at `b`
against the rational function at `a` -/
lemma hfun_direct (a b w : ℝ) (ha : 0 < a) (haw : a ≤ w) (hwb : w ≤ b) (h21 : w ^ 2 < 21)
    (hexp : Real.exp (b - b⁻¹) ≤ 20 * a ^ 2 / (21 - a ^ 2)) : 0 ≤ hfun w := by
  have hw : 0 < w := lt_of_lt_of_le ha haw
  have ha21 : 0 < 21 - a ^ 2 := by nlinarith
  have hw21 : 0 < 21 - w ^ 2 := sub_pos.2 h21
  have h1 : Real.log (20 * a ^ 2) ≤ Real.log (20 * w ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have h2 : Real.log (21 - w ^ 2) ≤ Real.log (21 - a ^ 2) :=
    Real.log_le_log hw21 (by nlinarith)
  have h3 : w - w⁻¹ ≤ b - b⁻¹ := by
    have : b⁻¹ ≤ w⁻¹ := inv_anti₀ hw hwb
    linarith
  have h4 : b - b⁻¹ ≤ Real.log (20 * a ^ 2 / (21 - a ^ 2)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact hexp
  rw [Real.log_div (by positivity) ha21.ne'] at h4
  unfold hfun
  linarith

/-- `0 ≤ hfun w` for `w ≥ 1` with `w² < 21` -/
lemma hfun_nonneg (w : ℝ) (hw : 1 ≤ w) (h21 : w ^ 2 < 21) : 0 ≤ hfun w := by
  rcases le_total w (46 / 25) with ha | ha
  · have h := hfun_monotoneOn 1 (46 / 25) one_pos (by norm_num)
      (fun x h1 h2 => quartic_nonneg_left x h1 h2)
      (mem_Icc.2 ⟨le_rfl, by norm_num⟩) (mem_Icc.2 ⟨hw, ha⟩) hw
    rw [hfun_one] at h
    exact h
  rcases le_total w (37 / 20) with hb | hb
  · exact hfun_direct (46 / 25) (37 / 20) w (by norm_num) ha hb h21 exp_bound_left
  have h271 : 0 ≤ hfun (271 / 100) :=
    hfun_direct (271 / 100) (273 / 100) (271 / 100) (by norm_num) le_rfl (by norm_num)
      (by norm_num) exp_bound_right
  rcases le_total w (271 / 100) with hc | hc
  · have h := hfun_antitoneOn (37 / 20) (271 / 100) (by norm_num) (by norm_num)
      (fun x h1 h2 => quartic_nonpos_mid x h1 h2)
      (mem_Icc.2 ⟨hb, hc⟩) (mem_Icc.2 ⟨by norm_num, le_rfl⟩) hc
    exact h271.trans h
  rcases le_total w (273 / 100) with hd | hd
  · exact hfun_direct (271 / 100) (273 / 100) w (by norm_num) hc hd h21 exp_bound_right
  have h273 : 0 ≤ hfun (273 / 100) :=
    hfun_direct (271 / 100) (273 / 100) (273 / 100) (by norm_num) (by norm_num) le_rfl
      (by norm_num) exp_bound_right
  have h := hfun_monotoneOn (273 / 100) w (by norm_num) h21
    (fun x h1 _ => quartic_nonneg_right x h1)
    (mem_Icc.2 ⟨le_rfl, hd⟩) (mem_Icc.2 ⟨hd, le_rfl⟩) hd
  exact h273.trans h

/-- **`(21 − w²) e^{w − 1/w} ≤ 20 w²` for `w ≥ 1`**: the bound that puts the simple function at
most `5%` above Eq. (law). -/
theorem exp_le_of_one_le (w : ℝ) (hw : 1 ≤ w) :
    (21 - w ^ 2) * Real.exp (w - w⁻¹) ≤ 20 * w ^ 2 := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  rcases le_or_gt 21 (w ^ 2) with h21 | h21
  · have h0 : (21 - w ^ 2) * Real.exp (w - w⁻¹) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    nlinarith [sq_nonneg w]
  · have hh : 0 ≤ hfun w := hfun_nonneg w hw h21
    have hpos : 0 < 21 - w ^ 2 := sub_pos.2 h21
    have hle : w - w⁻¹ ≤ Real.log (20 * w ^ 2 / (21 - w ^ 2)) := by
      rw [Real.log_div (by positivity) hpos.ne']
      unfold hfun at hh
      linarith
    have h := Real.exp_le_exp.2 hle
    rw [Real.exp_log (by positivity), le_div_iff₀ hpos] at h
    linarith

/-! ### Milgrom's simple interpolating function against Eq. (law) -/

/-- **Eq. (law)** (Sec. IV.C), as a function: the acceleration about a mass with Newton's field
`g_N`, for the scale `a₀` (`Sources.Derived.galactic_law` is `a = law R.a0 g_N`) -/
noncomputable def law (a0 gN : ℝ) : ℝ := gN / (1 - Real.exp (-Real.sqrt (gN / a0)))

/-- **Milgrom's simple interpolating function** `μ(x) = x/(1 + x)` (Sec. IV.C): the acceleration
that it gives for Newton's field `g_N`, the positive root of `a μ(a/a₀) = g_N` (`simple_root`) -/
noncomputable def simple (a0 gN : ℝ) : ℝ := (gN + Real.sqrt (gN ^ 2 + 4 * gN * a0)) / 2

/-- **The simple function's acceleration solves Milgrom's relation**: `simple a₀ g_N` is positive
and `a μ(a/a₀) = g_N` holds for it, with `μ(x) = x/(1 + x)`. -/
theorem simple_root (a0 gN : ℝ) (ha : 0 < a0) (hg : 0 < gN) :
    0 < simple a0 gN ∧
      simple a0 gN * ((simple a0 gN / a0) / (1 + simple a0 gN / a0)) = gN := by
  have hR0 : 0 ≤ gN ^ 2 + 4 * gN * a0 := by positivity
  have hR := Real.sq_sqrt hR0
  have hRpos : 0 ≤ Real.sqrt (gN ^ 2 + 4 * gN * a0) := Real.sqrt_nonneg _
  have hpos : 0 < simple a0 gN := by
    unfold simple
    positivity
  refine ⟨hpos, ?_⟩
  have hquad : simple a0 gN ^ 2 = gN * (simple a0 gN + a0) := by
    unfold simple
    nlinarith [hR]
  have hden : (0 : ℝ) < a0 + simple a0 gN := by positivity
  field_simp
  nlinarith [hquad]

/-- **Milgrom's simple interpolating function differs from Eq. (law) by at most `5%` at every
acceleration** (Sec. IV.C, in these words): with one scale `a₀` in both, the simple function's
acceleration is at least that of Eq. (law) and at most `21/20` of it, for every `g_N > 0`. -/
theorem simple_within (a0 gN : ℝ) (ha : 0 < a0) (hg : 0 < gN) :
    law a0 gN ≤ simple a0 gN ∧ simple a0 gN ≤ 21 / 20 * law a0 gN := by
  have hy : 0 < gN / a0 := div_pos hg ha
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (gN / a0) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hy
  have hs2 : s ^ 2 = gN / a0 := by rw [hs]; exact Real.sq_sqrt hy.le
  have hgN : gN = a0 * s ^ 2 := by
    rw [hs2]
    field_simp
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (s ^ 2 + 4) := ⟨_, rfl⟩
  have hr2 : r ^ 2 = s ^ 2 + 4 := by rw [hr]; exact Real.sq_sqrt (by positivity)
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 (by positivity)
  obtain ⟨w, hw⟩ : ∃ w, w = (s + r) / 2 := ⟨_, rfl⟩
  have hrs : 2 - s < r := by
    by_contra h
    push Not at h
    nlinarith
  have hw1 : 1 < w := by rw [hw]; linarith
  have hw0 : 0 < w := lt_trans one_pos hw1
  have hww : w ^ 2 = s * w + 1 := by rw [hw]; nlinarith
  have hsw : s = w - w⁻¹ := by
    field_simp
    nlinarith
  -- the two functions in `s` and `w`
  have hsqrt : Real.sqrt (gN ^ 2 + 4 * gN * a0) = a0 * s * r := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), hgN]
    nlinarith [hr2]
  have hsimple : simple a0 gN = a0 * s * w := by
    unfold simple
    rw [hsqrt, hgN, hw]
    ring
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp s := ⟨_, rfl⟩
  have hE1 : 1 < E := by
    rw [hE]
    have := Real.add_one_le_exp s
    linarith
  have hlaw : law a0 gN = a0 * s ^ 2 * E / (E - 1) := by
    unfold law
    rw [← hs, Real.exp_neg, ← hE, hgN]
    have hE0 : E ≠ 0 := by positivity
    have hE1' : E - 1 ≠ 0 := by linarith
    field_simp
  have hEm : 0 < E - 1 := by linarith
  -- the two bounds on `E = e^{w − 1/w}`
  have hi : w ^ 2 ≤ E := by rw [hE, hsw]; exact sq_le_exp w hw1.le
  have hii : (21 - w ^ 2) * E ≤ 20 * w ^ 2 := by rw [hE, hsw]; exact exp_le_of_one_le w hw1.le
  have hk1 : s * E ≤ w * (E - 1) := by
    have hid : w * (w * (E - 1) - s * E) = E - w ^ 2 := by linear_combination E * hww
    have : 0 ≤ w * (w * (E - 1) - s * E) := by rw [hid]; linarith
    nlinarith [this]
  have hk2 : 20 * w * (E - 1) ≤ 21 * s * E := by
    have hid : w * (21 * s * E - 20 * w * (E - 1)) = 20 * w ^ 2 - (21 - w ^ 2) * E := by
      linear_combination (-(21 : ℝ) * E) * hww
    have : 0 ≤ w * (21 * s * E - 20 * w * (E - 1)) := by rw [hid]; linarith
    nlinarith [this]
  rw [hsimple, hlaw]
  constructor
  · rw [div_le_iff₀ hEm]
    have := mul_le_mul_of_nonneg_left hk1 (mul_pos ha hs0).le
    nlinarith [this]
  · rw [mul_div_assoc', le_div_iff₀ hEm]
    have := mul_le_mul_of_nonneg_left hk2 (mul_pos ha hs0).le
    nlinarith [this]

end Interpolation
end Register
