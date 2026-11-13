import RegisterGravity.Chain
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

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
* `Reg.law`, Eq. (law): with the threshold exponential with mean one in amplitude (`hME`,
  maximum entropy with one qubit as the only scale), the fraction of carriers is `b = 1 − e^{−√f}`,
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

The amplitude `h = √f` follows from Postulate 1 with the probability rule of Sec. IV.A: a string
that carries the body's information is one of its qubits, so its share of the body is the fraction
`f` of a whole qubit, and the amplitude of that share is `√f`, in units of one whole qubit.  It
enters through the argument of `hME`.  The fraction `b` of carriers is the probability that a
string's threshold lies below `h`, and so the fraction of the sphere's strings that carry the
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

/-- **The law**, Eq. (law).  The threshold's survival function is `e^{−x}` (`hME`: maximum entropy
for a positive quantity whose only scale, one qubit, is its mean), so the strings whose threshold
lies below the amplitude `√(g_N/a₀)` are the fraction `b = 1 − e^{−√(g_N/a₀)}` (`hb`), and with
`a = g_N/b` (`share_acceleration`) the relation follows. -/
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

/-- **The radial acceleration relation from its inputs** (Sec. IV.C), chained into one statement
whose hypotheses are exactly the inputs, each named:
* `hJ`, thermodynamics, Jacobson: Einstein's equations with `G = c³k_B/4ℏη`;
* `hdS`, the constant of the solution without a mass, the horizon at `R_Λ` (Sec. IV.D);
* `I1dS`, `I1N`, `I1a`, thermodynamics, the temperature of a horizon from its period: the
  cosmological horizon, whose period is a largest ring's lap, and the Unruh horizons of `g_N` and
  of `a`;
* `hGibbs`, thermodynamics: the strings' energies are spread at the horizon's temperature and do
  not change, so their mean `ε_s` is the mean of the Gibbs distribution at that temperature;
* `hME`, thermodynamics, maximum entropy, with Postulate 1's unit: a string's threshold has the
  survival function `e^{−x}`, exponential with mean one qubit;
* `hb`, Postulate 1 with the probability rule of Sec. IV.A: a string that carries the body's
  information is one of its qubits, so the body's share at a string enters as the amplitude
  `√(E/u)`; a string carries that information when the amplitude exceeds the string's threshold,
  so the carriers are the fraction `b` of the strings whose threshold lies below it;
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
