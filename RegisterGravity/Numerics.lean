import RegisterGravity.Cosmo
import RegisterGravity.DeSitter
import RegisterGravity.Capacity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# The numbers of the paper, certified

Every number that *Gravitation from Hilbert-Space Granularity* (v11.2) computes from its inputs, in
Table I, the text, and Appendix A, recomputed from the Appendix's inputs and certified by an
interval: each theorem states `lo < quantity < hi`, and every number in the interval rounds to the
value the paper quotes.  Observational values and their uncertainties are inputs, not claims.

## Inputs (Appendix A), as exact rationals

`c = 299792458 m/s`, `ℏ = 1.054571817e-34 J s`, `k_B = 1.380649e-23 J/K`,
`G = 6.67430e-11 m³ kg⁻¹ s⁻²`, `H₀ = 67.4 km/s/Mpc` with `1 Mpc = 3.0856775814913673e22 m`,
`Ω_Λ = 0.685`, `a₀ = 1.20e-10 m/s²` with the uncertainties `±0.02 ± 0.24` [McGaugh 2016] and
`1.19 ± 0.04 ± 0.09` [Desmond 2023]; for the Sun the IAU heliocentric constant
`GM☉ = 1.32712440018e20 m³/s²` (so `M☉ = GM☉/G`), `1 au = 149597870700 m`, `R☉ = 6.957e8 m`, and
for Mercury `a = 5.7909050e10 m`, `e = 0.205630`, `T = 87.9691 d`; `1 yr = 365.25 d`;
`Ω_m = 0.315`, `q = −0.53`; the lunar-laser-ranging bound `|Ġ/G| ≲ 10⁻¹³ yr⁻¹`; Palmer's range
of `L`, `10⁶⁴` to `10¹⁰⁹`, and Davies' `10¹²²`.

## `π`, `ln 2` and `e`

`π` and `ln 2` are Mathlib's `Real.pi` and `Real.log 2`, and they enter through Mathlib's bounds
`3.141592 < π < 3.141593` (`Real.pi_gt_d6`, `Real.pi_lt_d6`) and
`0.6931471803 < ln 2 < 0.6931471808` (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`); `e` enters one
number, through `Real.exp_one_gt_d9` and `Real.exp_one_lt_d9`.  Nothing else is assumed.

## Bridge to the chain

`reg` is the register of `Chain.lean` with these inputs, `π` and `ln 2`, the cell fixed from `G`,
and `L` from the horizon.  With these choices the hypotheses of the chain hold by construction:
Jacobson's relation `hJ` (`reg_jacobson`), since the cell is fixed from `G`; the horizon at the
observed de Sitter radius (`reg_RL`), since `L` is fixed from the horizon; and the boundary
condition `hdS` for the observed `Λ` (`reg_deSitter`).  What they show is that the observed
universe meets the hypotheses together, so that the chain's quantities for these inputs are the
numbers certified here (`reg_*`).
-/

open Real

-- `norm_num` evaluates powers such as `2 ^ 41003` exactly; raise Lean's guard on large exponents.
set_option exponentiation.threshold 50000

namespace Register
namespace Numerics

local notation "c₀" => (299792458 : ℝ)
local notation "ℏ₀" => ((1054571817 : ℝ) / 10 ^ 43)
local notation "kB₀" => ((1380649 : ℝ) / 10 ^ 29)
local notation "G₀" => ((66743 : ℝ) / 10 ^ 15)
local notation "Mpc₀" => ((30856775814913673 : ℝ) * 10 ^ 6)
local notation "H₀" => ((67400 : ℝ) / ((30856775814913673 : ℝ) * 10 ^ 6))
local notation "ΩΛ₀" => ((685 : ℝ) / 1000)
local notation "a₀" => ((12 : ℝ) / 10 ^ 11)
local notation "GMs₀" => ((132712440018 : ℝ) * 10 ^ 9)
local notation "au₀" => ((149597870700 : ℝ))
local notation "yr₀" => ((31557600 : ℝ))
local notation "Rs₀" => ((6957 : ℝ) * 10 ^ 5)

lemma ln2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- Mathlib's bounds on `π` and `ln 2`, and their positivity, in the local context. -/
macro "pi_ln2" : tactic => `(tactic| (
  have := Real.pi_gt_d6; have := Real.pi_lt_d6; have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9; have := Real.pi_pos; have := Real.log_pos one_lt_two
  have := Real.pi_pos.ne'; have := (Real.log_pos one_lt_two).ne'))

lemma lt_of_sq {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 ≤ a) (h : a ^ 2 < Q ^ 2) : a < Q :=
  (pow_lt_pow_iff_left₀ ha hQ two_ne_zero).1 h

lemma lt_of_sq' {Q b : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b) (h : Q ^ 2 < b ^ 2) : Q < b :=
  (pow_lt_pow_iff_left₀ hQ hb two_ne_zero).1 h

/-! ## `π` and `ln 2` in the combinations the numbers use -/

lemma pl_lo : (3.141592 : ℝ) * 0.6931471803 < π * Real.log 2 :=
  mul_lt_mul'' Real.pi_gt_d6 Real.log_two_gt_d9 (by norm_num) (by norm_num)

lemma pl_hi : π * Real.log 2 < (3.141593 : ℝ) * 0.6931471808 :=
  mul_lt_mul'' Real.pi_lt_d6 Real.log_two_lt_d9 Real.pi_pos.le ln2_pos.le

lemma pq_lo : (3.141592 : ℝ) / 0.6931471808 < π / Real.log 2 := by
  pi_ln2
  rw [lt_div_iff₀ ln2_pos]
  have : (3.141592 : ℝ) / 0.6931471808 * Real.log 2 < 3.141592 / 0.6931471808 * 0.6931471808 :=
    mul_lt_mul_of_pos_left Real.log_two_lt_d9 (by norm_num)
  linarith [show (3.141592 : ℝ) / 0.6931471808 * 0.6931471808 = 3.141592 by norm_num]

lemma pq_hi : π / Real.log 2 < (3.141593 : ℝ) / 0.6931471803 := by
  pi_ln2
  rw [div_lt_iff₀ ln2_pos]
  have : (3.141593 : ℝ) / 0.6931471803 * 0.6931471803 < 3.141593 / 0.6931471803 * Real.log 2 :=
    mul_lt_mul_of_pos_left Real.log_two_gt_d9 (by norm_num)
  linarith [show (3.141593 : ℝ) / 0.6931471803 * 0.6931471803 = 3.141593 by norm_num]

lemma p2_lo : (3.141592 : ℝ) ^ 2 < π ^ 2 :=
  pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num) two_ne_zero

lemma p2_hi : π ^ 2 < (3.141593 : ℝ) ^ 2 :=
  pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le two_ne_zero

lemma p3q_lo : (3.141592 : ℝ) ^ 3 / 0.6931471808 < π ^ 3 / Real.log 2 := by
  have h3 : (3.141592 : ℝ) ^ 3 < π ^ 3 := pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num) (by norm_num)
  calc (3.141592 : ℝ) ^ 3 / 0.6931471808 < π ^ 3 / 0.6931471808 := by gcongr
    _ < π ^ 3 / Real.log 2 := by
      apply div_lt_div_of_pos_left (by positivity) ln2_pos Real.log_two_lt_d9

lemma p3q_hi : π ^ 3 / Real.log 2 < (3.141593 : ℝ) ^ 3 / 0.6931471803 := by
  have h3 : π ^ 3 < (3.141593 : ℝ) ^ 3 := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by norm_num)
  calc π ^ 3 / Real.log 2 < π ^ 3 / 0.6931471803 := by
        apply div_lt_div_of_pos_left (by positivity) (by norm_num) Real.log_two_gt_d9
    _ < (3.141593 : ℝ) ^ 3 / 0.6931471803 := by gcongr

/-! ## The derived quantities -/

/-- the Planck length, `ℓ_P = √(ℏG/c³)` -/
noncomputable def lP : ℝ := Real.sqrt (ℏ₀ * G₀ / c₀ ^ 3)
/-- the cell, Eq. (cell): `ℓ_c = √(π ln 2 ℏG/c³)` -/
noncomputable def lc : ℝ := Real.sqrt (π * Real.log 2 * ℏ₀ * G₀ / c₀ ^ 3)
/-- the asymptotic Hubble rate, `H_∞ = H₀√Ω_Λ` -/
noncomputable def Hinf : ℝ := H₀ * Real.sqrt ΩΛ₀
/-- the de Sitter radius, `R_Λ = c/H_∞` -/
noncomputable def RL : ℝ := c₀ / Hinf
/-- `L` from the horizon, Eq. (Lcos): `L = 2πR_Λ/ℓ_c` -/
noncomputable def Lcos : ℝ := 2 * π * RL / lc
/-- `L` from galaxies, Eq. (Lgal): `L = (π²/6)c²/(a₀ℓ_c)` -/
noncomputable def Lgal : ℝ := π ^ 2 / 6 * c₀ ^ 2 / (a₀ * lc)
/-- the galactic acceleration, Eq. (aM): `a_M = πc²/12R_Λ` -/
noncomputable def aM : ℝ := π * c₀ ^ 2 / (12 * RL)
/-- the Sun's mass in cell masses, `α = M☉/m_c = M☉cℓ_c/ℏ` with `M☉ = GM☉/G` -/
noncomputable def αs : ℝ := GMs₀ / G₀ * c₀ * lc / ℏ₀
/-- Newton's constant from `L`, Eq. (G): `G = 4πc³R_Λ²/(ℏL² ln 2)` -/
noncomputable def Gof (L : ℝ) : ℝ := 4 * π * c₀ ^ 3 * RL ^ 2 / (ℏ₀ * L ^ 2 * Real.log 2)

lemma lc_pos : 0 < lc := by pi_ln2; unfold lc; positivity

lemma lc_sq : lc ^ 2 = π * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3) := by
  pi_ln2; unfold lc; rw [Real.sq_sqrt (by positivity)]; ring

lemma lP_pos : 0 < lP := by unfold lP; positivity

lemma lP_sq : lP ^ 2 = ℏ₀ * G₀ / c₀ ^ 3 := by unfold lP; rw [Real.sq_sqrt (by positivity)]

lemma Hinf_pos : 0 < Hinf := by unfold Hinf; positivity

lemma Hinf_sq : Hinf ^ 2 = H₀ ^ 2 * ΩΛ₀ := by
  unfold Hinf; rw [mul_pow, Real.sq_sqrt (by norm_num)]

lemma RL_pos : 0 < RL := by unfold RL; have := Hinf_pos; positivity

lemma RL_sq : RL ^ 2 = c₀ ^ 2 / (H₀ ^ 2 * ΩΛ₀) := by
  unfold RL; rw [div_pow, Hinf_sq]

lemma Lcos_pos : 0 < Lcos := by
  have := lc_pos; have := RL_pos; unfold Lcos; positivity

lemma Lcos_sq : Lcos ^ 2 = π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
  pi_ln2
  unfold Lcos
  rw [div_pow, mul_pow, mul_pow, RL_sq, lc_sq]
  field_simp
  ring

lemma Lgal_pos : 0 < Lgal := by
  have := lc_pos; unfold Lgal; positivity

lemma Lgal_sq : Lgal ^ 2 = π ^ 3 / Real.log 2 * (c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀)) := by
  pi_ln2
  unfold Lgal
  simp only [div_pow, mul_pow]
  rw [lc_sq]
  field_simp
  ring

lemma aM_pos : 0 < aM := by
  have := RL_pos; unfold aM; positivity

lemma aM_sq : aM ^ 2 = π ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144) := by
  unfold aM
  rw [div_pow, mul_pow, mul_pow, RL_sq]
  field_simp
  ring

lemma αs_pos : 0 < αs := by
  have := lc_pos; unfold αs; positivity

lemma αs_sq : αs ^ 2 = π * Real.log 2 * (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) := by
  unfold αs
  rw [div_pow, mul_pow, mul_pow, lc_sq]
  field_simp

lemma Gof_eq (L : ℝ) :
    Gof L = π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * L ^ 2)) := by
  pi_ln2
  unfold Gof
  rw [RL_sq]
  field_simp

/-! ## Bridge to the chain -/

/-- The register of `Chain.lean` with the Appendix's inputs, Mathlib's `π` and `ln 2`, the cell from
`G`, and `L` from the horizon. -/
noncomputable def reg : Reg where
  c := c₀
  ℏ := ℏ₀
  kB := kB₀
  ℓc := lc
  L := Lcos
  pi := π
  ln2 := Real.log 2
  c_pos := by norm_num
  ℏ_pos := by norm_num
  kB_pos := by norm_num
  ℓc_pos := lc_pos
  L_pos := Lcos_pos
  pi_pos := Real.pi_pos
  ln2_pos := ln2_pos

/-- The horizon of Eq. (ident) is at the observed de Sitter radius, by construction: `L` is fixed
from the horizon. -/
theorem reg_RL : reg.RL = RL := by
  have := lc_pos; have := Real.pi_pos
  simp only [Reg.RL, reg]
  unfold Lcos
  field_simp

/-- The observed `Λ = 3/R_Λ²` satisfies the boundary condition of the chain: the horizon of the
solution without a mass is the register's (`Reg.deSitter`). -/
theorem reg_deSitter : reg.fSdS G₀ 0 (3 / RL ^ 2) reg.RL = 0 :=
  (reg.deSitter G₀ _).2 (by rw [reg_RL])

/-- **Jacobson's relation holds for these inputs**, by construction: with the cell fixed from the
measured `G`, the register's entropy density gives that `G` back, so the hypothesis `hJ` of every
theorem of the chain is met. -/
theorem reg_jacobson : G₀ = reg.c ^ 3 * reg.kB / (4 * reg.ℏ * reg.η) := by
  pi_ln2
  rw [Reg.eta_eq]
  simp only [reg]
  rw [lc_sq]
  field_simp

/-- **The cell is `√(π ln 2)` Planck lengths** (Eq. (cell)), from the chain's `cell_from_G`. -/
theorem reg_cell : lc = Real.sqrt (π * Real.log 2) * lP := by
  have h := (reg.cell_from_G G₀ reg_jacobson).2
  simp only [reg] at h
  rw [h]
  rfl

/-- The chain's `a_M` for these inputs is `πc²/12R_Λ` with the observed `R_Λ`. -/
theorem reg_aM : reg.aM 4 = aM := by
  rw [reg.aM_values.1, reg_RL]
  rfl

/-- The chain's `G = 4πc³R_Λ²/(ℏL² ln 2)` for these inputs is `Gof L`, and at `L_cos` it is the
measured `G` (the identity the paper notes: with `L_cos`, Eq. (G) returns its input). -/
theorem Gof_Lcos : Gof Lcos = G₀ := by
  have h := (reg.G_eq G₀ reg_jacobson).2
  rw [reg_RL] at h
  rw [h]
  rfl

/-- The chain's temperature `E_c/L` for these inputs is `ℏH_∞/2π`, Eq. (energy). -/
theorem reg_temperature : reg.Ec / reg.L = ℏ₀ * Hinf / (2 * π) := by
  have := Real.pi_pos; have := lc_pos; have := Hinf_pos
  simp only [Reg.Ec, reg]
  unfold Lcos RL
  field_simp

/-- The chain's lap time `Lt_c` for these inputs is the de Sitter period `2π/H_∞`, and its Hubble
rate `2π/Lt_c` is `H_∞`. -/
theorem reg_clock : reg.L * reg.tc = 2 * π / Hinf ∧ 2 * π / (reg.L * reg.tc) = Hinf := by
  have := Real.pi_pos; have := Hinf_pos
  have h : reg.L * reg.tc = 2 * π / Hinf := by
    rw [reg.lap_time, reg_RL]
    simp only [reg]
    unfold RL
    field_simp
  refine ⟨h, ?_⟩
  rw [h]; field_simp

/-! ## The cell and the units of the cell (Table I, Eq. (cell), Appendix A) -/

/-- A tight enclosure of the cell. -/
lemma lc_tight : 2.38504e-35 < lc ∧ lc < 2.38506e-35 := by
  constructor
  · apply lt_of_sq lc_pos.le (by norm_num)
    rw [lc_sq]
    calc (2.38504e-35 : ℝ) ^ 2 < (3.141592 * 0.6931471803) * (ℏ₀ * G₀ / c₀ ^ 3) := by norm_num
      _ < π * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3) := mul_lt_mul_of_pos_right pl_lo (by norm_num)
  · apply lt_of_sq' lc_pos.le (by norm_num)
    rw [lc_sq]
    calc π * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3) < (3.141593 * 0.6931471808) * (ℏ₀ * G₀ / c₀ ^ 3) :=
          mul_lt_mul_of_pos_right pl_hi (by norm_num)
      _ < (2.38506e-35 : ℝ) ^ 2 := by norm_num

/-- `ℓ_P = 1.616×10⁻³⁵ m` (`1.62` to three figures) and `ℓ_c = √(π ln 2) ℓ_P = 2.385×10⁻³⁵ m`
(`2.39` to three figures). -/
theorem cell_val :
    (1.6155e-35 < lP ∧ lP < 1.6165e-35) ∧ (2.38504e-35 < lc ∧ lc < 2.38506e-35) := by
  refine ⟨⟨?_, ?_⟩, lc_tight⟩
  · apply lt_of_sq lP_pos.le (by norm_num); rw [lP_sq]; norm_num
  · apply lt_of_sq' lP_pos.le (by norm_num); rw [lP_sq]; norm_num

/-- The units of the cell (Appendix A): `t_c = 7.96×10⁻⁴⁴ s`, `m_c = 1.475×10⁻⁸ kg`,
`E_c = 1.326×10⁹ J`, `a_c = 3.77×10⁵¹ m/s²`. -/
theorem cell_units :
    (7.955e-44 < lc / c₀ ∧ lc / c₀ < 7.965e-44) ∧
    (1.4745e-8 < ℏ₀ / (c₀ * lc) ∧ ℏ₀ / (c₀ * lc) < 1.4755e-8) ∧
    (1.3255e9 < ℏ₀ * c₀ / lc ∧ ℏ₀ * c₀ / lc < 1.3265e9) ∧
    (3.765e51 < c₀ ^ 2 / lc ∧ c₀ ^ 2 / lc < 3.775e51) := by
  obtain ⟨h1, h2⟩ := lc_tight
  have := lc_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-! ## The horizon (Sec. II, Sec. IV.D, Appendix A) -/

lemma Hinf_tight : 1.8078e-18 < Hinf ∧ Hinf < 1.8079e-18 := by
  constructor
  · apply lt_of_sq Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num
  · apply lt_of_sq' Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num

lemma RL_tight : 1.6583e26 < RL ∧ RL < 1.6584e26 := by
  constructor
  · apply lt_of_sq RL_pos.le (by norm_num); rw [RL_sq]; norm_num
  · apply lt_of_sq' RL_pos.le (by norm_num); rw [RL_sq]; norm_num

/-- The horizon (Appendix A, Sec. IV.C–D): `H_∞ = H₀√Ω_Λ = 1.81×10⁻¹⁸ s⁻¹`,
`Λ = 3H_∞²/c² = 1.09×10⁻⁵² m⁻²`, `R_Λ = c/H_∞ = 1.66×10²⁶ m`, and the horizon's surface gravity
`c²/R_Λ = cH_∞ = 5.4×10⁻¹⁰ m/s²`. -/
theorem horizon_val :
    (1.805e-18 < Hinf ∧ Hinf < 1.815e-18) ∧
    (1.085e-52 < 3 / RL ^ 2 ∧ 3 / RL ^ 2 < 1.095e-52) ∧
    (1.655e26 < RL ∧ RL < 1.665e26) ∧
    (5.35e-10 < c₀ ^ 2 / RL ∧ c₀ ^ 2 / RL < 5.45e-10) ∧
    c₀ ^ 2 / RL = c₀ * Hinf ∧ 3 / RL ^ 2 = 3 * Hinf ^ 2 / c₀ ^ 2 := by
  obtain ⟨h1, h2⟩ := Hinf_tight
  obtain ⟨r1, r2⟩ := RL_tight
  have hH := Hinf_pos
  have hs : c₀ ^ 2 / RL = c₀ * Hinf := by unfold RL; field_simp
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, hs, ?_⟩
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num
  · rw [hs]; nlinarith
  · rw [hs]; nlinarith
  · unfold RL; field_simp

/-! ## `L` from the horizon, and the qubit ceiling (Eqs. (Lcos), (nmax); Appendix A) -/

/-- **`L` from the horizon**, Eq. (Lcos): `L_cos = 4.37×10⁶¹` (`4.4×10⁶¹` to two figures). -/
theorem Lcos_val : 4.365e61 < Lcos ∧ Lcos < 4.375e61 := by
  constructor
  · apply lt_of_sq Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc (4.365e61 : ℝ) ^ 2
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · apply lt_of_sq' Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (4.375e61 : ℝ) ^ 2 := by norm_num

/-- A tighter enclosure of `L_cos`, for the Appendix's products. -/
lemma Lcos_tight : 4.3686e61 < Lcos ∧ Lcos < 4.3687e61 := by
  constructor
  · apply lt_of_sq Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc (4.3686e61 : ℝ) ^ 2
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · apply lt_of_sq' Lcos_pos.le (by norm_num)
    rw [Lcos_sq]
    calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (4.3687e61 : ℝ) ^ 2 := by norm_num

/-- `L_cos²` lies between `1.4435·2⁴⁰⁹` and `1.4436·2⁴⁰⁹`. -/
lemma Lcos_sq_bounds : 1.4435 * (2 : ℝ) ^ 409 < Lcos ^ 2 ∧ Lcos ^ 2 < 1.4436 * (2 : ℝ) ^ 409 := by
  rw [Lcos_sq]
  constructor
  · calc 1.4435 * (2 : ℝ) ^ 409
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < 1.4436 * (2 : ℝ) ^ 409 := by norm_num

/-- **`log₂ L_cos = 204.76`** (`204.8` to one decimal): `2⁴⁰⁹⁵¹ < L_cos²⁰⁰ < 2⁴⁰⁹⁵³`, that is,
`204.755 < log₂ L_cos < 204.765`. -/
theorem log2_Lcos : (2 : ℝ) ^ 40951 < Lcos ^ 200 ∧ Lcos ^ 200 < 2 ^ 40953 := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have e : Lcos ^ 200 = (Lcos ^ 2) ^ 100 := by ring
  rw [e]
  constructor
  · calc (2 : ℝ) ^ 40951 < (1.4435 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lcos ^ 2) ^ 100 := by gcongr
  · calc (Lcos ^ 2) ^ 100 < (1.4436 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 40953 := by norm_num

/-- **The ceiling from the horizon**: `2²⁰⁴ < L_cos < 2²⁰⁵`. -/
theorem ceiling_cos : (2 : ℝ) ^ 204 < Lcos ∧ Lcos < 2 ^ 205 := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  constructor
  · apply lt_of_sq Lcos_pos.le (by positivity)
    calc ((2 : ℝ) ^ 204) ^ 2 < 1.4435 * (2 : ℝ) ^ 409 := by norm_num
      _ < _ := h1
  · apply lt_of_sq' Lcos_pos.le (by positivity)
    calc Lcos ^ 2 < 1.4436 * (2 : ℝ) ^ 409 := h2
      _ < ((2 : ℝ) ^ 205) ^ 2 := by norm_num

/-- **`N_max = 204`**, Eq. (nmax): `2^N ≤ L_cos` exactly when `N ≤ 204` (`Capacity.ceiling` gives
`2^N ≤ L` for a random state of `N` qubits). -/
theorem nmax_cos (N : ℕ) : (2 : ℝ) ^ N ≤ Lcos ↔ N ≤ 204 :=
  Capacity.nmax_iff 204 ceiling_cos.1.le ceiling_cos.2 N

/-! ### The robustness of the ceiling (Appendix A) -/

/-- **The margins of the ceiling** (Appendix A): `2²⁰⁴` and `2²⁰⁵` lie at `0.59` and `1.18` of
`L_cos`, certified as `0.585 L_cos < 2²⁰⁴ < 0.595 L_cos` and `1.175 L_cos < 2²⁰⁵ < 1.18 L_cos`
(the values are `0.5885` and `1.1771`). -/
theorem ceiling_margins :
    (0.585 * Lcos < 2 ^ 204 ∧ (2 : ℝ) ^ 204 < 0.595 * Lcos) ∧
    (1.175 * Lcos < 2 ^ 205 ∧ (2 : ℝ) ^ 205 < 1.18 * Lcos) := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have hL := Lcos_pos
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply lt_of_sq (by positivity) (by positivity)
    calc (0.585 * Lcos) ^ 2 = 0.585 ^ 2 * Lcos ^ 2 := by ring
      _ < 0.585 ^ 2 * (1.4436 * (2 : ℝ) ^ 409) := by gcongr
      _ < ((2 : ℝ) ^ 204) ^ 2 := by norm_num
  · apply lt_of_sq (by positivity) (by positivity)
    calc ((2 : ℝ) ^ 204) ^ 2 < 0.595 ^ 2 * (1.4435 * (2 : ℝ) ^ 409) := by norm_num
      _ < 0.595 ^ 2 * Lcos ^ 2 := by gcongr
      _ = (0.595 * Lcos) ^ 2 := by ring
  · apply lt_of_sq (by positivity) (by positivity)
    calc (1.175 * Lcos) ^ 2 = 1.175 ^ 2 * Lcos ^ 2 := by ring
      _ < 1.175 ^ 2 * (1.4436 * (2 : ℝ) ^ 409) := by gcongr
      _ < ((2 : ℝ) ^ 205) ^ 2 := by norm_num
  · apply lt_of_sq (by positivity) (by positivity)
    calc ((2 : ℝ) ^ 205) ^ 2 < 1.18 ^ 2 * (1.4435 * (2 : ℝ) ^ 409) := by norm_num
      _ < 1.18 ^ 2 * Lcos ^ 2 := by gcongr
      _ = (1.18 * Lcos) ^ 2 := by ring

/-- `L` from the horizon for a Hubble rate `H` and a dark-energy fraction `Ω`: `2πR_Λ/ℓ_c` with
`R_Λ = c/(H√Ω)`. `Lof H₀ ΩΛ₀` is `L_cos`. -/
noncomputable def Lof (H Ω : ℝ) : ℝ := 2 * π * (c₀ / (H * Real.sqrt Ω)) / lc

lemma Lof_sq (H Ω : ℝ) (hH : H ≠ 0) (hΩ : 0 < Ω) :
    Lof H Ω ^ 2 = π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) := by
  pi_ln2
  have hsq : Real.sqrt Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  have hsqrt : Real.sqrt Ω ≠ 0 := (Real.sqrt_pos.2 hΩ).ne'
  unfold Lof
  rw [div_pow, mul_pow, mul_pow, div_pow, mul_pow, hsq, lc_sq]
  field_simp
  ring

lemma Lof_sq_73 :
    1.2305 * (2 : ℝ) ^ 409 < Lof (73000 / Mpc₀) ΩΛ₀ ^ 2 ∧
    Lof (73000 / Mpc₀) ΩΛ₀ ^ 2 < 1.2306 * (2 : ℝ) ^ 409 := by
  rw [Lof_sq _ _ (by norm_num) (by norm_num)]
  constructor
  · calc 1.2305 * (2 : ℝ) ^ 409
        < (3.141592 / 0.6931471808) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀))) := by norm_num
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀)))
        < (3.141593 / 0.6931471803) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((73000 / Mpc₀) ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < 1.2306 * (2 : ℝ) ^ 409 := by norm_num

/-- **`log₂ L = 204.65` at the local `H₀ = 73 km/s/Mpc`** (Appendix A): `2⁴⁰⁹²⁹ < L²⁰⁰ < 2⁴⁰⁹³¹`,
that is, `204.645 < log₂ L < 204.655`; the ceiling is `204` at this `H₀` too. -/
theorem log2_L73 :
    (2 : ℝ) ^ 40929 < Lof (73000 / Mpc₀) ΩΛ₀ ^ 200 ∧
    Lof (73000 / Mpc₀) ΩΛ₀ ^ 200 < 2 ^ 40931 := by
  obtain ⟨h1, h2⟩ := Lof_sq_73
  have e : Lof (73000 / Mpc₀) ΩΛ₀ ^ 200 = (Lof (73000 / Mpc₀) ΩΛ₀ ^ 2) ^ 100 := by ring
  rw [e]
  constructor
  · calc (2 : ℝ) ^ 40929 < (1.2305 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lof (73000 / Mpc₀) ΩΛ₀ ^ 2) ^ 100 := by gcongr
  · calc (Lof (73000 / Mpc₀) ΩΛ₀ ^ 2) ^ 100 < (1.2306 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 40931 := by norm_num

/-- **Planck's uncertainties move `log₂ L_cos` by about `±0.02`** (Appendix A): for `H₀` within
`±0.5 km/s/Mpc` of `67.4` and `Ω_Λ` within `±0.007` of `0.685`, `2⁴⁰⁹⁴⁹ < L²⁰⁰ < 2⁴⁰⁹⁵⁷`, that is,
`204.745 < log₂ L < 204.785`, against `log₂ L_cos = 204.76` (`log2_Lcos`); the ceiling is `204`
throughout the band. -/
theorem log2_planck_band (H Ω : ℝ) (hH1 : 66900 / Mpc₀ ≤ H) (hH2 : H ≤ 67900 / Mpc₀)
    (hΩ1 : 0.678 ≤ Ω) (hΩ2 : Ω ≤ 0.692) :
    (2 : ℝ) ^ 40949 < Lof H Ω ^ 200 ∧ Lof H Ω ^ 200 < 2 ^ 40957 := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH1
  have hΩpos : 0 < Ω := lt_of_lt_of_le (by norm_num) hΩ1
  have hsq := Lof_sq H Ω hHpos.ne' hΩpos
  have hlo : (66900 / Mpc₀) ^ 2 * 0.678 ≤ H ^ 2 * Ω :=
    mul_le_mul (pow_le_pow_left₀ (by norm_num) hH1 2) hΩ1 (by norm_num) (by positivity)
  have hhi : H ^ 2 * Ω ≤ (67900 / Mpc₀) ^ 2 * 0.692 :=
    mul_le_mul (pow_le_pow_left₀ hHpos.le hH2 2) hΩ2 hΩpos.le (by positivity)
  have hpos : 0 < H ^ 2 * Ω := by positivity
  have hL2lo : 1.4079 * (2 : ℝ) ^ 409 < Lof H Ω ^ 2 := by
    rw [hsq]
    calc 1.4079 * (2 : ℝ) ^ 409
        < (3.141592 / 0.6931471808) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((67900 / Mpc₀) ^ 2 * 0.692))) := by norm_num
      _ ≤ (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) := by
          gcongr
      _ < π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) :=
          mul_lt_mul_of_pos_right pq_lo (by positivity)
  have hL2hi : Lof H Ω ^ 2 < 1.4805 * (2 : ℝ) ^ 409 := by
    rw [hsq]
    calc π / Real.log 2 * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω)))
        < (3.141593 / 0.6931471803) * (4 * c₀ ^ 5 / (ℏ₀ * G₀ * (H ^ 2 * Ω))) :=
          mul_lt_mul_of_pos_right pq_hi (by positivity)
      _ ≤ (3.141593 / 0.6931471803) *
            (4 * c₀ ^ 5 / (ℏ₀ * G₀ * ((66900 / Mpc₀) ^ 2 * 0.678))) := by
          gcongr
      _ < 1.4805 * (2 : ℝ) ^ 409 := by norm_num
  have e : Lof H Ω ^ 200 = (Lof H Ω ^ 2) ^ 100 := by ring
  rw [e]
  constructor
  · calc (2 : ℝ) ^ 40949 < (1.4079 * (2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lof H Ω ^ 2) ^ 100 := by gcongr
  · calc (Lof H Ω ^ 2) ^ 100 < (1.4805 * (2 : ℝ) ^ 409) ^ 100 := by gcongr
      _ < 2 ^ 40957 := by norm_num

/-- The Appendix's powers of two: `2²⁰⁴ = 2.57×10⁶¹`, `2²⁰⁵ = 5.14×10⁶¹`, `2²¹² = 6.58×10⁶³`,
`2²¹³ = 1.32×10⁶⁴`. -/
theorem powers_of_two :
    ((2.565e61 : ℝ) < 2 ^ 204 ∧ (2 : ℝ) ^ 204 < 2.575e61) ∧
    ((5.135e61 : ℝ) < 2 ^ 205 ∧ (2 : ℝ) ^ 205 < 5.145e61) ∧
    ((6.575e63 : ℝ) < 2 ^ 212 ∧ (2 : ℝ) ^ 212 < 6.585e63) ∧
    ((1.315e64 : ℝ) < 2 ^ 213 ∧ (2 : ℝ) ^ 213 < 1.325e64) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩⟩

/-- **Palmer's bit count** `2^(N+1) − 2 ≤ NL` (Sec. V, Appendix A): with `L_cos` it holds at
`N = 211`, `2²¹² ≤ 211L_cos = 9.22×10⁶³`, and fails at `N = 212`, `2²¹³ > 212L_cos = 9.26×10⁶³`;
so it holds exactly for `N ≤ 211` (`Capacity.palmer_threshold`). -/
theorem palmer_211 :
    ((2 : ℝ) ^ 212 - 2 ≤ 211 * Lcos ∧ 212 * Lcos < 2 ^ 213 - 2) ∧
    (9.215e63 < 211 * Lcos ∧ 211 * Lcos < 9.225e63) ∧
    (9.255e63 < 212 * Lcos ∧ 212 * Lcos < 9.265e63) ∧
    ∀ N : ℕ, (2 : ℝ) ^ (N + 1) - 2 ≤ N * Lcos ↔ N ≤ 211 := by
  obtain ⟨h1, h2⟩ := Lcos_tight
  have hyes : (2 : ℝ) ^ 212 - 2 ≤ 211 * Lcos := by
    have : (2 : ℝ) ^ 212 - 2 ≤ 211 * 4.3686e61 := by norm_num
    linarith
  have hno : 212 * Lcos < (2 : ℝ) ^ 213 - 2 := by
    have : 212 * 4.3687e61 < (2 : ℝ) ^ 213 - 2 := by norm_num
    linarith
  refine ⟨⟨hyes, hno⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  intro N
  refine Capacity.palmer_threshold Lcos Lcos_pos 211 (by norm_num) ?_ ?_ N
  · push_cast; exact hyes
  · push_cast; norm_num; linarith

/-- **Palmer's range of `L`** (Sec. V): the ceiling `⌊log₂ L⌋` is `212` for `L = 10⁶⁴`, "near 210",
and `362` for `L = 10¹⁰⁹`, "near 360"; and `L_cos` lies below the smaller. -/
theorem palmer_range :
    ((2 : ℝ) ^ 212 < 10 ^ 64 ∧ (10 : ℝ) ^ 64 < 2 ^ 213) ∧
    ((2 : ℝ) ^ 362 < 10 ^ 109 ∧ (10 : ℝ) ^ 109 < 2 ^ 363) ∧ Lcos < 10 ^ 64 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  have := Lcos_val.2
  linarith [show (4.375e61 : ℝ) < 10 ^ 64 by norm_num]

/-! ## The horizon's counts, and Davies (Sec. II, Sec. V, Appendix A) -/

/-- **The horizon's counts**, Eq. (counts) to leading order: `L²/2 = 9.5×10¹²²` cells,
`L²/4 = 4.8×10¹²²` rings, and the entropy `(L²/4) ln 2 = 3.3×10¹²²`, which equals `πR_Λ²/ℓ_P²`. -/
theorem horizon_counts :
    (9.45e122 < Lcos ^ 2 / 2 ∧ Lcos ^ 2 / 2 < 9.55e122) ∧
    (4.75e122 < Lcos ^ 2 / 4 ∧ Lcos ^ 2 / 4 < 4.85e122) ∧
    (3.25e122 < Lcos ^ 2 / 4 * Real.log 2 ∧ Lcos ^ 2 / 4 * Real.log 2 < 3.35e122) ∧
    Lcos ^ 2 / 4 * Real.log 2 = π * RL ^ 2 / lP ^ 2 := by
  pi_ln2
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have e : Lcos ^ 2 / 4 * Real.log 2 = π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [Lcos_sq]; field_simp
  have e2 : π * RL ^ 2 / lP ^ 2 = π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [RL_sq, lP_sq]; field_simp
  have b1 : (1.4435 * (2 : ℝ) ^ 409) / 2 > 9.45e122 := by norm_num
  have b2 : (1.4436 * (2 : ℝ) ^ 409) / 2 < 9.55e122 := by norm_num
  have b3 : (1.4435 * (2 : ℝ) ^ 409) / 4 > 4.75e122 := by norm_num
  have b4 : (1.4436 * (2 : ℝ) ^ 409) / 4 < 4.85e122 := by norm_num
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, by rw [e, e2]⟩
  · rw [e]
    calc (3.25e122 : ℝ) < 3.141592 * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right Real.pi_gt_d6 (by norm_num)
  · rw [e]
    calc π * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)))
        < 3.141593 * (c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right Real.pi_lt_d6 (by norm_num)
      _ < (3.35e122 : ℝ) := by norm_num

/-- The chain's entropy for these inputs is the same number: `(L²/4) ln 2 = πR_Λ²/ℓ_P²`
(`Reg.entropy_quarter`). -/
theorem reg_entropy : reg.Shor = Lcos ^ 2 / 4 * Real.log 2 := by
  simp only [Reg.Shor, Reg.Rhor, reg]

/-- **Davies** (Sec. V): `log₂ 10¹²² ≈ 405` (`2⁸¹⁰ < 10²⁴⁴ < 2⁸¹¹`, that is,
`405 < log₂ 10¹²² < 405.5`), and the logarithm of the horizon's `L²/4` rings is
`2 log₂ L − 2 = 407.5`: `2⁸¹⁴⁹ < (L²/4)²⁰ < 2⁸¹⁵¹`, that is, `407.45 < log₂(L²/4) < 407.55`. -/
theorem davies :
    ((2 : ℝ) ^ 810 < 10 ^ 244 ∧ (10 : ℝ) ^ 244 < 2 ^ 811) ∧
    ((2 : ℝ) ^ 8149 < (Lcos ^ 2 / 4) ^ 20 ∧ (Lcos ^ 2 / 4) ^ 20 < 2 ^ 8151) := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · calc (2 : ℝ) ^ 8149 < (1.4435 * (2 : ℝ) ^ 409 / 4) ^ 20 := by norm_num
      _ < (Lcos ^ 2 / 4) ^ 20 := by gcongr
  · calc (Lcos ^ 2 / 4) ^ 20 < (1.4436 * (2 : ℝ) ^ 409 / 4) ^ 20 := by gcongr
      _ < 2 ^ 8151 := by norm_num

/-! ## Newton's constant from the ceiling (Sec. V, Prediction 2, Appendix A) -/

/-- **The bracket**: Eq. (G) with `L = 2²⁰⁴` and `2²⁰⁵` gives `1.93×10⁻¹⁰` and `4.82×10⁻¹¹`
(`1.9×10⁻¹⁰` and `4.8×10⁻¹¹` to two figures), and the measured `G` lies strictly between them:
not in the bracket of a ceiling of `205`, `[G(2²⁰⁶), G(2²⁰⁵)]`, which every higher ceiling's
bracket lies below, nor in that of `203`, `[G(2²⁰⁴), G(2²⁰³)]`. -/
theorem G_bracket :
    (1.925e-10 < Gof (2 ^ 204) ∧ Gof (2 ^ 204) < 1.935e-10) ∧
    (4.815e-11 < Gof (2 ^ 205) ∧ Gof (2 ^ 205) < 4.825e-11) ∧
    (Gof (2 ^ 205) < G₀ ∧ G₀ < Gof (2 ^ 204)) := by
  rw [Gof_eq, Gof_eq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · calc (1.925e-10 : ℝ)
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 204) ^ 2)) := by
          norm_num
      _ < _ := mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc _ < (3.141593 / 0.6931471803) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 204) ^ 2)) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (1.935e-10 : ℝ) := by norm_num
  · calc (4.815e-11 : ℝ)
        < (3.141592 / 0.6931471808) * (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 205) ^ 2)) := by
          norm_num
      _ < _ := mul_lt_mul_of_pos_right pq_lo (by norm_num)
  · calc _ < (3.141593 / 0.6931471803) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 205) ^ 2)) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < (4.825e-11 : ℝ) := by norm_num
  · calc _ < (3.141593 / 0.6931471803) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 205) ^ 2)) :=
          mul_lt_mul_of_pos_right pq_hi (by norm_num)
      _ < G₀ := by norm_num
  · calc G₀ < (3.141592 / 0.6931471808) *
          (4 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * ((2 : ℝ) ^ 204) ^ 2)) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right pq_lo (by norm_num)

/-- **A factor of two in `L` is a factor of four in `G`** (Sec. V): `G(2^N) = 4G(2^(N+1))`, so a
measured ceiling, `2^N ≤ L < 2^(N+1)`, returns `ℓ_c = 2πR_Λ/L` to a factor of two and `G` to a
factor of four. -/
theorem Gof_factor_four (N : ℕ) : Gof (2 ^ N) = 4 * Gof (2 ^ (N + 1)) := by
  rw [Gof_eq, Gof_eq, pow_succ]
  field_simp
  ring

/-- **`G` falls as `L` grows**: Eq. (G) goes as `1/L²`, so for `0 < L₁ ≤ L₂`, `G(L₂) ≤ G(L₁)`. -/
theorem Gof_antitone {L₁ L₂ : ℝ} (h1 : 0 < L₁) (h12 : L₁ ≤ L₂) : Gof L₂ ≤ Gof L₁ := by
  pi_ln2
  unfold Gof
  have hR := RL_pos
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : L₁ ^ 2 ≤ L₂ ^ 2 := pow_le_pow_left₀ h1.le h12 2
  have hℏ : (0 : ℝ) < ℏ₀ := by norm_num
  nlinarith [this, hℏ, Real.log_pos one_lt_two]

/-- **A ceiling of `205` or more falsifies Eq. (G)** (Sec. V, Prediction 2): for every `N ≥ 205`
the bracket `[G(2^(N+1)), G(2^N)]` lies below the measured `G`, since `G(2^N) ≤ G(2²⁰⁵) < G₀`. -/
theorem ceiling_above_204 (N : ℕ) (hN : 205 ≤ N) : Gof (2 ^ N) < G₀ := by
  have h205 : Gof (2 ^ 205) < G₀ := G_bracket.2.2.1
  have hle : Gof (2 ^ N) ≤ Gof (2 ^ 205) :=
    Gof_antitone (by positivity) (pow_le_pow_right₀ (by norm_num) hN)
  exact lt_of_le_of_lt hle h205

/-! ## The solar scale (Sec. IV.B–C, Table I, Appendix A) -/

/-- The chain's `α` for the Sun, its mass in cell masses `M☉/m_c` with `M☉ = GM☉/G`, is `αs`. -/
theorem reg_αs : reg.α (GMs₀ / G₀) = αs := by
  have := lc_pos
  simp only [Reg.α, Reg.mc, reg]
  unfold αs
  field_simp

/-- **The Sun** (Sec. IV.C, Table I, Appendix A): `α = M☉/m_c = 1.35×10³⁸`; the horizon is drawn
in by `GM☉/c²ℓ_c = α/(π ln 2) = 6.19×10³⁷` cells (`Reg.shift_in_cells`); the entropy the Sun
removes is `Lα = 5.9×10⁹⁹`, and `5.9×10¹¹⁰` for a galaxy of `10¹¹ M☉`. -/
theorem sun_counts :
    (1.345e38 < αs ∧ αs < 1.355e38) ∧
    GMs₀ / (c₀ ^ 2 * lc) = αs / (π * Real.log 2) ∧
    (6.185e37 < αs / (π * Real.log 2) ∧ αs / (π * Real.log 2) < 6.195e37) ∧
    (5.85e99 < Lcos * αs ∧ Lcos * αs < 5.95e99) ∧
    (5.85e110 < Lcos * (1e11 * αs) ∧ Lcos * (1e11 * αs) < 5.95e110) := by
  pi_ln2
  have ha := αs_pos; have hL := Lcos_pos; have hl := lc_pos
  have hshift : GMs₀ / (c₀ ^ 2 * lc) = αs / (π * Real.log 2) := by
    have h := reg.shift_in_cells G₀ (GMs₀ / G₀) reg_jacobson
    rw [reg_αs] at h
    simp only [reg] at h
    have e : G₀ * (GMs₀ / G₀) / c₀ ^ 2 = GMs₀ / c₀ ^ 2 := by field_simp
    rw [e] at h
    rw [div_mul_eq_div_div, h]
    field_simp
  have hα : 1.345e38 < αs ∧ αs < 1.355e38 := by
    constructor
    · apply lt_of_sq ha.le (by norm_num)
      rw [αs_sq]
      calc (1.345e38 : ℝ) ^ 2 < (3.141592 * 0.6931471803) * (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) := by
            norm_num
        _ < _ := mul_lt_mul_of_pos_right pl_lo (by norm_num)
    · apply lt_of_sq' ha.le (by norm_num)
      rw [αs_sq]
      calc _ < (3.141593 * 0.6931471808) * (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) :=
            mul_lt_mul_of_pos_right pl_hi (by norm_num)
        _ < (1.355e38 : ℝ) ^ 2 := by norm_num
  -- `(α/π ln 2)² = (GM☉²/Gcℏ)/(π ln 2)`
  have eα : (αs / (π * Real.log 2)) ^ 2 = (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) / (π * Real.log 2) := by
    rw [div_pow, αs_sq]; field_simp
  -- `(Lα)² = π² · 4c⁴GM☉²/(ℏ²G²H²Ω_Λ)`
  have eL : (Lcos * αs) ^ 2 = π ^ 2 * (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [mul_pow, Lcos_sq, αs_sq]; field_simp
  have hLα : 5.85e99 < Lcos * αs ∧ Lcos * αs < 5.95e99 := by
    constructor
    · apply lt_of_sq (by positivity) (by norm_num)
      rw [eL]
      calc (5.85e99 : ℝ) ^ 2 < (3.141592 : ℝ) ^ 2 *
            (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
        _ < _ := mul_lt_mul_of_pos_right p2_lo (by norm_num)
    · apply lt_of_sq' (by positivity) (by norm_num)
      rw [eL]
      calc _ < (3.141593 : ℝ) ^ 2 *
            (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) :=
            mul_lt_mul_of_pos_right p2_hi (by norm_num)
        _ < (5.95e99 : ℝ) ^ 2 := by norm_num
  have eg : Lcos * (1e11 * αs) = 1e11 * (Lcos * αs) := by ring
  refine ⟨hα, hshift, ⟨?_, ?_⟩, hLα, ?_, ?_⟩
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [eα]
    calc (6.185e37 : ℝ) ^ 2 < (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) / (3.141593 * 0.6931471808) := by
          norm_num
      _ < _ := div_lt_div_of_pos_left (by norm_num) (by positivity) pl_hi
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [eα]
    calc _ < (GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀)) / (3.141592 * 0.6931471803) :=
          div_lt_div_of_pos_left (by norm_num) (by norm_num) pl_lo
      _ < (6.195e37 : ℝ) ^ 2 := by norm_num
  · rw [eg]; linarith [hLα.1]
  · rw [eg]; linarith [hLα.2]

/-- The chain's entropy removed by the Sun, `Lα = 2πM☉cR_Λ/ℏ` (`Reg.entropy_removed`), for these
inputs. -/
theorem reg_sun_entropy : reg.L * reg.α (GMs₀ / G₀) = Lcos * αs := by
  rw [reg_αs]; rfl

/-- **The Earth's orbit** (Sec. IV.B, Table I, Appendix A): `n = 1 au/ℓ_c = 6.27×10⁴⁵`, and
`a_cα/(πn² ln 2) = GM☉/r² = 5.93×10⁻³ m/s²` (the chain's Eq. (newton), `reg_newton_earth`); the
push there is `c²r/R_Λ² = 4.9×10⁻²⁵ m/s²` (`5×10⁻²⁵` to one figure). -/
theorem earth_orbit :
    (6.265e45 < au₀ / lc ∧ au₀ / lc < 6.275e45) ∧
    (5.925e-3 < GMs₀ / au₀ ^ 2 ∧ GMs₀ / au₀ ^ 2 < 5.935e-3) ∧
    (4.85e-25 < c₀ ^ 2 * au₀ / RL ^ 2 ∧ c₀ ^ 2 * au₀ / RL ^ 2 < 4.95e-25) := by
  pi_ln2
  have hl := lc_pos
  have e : (au₀ / lc) ^ 2 = au₀ ^ 2 / (ℏ₀ * G₀ / c₀ ^ 3) / (π * Real.log 2) := by
    rw [div_pow, lc_sq]; field_simp
  refine ⟨⟨?_, ?_⟩, ⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [e]
    calc (6.265e45 : ℝ) ^ 2 < au₀ ^ 2 / (ℏ₀ * G₀ / c₀ ^ 3) / (3.141593 * 0.6931471808) := by
          norm_num
      _ < _ := div_lt_div_of_pos_left (by norm_num) (by positivity) pl_hi
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [e]
    calc _ < au₀ ^ 2 / (ℏ₀ * G₀ / c₀ ^ 3) / (3.141592 * 0.6931471803) :=
          div_lt_div_of_pos_left (by norm_num) (by norm_num) pl_lo
      _ < (6.275e45 : ℝ) ^ 2 := by norm_num
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num

/-- The chain's Newton's law in cells, `a/a_c = α/(πn² ln 2)` (`Reg.newton`), for the Sun at 1 au
is `GM☉/r²`. -/
theorem reg_newton_earth :
    reg.ac * (reg.α (GMs₀ / G₀) / (reg.pi * reg.n au₀ ^ 2 * reg.ln2)) = GMs₀ / au₀ ^ 2 := by
  have hr : (0 : ℝ) < au₀ := by norm_num
  have ha0 : (0 : ℝ) < GMs₀ / au₀ ^ 2 := by positivity
  have ha : GMs₀ / au₀ ^ 2 = reg.gSdS G₀ (GMs₀ / G₀) 0 au₀ := by
    rw [reg.gSdS_mass _ _ _ hr.ne']; field_simp
  have I1 : reg.kB * (reg.ℏ / (reg.La (GMs₀ / au₀ ^ 2) * reg.tc) / reg.kB)
      = reg.ℏ / (reg.La (GMs₀ / au₀ ^ 2) * reg.tc) := by
    have := reg.kB_pos.ne'; field_simp
  have h := (reg.newton G₀ (GMs₀ / G₀) au₀ (GMs₀ / au₀ ^ 2) _ hr ha0 reg_jacobson ha I1).2.2
  have hac : reg.ac ≠ 0 := by
    have := reg.c_pos; have := reg.ℓc_pos; unfold Reg.ac; positivity
  unfold Reg.α
  rw [← h]
  field_simp

/-- **Mercury and the deflection of light** (Sec. IV.B): the anomalous advance
`6πGM☉/(a(1−e²)c²)` is `5.0×10⁻⁷ rad` per orbit and `42.98″` per century (the `π` of the advance
cancels the `π` of the conversion to arcseconds); the deflection of starlight at the solar limb
`4GM☉/(c²R☉)` is `1.75″`. -/
theorem solar_tests :
    (5.0e-7 < 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) ∧
      6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) < 5.05e-7) ∧
    (42.975 < 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
        (648000 / π) ∧
      6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
        (648000 / π) < 42.985) ∧
    (1.75 < 4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / π) ∧
      4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / π) < 1.755) := by
  pi_ln2
  have e : 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
      (648000 / π) = 6 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
      648000 := by field_simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · calc (5.0e-7 : ℝ) < 6 * 3.141592 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) := by
          norm_num
      _ < _ := by gcongr
  · calc _ < 6 * 3.141593 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) := by gcongr
      _ < (5.05e-7 : ℝ) := by norm_num
  · rw [e]; norm_num
  · rw [e]; norm_num
  · calc (1.75 : ℝ) < 4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / 3.141593) := by norm_num
      _ < _ := by gcongr
  · calc _ < 4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / 3.141592) := by gcongr
      _ < (1.755 : ℝ) := by norm_num

/-- **The phase grid** (Sec. IV.B): the kinematic effect of a `2π/L` grid, `1.4×10⁻⁶¹ rad`
(`∼10⁻⁶¹`), lies fifty-four orders of magnitude below Mercury's `5×10⁻⁷ rad` per orbit: the ratio
is between `10⁵⁴` and `10⁵⁵`. -/
theorem phase_grid :
    (1.43e-61 < 2 * π / Lcos ∧ 2 * π / Lcos < 1.44e-61) ∧
    (10 ^ 54 < 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * π / Lcos) ∧
      6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * π / Lcos) < 10 ^ 55) := by
  pi_ln2
  obtain ⟨h1, h2⟩ := Lcos_val
  have hL := Lcos_pos
  have e : 6 * π * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * π / Lcos)
      = 3 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * Lcos := by
    field_simp; norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hL]; nlinarith
  · rw [div_lt_iff₀ hL]; nlinarith
  · rw [e]; nlinarith
  · rw [e]; nlinarith

/-- **Where the Sun's sphere stops being saturated** (Sec. IV.B): the crossing of Eq. (criterion),
`GM☉/r² = c²/πR_Λ`, lies at `r² = πGM☉R_Λ/c²`, `5900 au` from the Sun. -/
theorem sun_crossing :
    (5850 * au₀) ^ 2 < π * GMs₀ * RL / c₀ ^ 2 ∧ π * GMs₀ * RL / c₀ ^ 2 < (5950 * au₀) ^ 2 := by
  pi_ln2
  obtain ⟨r1, r2⟩ := RL_tight
  have hR := RL_pos
  constructor
  · have : (5850 * au₀) ^ 2 < 3.141592 * GMs₀ * 1.6583e26 / c₀ ^ 2 := by norm_num
    have h2 : 3.141592 * GMs₀ * 1.6583e26 / c₀ ^ 2 < π * GMs₀ * RL / c₀ ^ 2 := by
      gcongr
    linarith
  · have : 3.141593 * GMs₀ * 1.6584e26 / c₀ ^ 2 < (5950 * au₀) ^ 2 := by norm_num
    have h2 : π * GMs₀ * RL / c₀ ^ 2 < 3.141593 * GMs₀ * 1.6584e26 / c₀ ^ 2 := by
      gcongr
    linarith

/-! ## The galactic scale (Sec. IV.C, Table I, Appendix A) -/

/-- **Eq. (aM)**: `a_M = πc²/12R_Λ = 1.42×10⁻¹⁰ m/s²` (`1.4` to two figures), and Verlinde's
`c²/6R_Λ = 0.90×10⁻¹⁰`. -/
theorem aM_val :
    (1.415e-10 < aM ∧ aM < 1.425e-10) ∧
    (0.895e-10 < c₀ ^ 2 / (6 * RL) ∧ c₀ ^ 2 / (6 * RL) < 0.905e-10) := by
  have hR := RL_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq aM_pos.le (by norm_num)
    rw [aM_sq]
    calc (1.415e-10 : ℝ) ^ 2 < (3.141592 : ℝ) ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right p2_lo (by norm_num)
  · apply lt_of_sq' aM_pos.le (by norm_num)
    rw [aM_sq]
    calc _ < (3.141593 : ℝ) ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144) :=
          mul_lt_mul_of_pos_right p2_hi (by norm_num)
      _ < (1.425e-10 : ℝ) ^ 2 := by norm_num
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num

/-- A tighter enclosure of `a_M`. -/
lemma aM_tight : 1.4188e-10 < aM ∧ aM < 1.4189e-10 := by
  constructor
  · apply lt_of_sq aM_pos.le (by norm_num)
    rw [aM_sq]
    calc (1.4188e-10 : ℝ) ^ 2 < (3.141592 : ℝ) ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right p2_lo (by norm_num)
  · apply lt_of_sq' aM_pos.le (by norm_num)
    rw [aM_sq]
    calc _ < (3.141593 : ℝ) ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144) :=
          mul_lt_mul_of_pos_right p2_hi (by norm_num)
      _ < (1.4189e-10 : ℝ) ^ 2 := by norm_num

/-- The chain's `a_M` with these inputs (`reg_aM`) is the same number. -/
theorem reg_aM_val : 1.415e-10 < reg.aM 4 ∧ reg.aM 4 < 1.425e-10 := by
  rw [reg_aM]; exact aM_val.1

/-- **Against observation** (Sec. IV.C, Table I): `a₀/a_M = 0.85`, "observation reaches 85%
of the bound"; `(a_M − 1.20)/0.24 = 0.9σ` [McGaugh 2016] and `(a_M − 1.19)/0.10 = 2.3σ`
[Desmond 2023], with the total uncertainties `√(0.02² + 0.24²) = 0.24` and `√(0.04² + 0.09²) =
0.10`. -/
theorem aM_vs_observation :
    (0.845 < a₀ / aM ∧ a₀ / aM < 0.855) ∧
    (0.85 < (aM - a₀) / 0.24e-10 ∧ (aM - a₀) / 0.24e-10 < 0.95) ∧
    (2.25 < (aM - 1.19e-10) / 0.10e-10 ∧ (aM - 1.19e-10) / 0.10e-10 < 2.35) ∧
    (0.235 < Real.sqrt (0.02 ^ 2 + 0.24 ^ 2) ∧ Real.sqrt (0.02 ^ 2 + 0.24 ^ 2) < 0.245) ∧
    (0.095 < Real.sqrt (0.04 ^ 2 + 0.09 ^ 2) ∧ Real.sqrt (0.04 ^ 2 + 0.09 ^ 2) < 0.105) := by
  obtain ⟨t1, t2⟩ := aM_tight
  have ha := aM_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ ha]; nlinarith
  · rw [div_lt_iff₀ ha]; nlinarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The coefficients** (Sec. IV.C, Appendix A), in units of `cH_∞ = c²/R_Λ`:
`a₀/cH_∞ = 0.22 ± 0.04` measured [McGaugh 2016] and `0.22 ± 0.02` [Desmond 2023]; `π/12 = 0.26`
here and `1/6 = 0.17` Verlinde. -/
theorem coefficients :
    (0.215 < a₀ / (c₀ * Hinf) ∧ a₀ / (c₀ * Hinf) < 0.225) ∧
    (0.035 < 0.24e-10 / (c₀ * Hinf) ∧ 0.24e-10 / (c₀ * Hinf) < 0.045) ∧
    (0.215 < 1.19e-10 / (c₀ * Hinf) ∧ 1.19e-10 / (c₀ * Hinf) < 0.225) ∧
    (0.015 < 0.10e-10 / (c₀ * Hinf) ∧ 0.10e-10 / (c₀ * Hinf) < 0.025) ∧
    (0.255 < π / 12 ∧ π / 12 < 0.265) ∧ (0.165 < (1 : ℝ) / 6 ∧ (1 : ℝ) / 6 < 0.175) := by
  pi_ln2
  obtain ⟨k1, k2⟩ := Hinf_tight
  have hH := Hinf_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨by linarith, by linarith⟩,
    ⟨by norm_num, by norm_num⟩⟩
  all_goals first
    | (rw [lt_div_iff₀ (by positivity)]; nlinarith)
    | (rw [div_lt_iff₀ (by positivity)]; nlinarith)

/-- **`L` from galaxies**, Eq. (Lgal): `L_gal = 5.17×10⁶¹` (`5.2×10⁶¹` to two figures). -/
theorem Lgal_val : 5.165e61 < Lgal ∧ Lgal < 5.175e61 := by
  constructor
  · apply lt_of_sq Lgal_pos.le (by norm_num)
    rw [Lgal_sq]
    calc (5.165e61 : ℝ) ^ 2 < ((3.141592 : ℝ) ^ 3 / 0.6931471808) *
          (c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀)) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right p3q_lo (by norm_num)
  · apply lt_of_sq' Lgal_pos.le (by norm_num)
    rw [Lgal_sq]
    calc _ < ((3.141593 : ℝ) ^ 3 / 0.6931471803) * (c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀)) :=
          mul_lt_mul_of_pos_right p3q_hi (by norm_num)
      _ < (5.175e61 : ℝ) ^ 2 := by norm_num

/-- `L_gal²` lies between `1.009·2⁴¹⁰` and `1.0091·2⁴¹⁰`. -/
lemma Lgal_sq_bounds : 1.009 * (2 : ℝ) ^ 410 < Lgal ^ 2 ∧ Lgal ^ 2 < 1.0091 * (2 : ℝ) ^ 410 := by
  rw [Lgal_sq]
  constructor
  · calc 1.009 * (2 : ℝ) ^ 410 < ((3.141592 : ℝ) ^ 3 / 0.6931471808) *
          (c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀)) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right p3q_lo (by norm_num)
  · calc _ < ((3.141593 : ℝ) ^ 3 / 0.6931471803) * (c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀)) :=
          mul_lt_mul_of_pos_right p3q_hi (by norm_num)
      _ < 1.0091 * (2 : ℝ) ^ 410 := by norm_num

/-- **`log₂ L_gal = 205.01`** (`205.0` to one decimal): `2⁴¹⁰⁰¹ < L_gal²⁰⁰ < 2⁴¹⁰⁰³`, that is,
`205.005 < log₂ L_gal < 205.015`; and `L_gal` lies just above `2²⁰⁵`, by less than a hundredth of a
bit: `2²⁰⁵ < L_gal` and `L_gal¹⁰⁰ < 2²⁰⁵⁰¹`. -/
theorem log2_Lgal :
    ((2 : ℝ) ^ 41001 < Lgal ^ 200 ∧ Lgal ^ 200 < 2 ^ 41003) ∧
    ((2 : ℝ) ^ 205 < Lgal ∧ Lgal ^ 100 < 2 ^ 20501) := by
  obtain ⟨h1, h2⟩ := Lgal_sq_bounds
  have e2 : Lgal ^ 200 = (Lgal ^ 2) ^ 100 := by ring
  have e1 : Lgal ^ 100 = (Lgal ^ 2) ^ 50 := by ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [e2]
    calc (2 : ℝ) ^ 41001 < (1.009 * (2 : ℝ) ^ 410) ^ 100 := by norm_num
      _ < (Lgal ^ 2) ^ 100 := by gcongr
  · rw [e2]
    calc (Lgal ^ 2) ^ 100 < (1.0091 * (2 : ℝ) ^ 410) ^ 100 := by gcongr
      _ < 2 ^ 41003 := by norm_num
  · apply lt_of_sq Lgal_pos.le (by positivity)
    calc ((2 : ℝ) ^ 205) ^ 2 < 1.009 * (2 : ℝ) ^ 410 := by norm_num
      _ < _ := h1
  · rw [e1]
    calc (Lgal ^ 2) ^ 50 < (1.0091 * (2 : ℝ) ^ 410) ^ 50 := by gcongr
      _ < 2 ^ 20501 := by norm_num

/-- **The two pins agree to 18%, a quarter of a bit** (Sec. V): `L_gal/L_cos = 1.18`,
with `2²⁴ < (L_gal/L_cos)¹⁰⁰ < 2²⁵`, that is, `0.24 < log₂(L_gal/L_cos) < 0.25`; and
`L_cos/L_gal = 0.85`: the value lies inside the bound at 85%. -/
theorem pins_agree :
    (1.175 < Lgal / Lcos ∧ Lgal / Lcos < 1.185) ∧
    ((2 : ℝ) ^ 24 < (Lgal / Lcos) ^ 100 ∧ (Lgal / Lcos) ^ 100 < 2 ^ 25) ∧
    (0.845 < Lcos / Lgal ∧ Lcos / Lgal < 0.855) := by
  pi_ln2
  have hg := Lgal_pos; have hc := Lcos_pos
  have e : (Lgal / Lcos) ^ 2 = π ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (144 * a₀ ^ 2)) := by
    rw [div_pow, Lgal_sq, Lcos_sq]; field_simp; ring
  have b1 : 1.398 < (Lgal / Lcos) ^ 2 := by
    rw [e]
    calc (1.398 : ℝ) < (3.141592 : ℝ) ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (144 * a₀ ^ 2)) := by
          norm_num
      _ < _ := mul_lt_mul_of_pos_right p2_lo (by norm_num)
  have b2 : (Lgal / Lcos) ^ 2 < 1.3982 := by
    rw [e]
    calc _ < (3.141593 : ℝ) ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (144 * a₀ ^ 2)) :=
          mul_lt_mul_of_pos_right p2_hi (by norm_num)
      _ < (1.3982 : ℝ) := by norm_num
  have hq : 0 < Lgal / Lcos := by positivity
  have r1 : 1.175 < Lgal / Lcos := by
    apply lt_of_sq hq.le (by norm_num); linarith [show (1.175 : ℝ) ^ 2 < 1.398 by norm_num]
  have r2 : Lgal / Lcos < 1.185 := by
    apply lt_of_sq' hq.le (by norm_num); linarith [show (1.3982 : ℝ) < 1.185 ^ 2 by norm_num]
  have einv : Lcos / Lgal = 1 / (Lgal / Lcos) := by field_simp
  refine ⟨⟨r1, r2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have e2 : (Lgal / Lcos) ^ 100 = ((Lgal / Lcos) ^ 2) ^ 50 := by ring
    rw [e2]
    calc (2 : ℝ) ^ 24 < (1.398 : ℝ) ^ 50 := by norm_num
      _ < _ := by gcongr
  · have e2 : (Lgal / Lcos) ^ 100 = ((Lgal / Lcos) ^ 2) ^ 50 := by ring
    rw [e2]
    calc ((Lgal / Lcos) ^ 2) ^ 50 < (1.3982 : ℝ) ^ 50 := by gcongr
      _ < 2 ^ 25 := by norm_num
  · rw [einv, lt_div_iff₀ hq]; nlinarith
  · rw [einv, div_lt_iff₀ hq]; nlinarith

/-- **Why the temperature cannot lead** (Sec. IV.C): `2c²/R_Λ` is nine times the observed `a₀`;
`√(1 + 2a_Λ/g_N)` at `g_N = 10a₀` is `1.38`, a transition 38% above Newton; and the observed
relation there, `1/(1 − e^{−√10})` [McGaugh 2016], is `1.04`, 4% above. -/
theorem temperature_led_numbers :
    (9.0 < 2 * c₀ ^ 2 / (RL * a₀) ∧ 2 * c₀ ^ 2 / (RL * a₀) < 9.1) ∧
    (1.375 < Real.sqrt (1 + 2 * (c₀ ^ 2 / RL) / (10 * a₀)) ∧
      Real.sqrt (1 + 2 * (c₀ ^ 2 / RL) / (10 * a₀)) < 1.385) ∧
    (1.035 < 1 / (1 - Real.exp (-Real.sqrt 10)) ∧ 1 / (1 - Real.exp (-Real.sqrt 10)) < 1.045) := by
  have hR := RL_pos; have hH := Hinf_pos
  have e1 : 2 * c₀ ^ 2 / (RL * a₀) = 2 * c₀ * Hinf / a₀ := by unfold RL; field_simp
  have e2 : c₀ ^ 2 / RL = c₀ * Hinf := by unfold RL; field_simp
  obtain ⟨j1, j2⟩ := Hinf_tight
  -- `e^{√10}` lies between `23.3` and `24`
  have hs1 : (3.1622 : ℝ) < Real.sqrt 10 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 10 < 3.1623 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hE1 : (23.3 : ℝ) < Real.exp (Real.sqrt 10) := by
    have ha : Real.exp 3 * Real.exp 0.1622 < Real.exp (Real.sqrt 10) := by
      rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
    have hb : (0.1622 : ℝ) + 1 ≤ Real.exp 0.1622 := Real.add_one_le_exp _
    have hc : (2.7182818283 : ℝ) ^ 3 < Real.exp 3 := by
      rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
    have hd : (2.7182818283 : ℝ) ^ 3 * 1.1622 < Real.exp 3 * Real.exp 0.1622 := by
      apply mul_lt_mul hc (by linarith) (by norm_num) (Real.exp_pos _).le
    have : (23.3 : ℝ) < 2.7182818283 ^ 3 * 1.1622 := by norm_num
    linarith
  have hE2 : Real.exp (Real.sqrt 10) < 24 := by
    have ha : Real.exp (Real.sqrt 10) < Real.exp 3 * Real.exp 0.1623 := by
      rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
    have hb : Real.exp 0.1623 < 1 / (1 - 0.1623) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    have hc : Real.exp 3 < (2.7182818286 : ℝ) ^ 3 := by
      rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have hd : Real.exp 3 * Real.exp 0.1623 < (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) := by
      apply mul_lt_mul'' hc hb (Real.exp_pos _).le (Real.exp_pos _).le
    have : (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) < 24 := by norm_num
    linarith
  have hrar : 1 / (1 - Real.exp (-Real.sqrt 10))
      = Real.exp (Real.sqrt 10) / (Real.exp (Real.sqrt 10) - 1) := by
    rw [Real.exp_neg]
    have : Real.exp (Real.sqrt 10) - 1 ≠ 0 := by linarith
    field_simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [e1, lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [e1, div_lt_iff₀ (by norm_num)]; nlinarith
  · rw [e2, Real.lt_sqrt (by norm_num)]
    have : (1.375 : ℝ) ^ 2 < 1 + 2 * (c₀ * 1.8078e-18) / (10 * a₀) := by norm_num
    have h3 : 2 * (c₀ * 1.8078e-18) / (10 * a₀) < 2 * (c₀ * Hinf) / (10 * a₀) := by gcongr
    linarith
  · rw [e2, Real.sqrt_lt' (by norm_num)]
    have : 1 + 2 * (c₀ * 1.8079e-18) / (10 * a₀) < (1.385 : ℝ) ^ 2 := by norm_num
    have h3 : 2 * (c₀ * Hinf) / (10 * a₀) < 2 * (c₀ * 1.8079e-18) / (10 * a₀) := by gcongr
    linarith
  · rw [hrar, lt_div_iff₀ (by linarith)]; nlinarith
  · rw [hrar, div_lt_iff₀ (by linarith)]; nlinarith

/-- **The Tully–Fisher speed** of a `10¹¹ M☉` galaxy (Sec. IV.C): `v_c⁴ = a_M G M`,
`v_c = 208 km/s`. -/
theorem tully_fisher_speed :
    (208e3 : ℝ) ^ 4 < aM * (1e11 * GMs₀) ∧ aM * (1e11 * GMs₀) < (208.5e3 : ℝ) ^ 4 := by
  obtain ⟨h1, h2⟩ := aM_tight
  constructor <;> nlinarith

/-! ## The cosmological scale (Sec. IV.D, Table I, Appendix A) -/

/-- **Eq. (EL)**: the chain's `E_Λ = (LE_c/4) ln 2 = c⁴R_Λ/2G` for these inputs is
`1.00×10⁷⁰ J`. -/
theorem EΛ_val :
    reg.EΛ = c₀ ^ 4 * RL / (2 * G₀) ∧
    1.003e70 < c₀ ^ 4 * RL / (2 * G₀) ∧ c₀ ^ 4 * RL / (2 * G₀) < 1.004e70 := by
  have hR := RL_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [(reg.EΛ_eq G₀ reg_jacobson).2, reg_RL]; rfl
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num

/-- **The vacuum energy density**: the chain's `ρ_Λ = 3π²ρ_c ln 2/2L²` for these inputs equals
`Λc⁴/8πG`, which is `5.25×10⁻¹⁰ J/m³` (`5.3` to two figures, as in Sec. IV.D). -/
theorem ρΛ_val :
    reg.ρΛ = 3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) ∧
    5.25e-10 < 3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) ∧
    3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) < 5.255e-10 := by
  pi_ln2
  have e : 3 / RL ^ 2 * c₀ ^ 4 / (8 * π * G₀) = 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / π := by
    rw [RL_sq]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have h := (reg.ρΛ_eq G₀ (3 / RL ^ 2) reg_jacobson reg_deSitter).2
    rw [h]; rfl
  · rw [e]
    calc (5.25e-10 : ℝ) < 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / 3.141593 := by norm_num
      _ < _ := div_lt_div_of_pos_left (by norm_num) Real.pi_pos Real.pi_lt_d6
  · rw [e]
    calc _ < 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / 3.141592 :=
          div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_d6
      _ < (5.255e-10 : ℝ) := by norm_num

/-- **Eq. (Lambda)**: the chain's `GΛ = 12πc³/(ℏL² ln 2)` for these inputs is `GΛ` with the
observed `Λ`, `7.28×10⁻⁶³`. -/
theorem GΛ_val :
    G₀ * (3 / RL ^ 2) = 12 * π * c₀ ^ 3 / (ℏ₀ * Lcos ^ 2 * Real.log 2) ∧
    7.275e-63 < G₀ * (3 / RL ^ 2) ∧ G₀ * (3 / RL ^ 2) < 7.285e-63 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (reg.G_Lambda G₀ (3 / RL ^ 2) reg_jacobson reg_deSitter).1
    rw [h]; rfl
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num

/-- **The horizon's temperature and the reduction clock** (Sec. II, Table I, Appendix A):
`k_BT_dS = E_c/L = ℏH_∞/2π = 3.03×10⁻⁵³ J` (`3.0` to two figures); `τ* = Lt_c = 2π/H_∞ =
3.5×10¹⁸ s = 1.1×10¹¹ yr`; and the Hubble rate `2π/Lt_c = H_∞ = 1.81×10⁻¹⁸ s⁻¹`
(`reg_clock`, `horizon_val`). -/
theorem temperature_and_clock :
    (3.025e-53 < ℏ₀ * Hinf / (2 * π) ∧ ℏ₀ * Hinf / (2 * π) < 3.035e-53) ∧
    (3.45e18 < 2 * π / Hinf ∧ 2 * π / Hinf < 3.55e18) ∧
    (1.05e11 < 2 * π / Hinf / yr₀ ∧ 2 * π / Hinf / yr₀ < 1.15e11) := by
  pi_ln2
  have hH := Hinf_pos
  obtain ⟨j1, j2⟩ := Hinf_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ hH]; nlinarith
  · rw [div_lt_iff₀ hH]; nlinarith
  · rw [div_div, lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_div, div_lt_iff₀ (by positivity)]; nlinarith

/-- **Any galaxy, group or cluster** (Sec. IV.D): the zero-gravity radius lies below the crossing
when `M < c²R_Λ/(π³G)` (`Reg.zero_gravity_mass`), which is `3.6×10²¹ M☉`, above any cluster;
for these inputs, every mass up to `10¹⁶ M☉` has `r_z < R_Λ/π`. -/
theorem zero_gravity_masses :
    (3.6e21 * (GMs₀ / G₀) < c₀ ^ 2 * RL / (π ^ 3 * G₀) ∧
      c₀ ^ 2 * RL / (π ^ 3 * G₀) < 3.65e21 * (GMs₀ / G₀)) ∧
    ∀ M rz : ℝ, 0 < M → M ≤ 1e16 * (GMs₀ / G₀) → 0 < rz →
      rz ^ 3 = G₀ * M * RL ^ 2 / c₀ ^ 2 → rz < RL / π := by
  pi_ln2
  obtain ⟨r1, r2⟩ := RL_tight
  have hR := RL_pos
  have p3lo : (3.141592 : ℝ) ^ 3 < π ^ 3 := pow_lt_pow_left₀ Real.pi_gt_d6 (by norm_num) (by norm_num)
  have p3hi : π ^ 3 < (3.141593 : ℝ) ^ 3 := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by norm_num)
  have hlo : 3.6e21 * (GMs₀ / G₀) < c₀ ^ 2 * RL / (π ^ 3 * G₀) := by
    rw [lt_div_iff₀ (by positivity)]
    have : 3.6e21 * (GMs₀ / G₀) * ((3.141593 : ℝ) ^ 3 * G₀) < c₀ ^ 2 * 1.6583e26 := by norm_num
    have h2 : 3.6e21 * (GMs₀ / G₀) * (π ^ 3 * G₀) < 3.6e21 * (GMs₀ / G₀) * ((3.141593 : ℝ) ^ 3 * G₀) := by
      gcongr
    nlinarith
  have hhi : c₀ ^ 2 * RL / (π ^ 3 * G₀) < 3.65e21 * (GMs₀ / G₀) := by
    rw [div_lt_iff₀ (by positivity)]
    have : c₀ ^ 2 * 1.6584e26 < 3.65e21 * (GMs₀ / G₀) * ((3.141592 : ℝ) ^ 3 * G₀) := by norm_num
    have h2 : 3.65e21 * (GMs₀ / G₀) * ((3.141592 : ℝ) ^ 3 * G₀) < 3.65e21 * (GMs₀ / G₀) * (π ^ 3 * G₀) := by
      gcongr
    nlinarith
  refine ⟨⟨hlo, hhi⟩, ?_⟩
  intro M rz hM hMle hrz h3
  have h3' : rz ^ 3 = G₀ * M * reg.RL ^ 2 / reg.c ^ 2 := by rw [reg_RL]; exact h3
  have key := (reg.zero_gravity_mass G₀ M rz (by norm_num) hrz h3').2
  rw [reg_RL] at key
  have hM' : M < c₀ ^ 2 * RL / (π ^ 3 * G₀) := by
    have : (1e16 : ℝ) * (GMs₀ / G₀) < 3.6e21 * (GMs₀ / G₀) := by norm_num
    linarith
  exact key hM'

/-- **The crossover** of the deep pull and the push (Sec. IV.D), `r⁴ = R_Λ⁴a_M GM/c⁴`, that is
`r = R_Λv_c/c`: `3.7 Mpc` for `10¹¹ M☉`. -/
theorem crossover_radius :
    (3.7 * Mpc₀) ^ 4 < RL ^ 4 * aM * (1e11 * GMs₀) / c₀ ^ 4 ∧
    RL ^ 4 * aM * (1e11 * GMs₀) / c₀ ^ 4 < (3.75 * Mpc₀) ^ 4 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := aM_val
  have e : RL ^ 4 = (RL ^ 2) ^ 2 := by ring
  rw [e, RL_sq]
  constructor
  · calc (3.7 * Mpc₀) ^ 4 < (c₀ ^ 2 / (H₀ ^ 2 * ΩΛ₀)) ^ 2 * 1.415e-10 * (1e11 * GMs₀) / c₀ ^ 4 := by
          norm_num
      _ < _ := by gcongr
  · calc _ < (c₀ ^ 2 / (H₀ ^ 2 * ΩΛ₀)) ^ 2 * 1.425e-10 * (1e11 * GMs₀) / c₀ ^ 4 := by gcongr
      _ < (3.75 * Mpc₀) ^ 4 := by norm_num

/-- **The 123 orders are `L²`** (Table I, Sec. IV.D): the Planck density `c⁷/ℏG²`, the quantum field
theory estimate of the vacuum energy density, is `4.6×10¹¹³ J/m³` (`10¹¹³`); it exceeds the
ring's `ρ_Λ` by `(2 ln 2/3) L²` (`Reg.vacuum_ratio`), `8.8×10¹²²`, with `L² = 1.9×10¹²³`. -/
theorem vacuum_orders :
    (4.6e113 < c₀ ^ 7 / (ℏ₀ * G₀ ^ 2) ∧ c₀ ^ 7 / (ℏ₀ * G₀ ^ 2) < 4.65e113) ∧
    c₀ ^ 7 / (ℏ₀ * G₀ ^ 2) / reg.ρΛ = 2 * Real.log 2 / 3 * Lcos ^ 2 ∧
    (8.8e122 < 2 * Real.log 2 / 3 * Lcos ^ 2 ∧ 2 * Real.log 2 / 3 * Lcos ^ 2 < 8.85e122) ∧
    (1.9e123 < Lcos ^ 2 ∧ Lcos ^ 2 < 1.91e123) := by
  pi_ln2
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds
  have e : 2 * Real.log 2 / 3 * Lcos ^ 2 = π * (8 * c₀ ^ 5 / (3 * ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by
    rw [Lcos_sq]; field_simp; ring
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := (reg.vacuum_ratio G₀ reg_jacobson).2
    simp only [reg] at h
    exact h
  · rw [e]
    calc (8.8e122 : ℝ) < 3.141592 * (8 * c₀ ^ 5 / (3 * ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
      _ < _ := mul_lt_mul_of_pos_right Real.pi_gt_d6 (by norm_num)
  · rw [e]
    calc _ < 3.141593 * (8 * c₀ ^ 5 / (3 * ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))) :=
          mul_lt_mul_of_pos_right Real.pi_lt_d6 (by norm_num)
      _ < (8.85e122 : ℝ) := by norm_num
  · have : (1.9e123 : ℝ) < 1.4435 * (2 : ℝ) ^ 409 := by norm_num
    linarith
  · have : 1.4436 * (2 : ℝ) ^ 409 < (1.91e123 : ℝ) := by norm_num
    linarith

/-! ## Predictions and the constancy of `G` (Secs. IV.D, VI, Appendix A) -/

/-- `a₀ ∝ cH(z)` predicts a scale `H(1)/H₀ = √(8Ω_m + Ω_Λ) = 1.79` times larger at `z = 1`
(`1.8` to two figures). -/
theorem redshift_one :
    1.785 < Real.sqrt (0.315 * 8 + 0.685) ∧ Real.sqrt (0.315 * 8 + 0.685) < 1.795 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The equation of state** (Sec. VI, Appendix A): the drift bounded is that of the term `Λc²/3`
of the expansion rate, `|Λ̇/Λ| = |Ġ/G| ≲ 10⁻¹³ yr⁻¹`, so with `H₀ = 6.89×10⁻¹¹ yr⁻¹`,
`|1 + w₀| ≲ 10⁻¹³/3H₀ = 4.8×10⁻⁴` (`5×10⁻⁴` to one figure); the drift a Hubble-radius horizon would
give, `Ġ/G = 2H(1+q) ≈ 6×10⁻¹¹ yr⁻¹` at `q = −0.53` (`Reg.G_drift`), is six hundred times the
lunar-laser-ranging bound `10⁻¹³ yr⁻¹`. -/
theorem constancy_numbers :
    (6.885e-11 < H₀ * yr₀ ∧ H₀ * yr₀ < 6.895e-11) ∧
    (4.8e-4 < 1e-13 / (3 * (H₀ * yr₀)) ∧ 1e-13 / (3 * (H₀ * yr₀)) < 4.85e-4) ∧
    (5.5e-11 < 2 * (H₀ * yr₀) * (1 - 0.53) ∧ 2 * (H₀ * yr₀) * (1 - 0.53) < 6.5e-11) ∧
    (550 < 2 * (H₀ * yr₀) * (1 - 0.53) / 1e-13 ∧ 2 * (H₀ * yr₀) * (1 - 0.53) / 1e-13 < 650) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩⟩

end Numerics
end Register
