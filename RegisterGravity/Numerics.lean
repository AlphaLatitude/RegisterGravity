import RegisterGravity.Cosmo
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# The numbers of the paper, certified

Every number that *Gravitation from Hilbert-Space Granularity* (v11.1) computes from its inputs,
in Table I, the text, and Appendix A, recomputed from the Appendix's inputs and certified by an
interval: each theorem states `lo < quantity < hi`, and every number in the interval rounds to the
value the paper quotes.  Observational values and their uncertainties are inputs, not claims.

## Inputs (Appendix A), as exact rationals

`c = 299792458 m/s`, `ℏ = 1.054571817e-34 J s`, `k_B = 1.380649e-23 J/K`,
`G = 6.67430e-11 m³ kg⁻¹ s⁻²`, `H₀ = 67.4 km/s/Mpc` with `1 Mpc = 3.0856775814913673e22 m`,
`Ω_Λ = 0.685`, `a₀ = 1.20e-10 m/s²`; for the Sun the IAU heliocentric constant
`GM☉ = 1.32712440018e20 m³/s²` (so `M☉ = GM☉/G`), `1 au = 149597870700 m`,
`R☉ = 6.957e8 m`, and for Mercury `a = 5.7909050e10 m`, `e = 0.205630`, `T = 87.9691 d`;
`1 yr = 365.25 d`; `Ω_m = 0.315`.

## The one mathematical input

`π` enters as a real `p` with `3.141592 < p < 3.141593` (`PiBounds`).  These are Mathlib's
`Real.pi_gt_d6` and `Real.pi_lt_d6`; they are taken as a hypothesis here only to keep the build to
the part of Mathlib that the rest of the development needs.  Nothing else is assumed.

## Bridge to the chain

`reg hp` is the register of `Chain.lean` with these inputs, the cell fixed from `G`, and `L` from
the horizon.  `reg_jacobson` shows that Jacobson's relation with the register's entropy density
returns the measured `G` (the hypothesis `hJ` of the chain, now discharged), `reg_RL` that the
placement returns the observed de Sitter radius, and `reg_deSitter` that the observed `Λ` meets the
boundary condition `hdS` of the chain.
-/

open Real

-- `norm_num` evaluates powers such as `2 ^ 40801` exactly; raise Lean's guard on large exponents.
set_option exponentiation.threshold 50000

namespace Register
namespace Numerics

local notation "c₀" => (299792458 : ℝ)
local notation "ℏ₀" => ((1054571817 : ℝ) / 10 ^ 43)
local notation "kB₀" => ((1380649 : ℝ) / 10 ^ 29)
local notation "G₀" => ((66743 : ℝ) / 10 ^ 15)
local notation "Mpc₀" => ((30856775814913673 : ℝ) * 10 ^ 6)
local notation "pc₀" => ((30856775814913673 : ℝ))
local notation "H₀" => ((67400 : ℝ) / ((30856775814913673 : ℝ) * 10 ^ 6))
local notation "ΩΛ₀" => ((685 : ℝ) / 1000)
local notation "a₀" => ((12 : ℝ) / 10 ^ 11)
local notation "GMs₀" => ((132712440018 : ℝ) * 10 ^ 9)
local notation "au₀" => ((149597870700 : ℝ))
local notation "yr₀" => ((31557600 : ℝ))
local notation "Rs₀" => ((6957 : ℝ) * 10 ^ 5)

/-- `π` to six decimals: Mathlib's `Real.pi_gt_d6` and `Real.pi_lt_d6`. -/
structure PiBounds (p : ℝ) : Prop where
  lo : (3.141592 : ℝ) < p
  hi : p < (3.141593 : ℝ)

variable {p : ℝ}

lemma PiBounds.pos (hp : PiBounds p) : 0 < p := lt_trans (by norm_num) hp.lo

lemma lt_of_sq {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 ≤ a) (h : a ^ 2 < Q ^ 2) : a < Q :=
  (pow_lt_pow_iff_left₀ ha hQ two_ne_zero).1 h

lemma lt_of_sq' {Q b : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b) (h : Q ^ 2 < b ^ 2) : Q < b :=
  (pow_lt_pow_iff_left₀ hQ hb two_ne_zero).1 h

/-! ## The derived quantities -/

/-- the cell, Eq. (cell): `ℓ_c = √(πℏG/c³)` -/
noncomputable def lc (p : ℝ) : ℝ := Real.sqrt (p * ℏ₀ * G₀ / c₀ ^ 3)
/-- the Planck length, `ℓ_P = √(ℏG/c³)` -/
noncomputable def lP : ℝ := Real.sqrt (ℏ₀ * G₀ / c₀ ^ 3)
/-- the asymptotic Hubble rate, `H_∞ = H₀√Ω_Λ` -/
noncomputable def Hinf : ℝ := H₀ * Real.sqrt ΩΛ₀
/-- the de Sitter radius, `R_Λ = c/H_∞` -/
noncomputable def RL : ℝ := c₀ / Hinf
/-- `L` from the horizon, Eq. (Lcos): `L = 2πR_Λ/ℓ_c` -/
noncomputable def Lcos (p : ℝ) : ℝ := 2 * p * RL / lc p
/-- `L` from galaxies, Eq. (Lgal): `L = (π²/6)c²/(a₀ℓ_c)` -/
noncomputable def Lgal (p : ℝ) : ℝ := p ^ 2 / 6 * c₀ ^ 2 / (a₀ * lc p)
/-- the galactic acceleration, Eq. (aM): `a_M = πc²/12R_Λ` -/
noncomputable def aM (p : ℝ) : ℝ := p * c₀ ^ 2 / (12 * RL)
/-- the Sun's flip rate, `α = M☉/m_c = M☉cℓ_c/ℏ` with `M☉ = GM☉/G` -/
noncomputable def αs (p : ℝ) : ℝ := GMs₀ / G₀ * c₀ * lc p / ℏ₀
/-- Newton's constant from `L`, Eq. (G): `G = 4πc³R_Λ²/ℏL²` -/
noncomputable def Gof (p L : ℝ) : ℝ := 4 * p * c₀ ^ 3 * RL ^ 2 / (ℏ₀ * L ^ 2)

lemma lc_pos (hp : PiBounds p) : 0 < lc p := by
  have := hp.pos; unfold lc; positivity

lemma lc_sq (hp : PiBounds p) : lc p ^ 2 = p * ℏ₀ * G₀ / c₀ ^ 3 := by
  have := hp.pos; unfold lc; rw [Real.sq_sqrt (by positivity)]

lemma lP_pos : 0 < lP := by unfold lP; positivity

lemma lP_sq : lP ^ 2 = ℏ₀ * G₀ / c₀ ^ 3 := by unfold lP; rw [Real.sq_sqrt (by positivity)]

lemma Hinf_pos : 0 < Hinf := by unfold Hinf; positivity

lemma Hinf_sq : Hinf ^ 2 = H₀ ^ 2 * ΩΛ₀ := by
  unfold Hinf; rw [mul_pow, Real.sq_sqrt (by norm_num)]

lemma RL_pos : 0 < RL := by unfold RL; have := Hinf_pos; positivity

lemma RL_sq : RL ^ 2 = c₀ ^ 2 / (H₀ ^ 2 * ΩΛ₀) := by
  unfold RL; rw [div_pow, Hinf_sq]

lemma Lcos_pos (hp : PiBounds p) : 0 < Lcos p := by
  have := hp.pos; have := lc_pos hp; have := RL_pos; unfold Lcos; positivity

lemma Lcos_sq (hp : PiBounds p) :
    Lcos p ^ 2 = 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by
  have := hp.pos
  unfold Lcos
  rw [div_pow, mul_pow, RL_sq, lc_sq hp]
  field_simp; ring

lemma Lgal_pos (hp : PiBounds p) : 0 < Lgal p := by
  have := hp.pos; have := lc_pos hp; unfold Lgal; positivity

lemma Lgal_sq (hp : PiBounds p) :
    Lgal p ^ 2 = p ^ 3 * c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀) := by
  have := hp.pos
  unfold Lgal
  simp only [div_pow, mul_pow]
  rw [lc_sq hp]
  field_simp; ring

lemma aM_pos (hp : PiBounds p) : 0 < aM p := by
  have := hp.pos; have := RL_pos; unfold aM; positivity

lemma aM_sq (hp : PiBounds p) : aM p ^ 2 = p ^ 2 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144 := by
  have := hp.pos
  unfold aM
  rw [div_pow, mul_pow, mul_pow, RL_sq]
  field_simp; ring

lemma αs_pos (hp : PiBounds p) : 0 < αs p := by
  have := lc_pos hp; unfold αs; positivity

lemma αs_sq (hp : PiBounds p) : αs p ^ 2 = p * GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀) := by
  unfold αs
  rw [div_pow, mul_pow, mul_pow, lc_sq hp]
  field_simp

/-! ## Bridge to the chain -/

/-- The register of `Chain.lean` with the Appendix's inputs, the cell from `G`, and `L` from the
horizon. -/
noncomputable def reg (hp : PiBounds p) : Reg where
  c := c₀
  ℏ := ℏ₀
  kB := kB₀
  ℓc := lc p
  L := Lcos p
  pi := p
  c_pos := by norm_num
  ℏ_pos := by norm_num
  kB_pos := by norm_num
  ℓc_pos := lc_pos hp
  L_pos := Lcos_pos hp
  pi_pos := hp.pos

/-- The placement returns the observed de Sitter radius. -/
theorem reg_RL (hp : PiBounds p) : (reg hp).RL = RL := by
  have := lc_pos hp; have := hp.pos
  simp only [Reg.RL, reg]
  unfold Lcos
  field_simp

/-- The observed `Λ = 3/R_Λ²` satisfies the boundary condition of the chain: the horizon of the
solution without a mass is the register's (`Reg.deSitter`). -/
theorem reg_deSitter (hp : PiBounds p) : (reg hp).fSdS G₀ 0 (3 / RL ^ 2) (reg hp).RL = 0 :=
  ((reg hp).deSitter G₀ _).2 (by rw [reg_RL])

/-- **Jacobson's relation with the register's entropy density returns the measured `G`**: the
hypothesis `hJ` of every theorem of the chain holds for these inputs. -/
theorem reg_jacobson (hp : PiBounds p) :
    G₀ = (reg hp).c ^ 3 * (reg hp).kB / (4 * (reg hp).ℏ * (reg hp).η) := by
  have := hp.pos
  rw [Reg.eta_eq]
  simp only [reg]
  rw [lc_sq hp]
  field_simp

/-- The chain's `a_M` for these inputs is `πc²/12R_Λ` with the observed `R_Λ`. -/
theorem reg_aM (hp : PiBounds p) : (reg hp).aM 4 = aM p := by
  rw [(reg hp).aM_values.1, reg_RL]
  rfl

/-- The chain's `G = 4πc³R_Λ²/ℏL²` for these inputs is `Gof p L`, and at `L_cos` it is the
measured `G` (the identity the paper notes: with `L_cos` Eq. (G) returns its input). -/
theorem Gof_Lcos (hp : PiBounds p) : Gof p (Lcos p) = G₀ := by
  have h := ((reg hp).G_eq G₀ (reg_jacobson hp)).2
  rw [reg_RL] at h
  rw [h]
  rfl

/-! ## The cell and the units of the cell (Table I, Eq. (cell), Appendix A) -/

/-- `ℓ_c = 2.865×10⁻³⁵ m`, which is `2.86×10⁻³⁵ m` to three figures. -/
theorem lc_val (hp : PiBounds p) : 2.8645e-35 < lc p ∧ lc p < 2.865e-35 := by
  have := hp.lo; have := hp.hi
  constructor
  · apply lt_of_sq (lc_pos hp).le (by norm_num)
    rw [lc_sq hp]
    calc (2.8645e-35 : ℝ) ^ 2 < 3.141592 * ℏ₀ * G₀ / c₀ ^ 3 := by norm_num
      _ < p * ℏ₀ * G₀ / c₀ ^ 3 := by gcongr
  · apply lt_of_sq' (lc_pos hp).le (by norm_num)
    rw [lc_sq hp]
    calc p * ℏ₀ * G₀ / c₀ ^ 3 < 3.141593 * ℏ₀ * G₀ / c₀ ^ 3 := by gcongr
      _ < (2.865e-35 : ℝ) ^ 2 := by norm_num

/-- `ℓ_P = 1.616×10⁻³⁵ m`, which is `1.62×10⁻³⁵ m` to three figures. -/
theorem lP_val : 1.616e-35 < lP ∧ lP < 1.6165e-35 := by
  constructor
  · apply lt_of_sq lP_pos.le (by norm_num); rw [lP_sq]; norm_num
  · apply lt_of_sq' lP_pos.le (by norm_num); rw [lP_sq]; norm_num

/-- Tighter enclosures used below. -/
lemma lc_tight (hp : PiBounds p) : 2.8647e-35 < lc p ∧ lc p < 2.8648e-35 := by
  have := hp.lo; have := hp.hi
  constructor
  · apply lt_of_sq (lc_pos hp).le (by norm_num)
    rw [lc_sq hp]
    calc (2.8647e-35 : ℝ) ^ 2 < 3.141592 * ℏ₀ * G₀ / c₀ ^ 3 := by norm_num
      _ < p * ℏ₀ * G₀ / c₀ ^ 3 := by gcongr
  · apply lt_of_sq' (lc_pos hp).le (by norm_num)
    rw [lc_sq hp]
    calc p * ℏ₀ * G₀ / c₀ ^ 3 < 3.141593 * ℏ₀ * G₀ / c₀ ^ 3 := by gcongr
      _ < (2.8648e-35 : ℝ) ^ 2 := by norm_num

lemma Hinf_tight : 1.8078e-18 < Hinf ∧ Hinf < 1.8079e-18 := by
  constructor
  · apply lt_of_sq Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num
  · apply lt_of_sq' Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num

lemma RL_tight : 1.6583e26 < RL ∧ RL < 1.6584e26 := by
  constructor
  · apply lt_of_sq RL_pos.le (by norm_num); rw [RL_sq]; norm_num
  · apply lt_of_sq' RL_pos.le (by norm_num); rw [RL_sq]; norm_num

/-- `t_c = 9.56×10⁻⁴⁴ s`, `m_c = 1.228×10⁻⁸ kg`, `E_c = 1.104×10⁹ J`, `a_c = 3.14×10⁵¹ m/s²`. -/
theorem cell_units (hp : PiBounds p) :
    (9.555e-44 < lc p / c₀ ∧ lc p / c₀ < 9.565e-44) ∧
    (1.2275e-8 < ℏ₀ / (c₀ * lc p) ∧ ℏ₀ / (c₀ * lc p) < 1.2285e-8) ∧
    (1.1035e9 < ℏ₀ * c₀ / lc p ∧ ℏ₀ * c₀ / lc p < 1.1045e9) ∧
    (3.135e51 < c₀ ^ 2 / lc p ∧ c₀ ^ 2 / lc p < 3.145e51) := by
  obtain ⟨h1, h2⟩ := lc_tight hp
  have := lc_pos hp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith

/-! ## The horizon (Sec. II, Sec. IV.D, Appendix A) -/

/-- `H_∞ = H₀√Ω_Λ = 1.81×10⁻¹⁸ s⁻¹`. -/
theorem Hinf_val : 1.805e-18 < Hinf ∧ Hinf < 1.815e-18 := by
  constructor
  · apply lt_of_sq Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num
  · apply lt_of_sq' Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num

/-- `R_Λ = c/H_∞ = 1.66×10²⁶ m`. -/
theorem RL_val : 1.655e26 < RL ∧ RL < 1.665e26 := by
  constructor
  · apply lt_of_sq RL_pos.le (by norm_num); rw [RL_sq]; norm_num
  · apply lt_of_sq' RL_pos.le (by norm_num); rw [RL_sq]; norm_num

/-- `Λ = 3/R_Λ² = 1.09×10⁻⁵² m⁻²`. -/
theorem Lambda_val : 1.085e-52 < 3 / RL ^ 2 ∧ 3 / RL ^ 2 < 1.095e-52 := by
  rw [RL_sq]; constructor <;> norm_num

/-- `c²/R_Λ = cH_∞ = 5.4×10⁻¹⁰ m/s²`, and the crossing `g_N = c²/πR_Λ = 1.73×10⁻¹⁰ m/s²`. -/
theorem surface_gravity (hp : PiBounds p) :
    (5.415e-10 < c₀ ^ 2 / RL ∧ c₀ ^ 2 / RL < 5.425e-10) ∧
    (1.72e-10 < c₀ ^ 2 / (p * RL) ∧ c₀ ^ 2 / (p * RL) < 1.73e-10) := by
  have hs : c₀ ^ 2 / RL = c₀ * Hinf := by
    have := Hinf_pos; unfold RL; field_simp
  have hs2 : c₀ ^ 2 / (p * RL) = c₀ * Hinf / p := by
    have := Hinf_pos; have := hp.pos; unfold RL; field_simp
  obtain ⟨h1, h2⟩ := Hinf_tight
  have := hp.lo; have := hp.hi; have := hp.pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hs]; linarith
  · rw [hs]; linarith
  · rw [hs2, lt_div_iff₀ hp.pos]
    have : (1.72e-10 : ℝ) * p < 1.72e-10 * 3.141593 := by gcongr
    nlinarith
  · rw [hs2, div_lt_iff₀ hp.pos]
    have : (1.73e-10 : ℝ) * 3.141592 < 1.73e-10 * p := by gcongr
    nlinarith

/-- **`L` from the horizon**, Eq. (Lcos): `L_cos = 3.64×10⁶¹`. -/
theorem Lcos_val (hp : PiBounds p) : 3.635e61 < Lcos p ∧ Lcos p < 3.645e61 := by
  have := hp.lo; have := hp.hi
  constructor
  · apply lt_of_sq (Lcos_pos hp).le (by norm_num)
    rw [Lcos_sq hp]
    calc (3.635e61 : ℝ) ^ 2 < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by norm_num
      _ < 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by gcongr
  · apply lt_of_sq' (Lcos_pos hp).le (by norm_num)
    rw [Lcos_sq hp]
    calc 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))
        < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by gcongr
      _ < (3.645e61 : ℝ) ^ 2 := by norm_num

/-- `L_cos²` lies between `2⁴⁰⁹` and `1.0007·2⁴⁰⁹`. -/
lemma Lcos_sq_bounds (hp : PiBounds p) :
    (2 : ℝ) ^ 409 < Lcos p ^ 2 ∧ Lcos p ^ 2 < 1.0007 * 2 ^ 409 := by
  have := hp.lo; have := hp.hi
  rw [Lcos_sq hp]
  constructor
  · calc (2 : ℝ) ^ 409 < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by norm_num
      _ < 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by gcongr
  · calc 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))
        < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by gcongr
      _ < 1.0007 * 2 ^ 409 := by norm_num

/-- **The capacity condition**, Eq. (nmax).  A string of `L` bits gives each outcome of a state of
`N` qubits a probability that is a frequency over its bits, `k/L` with `k` a whole number, and a
state spread over all `2^N` outcomes gives each of them at least one bit, so `2^N ≤ L`. -/
theorem capacity (N L : ℕ) (k : Fin (2 ^ N) → ℕ) (hk : ∀ i, 1 ≤ k i) (hL : ∑ i, k i = L) :
    2 ^ N ≤ L := by
  calc 2 ^ N = ∑ _i : Fin (2 ^ N), 1 := by simp
    _ ≤ ∑ i, k i := Finset.sum_le_sum (fun i _ => hk i)
    _ = L := hL

/-- The largest `N` with `2^N ≤ L` is `204` whenever `2²⁰⁴ < L < 2²⁰⁵`. -/
lemma nmax_of_bounds {L : ℝ} (h1 : (2 : ℝ) ^ 204 < L) (h2 : L < 2 ^ 205) (N : ℕ) :
    (2 : ℝ) ^ N ≤ L ↔ N ≤ 204 := by
  constructor
  · intro h
    by_contra hN
    have : (2 : ℝ) ^ 205 ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  · intro hN
    have : (2 : ℝ) ^ N ≤ 2 ^ 204 := pow_le_pow_right₀ (by norm_num) hN
    linarith

/-- **The ceiling from the horizon**: `2²⁰⁴ < L_cos < 2²⁰⁵`, so `N_max = ⌊log₂ L⌋ = 204`. -/
theorem ceiling_cos (hp : PiBounds p) : (2 : ℝ) ^ 204 < Lcos p ∧ Lcos p < 2 ^ 205 := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds hp
  constructor
  · apply lt_of_sq (Lcos_pos hp).le (by positivity)
    calc ((2 : ℝ) ^ 204) ^ 2 < 2 ^ 409 := by norm_num
      _ < _ := h1
  · apply lt_of_sq' (Lcos_pos hp).le (by positivity)
    calc Lcos p ^ 2 < 1.0007 * 2 ^ 409 := h2
      _ < ((2 : ℝ) ^ 205) ^ 2 := by norm_num

/-- **`N_max = 204`** from the horizon: `2^N ≤ L_cos` exactly when `N ≤ 204`. -/
theorem nmax_cos (hp : PiBounds p) (N : ℕ) : (2 : ℝ) ^ N ≤ Lcos p ↔ N ≤ 204 :=
  nmax_of_bounds (ceiling_cos hp).1 (ceiling_cos hp).2 N

/-- **`log₂ L_cos = 204.50`**: `2⁴⁰⁸⁹⁹ < L_cos²⁰⁰ < 2⁴⁰⁹⁰¹`, that is,
`204.495 < log₂ L_cos < 204.505`. -/
theorem log2_Lcos (hp : PiBounds p) :
    (2 : ℝ) ^ 40899 < Lcos p ^ 200 ∧ Lcos p ^ 200 < 2 ^ 40901 := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds hp
  have e : Lcos p ^ 200 = (Lcos p ^ 2) ^ 100 := by ring
  rw [e]
  constructor
  · calc (2 : ℝ) ^ 40899 < ((2 : ℝ) ^ 409) ^ 100 := by norm_num
      _ < (Lcos p ^ 2) ^ 100 := by gcongr
  · calc (Lcos p ^ 2) ^ 100 < (1.0007 * (2 : ℝ) ^ 409) ^ 100 := by
          gcongr
      _ < 2 ^ 40901 := by norm_num

/-- A tighter enclosure of `L_cos`, for the Appendix's products. -/
lemma Lcos_tight (hp : PiBounds p) : 3.6370e61 < Lcos p ∧ Lcos p < 3.6373e61 := by
  have := hp.lo; have := hp.hi
  constructor
  · apply lt_of_sq (Lcos_pos hp).le (by norm_num)
    rw [Lcos_sq hp]
    calc (3.6370e61 : ℝ) ^ 2 < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by norm_num
      _ < 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by gcongr
  · apply lt_of_sq' (Lcos_pos hp).le (by norm_num)
    rw [Lcos_sq hp]
    calc 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀))
        < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) := by gcongr
      _ < (3.6373e61 : ℝ) ^ 2 := by norm_num

/-- **Palmer's bit count** `2^{N+1} − 2 ≤ NL` holds at `N = 211` and fails at `N = 212`, with the
Appendix's figures: `2²⁰⁴ = 2.57×10⁶¹`, `2²⁰⁵ = 5.14×10⁶¹`, `2²¹² = 6.58×10⁶³`,
`211 L_cos = 7.67×10⁶³`, `2²¹³ = 1.32×10⁶⁴`, `212 L_cos = 7.71×10⁶³`. -/
theorem palmer_211 (hp : PiBounds p) :
    ((2 : ℝ) ^ 212 - 2 ≤ 211 * Lcos p ∧ 212 * Lcos p < 2 ^ 213 - 2) ∧
    ((2.565e61 : ℝ) < 2 ^ 204 ∧ (2 : ℝ) ^ 204 < 2.575e61) ∧
    ((5.135e61 : ℝ) < 2 ^ 205 ∧ (2 : ℝ) ^ 205 < 5.145e61) ∧
    ((6.575e63 : ℝ) < 2 ^ 212 ∧ (2 : ℝ) ^ 212 < 6.585e63) ∧
    ((1.315e64 : ℝ) < 2 ^ 213 ∧ (2 : ℝ) ^ 213 < 1.325e64) ∧
    (7.665e63 < 211 * Lcos p ∧ 211 * Lcos p < 7.675e63) ∧
    (7.705e63 < 212 * Lcos p ∧ 212 * Lcos p < 7.715e63) := by
  obtain ⟨h1, h2⟩ := Lcos_tight hp
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩

/-- **The horizon's counts**, Eq. (counts) to leading order: `L²/2 = 6.6×10¹²²` cells and
`L²/4 = 3.3×10¹²²` rings. -/
theorem horizon_counts (hp : PiBounds p) :
    (6.61e122 < Lcos p ^ 2 / 2 ∧ Lcos p ^ 2 / 2 < 6.62e122) ∧
    (3.30e122 < Lcos p ^ 2 / 4 ∧ Lcos p ^ 2 / 4 < 3.31e122) := by
  have := hp.lo; have := hp.hi
  have h : ∀ k : ℝ, 0 < k → Lcos p ^ 2 / k = 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) / k := by
    intro k _; rw [Lcos_sq hp]
  rw [h 2 (by norm_num), h 4 (by norm_num)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · calc (6.61e122 : ℝ) < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) / 2 := by norm_num
      _ < _ := by gcongr
  · calc _ < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) / 2 := by gcongr
      _ < (6.62e122 : ℝ) := by norm_num
  · calc (3.30e122 : ℝ) < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) / 4 := by norm_num
      _ < _ := by gcongr
  · calc _ < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) / 4 := by gcongr
      _ < (3.31e122 : ℝ) := by norm_num

/-- **Davies**: `log₂ 10¹²² ≈ 405` (`2⁸¹⁰ < 10²⁴⁴ < 2⁸¹¹`, that is,
`405 < log₂ 10¹²² < 405.5`), and the logarithm of the horizon's cells is `2 log₂ L − 1 = 408`:
`2⁴⁰⁷⁹⁹ < (L²/2)¹⁰⁰ < 2⁴⁰⁸⁰¹`, that is, `407.99 < log₂(L²/2) < 408.01`. -/
theorem davies (hp : PiBounds p) :
    ((2 : ℝ) ^ 810 < 10 ^ 244 ∧ (10 : ℝ) ^ 244 < 2 ^ 811) ∧
    ((2 : ℝ) ^ 40799 < (Lcos p ^ 2 / 2) ^ 100 ∧ (Lcos p ^ 2 / 2) ^ 100 < 2 ^ 40801) := by
  obtain ⟨h1, h2⟩ := Lcos_sq_bounds hp
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · calc (2 : ℝ) ^ 40799 < ((2 : ℝ) ^ 409 / 2) ^ 100 := by norm_num
      _ < (Lcos p ^ 2 / 2) ^ 100 := by gcongr
  · calc (Lcos p ^ 2 / 2) ^ 100 < (1.0007 * (2 : ℝ) ^ 409 / 2) ^ 100 := by gcongr
      _ < 2 ^ 40801 := by norm_num

/-! ## Newton's constant from the ceiling (Sec. V, Prediction 2) -/

lemma Gof_eq (L : ℝ) : Gof p L = 4 * p * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * L ^ 2) := by
  unfold Gof; rw [RL_sq]; field_simp

/-- **The bracket**: a ceiling of 204 puts `G` between `G(2²⁰⁵) = 3.3×10⁻¹¹` and
`G(2²⁰⁴) = 1.3×10⁻¹⁰` (the Appendix's `3.34×10⁻¹¹` and `1.34×10⁻¹⁰`), and the measured value
lies inside. -/
theorem G_bracket (hp : PiBounds p) :
    (1.335e-10 < Gof p (2 ^ 204) ∧ Gof p (2 ^ 204) < 1.345e-10) ∧
    (3.335e-11 < Gof p (2 ^ 205) ∧ Gof p (2 ^ 205) < 3.345e-11) ∧
    (Gof p (2 ^ 205) < G₀ ∧ G₀ < Gof p (2 ^ 204)) := by
  have := hp.lo; have := hp.hi
  rw [Gof_eq, Gof_eq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · calc (1.335e-10 : ℝ) < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 204) ^ 2) := by
          norm_num
      _ < _ := by gcongr
  · calc _ < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 204) ^ 2) := by gcongr
      _ < (1.345e-10 : ℝ) := by norm_num
  · calc (3.335e-11 : ℝ) < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 205) ^ 2) := by
          norm_num
      _ < _ := by gcongr
  · calc _ < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 205) ^ 2) := by gcongr
      _ < (3.345e-11 : ℝ) := by norm_num
  · calc _ < 4 * 3.141593 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 205) ^ 2) := by gcongr
      _ < G₀ := by norm_num
  · calc G₀ < 4 * 3.141592 * c₀ ^ 5 / (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 204) ^ 2) := by norm_num
      _ < _ := by gcongr

/-- **At the middle of the bracket**: `G² / (G(2²⁰⁴) G(2²⁰⁵))` lies within 0.2 percent of one,
since `log₂ L_cos = 204.5`. -/
theorem G_mid (hp : PiBounds p) :
    0.998 < G₀ ^ 2 / (Gof p (2 ^ 204) * Gof p (2 ^ 205)) ∧
    G₀ ^ 2 / (Gof p (2 ^ 204) * Gof p (2 ^ 205)) < 1 := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  have e : G₀ ^ 2 / (Gof p (2 ^ 204) * Gof p (2 ^ 205))
      = G₀ ^ 2 * (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 204) ^ 2) * (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 205) ^ 2)
        / (16 * c₀ ^ 10) / p ^ 2 := by
    rw [Gof_eq, Gof_eq]; field_simp; ring
  rw [e]
  constructor
  · calc (0.998 : ℝ) < G₀ ^ 2 * (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 204) ^ 2) *
          (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 205) ^ 2) / (16 * c₀ ^ 10) / 3.141593 ^ 2 := by norm_num
      _ < _ := by gcongr
  · calc _ < G₀ ^ 2 * (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 204) ^ 2) *
          (ℏ₀ * (H₀ ^ 2 * ΩΛ₀) * (2 ^ 205) ^ 2) / (16 * c₀ ^ 10) / 3.141592 ^ 2 := by gcongr
      _ < (1 : ℝ) := by norm_num

/-! ## The solar scale (Sec. IV.B, Appendix A) -/

/-- The Sun: `α = M☉/m_c = 1.62×10³⁸`; the horizon is drawn in by `α/π = 5.15×10³⁷` cells;
`Lα = 5.9×10⁹⁹`, and `5.9×10¹¹⁰` for a galaxy of `10¹¹ M☉`. -/
theorem sun_counts (hp : PiBounds p) :
    (1.615e38 < αs p ∧ αs p < 1.625e38) ∧
    (5.145e37 < αs p / p ∧ αs p / p < 5.155e37) ∧
    (5.85e99 < Lcos p * αs p ∧ Lcos p * αs p < 5.95e99) ∧
    (5.85e110 < Lcos p * (1e11 * αs p) ∧ Lcos p * (1e11 * αs p) < 5.95e110) := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  have ha := αs_pos hp; have hL := Lcos_pos hp
  have hα : 1.615e38 < αs p ∧ αs p < 1.625e38 := by
    constructor
    · apply lt_of_sq ha.le (by norm_num)
      rw [αs_sq hp]
      calc (1.615e38 : ℝ) ^ 2 < 3.141592 * GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀) := by norm_num
        _ < _ := by gcongr
    · apply lt_of_sq' ha.le (by norm_num)
      rw [αs_sq hp]
      calc _ < 3.141593 * GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀) := by gcongr
        _ < (1.625e38 : ℝ) ^ 2 := by norm_num
  have eα : p * GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀) / p ^ 2 = GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀) / p := by
    field_simp
  have eL : 4 * p * c₀ ^ 5 / (ℏ₀ * G₀ * (H₀ ^ 2 * ΩΛ₀)) * (p * GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀))
      = p ^ 2 * (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) := by
    field_simp
  have hLα : 5.85e99 < Lcos p * αs p ∧ Lcos p * αs p < 5.95e99 := by
    constructor
    · apply lt_of_sq (by positivity) (by norm_num)
      rw [mul_pow, Lcos_sq hp, αs_sq hp, eL]
      calc (5.85e99 : ℝ) ^ 2 < 3.141592 ^ 2 *
            (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) := by norm_num
        _ < _ := by gcongr
    · apply lt_of_sq' (by positivity) (by norm_num)
      rw [mul_pow, Lcos_sq hp, αs_sq hp, eL]
      calc _ < 3.141593 ^ 2 *
            (4 * c₀ ^ 4 * GMs₀ ^ 2 / (ℏ₀ ^ 2 * G₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀))) := by gcongr
        _ < (5.95e99 : ℝ) ^ 2 := by norm_num
  have eg : Lcos p * (1e11 * αs p) = 1e11 * (Lcos p * αs p) := by ring
  refine ⟨hα, ⟨?_, ?_⟩, hLα, ?_, ?_⟩
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, αs_sq hp, eα]
    calc (5.145e37 : ℝ) ^ 2 < GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀) / 3.141593 := by norm_num
      _ < _ := by gcongr
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, αs_sq hp, eα]
    calc _ < GMs₀ ^ 2 / (G₀ * c₀ * ℏ₀) / 3.141592 := by gcongr
      _ < (5.155e37 : ℝ) ^ 2 := by norm_num
  · rw [eg]; linarith [hLα.1]
  · rw [eg]; linarith [hLα.2]

/-- Earth's orbit: `n = 1 au/ℓ_c = 5.22×10⁴⁵` and `GM☉/r² = 5.93×10⁻³ m/s²`; the push there is
`c²r/R_Λ² = 5×10⁻²⁵ m/s²`; solar gravity at 1 au exceeds `a_M` by `10^7.6`, "eight orders". -/
theorem earth_orbit (hp : PiBounds p) :
    (5.215e45 < au₀ / lc p ∧ au₀ / lc p < 5.225e45) ∧
    (5.925e-3 < GMs₀ / au₀ ^ 2 ∧ GMs₀ / au₀ ^ 2 < 5.935e-3) ∧
    (4.85e-25 < c₀ ^ 2 * au₀ / RL ^ 2 ∧ c₀ ^ 2 * au₀ / RL ^ 2 < 4.95e-25) ∧
    (10 ^ 15 < (GMs₀ / au₀ ^ 2 / aM p) ^ 2 ∧ (GMs₀ / au₀ ^ 2 / aM p) ^ 2 < 10 ^ 16) := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos; have hl := lc_pos hp
  have ha := aM_pos hp
  refine ⟨⟨?_, ?_⟩, ⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, lc_sq hp]
    calc (5.215e45 : ℝ) ^ 2 < au₀ ^ 2 / (3.141593 * ℏ₀ * G₀ / c₀ ^ 3) := by norm_num
      _ < _ := by gcongr
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, lc_sq hp]
    calc _ < au₀ ^ 2 / (3.141592 * ℏ₀ * G₀ / c₀ ^ 3) := by gcongr
      _ < (5.225e45 : ℝ) ^ 2 := by norm_num
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num
  · rw [div_pow, aM_sq hp]
    calc (10 : ℝ) ^ 15 < (GMs₀ / au₀ ^ 2) ^ 2 /
          (3.141593 ^ 2 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144) := by norm_num
      _ < _ := by gcongr
  · rw [div_pow, aM_sq hp]
    calc _ < (GMs₀ / au₀ ^ 2) ^ 2 / (3.141592 ^ 2 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144) := by gcongr
      _ < (10 : ℝ) ^ 16 := by norm_num

/-- Mercury's anomalous advance `6πGM☉/(a(1−e²)c²)` per orbit is `5.0×10⁻⁷ rad`, and per century
`42.98″` (the `π` of the advance cancels the `π` of the conversion to arcseconds); the
deflection of starlight at the solar limb `4GM☉/(c²R☉)` is `1.75″`. -/
theorem solar_tests (hp : PiBounds p) :
    (5.0e-7 < 6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) ∧
      6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) < 5.05e-7) ∧
    (42.975 < 6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
        (648000 / p) ∧
      6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
        (648000 / p) < 42.985) ∧
    (1.75 < 4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / p) ∧
      4 * GMs₀ / (c₀ ^ 2 * Rs₀) * (648000 / p) < 1.755) := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  have e : 6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
      (648000 / p) = 6 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * (36525 / 87.9691) *
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

/-- The kinematic effect of a `2π/L` phase grid, `1.7×10⁻⁶¹ rad`, lies fifty-four orders of
magnitude below Mercury's `5×10⁻⁷ rad` per orbit: the ratio is between `10⁵⁴` and `10⁵⁵`. -/
theorem phase_grid (hp : PiBounds p) :
    (1.7e-61 < 2 * p / Lcos p ∧ 2 * p / Lcos p < 1.75e-61) ∧
    (10 ^ 54 < 6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * p / Lcos p) ∧
      6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * p / Lcos p) < 10 ^ 55) := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  obtain ⟨h1, h2⟩ := Lcos_val hp
  have hL := Lcos_pos hp
  have e : 6 * p * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) / (2 * p / Lcos p)
      = 3 * GMs₀ / (57909050e3 * (1 - 0.205630 ^ 2) * c₀ ^ 2) * Lcos p := by
    field_simp; norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hL]; nlinarith
  · rw [div_lt_iff₀ hL]; nlinarith
  · rw [e]; nlinarith
  · rw [e]; nlinarith

/-! ## The galactic scale (Sec. IV.C, Table I) -/

/-- **Eq. (aM)**: `a_M = πc²/12R_Λ = 1.42×10⁻¹⁰ m/s²`, and Verlinde's `c²/6R_Λ = 0.90×10⁻¹⁰`. -/
theorem aM_val (hp : PiBounds p) :
    (1.415e-10 < aM p ∧ aM p < 1.425e-10) ∧
    (0.895e-10 < c₀ ^ 2 / (6 * RL) ∧ c₀ ^ 2 / (6 * RL) < 0.905e-10) := by
  have := hp.lo; have := hp.hi
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq (aM_pos hp).le (by norm_num)
    rw [aM_sq hp]
    calc (1.415e-10 : ℝ) ^ 2 < 3.141592 ^ 2 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144 := by norm_num
      _ < _ := by gcongr
  · apply lt_of_sq' (aM_pos hp).le (by norm_num)
    rw [aM_sq hp]
    calc _ < 3.141593 ^ 2 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144 := by gcongr
      _ < (1.425e-10 : ℝ) ^ 2 := by norm_num
  · have := RL_pos
    apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num
  · have := RL_pos
    apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num

/-- The chain's `a_M` with these inputs (`reg_aM`) is the same number. -/
theorem reg_aM_val (hp : PiBounds p) : 1.415e-10 < (reg hp).aM 4 ∧ (reg hp).aM 4 < 1.425e-10 := by
  rw [reg_aM]; exact (aM_val hp).1

/-- A tighter enclosure of `a_M`. -/
lemma aM_tight (hp : PiBounds p) : 1.4185e-10 < aM p ∧ aM p < 1.4190e-10 := by
  have := hp.lo; have := hp.hi
  have ha := aM_pos hp
  constructor
  · apply lt_of_sq ha.le (by norm_num); rw [aM_sq hp]
    calc (1.4185e-10 : ℝ) ^ 2 < 3.141592 ^ 2 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144 := by norm_num
      _ < _ := by gcongr
  · apply lt_of_sq' ha.le (by norm_num); rw [aM_sq hp]
    calc _ < 3.141593 ^ 2 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / 144 := by gcongr
      _ < (1.4190e-10 : ℝ) ^ 2 := by norm_num

/-- **Against observation**: `a₀/a_M = 0.85` ("observation saturates 85 percent of the bound");
`(a_M − 1.20)/0.24 = 0.9σ` (McGaugh 2016) and `(a_M − 1.19)/0.10 = 2.3σ` (Desmond 2023). -/
theorem aM_vs_observation (hp : PiBounds p) :
    (0.845 < a₀ / aM p ∧ a₀ / aM p < 0.855) ∧
    (0.85 < (aM p - a₀) / 0.24e-10 ∧ (aM p - a₀) / 0.24e-10 < 0.95) ∧
    (2.25 < (aM p - 1.19e-10) / 0.10e-10 ∧ (aM p - 1.19e-10) / 0.10e-10 < 2.35) := by
  obtain ⟨t1, t2⟩ := aM_tight hp
  have ha := aM_pos hp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ ha]; nlinarith
  · rw [div_lt_iff₀ ha]; nlinarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- The coefficients of Sec. IV.C and Appendix A: `γ = a₀/(c²/2πR_Λ) = 1.39` measured against
`π²/6 = 1.645` here (`1.64` to three figures); `a₀/cH_∞ = 0.22` observed against `π/12 = 0.26`
here. -/
theorem coefficients (hp : PiBounds p) :
    (1.385 < 2 * p * a₀ * RL / c₀ ^ 2 ∧ 2 * p * a₀ * RL / c₀ ^ 2 < 1.395) ∧
    (1.6445 < p ^ 2 / 6 ∧ p ^ 2 / 6 < 1.645) ∧
    (0.215 < a₀ / (c₀ * Hinf) ∧ a₀ / (c₀ * Hinf) < 0.225) ∧
    (0.2615 < p / 12 ∧ p / 12 < 0.2625) := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  have hR := RL_pos; have hH := Hinf_pos
  obtain ⟨r1, r2⟩ := RL_val
  obtain ⟨k1, k2⟩ := Hinf_val
  obtain ⟨s1, s2⟩ := RL_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith
  · nlinarith
  · nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · linarith
  · linarith

/-- **`L` from galaxies**, Eq. (Lgal): `L_gal = 4.30×10⁶¹`, with the same ceiling,
`2²⁰⁴ < L_gal < 2²⁰⁵`, and `2⁴⁰⁹⁴⁷ < L_gal²⁰⁰ < 2⁴⁰⁹⁴⁹`, that is,
`204.735 < log₂ L_gal < 204.745`. -/
theorem Lgal_val (hp : PiBounds p) :
    (4.295e61 < Lgal p ∧ Lgal p < 4.305e61) ∧
    ((2 : ℝ) ^ 204 < Lgal p ∧ Lgal p < 2 ^ 205) ∧
    ((2 : ℝ) ^ 40947 < Lgal p ^ 200 ∧ Lgal p ^ 200 < 2 ^ 40949) := by
  have := hp.lo; have := hp.hi
  have hL := Lgal_pos hp
  have b1 : 2.797 * (2 : ℝ) ^ 408 < Lgal p ^ 2 := by
    rw [Lgal_sq hp]
    calc 2.797 * (2 : ℝ) ^ 408 < 3.141592 ^ 3 * c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀) := by norm_num
      _ < _ := by gcongr
  have b2 : Lgal p ^ 2 < 2.799 * (2 : ℝ) ^ 408 := by
    rw [Lgal_sq hp]
    calc _ < 3.141593 ^ 3 * c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀) := by gcongr
      _ < 2.799 * (2 : ℝ) ^ 408 := by norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq hL.le (by norm_num)
    rw [Lgal_sq hp]
    calc (4.295e61 : ℝ) ^ 2 < 3.141592 ^ 3 * c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀) := by norm_num
      _ < _ := by gcongr
  · apply lt_of_sq' hL.le (by norm_num)
    rw [Lgal_sq hp]
    calc _ < 3.141593 ^ 3 * c₀ ^ 7 / (36 * a₀ ^ 2 * ℏ₀ * G₀) := by gcongr
      _ < (4.305e61 : ℝ) ^ 2 := by norm_num
  · apply lt_of_sq hL.le (by positivity)
    calc ((2 : ℝ) ^ 204) ^ 2 < 2.797 * (2 : ℝ) ^ 408 := by norm_num
      _ < _ := b1
  · apply lt_of_sq' hL.le (by positivity)
    calc _ < 2.799 * (2 : ℝ) ^ 408 := b2
      _ < ((2 : ℝ) ^ 205) ^ 2 := by norm_num
  · have e : Lgal p ^ 200 = (Lgal p ^ 2) ^ 100 := by ring
    rw [e]
    calc (2 : ℝ) ^ 40947 < (2.797 * (2 : ℝ) ^ 408) ^ 100 := by norm_num
      _ < (Lgal p ^ 2) ^ 100 := by gcongr
  · have e : Lgal p ^ 200 = (Lgal p ^ 2) ^ 100 := by ring
    rw [e]
    calc (Lgal p ^ 2) ^ 100 < (2.799 * (2 : ℝ) ^ 408) ^ 100 := by gcongr
      _ < 2 ^ 40949 := by norm_num

/-- **`N_max = 204`** from galaxies as well: `2^N ≤ L_gal` exactly when `N ≤ 204`. -/
theorem nmax_gal (hp : PiBounds p) (N : ℕ) : (2 : ℝ) ^ N ≤ Lgal p ↔ N ≤ 204 :=
  nmax_of_bounds (Lgal_val hp).2.1.1 (Lgal_val hp).2.1.2 N

/-- **The two pins agree to eighteen percent, a quarter of a bit**: `L_gal/L_cos = 1.18`, and
`2²⁴ < (L_gal/L_cos)¹⁰⁰ < 2²⁵`, that is, `0.24 < log₂(L_gal/L_cos) < 0.25`. -/
theorem pins_agree (hp : PiBounds p) :
    (1.175 < Lgal p / Lcos p ∧ Lgal p / Lcos p < 1.185) ∧
    ((2 : ℝ) ^ 24 < (Lgal p / Lcos p) ^ 100 ∧ (Lgal p / Lcos p) ^ 100 < 2 ^ 25) := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  have hg := Lgal_pos hp; have hc := Lcos_pos hp
  have e : (Lgal p / Lcos p) ^ 2 = p ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (144 * a₀ ^ 2)) := by
    rw [div_pow, Lgal_sq hp, Lcos_sq hp]; field_simp; ring
  have b1 : 1.398 < (Lgal p / Lcos p) ^ 2 := by
    rw [e]
    calc (1.398 : ℝ) < 3.141592 ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (144 * a₀ ^ 2)) := by norm_num
      _ < _ := by gcongr
  have b2 : (Lgal p / Lcos p) ^ 2 < 1.3982 := by
    rw [e]
    calc _ < 3.141593 ^ 2 * (c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (144 * a₀ ^ 2)) := by gcongr
      _ < (1.3982 : ℝ) := by norm_num
  have hq : 0 < Lgal p / Lcos p := by positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply lt_of_sq hq.le (by norm_num); linarith [show (1.175 : ℝ) ^ 2 < 1.398 by norm_num]
  · apply lt_of_sq' hq.le (by norm_num); linarith [show (1.3982 : ℝ) < 1.185 ^ 2 by norm_num]
  · have e2 : (Lgal p / Lcos p) ^ 100 = ((Lgal p / Lcos p) ^ 2) ^ 50 := by ring
    rw [e2]
    calc (2 : ℝ) ^ 24 < (1.398 : ℝ) ^ 50 := by norm_num
      _ < _ := by gcongr
  · have e2 : (Lgal p / Lcos p) ^ 100 = ((Lgal p / Lcos p) ^ 2) ^ 50 := by ring
    rw [e2]
    calc ((Lgal p / Lcos p) ^ 2) ^ 50 < (1.3982 : ℝ) ^ 50 := by gcongr
      _ < 2 ^ 25 := by norm_num

/-- **Why the temperature cannot lead**: `2c²/R_Λ` is nine times the observed `a₀`, and
`√(1 + 2a_Λ/g_N)` at `g_N = 10a₀` is `1.38`, a transition 38 percent above Newton. -/
theorem temperature_led_numbers :
    (9.0 < 2 * c₀ ^ 2 / (RL * a₀) ∧ 2 * c₀ ^ 2 / (RL * a₀) < 9.1) ∧
    (1.375 < Real.sqrt (1 + 2 * (c₀ ^ 2 / RL) / (10 * a₀)) ∧
      Real.sqrt (1 + 2 * (c₀ ^ 2 / RL) / (10 * a₀)) < 1.385) := by
  have hR := RL_pos; have hH := Hinf_pos
  have e1 : 2 * c₀ ^ 2 / (RL * a₀) = 2 * c₀ * Hinf / a₀ := by unfold RL; field_simp
  have e2 : c₀ ^ 2 / RL = c₀ * Hinf := by unfold RL; field_simp
  obtain ⟨k1, k2⟩ := Hinf_val
  obtain ⟨j1, j2⟩ := Hinf_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [e1, lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [e1, div_lt_iff₀ (by norm_num)]; nlinarith
  · rw [e2, Real.lt_sqrt (by norm_num)]
    rw [show (1.375 : ℝ) ^ 2 = 1.890625 by norm_num]
    have : (1.890625 : ℝ) < 1 + 2 * (c₀ * 1.8078e-18) / (10 * a₀) := by norm_num
    have h3 : 2 * (c₀ * 1.8078e-18) / (10 * a₀) < 2 * (c₀ * Hinf) / (10 * a₀) := by gcongr
    linarith
  · rw [e2, Real.sqrt_lt' (by norm_num)]
    have : 1 + 2 * (c₀ * 1.8079e-18) / (10 * a₀) < (1.385 : ℝ) ^ 2 := by norm_num
    have h3 : 2 * (c₀ * Hinf) / (10 * a₀) < 2 * (c₀ * 1.8079e-18) / (10 * a₀) := by gcongr
    linarith

/-- **The Tully–Fisher speed** of a `10¹¹ M☉` galaxy: `v_c⁴ = a_M G M`, `v_c = 208 km/s`. -/
theorem tully_fisher_speed (hp : PiBounds p) :
    (208e3 : ℝ) ^ 4 < aM p * (1e11 * GMs₀) ∧ aM p * (1e11 * GMs₀) < (208.5e3 : ℝ) ^ 4 := by
  obtain ⟨h1, h2⟩ := aM_tight hp
  constructor <;> nlinarith

/-! ## The cosmological scale (Sec. IV.D, Table I) -/

/-- **Eq. (EL)**: `E_Λ = c⁴R_Λ/2G = 1.00×10⁷⁰ J`, and the chain's `E_Λ = LE_c/4` is this number. -/
theorem EΛ_val (hp : PiBounds p) :
    (reg hp).EΛ = c₀ ^ 4 * RL / (2 * G₀) ∧
    1.00e70 < c₀ ^ 4 * RL / (2 * G₀) ∧ c₀ ^ 4 * RL / (2 * G₀) < 1.005e70 := by
  have hR := RL_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [((reg hp).EΛ_eq G₀ (reg_jacobson hp)).2, reg_RL]; rfl
  · apply lt_of_sq (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num
  · apply lt_of_sq' (by positivity) (by norm_num)
    rw [div_pow, mul_pow, RL_sq]; norm_num

/-- **The vacuum energy density**: the chain's `ρ_Λ = 3π²ρ_c/2L²` equals `Λc⁴/8πG`, which is
`5.25×10⁻¹⁰ J/m³` (`5.3` to two figures, as in Sec. IV.D). -/
theorem ρΛ_val (hp : PiBounds p) :
    (reg hp).ρΛ = 3 / RL ^ 2 * c₀ ^ 4 / (8 * p * G₀) ∧
    5.25e-10 < 3 / RL ^ 2 * c₀ ^ 4 / (8 * p * G₀) ∧
    3 / RL ^ 2 * c₀ ^ 4 / (8 * p * G₀) < 5.255e-10 := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  have e : 3 / RL ^ 2 * c₀ ^ 4 / (8 * p * G₀) = 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / p := by
    rw [RL_sq]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have h := ((reg hp).ρΛ_eq G₀ (3 / RL ^ 2) (reg_jacobson hp) (reg_deSitter hp)).2
    rw [h]; rfl
  · rw [e]
    calc (5.25e-10 : ℝ) < 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / 3.141593 := by norm_num
      _ < _ := by gcongr
  · rw [e]
    calc _ < 3 * c₀ ^ 2 * (H₀ ^ 2 * ΩΛ₀) / (8 * G₀) / 3.141592 := by gcongr
      _ < (5.255e-10 : ℝ) := by norm_num

/-- **Eq. (Lambda)**: the chain's `GΛ = 12πc³/ℏL²` for these inputs is `7.28×10⁻⁶³`. -/
theorem GΛ_val (hp : PiBounds p) :
    G₀ * (3 / RL ^ 2) = 12 * p * c₀ ^ 3 / (ℏ₀ * Lcos p ^ 2) ∧
    7.275e-63 < G₀ * (3 / RL ^ 2) ∧ G₀ * (3 / RL ^ 2) < 7.285e-63 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := ((reg hp).G_Lambda G₀ (3 / RL ^ 2) (reg_jacobson hp) (reg_deSitter hp)).1
    rw [h]; rfl
  · rw [RL_sq]; norm_num
  · rw [RL_sq]; norm_num

/-- **The horizon's temperature**: `k_B T_dS = ℏH_∞/2π = E_c/L = 3.0×10⁻⁵³ J`; the reduction
clock `τ* = 2π/H_∞ = 3.5×10¹⁸ s = 1.1×10¹¹ yr`. -/
theorem temperature_and_clock (hp : PiBounds p) :
    (3.03e-53 < ℏ₀ * Hinf / (2 * p) ∧ ℏ₀ * Hinf / (2 * p) < 3.035e-53) ∧
    (3.47e18 < 2 * p / Hinf ∧ 2 * p / Hinf < 3.48e18) ∧
    (1.09e11 < 2 * p / Hinf / yr₀ ∧ 2 * p / Hinf / yr₀ < 1.11e11) := by
  have := hp.lo; have := hp.hi; have hp0 := hp.pos
  have hH := Hinf_pos
  obtain ⟨j1, j2⟩ := Hinf_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ hH]; nlinarith
  · rw [div_lt_iff₀ hH]; nlinarith
  · rw [div_div, lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_div, div_lt_iff₀ (by positivity)]; nlinarith

/-- The chain's temperature `E_c/L` for these inputs is `ℏH_∞/2π` (Eq. (energy)). -/
theorem reg_temperature (hp : PiBounds p) :
    (reg hp).Ec / (reg hp).L = ℏ₀ * Hinf / (2 * p) := by
  have := hp.pos; have := lc_pos hp; have := Hinf_pos
  simp only [Reg.Ec, reg]
  unfold Lcos RL
  field_simp

/-- **The zero-velocity radius** `r_z³ = GMR_Λ²/c²`: `111 pc` for the Sun and `1.6 Mpc` for the
Local Group at `3×10¹² M☉`. -/
theorem zero_velocity_radii :
    ((111 * pc₀) ^ 3 < GMs₀ * RL ^ 2 / c₀ ^ 2 ∧ GMs₀ * RL ^ 2 / c₀ ^ 2 < (111.5 * pc₀) ^ 3) ∧
    ((1.55 * Mpc₀) ^ 3 < 3e12 * GMs₀ * RL ^ 2 / c₀ ^ 2 ∧
      3e12 * GMs₀ * RL ^ 2 / c₀ ^ 2 < (1.65 * Mpc₀) ^ 3) := by
  rw [RL_sq]
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- **The crossover** of the deep pull and the push, `r⁴ = R_Λ⁴ a_M GM/c⁴`: `3.7 Mpc` for
`10¹¹ M☉`. -/
theorem crossover_radius (hp : PiBounds p) :
    (3.7 * Mpc₀) ^ 4 < RL ^ 4 * aM p * (1e11 * GMs₀) / c₀ ^ 4 ∧
    RL ^ 4 * aM p * (1e11 * GMs₀) / c₀ ^ 4 < (3.75 * Mpc₀) ^ 4 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := aM_val hp
  have e : RL ^ 4 = (RL ^ 2) ^ 2 := by ring
  rw [e, RL_sq]
  constructor
  · calc (3.7 * Mpc₀) ^ 4 < (c₀ ^ 2 / (H₀ ^ 2 * ΩΛ₀)) ^ 2 * 1.415e-10 * (1e11 * GMs₀) / c₀ ^ 4 := by
          norm_num
      _ < _ := by gcongr
  · calc _ < (c₀ ^ 2 / (H₀ ^ 2 * ΩΛ₀)) ^ 2 * 1.425e-10 * (1e11 * GMs₀) / c₀ ^ 4 := by gcongr
      _ < (3.75 * Mpc₀) ^ 4 := by norm_num

/-! ## Predictions (Sec. VI) -/

/-- `a₀ ∝ cH(z)` predicts a scale `H(1)/H₀ = √(Ω_m·8 + Ω_Λ) = 1.8` times larger at `z = 1`. -/
theorem redshift_one : 1.785 < Real.sqrt (0.315 * 8 + 0.685) ∧ Real.sqrt (0.315 * 8 + 0.685) < 1.795 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The equation of state**: with `H₀ = 6.89×10⁻¹¹ yr⁻¹`, `|1 + w₀| ≲ 10⁻¹³/3H₀ = 4.8×10⁻⁴`;
the drift a Hubble-radius horizon would give, `Ġ/G = 2H(1+q) ≈ 6×10⁻¹¹ yr⁻¹` at `q = −0.53`, is
six hundred times the lunar-laser-ranging bound `10⁻¹³ yr⁻¹`. -/
theorem constancy_numbers :
    (6.885e-11 < H₀ * yr₀ ∧ H₀ * yr₀ < 6.895e-11) ∧
    (4.8e-4 < 1e-13 / (3 * (H₀ * yr₀)) ∧ 1e-13 / (3 * (H₀ * yr₀)) < 4.85e-4) ∧
    (5.5e-11 < 2 * (H₀ * yr₀) * (1 - 0.53) ∧ 2 * (H₀ * yr₀) * (1 - 0.53) < 6.5e-11) ∧
    (550 < 2 * (H₀ * yr₀) * (1 - 0.53) / 1e-13 ∧ 2 * (H₀ * yr₀) * (1 - 0.53) / 1e-13 < 650) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩⟩

end Numerics
end Register
