import RegisterGravity.Chain
import RegisterGravity.Einstein
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The constant `Λ` of the equations, and the limit of the solution's horizon (Secs. III and IV.D)

Formal counterpart of three sentences of the paper about the cosmological constant and the
Schwarzschild–de Sitter solution.

* `Einstein.vacuumModel`, `Einstein.any_constant_model`: "Einstein's equations, Eq. (einstein),
  leave the value of `Λ` free" (Sec. IV.D).  The three inputs from which the files derive the
  equations hold, for every value of `Λ`, on the vacuum spacetime with `R_ab = Λ g_ab`, and the
  equations hold there with that value of the constant and with no other.
* `Einstein.quad_add_smul_eta_of_null`: "The zero-point energy of the fields does not set `Λ`,
  which enters Einstein's equations as an integration constant" (Sec. IV.D).  A term `c g_ab` of
  the stress tensor, a vacuum energy, has the value zero on every null vector, so Jacobson's step,
  which takes `T_ab k^a k^b` on null vectors alone, does not see it (`Main.vacuum_energy_unseen`
  states this for the step).
* `Reg.horizon_limit`: of the Schwarzschild–de Sitter solution the paper "reads off the surface
  gravity of its horizons and the limit up to which it has them" (Sec. III).  The surface gravity
  is the field at the horizon, `Reg.gSdS` (`Chain.lean`, with `DeSitter.surface_gravity_eq` for its
  value without a mass).  The limit is derived here: with the metric function
  `f(r) = 1 − 2m/r − Λr²/3`, `m = GM/c²` (`Reg.fSdS`), a horizon is a radius `r > 0` with
  `f(r) = 0`, and for `M > 0` and `Λ > 0` such a radius exists exactly when `9Λm² ≤ 1`.  With
  `Λ = 3/R_Λ²` the limit is `GM/c²R_Λ ≤ 1/(3√3)`, Nariai's limit, the number `0.19` that
  `Numerics.cosmic_mass_beyond_nariai` compares the matter of the universe with.

* `Reg.La_lt_L`: "the horizon of an observer held at solar radii is his own, `L_a ≪ L`, since
  `a ≫ c²/R_Λ` there" (Sec. IV.B).  The period of an accelerated observer's horizon, in ticks, is
  to `L` as `c²/R_Λ` is to his acceleration.

The proof of the limit.  For `r > 0`, `f(r) = 0` exactly when `p(r) = r − 2m − Λr³/3` vanishes.
If it does, then with `x = Λr²` one has `2m = r(1 − x/3)`, so `x < 3` and
`4 − 36Λm² = (x − 1)²(4 − x) ≥ 0`.  Conversely `p(0) = −2m < 0`, and at `r₀ = 1/√Λ`,
`p(r₀) = 2r₀/3 − 2m ≥ 0` when `3m ≤ r₀`, which is `9Λm² ≤ 1`; `p` is continuous, so it vanishes
between.
-/

namespace Register.Einstein

open Matrix

/-- **A term of the stress tensor that is a multiple of the metric has no flux through null
surfaces** (Sec. IV.D: "The zero-point energy of the fields does not set `Λ`, which enters
Einstein's equations as an integration constant").  For a null vector `k`, the form of
`S + c g` on `k` is the form of `S`: `g_ab k^a k^b = 0`.  Jacobson's step takes only the values
`T_ab k^a k^b` on null vectors, so it does not see a vacuum energy `c g_ab` in the stress tensor,
whatever `c`. -/
theorem quad_add_smul_eta_of_null (S : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (k : Fin 4 → ℝ)
    (hk : IsNull k) : quad (S + c • eta) k = quad S k := by
  have h : S + c • eta = S - (-c) • eta := by
    rw [neg_smul, sub_neg_eq_add]
  have hk' : quad eta k = 0 := hk
  rw [h, quad_sub, quad_smul, hk', mul_zero, sub_zero]

/-- **The vacuum with the constant `Λ`**, as the files see a spacetime: no matter, and the Ricci
tensor `R_ab = Λ g_ab` at every point.  These are the Ricci tensor and the stress tensor of de
Sitter space for `Λ > 0`, of Minkowski space for `Λ = 0` and of anti-de Sitter space for `Λ < 0`
[R. M. Wald, *General Relativity* (1984), Sec. 5.2]. -/
def vacuumModel (Pt : Type) (Λ : ℝ) : Spacetime where
  Pt := Pt
  ric := fun _ => Λ • eta
  stress := fun _ => 0
  divStress := fun _ => 0
  ric_symm := fun _ => by
    unfold Matrix.IsSymm eta
    rw [transpose_smul, diagonal_transpose]

/-- **The inputs of Einstein's equations hold with any value of `Λ`** (Sec. IV.D: "Einstein's
equations, Eq. (einstein), leave the value of `Λ` free").  On the vacuum with the constant `Λ`
(`vacuumModel`), for every `Λ` and every coefficient `κ`, the three inputs from which the files
derive the equations hold: Jacobson's step on every null vector, the first law for every
observer, and the Bianchi identity.  These are the hypotheses of `einstein_equations`, which are
the conclusion of `Sources.Derived.clausius`, `Sources.Thermo.first_law_local` and
`Sources.Geometry.bianchi` written out, since `Sources.lean` stands after this file.  The
equations hold there with the constant `Λ`, and with no other value where the spacetime has a
point.  So the inputs fix no value of the constant: it enters as a number that they leave free,
and Sec. IV.D finds it from the horizon (`Main.deSitter_horizon`). -/
theorem any_constant_model (Pt : Type) (κ Λ : ℝ) :
    (∀ p k, IsNull k → quad ((vacuumModel Pt Λ).ric p) k
      = κ * quad ((vacuumModel Pt Λ).stress p) k) ∧
    (∀ p u, IsTimelike u → (vacuumModel Pt Λ).divStress p ⬝ᵥ u = 0) ∧
    (∀ φ : (vacuumModel Pt Λ).Pt → ℝ,
      (∀ p, (vacuumModel Pt Λ).ric p - κ • symmPart ((vacuumModel Pt Λ).stress p) = φ p • eta) →
      (∀ p, (vacuumModel Pt Λ).divStress p = 0) →
      ∀ p q, φ p + κ / 2 * trace (symmPart ((vacuumModel Pt Λ).stress p))
        = φ q + κ / 2 * trace (symmPart ((vacuumModel Pt Λ).stress q))) ∧
    FieldEquations (vacuumModel Pt Λ) κ Λ ∧
    (Nonempty Pt → ∀ Λ', FieldEquations (vacuumModel Pt Λ) κ Λ' → Λ' = Λ) := by
  have hz : symmPart (0 : Matrix (Fin 4) (Fin 4) ℝ) = 0 := by simp [symmPart]
  have ht : trace (Λ • eta) = 4 * Λ := by
    simp [trace, eta, diagonal]
    ring
  have h00 : eta 0 0 = -1 := by simp [eta]
  refine ⟨fun p k hk => ?_, fun p u _ => ?_, fun φ hφ _ p q => ?_, fun p => ?_, fun ⟨p⟩ Λ' h => ?_⟩
  · show quad (Λ • eta) k = κ * quad (0 : Matrix (Fin 4) (Fin 4) ℝ) k
    have hk' : quad eta k = 0 := hk
    rw [quad_smul, hk', mul_zero]
    simp [quad]
  · show (0 : Fin 4 → ℝ) ⬝ᵥ u = 0
    simp
  · have hφ' : ∀ r, φ r = Λ := by
      intro r
      have h := hφ r
      have h1 : Λ • eta - κ • symmPart (0 : Matrix (Fin 4) (Fin 4) ℝ) = φ r • eta := h
      rw [hz, smul_zero, sub_zero] at h1
      have h2 := congrFun (congrFun h1 0) 0
      simp only [Matrix.smul_apply, smul_eq_mul, h00] at h2
      linarith
    rw [hφ' p, hφ' q]
    rfl
  · show Λ • eta - (trace (Λ • eta) / 2) • eta + Λ • eta = κ • symmPart 0
    rw [ht, hz, smul_zero, ← sub_smul, ← add_smul]
    have : Λ - 4 * Λ / 2 + Λ = 0 := by ring
    rw [this, zero_smul]
  · have h1 : Λ • eta - (trace (Λ • eta) / 2) • eta + Λ' • eta = κ • symmPart 0 := h p
    rw [ht, hz, smul_zero, ← sub_smul, ← add_smul] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp only [Matrix.smul_apply, smul_eq_mul, h00, Matrix.zero_apply] at h2
    linarith

end Register.Einstein

namespace Register
namespace Reg

variable (R : Reg)

/-- **An accelerated observer's horizon is his own** (Sec. IV.B: "the horizon of an observer held
at solar radii is his own, `L_a ≪ L`, since `a ≫ c²/R_Λ` there").  The period of the horizon of
an observer held at the acceleration `a`, in ticks, is `L_a = 2πc²/aℓ_c` (`La`).  It is to `L` as
the surface gravity of the cosmological horizon, `c²/R_Λ`, is to `a`, so `L_a < L` exactly where
`a` exceeds `c²/R_Λ`. -/
theorem La_lt_L (a : ℝ) (ha : 0 < a) :
    R.La a / R.L = (R.c ^ 2 / R.RL) / a ∧ (R.La a < R.L ↔ R.c ^ 2 / R.RL < a) := by
  reg_facts R
  have hRL := R.RL_pos
  have hL : (0 : ℝ) < R.L := by
    have h := hRL
    unfold RL at h
    by_contra hno
    have hle : R.L ≤ 0 := not_lt.1 hno
    have : R.L * R.ℓc / (2 * R.pi) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg hle (by positivity)
      · positivity
    linarith
  have hratio : R.La a / R.L = (R.c ^ 2 / R.RL) / a := by
    unfold La RL
    field_simp
  refine ⟨hratio, ?_⟩
  rw [← div_lt_one hL, hratio, div_lt_one ha]

/-- **The limit up to which the solution has a horizon** (Secs. III and IV.D).  About a mass
`M > 0`, with a constant `Λ > 0`, the Schwarzschild–de Sitter solution has a horizon, a radius
`r > 0` at which its metric function `f(r) = 1 − 2GM/c²r − Λr²/3` vanishes, exactly when
`9Λ(GM/c²)² ≤ 1`. -/
theorem horizon_limit (G M Λ : ℝ) (hG : 0 < G) (hM : 0 < M) (hΛ : 0 < Λ) :
    (∃ r, 0 < r ∧ R.fSdS G M Λ r = 0) ↔ 9 * Λ * (G * M / R.c ^ 2) ^ 2 ≤ 1 := by
  have hc := R.c_pos
  obtain ⟨m, hm⟩ : ∃ m, m = G * M / R.c ^ 2 := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hfr : ∀ r, 0 < r → R.fSdS G M Λ r * r = r - 2 * m - Λ * r ^ 3 / 3 := by
    intro r hr
    unfold fSdS
    rw [hm]
    field_simp
  rw [← hm]
  constructor
  · rintro ⟨r, hr, h0⟩
    have hp : r - 2 * m - Λ * r ^ 3 / 3 = 0 := by rw [← hfr r hr, h0, zero_mul]
    have hm2 : m = (r - Λ * r ^ 3 / 3) / 2 := by linarith
    have hx3 : Λ * r ^ 2 < 3 := by
      have h2m : 0 < r * (1 - Λ * r ^ 2 / 3) := by
        have : r * (1 - Λ * r ^ 2 / 3) = 2 * m := by rw [hm2]; ring
        rw [this]; linarith
      have := (mul_pos_iff_of_pos_left hr).1 h2m
      linarith
    have key : 4 - 36 * Λ * m ^ 2 = (Λ * r ^ 2 - 1) ^ 2 * (4 - Λ * r ^ 2) := by
      rw [hm2]; ring
    have hnn : 0 ≤ (Λ * r ^ 2 - 1) ^ 2 * (4 - Λ * r ^ 2) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  · intro h
    have hs : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
    have hs2 : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ.le
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = 1 / Real.sqrt Λ := ⟨_, rfl⟩
    have hr₀pos : 0 < r₀ := by rw [hr₀]; positivity
    have hΛr : Λ * r₀ ^ 2 = 1 := by
      have hΛ' := hΛ.ne'
      rw [hr₀, div_pow, one_pow, hs2]
      field_simp
    have h3m : 3 * m ≤ r₀ := by
      by_contra hcon
      push Not at hcon
      have h1 : r₀ ^ 2 < (3 * m) ^ 2 := by nlinarith
      have h2 : Λ * r₀ ^ 2 < Λ * (3 * m) ^ 2 := mul_lt_mul_of_pos_left h1 hΛ
      rw [hΛr] at h2
      nlinarith
    have hcont : ContinuousOn (fun r : ℝ => r - 2 * m - Λ * r ^ 3 / 3) (Set.Icc 0 r₀) := by
      fun_prop
    have h0 : (fun r : ℝ => r - 2 * m - Λ * r ^ 3 / 3) 0 ≤ 0 := by
      simp only
      nlinarith
    have h1 : 0 ≤ (fun r : ℝ => r - 2 * m - Λ * r ^ 3 / 3) r₀ := by
      simp only
      have : Λ * r₀ ^ 3 = r₀ := by
        rw [show Λ * r₀ ^ 3 = (Λ * r₀ ^ 2) * r₀ by ring, hΛr, one_mul]
      rw [this]
      linarith
    obtain ⟨r, hr, hpr⟩ := intermediate_value_Icc hr₀pos.le hcont ⟨h0, h1⟩
    simp only at hpr
    have hr0 : r ≠ 0 := by
      rintro rfl
      nlinarith
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    refine ⟨r, hrpos, ?_⟩
    have hmul := hfr r hrpos
    rw [hpr] at hmul
    exact (mul_eq_zero.1 hmul).resolve_right hr0

end Reg
end Register
