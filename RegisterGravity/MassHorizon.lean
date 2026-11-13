import RegisterGravity.DeSitter
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The constant `Λ` with a mass at rest (Sec. IV.D)

Sec. IV.D fixes the constant of Einstein's equations, `Λ = 3/R_Λ²`, in the solution without a mass
(`Space.lean`, `Main.deSitter_horizon`).  About a body of mass `M` at rest, alone, the solution is
Schwarzschild–de Sitter, `f(r) = 1 − 2GM/c²r − Λr²/3`, with `Λ` the constant of its own Einstein
equations (`Main.schwarzschild_deSitter`).  This file shows that it is the same number, from the
thermodynamics that Sec. III takes: a horizon is thermal at the temperature of its period, and the
energy that crosses it is heat, `δQ = T dS`.

Take a family of such solutions, `s ↦ (M s, Λ s)`, in which the body's mass grows.
The observer's cosmological horizon lies at `r s`, a zero of `f` where the field `g = (c²/2) f′`
points outward, `g < 0`; its surface gravity is `−g`, so its temperature is
`k_BT = ℏ(−g)/(2πc)` (`T_Unruh`), and its entropy is `η₀·4πr²`, the entropy density of every horizon
times its area, whatever its value.
As the mass grows by `dM`, the energy `dMc²` crosses the horizon into the observer's region, and
the Clausius relation reads `d(Mc²) = −T dS`.  With Jacobson's `G = c³k_B/(4ℏη₀)` for the same
density this is
`dm = (r/2) f′(r) dr` for `m = GM/c²` (`clausius_geometric`).  Differentiating the horizon condition
`1 − 2m/r − Λr²/3 = 0` gives `dm = (r/2) f′(r) dr − (r³/6) dΛ` (`deriv_lambda_zero`), so `dΛ = 0`:
the constant does not change as the mass grows (`lambda_with_mass`), and where the family starts
with the constant of the solution without a mass, `Λ 0 = 3/R_Λ²` (`hdS`), it keeps it
(`lambda_with_mass_deSitter`).  The field about
the body is then `GM/r² − c²r/R_Λ²` (`push`), and its cosmological horizon is drawn in by `GM/c²`
(`sds_outer_horizon`).

With `Λ` free, the same horizon condition gives `d(Mc²) = −T dS + V dP`, with the volume
`V = 4πr³/3` and the pressure `P = −Λc⁴/8πG` (`first_law_extended`), the first law of the
cosmological horizon of Dolan, Kastor, Kubizňák, Mann and Traschen.  So the Clausius relation, which
takes all the energy that crosses as heat, holds exactly when the work `V dP` is zero, that is when
`dΛ = 0` (`clausius_iff`): that no part of the energy is work is the input that keeps `Λ`.
-/

open Real Set Filter Topology

namespace Register
namespace Reg

variable (R : Reg)

/-- **The horizon condition along a family** (geometric form).  Along a family `t ↦ (m t, Λ t)` of
metric functions `f = 1 − 2m/r − Λr²/3` whose zero `r t > 0` stays a zero near `s`, the relation
`m′ = (r/2) f′(r) r′`, with `f′(r) = 2m/r² − 2Λr/3`, makes `Λ′ = 0`: the derivative of the horizon
condition is `−2m′/r + f′(r) r′ − Λ′r²/3 = 0`. -/
theorem deriv_lambda_zero {m Λ r : ℝ → ℝ} {s : ℝ}
    (hm : DifferentiableAt ℝ m s) (hΛ : DifferentiableAt ℝ Λ s) (hr : DifferentiableAt ℝ r s)
    (hpos : 0 < r s)
    (hhor : ∀ᶠ t in 𝓝 s, 1 - 2 * m t / r t - Λ t * r t ^ 2 / 3 = 0)
    (hcl : deriv m s = r s / 2 * (2 * m s / r s ^ 2 - 2 * Λ s * r s / 3) * deriv r s) :
    deriv Λ s = 0 := by
  have hr0 : r s ≠ 0 := hpos.ne'
  -- the derivative of the horizon condition
  have hF : HasDerivAt (fun t => 1 - 2 * m t / r t - Λ t * r t ^ 2 / 3)
      (-(2 * deriv m s * r s - 2 * m s * deriv r s) / r s ^ 2 -
        (deriv Λ s * r s ^ 2 + Λ s * (2 * r s * deriv r s)) / 3) s := by
    have h1 := (hm.hasDerivAt.const_mul 2).div hr.hasDerivAt hr0
    have h2 := (hΛ.hasDerivAt.mul (hr.hasDerivAt.pow 2)).div_const 3
    have h3 := ((hasDerivAt_const s (1 : ℝ)).sub h1).sub h2
    refine h3.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.cast_ofNat]
    ring
  -- the condition holds near `s`, so its derivative there is zero
  have hzero : deriv (fun t => 1 - 2 * m t / r t - Λ t * r t ^ 2 / 3) s = 0 := by
    have hev : (fun t => 1 - 2 * m t / r t - Λ t * r t ^ 2 / 3) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := hhor
    rw [hev.deriv_eq]; simp
  rw [hF.deriv, hcl] at hzero
  have hr2 : r s ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  field_simp at hzero
  have h4 : deriv Λ s * r s ^ 4 = 0 := by nlinarith [hzero]
  rcases mul_eq_zero.1 h4 with h | h
  · exact h
  · exact absurd h (pow_ne_zero 4 hr0)

/-- **The Clausius relation on the cosmological horizon, in the solution's terms.**  With the
horizon's temperature from its period, `k_BT = ℏa/(2πc)` for its surface gravity `a = −g(r)`
(`horizon_thermal`, `T_Unruh`), its entropy `η₀·4πr²` for an entropy density `η₀ > 0`, and
`G = c³k_B/(4ℏη₀)`, the relation
`d(Mc²) = −T dS` is `m′ = (r/2) f′(r) r′` for `m = GM/c²`. -/
theorem clausius_geometric (G η₀ : ℝ) {M Λ r T : ℝ → ℝ} {s : ℝ} (hη : 0 < η₀)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * η₀))
    (hM : DifferentiableAt ℝ M s) (hr : DifferentiableAt ℝ r s) (hpos : 0 < r s)
    (hg : R.gSdS G (M s) (Λ s) (r s) < 0)
    (I1 : R.kB * T s = R.ℏ / (R.La (-R.gSdS G (M s) (Λ s) (r s)) * R.tc))
    (hcl : deriv (fun t => M t * R.c ^ 2) s =
      -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s) :
    deriv (fun t => G * M t / R.c ^ 2) s =
      r s / 2 * (2 * (G * M s / R.c ^ 2) / r s ^ 2 - 2 * Λ s * r s / 3) * deriv r s := by
  reg_facts R
  have hr0 : r s ≠ 0 := hpos.ne'
  -- the temperature from the period of the horizon
  have hT := R.T_Unruh _ (T s) (neg_pos.2 hg) I1
  rw [R.gSdS_eq G (M s) (Λ s) (r s) hr0] at hT
  -- the two derivatives of the Clausius relation
  have hE : deriv (fun t => M t * R.c ^ 2) s = deriv M s * R.c ^ 2 :=
    (hM.hasDerivAt.mul_const (R.c ^ 2)).deriv
  have hS : deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s =
      η₀ * (4 * R.pi * (2 * r s * deriv r s)) := by
    have h := ((hr.hasDerivAt.pow 2).const_mul (4 * R.pi)).const_mul η₀
    refine (h.congr_deriv ?_).deriv
    simp only [Nat.cast_ofNat]
    ring
  have hm : deriv (fun t => G * M t / R.c ^ 2) s = G * deriv M s / R.c ^ 2 :=
    ((hM.hasDerivAt.const_mul G).div_const (R.c ^ 2)).deriv
  rw [hE, hS] at hcl
  rw [hm]
  -- `G` from Jacobson's step: `ℏη/k_B = c³/(4G)`
  have hG : G * (4 * R.ℏ * η₀) = R.c ^ 3 * R.kB := by
    rw [hJ]; field_simp
  -- solve the temperature for `T` and substitute
  have hTs : T s = R.ℏ * -(G * M s / r s ^ 2 - Λ s * R.c ^ 2 * r s / 3) /
      (2 * R.pi * R.c) / R.kB := by
    rw [eq_div_iff R.kB_pos.ne']; linarith [hT]
  rw [hTs] at hcl
  have hc4 : (R.c ^ 2) ≠ 0 := by positivity
  field_simp
  field_simp at hcl
  have hck : R.c ^ 3 * R.kB ≠ 0 := by positivity
  refine mul_right_cancel₀ hck ?_
  calc G * deriv M s * r s * 3 * (R.c ^ 3 * R.kB)
      = G * (deriv M s * R.c ^ 3 * r s * 3 * R.kB) := by ring
    _ = G * (R.ℏ * (G * M s * 3 - R.c ^ 2 * r s ^ 3 * Λ s) * η₀ * 4 * deriv r s) := by rw [hcl]
    _ = G * (4 * R.ℏ * η₀) * ((G * M s * 3 - R.c ^ 2 * r s ^ 3 * Λ s) * deriv r s) := by ring
    _ = (G * M s * 3 - R.c ^ 2 * r s ^ 3 * Λ s) * deriv r s * (R.c ^ 3 * R.kB) := by
      rw [hG]; ring

/-- **The first law of the cosmological horizon with `Λ` free**, derived: along the family, the
horizon condition, with the horizon's temperature from its period, its entropy `η₀·4πr²` and
`G = c³k_B/(4ℏη₀)`, gives `d(Mc²) = −T dS + V dP`, with the volume `V = 4πr³/3` and the pressure
`P = −Λc⁴/(8πG)` [B. P. Dolan, D. Kastor, D. Kubizňák, R. B. Mann and J. Traschen, Phys. Rev. D
**87**, 104017 (2013), Eq. (2.25)].  The term `V dP` is the work done on the horizon as `Λ`
changes. -/
theorem first_law_extended (G η₀ : ℝ) {M Λ r T : ℝ → ℝ} {s : ℝ} (hη : 0 < η₀)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * η₀))
    (hM : DifferentiableAt ℝ M s) (hΛ : DifferentiableAt ℝ Λ s) (hr : DifferentiableAt ℝ r s)
    (hpos : 0 < r s) (hg : R.gSdS G (M s) (Λ s) (r s) < 0)
    (hhor : ∀ᶠ t in 𝓝 s, R.fSdS G (M t) (Λ t) (r t) = 0)
    (I1 : R.kB * T s = R.ℏ / (R.La (-R.gSdS G (M s) (Λ s) (r s)) * R.tc)) :
    deriv (fun t => M t * R.c ^ 2) s =
      -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s
        + 4 * R.pi * r s ^ 3 / 3 * deriv (fun t => -(Λ t) * R.c ^ 4 / (8 * R.pi * G)) s := by
  reg_facts R
  have hr0 : r s ≠ 0 := hpos.ne'
  have hGpos : 0 < G := by rw [hJ]; positivity
  have hG0 : G ≠ 0 := hGpos.ne'
  -- the temperature from the period of the horizon
  have hT := R.T_Unruh _ (T s) (neg_pos.2 hg) I1
  rw [R.gSdS_eq G (M s) (Λ s) (r s) hr0] at hT
  -- the derivatives
  have hE : deriv (fun t => M t * R.c ^ 2) s = deriv M s * R.c ^ 2 :=
    (hM.hasDerivAt.mul_const (R.c ^ 2)).deriv
  have hS : deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s =
      η₀ * (4 * R.pi * (2 * r s * deriv r s)) := by
    have h := ((hr.hasDerivAt.pow 2).const_mul (4 * R.pi)).const_mul η₀
    refine (h.congr_deriv ?_).deriv
    simp only [Nat.cast_ofNat]
    ring
  have hP : deriv (fun t => -(Λ t) * R.c ^ 4 / (8 * R.pi * G)) s =
      -(deriv Λ s) * R.c ^ 4 / (8 * R.pi * G) :=
    ((hΛ.hasDerivAt.neg.mul_const (R.c ^ 4)).div_const (8 * R.pi * G)).deriv
  -- the horizon condition holds near `s`, so its derivative there is zero
  have hF : HasDerivAt (fun t => R.fSdS G (M t) (Λ t) (r t))
      (-(2 * G * (deriv M s * r s - M s * deriv r s)) / (R.c ^ 2 * r s ^ 2) -
        (deriv Λ s * r s ^ 2 + Λ s * (2 * r s * deriv r s)) / 3) s := by
    have h1 := ((hM.hasDerivAt.const_mul (2 * G)).div (hr.hasDerivAt.const_mul (R.c ^ 2))
      (mul_ne_zero (by positivity) hr0))
    have h2 := (hΛ.hasDerivAt.mul (hr.hasDerivAt.pow 2)).div_const 3
    have h3 := ((hasDerivAt_const s (1 : ℝ)).sub h1).sub h2
    have heq : (fun t => R.fSdS G (M t) (Λ t) (r t))
        = fun t => 1 - 2 * G * M t / (R.c ^ 2 * r t) - Λ t * r t ^ 2 / 3 := by
      funext t; unfold fSdS; ring
    rw [heq]
    refine h3.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    ring
  have hzero : deriv (fun t => R.fSdS G (M t) (Λ t) (r t)) s = 0 := by
    have hev : (fun t => R.fSdS G (M t) (Λ t) (r t)) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := hhor
    rw [hev.deriv_eq]; simp
  rw [hF.deriv] at hzero
  -- `G` from Jacobson's step: `4ℏη₀ = c³k_B/G`
  have hη0 : η₀ = R.c ^ 3 * R.kB / (4 * R.ℏ * G) := by
    rw [hJ]; field_simp
  have hTs : T s = R.ℏ * -(G * M s / r s ^ 2 - Λ s * R.c ^ 2 * r s / 3) /
      (2 * R.pi * R.c) / R.kB := by
    rw [eq_div_iff R.kB_pos.ne']; linarith [hT]
  -- solve the horizon condition's derivative for `M′`
  have hM' : deriv M s = M s * deriv r s / r s
      - R.c ^ 2 * r s * (deriv Λ s * r s ^ 2 + 2 * Λ s * r s * deriv r s) / (6 * G) := by
    field_simp at hzero
    field_simp
    linear_combination (-1 : ℝ) * hzero
  rw [hE, hS, hP, hTs, hη0, hM']
  field_simp
  ring

/-- **The Clausius relation on the cosmological horizon holds exactly when `Λ` does not change**:
by `first_law_extended`, `d(Mc²) = −T dS` holds exactly when the work `V dP` is zero, and `V > 0`,
so exactly when `dΛ = 0`.  The relation takes all the energy that crosses the horizon as heat
(`Sources.Thermo.horizon_clausius`, Sec. III's `δQ = T dS`); that no part of it is work is what
keeps `Λ` (`lambda_with_mass`). -/
theorem clausius_iff (G η₀ : ℝ) {M Λ r T : ℝ → ℝ} {s : ℝ} (hη : 0 < η₀)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * η₀))
    (hM : DifferentiableAt ℝ M s) (hΛ : DifferentiableAt ℝ Λ s) (hr : DifferentiableAt ℝ r s)
    (hpos : 0 < r s) (hg : R.gSdS G (M s) (Λ s) (r s) < 0)
    (hhor : ∀ᶠ t in 𝓝 s, R.fSdS G (M t) (Λ t) (r t) = 0)
    (I1 : R.kB * T s = R.ℏ / (R.La (-R.gSdS G (M s) (Λ s) (r s)) * R.tc)) :
    deriv (fun t => M t * R.c ^ 2) s = -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s ↔
      deriv Λ s = 0 := by
  reg_facts R
  have hGpos : 0 < G := by rw [hJ]; positivity
  have hP : deriv (fun t => -(Λ t) * R.c ^ 4 / (8 * R.pi * G)) s =
      -(deriv Λ s) * R.c ^ 4 / (8 * R.pi * G) :=
    ((hΛ.hasDerivAt.neg.mul_const (R.c ^ 4)).div_const (8 * R.pi * G)).deriv
  rw [R.first_law_extended G η₀ hη hJ hM hΛ hr hpos hg hhor I1, hP]
  have hV : 0 < 4 * R.pi * r s ^ 3 / 3 := by positivity
  constructor
  · intro h
    have h' : 4 * R.pi * r s ^ 3 / 3 * (-(deriv Λ s) * R.c ^ 4 / (8 * R.pi * G)) = 0 := by
      linarith
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact absurd h1 hV.ne'
    · have : -(deriv Λ s) * R.c ^ 4 = 0 := by
        rcases div_eq_zero_iff.1 h1 with h2 | h2
        · exact h2
        · exact absurd h2 (by positivity)
      rcases mul_eq_zero.1 this with h2 | h2
      · linarith
      · exact absurd h2 (by positivity)
  · intro h
    rw [h]; ring

/-- **A mass at rest leaves `Λ` unchanged** (Sec. IV.D).  Along a family of solutions about a
body at rest, `f = 1 − 2GM/c²r − Λr²/3` with the mass `M s` and the constant `Λ s`, continuous in
`s` on `[0, s₁]`, with the observer's cosmological horizon at `r s` (a zero of `f` where the field
points outward), thermal at the temperature of its period, and the Clausius relation
`d(Mc²) = −T dS` for its entropy `η₀·4πr²` as the mass grows, with `G = c³k_B/(4ℏη₀)` for the same
density `η₀ > 0`, whatever its value, `Λ s = Λ 0` for every `s`. -/
theorem lambda_with_mass (G η₀ : ℝ) (M Λ r T : ℝ → ℝ) (s₁ : ℝ) (hη : 0 < η₀)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * η₀)) (hcont : ContinuousOn Λ (Icc 0 s₁))
    (hdiff : ∀ s ∈ Ioo 0 s₁,
      DifferentiableAt ℝ M s ∧ DifferentiableAt ℝ Λ s ∧ DifferentiableAt ℝ r s)
    (hhor : ∀ s ∈ Ioo 0 s₁, 0 < r s ∧ R.fSdS G (M s) (Λ s) (r s) = 0 ∧
      R.gSdS G (M s) (Λ s) (r s) < 0)
    (I1 : ∀ s ∈ Ioo 0 s₁, R.kB * T s = R.ℏ / (R.La (-R.gSdS G (M s) (Λ s) (r s)) * R.tc))
    (hcl : ∀ s ∈ Ioo 0 s₁, deriv (fun t => M t * R.c ^ 2) s =
      -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s) :
    ∀ s ∈ Icc 0 s₁, Λ s = Λ 0 := by
  reg_facts R
  -- `Λ′ = 0` at every `s` of the open interval
  have hd : ∀ s ∈ Ioo 0 s₁, deriv Λ s = 0 := by
    intro s hs
    obtain ⟨hM, hΛ, hr⟩ := hdiff s hs
    obtain ⟨hpos, -, hg⟩ := hhor s hs
    refine deriv_lambda_zero (m := fun t => G * M t / R.c ^ 2)
      ((hM.const_mul G).div_const _) hΛ hr hpos ?_
      (R.clausius_geometric G η₀ hη hJ hM hr hpos hg (I1 s hs) (hcl s hs))
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    obtain ⟨htpos, hf, -⟩ := hhor t ht
    have : R.fSdS G (M t) (Λ t) (r t) = 1 - 2 * (G * M t / R.c ^ 2) / r t - Λ t * r t ^ 2 / 3 := by
      unfold fSdS; field_simp
    rw [← this]; exact hf
  -- the mean value theorem on `[0, s]`
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0]
  · obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope Λ h0
      (hcont.mono (Icc_subset_Icc le_rfl hs.2))
      (fun t ht => (hdiff t ⟨ht.1, ht.2.trans_le hs.2⟩).2.1.differentiableWithinAt)
    rw [hd c ⟨hc.1, hc.2.trans_le hs.2⟩, eq_comm, div_eq_zero_iff] at hdc
    rcases hdc with h | h
    · linarith
    · linarith

/-- **With a mass at rest, `Λ = 3/R_Λ²`, and the field about the body is `GM/r² − c²r/R_Λ²`**.  The
family starts with the constant of the solution without a mass, which the rings fix (`hdS`,
`Main.deSitter_horizon`; the theorem takes the constant at `s = 0`, not a mass `M 0 = 0`); by
`lambda_with_mass` every solution of the family has that constant, so its field is the pull of the
mass less the push of the ring's content (`push`). -/
theorem lambda_with_mass_deSitter (G η₀ : ℝ) (M Λ r T : ℝ → ℝ) (s₁ : ℝ) (hη : 0 < η₀)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * η₀)) (hdS : R.fSdS G 0 (Λ 0) R.RL = 0)
    (hcont : ContinuousOn Λ (Icc 0 s₁))
    (hdiff : ∀ s ∈ Ioo 0 s₁,
      DifferentiableAt ℝ M s ∧ DifferentiableAt ℝ Λ s ∧ DifferentiableAt ℝ r s)
    (hhor : ∀ s ∈ Ioo 0 s₁, 0 < r s ∧ R.fSdS G (M s) (Λ s) (r s) = 0 ∧
      R.gSdS G (M s) (Λ s) (r s) < 0)
    (I1 : ∀ s ∈ Ioo 0 s₁, R.kB * T s = R.ℏ / (R.La (-R.gSdS G (M s) (Λ s) (r s)) * R.tc))
    (hcl : ∀ s ∈ Ioo 0 s₁, deriv (fun t => M t * R.c ^ 2) s =
      -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s) :
    ∀ s ∈ Icc 0 s₁, R.fSdS G 0 (Λ s) R.RL = 0 ∧
      ∀ x, 0 < x → R.gSdS G (M s) (Λ s) x = G * M s / x ^ 2 - R.c ^ 2 * x / R.RL ^ 2 := by
  intro s hs
  have hΛ := R.lambda_with_mass G η₀ M Λ r T s₁ hη hJ hcont hdiff hhor I1 hcl s hs
  have hdS' : R.fSdS G 0 (Λ s) R.RL = 0 := by rw [hΛ]; exact hdS
  refine ⟨hdS', fun x hx => ?_⟩
  reg_facts R
  have hRL := R.RL_pos.ne'
  rw [R.gSdS_eq G (M s) (Λ s) x hx.ne', (R.deSitter G (Λ s)).1 hdS']
  field_simp

end Reg
end Register
