import RegisterGravity.Einstein
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The Schwarzschild–de Sitter solution, from the vacuum equations (Secs. III and IV.D)

About a spherical body at rest, alone, the solution is static and spherically symmetric: outside the
body its metric is `−e^{2α(r)}c²dt² + e^{2β(r)}dr² + r²dΩ²`, with `r` the areal radius, which grows
outward [R. M. Wald, *General Relativity* (1984), Sec. 6.1].  Its Ricci tensor is the textbook
formula `ricSS`, taken in the orthonormal frame of the observers at rest.  The vacuum equations
`R_ab = Λ g_ab`, which `Einstein.lean` derives where there is no matter, then reduce to two
ordinary differential equations, and `static_vacuum` solves them:

* the sum of the time and radial components gives `α′ + β′ = 0`, so `α + β` is one number;
* the angular component then gives `(r e^{−2β})′ = 1 − Λr²`, so `e^{−2β} = 1 − 2m/r − Λr²/3` for one
  number `m`.

With the unit of time chosen so that `α + β = 0` (Schwarzschild's time), `e^{2α} = e^{−2β}`, and the
metric function is `f(r) = 1 − 2m/r − Λr²/3`, the Schwarzschild–de Sitter solution [F. Kottler,
Ann. Phys. (Leipzig) **361**, 401 (1918)].  This is the static, spherically symmetric case of
Birkhoff's theorem with `Λ` [J. Schleich and D. M. Witt, J. Math. Phys. **51**, 112502 (2010),
Thm. 1, a reference of the files; the paper cites Kottler and Wald]: the
solution is not quoted but derived from the vacuum equations.  Far from the body, where `2m/r` is
small and `Λr²` negligible, the potential `c²(f − 1)/2` is `−c²m/r`, Newton's `−GM/r` for the body's
mass `M = c²m/G` (`Reg.fSdS`).
-/

open Real Set

namespace Register.Schwarzschild

/-- **The Ricci tensor of a static, spherically symmetric metric**,
`−e^{2α(r)}c²dt² + e^{2β(r)}dr² + r²dΩ²`, at the areal radius `r`, in the orthonormal frame
`(e^{−α}∂_{ct}, e^{−β}∂_r, r⁻¹∂_θ, (r sin θ)⁻¹∂_φ)` of the observers at rest:
`R_t̂t̂ = e^{−2β}(α″ + α′² − α′β′ + 2α′/r)`, `R_r̂r̂ = e^{−2β}(−α″ − α′² + α′β′ + 2β′/r)`, and
`R_θ̂θ̂ = R_φ̂φ̂ = (e^{−2β}(r(β′ − α′) − 1) + 1)/r²` [R. M. Wald, *General Relativity* (1984),
Sec. 6.1]. -/
noncomputable def ricSS (α β : ℝ → ℝ) (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![
    exp (-2 * β r) *
      (deriv (deriv α) r + deriv α r ^ 2 - deriv α r * deriv β r + 2 * deriv α r / r),
    exp (-2 * β r) *
      (-deriv (deriv α) r - deriv α r ^ 2 + deriv α r * deriv β r + 2 * deriv β r / r),
    (exp (-2 * β r) * (r * (deriv β r - deriv α r) - 1) + 1) / r ^ 2,
    (exp (-2 * β r) * (r * (deriv β r - deriv α r) - 1) + 1) / r ^ 2]

/-- **The static, spherically symmetric vacuum solution** (Secs. III and IV.D).  On an interval
`a < r < b` of areal radii, `a > 0`, where the vacuum equations `R_ab = Λ g_ab` hold, `α + β` is one
number `c₀` and `e^{−2β} = 1 − 2m/r − Λr²/3` for one number `m`.  The time and radial components
give `e^{−2β}·2(α′ + β′)/r = 0`, so `α′ + β′ = 0`; with it the angular component gives
`(r e^{−2β})′ = 1 − Λr²`, so `r e^{−2β} − r + Λr³/3` is one number, `−2m`. -/
theorem static_vacuum {α β : ℝ → ℝ} {Λ a b : ℝ} (ha : 0 < a)
    (hα : ∀ r ∈ Ioo a b, DifferentiableAt ℝ α r) (hβ : ∀ r ∈ Ioo a b, DifferentiableAt ℝ β r)
    (hvac : ∀ r ∈ Ioo a b, ricSS α β r = Λ • Einstein.eta) :
    ∃ m c₀ : ℝ, ∀ r ∈ Ioo a b,
      α r + β r = c₀ ∧ exp (-2 * β r) = 1 - 2 * m / r - Λ * r ^ 2 / 3 := by
  -- the three components of the vacuum equations at a radius
  have comp : ∀ r ∈ Ioo a b,
      exp (-2 * β r) * (deriv (deriv α) r + deriv α r ^ 2 - deriv α r * deriv β r +
        2 * deriv α r / r) = -Λ ∧
      exp (-2 * β r) * (-deriv (deriv α) r - deriv α r ^ 2 + deriv α r * deriv β r +
        2 * deriv β r / r) = Λ ∧
      (exp (-2 * β r) * (r * (deriv β r - deriv α r) - 1) + 1) / r ^ 2 = Λ := by
    intro r hr
    have h := hvac r hr
    have e0 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 0) h
    have e1 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 1) h
    have e2 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 2) h
    simp [ricSS, Einstein.eta, Matrix.diagonal, -neg_mul] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  -- `α′ + β′ = 0`
  have hsum : ∀ r ∈ Ioo a b, deriv α r + deriv β r = 0 := by
    intro r hr
    obtain ⟨e0, e1, -⟩ := comp r hr
    have hr0 : 0 < r := ha.trans hr.1
    have hE : 0 < exp (-2 * β r) := exp_pos _
    have h2 : exp (-2 * β r) * (2 * (deriv α r + deriv β r) / r) = 0 := by
      have : exp (-2 * β r) * (2 * (deriv α r + deriv β r) / r) =
          exp (-2 * β r) * (deriv (deriv α) r + deriv α r ^ 2 - deriv α r * deriv β r +
            2 * deriv α r / r) +
          exp (-2 * β r) * (-deriv (deriv α) r - deriv α r ^ 2 + deriv α r * deriv β r +
            2 * deriv β r / r) := by ring
      rw [this, e0, e1]; ring
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hE.ne'
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · linarith
      · exact absurd h hr0.ne'
  -- `α + β` is one number on the interval
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, ∀ r ∈ Ioo a b, α r + β r = c₀ := by
    refine isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun r hr => ((hα r hr).add (hβ r hr)).differentiableWithinAt) fun r hr => ?_
    show deriv (α + β) r = 0
    rw [((hα r hr).hasDerivAt.add (hβ r hr).hasDerivAt).deriv]
    exact hsum r hr
  -- `(r e^{−2β})′ = 1 − Λr²`
  have hE' : ∀ r ∈ Ioo a b, HasDerivAt (fun r => exp (-2 * β r))
      (exp (-2 * β r) * (-2 * deriv β r)) r := fun r hr =>
    ((hβ r hr).hasDerivAt.const_mul (-2)).exp
  have hF : ∀ r ∈ Ioo a b, HasDerivAt (fun r => r * exp (-2 * β r) - r + Λ * r ^ 3 / 3)
      (1 * exp (-2 * β r) + r * (exp (-2 * β r) * (-2 * deriv β r)) - 1 +
        Λ * (3 * r ^ 2) / 3) r := by
    intro r hr
    have h3 := (((hasDerivAt_id' r).mul (hE' r hr)).sub (hasDerivAt_id' r)).add
      (((hasDerivAt_pow 3 r).const_mul Λ).div_const 3)
    refine h3.congr_deriv ?_
    norm_num
  have hF0 : ∀ r ∈ Ioo a b, 1 * exp (-2 * β r) + r * (exp (-2 * β r) * (-2 * deriv β r)) - 1 +
      Λ * (3 * r ^ 2) / 3 = 0 := by
    intro r hr
    obtain ⟨-, -, e2⟩ := comp r hr
    have hr0 : 0 < r := ha.trans hr.1
    have hab : deriv α r = -deriv β r := by linarith [hsum r hr]
    rw [hab] at e2
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0.ne'
    rw [div_eq_iff hr2] at e2
    nlinarith [e2]
  obtain ⟨C, hC⟩ : ∃ C, ∀ r ∈ Ioo a b, r * exp (-2 * β r) - r + Λ * r ^ 3 / 3 = C := by
    refine isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun r hr => (hF r hr).differentiableAt.differentiableWithinAt) fun r hr => ?_
    show deriv (fun r => r * exp (-2 * β r) - r + Λ * r ^ 3 / 3) r = 0
    rw [(hF r hr).deriv]
    exact hF0 r hr
  refine ⟨-C / 2, c₀, fun r hr => ⟨hc₀ r hr, ?_⟩⟩
  have hr0 : 0 < r := ha.trans hr.1
  have e := hC r hr
  have hE : exp (-2 * β r) = (C + r - Λ * r ^ 3 / 3) / r := by
    rw [eq_div_iff hr0.ne']
    linarith [e]
  rw [hE]
  field_simp
  ring

/-- **The time part** of the static vacuum solution: `e^{2α} = e^{2c₀}·e^{−2β}`, since
`α + β = c₀`; with Schwarzschild's time, `c₀ = 0`, the two metric functions are one function. -/
theorem time_part {α β : ℝ → ℝ} {c₀ r : ℝ} (h : α r + β r = c₀) :
    exp (2 * α r) = exp (2 * c₀) * exp (-2 * β r) := by
  rw [← exp_add]
  congr 1
  linarith

end Register.Schwarzschild
