import RegisterGravity.Galactic

/-!
# The cosmological scale: the ring (Sec. IV.D), and the pins (Sec. V)

`L` from the horizon, `GΛ`, the energy and density of the ring, the push, the zero-velocity
radius, the crossover, `Λ = 432 a_M²/π²c⁴`, the ratio of the two pins, the drift of `G` that a
Hubble-radius horizon would give, and the equation-of-state bound.  `Λ` is the integration constant
of the solution of `Chain.lean`, fixed by the boundary condition `hdS` (`deSitter`); the inputs are
the named hypotheses (see `Chain.lean`).
-/

open Real

namespace Register
namespace Reg

variable (R : Reg)

/-- **Eq. (Lcos)**: the placement read backwards, `L = 2πR_Λ/ℓ_c`. -/
theorem L_from_horizon : R.L = 2 * R.pi * R.RL / R.ℓc := by
  reg_facts R
  unfold RL; field_simp

/-- **Eq. (Lambda)**: with the boundary condition (`deSitter`, `Λ = 3/R_Λ²`) and Jacobson,
`GΛ = 12πc³/ℏL²`, and `Λ = 12π²/L²ℓ_c²`. -/
theorem G_Lambda (G Λ : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    G * Λ = 12 * R.pi * R.c ^ 3 / (R.ℏ * R.L ^ 2) ∧ Λ = 12 * R.pi ^ 2 / (R.L ^ 2 * R.ℓc ^ 2) := by
  reg_facts R
  rw [(R.deSitter G Λ).1 hdS, (R.G_eq G hJ).1]
  unfold RL
  constructor <;> (field_simp; ring)

/-- the energy of the ring: entropy times temperature, `E_Λ = (L²/4)(E_c/L)` -/
noncomputable def EΛ : ℝ := R.Shor * (R.Ec / R.L)
/-- the energy density of the ring spread over the interior, `ρ_Λ = E_Λ/(4πR_Λ³/3)` -/
noncomputable def ρΛ : ℝ := R.EΛ / (4 / 3 * R.pi * R.RL ^ 3)

/-- **Eq. (EL)**: `E_Λ = LE_c/4 = c⁴R_Λ/2G`. -/
theorem EΛ_eq (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.EΛ = R.L * R.Ec / 4 ∧ R.EΛ = R.c ^ 4 * R.RL / (2 * G) := by
  reg_facts R
  rw [(R.G_eq G hJ).1]
  unfold EΛ Shor Rhor Ec RL
  constructor <;> (field_simp <;> ring)

/-- **The vacuum energy density**: `ρ_Λ = 3π²ρ_c/2L²`, and with the boundary condition it is
`Λc⁴/8πG`. -/
theorem ρΛ_eq (G Λ : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.ρΛ = 3 * R.pi ^ 2 * R.ρc / (2 * R.L ^ 2) ∧ R.ρΛ = Λ * R.c ^ 4 / (8 * R.pi * G) := by
  reg_facts R
  rw [(R.deSitter G Λ).1 hdS, (R.G_eq G hJ).1]
  unfold ρΛ EΛ Shor Rhor ρc Ec RL
  constructor <;> (field_simp; ring)

/-- **Eq. (push)**: with the boundary condition, the field of the solution about a mass is
`g = GM/r² − c²r/R_Λ²`, the pull of the mass less the push of the ring's content, and in cells
`a/a_c = α/πn² − 4π²n/L²`. -/
theorem push (G M Λ r : ℝ) (hr : 0 < r) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.gSdS G M Λ r = G * M / r ^ 2 - R.c ^ 2 * r / R.RL ^ 2 ∧
    R.gSdS G M Λ r / R.ac = R.α M / (R.pi * R.n r ^ 2) - 4 * R.pi ^ 2 * R.n r / R.L ^ 2 := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  have hRL := R.RL_pos.ne'
  have hg : R.gSdS G M Λ r = G * M / r ^ 2 - R.c ^ 2 * r / R.RL ^ 2 := by
    rw [R.gSdS_eq G M Λ r hr', (R.deSitter G Λ).1 hdS]
    field_simp
  refine ⟨hg, ?_⟩
  rw [hg, (R.G_eq G hJ).1]
  unfold ac α mc n RL
  field_simp; ring

/-- The Hubble rate is `2π` over the lap time: `H_∞ = c/R_Λ = 2π/Lt_c`. -/
theorem hubble : R.c / R.RL = 2 * R.pi / (R.L * R.tc) := by
  reg_facts R
  unfold RL tc; field_simp

/-- **The zero-velocity radius**: the field of the solution vanishes, the push balancing the pull,
where `r_z³ = GMR_Λ²/c²`, in cells `n_z³ = αL²/4π³`. -/
theorem zero_velocity (G M Λ rz : ℝ) (hrz : 0 < rz) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) (hz : R.gSdS G M Λ rz = 0) :
    rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2 ∧ R.n rz ^ 3 = R.α M * R.L ^ 2 / (4 * R.pi ^ 3) := by
  reg_facts R
  have hrz' : rz ≠ 0 := hrz.ne'
  have hRL := R.RL_pos.ne'
  have h3 : rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2 := by
    rw [(R.push G M Λ rz hrz hJ hdS).1] at hz
    rw [eq_div_iff (by positivity)]
    field_simp at hz
    linear_combination (-1 : ℝ) * hz
  refine ⟨h3, ?_⟩
  unfold n
  rw [div_pow, h3, (R.G_eq G hJ).1]
  unfold α mc RL
  field_simp; ring

/-- **The crossover**: the deep pull `√(a_M g_N)`, with `g_N` the field of the mass, balances the
push, the field of the ring's content alone, where `r⁴ = R_Λ⁴ a_M GM/c⁴`, that is
`r² = R_Λ²√(a_M GM)/c²`. -/
theorem crossover (aM G M Λ r : ℝ) (hr : 0 < r) (hdS : R.fSdS G 0 Λ R.RL = 0)
    (hbal : aM * R.gSdS G M 0 r = R.gSdS G 0 Λ r ^ 2) :
    r ^ 4 = R.RL ^ 4 * aM * G * M / R.c ^ 4 := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  have hRL := R.RL_pos.ne'
  have hpush : R.gSdS G 0 Λ r ^ 2 = R.c ^ 4 * r ^ 2 / R.RL ^ 4 := by
    rw [R.gSdS_eq G 0 Λ r hr', (R.deSitter G Λ).1 hdS]
    field_simp; ring
  rw [R.gSdS_mass G M r hr', hpush] at hbal
  have key : aM * G * M * R.RL ^ 4 = R.c ^ 4 * r ^ 4 := by
    have h2 := congrArg (fun x => x * (r ^ 2 * R.RL ^ 4)) hbal
    field_simp at h2
    linear_combination h2
  rw [eq_div_iff (by positivity)]
  linear_combination (-1 : ℝ) * key

/-- **`Λ = 432 a_M²/π²c⁴`** (Sec. V), from the boundary condition and Eq. (aM). -/
theorem Lambda_from_aM (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    Λ = 432 * R.aM 4 ^ 2 / (R.pi ^ 2 * R.c ^ 4) := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  rw [(R.deSitter G Λ).1 hdS, R.aM_values.1]
  field_simp; ring

/-- **The two pins** (Sec. V): `ℓ_c` cancels in `L_gal/L_cos = πc²/(12 a_0 R_Λ) = a_M/a_0`. -/
theorem pins_ratio (a0 : ℝ) (ha0 : 0 < a0) :
    (R.pi ^ 2 / 6 * R.c ^ 2 / (a0 * R.ℓc)) / (2 * R.pi * R.RL / R.ℓc)
      = R.pi * R.c ^ 2 / (12 * a0 * R.RL) ∧
    R.pi * R.c ^ 2 / (12 * a0 * R.RL) = R.aM 4 / a0 := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  constructor
  · field_simp; ring
  · rw [R.aM_values.1]; field_simp

/-- **Only the product `Lℓ_c` enters `a_M`**: `a_M = πc²/12R_Λ` with `R_Λ = Lℓ_c/2π`. -/
theorem aM_depends_on_product : R.aM 4 = R.pi ^ 2 * R.c ^ 2 / (6 * (R.L * R.ℓc)) := by
  reg_facts R
  rw [R.aM_values.2.1]; field_simp

/-- Newton's constant of Eq. (G) were the horizon of the placement the Hubble radius `c/H`, with
`L` fixed: `G = 4πc³(c/H)²/ℏL²` -/
noncomputable def GHubble (H : ℝ) : ℝ := 4 * R.pi * R.c ^ 3 * (R.c / H) ^ 2 / (R.ℏ * R.L ^ 2)

/-- **The drift of `G` with a Hubble-radius horizon** (Sec. IV.D).  With the scale factor `a`, the
Hubble rate `H = ȧ/a` and the deceleration parameter `q = −äa/ȧ²`, the `G` of `GHubble` changes at
`Ġ = 2H(1 + q)G`. -/
theorem G_drift (a adot : ℝ → ℝ) (addot t : ℝ) (ha : a t ≠ 0) (had : adot t ≠ 0)
    (hA : HasDerivAt a (adot t) t) (hAd : HasDerivAt adot addot t) :
    HasDerivAt (fun s => R.GHubble (adot s / a s))
      (2 * (adot t / a t) * (1 + -(addot * a t / adot t ^ 2)) * R.GHubble (adot t / a t)) t := by
  reg_facts R
  have e : (fun s => R.GHubble (adot s / a s))
      = fun s => 4 * R.pi * R.c ^ 5 / (R.ℏ * R.L ^ 2) * (a s / adot s) ^ 2 := by
    funext s; unfold GHubble; rw [div_div_eq_mul_div]; ring
  rw [e]
  have h := ((hA.fun_div hAd had).fun_pow 2).const_mul (4 * R.pi * R.c ^ 5 / (R.ℏ * R.L ^ 2))
  convert h using 1
  unfold GHubble
  norm_num
  field_simp
  ring

/-- **The fluid equation, from the first law.**  A comoving volume `V = a³` of a component of the
universe with energy density `ρ` and pressure `p = wρ` expands adiabatically, `d(ρV) = −p dV`; with
the Hubble rate `H = ȧ/a` this is `ρ̇ = −3H(1 + w)ρ`. -/
theorem fluid_equation (ρ a : ℝ → ℝ) (ρdot adot w t : ℝ) (ha : a t ≠ 0)
    (hρ : HasDerivAt ρ ρdot t) (hA : HasDerivAt a adot t)
    (first_law : HasDerivAt (fun s => ρ s * a s ^ 3)
      (-(w * ρ t) * deriv (fun s => a s ^ 3) t) t) :
    ρdot = -3 * (adot / a t) * (1 + w) * ρ t := by
  have hV : HasDerivAt (fun s => a s ^ 3) (3 * a t ^ 2 * adot) t := by
    convert hA.fun_pow 3 using 1
  have hE : HasDerivAt (fun s => ρ s * a s ^ 3) (ρdot * a t ^ 3 + ρ t * (3 * a t ^ 2 * adot)) t :=
    hρ.fun_mul hV
  have hu := hE.unique first_law
  rw [hV.deriv] at hu
  -- `a²(ρ̇a + 3ȧ(1 + w)ρ) = 0`, and `a ≠ 0`
  have h1 : a t ^ 2 * (ρdot * a t + 3 * adot * (1 + w) * ρ t) = 0 := by linear_combination hu
  have h2 : ρdot * a t + 3 * adot * (1 + w) * ρ t = 0 :=
    (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 ha)
  field_simp
  linear_combination h2

/-- **`w = −1` exactly** (Table I): the ring's energy density `ρ_Λ = 3π²ρ_c/2L²` is fixed by `L` and
the cell, so it does not change as the universe expands, and the first law gives `w = −1`. -/
theorem w_exact (a : ℝ → ℝ) (adot w t : ℝ) (ha : a t ≠ 0) (hH : adot / a t ≠ 0)
    (hA : HasDerivAt a adot t)
    (first_law : HasDerivAt (fun s => R.ρΛ * a s ^ 3)
      (-(w * R.ρΛ) * deriv (fun s => a s ^ 3) t) t) :
    w = -1 := by
  reg_facts R
  have hρ : 0 < R.ρΛ := by
    have := R.RL_pos
    unfold ρΛ EΛ Shor Rhor Ec
    positivity
  have h := fluid_equation (fun _ => R.ρΛ) a 0 adot w t ha (hasDerivAt_const t R.ρΛ) hA first_law
  have h0 : (adot / a t) * ((1 + w) * R.ρΛ) = 0 := by linear_combination (1 / 3 : ℝ) * h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hH
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · linarith
    · exact absurd h2 hρ.ne'

/-- **The equation-of-state bound** (Sec. VI, item 5): with the fluid equation, `|ρ̇/ρ| ≤ b`
gives `|1 + w| ≤ b/3H`. -/
theorem w_bound (ρ a : ℝ → ℝ) (ρdot adot w b t : ℝ) (ha : a t ≠ 0) (hρ0 : ρ t ≠ 0)
    (hH : 0 < adot / a t) (hρ : HasDerivAt ρ ρdot t) (hA : HasDerivAt a adot t)
    (first_law : HasDerivAt (fun s => ρ s * a s ^ 3)
      (-(w * ρ t) * deriv (fun s => a s ^ 3) t) t)
    (hb : |ρdot / ρ t| ≤ b) :
    |1 + w| ≤ b / (3 * (adot / a t)) := by
  have hw : ρdot / ρ t = -3 * (adot / a t) * (1 + w) := by
    rw [fluid_equation ρ a ρdot adot w t ha hρ hA first_law]
    field_simp
  rw [hw, abs_mul, abs_mul, abs_neg] at hb
  rw [abs_of_pos hH] at hb
  have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
  rw [h3] at hb
  rw [le_div_iff₀ (by positivity)]
  linarith

end Reg
end Register
