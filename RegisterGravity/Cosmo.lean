import RegisterGravity.Galactic

/-!
# The cosmological scale: the ring (Sec. IV.D), and the pins (Sec. V)

`L` from the horizon, `GΛ`, the energy and density of the ring, its Misner–Sharp and Komar energies,
the push, the zero-gravity radius and why it lies below the crossing, the crossover `r = R_Λ v_c/c`,
`Λ = 432 a_M²/π²c⁴`, the ratio of the two pins, the drift of `G` that a Hubble-radius horizon would
give, and the equation-of-state bound.  `Λ` is the integration constant
of the solution of `Chain.lean`, fixed by the boundary condition `hdS` (`deSitter`); the inputs are
the named hypotheses (see `Chain.lean`).
-/

open Real

namespace Register
namespace Reg

variable (R : Reg)

/-- **Eq. (Lcos)**: Eq. (ident) read backwards, `L = 2πR_Λ/ℓ_c`. -/
theorem L_from_horizon : R.L = 2 * R.pi * R.RL / R.ℓc := by
  reg_facts R
  unfold RL; field_simp

/-- **Eq. (Lambda)**: with the boundary condition (`deSitter`, `Λ = 3/R_Λ²`) and Jacobson,
`GΛ = 12πc³/(ℏL² ln 2)`, and `Λ = 12π²/L²ℓ_c²`. -/
theorem G_Lambda (G Λ : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    G * Λ = 12 * R.pi * R.c ^ 3 / (R.ℏ * R.L ^ 2 * R.ln2) ∧
    Λ = 12 * R.pi ^ 2 / (R.L ^ 2 * R.ℓc ^ 2) := by
  reg_facts R
  rw [(R.deSitter G Λ).1 hdS, (R.G_eq G hJ).1]
  unfold RL
  constructor <;> (field_simp; ring)

/-- the energy of the ring: entropy times temperature, `E_Λ = (L²/4) ln 2 · (E_c/L)`, one Landauer
energy for each string -/
noncomputable def EΛ : ℝ := R.Shor * (R.Ec / R.L)
/-- the energy density of the ring spread over the interior, `ρ_Λ = E_Λ/(4πR_Λ³/3)` -/
noncomputable def ρΛ : ℝ := R.EΛ / (4 / 3 * R.pi * R.RL ^ 3)

/-- **Eq. (EL)**: `E_Λ = (LE_c/4) ln 2 = c⁴R_Λ/2G`. -/
theorem EΛ_eq (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.EΛ = R.L * R.Ec / 4 * R.ln2 ∧ R.EΛ = R.c ^ 4 * R.RL / (2 * G) := by
  reg_facts R
  rw [(R.G_eq G hJ).1]
  unfold EΛ Shor Rhor Ec RL
  constructor <;> (field_simp <;> ring)

/-- **The vacuum energy density**: `ρ_Λ = 3π²ρ_c ln 2/2L²`, and with the boundary condition it is
`Λc⁴/8πG`. -/
theorem ρΛ_eq (G Λ : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.ρΛ = 3 * R.pi ^ 2 * R.ρc * R.ln2 / (2 * R.L ^ 2) ∧
    R.ρΛ = Λ * R.c ^ 4 / (8 * R.pi * G) := by
  reg_facts R
  rw [(R.deSitter G Λ).1 hdS, (R.G_eq G hJ).1]
  unfold ρΛ EΛ Shor Rhor ρc Ec RL
  constructor <;> (field_simp; ring)

/-- **The 123 orders are `L²`** (Table I, Sec. IV.D): the Planck density `c⁷/ℏG²`, the quantum field
theory estimate of the vacuum energy density, is `π² ln²2 ρ_c` in the cell, and it exceeds the
ring's `ρ_Λ` by `(2 ln 2/3) L²`. -/
theorem vacuum_ratio (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.c ^ 7 / (R.ℏ * G ^ 2) = R.pi ^ 2 * R.ln2 ^ 2 * R.ρc ∧
    R.c ^ 7 / (R.ℏ * G ^ 2) / R.ρΛ = 2 * R.ln2 / 3 * R.L ^ 2 := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hρ : R.ρΛ = 3 * R.pi ^ 2 * R.ρc * R.ln2 / (2 * R.L ^ 2) := by
    unfold ρΛ EΛ Shor Rhor ρc Ec RL
    field_simp; ring
  have hP : R.c ^ 7 / (R.ℏ * G ^ 2) = R.pi ^ 2 * R.ln2 ^ 2 * R.ρc := by
    rw [hG]; unfold ρc Ec; field_simp
  refine ⟨hP, ?_⟩
  rw [hP, hρ]
  have : R.ρc ≠ 0 := by unfold ρc Ec; positivity
  field_simp

/-- the Misner–Sharp energy inside radius `r` of a static spherical solution, `c⁴r(1 − f)/2G`
(the classical definition) -/
noncomputable def EMS (G Λ r : ℝ) : ℝ := R.c ^ 4 * r * (1 - R.fSdS G 0 Λ r) / (2 * G)
/-- the Komar energy inside radius `r` of a static spherical solution, `c⁴r²f'/2G`
(the classical definition) -/
noncomputable def EK (G Λ r : ℝ) : ℝ := R.c ^ 4 * r ^ 2 * deriv (R.fSdS G 0 Λ) r / (2 * G)

/-- **The ring's energy is the Misner–Sharp energy; the energy that gravitates is its Komar energy,
`−2E_Λ`** (Sec. IV.D).  With the boundary condition, at the horizon the Misner–Sharp energy is
`E_Λ`, one Landauer energy per string, and the Komar energy, which counts the pressure three times,
`ρ + 3p = −2ρ_Λ`, is `−2E_Λ`: two Landauer energies per string as for a mass, but negative. -/
theorem komar_misner_sharp (G Λ : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.EMS G Λ R.RL = R.EΛ ∧ R.EK G Λ R.RL = -2 * R.EΛ := by
  reg_facts R
  have hRL := R.RL_pos
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hΛ := (R.deSitter G Λ).1 hdS
  have hE := (R.EΛ_eq G hJ).2
  constructor
  · rw [hE]
    unfold EMS
    rw [hdS, sub_zero, mul_one]
  · rw [hE]
    unfold EK
    rw [(R.hasDerivAt_fSdS G 0 Λ R.RL hRL.ne').deriv, hΛ]
    field_simp
    ring

/-- **The Komar energy of the mass** (Sec. III.C): the Komar energy `c⁴r²f′/2G` inside any sphere
about the mass, in the solution with the mass alone, is `Mc²`, the energy that gravitates, which
`Reg.newton` shows is two Landauer energies for each string of the sphere. -/
theorem komar_mass (G M r : ℝ) (hr : 0 < r) (hG : G ≠ 0) :
    R.c ^ 4 * r ^ 2 * deriv (R.fSdS G M 0) r / (2 * G) = M * R.c ^ 2 := by
  reg_facts R
  rw [(R.hasDerivAt_fSdS G M 0 r hr.ne').deriv]
  have hr' := hr.ne'
  field_simp
  ring

/-- **Eq. (push)**: with the boundary condition, the field of the solution about a mass is
`g = GM/r² − c²r/R_Λ²`, the pull of the mass less the push of the ring's content, and in cells
`a/a_c = α/(πn² ln 2) − 4π²n/L²`. -/
theorem push (G M Λ r : ℝ) (hr : 0 < r) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.gSdS G M Λ r = G * M / r ^ 2 - R.c ^ 2 * r / R.RL ^ 2 ∧
    R.gSdS G M Λ r / R.ac = R.α M / (R.pi * R.n r ^ 2 * R.ln2) - 4 * R.pi ^ 2 * R.n r / R.L ^ 2 := by
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

/-- **The zero-gravity radius** (Sec. IV.D): against the Newtonian pull the push would balance at
`r_z³ = GMR_Λ²/c²`, where each equals `c²r_z/R_Λ²`.  That is below the crossing value `c²/πR_Λ` of
`crossing` exactly when `r_z < R_Λ/π`, so for any smaller mass the pull that meets the push is the
deep one (`crossover`). -/
theorem zero_gravity (G M Λ rz : ℝ) (hrz : 0 < rz) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) (hz : R.gSdS G M Λ rz = 0) :
    rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2 ∧ G * M / rz ^ 2 = R.c ^ 2 * rz / R.RL ^ 2 ∧
    (R.c ^ 2 * rz / R.RL ^ 2 < R.c ^ 2 / (R.pi * R.RL) ↔ rz < R.RL / R.pi) := by
  reg_facts R
  have hrz' : rz ≠ 0 := hrz.ne'
  have hRL := R.RL_pos
  have hpull : G * M / rz ^ 2 = R.c ^ 2 * rz / R.RL ^ 2 := by
    rw [(R.push G M Λ rz hrz hJ hdS).1] at hz
    linarith
  have h3 : rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2 := by
    rw [eq_div_iff (by positivity)]
    field_simp at hpull
    linear_combination (-1 : ℝ) * hpull
  refine ⟨h3, hpull, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) (by positivity), lt_div_iff₀ R.pi_pos]
  constructor
  · intro h
    nlinarith [sq_nonneg R.RL, mul_pos (pow_pos R.c_pos 2) hRL]
  · intro h
    have hc2 : 0 < R.c ^ 2 * R.RL := by positivity
    nlinarith

/-- **Any galaxy, group or cluster** (Sec. IV.D): the zero-gravity radius `r_z³ = GMR_Λ²/c²` lies
below `R_Λ/π`, and so below the crossing (`zero_gravity`), exactly when `M < c²R_Λ/(π³G)`. -/
theorem zero_gravity_mass (G M rz : ℝ) (hG : 0 < G) (hrz : 0 < rz)
    (h3 : rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2) :
    rz < R.RL / R.pi ↔ M < R.c ^ 2 * R.RL / (R.pi ^ 3 * G) := by
  reg_facts R
  have hRL := R.RL_pos
  rw [← pow_lt_pow_iff_left₀ hrz.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0), h3, div_pow,
    div_lt_div_iff₀ (by positivity) (by positivity), lt_div_iff₀ (by positivity)]
  have e1 : G * M * R.RL ^ 2 * R.pi ^ 3 = R.RL ^ 2 * (M * (R.pi ^ 3 * G)) := by ring
  have e2 : R.RL ^ 3 * R.c ^ 2 = R.RL ^ 2 * (R.c ^ 2 * R.RL) := by ring
  rw [e1, e2]
  have hR2 : 0 < R.RL ^ 2 := by positivity
  constructor
  · intro h; exact lt_of_mul_lt_mul_left h hR2.le
  · intro h; exact mul_lt_mul_of_pos_left h hR2

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

/-- **The crossover in terms of the rotation speed** (Sec. IV.D): with `v_c⁴ = a_M GM`
(`tully_fisher`), the balance lies at `r = R_Λ v_c/c`, in cells `n = Lv_c/2πc`. -/
theorem crossover_speed (aM G M r vc : ℝ) (hr : 0 < r) (hvc : 0 < vc)
    (hTF : vc ^ 4 = aM * G * M) (h4 : r ^ 4 = R.RL ^ 4 * aM * G * M / R.c ^ 4) :
    r = R.RL * vc / R.c ∧ R.n r = R.L * vc / (2 * R.pi * R.c) := by
  reg_facts R
  have hRL := R.RL_pos
  have e : r ^ 4 = (R.RL * vc / R.c) ^ 4 := by
    rw [h4, div_pow, mul_pow, hTF]; ring
  have hr' : r = R.RL * vc / R.c := by
    have h0 : 0 ≤ R.RL * vc / R.c := by positivity
    exact (pow_left_inj₀ hr.le h0 (by norm_num : (4 : ℕ) ≠ 0)).1 e
  refine ⟨hr', ?_⟩
  rw [hr']
  unfold n RL
  field_simp

/-- **`Λ = 432 a_M²/π²c⁴`** (Sec. V), from Eq. (aM) and `Λ = 3/R_Λ²` alone. -/
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

/-- Newton's constant of Eq. (G) were the horizon of Eq. (ident) the Hubble radius `c/H`, with
`L` fixed: `G = 4πc³(c/H)²/(ℏL² ln 2)` -/
noncomputable def GHubble (H : ℝ) : ℝ :=
  4 * R.pi * R.c ^ 3 * (R.c / H) ^ 2 / (R.ℏ * R.L ^ 2 * R.ln2)

/-- **The drift of `G` with a Hubble-radius horizon** (Sec. IV.D).  With the scale factor `a`, the
Hubble rate `H = ȧ/a` and the deceleration parameter `q = −äa/ȧ²`, the `G` of `GHubble` changes at
`Ġ = 2H(1 + q)G`. -/
theorem G_drift (a adot : ℝ → ℝ) (addot t : ℝ) (ha : a t ≠ 0) (had : adot t ≠ 0)
    (hA : HasDerivAt a (adot t) t) (hAd : HasDerivAt adot addot t) :
    HasDerivAt (fun s => R.GHubble (adot s / a s))
      (2 * (adot t / a t) * (1 + -(addot * a t / adot t ^ 2)) * R.GHubble (adot t / a t)) t := by
  reg_facts R
  have e : (fun s => R.GHubble (adot s / a s))
      = fun s => 4 * R.pi * R.c ^ 5 / (R.ℏ * R.L ^ 2 * R.ln2) * (a s / adot s) ^ 2 := by
    funext s; unfold GHubble; rw [div_div_eq_mul_div]; ring
  rw [e]
  have h := ((hA.fun_div hAd had).fun_pow 2).const_mul
    (4 * R.pi * R.c ^ 5 / (R.ℏ * R.L ^ 2 * R.ln2))
  convert h using 1
  unfold GHubble
  norm_num
  field_simp
  ring

/-- **`Λ̇/Λ = −Ġ/G`** (Sec. VI, Appendix A): with `L` fixed, `GΛ = 12πc³/(ℏL² ln 2)` is a constant
(`G_Lambda`), so the rates of change of `G` and `Λ` are opposite, and the lunar-laser-ranging bound
on `|Ġ/G|` bounds `|Λ̇/Λ|` by the same number. -/
theorem constancy_of_Lambda (G Λ : ℝ → ℝ) (G' Λ' t K : ℝ) (hG : HasDerivAt G G' t)
    (hΛ : HasDerivAt Λ Λ' t) (hK : ∀ s, G s * Λ s = K) (hG0 : G t ≠ 0) (hΛ0 : Λ t ≠ 0) :
    Λ' / Λ t = -(G' / G t) := by
  have hc : HasDerivAt (fun s => G s * Λ s) (G' * Λ t + G t * Λ') t := hG.fun_mul hΛ
  have hconst : (fun s => G s * Λ s) = fun _ => K := funext hK
  rw [hconst] at hc
  have h0 := hc.unique (hasDerivAt_const t K)
  field_simp
  linear_combination h0

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

/-- **`w = −1` exactly** (Table I): the ring's energy density `ρ_Λ = 3π²ρ_c ln 2/2L²` is fixed by `L` and
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
