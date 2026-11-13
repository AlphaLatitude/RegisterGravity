import RegisterGravity.Galactic
import RegisterGravity.Carriers
import RegisterGravity.Bridge
import RegisterGravity.Qubit

/-!
# The cosmological scale: the ring (Sec. IV.D), the pins (Sec. V), the equation of state (Sec. VI)

`L` from the horizon, `GΛ`, the energy and density of the ring, the energy of a string and its
split into heat and matter, with the vacuum's share (Sec. IV.E), the ring's Misner–Sharp and Komar
energies, the push, the zero-gravity radius and why it lies in the deep regime, the drift of `G`
that a Hubble-radius horizon would give, and the equation-of-state bound.  `Λ` is the integration
constant of the solution of `Chain.lean`, fixed by the boundary condition `hdS` (`deSitter`); the
inputs are the named hypotheses (see `Chain.lean`).
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

/-- **A black hole's horizon by the area law** (Sec. IV.D, on the circles at the horizons): its
great circles have `L' = 4πGM/c²ℓ_c` cells, and `(L'²/4) ln 2 = πr_s²/ℓ_P² = A/4ℓ_P²` with
`r_s = 2GM/c²` and `A = 4πr_s²`, the quarter per Planck area again, by Eq. (cell) alone. -/
theorem black_hole_quarter (G M : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    (4 * R.pi * G * M / (R.c ^ 2 * R.ℓc)) ^ 2 / 4 * R.ln2
      = R.pi * (2 * G * M / R.c ^ 2) ^ 2 / R.ℓP G ^ 2 ∧
    R.pi * (2 * G * M / R.c ^ 2) ^ 2 / R.ℓP G ^ 2
      = 4 * R.pi * (2 * G * M / R.c ^ 2) ^ 2 / (4 * R.ℓP G ^ 2) := by
  reg_facts R
  have hℓP : R.ℓP G ^ 2 = R.ℓc ^ 2 / (R.pi * R.ln2) := by
    have h := (R.cell_from_G G hJ).2
    have hs : Real.sqrt (R.pi * R.ln2) ^ 2 = R.pi * R.ln2 := Real.sq_sqrt (by positivity)
    have : R.ℓc ^ 2 = R.pi * R.ln2 * R.ℓP G ^ 2 := by rw [h, mul_pow, hs]
    rw [this]; field_simp
  constructor
  · rw [hℓP]; field_simp; ring
  · field_simp

/-- **The vacuum's energy** (Sec. IV.D): the heat of the horizon, its entropy times its
temperature, `E_Λ = (L²/4) ln 2 · (E_c/L)`, one Landauer energy for each string.  The entropy is
that of the horizon's thermal state, a state of the strings alone (the thesis, applied in
`Bridge.horizonEntropy`), so the vacuum's energy is fixed by that state and the horizon's
temperature (`I1`); `vacuum_energy` derives it from the two, to relative order `2/L`. -/
noncomputable def EΛ : ℝ := R.Shor * (R.Ec / R.L)

/-- **The vacuum's energy from the strings** (Sec. IV.D): the horizon's temperature, `k_BT = E_c/L`
(`I1`, `T_dS`), times the entropy of its thermal state, a state of the strings alone with one bit
per string (`Bridge.horizon_entropy`), is `E_Λ` to relative order `2/L`.  The entropy does not
depend on the inverse temperature `β` of the state, since the two senses of a string have one
energy (`hsense` of `Qubit.Tick`), so no relation between `β` and `T` is taken.  Nothing below
rests on this theorem; it shows what `E_Λ` rests on. -/
theorem vacuum_energy {L : ℕ} (H : Horizon L) (hL : 4 ≤ L) (hRL : R.L = L)
    (T : ℝ) (I1 : R.kB * T = R.ℏ / (R.L * R.tc))
    [NeZero L] (Tk : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ)
    (P : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) (hfree : P = Entropy.jointProb q)
    (hq : ∀ l, q l = Qubit.prob ((Tk l).state β En) 0) :
    R.kB * T * Bridge.horizonEntropy H P = R.EΛ * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  obtain ⟨h1, h2⟩ := Bridge.horizon_entropy H R hL hRL Tk β En P q hfree hq
  rw [h1, h2, (R.T_dS T I1).1]
  unfold EΛ
  ring

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

/-- **The 123 orders are `L²`** (Table I): the Planck density `c⁷/ℏG²`, the quantum field
theory estimate of the vacuum energy density, is `π² ln²2 ρ_c` in the cell's unit, and it exceeds
the ring's `ρ_Λ` by `(2 ln 2/3) L²`. -/
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

/-- the Misner–Sharp energy inside radius `r`, `c⁴r(1 − f)/2G` (the classical definition for a
static spherical solution), here of the solution without a mass, `f = fSdS G 0 Λ` -/
noncomputable def EMS (G Λ r : ℝ) : ℝ := R.c ^ 4 * r * (1 - R.fSdS G 0 Λ r) / (2 * G)
/-- the Komar energy inside radius `r`, `c⁴r²f'/2G` (the classical definition for a static
spherical solution), here of the solution without a mass, `f = fSdS G 0 Λ` -/
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

/-- **The Misner–Sharp energy with the exact count** (the factor of Sec. III.C in the energy of
Sec. IV.D): with `G` from the count's density
with its `L²/4 − L/2 + 1` rings, `η(1 − 2/L + 4/L²)` (`hJ`, `Main.jacobson_G_exact`), and the
horizon at `R_Λ` (`hdS`), the Misner–Sharp energy of the horizon is `E_Λ(1 − 2/L + 4/L²)`. -/
theorem EMS_exact (G Λ : ℝ)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * (R.η * (1 - 2 / R.L + 4 / R.L ^ 2))))
    (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.EMS G Λ R.RL = R.EΛ * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  reg_facts R
  have hRL := R.RL_pos
  have hf := R.count_factor_pos
  set f := 1 - 2 / R.L + 4 / R.L ^ 2 with hfdef
  have hη : 0 < R.η := by rw [R.eta_eq]; positivity
  unfold EMS
  rw [hdS, sub_zero, mul_one, hJ]
  unfold EΛ Shor Rhor Ec
  rw [R.eta_eq]
  unfold RL
  field_simp
  ring

/-! ### The energy of a free string (Sec. IV.E) -/

/-- **The vacuum's energy is one Landauer energy per string** (Sec. IV.D): at the temperature `T`
that `I1` gives for the lap, `k_BT = E_c/L` (`T_dS`), the vacuum's energy `E_Λ` over the `L²/4`
strings is `k_BT ln 2`, Landauer's energy of a bit, and the strings' heat, `T` times one bit each
(`Shor`), is `E_Λ`. -/
theorem vacuum_per_string (T : ℝ) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) :
    R.EΛ / R.Rhor = R.kB * T * R.ln2 ∧ R.kB * T * R.Shor = R.EΛ := by
  reg_facts R
  have hT := (R.T_dS T I1).1
  have hRh : R.Rhor ≠ 0 := by unfold Rhor; positivity
  unfold EΛ Shor
  rw [hT]
  constructor
  · field_simp
  · ring

/-- **The Misner–Sharp energy is one Landauer energy for each ring of the count** (Sec. IV.E): with
`G` from the count's exact density (`hJ`), the horizon at `R_Λ` (`hdS`) and its temperature that
of the lap (`I1`), the Misner–Sharp energy of the horizon is `k_BT ln 2` for each of its
`L²/4 − L/2 + 1` rings (`Bridge.counts_exact`): the count's factor `1 − 2/L + 4/L²` cancels between
`G` and the number of rings. -/
theorem EMS_per_ring {L : ℕ} (H : Horizon L) (hL : 4 ≤ L) (hRL : R.L = L) (G Λ T : ℝ)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * (R.η * (1 - 2 / R.L + 4 / R.L ^ 2))))
    (hdS : R.fSdS G 0 Λ R.RL = 0) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) :
    R.EMS G Λ R.RL = Fintype.card H.Loop * (R.kB * T * R.ln2) := by
  have hRh : R.Rhor ≠ 0 := by unfold Rhor; have := R.L_pos; positivity
  have hv := (R.vacuum_per_string T I1).1
  rw [R.EMS_exact G Λ hJ hdS, (Bridge.counts_exact H R hL hRL).1, ← hv]
  field_simp

/-- **The split of a string's energy** (Sec. IV.E).  With the strings' mean energy one horizon
thermal energy, `ε_s = k_BT_dS` (`hεs`, derived by `Carriers.string_energy` from the Gibbs
distribution at the horizon's temperature), a string's
heat, the horizon's temperature times the string's one bit of entropy, is `ln 2` of it and equals
the vacuum's energy per string of the horizon (`vacuum_per_string`), and the rest, `(1 − ln 2)ε_s`,
is matter, positive. -/
theorem string_split (T εs : ℝ) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) (hεs : εs = R.kB * T) :
    R.ln2 * εs = R.EΛ / R.Rhor ∧ εs = R.ln2 * εs + (1 - R.ln2) * εs ∧ 0 < (1 - R.ln2) * εs := by
  reg_facts R
  have hv := (R.vacuum_per_string T I1).1
  have hT := (R.T_dS T I1).2
  have hTpos : 0 < R.kB * T := by rw [hT]; have := R.RL_pos; positivity
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  refine ⟨?_, by ring, ?_⟩
  · rw [hv, hεs]; ring
  · rw [hεs]; exact mul_pos hm hTpos

/-- **The vacuum's share is `ln 2`** (Sec. IV.E).  The energy inside the horizon is the strings'
and nothing else's (Postulate 1, `hin`: `E_in` is the sum of the strings' energies), whose mean is
`k_BT_dS` (`hmean`); the vacuum's energy, the Misner–Sharp energy of the horizon, is
`k_BT_dS ln 2` for each of the same strings (`EMS_per_ring`).  So the vacuum's share of the energy
inside the horizon is `Ω_Λ = ln 2`. -/
theorem vacuum_share {L : ℕ} (H : Horizon L) (hL : 4 ≤ L) (hRL : R.L = L) (G Λ T Ein : ℝ)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * (R.η * (1 - 2 / R.L + 4 / R.L ^ 2))))
    (hdS : R.fSdS G 0 Λ R.RL = 0) (I1 : R.kB * T = R.ℏ / (R.L * R.tc))
    (Es : H.Loop → ℝ) (hmean : (∑ l, Es l) / Fintype.card H.Loop = R.kB * T)
    (hin : Ein = ∑ l, Es l) :
    R.EMS G Λ R.RL / Ein = R.ln2 := by
  reg_facts R
  have hN : (0 : ℝ) < Fintype.card H.Loop := by
    rw [(Bridge.counts_exact H R hL hRL).1]
    have := R.count_factor_pos
    unfold Rhor
    positivity
  have hT := (R.T_dS T I1).2
  have hTpos : 0 < R.kB * T := by rw [hT]; have := R.RL_pos; positivity
  have hsum : Ein = (Fintype.card H.Loop : ℝ) * (R.kB * T) := by
    rw [hin, ← hmean]
    field_simp
  have hT' : T ≠ 0 := by
    intro h
    rw [h, mul_zero] at hTpos
    exact lt_irrefl 0 hTpos
  rw [R.EMS_per_ring H hL hRL G Λ T hJ hdS I1, hsum]
  field_simp

/-- **The free tick of a string of the mean energy is the factor `e^{−i/L}`** (Sec. IV.E): by
Sec. II's definition of energy the tick of a string of energy `E` is `e^{−iEt_c/ℏ}` on every state
(`hS`, `P1.string_energies` for one string), and the strings' mean energy is `k_BT_dS = ℏ/(Lt_c)`
(`I1`;
the Gibbs mean, `Carriers.string_energy`), so for that energy `Et_c/ℏ = 1/L`: on average a
string's global phase decreases by one radian in a lap.  The factor is one for all the string's
states, so the energy adds no state. -/
theorem string_tick {L : ℕ} (T : ℝ) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) (τ : Qubit.Tick L)
    (hS : τ.U = Complex.exp (-((R.kB * T * R.tc / R.ℏ : ℝ) : ℂ) * Complex.I) • (1 : Qubit.Op)) :
    τ.U = Complex.exp (-((1 / R.L : ℝ) : ℂ) * Complex.I) • (1 : Qubit.Op) := by
  reg_facts R
  have htc : R.tc ≠ 0 := by unfold tc; positivity
  have h : R.kB * T * R.tc / R.ℏ = 1 / R.L := by
    rw [I1]; field_simp
  rw [hS, h]

/-- **The Komar energy the mass adds** (Sec. III.C): the Komar energy `c⁴r²f′/2G` inside any sphere
about the mass, less that of the solution without the mass at the same `Λ`, is `Mc²` at every `Λ`,
the energy that gravitates, which `Reg.newton` shows is two Landauer energies for each string of the
sphere.  The rest, `−Λc⁴r³/3G`, is the vacuum's: `−2E_Λ` at the horizon (`komar_misner_sharp`). -/
theorem komar_mass (G M Λ r : ℝ) (hr : 0 < r) (hG : G ≠ 0) :
    R.c ^ 4 * r ^ 2 * (deriv (R.fSdS G M Λ) r - deriv (R.fSdS G 0 Λ) r) / (2 * G)
      = M * R.c ^ 2 := by
  reg_facts R
  rw [(R.hasDerivAt_fSdS G M Λ r hr.ne').deriv, (R.hasDerivAt_fSdS G 0 Λ r hr.ne').deriv]
  have hr' := hr.ne'
  field_simp
  ring

/-- **Eq. (push)**: with the boundary condition, the field of the solution about a mass is
`g = GM/r² − c²r/R_Λ²`, the pull of the mass less the push of the ring's content (`hdS` for the
constant of the solution about the mass, the same as without it, `lambda_with_mass`), and in cells
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
`r_z³ = GMR_Λ²/c²`, where each equals `c²r_z/R_Λ²` (`hdS` for the constant of the solution about
the mass, the same as without it, `lambda_with_mass`).  That is below the scale `a₀` of Eq. (f)
exactly when `r_z < (1 − ln 2)R_Λ/(2 ln 2)`, so for any smaller mass the pull that meets the push is
in the deep regime, Eq. (deep). -/
theorem zero_gravity (G M Λ rz : ℝ) (hrz : 0 < rz)
    (hdS : R.fSdS G 0 Λ R.RL = 0) (hz : R.gSdS G M Λ rz = 0) :
    rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2 ∧ G * M / rz ^ 2 = R.c ^ 2 * rz / R.RL ^ 2 ∧
    (R.c ^ 2 * rz / R.RL ^ 2 < R.a0 ↔ rz < (1 - R.ln2) * R.RL / (2 * R.ln2)) := by
  reg_facts R
  have hrz' : rz ≠ 0 := hrz.ne'
  have hRL := R.RL_pos
  have hRL' := R.RL_pos.ne'
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hg : R.gSdS G M Λ rz = G * M / rz ^ 2 - R.c ^ 2 * rz / R.RL ^ 2 := by
    rw [R.gSdS_eq G M Λ rz hrz', (R.deSitter G Λ).1 hdS]
    field_simp
  have hpull : G * M / rz ^ 2 = R.c ^ 2 * rz / R.RL ^ 2 := by
    rw [hg] at hz
    linarith
  have h3 : rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2 := by
    rw [eq_div_iff (by positivity)]
    field_simp at hpull
    linear_combination (-1 : ℝ) * hpull
  refine ⟨h3, hpull, ?_⟩
  unfold a0
  rw [div_lt_div_iff₀ (by positivity) (by positivity), lt_div_iff₀ (by positivity)]
  constructor
  · intro h
    nlinarith [sq_nonneg R.RL, mul_pos (pow_pos R.c_pos 2) hRL]
  · intro h
    have hc2 : 0 < R.c ^ 2 * R.RL := by positivity
    nlinarith

/-- **Any galaxy, group or cluster** (Sec. IV.D): the zero-gravity radius `r_z³ = GMR_Λ²/c²` lies
below `(1 − ln 2)R_Λ/(2 ln 2)`, and so in the deep regime (`zero_gravity`), exactly when
`M < ((1 − ln 2)/2 ln 2)³ c²R_Λ/G`. -/
theorem zero_gravity_mass (G M rz : ℝ) (hG : 0 < G) (hrz : 0 < rz)
    (h3 : rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2) :
    rz < (1 - R.ln2) * R.RL / (2 * R.ln2) ↔
      M < ((1 - R.ln2) / (2 * R.ln2)) ^ 3 * (R.c ^ 2 * R.RL / G) := by
  reg_facts R
  have hRL := R.RL_pos
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hk : 0 < (1 - R.ln2) * R.RL / (2 * R.ln2) := by positivity
  rw [← pow_lt_pow_iff_left₀ hrz.le hk.le (by norm_num : (3 : ℕ) ≠ 0), h3,
    div_lt_iff₀ (by positivity)]
  have e1 : ((1 - R.ln2) * R.RL / (2 * R.ln2)) ^ 3 * R.c ^ 2
      = R.RL ^ 2 * (((1 - R.ln2) / (2 * R.ln2)) ^ 3 * (R.c ^ 2 * R.RL / G) * G) := by
    field_simp
  rw [e1, show G * M * R.RL ^ 2 = R.RL ^ 2 * (M * G) by ring]
  have hR2 : 0 < R.RL ^ 2 := by positivity
  constructor
  · intro h
    have := lt_of_mul_lt_mul_left h hR2.le
    exact lt_of_mul_lt_mul_right this hG.le
  · intro h
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h hG) hR2

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
on `|Ġ/G|` bounds `|Λ̇/Λ|` by the same number.  `hK` is derived by `GLambda_constant`;
`Lambda_rate_in_time` puts the two together. -/
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

/-- **`w = −1` exactly** (Table I): the ring's energy density `ρ_Λ = 3π²ρ_c ln 2/2L²` is fixed by `L`,
the cell and the bit per ring, constants of the register, so it does not change as the universe
expands.  This theorem writes the first law for that fixed density; `w_exact_in_time` writes it
for the density of the register at each time and derives the constancy from `L` and the cell, the
constants of Postulate 1. -/
theorem w_exact (a : ℝ → ℝ) (adot w t : ℝ) (hH : adot / a t ≠ 0)
    (hA : HasDerivAt a adot t)
    (first_law : HasDerivAt (fun s => R.ρΛ * a s ^ 3)
      (-(w * R.ρΛ) * deriv (fun s => a s ^ 3) t) t) :
    w = -1 := by
  have ha : a t ≠ 0 := fun h => hH (by rw [h, div_zero])
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

/-! ### Constancy in time (Secs. IV.D and VI) -/

/-- **`GΛ` is fixed by `L` alone, so it is constant in time** (Eq. (Lambda), Sec. VI).  `Rt s` is
the register at the time `s`, and `G s`, `Λ s` are Newton's constant and the cosmological constant
then.  Inputs, each named: `L` is one natural number at every time (`hL`, Postulate 1); `c`, `ℏ`
and `k_B` are the same at every time (`hconst`, the defining constants of the SI, so by the
definition of the units); the horizon is where the de Sitter solution's `f` vanishes (`hdS`, the solution of
Sec. IV.D, as in `G_Lambda`); Jacobson's step gives `G` (`hJ`, thermodynamics).  This is the `hK`
of `constancy_of_Lambda`, derived. -/
theorem GLambda_constant (Rt : ℝ → Reg) (G Λ : ℝ → ℝ) (hL : ∀ s, (Rt s).L = (Rt 0).L)
    (hconst : ∀ s, (Rt s).c = (Rt 0).c ∧ (Rt s).ℏ = (Rt 0).ℏ ∧ (Rt s).kB = (Rt 0).kB)
    (hdS : ∀ s, (Rt s).fSdS (G s) 0 (Λ s) (Rt s).RL = 0)
    (hJ : ∀ s, G s = (Rt s).c ^ 3 * (Rt s).kB / (4 * (Rt s).ℏ * (Rt s).η)) :
    ∀ s, G s * Λ s = 12 * (Rt 0).pi * (Rt 0).c ^ 3 / ((Rt 0).ℏ * (Rt 0).L ^ 2 * (Rt 0).ln2) := by
  intro s
  obtain ⟨hc, hℏ, -⟩ := hconst s
  have hpi : (Rt s).pi = (Rt 0).pi := rfl
  have hln2 : (Rt s).ln2 = (Rt 0).ln2 := rfl
  rw [((Rt s).G_Lambda (G s) (Λ s) (hJ s) (hdS s)).1, hc, hℏ, hpi, hln2, hL]

/-- **The horizon's radius is constant in time** (Secs. IV.D and VI): `R_Λ = Lℓ_c/2π` (Eq. (ident)),
with `L` and the cell `ℓ_c` the constants of Postulate 1 (`hL`, `hℓc`): one natural number and one
length, the same at every time, the first of the "two facts of the register" of Sec. VI. -/
theorem horizon_constant (Rt : ℝ → Reg) (hL : ∀ s, (Rt s).L = (Rt 0).L)
    (hℓc : ∀ s, (Rt s).ℓc = (Rt 0).ℓc) :
    ∀ s, (Rt s).RL = (Rt 0).RL := by
  intro s
  have hpi : (Rt s).pi = (Rt 0).pi := rfl
  unfold RL
  rw [hL, hℓc, hpi]

/-- **`Λ` is constant in time** (Sec. IV.D, "With `R_Λ` constant, and `c`, `ℏ` and `k_B` fixed by
the definition of the SI units, `G`, `a₀`, and `Λ` are all constant"): the horizon is at `R_Λ = √(3/Λ)` (`hdS`, `deSitter`), and `R_Λ` is constant, since `L`
and the cell are the constants of Postulate 1 (`hL`, `hℓc`, `horizon_constant`).  So the constancy
of `Λ` that Einstein's equations assert is here a consequence of the register's constants, not an
input. -/
theorem Lambda_constant (Rt : ℝ → Reg) (G Λ : ℝ → ℝ) (hL : ∀ s, (Rt s).L = (Rt 0).L)
    (hℓc : ∀ s, (Rt s).ℓc = (Rt 0).ℓc)
    (hdS : ∀ s, (Rt s).fSdS (G s) 0 (Λ s) (Rt s).RL = 0) :
    ∀ s, Λ s = Λ 0 := by
  intro s
  rw [((Rt s).deSitter (G s) (Λ s)).1 (hdS s), ((Rt 0).deSitter (G 0) (Λ 0)).1 (hdS 0),
    horizon_constant Rt hL hℓc s]

/-- **`G` is constant in time** (Sec. IV.D): `G = c³ℓ_c²/(πℏ ln 2)` (Eq. (G), `G_eq`), with the
cell constant. -/
theorem G_constant (Rt : ℝ → Reg) (G : ℝ → ℝ)
    (hconst : ∀ s, (Rt s).c = (Rt 0).c ∧ (Rt s).ℏ = (Rt 0).ℏ ∧ (Rt s).kB = (Rt 0).kB)
    (hℓc : ∀ s, (Rt s).ℓc = (Rt 0).ℓc)
    (hJ : ∀ s, G s = (Rt s).c ^ 3 * (Rt s).kB / (4 * (Rt s).ℏ * (Rt s).η)) :
    ∀ s, G s = G 0 := by
  intro s
  obtain ⟨hc, hℏ, -⟩ := hconst s
  have hpi : (Rt s).pi = (Rt 0).pi := rfl
  have hln2 : (Rt s).ln2 = (Rt 0).ln2 := rfl
  rw [((Rt s).G_eq (G s) (hJ s)).1, ((Rt 0).G_eq (G 0) (hJ 0)).1, hc, hℏ, hpi, hln2, hℓc]

/-- **The vacuum's energy density is constant in time** (Sec. VI): `ρ_Λ` is a function of `L`,
the cell, the bit per ring and the horizon's radius (`ρΛ`, `EΛ`, `Shor`, `Ec`), all constant
(`horizon_constant` for the radius). -/
theorem rhoΛ_constant (Rt : ℝ → Reg) (hL : ∀ s, (Rt s).L = (Rt 0).L)
    (hconst : ∀ s, (Rt s).c = (Rt 0).c ∧ (Rt s).ℏ = (Rt 0).ℏ ∧ (Rt s).kB = (Rt 0).kB)
    (hℓc : ∀ s, (Rt s).ℓc = (Rt 0).ℓc) :
    ∀ s, (Rt s).ρΛ = (Rt 0).ρΛ := by
  have hRL := horizon_constant Rt hL hℓc
  intro s
  obtain ⟨hc, hℏ, -⟩ := hconst s
  have hpi : (Rt s).pi = (Rt 0).pi := rfl
  have hln2 : (Rt s).ln2 = (Rt 0).ln2 := rfl
  unfold ρΛ EΛ Shor Rhor Ec
  rw [hL, hc, hℏ, hpi, hln2, hℓc, hRL]

/-- **`w = −1`, with the constancy of `ρ_Λ` derived** (Sec. VI).  The first law is written for
the vacuum's density `ρ_Λ(s)` of the register at the time `s`, which a priori could change.  What
makes it constant is named: `L` and the cell are the constants of Postulate 1, one number and one
length at every time (`hL`, `hℓc`: the first of the "two facts of the register" of Sec. VI), and
`c`, `ℏ` and
`k_B` are the same at every time (`hconst`, the defining constants of the SI).  Then the horizon's radius and `ρ_Λ` are
constant (`horizon_constant`, `rhoΛ_constant`), and the first law gives `w = −1` (`w_exact`).  The
bit per ring is the count (`Shor`), inside `ρ_Λ`. -/
theorem w_exact_in_time (Rt : ℝ → Reg) (hL : ∀ s, (Rt s).L = (Rt 0).L)
    (hℓc : ∀ s, (Rt s).ℓc = (Rt 0).ℓc)
    (hconst : ∀ s, (Rt s).c = (Rt 0).c ∧ (Rt s).ℏ = (Rt 0).ℏ ∧ (Rt s).kB = (Rt 0).kB)
    (a : ℝ → ℝ) (adot w t : ℝ) (hH : adot / a t ≠ 0) (hA : HasDerivAt a adot t)
    (first_law : HasDerivAt (fun s => (Rt s).ρΛ * a s ^ 3)
      (-(w * (Rt t).ρΛ) * deriv (fun s => a s ^ 3) t) t) :
    w = -1 := by
  have hρ := rhoΛ_constant Rt hL hconst hℓc
  have e : (fun s => (Rt s).ρΛ * a s ^ 3) = fun s => (Rt 0).ρΛ * a s ^ 3 := by
    funext s
    rw [hρ s]
  rw [e, hρ t] at first_law
  exact (Rt 0).w_exact a adot w t hH hA first_law

/-- **`Λ̇/Λ = −Ġ/G`, with `GΛ` constant derived** (Sec. VI, Appendix A): `constancy_of_Lambda`
with its `hK` from `GLambda_constant`. -/
theorem Lambda_rate_in_time (Rt : ℝ → Reg) (G Λ : ℝ → ℝ) (hL : ∀ s, (Rt s).L = (Rt 0).L)
    (hconst : ∀ s, (Rt s).c = (Rt 0).c ∧ (Rt s).ℏ = (Rt 0).ℏ ∧ (Rt s).kB = (Rt 0).kB)
    (hdS : ∀ s, (Rt s).fSdS (G s) 0 (Λ s) (Rt s).RL = 0)
    (hJ : ∀ s, G s = (Rt s).c ^ 3 * (Rt s).kB / (4 * (Rt s).ℏ * (Rt s).η))
    (G' Λ' t : ℝ) (hG : HasDerivAt G G' t) (hΛ : HasDerivAt Λ Λ' t)
    (hG0 : G t ≠ 0) (hΛ0 : Λ t ≠ 0) :
    Λ' / Λ t = -(G' / G t) :=
  constancy_of_Lambda G Λ G' Λ' t _ hG hΛ (GLambda_constant Rt G Λ hL hconst hdS hJ) hG0 hΛ0

/-- **The equation-of-state bound** (Sec. VI, item 6): with the fluid equation, `|ρ̇/ρ| ≤ b`
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
