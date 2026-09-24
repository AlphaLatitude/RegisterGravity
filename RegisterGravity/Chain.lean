import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The chain of the paper, Secs. II–IV

Every relation of *Gravitation from Hilbert-Space Granularity* (v11.1) that follows from the
register's counts, with the physical inputs stated as **named hypotheses** of the theorems that
use them.  A theorem's hypotheses are therefore its ledger: what it takes from outside the
postulates is exactly what is written in its statement, and nothing else.  The `#print axioms` of
every theorem is the logical minimum (`propext`, `Classical.choice`, `Quot.sound`); no physical
axiom is declared.

## The inputs, as they appear below

Beyond the two postulates the paper takes two inputs, thermodynamics and elasticity, both in form
and neither as a number.

Thermodynamics:
* `I1` (a horizon is thermal): a horizon whose lap time is `τ` has `k_B T = ℏ/τ`
  [Gibbons–Hawking, Unruh; the KMS period].  Hypothesis `I1`.
* Jacobson: the entropy of a horizon is proportional to its area, `S = ηA`, and the heat that
  crosses a local horizon obeys the Clausius relation; with the Raychaudhuri equation this gives
  Einstein's equation with `G = c³k_B/(4ℏη)`.  Hypothesis `hJ`; the proportionality `S = ηA` is
  the definition `Ns` of the strings a sphere holds.  The count fixes `η` (`eta_eq`), and from it
  follow the counts of every sphere in the bulk (`bulk_counts`, `ratio_of_areas`).
* The first law, `d(ρV) = −p dV`, for a component of the universe; it gives the fluid equation
  and `w = −1` (`Cosmo.lean`).  Hypothesis `first_law`.

Elasticity, in the galactic law only (`Galactic.lean`):
* `I5`, `I6` (Verlinde's elastic response): `ε² A = dV_M/dr`, with equality under his assumption
  on the principal strain, and `Σ_D = (a_Λ/8πG) ε`.  Hypotheses `I5`, `I6`.

The share of a string's entropy inside a sphere is proved from Postulate 1 (`string_share`,
`Sin_share`): the string's one unit is spread evenly over its cells, and of the `L/4` between the
body and the horizon, `n` lie inside the sphere.

## The solution of Einstein's equation

One result of general relativity is stated rather than proved: the Schwarzschild–de Sitter
solution about a mass (`fSdS`).  Mathlib has no Lorentzian curvature, so that it solves Einstein's
equation is not checked here.  Everything else the paper takes from general relativity is derived
from it: Newton's law and Padmanabhan's equipartition (`newton`), Gauss's law (`gauss`), the de
Sitter radius `Λ = 3/R_Λ²` (`deSitter`), the shift of the horizon (`sds_horizon_shift`), the area
deficit (`area_deficit`), the push (`push`), and the zero-velocity radius (`zero_velocity`).  The
integration constant `Λ` is fixed by the boundary condition of Sec. IV.D, that the horizon of the
solution without a mass is the register's, at `R_Λ` (hypothesis `hdS`).

The register's own inputs are definitions: the units of the cell, the placement
`R_Λ = Lℓ_c/2π`, and the counts `L²/2` and `L²/4` (from `Horizon.counts`, to leading order).
-/

open Real

namespace Register

/-- The register's constants: the speed of light, `ℏ`, `k_B`, the cell, the length `L` of the
largest ring (as a real number), and `π` (a positive real; its value is never used here). -/
structure Reg where
  c : ℝ
  ℏ : ℝ
  kB : ℝ
  ℓc : ℝ
  L : ℝ
  pi : ℝ
  c_pos : 0 < c
  ℏ_pos : 0 < ℏ
  kB_pos : 0 < kB
  ℓc_pos : 0 < ℓc
  L_pos : 0 < L
  pi_pos : 0 < pi

namespace Reg

variable (R : Reg)

/-- Introduce the positivity and non-vanishing facts of the register's constants into the
local context, where `positivity` and `field_simp` find them. -/
macro "reg_facts " R:term : tactic => `(tactic| (
  have := ($R).c_pos; have := ($R).ℏ_pos; have := ($R).kB_pos
  have := ($R).ℓc_pos; have := ($R).L_pos; have := ($R).pi_pos
  have := ($R).c_pos.ne'; have := ($R).ℏ_pos.ne'; have := ($R).kB_pos.ne'
  have := ($R).ℓc_pos.ne'; have := ($R).L_pos.ne'; have := ($R).pi_pos.ne'))

lemma nz : R.c ≠ 0 ∧ R.ℏ ≠ 0 ∧ R.kB ≠ 0 ∧ R.ℓc ≠ 0 ∧ R.L ≠ 0 ∧ R.pi ≠ 0 :=
  ⟨R.c_pos.ne', R.ℏ_pos.ne', R.kB_pos.ne', R.ℓc_pos.ne', R.L_pos.ne', R.pi_pos.ne'⟩

/-! ### Units of the cell (Sec. II) -/

/-- the tick, `t_c = ℓ_c/c` -/
noncomputable def tc : ℝ := R.ℓc / R.c
/-- the mass of the cell, `m_c = ℏ/(cℓ_c)` -/
noncomputable def mc : ℝ := R.ℏ / (R.c * R.ℓc)
/-- the energy of the cell, `E_c = ℏc/ℓ_c` -/
noncomputable def Ec : ℝ := R.ℏ * R.c / R.ℓc
/-- the acceleration of the cell, `a_c = c²/ℓ_c` -/
noncomputable def ac : ℝ := R.c ^ 2 / R.ℓc
/-- the energy density of the cell, `ρ_c = E_c/ℓ_c³` -/
noncomputable def ρc : ℝ := R.Ec / R.ℓc ^ 3

/-! ### The placement and the count (Sec. II) -/

/-- **The placement**, Eq. (ident): `R_Λ = Lℓ_c/2π`. -/
noncomputable def RL : ℝ := R.L * R.ℓc / (2 * R.pi)
/-- the area of the horizon in the interpolating continuum -/
noncomputable def Ahor : ℝ := 4 * R.pi * R.RL ^ 2
/-- the cells of the horizon, `L²/2` to leading order (`Horizon.counts`) -/
noncomputable def Chor : ℝ := R.L ^ 2 / 2
/-- the largest rings of the horizon, `L²/4` to leading order (`Horizon.counts`) -/
noncomputable def Rhor : ℝ := R.L ^ 2 / 4
/-- **The entropy**, Eq. (S): one string per largest ring. -/
noncomputable def Shor : ℝ := R.Rhor
/-- a cell's share of the area -/
noncomputable def cellShare : ℝ := R.Ahor / R.Chor
/-- a ring's share of the area -/
noncomputable def ringShare : ℝ := R.Ahor / R.Rhor
/-- the entropy per unit area of the horizon, `η = k_B R/A_hor` -/
noncomputable def η : ℝ := R.kB * R.Shor / R.Ahor

lemma RL_pos : 0 < R.RL := by reg_facts R; unfold RL; positivity
lemma Ahor_pos : 0 < R.Ahor := by unfold Ahor; have := R.RL_pos; reg_facts R; positivity

/-- A cell's share of the horizon's area is `2ℓ_c²/π`, a ring's is `4ℓ_c²/π` (Sec. II). -/
theorem shares : R.cellShare = 2 * R.ℓc ^ 2 / R.pi ∧ R.ringShare = 4 * R.ℓc ^ 2 / R.pi := by
  reg_facts R
  unfold cellShare ringShare Ahor Chor Rhor RL
  constructor <;> (field_simp; ring)

/-- The lap time of the largest ring is the de Sitter period, Eq. (clock): `Lt_c = 2πR_Λ/c`. -/
theorem lap_time : R.L * R.tc = 2 * R.pi * R.RL / R.c := by
  reg_facts R
  unfold tc RL
  field_simp

/-- The quarter lap (Sec. II): the horizon's proper distance `πR_Λ/2` is `Lℓ_c/4`, a quarter of
the largest ring, halfway to the opposite cell. -/
theorem quarter_lap : R.pi * R.RL / 2 = R.L * R.ℓc / 4 := by
  reg_facts R
  unfold RL
  field_simp
  ring

/-! ### Counting in the bulk, Eq. (N) -/

/-- the distance in cells, `n = r/ℓ_c` -/
noncomputable def n (r : ℝ) : ℝ := r / R.ℓc
/-- the strings a sphere of radius `r` holds: its entropy over `k_B`.  The entropy of a horizon
is proportional to its area, `S = ηA`, which is part of the thermodynamic input of Jacobson, and
the entropy per unit area `η` is the horizon's, fixed by the count (`eta_eq`). -/
noncomputable def Ns (r : ℝ) : ℝ := R.η * (4 * R.pi * r ^ 2) / R.kB
/-- the cells of a sphere of radius `r`: two for each string, as on the horizon, where the count
gives `C = 2R` (`Horizon.counts`) -/
noncomputable def Nc (r : ℝ) : ℝ := 2 * R.Ns r

/-- Eq. (N): `N_c(r) = 2π²n²` and `N_s(r) = π²n²`; `L` cancels. -/
theorem bulk_counts (r : ℝ) :
    R.Nc r = 2 * R.pi ^ 2 * R.n r ^ 2 ∧ R.Ns r = R.pi ^ 2 * R.n r ^ 2 := by
  reg_facts R
  unfold Nc Ns η Shor Rhor Ahor RL n
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **The ratio of areas**, derived: a sphere of radius `r` holds the fraction `(r/R_Λ)²` of the
horizon's rings and cells, its area in units of a ring's (or a cell's) share. -/
theorem ratio_of_areas (r : ℝ) :
    R.Ns r = R.Rhor * (r / R.RL) ^ 2 ∧ R.Nc r = R.Chor * (r / R.RL) ^ 2 ∧
    R.Ns r = 4 * R.pi * r ^ 2 / R.ringShare := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold Ns η Shor Rhor Ahor
    field_simp
  · unfold Nc Ns η Shor Rhor Ahor Chor
    field_simp
    ring
  · unfold Ns η Shor ringShare Rhor Ahor
    field_simp

/-! ### The temperature of a horizon in cells (Sec. III.A) -/

/-- **I1 applied to the largest ring**, Eq. (energy): `k_B T_dS = E_c/L = ℏc/2πR_Λ`. -/
theorem T_dS (T : ℝ) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) :
    R.kB * T = R.Ec / R.L ∧ R.kB * T = R.ℏ * R.c / (2 * R.pi * R.RL) := by
  reg_facts R
  rw [I1]
  unfold tc Ec RL
  constructor <;> (field_simp)

/-- the ring of a held observer: the ring whose lap time is the thermal period `2πc/a` of
the Rindler horizon `c²/a` behind him (the period is the geometry of that horizon) -/
noncomputable def La (a : ℝ) : ℝ := 2 * R.pi * R.c ^ 2 / (a * R.ℓc)

theorem La_lap (a : ℝ) (ha : 0 < a) : R.La a * R.tc = 2 * R.pi * R.c / a := by
  reg_facts R
  unfold La tc
  field_simp

/-- **I1 applied to the ring `L_a`**: Unruh's temperature, `k_B T_a = ℏa/2πc`. -/
theorem T_Unruh (a T : ℝ) (ha : 0 < a) (I1 : R.kB * T = R.ℏ / (R.La a * R.tc)) :
    R.kB * T = R.ℏ * a / (2 * R.pi * R.c) := by
  reg_facts R
  rw [I1, R.La_lap a ha]
  field_simp

/-- The register's quantum of a ring is `h` over its lap time; the temperature is that quantum
over `2π`: `ℏ/τ = (2πℏ/τ)/2π`. -/
theorem temperature_is_quantum_over_two_pi (τ : ℝ) (hτ : τ ≠ 0) :
    R.ℏ / τ = (2 * R.pi * R.ℏ / τ) / (2 * R.pi) := by
  reg_facts R
  field_simp

/-! ### Newton's constant from the count (Sec. III.B–C) -/

/-- The entropy per unit area of the horizon is `η = πk_B/4ℓ_c²`, Eq. (G). -/
theorem eta_eq : R.η = R.pi * R.kB / (4 * R.ℓc ^ 2) := by
  reg_facts R
  unfold η Shor Rhor Ahor RL
  field_simp; ring

/-- Energy crossing a horizon adds `2πc/ℏa` rings per unit of energy, and with a ring's share
`4ℓ_c²/π` it adds the area `(8ℓ_c²c/ℏa) δQ` (Sec. III.B). -/
theorem area_per_heat (a δQ : ℝ) (ha : 0 < a) :
    (2 * R.pi * R.c / (R.ℏ * a)) * δQ * R.ringShare = (8 * R.ℓc ^ 2 * R.c / (R.ℏ * a)) * δQ := by
  reg_facts R
  rw [R.shares.2]
  field_simp; ring

/-- **Jacobson (`hJ`) with the register's entropy density**, Eq. (G):
`G = c³ℓ_c²/πℏ = 4πc³R_Λ²/ℏL²`. -/
theorem G_eq (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ) ∧ G = 4 * R.pi * R.c ^ 3 * R.RL ^ 2 / (R.ℏ * R.L ^ 2) := by
  reg_facts R
  rw [hJ, R.eta_eq]
  unfold RL
  constructor <;> (field_simp <;> ring)

/-- The Planck length, defined from `G`. -/
noncomputable def ℓP (G : ℝ) : ℝ := Real.sqrt (R.ℏ * G / R.c ^ 3)

/-- **The cell from Newton's constant**, Eq. (cell): `ℓ_c = √(πℏG/c³) = √π ℓ_P`. -/
theorem cell_from_G (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.ℓc = Real.sqrt (R.pi * R.ℏ * G / R.c ^ 3) ∧ R.ℓc = Real.sqrt R.pi * R.ℓP G := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hsq : R.pi * R.ℏ * G / R.c ^ 3 = R.ℓc ^ 2 := by
    rw [hG]; field_simp
  constructor
  · rw [hsq, Real.sqrt_sq R.ℓc_pos.le]
  · unfold ℓP
    rw [← Real.sqrt_mul R.pi_pos.le]
    have h2 : R.pi * (R.ℏ * G / R.c ^ 3) = R.ℓc ^ 2 := by rw [← hsq]; ring
    rw [h2, Real.sqrt_sq R.ℓc_pos.le]

/-- With the cell fixed, the horizon's entropy is `L²/4 = πR_Λ²/ℓ_P² = A_hor/4ℓ_P²`: Bekenstein
and Hawking's quarter per Planck area is the register's one string per ring, a ring's share
being `4ℓ_P²` (Sec. III.C).  (The paper's text writes the middle term with `ℓ_c`; it is `ℓ_P`,
equivalently `π²R_Λ²/ℓ_c²`.) -/
theorem entropy_quarter (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.Shor = R.pi * R.RL ^ 2 / R.ℓP G ^ 2 ∧ R.Shor = R.pi ^ 2 * R.RL ^ 2 / R.ℓc ^ 2 ∧
    R.Shor = R.Ahor / (4 * R.ℓP G ^ 2) ∧ R.ringShare = 4 * R.ℓP G ^ 2 := by
  reg_facts R
  have hℓP : R.ℓP G ^ 2 = R.ℓc ^ 2 / R.pi := by
    have h := (R.cell_from_G G hJ).2
    have hs : Real.sqrt R.pi ^ 2 = R.pi := Real.sq_sqrt R.pi_pos.le
    have : R.ℓc ^ 2 = R.pi * R.ℓP G ^ 2 := by rw [h, mul_pow, hs]
    rw [this]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hℓP]; unfold Shor Rhor RL; field_simp; ring
  · unfold Shor Rhor RL; field_simp; ring
  · rw [hℓP]; unfold Shor Rhor Ahor RL; field_simp; ring
  · rw [hℓP, R.shares.2]; field_simp

/-- **A misprint in Sec. III.C of v11, caught here and corrected in v11.1.**  Version 11 wrote
`L²/4 = πR_Λ²/ℓ_c²`; with the placement that equality holds only if `π = 1`.  The correct middle
term is `π²R_Λ²/ℓ_c²`, which is `πR_Λ²/ℓ_P²` (`entropy_quarter`). -/
theorem entropy_misprint : R.Shor = R.pi * R.RL ^ 2 / R.ℓc ^ 2 ↔ R.pi = 1 := by
  reg_facts R
  have e : R.pi * R.RL ^ 2 / R.ℓc ^ 2 = R.Shor / R.pi := by
    unfold Shor Rhor RL; field_simp; ring
  have hS : 0 < R.Shor := by unfold Shor Rhor; positivity
  rw [e]
  constructor
  · intro h
    rw [eq_div_iff R.pi_pos.ne'] at h
    have h0 : R.Shor * (R.pi - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hS.ne'
    · linarith
  · intro h; rw [h, div_one]

/-! ### The solution about a mass (Secs. III–IV) -/

/-- **Schwarzschild–de Sitter**, the static solution of Einstein's equation about a mass `M`, with
`Λ` its integration constant: `ds² = −f c²dt² + dr²/f + r²dΩ²` with `f(r) = 1 − 2GM/c²r − Λr²/3`.
This is the one result of general relativity stated here rather than proved; what the paper takes
from general relativity is derived from it below. -/
noncomputable def fSdS (G M Λ r : ℝ) : ℝ := 1 - 2 * G * M / (R.c ^ 2 * r) - Λ * r ^ 2 / 3

/-- the field of the solution, the acceleration toward the mass: `g = (c²/2) df/dr`, the gradient
of the potential `Φ = c²(f − 1)/2` that the time part of the metric carries -/
noncomputable def gSdS (G M Λ r : ℝ) : ℝ := R.c ^ 2 / 2 * deriv (R.fSdS G M Λ) r

theorem hasDerivAt_fSdS (G M Λ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (R.fSdS G M Λ) (2 * G * M / (R.c ^ 2 * r ^ 2) - 2 * Λ * r / 3) r := by
  reg_facts R
  have e : R.fSdS G M Λ = fun s => 1 - 2 * G * M / R.c ^ 2 * s⁻¹ - Λ / 3 * s ^ 2 := by
    funext s; unfold fSdS; ring
  rw [e]
  have h := ((hasDerivAt_const r (1 : ℝ)).fun_sub
    ((hasDerivAt_inv hr).const_mul (2 * G * M / R.c ^ 2))).fun_sub
    ((hasDerivAt_pow 2 r).const_mul (Λ / 3))
  convert h using 1
  norm_num
  field_simp

/-- **The field of the solution**: `g = GM/r² − Λc²r/3`, the pull of the mass less the push of the
vacuum. -/
theorem gSdS_eq (G M Λ r : ℝ) (hr : r ≠ 0) :
    R.gSdS G M Λ r = G * M / r ^ 2 - Λ * R.c ^ 2 * r / 3 := by
  reg_facts R
  unfold gSdS
  rw [(R.hasDerivAt_fSdS G M Λ r hr).deriv]
  field_simp

/-- The field of the mass alone (`Λ = 0`) is Newton's, `g = GM/r²`. -/
theorem gSdS_mass (G M r : ℝ) (hr : r ≠ 0) : R.gSdS G M 0 r = G * M / r ^ 2 := by
  rw [R.gSdS_eq G M 0 r hr]; ring

/-- **The de Sitter horizon.**  Without a mass the solution has its horizon where `f = 0`, and the
register's horizon at `R_Λ` is that horizon exactly when `Λ = 3/R_Λ²`.  In Einstein's equation `Λ`
is an integration constant; this boundary condition fixes it (Sec. IV.D). -/
theorem deSitter (G Λ : ℝ) : R.fSdS G 0 Λ R.RL = 0 ↔ Λ = 3 / R.RL ^ 2 := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  unfold fSdS
  constructor
  · intro h
    simp only [mul_zero, zero_div, sub_zero] at h
    rw [eq_div_iff (by positivity)]
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Newton's law and equipartition**, Eq. (newton).  The field of the solution about the mass
alone (`Λ = 0`; the vacuum's part is the push of `push`) is `a = GM/r²`.  With I1 for the
temperature `T_a` that an observer held on the sphere sees, the energy inside the sphere is two
quanta `k_BT_a` for each of its strings, `Mc² = 2N_s(r) k_BT_a`, which is Padmanabhan's
equipartition, here derived; in cells, `a/a_c = α/πn²` with `α = M/m_c`. -/
theorem newton (G M r a T : ℝ) (hr : 0 < r)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (ha : a = R.gSdS G M 0 r)
    (I1 : R.kB * T = R.ℏ * a / (2 * R.pi * R.c)) :
    a = G * M / r ^ 2 ∧ M * R.c ^ 2 = 2 * R.Ns r * (R.kB * T) ∧
    a / R.ac = (M / R.mc) / (R.pi * R.n r ^ 2) := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hr' : r ≠ 0 := hr.ne'
  have ha' : a = G * M / r ^ 2 := by rw [ha, R.gSdS_mass G M r hr']
  refine ⟨ha', ?_, ?_⟩
  · rw [I1, (R.bulk_counts r).2, ha', hG]
    unfold n
    field_simp
  · rw [ha', hG]
    unfold ac mc n
    field_simp

/-- **Gauss's law**, derived: the mass `M` inside a sphere of radius `r`, spread over the sphere, has
the surface density `Σ = M/4πr²`, and the field of the solution there is `g = GM/r²`, so
`Σ = g/4πG`. -/
theorem gauss (G M r : ℝ) (hr : 0 < r) (hG : G ≠ 0) :
    M / (4 * R.pi * r ^ 2) = R.gSdS G M 0 r / (4 * R.pi * G) := by
  reg_facts R
  have hr' : r ≠ 0 := hr.ne'
  rw [R.gSdS_mass G M r hr']
  field_simp

/-- A continuum does not gravitate: with `η` unbounded, `G = c³k_B/4ℏη` tends to zero.  Stated as
the exact inverse relation: `G · η = c³k_B/4ℏ` (Sec. III.C, first remark). -/
theorem G_mul_eta (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G * R.η = R.c ^ 3 * R.kB / (4 * R.ℏ) := by
  reg_facts R
  have hη : R.η ≠ 0 := by rw [R.eta_eq]; positivity
  rw [hJ]; field_simp

end Reg

end Register
