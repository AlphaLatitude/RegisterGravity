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
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The chain of the paper, Secs. II–IV

Every relation of *Gravitation from Hilbert-Space Granularity* (v11.2) that follows from the
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
  [the Kubo–Martin–Schwinger period; Gibbons–Hawking, Unruh].  Hypothesis `I1`.
* Jacobson: the entropy of a horizon is proportional to its area, `S = ηA`, and the heat that
  crosses a local horizon obeys the Clausius relation; with the Raychaudhuri equation this gives
  Einstein's equation with `G = c³k_B/(4ℏη)`.  Hypothesis `hJ`; the proportionality `S = ηA` is
  the definition `Ns` of the strings a sphere holds.  The count fixes `η` (`eta_eq`), and from it
  follow the counts of every sphere in the bulk (`bulk_counts`, `ratio_of_areas`).
* The first law, `d(ρV) = −p dV`, for a component of the universe; it gives the fluid equation
  and `w = −1` (`Cosmo.lean`).  Hypothesis `first_law`.
* In de Sitter space an observer held at acceleration `a` sees the temperature
  `k_BT = (ℏ/2πc)√(a² + a_Λ²)` [Deser–Levin], a case of the thermality of horizons; it enters only
  the temperature floor (`Galactic.lean`).  Hypothesis `hDL`.

Elasticity, in the galactic law only (`Galactic.lean`):
* `I5`, `I6` (Verlinde's elastic response): `∫₀^r ε²A dr' ≤ V_M(r)`, with equality under his
  assumption on the principal strain, and `Σ_D = (a_Λ/8πG) ε`.  Hypotheses `I5`, `I6`.

## One bit per ring

The entropy of the horizon is one bit, `k_B ln 2`, for each largest ring (Sec. II, Eq. (S)); `ln 2`
enters as the positive real `ln2` of the register, whose value the chain never uses.

## The solution of Einstein's equation

Einstein's equations are derived (`G_eq` gives their coefficient).  Of their classical results the
paper uses the Schwarzschild–de Sitter solution about a mass, taken as already proven
[F. Kottler, Ann. Phys. (Leipzig) 361, 401 (1918)]; here it is the definition `fSdS`, and its field
is read in the classical weak-field way, `g = (c²/2) df/dr` (`gSdS`).  What else the paper takes
from general relativity is derived from it: Newton's law and Padmanabhan's equipartition
(`newton`), the Komar energy of the mass (`komar_mass`), Gauss's law (`gauss`), the de Sitter
radius `Λ = 3/R_Λ²` (`deSitter`), the proper distance `πR_Λ/2` to the horizon
(`proper_distance`), the outer horizon drawn in by `GM/c²` (`sds_horizon_shift`,
`sds_outer_horizon`), the area deficit (`area_deficit`), the push (`push`), the zero-gravity
radius (`zero_gravity`), and the Misner–Sharp and Komar energies of the horizon
(`komar_misner_sharp`).  The integration constant `Λ` is fixed by the horizon of the solution
without a mass being the sphere of the largest rings, at `R_Λ` (hypothesis `hdS` of the theorems
that use `Λ`); Sec. IV.D derives that from Postulate 1 and the solution's horizon, given `Λ > 0`,
and `DeSitter.horizon_radius` derives it, with `Λ > 0` as a hypothesis, from the largest ring at
rest relative to its center within the horizon and the horizon's great circles being rings of at
most `L` cells.  The perihelion and deflection formulas of Sec. IV.B are also classical
results, evaluated in `Numerics.solar_tests`.

The register's own quantities are definitions: the units of the cell, the radius of the largest
ring `R_Λ = Lℓ_c/2π` (Eq. (ident); the horizon's radius by Sec. IV.D), and the counts `L²/2` and `L²/4`, those of `Horizon.counts` to leading order in
`1/L` (`Bridge.counts_exact` gives the exact counts of a `Horizon L` in these terms).
-/

open Real

namespace Register

/-- The register's constants: the speed of light, `ℏ`, `k_B`, the cell, the length `L` of the
largest ring (as a real number), `π`, and `ln 2` (positive reals whose values are never used here). -/
structure Reg where
  c : ℝ
  ℏ : ℝ
  kB : ℝ
  ℓc : ℝ
  L : ℝ
  pi : ℝ
  ln2 : ℝ
  c_pos : 0 < c
  ℏ_pos : 0 < ℏ
  kB_pos : 0 < kB
  ℓc_pos : 0 < ℓc
  L_pos : 0 < L
  pi_pos : 0 < pi
  ln2_pos : 0 < ln2

namespace Reg

variable (R : Reg)

/-- Introduce the positivity and non-vanishing facts of the register's constants into the
local context, where `positivity` and `field_simp` find them. -/
macro "reg_facts " R:term : tactic => `(tactic| (
  have := ($R).c_pos; have := ($R).ℏ_pos; have := ($R).kB_pos
  have := ($R).ℓc_pos; have := ($R).L_pos; have := ($R).pi_pos; have := ($R).ln2_pos
  have := ($R).c_pos.ne'; have := ($R).ℏ_pos.ne'; have := ($R).kB_pos.ne'
  have := ($R).ℓc_pos.ne'; have := ($R).L_pos.ne'; have := ($R).pi_pos.ne'
  have := ($R).ln2_pos.ne'))

/-- **One bit** (Sec. II, the entropy): a doublet whose two senses are weighted equally holds the
entropy `ln 2`, and no doublet holds more: the binary entropy `−p ln p − (1 − p) ln(1 − p)` is
`ln 2` at `p = 1/2` and at most `ln 2` for every `p` (Mathlib's `Real.binEntropy`). -/
theorem one_bit : Real.binEntropy (1 / 2) = Real.log 2 ∧ ∀ p, Real.binEntropy p ≤ Real.log 2 :=
  ⟨by rw [one_div]; exact Real.binEntropy_two_inv, fun _ => Real.binEntropy_le_log_two⟩

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

/-! ### The sphere of the largest rings and the count (Sec. II) -/

/-- **The radius of the largest ring**, Eq. (ident): `R_Λ = Lℓ_c/2π`, a great circle of length
`Lℓ_c`; Sec. IV.D derives that it is the horizon's radius (`DeSitter.horizon_radius`). -/
noncomputable def RL : ℝ := R.L * R.ℓc / (2 * R.pi)
/-- the area of the sphere of the largest rings, the horizon's by Sec. IV.D -/
noncomputable def Ahor : ℝ := 4 * R.pi * R.RL ^ 2
/-- the cells of the horizon, `L²/2` to leading order in `1/L` (`Bridge.counts_exact`) -/
noncomputable def Chor : ℝ := R.L ^ 2 / 2
/-- the largest rings of the horizon, `L²/4` to leading order in `1/L` (`Bridge.counts_exact`) -/
noncomputable def Rhor : ℝ := R.L ^ 2 / 4
/-- **The entropy**, Eq. (S), in units of `k_B`: one bit, `ln 2`, for each largest ring.  The
horizon holds one string on each largest ring, the most the register allows, since a ring has no
more than one bit per cell (Sec. II, the glossary), and a string's doublet weighted equally holds
one bit (`one_bit`). -/
noncomputable def Shor : ℝ := R.Rhor * R.ln2
/-- a cell's share of the area -/
noncomputable def cellShare : ℝ := R.Ahor / R.Chor
/-- a ring's share of the area -/
noncomputable def ringShare : ℝ := R.Ahor / R.Rhor
/-- the entropy per unit area of the horizon, `η = k_B R ln 2/A_hor` -/
noncomputable def η : ℝ := R.kB * R.Shor / R.Ahor

lemma RL_pos : 0 < R.RL := by reg_facts R; unfold RL; positivity
lemma Ahor_pos : 0 < R.Ahor := by unfold Ahor; have := R.RL_pos; reg_facts R; positivity

/-- The count uses only the area of the sphere of the largest rings, `4πR_Λ² = L²ℓ_c²/π` (Sec. II). -/
theorem area_in_cells : R.Ahor = R.L ^ 2 * R.ℓc ^ 2 / R.pi := by
  reg_facts R
  unfold Ahor RL
  field_simp
  ring

/-- **The counts to leading order** (Sec. II).  The exact counts `C = L²/2 − L + 2` and
`R = L²/4 − L/2 + 1` are the leading `L²/2` and `L²/4` times `1 − 2/L + 4/L²`, so every relation
below that uses the leading counts holds to relative order `2/L`.  `Bridge.counts_exact` applies
this to the rings and cells of a `Horizon L`. -/
theorem counts_leading_order :
    R.L ^ 2 / 2 - R.L + 2 = R.Chor * (1 - 2 / R.L + 4 / R.L ^ 2) ∧
    R.L ^ 2 / 4 - R.L / 2 + 1 = R.Rhor * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  reg_facts R
  unfold Chor Rhor
  constructor <;> (field_simp; ring)

/-- To leading order in `1/L`, a cell's share of the horizon's area is `2ℓ_c²/π`, a ring's is
`4ℓ_c²/π` (Sec. II). -/
theorem shares : R.cellShare = 2 * R.ℓc ^ 2 / R.pi ∧ R.ringShare = 4 * R.ℓc ^ 2 / R.pi := by
  reg_facts R
  unfold cellShare ringShare Ahor Chor Rhor RL
  constructor <;> (field_simp; ring)

/-- The lap time of the largest ring is the de Sitter period, Eq. (clock): `Lt_c = 2πR_Λ/c`. -/
theorem lap_time : R.L * R.tc = 2 * R.pi * R.RL / R.c := by
  reg_facts R
  unfold tc RL
  field_simp

/-- The quarter lap (Sec. IV.C): the horizon's proper distance `πR_Λ/2` (`proper_distance`) is
`Lℓ_c/4`, a quarter of a largest ring. -/
theorem quarter_lap : R.pi * R.RL / 2 = R.L * R.ℓc / 4 := by
  reg_facts R
  unfold RL
  field_simp
  ring

/-! ### Counting in the bulk, Eq. (N) -/

/-- the distance in cells, `n = r/ℓ_c` -/
noncomputable def n (r : ℝ) : ℝ := r / R.ℓc
/-- the strings a sphere of radius `r` holds: its entropy over `k_B ln 2`, one bit per string.
The entropy of a horizon is proportional to its area, `S = ηA`, which is part of the thermodynamic
input of Jacobson, and the entropy per unit area `η` is the horizon's, fixed by the count
(`eta_eq`). -/
noncomputable def Ns (r : ℝ) : ℝ := R.η * (4 * R.pi * r ^ 2) / (R.kB * R.ln2)
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

/-- **The temperature of a horizon in cells**, Eq. (T): `I1` for a ring of `L_h` cells, whose lap
time is `L_h t_c`, gives `k_BT = ℏ/(L_h t_c) = E_c/L_h`. -/
theorem T_ring (Lh T : ℝ) (hLh : 0 < Lh) (I1 : R.kB * T = R.ℏ / (Lh * R.tc)) :
    R.kB * T = R.Ec / Lh := by
  reg_facts R
  rw [I1]
  unfold tc Ec
  field_simp

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

/-- The entropy per unit area of the horizon is `η = πk_B ln 2/4ℓ_c²`, Eq. (G). -/
theorem eta_eq : R.η = R.pi * R.kB * R.ln2 / (4 * R.ℓc ^ 2) := by
  reg_facts R
  unfold η Shor Rhor Ahor RL
  field_simp; ring

/-- **The Clausius relation with the register's entropy**, Eq. (clausius): with `I1` for the
Unruh temperature `T_a` of a local Rindler horizon, a ring the horizon gains takes in its
temperature times one bit, `k_BT_a ln 2`, Landauer's energy of a bit; energy crossing the horizon
adds `2πc/(ℏa ln 2)` rings per unit of energy, and with a ring's share `4ℓ_c²/π` the area
`(8ℓ_c²c/(ℏa ln 2)) δQ` (Sec. III.B). -/
theorem clausius (a T δQ : ℝ) (ha : 0 < a) (I1 : R.kB * T = R.ℏ / (R.La a * R.tc)) :
    R.kB * T * R.ln2 = R.ℏ * a * R.ln2 / (2 * R.pi * R.c) ∧
    (δQ / (R.kB * T * R.ln2)) * R.ringShare = (8 * R.ℓc ^ 2 * R.c / (R.ℏ * a * R.ln2)) * δQ := by
  reg_facts R
  have hT := R.T_Unruh a T ha I1
  refine ⟨by rw [hT]; ring, ?_⟩
  rw [hT, R.shares.2]
  field_simp; ring

/-- **Newton's constant from Einstein's equation** (Sec. III.B): the coefficient `2πk_B/(ℏcη)` of
Eq. (einstein) equals `8πG/c⁴` exactly when `G = c³k_B/4ℏη`, which is the hypothesis `hJ`. -/
theorem einstein_coefficient (G η' : ℝ) (hη : 0 < η') :
    2 * R.pi * R.kB / (R.ℏ * R.c * η') = 8 * R.pi * G / R.c ^ 4 ↔
      G = R.c ^ 3 * R.kB / (4 * R.ℏ * η') := by
  reg_facts R
  have hη' := hη.ne'
  constructor
  · intro h
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    rw [eq_div_iff (by positivity)]
    have h2 : (2 * R.pi * R.c) * (R.c ^ 3 * R.kB - G * (4 * R.ℏ * η')) = 0 := by
      linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso
      have : 0 < 2 * R.pi * R.c := by positivity
      linarith
    · linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Jacobson (`hJ`) with the register's entropy density**, Eq. (G):
`G = c³ℓ_c²/(πℏ ln 2) = 4πc³R_Λ²/(ℏL² ln 2)`. -/
theorem G_eq (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ * R.ln2) ∧
    G = 4 * R.pi * R.c ^ 3 * R.RL ^ 2 / (R.ℏ * R.L ^ 2 * R.ln2) := by
  reg_facts R
  rw [hJ, R.eta_eq]
  unfold RL
  constructor <;> (field_simp <;> ring)

/-- The Planck length, defined from `G`. -/
noncomputable def ℓP (G : ℝ) : ℝ := Real.sqrt (R.ℏ * G / R.c ^ 3)

/-- **The cell from Newton's constant**, Eq. (cell): `ℓ_c = √(π ln 2 ℏG/c³) = √(π ln 2) ℓ_P`. -/
theorem cell_from_G (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.ℓc = Real.sqrt (R.pi * R.ln2 * R.ℏ * G / R.c ^ 3) ∧
    R.ℓc = Real.sqrt (R.pi * R.ln2) * R.ℓP G := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hsq : R.pi * R.ln2 * R.ℏ * G / R.c ^ 3 = R.ℓc ^ 2 := by
    rw [hG]; field_simp
  constructor
  · rw [hsq, Real.sqrt_sq R.ℓc_pos.le]
  · unfold ℓP
    rw [← Real.sqrt_mul (by positivity)]
    have h2 : R.pi * R.ln2 * (R.ℏ * G / R.c ^ 3) = R.ℓc ^ 2 := by rw [← hsq]; ring
    rw [h2, Real.sqrt_sq R.ℓc_pos.le]

/-- **The quarter, with the cell fixed by the measured `G`** (Sec. III.C): the horizon's entropy is
`(L²/4) ln 2 = π²R_Λ² ln 2/ℓ_c² = πR_Λ²/ℓ_P² = A_hor/4ℓ_P²`, Bekenstein and Hawking's quarter per
Planck area, and a ring's share of the horizon is `4ℓ_P² ln 2`. -/
theorem entropy_quarter (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.Shor = R.pi ^ 2 * R.RL ^ 2 * R.ln2 / R.ℓc ^ 2 ∧
    R.Shor = R.pi * R.RL ^ 2 / R.ℓP G ^ 2 ∧
    R.Shor = R.Ahor / (4 * R.ℓP G ^ 2) ∧ R.ringShare = 4 * R.ℓP G ^ 2 * R.ln2 := by
  reg_facts R
  have hℓP : R.ℓP G ^ 2 = R.ℓc ^ 2 / (R.pi * R.ln2) := by
    have h := (R.cell_from_G G hJ).2
    have hs : Real.sqrt (R.pi * R.ln2) ^ 2 = R.pi * R.ln2 := Real.sq_sqrt (by positivity)
    have : R.ℓc ^ 2 = R.pi * R.ln2 * R.ℓP G ^ 2 := by rw [h, mul_pow, hs]
    rw [this]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Shor Rhor RL; field_simp; ring
  · rw [hℓP]; unfold Shor Rhor RL; field_simp; ring
  · rw [hℓP]; unfold Shor Rhor Ahor RL; field_simp; ring
  · rw [hℓP, R.shares.2]; field_simp

/-- **The quarter follows for any count** (Sec. III.C).  Whatever entropy per unit area `η'` a
count assigns, Jacobson's relation with the measured `G` makes it `k_B/4ℓ_P²`: the quarter itself
comes from Jacobson's coefficient and the measured `G`, and what the count fixes is the cell
(`cell_from_G`). -/
theorem quarter_any_count (G η' : ℝ) (hG : 0 < G) (hη : 0 < η')
    (hJ' : G = R.c ^ 3 * R.kB / (4 * R.ℏ * η')) :
    η' = R.kB / (4 * R.ℓP G ^ 2) := by
  reg_facts R
  have hℓP : R.ℓP G ^ 2 = R.ℏ * G / R.c ^ 3 := by
    unfold ℓP; rw [Real.sq_sqrt (by positivity)]
  rw [hℓP, hJ']
  field_simp

/-! ### The solution about a mass (Secs. III–IV) -/

/-- **Schwarzschild–de Sitter**, the static solution of Einstein's equation about a mass `M`, with
`Λ` its integration constant: `ds² = −f c²dt² + dr²/f + r²dΩ²` with `f(r) = 1 − 2GM/c²r − Λr²/3`.
Of general relativity it is the one solution the paper uses, taken as already proven
[Kottler 1918]; what the paper takes from general relativity is derived from it below. -/
noncomputable def fSdS (G M Λ r : ℝ) : ℝ := 1 - 2 * G * M / (R.c ^ 2 * r) - Λ * r ^ 2 / 3

/-- the field of the solution, the acceleration toward the mass: `g = (c²/2) df/dr`, the gradient
of the potential `Φ = c²(f − 1)/2` that the time part of the metric carries (the classical
weak-field reading) -/
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
alone (`Λ = 0`; the vacuum's part is the push of `push`) is `a = GM/r²`.  With `I1` for the ring
`L_a` of an observer held on the sphere (`T_Unruh`), the energy inside the sphere, the Komar energy
`Mc²` of the static solution (`komar_mass`), is two Landauer energies `k_BT_a ln 2` for each of its
strings, `Mc² = 2N_s(r) k_BT_a ln 2`, which is Padmanabhan's equipartition, here derived; in cells,
`a/a_c = α/(πn² ln 2)` with `α = M/m_c`, and `2N_s k_BT_a ln 2 = πn² ln 2 ℏa/c`
(`equipartition_in_cells`). -/
theorem newton (G M r a T : ℝ) (hr : 0 < r) (ha0 : 0 < a)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (ha : a = R.gSdS G M 0 r)
    (I1 : R.kB * T = R.ℏ / (R.La a * R.tc)) :
    a = G * M / r ^ 2 ∧ M * R.c ^ 2 = 2 * R.Ns r * (R.kB * T * R.ln2) ∧
    a / R.ac = (M / R.mc) / (R.pi * R.n r ^ 2 * R.ln2) := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hr' : r ≠ 0 := hr.ne'
  have ha' : a = G * M / r ^ 2 := by rw [ha, R.gSdS_mass G M r hr']
  have hT := R.T_Unruh a T ha0 I1
  refine ⟨ha', ?_, ?_⟩
  · rw [hT, (R.bulk_counts r).2, ha', hG]
    unfold n
    field_simp
  · rw [ha', hG]
    unfold ac mc n
    field_simp

/-- **Two Landauer energies per string, in cells** (Eq. (newton)): with `I1` for the Unruh
temperature of an observer held at acceleration `a` on the sphere of radius `r`,
`2N_s(r)k_BT_a ln 2 = πn² ln 2 ℏa/c`. -/
theorem equipartition_in_cells (a T r : ℝ) (ha : 0 < a) (I1 : R.kB * T = R.ℏ / (R.La a * R.tc)) :
    2 * R.Ns r * (R.kB * T * R.ln2) = R.pi * R.n r ^ 2 * R.ln2 * R.ℏ * a / R.c := by
  reg_facts R
  rw [R.T_Unruh a T ha I1, (R.bulk_counts r).2]
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
