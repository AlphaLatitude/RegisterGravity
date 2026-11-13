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

Every relation of *Gravitation from Hilbert-Space Granularity* that follows from the
register's counts, with the physical inputs stated as **named hypotheses** of the theorems that
use them.  A theorem's hypotheses are therefore its ledger: what it takes from outside the
postulates is exactly what is written in its statement, and nothing else.  The `#print axioms` of
every theorem is the logical minimum (`propext`, `Classical.choice`, `Quot.sound`); no physical
axiom is declared.

## The inputs, as they appear below

Beyond the two postulates the paper takes three sources, as Sec. III lists, none of them a number:
thermodynamics (Sec. III), with the first law for the cosmic fluid (Sec. VI) and the principle of
maximum entropy (Secs. IV.C and IV.E); from quantum mechanics, the gates of Sec. IV.A
(`Sources.QM.gates`), which give the bound on the return above the ceiling (`Main.return_bound`),
with the Porter–Thomas distribution of a random state's probabilities, cited there, for its
numbers; and cited mathematics
(`Sources.Geometry`).  In the files every one of them that a theorem takes is
a named hypothesis of the theorems that use it.  The tick of a free string of energy `E` is not
among them: it is Sec. II's definition of energy (`hEs`, `Sources.P1.string_energies`).  The
strings of a sphere, for which the paper's versions up to -6-36 took the symmetry of space from
outside the postulates, are counted ring by ring: with the largest rings drawn as great circles of
the three-sphere, a sphere of areal radius `r` holds, averaged over its position, the number of
rings times `(r/R_Λ)²` (`Bridge.sphere_strings`, by Archimedes' hat-box theorem in four
dimensions, `HatBox.hatBox`).  The files prove this average with no hypothesis beyond the drawing.
The count about any point, averaged over the rotations `x ↦ φ⁻¹(qφ(x))` of the drawing, with `q`
a unit quaternion and `φ` an isometry of the space onto `ℍ`, which carry any point to any other,
is this average, exactly, for every drawing in any four-dimensional space
(`Center.strings_rotation_mean_of`, `Center.sphere_strings_centered_of`, and
`Center.sphere_strings_of_rings_centered` for the rings as closed geodesics of space).  The
postulates fix the rings, not which great circle each one is, and every physical law and quantity
is defined by qubits, so the drawing is no part of the state and no law prefers one rotation of it;
the count about a given body depends only on the strings (Postulate 1's first sentence: the thesis
of the paper), and with every rotation
weighted alike it is defined as this average, a value that does not depend on the drawing (Sec. II).
Nor does it depend on the weighting: a weighting of the rotations that prefers none is the unit
sphere's measure, normalized (`Weighting.eq_toSphere_of_invariant`, the uniqueness of Haar
measure), so it gives the same average.  The paper derives the symmetry of space in Sec. II, and
the files prove it from two clauses of Postulate 2 and the first sentence of Postulate 1, that
every physical law and quantity is defined by qubits (the thesis of the paper): a law is a function
of the register, and space is determined by the rings, since anything else would be a law or a
quantity the strings do not define.  The clauses say that no cell differs from another and that no law depends on the
direction in which a ring passes through a cell, so every law has the rings' symmetry, the same at
every place and in every direction, whatever the drawing (`Symmetry.laws_same`,
`Symmetry.lawAt_same`).  The symmetry enters through Jacobson's step, which takes one entropy
density on every local horizon (`Symmetry.one_density`; `Solution.jacobson_G_from_sources` gives
`hJ` from the step at every point and the count), and through the solution without a mass
(Sec. IV.D).
Without a mass, the strings free and so uncorrelated, the state is the same at every crossing too
(`Solution.state_same`), so by the
thesis the geometry of space is the same at every place and in every direction (`hgeom`,
`Solution.geometry_same`).  By the thesis applied to the space at an instant of an observer at
rest, a ring runs along every geodesic of it, so every geodesic of it closes; by the Killing–Hopf
theorem that space is a space form (`Sources.Geometry.space_form`), and its rings make it a quotient of
the three-sphere (`Space.slice_sphere`).  Its rings close with one length, which leaves only the
three-sphere and its antipodal quotient, and the rings through the observer's cell, drawn in that
space by Sec. II's cell and the last sentence of Postulate 2 with its first clause
(`Sources.P2.rings_drawn`), exclude the latter: the space is the three-sphere itself,
its great circles of a ring's length, and `Λ = 3/R_Λ²` (`Space.sphere_rings`,
`Space.cosmological_constant_of_sources`; every link at once in
`Solution.cosmological_constant_from_sources`).  The files prove that every closed spacelike
geodesic of de Sitter space has the length `2π√(3/Λ)`, and that in its space at an instant such a
geodesic is a great circle (`Geodesics.lean`).  That every largest ring is a closed geodesic of space, made of
its cells as segments of length `ℓ_c`, is the last sentence of Postulate 2.  It is the hypothesis of `Bridge.sphere_strings_of_rings` and
`Bridge.sphere_strings_deSitter`.  It is also part of the admissible drawings (`Symmetry.admissible`) of the
rings of the space at an instant (`Space.SliceIsQubits`) and of the rings through the observer's
cell drawn in that space (`Sources.P2.rings_drawn`).  It matches the register on pairs of cells: two cells that are not opposite lie on exactly one largest
ring, and two points of space that are not antipodal lie on exactly one geodesic
(`TwoCells.lean`).  Four of the five identifications that earlier versions of the paper listed as
readings of the postulates (its Table II) are derived below; the fifth, the even spread of a
string's bit, left the paper with the elastic response.  The step the paper had argued in
words, that the horizon counts every ring, follows from the thesis: a horizon's entropy depends
only on strings, its thermal state being a state of the whole register's strings and of nothing
else (`Bridge.horizonEntropy`); the strings being free between interactions, the entropy adds over
every string (`Entropy.shannon_jointProb`); and every ring also crosses every observer's horizon,
with half its cells inside (`Bridge.horizon_counts_every_ring`).  The section after the inputs
says where.

Thermodynamics:
* `I1` (a horizon is thermal): a horizon whose imaginary-time period is `τ` has `k_B T = ℏ/τ`
  [the Kubo–Martin–Schwinger condition]; the period is `2πc/a` for a horizon of surface gravity
  `a` [Unruh, Gibbons–Hawking]; for the cosmological horizon of the solution without a mass, at
  `r_h`, `a` is its surface gravity `−g(r_h)`, which `DeSitter.surface_gravity_eq` derives to be
  `a_Λ`, and the period is the lap time of the largest ring (`DeSitter.horizon_period`,
  `DeSitter.thermal_lap`).  Hypothesis `I1`.
* Jacobson's step: the heat that crosses a local horizon obeys the Clausius relation, and with the
  Raychaudhuri equation this gives Einstein's equation, with `G = c³k_B/(4ℏη)` for an entropy
  density `η` that is the same on every local horizon (`Einstein.G_of_clausius`).  Hypothesis `hJ`.
  The count fixes `η` in units of the cell, `πk_B ln 2/4ℓ_c²` to leading order in `1/L`
  (`eta_eq`; with the count's `L²/4 − L/2 + 1` rings it is that times `1 − 2/L + 4/L²`,
  `Main.jacobson_G_exact`, `G_exact_bound`), and the symmetry of space makes it the density of
  every local horizon (`Symmetry.one_density`); with them `hJ` follows from the step at every point
  (`Sources.Derived.clausius`, `Main.jacobson_step`), without the conservation law, with Newton's law in the static weak
  field (`Solution.jacobson_G_from_sources`, `Einstein.G_of_clausius`).  The theorems below take
  `hJ` itself, at leading order.
* The first law, `d(ρV) = −p dV`, for a component of the universe; it gives the fluid equation
  and `w = −1` (`Cosmo.lean`).  Hypothesis `first_law`.
* The horizon's thermal state (`Bridge.lean`, `Solution.lean`): each string's qubit is in the
  thermal state of its tick at one inverse temperature `β` (`hthermal`, `Qubit.Tick.state`), and
  the probability of a sense is that state's weight on the outcome that is the sense (`hq`; no
  sign or value of `β` is needed, since the two senses have one energy, `hsense` of `Qubit.Tick`);
  and, the strings being free between interactions (Postulate 1), the horizon's state is the
  product of the strings' own thermal states, hypothesis `hfree`.
* In de Sitter space an observer held at acceleration `a` sees the temperature
  `k_BT = (ℏ/2πc)√(a² + a²_h)` [Deser–Levin], with `a_h` the surface gravity of the horizon, which
  `DeSitter.surface_gravity_eq` derives to be `a_Λ`; a case of the thermality of horizons, it
  enters only the temperature floor (`Galactic.lean`).  Hypothesis `hDL`.

The energy of a string (`Carriers.lean`, `Cosmo.lean`):
* `hGibbs`: the strings' energies are spread at the horizon's temperature and do not change
  (thermodynamics, `Sources.Thermo.energies_thermal`; the paper treats matter that stays put, with
  interactions negligible), so their mean is the mean of the Gibbs distribution at that
  temperature, the thermal energy `k_BT_dS` (`Law.gibbsMean_eq`, `Carriers.string_energy`; within
  one step of it on a ladder of equal steps, `Law.gibbsLadder_within_step`).  What is derived
  around it:
  the two outcomes of the string's qubit are its two senses; the free tick keeps each string of one
  sense up to one and the same factor (`hsense` of `Qubit.Tick`, Sec. II: the shift leaves a string
  of one sense as it is up to its global phase, Postulate 1, and that phase changes alike in either
  sense, Postulate 2) and, the tick being linear, so is every state of the string
  (`Qubit.Tick.phase_unique`): no turn of a relative phase enters, and the energy adds no state;
  the factor is a phase, since a global phase is a factor of modulus one
  (`Qubit.Tick.norm_scalar`), and any factor `e^{−iθ}` is a tick's (`Qubit.Tick.ofPhase`).
* `hEs`: the strings' energies by Sec. II's definition of energy, the factor `e^{−iEt_c/ℏ}` on
  every state of a string of energy `E` (`Sources.P1.string_energies`), so the tick of a string
  that holds the mean energy is `e^{−i/L}` (`Cosmo.string_tick`).  A string's heat, the horizon's
  temperature times its
  one bit, is `ln 2` of the mean energy and is the vacuum's energy per string, the Misner–Sharp energy `E_Λ`, one Landauer
  energy `k_BT ln 2` per string (`Cosmo.komar_misner_sharp`, `Cosmo.vacuum_per_string`,
  `Cosmo.string_split`); the rest, `1 − ln 2`, is matter.  The energy inside the horizon is the
  strings' and nothing else's (`hin`, `Sources.P1.energy_inside_strings`, Postulate 1's first
  sentence as `hgeom` and `hslice` apply it to the geometry and to space), so the vacuum's share of
  it is `ln 2` (`Cosmo.vacuum_share`).
* The galactic law (Sec. IV.C, `Carriers.lean`): the body's energy is held by the strings that
  carry its information (`hcar`, Postulate 1's first sentence for a body's energy), the fraction
  `b` of the sphere's strings, each at the share `κT` of equipartition (`hκ`, `hκN`,
  `Sources.Thermo.equipartition`), so `a = g_N/b` (`Carriers.share_acceleration`); the body's
  energy per string of the sphere, in units of the matter a string holds on average, is `f = g_N/a₀` with
  `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)` (`Carriers.fill_fraction`); a string that carries the body's
  information is one of its qubits, so the share enters as the amplitude `√f` (`hb`,
  `Sources.P1.carriers_by_amplitude`), and the threshold of a string, a positive quantity
  with one qubit as its only scale, is exponential with mean one by maximum entropy (`hME`,
  `Sources.Thermo.max_entropy_threshold`), so the carriers are the fraction `1 − e^{−√f}` and
  `a = g_N/(1 − e^{−√(g_N/a₀)})` (`Carriers.law`, `Carriers.radial_acceleration_relation`).

## The readings of earlier versions, derived

Versions of the paper up to v11.1.18 listed five identifications as readings of the postulates
(its Table II), and the files carried them as definitions.  Four are derived now; the fifth, the
even spread of a string's bit inside a sphere, left the paper and the files with the elastic
response it served:
* The count identified with the horizon's area (`Ahor`, `ringShare`): every largest ring has half
  its cells inside any observer's horizon, counting a cell on it as half
  (`Horizon.Positions.horizon_weight_ring`, `Bridge.horizon_entropy_count`), so every ring crosses
  the horizon (`Horizon.Positions.crossesHorizon`); the horizon counts every one of the register's
  `R` rings, since its thermal state is a state of the strings alone, the thesis of the paper, and
  so of every string (`Bridge.horizonEntropy`, `Bridge.horizon_counts_every_ring`);
  `A_hor/R = 4ℓ_c²/π` (`shares`) is the solution's area over that count, a quotient.
* One string on each ring (`Shor`; the type of the horizon's state in `Bridge.horizon_entropy`, one
  sense for each ring): from the paper's definition of a cell, which
  holds one bit of each ring through it, so the bits on a ring's cells form one string of
  Postulate 1.  A string is one qubit, and its two outcomes are the two senses (Sec. II).  The two
  senses have the same energy, since the tick's phase changes alike in either sense, no law
  depending on the ring's direction (Postulate 2, `hsense` of `Qubit.Tick`), so the thermal state
  weights them equally (`Qubit.Tick.prob_state`), and two senses weighted equally hold one bit
  (`one_bit`), all that a qubit holds; on the string's own thermal state, half the identity since
  every state of a free string has one energy, the bit is `Main.string_one_bit`.
  `Bridge.horizon_entropy` derives from these
  the entropy of the strings, `card Loop · ln 2`, which is the definition `Shor` to relative order
  `2/L`.  The paper's Sec. II adds the bit's history, and its Sec. IV.E the mean energy of a string,
  one thermal energy of the horizon (`Carriers.string_energy`).  Interactions change the strings' states,
  not their number, and enter the count only as corrections.
* The strings of a sphere that is not a horizon (`Ns`): counted ring by ring.  A sphere holds one
  string for each largest ring that crosses it, and without a mass the largest rings are great
  circles of the three-sphere of radius `R_Λ` (Sec. IV.D).  A given great circle crosses a sphere
  of areal radius `r` from the fraction `(r/R_Λ)²` of the sphere's positions
  (`Crossing.Drawing.crossing_fraction`, Archimedes' hat-box theorem in four dimensions), so,
  averaged over its position, the sphere holds the number of rings times `(r/R_Λ)²`
  (`Crossing.Drawing.meanStrings_eq`): `(L²/4)(r/R_Λ)²` to relative order `2/L`, on average one
  string for each ring's share of its area, at every radius (`Bridge.sphere_strings`).  This is the
  area law of a screen, on average over the sphere's position.  On every local horizon Sec. III
  takes the same density, one string for each ring's share of area, from the symmetry of space
  (Sec. II), which makes that share the same at every place and in every direction
  (`Symmetry.one_density`); it needs no solution of Einstein's equations.  `bulk_counts` and
  `ratio_of_areas` give its forms.
* The pairing of a joint measurement (`Capacity.ceiling_in_step`): a joint measurement is one
  measurement, so it reads one position, the same on every string of the qubits it measures,
  which the shift keeps in step (Postulate 1); the joint outcome a position shows is the strings'
  bits there (`Capacity.jointOutcome`), no function chosen.

## One bit per ring

The entropy of the horizon is one bit, `k_B ln 2`, for each largest ring (Sec. II, Eq. (S));
`Bridge.horizon_entropy` derives it.

## The solution of Einstein's equation

Einstein's equations enter through Jacobson's step (`hJ`), and `G_eq` gives their coefficient.  The
Schwarzschild–de Sitter solution about a mass [F. Kottler, Ann. Phys. (Leipzig) 361, 401 (1918)]
is derived from the vacuum equations (`Schwarzschild.static_vacuum`, `Main.schwarzschild_deSitter`);
here its metric function is the definition `fSdS`, and its field is read in the classical
weak-field way, `g = (c²/2) df/dr` (`gSdS`); the field the mass adds to the solution without it, at
the same `Λ`, is its pull (`pull`), `GM/r²` at every `Λ`, and the rest is the push.  The files
derive from it what the chain uses: Newton's law and Padmanabhan's equipartition for the pull
(`newton`), the Komar energy the mass adds (`komar_mass`), the de Sitter radius `Λ = 3/R_Λ²` (`deSitter`), the proper distance `πR_Λ/2` to the
horizon (`proper_distance`), the outer horizon drawn in by `GM/c²` (`sds_outer_horizon`), the
area deficit (`area_deficit`), the push (`push`), the zero-gravity radius
(`zero_gravity`), and the Misner–Sharp and Komar energies of the horizon (`komar_misner_sharp`).
The closed geodesics of de Sitter space are derived (`Geodesics.lean`), as Sec. IV.D derives
the great circles of the space at an instant; the Deser–Levin temperature is a hypothesis (`hDL`), and the limit up to
which the solution has a horizon is not derived (`Numerics.cosmic_mass_beyond_nariai` certifies its
number).  The constant `Λ` of the vacuum equations is fixed by the horizon of the solution without
a mass having the radius of the largest ring, `R_Λ` (hypothesis `hdS` of the theorems that use `Λ`).
Sec. IV.D derives that from the rings: the solution is de Sitter space, all of whose closed
geodesics have the length `2π√(3/Λ)`, a largest ring being one of them
(`Space.cosmological_constant_of_sources`; `Solution.chain_from_sources` derives `hdS`).
The register's rings are the largest rings, of `L` cells; every one crosses an observer's horizon
with half its cells inside (`Horizon.Positions.horizon_weight_ring`), and the horizon's own
entropy is the register's count, every ring counted (`Shor`, `Bridge.horizon_entropy_count`).  With
a mass inside, the great circles of its horizons, of `L_M = L − 2α/ln 2` cells at the cosmological
horizon and `4πGM/c²ℓ_c` at a black hole's, are circles shorter than a largest ring, outside the
count of Postulate 2; the area law (`Ns`), one bit per
ring's share of area, gives the horizon `L_M²/4` bits, the number Eqs. (counts) and (S) would give
with `L_M` in place of `L` (`Galactic.massive_horizon_count`); the loss is
`Galactic.entropy_removed`.  The perihelion and deflection
formulas of Sec. IV.B are also classical results, evaluated in `Numerics.solar_tests`.

The register's own quantities are definitions: the units of the cell, the radius of the largest
ring `R_Λ = Lℓ_c/2π` (Eq. (ident); the horizon's radius by Sec. IV.D), and the counts `L²/2` and
`L²/4`, those of `Horizon.counts` to leading order in `1/L` (`Bridge.counts_exact` gives the exact
counts of a `Horizon L` in these terms).
-/

open Real

namespace Register

/-- The register's constants: the speed of light, `ℏ`, `k_B`, the cell and the length `L` of the
largest ring (as a real number), positive reals whose values are never used here.  `π` and `ln 2`
are Mathlib's (`Reg.pi`, `Reg.ln2`). -/
structure Reg where
  c : ℝ
  ℏ : ℝ
  kB : ℝ
  ℓc : ℝ
  L : ℝ
  c_pos : 0 < c
  ℏ_pos : 0 < ℏ
  kB_pos : 0 < kB
  ℓc_pos : 0 < ℓc
  L_pos : 0 < L

namespace Reg

variable (R : Reg)

/-- `π`, Mathlib's `Real.pi`, written `R.pi` in the chain -/
noncomputable def pi (_R : Reg) : ℝ := Real.pi

/-- `ln 2`, Mathlib's `Real.log 2`, written `R.ln2` in the chain -/
noncomputable def ln2 (_R : Reg) : ℝ := Real.log 2

theorem pi_def : R.pi = Real.pi := rfl

theorem ln2_def : R.ln2 = Real.log 2 := rfl

theorem pi_pos : 0 < R.pi := Real.pi_pos

theorem ln2_pos : 0 < R.ln2 := Real.log_pos (by norm_num)

/-- Introduce the positivity and non-vanishing facts of the register's constants into the
local context, where `positivity` and `field_simp` find them. -/
macro "reg_facts " R:term : tactic => `(tactic| (
  have := ($R).c_pos; have := ($R).ℏ_pos; have := ($R).kB_pos
  have := ($R).ℓc_pos; have := ($R).L_pos; have := ($R).pi_pos; have := ($R).ln2_pos
  have := ($R).c_pos.ne'; have := ($R).ℏ_pos.ne'; have := ($R).kB_pos.ne'
  have := ($R).ℓc_pos.ne'; have := ($R).L_pos.ne'; have := ($R).pi_pos.ne'
  have := ($R).ln2_pos.ne'))

/-- **One bit** (Sec. II, the entropy): two senses weighted equally hold the entropy `ln 2`, and no
weighting of two senses holds more: the binary entropy `−p ln p − (1 − p) ln(1 − p)` is `ln 2` at
`p = 1/2` and at most `ln 2` for every `p` (Mathlib's `Real.binEntropy`). -/
theorem one_bit : Real.binEntropy (1 / 2) = Real.log 2 ∧ ∀ p, Real.binEntropy p ≤ Real.log 2 :=
  ⟨by rw [one_div]; exact Real.binEntropy_two_inv, fun _ => Real.binEntropy_le_log_two⟩

/-! ### Units of the cell (Sec. II) -/

/-- the tick, `t_c = ℓ_c/c` -/
noncomputable def tc : ℝ := R.ℓc / R.c
/-- the cell's unit of mass, `m_c = ℏ/(cℓ_c)` -/
noncomputable def mc : ℝ := R.ℏ / (R.c * R.ℓc)
/-- the cell's unit of energy, `E_c = ℏc/ℓ_c` -/
noncomputable def Ec : ℝ := R.ℏ * R.c / R.ℓc
/-- the cell's unit of acceleration, `a_c = c²/ℓ_c` -/
noncomputable def ac : ℝ := R.c ^ 2 / R.ℓc
/-- the cell's unit of energy density, `ρ_c = E_c/ℓ_c³` -/
noncomputable def ρc : ℝ := R.Ec / R.ℓc ^ 3

/-! ### The largest ring, the horizon's area, and the count (Sec. II) -/

/-- **The radius of the largest ring**, Eq. (ident): `R_Λ = Lℓ_c/2π`, the radius of a circle of
length `Lℓ_c`; Sec. IV.D derives that each largest ring is such a circle and that the horizon has
the same radius (`Space.cosmological_constant_of_sources`, `Main.deSitter_horizon`). -/
noncomputable def RL : ℝ := R.L * R.ℓc / (2 * R.pi)
/-- the area of a sphere of radius `R_Λ`, the horizon's by Sec. IV.D; every one of the register's
rings has half its cells inside it (`Bridge.horizon_entropy_count`), the paper counts every ring on
it, and `ringShare` is its area over that count -/
noncomputable def Ahor : ℝ := 4 * R.pi * R.RL ^ 2
/-- the cells of the register, `L²/2` to leading order in `1/L` (`Bridge.counts_exact`); an
observer's horizon lies `L/4` steps from his cell (Sec. IV.D) -/
noncomputable def Chor : ℝ := R.L ^ 2 / 2
/-- the largest rings of the register, `L²/4` to leading order in `1/L` (`Bridge.counts_exact`),
each crossing every observer's horizon with half its cells inside (Sec. IV.C; Secs. II and IV.D
use it) -/
noncomputable def Rhor : ℝ := R.L ^ 2 / 4
/-- **The entropy**, Eq. (S), in units of `k_B`: one bit, `ln 2`, for each largest ring.  Every
ring carries exactly one string, since a cell holds one bit of each ring through it (the horizon's
state in `Bridge.horizon_entropy` is one sense for each ring); a string is one qubit (Postulate 1); its two senses, its two outcomes, have the same energy
(`hsense` of `Qubit.Tick`), so the thermal state weights them equally (`Qubit.Tick.prob_state`), and the string holds one bit (`one_bit`;
on its own thermal state, half the identity, `Main.string_one_bit`); and every
ring has half its cells inside any observer's horizon (`Bridge.horizon_entropy_count`); the horizon
counts every ring, since its thermal state is a state of the strings alone, the thesis of the paper
(`Bridge.horizonEntropy`, `Bridge.horizon_counts_every_ring`).
`Bridge.horizon_entropy`
derives the entropy of the strings,
which is this definition to relative order `2/L`.  Interactions enter the count only as
corrections. -/
noncomputable def Shor : ℝ := R.Rhor * R.ln2
/-- the horizon's area over the register's cells, an auxiliary the paper does not use -/
noncomputable def cellShare : ℝ := R.Ahor / R.Chor
/-- a ring's share of an observer's horizon, its area over the `L²/4` rings that cross it
(`Bridge.horizon_entropy_count`): a quotient of the solution's area by the register's count -/
noncomputable def ringShare : ℝ := R.Ahor / R.Rhor
/-- the entropy per unit area of the horizon, `η = k_B R ln 2/A_hor` -/
noncomputable def η : ℝ := R.kB * R.Shor / R.Ahor

lemma RL_pos : 0 < R.RL := by reg_facts R; unfold RL; positivity
lemma Ahor_pos : 0 < R.Ahor := by unfold Ahor; have := R.RL_pos; reg_facts R; positivity

/-- The horizon's area in cells, `4πR_Λ² = L²ℓ_c²/π` (Sec. II); the count uses only this number. -/
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

/-- To leading order in `1/L`, a ring's share of the horizon's area is `4ℓ_c²/π` (Sec. II); the
auxiliary `cellShare`, which the paper does not use, is `2ℓ_c²/π`. -/
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
/-- **The strings of a sphere that is not a horizon** (Sec. II, "Counting in the bulk"): its
entropy over `k_B ln 2`, one bit per string, at the horizon's entropy per unit area `η`
(`eta_eq`), `S = ηA`.  That a sphere of areal radius `r` holds this many strings,
`(L²/4)(r/R_Λ)²`, averaged over its position, is derived ring by ring in `Bridge.sphere_strings`,
to relative order `2/L`; this is the area law of a screen, and Sec. III takes the same density on
every local horizon.  The register's own counts, the same at every distance from the body (`L` cells, with
`L/2` rings through each), do not count a sphere's strings (Sec. II, "Counting in the bulk"); the
great circles that the largest rings draw in space do. -/
noncomputable def Ns (r : ℝ) : ℝ := R.η * (4 * R.pi * r ^ 2) / (R.kB * R.ln2)

/-- Eq. (N): `N_s(r) = π²n²`; `L` cancels. -/
theorem bulk_counts (r : ℝ) : R.Ns r = R.pi ^ 2 * R.n r ^ 2 := by
  reg_facts R
  unfold Ns η Shor Rhor Ahor RL n
  field_simp
  ring

/-- **The ratio of areas**: the number of strings held by a sphere of radius `r` is the horizon's
number, `L²/4`, times the ratio of the sphere's area to the horizon's, `(r/R_Λ)²`, which is what
the count ring by ring gives on average over the sphere's position (`Bridge.sphere_strings`); it
is one string for each ring's share of the sphere's area. -/
theorem ratio_of_areas (r : ℝ) :
    R.Ns r = R.Rhor * (r / R.RL) ^ 2 ∧ R.Ns r = 4 * R.pi * r ^ 2 / R.ringShare := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  refine ⟨?_, ?_⟩
  · unfold Ns η Shor Rhor Ahor
    field_simp
  · unfold Ns η Shor ringShare Rhor Ahor
    field_simp

/-- **The observer's own rings on a sphere: the arithmetic of the bound** (Sec. II, after
Eq. (N)).  The count of Eq. (N) is the average over the drawing's rotations, in which every ring
has the weight `(r/R_Λ)²` (`Bridge.sphere_strings`, `Main.sphere_strings`).  An observer's count,
with the `L/2` rings through his cell taken where the drawing places them and the other rings
turned, exceeds the average by at most `(L/2)(1 − r²/R_Λ²)` (`Main.observer_count`).  This theorem
proves the arithmetic: that number is the fraction `(R_Λℓ_c/πr²)(1 − r²/R_Λ²)` of `N_s(r)`, at
most `R_Λℓ_c/πr²`, and it is zero at the horizon, `r = R_Λ`. -/
theorem observer_rings (r : ℝ) (hr : 0 < r) :
    R.L / 2 * (1 - r ^ 2 / R.RL ^ 2) / R.Ns r =
      R.RL * R.ℓc / (R.pi * r ^ 2) * (1 - r ^ 2 / R.RL ^ 2) ∧
    R.L / 2 * (1 - r ^ 2 / R.RL ^ 2) / R.Ns r ≤ R.RL * R.ℓc / (R.pi * r ^ 2) ∧
    R.L / 2 * (1 - R.RL ^ 2 / R.RL ^ 2) = 0 := by
  reg_facts R
  have hRL := R.RL_pos
  have e : R.L / 2 * (1 - r ^ 2 / R.RL ^ 2) / R.Ns r =
      R.RL * R.ℓc / (R.pi * r ^ 2) * (1 - r ^ 2 / R.RL ^ 2) := by
    rw [bulk_counts]
    unfold n RL
    field_simp
  refine ⟨e, ?_, by rw [div_self (pow_ne_zero 2 hRL.ne'), sub_self, mul_zero]⟩
  rw [e]
  have hpos : 0 < R.RL * R.ℓc / (R.pi * r ^ 2) := by positivity
  have hle : 1 - r ^ 2 / R.RL ^ 2 ≤ 1 := by
    have : 0 ≤ r ^ 2 / R.RL ^ 2 := by positivity
    linarith
  calc R.RL * R.ℓc / (R.pi * r ^ 2) * (1 - r ^ 2 / R.RL ^ 2)
      ≤ R.RL * R.ℓc / (R.pi * r ^ 2) * 1 := mul_le_mul_of_nonneg_left hle hpos.le
    _ = R.RL * R.ℓc / (R.pi * r ^ 2) := mul_one _

/-! ### The temperature of a horizon in cells (Sec. III.A) -/

/-- **The temperature of a horizon in cells**, Eq. (T): `I1` for a horizon whose period is `L_h`
ticks, `τ = L_h t_c`, gives `k_BT = ℏ/(L_h t_c) = E_c/L_h`. -/
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

/-- the thermal period `2πc/a` of the horizon `c²/a` behind an observer held at acceleration `a`,
in ticks: `L_a = 2πc²/(aℓ_c)`; it equals `L`, a largest ring's length and the lap of the largest
ring, only at `a = a_Λ` (`DeSitter.horizon_period`) -/
noncomputable def La (a : ℝ) : ℝ := 2 * R.pi * R.c ^ 2 / (a * R.ℓc)

theorem La_lap (a : ℝ) (ha : 0 < a) : R.La a * R.tc = 2 * R.pi * R.c / a := by
  reg_facts R
  unfold La tc
  field_simp

/-- **I1 applied to the period `L_a t_c = 2πc/a`**: Unruh's temperature, `k_B T_a = ℏa/2πc`. -/
theorem T_Unruh (a T : ℝ) (ha : 0 < a) (I1 : R.kB * T = R.ℏ / (R.La a * R.tc)) :
    R.kB * T = R.ℏ * a / (2 * R.pi * R.c) := by
  reg_facts R
  rw [I1, R.La_lap a ha]
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

/-- **Jacobson (`hJ`) with the register's entropy density**, Eq. (G):
`G = c³ℓ_c²/(πℏ ln 2) = 4πc³R_Λ²/(ℏL² ln 2)`. -/
theorem G_eq (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ * R.ln2) ∧
    G = 4 * R.pi * R.c ^ 3 * R.RL ^ 2 / (R.ℏ * R.L ^ 2 * R.ln2) := by
  reg_facts R
  rw [hJ, R.eta_eq]
  unfold RL
  constructor <;> (field_simp <;> ring)

/-- The factor of the count, `1 − 2/L + 4/L² = ((L − 1)² + 3)/L²`, is positive. -/
theorem count_factor_pos : 0 < 1 - 2 / R.L + 4 / R.L ^ 2 := by
  have hL := R.L_pos
  have e : 1 - 2 / R.L + 4 / R.L ^ 2 = ((R.L - 1) ^ 2 + 3) / R.L ^ 2 := by
    field_simp; ring
  rw [e]; positivity

/-- **`G` with the exact count** (Sec. III.C).  The horizon's entropy over its area with the count's
`L²/4 − L/2 + 1` rings is `η(1 − 2/L + 4/L²)`, `η` the density with `L²/4` (`Bridge.counts_exact`);
the `G` of Jacobson's step at that density is the leading-order `G` of Eq. (G) over
`1 − 2/L + 4/L²`, and for `L ≥ 4` it exceeds it by at most `8/3L` of it. -/
theorem G_exact_bound (G : ℝ) (hL : 4 ≤ R.L)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * (R.η * (1 - 2 / R.L + 4 / R.L ^ 2)))) :
    G * (1 - 2 / R.L + 4 / R.L ^ 2) = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) ∧
    0 ≤ G - R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) ∧
    G - R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)
      ≤ 8 / (3 * R.L) * (R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) := by
  reg_facts R
  have hη : 0 < R.η := by rw [R.eta_eq]; positivity
  set G₀ := R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) with hG₀
  have hG₀pos : 0 < G₀ := by rw [hG₀]; positivity
  -- with `D = L² − 2L + 4 > 0`, `G = G₀L²/D`
  have hD : 0 < R.L ^ 2 - 2 * R.L + 4 := by nlinarith [sq_nonneg (R.L - 1)]
  have hf : 1 - 2 / R.L + 4 / R.L ^ 2 = (R.L ^ 2 - 2 * R.L + 4) / R.L ^ 2 := by
    field_simp
  have hG : G = G₀ * R.L ^ 2 / (R.L ^ 2 - 2 * R.L + 4) := by
    rw [hJ, hf, hG₀]
    field_simp
  have hD0 : R.L ^ 2 - 2 * R.L + 4 ≠ 0 := hD.ne'
  have hL0 : R.L ^ 2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [hG, hf]
    calc G₀ * R.L ^ 2 / (R.L ^ 2 - 2 * R.L + 4) * ((R.L ^ 2 - 2 * R.L + 4) / R.L ^ 2)
        = G₀ * (R.L ^ 2 / R.L ^ 2) * ((R.L ^ 2 - 2 * R.L + 4) / (R.L ^ 2 - 2 * R.L + 4)) := by
          ring
      _ = G₀ := by rw [div_self hL0, div_self hD0]; ring
  · -- `G − G₀ = G₀(2L − 4)/D ≥ 0`
    rw [hG, sub_nonneg, le_div_iff₀ hD]
    nlinarith
  · -- `(2L − 4)/D ≤ 8/3L`, since `3L(2L − 4) ≤ 8D`
    rw [hG]
    have e : G₀ * R.L ^ 2 / (R.L ^ 2 - 2 * R.L + 4) - G₀
        = G₀ * (2 * R.L - 4) / (R.L ^ 2 - 2 * R.L + 4) := by
      rw [eq_div_iff hD0, sub_mul, div_mul_cancel₀ _ hD0]; ring
    rw [e, div_le_iff₀ hD]
    have h3 : 3 * R.L * (2 * R.L - 4) ≤ 8 * (R.L ^ 2 - 2 * R.L + 4) := by nlinarith
    have h4 : G₀ * (2 * R.L - 4) * (3 * R.L) ≤ G₀ * (8 * (R.L ^ 2 - 2 * R.L + 4)) := by
      have := mul_le_mul_of_nonneg_left h3 hG₀pos.le
      linarith
    rw [show 8 / (3 * R.L) * G₀ * (R.L ^ 2 - 2 * R.L + 4)
        = G₀ * (8 * (R.L ^ 2 - 2 * R.L + 4)) / (3 * R.L) by ring]
    rw [le_div_iff₀ (by positivity)]
    linarith

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

/-- **Schwarzschild–de Sitter**, the static solution of the vacuum equations with `Λ` about a mass
`M`: `ds² = −f c²dt² + dr²/f + r²dΩ²` with `f(r) = 1 − 2GM/c²r − Λr²/3` [F. Kottler, Ann. Phys.
(Leipzig) **361**, 401 (1918)].  About a body at rest, alone, the static, spherically symmetric
solution of the vacuum equations has this metric function (`Main.schwarzschild_deSitter`, from
`Schwarzschild.static_vacuum`), the static, spherically symmetric case of Birkhoff's theorem with
`Λ` [J. Schleich and D. M. Witt, J. Math. Phys. **51**, 112502 (2010), Thm. 1, a reference of the
files; the paper cites Kottler and Wald]; with no mass it is de
Sitter space about an observer at rest.  What the chain uses of it is derived from it below. -/
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

/-- **The pull of a mass**: the field that the mass `M` adds to the solution without it, at the same
constant `Λ`, `g(M) − g(0)`.  It is `GM/r²` at every `Λ` (`pull_eq`), Newton's field of the mass;
the rest of the field, `g(0) = −Λc²r/3`, is the push of the ring's content (`Reg.push`). -/
noncomputable def pull (G M Λ r : ℝ) : ℝ := R.gSdS G M Λ r - R.gSdS G 0 Λ r

/-- The pull of a mass is `GM/r²`, at every `Λ`. -/
theorem pull_eq (G M Λ r : ℝ) (hr : r ≠ 0) : R.pull G M Λ r = G * M / r ^ 2 := by
  unfold pull
  rw [R.gSdS_eq G M Λ r hr, R.gSdS_eq G 0 Λ r hr]
  ring

/-- **The de Sitter horizon.**  Without a mass the solution has its horizon where `f = 0`, and the
register's horizon at `R_Λ` is that horizon exactly when `Λ = 3/R_Λ²`.  `Λ` is the constant of the
vacuum equations, and the rings fix it at `3/R_Λ²` (Sec. IV.D, `Space.cosmological_constant_of_sources`),
so the horizon is at `R_Λ`. -/
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

/-- **The horizon of the solution without a mass is at `R_Λ`** (Sec. IV.D): with `f` vanishing at
`R_Λ` (`hdS`, which is `Λ = 3/R_Λ²`, `deSitter`) the de Sitter solution's `f = 1 − Λr²/3` vanishes
at one positive radius, so a radius `r > 0` where `f` vanishes is `R_Λ`; the horizon's area is then
`4πR_Λ²`, the definition `Ahor`. -/
theorem horizon_radius_eq (G Λ r : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) (hr : 0 < r)
    (hf : R.fSdS G 0 Λ r = 0) : r = R.RL := by
  reg_facts R
  have hRL := R.RL_pos
  have hRL0 : R.RL ≠ 0 := hRL.ne'
  have hΛ := (R.deSitter G Λ).1 hdS
  have h2 : r ^ 2 = R.RL ^ 2 := by
    unfold fSdS at hf
    simp only [mul_zero, zero_div, sub_zero] at hf
    rw [hΛ] at hf
    field_simp at hf
    linarith
  exact (pow_left_inj₀ hr.le hRL.le (by norm_num)).1 h2

/-- **Newton's law and equipartition**, Eq. (newton).  The pull of the mass, the field it adds to
the solution at its constant `Λ` (`pull`; the rest of the field is the push of `push`), is
`a = GM/r²` at every `Λ`.  With `I1` for the period `L_a`, in ticks, of the horizon of an observer
held at the acceleration `a` (`T_Unruh`), the energy the mass adds inside the sphere, the Komar
energy `Mc²` (`komar_mass`), is two Landauer energies `k_BT_a ln 2` for each of its strings,
`Mc² = 2N_s(r) k_BT_a ln 2`, which is Padmanabhan's equipartition, a definition evaluated here on
the derived solution; in cells,
`a/a_c = α/(πn² ln 2)` with `α = M/m_c`, and `2N_s k_BT_a ln 2 = πn² ln 2 ℏa/c`
(`equipartition_in_cells`). -/
theorem newton (G M Λ r a T : ℝ) (hr : 0 < r) (ha0 : 0 < a)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (ha : a = R.pull G M Λ r)
    (I1 : R.kB * T = R.ℏ / (R.La a * R.tc)) :
    a = G * M / r ^ 2 ∧ M * R.c ^ 2 = 2 * R.Ns r * (R.kB * T * R.ln2) ∧
    a / R.ac = (M / R.mc) / (R.pi * R.n r ^ 2 * R.ln2) := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hr' : r ≠ 0 := hr.ne'
  have ha' : a = G * M / r ^ 2 := by rw [ha, R.pull_eq G M Λ r hr']
  have hT := R.T_Unruh a T ha0 I1
  refine ⟨ha', ?_, ?_⟩
  · rw [hT, R.bulk_counts r, ha', hG]
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
  rw [R.T_Unruh a T ha I1, R.bulk_counts r]
  field_simp

/-- **Without cells there is no count, and `η` stays free** (Sec. III.C, first remark): Jacobson's
coefficient ties `G` and the entropy density inversely, `G · η = c³k_B/4ℏ`, so a value of `η` is
a value of `G`, and it is the count, one bit per ring's share of area, that supplies the value. -/
theorem G_mul_eta (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G * R.η = R.c ^ 3 * R.kB / (4 * R.ℏ) := by
  reg_facts R
  have hη : R.η ≠ 0 := by rw [R.eta_eq]; positivity
  rw [hJ]; field_simp

end Reg

end Register
