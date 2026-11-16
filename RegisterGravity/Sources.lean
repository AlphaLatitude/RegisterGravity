import RegisterGravity.Solution
import RegisterGravity.Space
import RegisterGravity.Schwarzschild
import RegisterGravity.Motion
import RegisterGravity.MassHorizon
import RegisterGravity.Weighting
import RegisterGravity.Coding
import RegisterGravity.Matter

/-!
# The sources: every premise of the paper's results, named by its source (Secs. II–VI)

The paper derives its results from four sources: the two postulates with the definitions of
Sec. II, and the three that Sec. III lists beyond them.  The files take no premise beyond them:
the namespace `Open`, for a premise that no source states, holds none.  The rule of
Sec. IV.C by which a string carries a body's information, which the files up to v18-68 took as a
premise of Postulate 1 (`P1.carriers_by_amplitude`), with the distribution of a string's
threshold as a premise of thermodynamics (`Thermo.max_entropy_threshold`), is derived
(`Main.carriers_exact`).  Its inputs are two applications of Postulate 1 that Sec. IV.C makes,
the spread of the strings' energies, and mathematics that the files prove (`Carriers.lean`).  The
applications are the share's equal parts, one per tick for each of the string's `L` bits, which
add as amplitudes (`P1.share_in_parts`), and the rule that a string carries the body's
information when its global phase holds against the share, with the turn of a free tick that
Sec. II's definition of energy gives, whatever that turn is (`P1.carriers_hold_phase`).  The
spread is thermodynamics (`Thermo.energies_thermal`).  The amplitude of the body's share ties
the amplitude `h` to the body where the law takes the rule.  Up to v18-69 the files took
`h = √(E/u)`, in units of the matter `u` that a string holds on average, as one premise,
`P1.share_amplitude`.  `Main.share_amplitude` derives the exact amplitude for a share that one
string can hold, `E ≤ u`, from the count of bits (`Derived.share_amplitude_exact`).  Mass energy
is found in the bits of the cells where a measurement on the manifold finds it, and it adds over
cells (`P1.mass_in_bits`).  No cell differs from another, so the bit of each cell holds the same
(`P2.cells_hold_alike`).  A string holds its matter `u` on all its bits
(`P1.string_matter_in_bits`).  The share fills whole bits of the string, and `h` is their
amplitude (`P1.share_bits`).  Each bit is one possible outcome among the ring's
(`P1.ring_bits_alike`), so `h²` is the fraction of the string's bits that the share fills, less
than one bit below `E/u`.  The paper's `h = √(E/u)` is the leading order of that amplitude in
`1/L`, a named step (`Approx.share_amplitude`) whose error `Main.share_leading_order` bounds,
and `Main.law_whole_bits` bounds what the step changes in the law.
For a larger share, `E > u`, no count of bits names a set of the string's cells.  The paper
defines `h` on the same scale there, `h = √(E/u)`, and the files take that definition as a
condition (`Condition.same_scale`): they do not derive it, and no sentence of the postulates
states it.  The
paper's Eq. (b) is the leading order of the derived rule in `1/L`, a named step
(`Approx.carriers_leading`) whose error `Main.carriers_leading_order` bounds.  The three sources beyond the postulates are thermodynamics;
quantum mechanics, which gives the gates of Sec. IV.A (namespace `QM`): a circuit acts on what
the register holds as on any state, so the return above the ceiling is at most the probability
that the random state gives the outcomes that remain (`Main.return_bound`), and the
Porter–Thomas distribution of a random state's probabilities, cited there, gives that
probability its numbers (`Numerics.porter_thomas_bound`); and cited mathematics.  What the
postulates and Sec. II's definitions say in the words of quantum mechanics is carried with them:
that a state is a linear combination of outcomes (Postulate 1; `Qubit.Vec`, `Qubit.Op`), and the
energy of a state, by which the tick of a free string of energy `E` is the factor `e^{−iEt_c/ℏ}`
(Sec. II's definition of energy; `P1.string_energies`, Sec. IV.E).  What the paper takes from
general relativity is no law but that mathematics: Lorentzian geometry on the manifold that
Postulate 2 names and Riemannian geometry for the space at an instant (namespace `Geometry`), with
two definitions of that geometry, the Misner–Sharp
and Komar energies (`Reg.EMS`, `Reg.EK`), and three of its results on the derived solution used only
as numbers (the perihelion and deflection formulas and the limit up to which the solution has a
horizon, `Numerics.lean`).  The space at an instant has three dimensions, which the paper takes as
observed (Sec. IV.D, where it cites a companion preprint for the number); the dimension is built
into `Space.SpaceForm` and into the Killing–Hopf premise.  Einstein's equations are
derived from the
postulates with thermodynamics, by Jacobson's argument (Sec. III): the count gives every horizon
one bit per ring (`Bridge.horizon_entropy`), and Postulate 2
makes that entropy density the same on every horizon (`Symmetry.one_density`); a horizon is thermal
at the temperature of its period, the Unruh temperature at the acceleration `a` (thermodynamics,
`Thermo.horizon_thermal`); the energy that crosses every local horizon through a point, the
boost-energy flux of matter, is heat, `δQ = T dS` (thermodynamics, `Thermo.local_clausius`); the
horizon's entropy is the register's, its density times its area (`P1.local_entropy`, Postulate 1's
first sentence for the entropy of a local horizon, a quantity defined by qubits); and its area
changes by the Raychaudhuri equation (Lorentzian geometry, `Geometry.raychaudhuri`).
`Main.jacobson_step` derives from the last three, for one density `η` on every local horizon,
`R_ab k^a k^b = κ T_ab k^a k^b` for every null `k`,
`κ = 2πk_B/ℏcη` (`Derived.clausius`).
`Einstein.lean` derives from this the field equations up to a multiple of the metric; with the
first law for every small region and every observer (`Thermo.first_law_local`), which gives
`∇^a T_ab = 0`, and the contracted Bianchi identity (`Geometry.bianchi`), Einstein's equations
with one constant `Λ`, with matter and without; and with the static weak field
(`Geometry.weak_field`) and Newton's law, `κ = 8πG/c⁴` with `G = c³k_B/4ℏη`, which needs neither
the first law nor the Bianchi identity.  The rings then fix `Λ` (Sec. IV.D, `Space.lean`).  What
the files take from general relativity is what those equations imply by mathematics on the
manifold that Postulate 2 names, which describes the register at the scale of lengths and areas
(Sec. II).  Each is a published theorem whose inputs are proved in the files, are sentences of
the postulates or are conditions of the result, and each is a definition of the namespace
`Geometry` that states it with its
inputs and cites where it is proved: the Raychaudhuri equation on a local horizon; the contracted
Bianchi identity; the Leibniz rule for a flow; the Newtonian limit of geodesic motion; the
curvature of a static, spherically symmetric metric; the static weak field; Schur's lemma,
Hopf–Rinow and the Killing–Hopf theorem for the space at an instant; and Einstein's constraint on
that space.  The Schwarzschild–de Sitter solution is derived from the vacuum
equations (`Schwarzschild.static_vacuum`, `Main.schwarzschild_deSitter`); its metric function is
the definition `Reg.fSdS`, and its field and surface gravity are derived from it, with the pull of
a mass, the field the mass adds at the same `Λ` (`Reg.pull`).  Its constant is
that of the solution without a mass: as the body's mass grows from zero, the Clausius relation on
the observer's cosmological horizon (`Thermo.horizon_clausius`) keeps `Λ` unchanged
(`Reg.lambda_with_mass`, `Main.lambda_with_mass`).  The
Misner–Sharp and Komar energies of a sphere in it enter as the definitions `Reg.EMS` and `Reg.EK`,
each quoting the result it is.  The closed geodesics of de Sitter space are derived
(`Geodesics.lean`).  Lean has no Lorentzian geometry, no metric, curvature or Einstein tensor on a
manifold, so the files state each cited theorem for the objects they can name: the
Ricci and stress tensors of a spacetime and the divergence of the stress tensor at its points
(`Einstein.Spacetime`), the space forms (`Space.SpaceForm`), and the solution as a term of a type
that stands for the solutions.
This file is the one place where every premise the files take is written down, each as a
definition named by its source, with the sentence of the paper it is quoted in its docstring.
`Main.lean` states the paper's results with these definitions as their only hypotheses, and the
command `#premises` there checks, at build time, that every hypothesis of every result is one of
them (or a side condition from the namespace `Condition`, a result derived from them in
`Main.lean`, namespace `Derived`, a step at leading order whose exact form `Main.lean` derives,
namespace `Approx`, the units the results are stated in, namespace `Units`, or a premise that no
source states, listed as open, namespace `Open`, which holds none), and
that every object a result speaks of has a type that `Premises.allowedObjects` allows.  So a premise that is not in this file cannot enter a result without failing the build.
The command checks four things more.  Every result must take something from a source: a premise
of the postulates (the namespaces `P1` and `P2`), of thermodynamics (`Thermo`), of quantum
mechanics (`QM`) or of the cited geometry (`Geometry`), a derived statement, or an object of a
structure of the list below that carries clauses of the postulates; an open premise is none of
these.  The one other kind of result takes nothing and states that such a
structure has an instance (`Main.register_in_band`).  Every derived statement must be the
conclusion of a result that takes something from a source and whose own derived premises are
concluded before it, or, by its definition, such a statement at every time.  And every theorem
of the namespace `Register.Main`, or of a namespace under it, that stands before the command in
`Main.lean` must be among the results that the command is given.  And no result names a
measured number: the statement of a result, and the definition of everything of the package that
it names, through every definition, hold no constant of `Numerics.lean`, no decimal and no whole
number above 100.  The results that state an instance are excepted; `Main.register_in_band`,
which places a register in the measured band, is the one such result.  So a result that takes
nothing
from a source and states no instance fails the build.  The horizon's area takes the derived
constant of the solution without a mass.  The ceiling takes three sentences of Postulate 1: no
ring has more than `L` cells, and the bits as the possible outcomes with the joint measurement,
which Sec. IV.A reads together.  The limits of the law take the derived law.  These checks read
what a result takes.  Lean's unused-variables
linter reports a hypothesis that neither the statement nor the proof mentions, and the workflow
builds with `--wfail`, so that its warning fails the build.  Whether the conclusion needs a
premise depends on the statement, and no check of the build tests it.

Each definition unfolds to the hypothesis as the theorems of the other files take it, or to its
parts, so the results in `Main.lean` apply the theorems of the other files, with short arguments
joining them.

## The structures that carry sentences of the postulates, and the objects of the geometry

Some sentences of the postulates are the fields of structures, not hypotheses of theorems, and the
objects of the geometry are structures and definitions of the files.  They are listed here so that
the account is complete:

* `Horizon L` (`Horizon.lean`): Postulate 2's four clauses on incidence: every cell has one
  opposite, on every largest ring through it (`opp_opp`, `opp_ne`, `opp_mem`); two cells not
  opposite lie on exactly one largest ring (`exists_loop`, `unique_loop`); any two largest rings
  share a cell (`loops_meet`); no ring holds every cell (`misses`), which gives `4 ≤ L`
  (`Horizon.four_le`).  The structure also carries Sec. II's definition of a largest ring as a
  ring of `L` cells (`card_cells`), with a largest ring present (`exists_ring`).  Its finiteness
  fields are forced by the clauses (`Horizon.finite_of_clauses`).
* `Horizon.Positions H` (`RouteB.lean`): Postulate 1's "the string's cyclic position on its ring"
  (`pos`, `pos_inj`) and Postulate 2's "the same cell halfway around every largest ring through it"
  (`pos_opp`).
* `Horizon.Symmetry` (`Homogeneous.lean`): Postulate 2's "some map of the cells that keeps the
  largest rings" (`mem_iff`).
* `Qubit.Op`, `Qubit.Vec` (`Qubit.lean`): Sec. II's definition of a qubit as a two-level quantum
  system, with a state a linear combination of its two outcomes (Postulate 1) and a tick a linear
  map on the states; the bit values are the two senses by definition (Sec. II).
* `Qubit.Tick L` (`Qubit.lean`): Sec. II's sentence on a free tick, in its words, "A string of one
  sense has the same bit on every cell, so the shift leaves it as it is, up to its global phase
  (Postulate 1), and that phase changes alike in either sense, since no law depends on the ring's
  direction (Postulate 2)" (`hsense`: the tick keeps each string of one sense up to one and the
  same phase, a factor of modulus one, Sec. II's definition of the global phase).  What the tick
  does to a state of energy `E` is Sec. II's definition of energy (`P1.string_energies`).  By the
  same definition the energy of a string of one sense is a function `En : ℂ → ℝ` of the factor by
  which the tick multiplies it (`Qubit.Tick.energy`), an object of the results that take the
  thermal state of a tick; they hold for every such function.
* `Register.Reg` (`Chain.lean`): the constants `c`, `ℏ`, `k_B`, `ℓ_c`, `L` as positive reals; the
  register's own quantities are definitions on it.
* `Einstein.Spacetime` (`Einstein.lean`): a spacetime as the files see it, its points with the
  Ricci tensor, symmetric (`ric_symm`), the stress tensor and its divergence `∇^a T_ab` at each, in
  a frame where the metric is `diag(−1, 1, 1, 1)`.
* `Space.SpaceForm`, `Space.SphereQuotient` (`Space.lean`): the space forms of dimension three,
  the three-sphere, Euclidean space and hyperbolic space divided by a group acting freely and
  properly discontinuously, the sphere's group a finite group of rotations of space that leave time
  alone.
* `Register.Reg.fSdS`, `Reg.EMS`, `Reg.EK` (`Chain.lean`, `Cosmo.lean`): the metric function of
  the Schwarzschild–de Sitter solution, which `Main.schwarzschild_deSitter` derives, and the
  Misner–Sharp and Komar energies, as definitions.
-/

open Horizon Finset Filter Topology

namespace Register.Sources

variable {L : ℕ}

/-- the Borel sets of `ℍ`, the space of the drawing (`Center.lean`), for the weighting of its
rotations (`P1.no_rotation_preferred`) -/
noncomputable instance instMeasurableSpaceQuaternion : MeasurableSpace (Quaternion ℝ) :=
  borel (Quaternion ℝ)

instance instBorelSpaceQuaternion : BorelSpace (Quaternion ℝ) := ⟨rfl⟩

/-! ## Postulate 1 -/
namespace P1

/-- **Postulate 1, first sentence: "Every physical law and quantity is defined by qubits"**
(Sec. II).  The files take it in three forms, each the sentence for one kind of thing it speaks of,
and every premise of this namespace that joins a law or a quantity to the register is one of them
applied; the sentence quantifies over laws and quantities, and these are the forms a law and a
quantity take in the files.
* A **law** is a function of the register's crossings, `H.Cell → H.Loop → V`: the type every law
  has in the files (`Symmetry.laws_same`, `Main.lean`), of which Postulate 2's two clauses on laws
  speak; the premise ledger lists each law as an object of that type.
* A **quantity that varies over items** of the register, the crossings or the slots of space, is
  defined by what the register holds at the item, its content: `qubits content q`, the quantity
  `q` is `F (content i)` for one function `F` (`Symmetry.IsQubits`, which the theorems use;
  Sec. IV.D: the laws and the state alone set the geometry of space).  Applied
  to the geometry of space (`geometry_qubits`), with the laws and the state at a place as the
  content, and to the weighting of the drawing's rotations (`no_rotation_preferred`), with nothing
  as the content, since the drawing is no part of the register.
* A **quantity to which another description assigns a value**, the manifold or thermodynamics,
  has the register's value, since the register defines it: `physical manifold register`, the two
  values are equal, a difference being a physical quantity not defined by qubits; the quantity may
  be of any type.  Applied to the energy inside the horizon (`energy_inside_strings`),
  to the entropy of the cosmological horizon (`horizon_entropy`) and of a local horizon
  (`local_entropy`), and to a body's energy (`energy_in_carriers`); the second and the third are
  written with `physical`, the first and the last as the equation it unfolds to.  It is applied
  as well to the mass energy that a measurement on the manifold finds in a set of a string's
  cells (`mass_in_bits`): the register's value is what the bits in those cells hold, and the
  premise states it as a count that adds over cells.
Space enters through Postulate 2's last sentence, which places the cells on the geodesics, and
through `rings_along`: the geometry of space is a quantity, so a geodesic along which no ring runs
would be a feature of a quantity not defined by qubits.  Light crossing a cell in one tick
(`light`) is another sentence of Postulate 1.  The energy of light is not an application of the
first sentence: Sec. II gives energy to a state and does not place it in cells, so the light whose
energy moves with it along its ray is the case a result treats, a condition
(`Condition.light_flow`), as dust is (`Condition.dust_flow`).  Which cited definition is the
manifold's value of a quantity, the Misner–Sharp energy and the entropy of Clausius' relation, the
sources of the geometry and of thermodynamics state; which definition of Sec. II is the
register's, the entropy of the strings' state, the paper states. -/
def qubits {ι C α : Type*} (content : ι → C) (q : ι → α) : Prop := Symmetry.IsQubits content q

/-- **A quantity defined by qubits has one value, the register's** (Postulate 1's first sentence,
for a quantity to which another description, the manifold or thermodynamics, assigns a value):
the value that description assigns, `manifold`, is the value the register defines, `register`.
Were the two different, the difference would be a physical quantity not defined by qubits.  The
quantity may be a number, as the entropy of a horizon (`local_entropy`), and the values are of
any one type. -/
def physical {α : Type*} (manifold register : α) : Prop := manifold = register

/-- Postulate 1: "The bits are the possible outcomes of one measurement of the qubit", with
Eq. (raqm): each cell's bit is one possible outcome among the `L`, so the probability that a
measurement's outcome is the bit of a given cell is `1/L` (`halike`). -/
def bits_alike (H : Horizon L) (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ) : Prop :=
  ∀ l x, read l x = 1 / (L : ℝ)

/-- Postulate 1: "The bits are the possible outcomes of one measurement of the qubit", with
Eq. (raqm), for the string on one ring, whose cells are the type `Cell`: each cell's bit is one
possible outcome among the ring's, so the probability `read x` that a measurement's outcome is the
bit of the cell `x` is one over their number (`halike`; `bits_alike` is the same sentence on every
largest ring of the register, of `L` cells).  From it `Main.block_fraction` derives that the
fraction of 1s on a block of cells is the probability of the outcome `1` given the block, the
conditional probability built from the cells' probabilities (`Capacity.condProb`,
`Capacity.block_fraction_read`).  In a joint measurement, one measurement whose possible outcomes
are the positions (Sec. IV.A), `read x` is the probability of the position `x`, and the
probability of a set of positions is the sum of theirs.  `Main.joint_frequency`,
`Main.product_state` and `Main.strings_in_step` derive from it that the probability of a joint
outcome in a pairing is the share of the positions that show it, a multiple of one over the
number of the ring's cells, `1/L` on a largest ring, with every string exact.  The ceilings of
Sec. IV.A do not take these equal weights: they take `outcomes_at_positions`.
`Main.share_amplitude` takes the premise for the bits that a body's share fills at a string
(Sec. IV.C): the probability that the outcome is one of those bits is their share of the ring's
cells (`Capacity.share_read`), and the amplitude of the share is its square root. -/
def ring_bits_alike {Cell : Type*} [Fintype Cell] (read : Cell → ℝ) : Prop :=
  ∀ x, read x = 1 / (Fintype.card Cell : ℝ)

/-- Postulate 1: "The bits are the possible outcomes of one measurement of the qubit" and "Any two
qubits can be measured jointly".  Sec. IV.A reads the two sentences together: "A joint
measurement is one measurement, so its possible outcomes are the `L` positions", and "The outcome
at a position is the bits there".  Each cell `x` of a string is paired with the outcome `e x` of
the earlier qubits at its position, and `b x` is the string's bit there.  `pr k v` is the
probability, in the state that the register holds, that the earlier qubits show `k` and the
string's qubit shows the bit `v`.  A joint outcome that occurs, with `pr k v > 0`, is a possible
outcome, so it is the outcome at a position: some cell paired with `k` has the bit `v` (`hout`).
Sec. IV.A uses the sentences in this form: of the joint outcomes that occur, "each of them takes
at least one of the `L` positions".

The results on codes take the premise with `k` a conditional state, and `Main.ceiling_logical`
with `k` a label that stands for one.  The earlier bits at a position fix the conditional state
that they give the string's qubit, so a conditional state that occurs with a value of the bit is
at a position with that value.  The results on codes do not take the premise with `k` a reading
of the earlier physical bits.  Taken so, it asks a cell for each reading and value of the bit
that occur together, which is more than two cells for each conditional state where several
readings give one state.  The results on codes state the count by conditional state and no
other.  The paper's count for codes agrees with it (Sec. IV.A): the fullest physical string "has
up to `2^N` conditional states to hold", and "Where the equal and the opposite case both occur
and the `2^N` conditional states are superpositions that all differ in probability, as in a
random state, that string needs `2^N` blocks of at least two cells".  A reading of the earlier
physical bits with the string's bit is a joint outcome of physical qubits.  Of the joint
outcomes of the physical qubits the paper says, where it gives the ceiling for logical qubits:
"Below it the encoded state is held with its strings exact and its pairing approximate, as a
product state is, even where the joint outcomes of its physical qubits outnumber `L`".
`Main.joint_frequency` states that sentence's count: where more than `L` joint outcomes occur,
every pairing gives one of them the frequency zero (`Pairing.pairing_misses`), while every string
keeps its own fraction in every pairing (`Main.strings_in_step`).

In the ceilings and the results on codes the premise does not fix the probabilities, and nothing
else in a statement does.  The
docstrings read `pr` as the probabilities of the state that the register holds, and no statement
of those results says so.  `Main.overlap_bound` and `Main.return_bound` fix them.  They take the
premise with `k` a conditional state of the last qubit, as the results on codes take it: the
conditional states are those of the state `ψ` that the circuit calls for, and the probabilities
those of the state `held` that the register holds.  `pr s v` is the sum of `|held (k, v)|²` over
the joint outcomes `k` of the other qubits to which `ψ` gives the conditional state `s`, and a
block is taken to hold the conditional state that `ψ` gives its joint outcome.

A joint outcome is not a conditioned outcome.  A joint outcome is what one joint measurement
shows at a position, the bits of all its strings there.  With `k` a joint outcome of the earlier
qubits the premise is the sentence for one joint measurement, a pairing of the strings, and no
pairing shows more than `L` joint outcomes (`Main.joint_frequency`).  A conditioned outcome is
the outcome of one qubit given the outcomes of the others, its bit in the conditional state
that they give it.  With `k` a conditional state the premise is the sentence for the
measurement of that qubit: a conditional state that occurs with a bit has that bit at a cell of
a block that holds the state.  Strings that are measured jointly are not thereby conditioned.
In a product state the last qubit has one conditional state, however many joint outcomes of the
other qubits occur (`Conditional.product_one_state`), and its string holds that state on all
its cells.  So the premise by conditioned outcome does not bound a product state, nor any state
for whose conditional states the string has room, two cells for each
(`Conditional.room_holds`).  Where every joint outcome has a conditional state of its own, as
in a random state (`Condition.all_differ`), a conditioned outcome is one joint outcome, and the
premise is then the premise by joint outcome for what the register holds, which gives the bound
of `Main.overlap_bound`.

In the ceilings and the results on codes `pr`
occurs in the premise and in one condition.  Each outcome of a set has a cell of either bit exactly when some `pr` meets both the
premise and the condition that each outcome of the set occurs with either value of the bit
(`Capacity.outcomes_iff_cells`).  In `Main.one_cell_block` `pr` occurs in the premise and in the
conclusion.  Eq. (raqm), which gives the probabilities as shares of the bits, is
`ring_bits_alike`, and the ceilings do not take it. -/
def outcomes_at_positions {Cell K : Type*} (pr : K → Bool → ℝ) (e : Cell → K)
    (b : Cell → Bool) : Prop :=
  ∀ k v, 0 < pr k v → ∃ x, e x = k ∧ b x = v

/-- Postulate 1: "No ring has more than `L` cells, with `L ∈ ℕ`", for the ring of one qubit's
string, whose cells are the type `Cell` (`hL`).  The ceiling of Sec. IV.A follows from this
sentence and the room that a qubit's conditional states take on its string; a string on a shorter
ring, which the sentence allows, has less room, so that `2^N ≤ L` holds in every case
(Sec. IV.A).  `L` is the number that the sentence names, the length of a largest ring (Sec. II).
The premise states the sentence for this ring and names no register, so a result that takes it
holds for whatever `L` bounds the ring. -/
def ring_cells (Cell : Type*) [Fintype Cell] (L : ℕ) : Prop := Fintype.card Cell ≤ L

/-- `qubits` for the geometry of space (`hgeom`), a quantity defined by qubits: the geometry at a
slot is read off the laws and the state there, the content: the law `f` at the slot, and the state at the slot's crossings, the
string's thermal state, the cell's bit as one possible outcome, and the string's correlation with
the other strings under their joint distribution `Pst` (`Solution.crossingState`). -/
def geometry_qubits {Slot V Gm : Type*} (H : Horizon L) (f : H.Cell → H.Loop → V)
    (ρ : H.Loop → Qubit.Op) (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ)
    (Pst : (H.Loop → Bool) → ℝ) (geom : Slot → Gm) : Prop :=
  qubits (fun σ : Symmetry.described (Set.univ : Set (H.Cell → H.Loop → Slot)) =>
    (Symmetry.lawAt Set.univ f σ, Symmetry.lawAt Set.univ (Solution.crossingState ρ read Pst) σ))
    fun σ => geom σ

/-- **Postulate 1, first sentence, applied to the geodesics of a space** (Secs. II and IV.D: "a
largest ring can run through any place in any direction, and by Postulate 2 it is a closed geodesic
of space"): along every geodesic `σ` of the set `S` some admissible drawing runs a ring, which
closes there with a largest ring's length, `Closes σ` (`Symmetry.ringsAlong`).  The geometry of
space is a quantity defined by qubits, so a geodesic along which no ring runs would be a feature of
a quantity that the strings do not define.  The one sentence
is taken twice, each an application of this definition at the geodesics of the space at an instant
of an observer at rest: at its slots (`slice_qubits`) and at the geodesics of its space form
(`slice_form_qubits`). -/
def rings_along {Slot : Type*} (H : Horizon L) (S : Set Slot) (Closes : Slot → Prop) : Prop :=
  Symmetry.ringsAlong H S Closes

/-- `rings_along` for the space at an instant of an observer at rest, whose geodesics are all the
slots: along every one some admissible drawing runs a ring, which closes with a largest ring's
length (`hclose`; "space is the cells of the rings", Sec. II).  So every geodesic of space closes,
the completeness that the Killing–Hopf theorem asks (`Geometry.space_form`).  `Closes` is the
predicate of that premise, which reads it as "the geodesic closes": the files have no geodesics of
a space of their own, so the predicate is an object of the result, which the premise ledger names
as a predicate, and its meaning is fixed by `Geometry.space_form`. -/
def slice_qubits {Slot : Type*} (H : Horizon L) (Closes : Slot → Prop) : Prop :=
  rings_along H Set.univ Closes

/-- `rings_along` for the space at an instant once it is a space form `c`, at the form's geodesics
(`Space.SpaceForm.slots`), closing in its quotient with the length `Lℓ_c` (`Space.SpaceForm.closes`;
`hslice`, `Space.SliceIsQubits`). -/
def slice_form_qubits {Sp : Type*} (H : Horizon L) (R : Reg) (sp : Sp)
    (embedSp : (K : ℝ) → Space.SpaceForm K → Sp) : Prop :=
  ∀ K (c : Space.SpaceForm K), sp = embedSp K c → rings_along H c.slots (c.closes (R.L * R.ℓc))

/-- **The strings' energies, by Sec. II's definition of energy** (`hEs`; Sec. II: "A state that one
tick multiplies by `e^{−iΔ}` has energy `ℏΔ/t_c`, as in quantum mechanics, where a state
of energy `E` gains the factor `e^{−iEt/ℏ}` in the time `t`"; Sec. IV.E: "By the definition of
energy (Sec. II) the factor is `e^{−iEt_c/ℏ}`, with `E` the string's energy").  The definition is
that of quantum mechanics, taken in Sec. II with the postulates: it ties the energy of a state to
what a tick does to the state.  The free tick multiplies every state of a string by one factor
(`Qubit.Tick.phase_unique`, from Postulates 1 and 2 and linearity), and the statement is the
definition for that factor, read from the energy to the factor: with `Δ = Et_c/ℏ`, the tick of a
string of energy `E` is `e^{−iEt_c/ℏ}` on every state.  It says so for every string of the
register, with the energies `Es`.  The energies are given to the statement and not defined by it:
a factor fixes `Δ` only up to whole turns, and the statement names no turn.
`Main.string_energy` takes the same `Es` in the thermodynamic premise `Thermo.energies_thermal`.
The files up to v18-62 carried the same statement as a premise of quantum mechanics, named for
Schrödinger's equation. -/
def string_energies (H : Horizon L) (R : Reg) (τ : H.Loop → Qubit.Tick L) (Es : H.Loop → ℝ) :
    Prop :=
  ∀ l, (τ l).U = Complex.exp (-((Es l * R.tc / R.ℏ : ℝ) : ℂ) * Complex.I) • (1 : Qubit.Op)

/-- **The energy inside the horizon is the strings'** (`hin`; Sec. IV.E: "Every physical quantity
is defined by qubits (Postulate 1), so the energy inside the horizon is the strings' and nothing
else's").  Postulate 1's first sentence applied to the energy inside an observer's cosmological
horizon: `E_in`, the energy inside it, is the sum of the energies of the strings, Sec. II's energy,
the generator of the tick, over the free strings, one on each of the count's `L²/4 − L/2 + 1`
rings, every ring with half its cells inside the horizon (`Bridge.horizon_counts_every_ring`; the
cells are segments of the rings' geodesics, Postulate 2's last sentence), each string whole, as its
bit is in the horizon's entropy.  With the strings' mean energy `k_BT_dS` (the Gibbs distribution
at the horizon's temperature, `Carriers.string_energy`) and the vacuum's energy `k_BT_dS ln 2` per
string (`Reg.EMS_per_ring`), `Main.vacuum_share` derives the vacuum's share `ln 2`.  The strings
need not be alike: the result uses the mean of their energies. -/
def energy_inside_strings (H : Horizon L) (Ein : ℝ) (Es : H.Loop → ℝ) : Prop :=
  Ein = ∑ l, Es l

/-- **The body's energy is held by the strings that carry its information** (`hcar`; Sec. IV.C):
Postulate 1's first sentence for a body's energy.  Energy is held only by strings; a string that
does not carry the body's information keeps, at its two receiving cells, the cells where its ring
crosses the sphere, the state it has without the body, and holds none of the body's energy; so the
body's energy `Mc²`, `M` all the mass inside the sphere, is held by the `N_car` carriers, in equal
shares `ε_c` by equipartition (`Law.share_of_equipartition` gives the sum in finite form). -/
def energy_in_carriers (R : Reg) (M Ncar εc : ℝ) : Prop := M * R.c ^ 2 = Ncar * εc

/-- **Mass energy is found in the bits of its cells and adds over cells** (`hmass`; Sec. IV.C),
an application of Postulate 1's first sentence, with the manifold's measure of mass energy, for
the string on one ring, whose cells are the type `Cell`.  `held S` is the mass energy that a
measurement on the manifold finds in the cells of the set `S`.  A mass is measured on the
manifold, so it is represented by specific cells, the cells where the measurement finds it.
Mass energy is a physical quantity, so it is defined by qubits (Postulate 1), and the only bits
that can enter this measurement are the bits in those cells: the mass energy is found in the
bits there and nowhere else.  Conversely, cells that held no such bits would show no mass.  The
manifold's measure adds over regions that do not overlap, and the statement is that sum for the
cells: two sets of cells with no cell in common hold together the sum of what each holds.  With
it the empty set of cells holds none, `held ∅ = 0` (`Law.mass_empty`).  With Postulate 2's
clause that no cell differs from another (`P2.cells_hold_alike`) a set of cells holds the
number of its cells times what one cell's bit holds (`Law.mass_counts_bits`), so mass energy is
counted in bits.  `Main.share_amplitude` takes the premise, with `P2.cells_hold_alike`,
`string_matter_in_bits` and `share_bits`, and derives the amplitude of a body's share at a
string.  The argument is the author's of 14 November 2026.
Sec. IV.C: "Mass is measured on the manifold, at places, and a place is a cell (Sec. II)."
"The measurement finds the bits in those cells and nothing else (Postulate 1), so mass energy is
counted in bits: cells without such bits show no mass."  Sec. III lists the premise among the
applications of Postulate 1's first sentence, "to mass energy, which is counted in bits". -/
def mass_in_bits {Cell : Type*} [DecidableEq Cell] (held : Finset Cell → ℝ) : Prop :=
  ∀ S T : Finset Cell, Disjoint S T → held (S ∪ T) = held S + held T

/-- **A string holds its matter on all its bits** (`hstring`; Sec. IV.C), an application of
Postulate 1 for the string on one ring, whose cells are the type `Cell`.  Every qubit is a string
of bits, one on each cell of a ring (Postulate 1), and a string is one whole qubit, which holds
the matter `u = (1 − ln 2)ε_s` on average (`Reg.matter`, with `ε_s` the strings' mean energy).
The matter is mass energy, and the string's bits are on the cells of its ring, so the mass
energy that a measurement finds in all the cells of the ring is that matter: `held univ = u`,
with `held` the count of `mass_in_bits`.  With `mass_in_bits` and `P2.cells_hold_alike` each
cell's bit then holds `u/n`, `n` the number of the ring's cells, and a set of `m` cells holds
`(m/n)u` (`Law.mass_of_cells`).  `Main.share_amplitude` takes the premise.
Sec. IV.C: "The strings hold the matter `u` per string, on the `L` bits of one whole qubit, so for `f ≤ 1` a
string's share of the body, `E = fu`, fills the fraction `f` of its bits, to within one bit." -/
def string_matter_in_bits {Cell : Type*} [Fintype Cell] (R : Reg) (held : Finset Cell → ℝ)
    (εs : ℝ) : Prop :=
  held Finset.univ = R.matter εs

/-- **A share that one string can hold fills whole bits of the string, and `h` is their
amplitude** (`hbits`; Sec. IV.C), an application of Postulate 1 for the string on one ring.  A
body at rest, treated as a point, one cell, has a share at each string of a sphere about it.
The share is the body's energy per string of the sphere, two Landauer energies at the Unruh
temperature `T_N` of Newton's field, `E = 2k_BT_N ln 2` (Eq. (E)).  A string that carries the
body's information is one of the body's qubits, and it holds the matter `u` on all its bits
(`string_matter_in_bits`).  The body is a mass, so its share is mass energy, which is found in
the bits of specific cells (`mass_in_bits`).  The statement is for a share that one string can
hold, `0 ≤ E ≤ u`, and it has two parts.  The first: the share fills a set `S` of the string's
cells and not one cell more.  Every qubit is a string of bits, one on each cell of a ring
(Postulate 1), so a bit is whole, and the share fills whole bits: the bits of `S` hold at most
the share, `held S ≤ E`, and with the bit of any further cell `x` they would hold more than the
share, `E < held (insert x S)`.  The second: `h` is the amplitude of those bits.  The bits are
the possible outcomes of one measurement of the qubit (Postulate 1), `read x` is the
probability that the outcome is the bit of the cell `x` (`ring_bits_alike`), and the
probability that it is the bit of a cell of `S` is the sum of theirs.  A state is a linear
combination of outcomes (Postulate 1), in which the amplitude of an outcome is the square root
of its probability, Eq. (qubit) with Eq. (raqm), as in the state of a string
(`Qubit.stringState`): `h = √(∑ x ∈ S, read x)`.  With `mass_in_bits`, `P2.cells_hold_alike` and
`string_matter_in_bits`, for `u > 0`, such a set exists for every share `0 ≤ E ≤ u`
(`Law.fills_exists`), so the statement can be met at every such share
(`Law.share_bits_model`).  It then gives `E/u − 1/n < h² ≤ E/u` on a string of `n` bits, and
`h² = E/u` where the share is a whole number of bits (`Law.filled_bits`).  A share below one
bit fills no bit, and its amplitude is zero (`Law.share_leading_order`).
`Main.share_amplitude` derives the exact amplitude from it (`Derived.share_amplitude_exact`),
and `h = √(E/u)` is its leading order in `1/L` (`Approx.share_amplitude`).  For a larger share
the statement says nothing, and the condition `Condition.same_scale` gives `h`.
Sec. IV.C: "The strings hold the matter `u` per string, on the `L` bits of one whole qubit, so for `f ≤ 1` a
string's share of the body, `E = fu`, fills the fraction `f` of its bits, to within one bit."
"That fraction is the probability of Eq. (raqm), and its amplitude is `√f`, Eq. (qubit)."  The second sentence is the second
part, with `ring_bits_alike`. -/
def share_bits {Cell : Type*} [DecidableEq Cell] (R : Reg) (held : Finset Cell → ℝ)
    (read : Cell → ℝ) (h TN εs : ℝ) : Prop :=
  0 ≤ 2 * R.kB * TN * R.ln2 → 2 * R.kB * TN * R.ln2 ≤ R.matter εs →
    ∃ S : Finset Cell, held S ≤ 2 * R.kB * TN * R.ln2 ∧
      (∀ x, x ∉ S → 2 * R.kB * TN * R.ln2 < held (insert x S)) ∧
      h = Real.sqrt (∑ x ∈ S, read x)

/-- **A body's share reaches a string in equal parts, one per tick, which add as amplitudes**
(`hparts`; Sec. IV.C), an application of Postulate 1.  Sec. IV.C: "Treated as a point (above),
the body is one cell, so in one tick its share reaches one cell of the string, which holds one of
the string's `L` bits: each tick brings `1/L` of the share."  "As the injected signal adds to the
laser's field, these parts add as amplitudes: they arrive with the same phase at every tick, and
a state is a linear combination of outcomes (Postulate 1)."  "The share has the amplitude `h`
against the string's one whole qubit, and its `L` parts add up to it, so each tick adds the
amplitude `h/L`."  The statement counts the parts by the cells of the string's ring, one bit on
each: each tick adds to the string one and the same amplitude `ε`, and the parts add up to the
amplitude `h` of the share (`Derived.share_amplitude_exact`), so the number of the ring's cells
times `ε` is `h`, for the string of every largest ring `l`.  A largest ring has `L` cells
(`Horizon.card_ring`,
`Main.ring_one_string`), so `ε = h/L` (`Main.carriers_exact`): the factor `1/L` is the count of
the string's bits, which the structure `Horizon` carries.  Up to v18-68 the files stated no
share per tick: they took the carriers as a premise, the strings whose threshold the amplitude
of the share exceeds (`P1.carriers_by_amplitude`). -/
def share_in_parts (H : Horizon L) (h ε : ℝ) : Prop :=
  ∀ l : H.Loop, (Fintype.card {x // x ∈ H.cells l} : ℝ) * ε = h

/-- **A string carries a body's information when its global phase holds against the body's
share** (`hcarry`; Sec. IV.C), an application of Postulate 1 with Sec. II's definition of energy.
The rule speaks of a string as a whole.  Sec. IV.C: "A string is one qubit (Postulate 1), so it
carries the quantum information of the body's mass, the body's information for short, at both its
receiving cells or at neither."  The statement does not name the receiving cells; it counts the
strings that carry.  Sec. IV.C: "A string that carries it takes its phase from the body's state,
as a laser locked to an injected signal takes its phase from the signal."  The condition is that
of one tick.  Sec. IV.C: "For a string the round trip is one tick."  A free tick turns the global
phase of a string of energy `E` by `Δ = Et_c/ℏ`: Sec. II's definition of energy, which
`string_energies` states for the strings of the register, whose tick is the factor
`e^{−iEt_c/ℏ}`.  The turn `Δ` is the slip against the body's share.  Sec. IV.C: "The body is at
rest, so its share is the same at every tick, and the turn is the slip of the string's global
phase against the body's."  The same tick adds to the string the amplitude `ε` of the body's
share, at a fixed phase (`share_in_parts`).  The string's global phase holds against the share
when the tick leaves some phase of the string unchanged (`Law.keepsPhase Δ ε`): a state of unit
amplitude with that phase, turned by `Δ` and with the amplitude `ε` added, has that phase again.
Sec. IV.C: "Where the slip per tick is larger, the global phase slips at every tick and the
string takes no phase from the body."  "Where it is smaller, the ticks draw the global phase to a phase that they leave unchanged, as
the Lean files also prove."  "The share is the same at every tick, and the law is that of the state that the ticks leave
unchanged, in which the string holds that phase."
The statement is that law: it counts the strings whose phase holds, those for which the tick
leaves some phase unchanged (`Law.keepsPhase`), in the state that the ticks leave unchanged.
The files prove that this is the state to which the ticks draw the phase.  Where the added
amplitude `ε` is smaller than `|sin Δ|` the phase moves in one sense at every tick
(`Law.phase_slips`).  Inside the range the tick keeps the phases `φ₀` and `π − φ₀`
(`Law.kept_phases`), the phase moves toward `φ₀` (`Law.phase_drawn`) without passing it
(`Law.tick_between`), the tick leaves `φ₀` in place (`Law.tickPhase_kept`), and the repeated
tick converges to `φ₀` from every phase strictly between `−π − φ₀` and `π − φ₀`
(`Law.tick_converges`), a small gap shrinking per tick by a factor between `0` and `1`
(`Law.tick_contracts`).  `Main.phase_under_tick` states the slip outside the range and the
convergence inside it for a string of the register, with the turn `Δ = Et_c/ℏ` and the
amplitude `ε = h/L` that one tick adds (`Reg.phase_under_tick`).  The rule is that a string
carries the body's information when its phase holds, whatever the turn `Δ` of its free tick
is, so every turn counts.  The condition is the same after a whole turn more (`Law.keepsPhase_add_turns`), and
`string_energies` names no turn, so the strings whose turn lies near one or more whole turns
carry as well as the strings whose turn is small.  Sec. IV.C: "The exceptions are the strings
that a tick turns to within `arcsin(h/L)` of one or more whole turns."  "A whole turn is no turn,
so they carry the body's information too; they are a fraction below `e^{−3πL/2}` of the
strings."

The statement gives the carriers' fraction `b` through the spread of the strings' energies, with
`above x` the fraction of the strings whose energy exceeds `x` (`Thermo.energies_thermal`).
Whatever distribution `μ` of the strings' energies, a probability measure on the energies, has
the fraction `above x` above each energy `x ≥ 0`, `b` is the fraction that `μ` gives to the
strings of energy `E ≥ 0` whose phase holds.  The statement names no threshold and no range of
turns, and the files derive both.  Where `0 < ε < 1` the phase holds exactly when the turn lies
within `arcsin ε` of a whole number of turns (`Law.steady_phase_all_turns`,
`Law.steady_phase_iff_turns`).  So the carriers are the strings of energy at most
`(ℏ/t_c) arcsin ε` and the strings of energy within `(ℏ/t_c) arcsin ε` of `2πkℏ/t_c` for a
whole number `k ≥ 1` (`Reg.phase_all_turns`).  With the spread of `Thermo.energies_thermal` at
the horizon's temperature a distribution with these fractions exists
(`Law.gibbs_measure_exists`), and the statement holds exactly when
`b = (1 − e^{−L arcsin ε})(1 + (e^{L arcsin ε} + 1)/(e^{2πL} − 1))` (`Reg.carriers_rule_iff`).
It can then be met, together with the share's parts and the spread (`Reg.carriers_model`), and
it fixes `b`.  The strings whose turn lies near one or more whole turns are a fraction below
`e^{−3πL/2}` of the strings (`Main.carriers_exact`).  Up to v18-68 the files took the carriers
as a premise, the strings whose threshold the amplitude of the share exceeds
(`P1.carriers_by_amplitude`), with the distribution of the threshold as a premise of
thermodynamics (`Thermo.max_entropy_threshold`). -/
def carriers_hold_phase (R : Reg) (b ε : ℝ) (above : ℝ → ℝ) : Prop :=
  ∀ (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ],
    (∀ x : ℝ, 0 ≤ x → (μ (Set.Ioi x)).toReal = above x) →
    b = (μ {E : ℝ | 0 ≤ E ∧ Law.keepsPhase (E * R.tc / R.ℏ) ε}).toReal

/-- Postulate 1: "The global phase of a state is hidden: no law depends on its value"
(`hhidden`), for a law of a string's qubit.  `law v` is what the law reads off the state `v`, and
it reads the same off `e^{iγ}v` for every `γ`.  `Main.free_tick_hidden` takes it: no law tells a
free string's state after a tick from its state before.  The free tick carries the same sentence
in its field `hsense`, which leaves a string of one sense as it is "up to its global phase". -/
def phase_hidden {α : Type*} (law : Qubit.Vec → α) : Prop :=
  ∀ (γ : ℝ) (v : Qubit.Vec), law (Complex.exp ((γ : ℂ) * Complex.I) • v) = law v

/-- Postulate 1: "No ring has more than `L` cells, with `L ∈ ℕ`": `L` is a constant of the
postulate, one natural number at every time (`hL` of `Cosmo.GLambda_constant`; `ring_cells` is the
sentence for the cells of one ring). -/
def constant_L (Rt : ℝ → Reg) : Prop := ∀ s, (Rt s).L = (Rt 0).L

/-- Postulate 1: "each cell of length `ℓ_c`", one length at every time (`hℓc`). -/
def constant_cell (Rt : ℝ → Reg) : Prop := ∀ s, (Rt s).ℓc = (Rt 0).ℓc

/-- **Light crosses a cell in one tick** (`hlight`; Secs. II and III.B), a sentence of Postulate 1
read on the manifold with Postulate 2's last sentence.  Each cell has the length `ℓ_c`, "which light
crosses in one tick" (Postulate 1), the tick being the time light takes to cross a cell (Sec. II),
and a cell is a segment of length `ℓ_c` of a geodesic of space (Postulate 2's last sentence), so
light moves `ℓ_c` of proper length per tick, at `c`, and in every direction, since a largest ring
runs through any place in any direction (Sec. II).  In the frame the files use at a point, where
the metric is `diag(−1, 1, 1, 1)`, a direction of speed `c` is a null direction: the direction `k`
of a ray of light is null and not zero.  What the energy of light does is no part of this premise:
the result on light takes it as the case it treats (`Condition.light_flow`). -/
def light (k : Fin 4 → ℝ) : Prop := Einstein.IsNull k ∧ k ≠ 0

/-- `qubits` for the weighting of the drawing's rotations (`hν`; Sec. II: "the drawing is
no part of the state and no rotation of it is preferred: the rotations are weighted by a weighting
that no rotation changes").  The rotations `x ↦ qx` by the unit quaternions `q` are weighted by a
probability measure `ν` on them.  The drawing of the rings as great circles of the three-sphere is
no part of the register, which holds nothing about a rotation of it: the content at every
rotation is nothing, `()`, and the quantity read off it is the weighting as seen from that
rotation, `ν` carried by the rotation `g`, `map (g * ·) ν`.  Read off nothing, it is the same at
every rotation, so it is `ν` itself: `ν` is left invariant (`no_rotation_preferred.invariant`).
Such a weighting is the unit sphere's measure, normalized, with the rotations weighted alike, by
the uniqueness of Haar measure (`Weighting.eq_toSphere_of_invariant`), so the averages are those of
`Center.lean`.  The count about a body is its average over the rotations, by definition
(Sec. II). -/
def no_rotation_preferred (ν : MeasureTheory.Measure (Metric.sphere (0 : Quaternion ℝ) 1)) :
    Prop :=
  MeasureTheory.IsProbabilityMeasure ν ∧
    qubits (fun _ : Metric.sphere (0 : Quaternion ℝ) 1 => ())
      fun g => MeasureTheory.Measure.map (g * ·) ν

/-- a weighting read off nothing is the same at every rotation: left invariant -/
theorem no_rotation_preferred.invariant {ν : MeasureTheory.Measure (Metric.sphere (0 : Quaternion ℝ) 1)}
    (h : no_rotation_preferred ν) : ν.IsMulLeftInvariant := by
  obtain ⟨F, hF⟩ := h.2
  refine ⟨fun g => ?_⟩
  have h1 := hF 1
  simp only [one_mul] at h1
  rw [MeasureTheory.Measure.map_id'] at h1
  exact (hF g).trans h1.symm

/-- `physical` for the entropy of a local horizon (`hent`; Secs. II and III.B: "A local Rindler
horizon is crossed by largest rings, whose cells are segments of the geodesics there (Postulate 2),
and its state is a state of those strings (Postulate 1).  So its entropy per unit area is a law,
and by the symmetry of space it is the cosmological horizon's, one bit per ring's share of area").
The manifold's value is the entropy of Clausius' relation on the local horizon through the point
`p` generated by the null `k`, thermodynamics' definition, as it changes with the horizon's area:
`dS(p, k)`, the coefficient beside `dA(p, k)` in `−∫ λ … dλ dA` along the generators.  The
register's value is the entropy of the strings crossing the horizon, whose cells lie there
(Postulate 2's last sentence), the state of the horizon being a state of those strings as the
cosmological horizon's is (`Bridge.horizonEntropy`): their entropy per unit area is the law `η`,
which Postulate 2's two clauses on laws make one value `η₀` on every horizon
(`Symmetry.one_density`), the count's (`horizon_entropy` below, with `Main.jacobson_G_exact`), so
the register's entropy of the horizon changes as `η₀` times its area.  The two values are equal, `dS(p, k) = η₀ dA(p, k)`,
with the uniform `η₀` as the premise's hypothesis. -/
def local_entropy (H : Horizon L) (η : H.Cell → H.Loop → ℝ) (M : Einstein.Spacetime)
    (dS dA : M.Pt → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ η₀ : ℝ, (∀ l x, x ∈ H.cells l → η x l = η₀) → ∀ p k, Einstein.IsNull k →
    physical (dS p k) (η₀ * dA p k)

/-- `physical` for the entropy of the cosmological horizon (`hhor`; Sec. II, "The entropy": "A
horizon's entropy counts what can change in the strings that describe it, those that define its
physical laws, and by Postulate 1 all strings together do"; Sec. III.C: "the entropy per unit area
of the horizon is, to leading order in `1/L`, `η = k_B R ln 2/A_hor = k_B (L²/4) ln 2/(L²ℓ_c²/π)`",
where the order is that of `L²/4` put for the number `R` of largest rings; the premise and the
first of the two equalities are exact).  The manifold's value is the entropy that
thermodynamics assigns to the horizon of the solution without a mass, its entropy per unit area
times its area: the law `η` read at a crossing, which Postulate 2's two clauses on laws make one
value on every horizon (`Symmetry.one_density`), times `4πr_h²`, with `r_h` the horizon's radius.
The register's value is `k_B` times the entropy of the horizon's state, a state of all the
register's strings (`Bridge.horizonEntropy`).  From it `Main.jacobson_G_exact` derives the count's
density, `η = k_B R ln 2/4πr_h²` with `R` the number of largest rings, one bit for each
(`Bridge.horizon_entropy`, with the thermal state of the free strings). -/
def horizon_entropy (H : Horizon L) (R : Reg) (η : H.Cell → H.Loop → ℝ) (l₀ : H.Loop)
    (x₀ : H.Cell) (rh : ℝ) (P : (H.Loop → Bool) → ℝ) : Prop :=
  physical (η x₀ l₀ * (4 * R.pi * rh ^ 2)) (R.kB * Bridge.horizonEntropy H P)

end P1

/-! ## Postulate 2 -/
namespace P2

/-- Postulate 2: "No cell differs from another: some map of the cells that keeps the largest rings
carries any cell to any other and leaves every law unchanged" (`hsym`), for the law `f`. -/
def homogeneous (H : Horizon L) {V : Type*} (f : H.Cell → H.Loop → V) : Prop :=
  ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
    ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l

/-- Postulate 2: "No cell differs from another", for the mass energy in the cells of a string's
ring, whose cells are the type `Cell` (`hcells`; Sec. IV.C).  `held S` is the mass energy that a
measurement on the manifold finds in the cells of the set `S`, found in the bits there
(`P1.mass_in_bits`).  No cell differs from another, so the bit of each cell holds the same mass
energy: `held {x} = held {y}` for every two cells `x` and `y` of the ring.  `homogeneous` states
the same clause for a law at the register's crossings, with the maps of the cells that the
clause names.  With `P1.mass_in_bits` a set of cells holds the number of its cells times what
one cell's bit holds (`Law.mass_counts_bits`).  `Main.share_amplitude` takes the premise.  The
argument is the author's of 14 November 2026.
Sec. IV.C: "No cell differs from another (Postulate 2), so every bit counts the same." -/
def cells_hold_alike {Cell : Type*} (held : Finset Cell → ℝ) : Prop :=
  ∀ x y : Cell, held {x} = held {y}

/-- Postulate 2: "No law depends on the direction in which a ring passes through a cell" (`hdir`),
for the law `f`, on the line of the ring. -/
def directions (H : Horizon L) {V : Type*} (f : H.Cell → H.Loop → V) : Prop :=
  ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l'

/-- Postulate 2: "Every largest ring is a closed geodesic of space, made of its cells as segments of
length `ℓ_c`", with Sec. II's largest ring of `L` cells, so of length `Lℓ_c`, as a curve of de Sitter
space with the constant `Λ`: each ring's curve `γ l` is a spacelike geodesic that lies in the space
at an instant and closes with the length `Lℓ_c` (`hrings`; Secs. II and IV.D; the curves of
`Geodesics.lean`). -/
def rings_geodesics {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (H : Horizon L)
    (R : Reg) (Λ : ℝ) (γ : H.Loop → Geodesic.Curve ℝ E) : Prop :=
  ∀ l, Geodesic.IsGeodesic (3 / Λ) (γ l) ∧ Geodesic.IsSpacelike (γ l) ∧ Geodesic.InSpace (γ l) ∧
    Geodesic.HasLength (γ l) (R.L * R.ℓc)

/-- Postulate 2: "Every largest ring is a closed geodesic of space, made of its cells as segments of
length `ℓ_c`" (`hx`; Secs. II and IV.C).  A ring through the body's cell is a geodesic through the
body, so it runs out along a radial line, and its cells, segments of length `ℓ_c` of it, measure
proper distance along it: the count's horizon, `x` cells out along the ring, is the solution's
horizon, at the proper distance `σ(r_h)` from the observer (`Condition.radial_distance`). -/
def ring_distance (R : Reg) (σ : ℝ → ℝ) (rh x : ℝ) : Prop := x * R.ℓc = σ rh

/-- **The rings through the observer's cell, drawn in space** (`hdrawn`; Secs. II and IV.D):
Sec. II's ring and cell and Postulate 2's last sentence, with its first clause, at the observer's
cell `B`, on the space at an instant once it is the three-sphere of radius `√(1/K)` divided by `Γ`
(`Space.SpaceForm.sphere`; the definition is `Space.RingsDrawn`).
* "A ring is a closed line of translation in space; a cell is a place on a ring" (Sec. II), and
  "every largest ring is a closed geodesic of space, made of its cells as segments of length
  `ℓ_c`" (Postulate 2, last sentence): each largest ring through `B` runs along a great circle that
  closes in the quotient with the length `Lℓ_c`, `L` its number of cells, and its cell `j` steps
  from `B` (`Horizon.Positions.offset`, the ring's cyclic order of Postulate 1's shift) is placed
  at the arc length `jℓ_c`, where its segment begins (any other point of the segment would do, by
  starting the circle elsewhere).
* The cells of the drawn rings are places, Sec. II's "a cell is a place" read as an identity, in
  both directions: the same cell drawn on two of the rings is at one place, and two cells are two
  places.  The cells that two of the rings share are `B` itself and its opposite, "one opposite,
  the same cell halfway around every largest ring through it" (Postulate 2, first clause;
  `Horizon.Positions.offset_opp_self`, with `Horizon.inter_eq_pair`).  At the observer's cell the
  files so take a cell's place to be a point of the manifold, for the rings through it, as Sec. II
  states: "For an observer at rest, the manifold describes the register's incidence, that is,
  which rings share a cell, only for the rings through his cell".
Every cell lies on a ring through `B` (`Horizon.exists_loop_through`), so every cell is drawn, at
one place.  Nothing is said of the rings off `B`: drawn through the places of their cells as well,
the rings would draw the register's incidence with its cells as points and its rings as great
circles, which the Sylvester–Gallai theorem forbids for `L ≥ 6` [P. Erdős, Problem 4065, Amer.
Math. Monthly 50, 65 (1943); R. Steinberg, solution, ibid. 51, 169 (1944)], the reason the files
place cells on no other rings.  From the drawn rings, with the one length of every great circle
(`P1.slice_form_qubits`) and the register's incidence, `Space.sphere_rings` excludes the quotient
with the antipodal points identified: there every ring closes after half a turn, the opposite cell
sits a quarter turn from `B` on every ring through it, two rings through `B` lie on one great
circle, and the cell one step on from `B` along one falls on the place of the cell one step on, or
back, along the other: two cells at one place, so one cell on both, while two rings through `B`
share only `B` and its opposite.  The drawn
rings close with `Lℓ_c` and every great circle with `R.L ℓ_c`, so with `P1.slice_form_qubits` this
premise gives `L = R.L` (`Condition.same_L`); where that fails the two cannot both hold. -/
def rings_drawn {Sp : Type*} (H : Horizon L) (P : H.Positions) (R : Reg) (sp : Sp)
    (embedSp : (K : ℝ) → Space.SpaceForm K → Sp) (B : H.Cell) : Prop :=
  ∀ K Γ (hK : 0 < K) (hΓ : Space.SphereQuotient (1 / K) Γ),
    sp = embedSp K (Space.SpaceForm.sphere Γ hK hΓ) → Space.RingsDrawn H P (1 / K) Γ R.ℓc B

/-- Postulate 2: "No law depends on the direction in which a ring passes through a cell", for a
law of a string and the two directions of its ring (`hdir`, `hflip`).  `law σ` is what the law
gives for the state `σ` of the string, and `rev σ` is the state with the direction of the ring
reversed: the law gives the same for both.  `directions` is the same sentence for the rings
through a cell, and the free tick carries it for the phase of a string of one sense (the field
`hsense`).  `Main.sense_of_state` takes it for a law that a state obeys or does not, and
`Main.bit_kept` for the law of an interaction, the probability that it changes a sense, where
reversing the direction exchanges the two senses. -/
def direction_free {State α : Type*} (law : State → α) (rev : State → State) : Prop :=
  ∀ σ, law (rev σ) = law σ

end P2

/-! ## Thermodynamics -/
namespace Thermo

/-- A horizon is thermal: its state has the period `τ` in imaginary time and the temperature
`k_BT = ℏ/τ` (Kubo–Martin–Schwinger), and the period of a horizon of surface gravity `a` is `2πc/a`,
`L_a` ticks: the horizon of an observer held at the acceleration `a` (Unruh) or a cosmological
horizon of surface gravity `a` (Gibbons–Hawking) (`I1`; Sec. III).  For the cosmological horizon of
the solution without a mass, at its radius `r_h`, `a` is the surface gravity there, `−g(r_h)`,
whose value `Reg.surface_gravity_eq` derives, `a_Λ = c²/R_Λ`, and the period is then the lap
(`Reg.thermal_lap`). -/
def horizon_thermal (R : Reg) (a T : ℝ) : Prop := R.kB * T = R.ℏ / (R.La a * R.tc)

/-- **The energy that crosses a local horizon is heat** (`hcl`; Sec. III): Sec. III's second
thermodynamic input, on every local Rindler horizon through the point `p`, generated by the null
vector `k` and held by the boost of acceleration `a > 0` [T. Jacobson, Phys. Rev. Lett. **75**, 1260
(1995)].  The energy that crosses it is the boost-energy flux of matter,
`δQ = −(a/c²)∫ λ T_ab k^a k^b dλ dA` along its generators, and it is heat, `δQ = T dS`, at the
horizon's temperature, that of its period at the acceleration `a` (`horizon_thermal`, Unruh), with
the horizon's entropy changing as `δS = −∫ λ dS(p, k) dλ dA`.  Per unit of `−λ dλ dA`:
`(a/c²) T_ab k^a k^b = T dS(p, k)`.  Jacobson's further input, the conservation law `∇^a T_ab = 0`,
is derived from the first law (`first_law_local`, `Einstein.eq_zero_of_timelike`). -/
def local_clausius (R : Reg) (M : Einstein.Spacetime) (dS : M.Pt → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ a T, 0 < a → horizon_thermal R a T → ∀ p k, Einstein.IsNull k →
    a / R.c ^ 2 * Einstein.quad (M.stress p) k = T * dS p k

/-- The thermal state: without a mass the qubit of each string is in the thermal state of its
tick, at one inverse temperature `β` (`hthermal`, `Qubit.Tick.state`, the Gibbs state over the
string's two senses, each at the energy `En` of the factor by which the tick multiplies it,
`Qubit.Tick.energy`; `Entropy.shannon_le_shannon_gibbs` derives the Gibbs state as the state of
most entropy). -/
def thermal_state (H : Horizon L) [NeZero L] (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ)
    (ρ : H.Loop → Qubit.Op) : Prop :=
  ∀ l, ρ l = (T l).state β En

/-- Free strings: between interactions the strings are free (Postulate 1, Sec. II), and the thermal
state of systems that do not interact is the product of their own (thermodynamics), so the
horizon's thermal state is the product of the strings' own (`hfree`). -/
def free_strings (H : Horizon L) (P : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) : Prop :=
  P = Entropy.jointProb q

/-- **The first law for a component of the universe with the equation of state `w`** (Sec. VI):
its density `ρ` in the scale factor `a` obeys `d(ρa³) = −wρ d(a³)` (`first_law`, for a general
component; thermodynamics). -/
def first_law_component (ρ a : ℝ → ℝ) (w t : ℝ) : Prop :=
  HasDerivAt (fun s => ρ s * a s ^ 3) (-(w * ρ t) * deriv (fun s => a s ^ 3) t) t

/-- The probability of a string's first sense is its weight in the thermal state of its tick
(`hq`). -/
def sense_from_state (H : Horizon L) [NeZero L] (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ)
    (q : H.Loop → ℝ) : Prop :=
  ∀ l, q l = Qubit.prob ((T l).state β En) 0

/-- The first law for the cosmic fluid, `d(ρV) = −p dV`, for the component of density `ρ_Λ` with
`p = wρ_Λ` in a volume that scales as `a³` (`first_law`; Sec. VI). -/
def first_law (Rt : ℝ → Reg) (a : ℝ → ℝ) (w t : ℝ) : Prop :=
  HasDerivAt (fun s => (Rt s).ρΛ * a s ^ 3) (-(w * (Rt t).ρΛ) * deriv (fun s => a s ^ 3) t) t

/-- **The first law, for every small region and every observer** (Sec. III): energy is neither
made nor lost in a small region, only carried across its boundary, and this holds for every
observer.  The energy current of an observer `u` at rest in a local inertial frame at the point `p`
is `−T_ab u^b`, and its divergence there is `−(∇^a T_ab) u^b`; the first law makes it zero for every
timelike `u` (`hfirst`) [C. Eckart, Phys. Rev. **58**, 919 (1940); C. W. Misner, K. S. Thorne and
J. A. Wheeler, *Gravitation* (1973), Secs. 22.2 and 22.3].  `Einstein.eq_zero_of_timelike` derives
the local conservation of energy and momentum, `∇^a T_ab = 0`.  Sec. VI applies the same law to the
cosmic fluid (`first_law`), and Jacobson's step applies the Clausius relation to every local horizon
in the same way (`local_clausius`). -/
def first_law_local (M : Einstein.Spacetime) : Prop :=
  ∀ p u, Einstein.IsTimelike u → dotProduct (M.divStress p) u = 0

/-- The Deser–Levin temperature: in de Sitter space an observer held at the acceleration `a` sees
`2πT = (R⁻² + a²)^{1/2}` in units `c = ℏ = k_B = 1`, with `R` the de Sitter radius, where the
horizon is [S. Deser and O. Levin, Class. Quantum Grav. **14**, L163 (1997), Eq. (8)]; `c²/R` is the
horizon's surface gravity.  Here it is stated in the solution without a mass, with the surface
gravity of its horizon at the radius `r_h`, `−g(r_h)`: `k_BT = (ℏ/2πc)√(a² + g(r_h)²)`, the
Unruh and horizon terms combined in quadrature (`hDL`; thermodynamics of horizons with general
relativity; Sec. IV.C).  `Reg.surface_gravity_eq` derives `−g(r_h) = a_Λ`. -/
def deser_levin (R : Reg) (G Λ rh a T' : ℝ) : Prop :=
  R.kB * T' = R.ℏ / (2 * R.pi * R.c) * Real.sqrt (a ^ 2 + (-R.gSdS G 0 Λ rh) ^ 2)

/-- `I1` for the cosmological horizon about a body at rest: along the family of solutions of
`Condition.body_family`, the observer's cosmological horizon at `r s` is thermal at the temperature
of its period, `k_BT = ℏ/τ` with `τ = 2πc/a` for its surface gravity `a = −g(r s)`, the field of the
solution there, which points outward (`I1`; thermodynamics, as `horizon_thermal`; Secs. III and
IV.D). -/
def horizon_thermal_family (R : Reg) (G : ℝ) (M Λ r T : ℝ → ℝ) (s₁ : ℝ) : Prop :=
  ∀ s ∈ Set.Ioo 0 s₁, horizon_thermal R (-R.gSdS G (M s) (Λ s) (r s)) (T s)

/-- **The Clausius relation on the cosmological horizon as a mass grows inside it** (`hcl`): Sec.
III's two thermodynamic inputs, a horizon is thermal at the temperature of its period and the
energy that crosses it is heat, `δQ = T dS`, applied to the observer's cosmological horizon about a
body at rest.  As the body's mass grows by `dM`, the energy `dMc²` crosses the horizon into the
observer's region, all of it as heat, so `d(Mc²) = −T dS`, with the horizon's entropy
`S = η₀·4πr²`, the entropy density of every horizon times its area (one density on every horizon,
`Symmetry.one_density`), whatever its value.  The temperature and the entropy are those of Gibbons
and Hawking [G. W. Gibbons and S. W. Hawking, Phys. Rev. D **15**, 2738 (1977)]; their first law
holds `Λ` fixed and is not used.  With `Λ` free, the geometry gives `d(Mc²) = −T dS + V dP`
(`Reg.first_law_extended`), so the relation, which leaves no part of the energy as work, holds
exactly when `dΛ = 0` (`Reg.clausius_iff`).  Along the family of `Condition.body_family`, with the
temperatures `T s` of `horizon_thermal_family`.  Thermodynamics; `Reg.lambda_with_mass` derives from
it, with Jacobson's `G` for the same density (`Derived.jacobson_G_density`), that `Λ` does not
change as the mass grows. -/
def horizon_clausius (R : Reg) (η₀ : ℝ) (M r T : ℝ → ℝ) (s₁ : ℝ) : Prop :=
  ∀ s ∈ Set.Ioo 0 s₁, deriv (fun t => M t * R.c ^ 2) s =
    -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s

/-- **Equipartition** (`hκ`, `hκN`; Sec. IV.C): a string's share of a body's energy is
proportional to the temperature at which it holds it, `ε = κT`, with one coefficient `κ` for every
string, whether the string is a carrier at the sphere's temperature `T_a` or one of the `N_s`
strings of Newton's equal share at the Unruh temperature `T_N` of `g_N`.  With Eq. (newton) the
coefficient is `κ = 2k_B ln 2`, two Landauer energies per string
(`Reg.radial_acceleration_relation`). -/
def equipartition (κ ε T : ℝ) : Prop := ε = κ * T

/-- **The strings' energies are spread at the horizon's temperature and do not change** (`hGibbs`;
Secs. III and IV.E: "The energies the strings hold are spread at that temperature and, for matter
that stays put, do not change").  A string's energy is the same for all its states, since
Sec. II's definition of energy ties it to the one factor of the string's tick
(`P1.string_energies`), and by Sec. IV.E it differs from string to string with the
mass the string holds, from zero up.  Thermodynamics spreads the energies over the strings as the
Gibbs distribution at the horizon's temperature `T`, the weight `e^{−E/k_BT}` on the energy `E`, so
their mean `ε̄` is the mean of that distribution, `Law.gibbsMean (k_BT)`, which `Law.gibbsMean_eq`
evaluates as `k_BT`; on a ladder of equal steps the mean lies within one step of it
(`Law.gibbsLadder_within_step`).  The fraction of the strings whose energy exceeds `x` is that
distribution's too, `above x = Law.gibbsAbove (k_BT) x`, which `Law.gibbsAbove_eq` evaluates as
`e^{−x/k_BT}`; `Main.carriers_exact` and `Main.galactic_law` take it for the strings whose phase
holds against a body's share.  The energies do not change, since the paper treats matter that
stays put, with
interactions negligible (Sec. II), so their spread, a difference between strings and not a change
in time, is no part of the entropy that the horizon exchanges: that entropy
counts what can change, the sense, one bit per ring (`Bridge.horizon_entropy`).  The heat of a
string, the horizon's temperature times that bit, is derived separately (`Reg.vacuum_per_string`,
`Reg.string_split`).  This premise takes the place of Penrose's relation and the reduction clock
of the versions up to v18-56. -/
def energies_thermal (R : Reg) (T εbar : ℝ) (above : ℝ → ℝ) : Prop :=
  εbar = Law.gibbsMean (R.kB * T) ∧ ∀ x, 0 ≤ x → above x = Law.gibbsAbove (R.kB * T) x

end Thermo

/-! ## Quantum mechanics: the gates (Secs. III and IV.A) -/
namespace QM

/-- **The gates** (`hgates`; Sec. III: "Quantum mechanics: the gates, which act on what the
register holds as on any state"; Sec. IV.A: "A circuit acts on what the register holds as it acts
on any state, an input of Sec. III").  The test of Sec. IV.A runs a random circuit and then its
inverse.  `V` is the inverse circuit without error, as a map on the states, the amplitudes of
the joint outcomes.  A circuit of gates keeps the overlap `⟨a|b⟩ = ∑ ā_ω b_ω` of every two
states, and the inverse takes the random state `ψ`, which the circuit calls for, back to the
initial state `init`.  The gates act on what the register holds, the state `held`, as on any
state: a run without error leaves `V held`.  A run is without error with the probability `F`,
the gate fidelity, and the paper counts a return in such a run alone: "In quantum mechanics the
state returns to the initial one with the gate fidelity, the probability of a run without error".
So the probability `ret` that the test returns the initial state is `F |⟨init|V held⟩|²`.  Where
what the register holds is the state `ψ` that the circuit calls for, `Main.return_bound` derives
`ret = F` from the premise.  `Main.return_bound` takes the premise. -/
def gates {Ω : Type*} [Fintype Ω] (V : (Ω → ℂ) → Ω → ℂ) (ψ init held : Ω → ℂ) (F ret : ℝ) :
    Prop :=
  (∀ a b : Ω → ℂ, ∑ ω, (starRingEnd ℂ) (V a ω) * V b ω = ∑ ω, (starRingEnd ℂ) (a ω) * b ω) ∧
    V ψ = init ∧ 0 ≤ F ∧ ret = F * ‖∑ ω, (starRingEnd ℂ) (init ω) * V held ω‖ ^ 2

end QM

/-! ## The mathematics of the manifold: Lorentzian geometry and Riemannian geometry

What the paper takes from general relativity is mathematics, no law: theorems of the geometry of
the manifold that Postulate 2 names, a smooth, connected Lorentzian 4-manifold whose
space at an instant of an observer at rest is a slice, with light on its null directions
(Postulate 1).  Each is a published theorem, stated here with its inputs where the files can
state them, every input derived in the files, a sentence of the postulates, or a condition of the
result: Lorentzian geometry [R. M. Wald, *General Relativity* (1984); S. Weinberg, *Gravitation and
Cosmology* (1972); B. O'Neill, *Semi-Riemannian Geometry* (1983)] for the Raychaudhuri equation,
the contracted Bianchi identity, the Leibniz rule, the curvature of a static spherical metric and
of a static weak field, the Newtonian limit of the geodesic equation, the totally geodesic slices
of a static spacetime and the Gauss equation; Riemannian geometry [J. M. Lee, *Introduction to
Riemannian Manifolds* (2018); H. Hopf (1926)] for Schur's lemma, Hopf–Rinow and the Killing–Hopf
theorem on the space at an instant.  Einstein's equations themselves are
derived (`Einstein.einstein_equations`, from Jacobson's step and the first law), and so is the
Schwarzschild–de Sitter solution (`Schwarzschild.static_vacuum`); the Misner–Sharp and Komar
energies are that geometry's definitions, `Reg.EMS` and `Reg.EK` (`Cosmo.lean`), evaluated on it.
Lean has no Lorentzian geometry in which to prove these theorems. -/
namespace Geometry

/-- **The Raychaudhuri equation on a local horizon** (`hray`; Sec. III) [R. M. Wald, *General
Relativity* (1984), Sec. 9.2]: the local Rindler horizon through the point `p`, generated by the
null vector `k` with no expansion and no shear at `p`, changes its area, to first order in the
affine parameter `λ` of its generators, as `δA = −∫ λ R_ab k^a k^b dλ dA`; `dA(p, k)` is that
coefficient, `R_ab k^a k^b`.  Mathematics of the metric. -/
def raychaudhuri (M : Einstein.Spacetime) (dA : M.Pt → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ p k, Einstein.IsNull k → dA p k = Einstein.quad (M.ric p) k

/-- **The contracted Bianchi identity, with matter** (`hbianchi`): on the spacetime, a connected
Lorentzian manifold of dimension four, let `R_ab − κT_ab = φ g_ab` at every point.  The contracted
Bianchi identity `∇^a R_ab = ½∇_b R` [R. M. Wald, *General Relativity* (1984), Sec. 3.2], with
`R = κT + 4φ`, gives `∇_b(φ + ½κT) = κ∇^a T_ab`; where `∇^a T_ab = 0`, the function `φ + ½κT` has
no gradient, so it is one number on the connected spacetime.  Mathematics of the metric. -/
def bianchi (M : Einstein.Spacetime) : Prop :=
  ∀ (κ : ℝ) (φ : M.Pt → ℝ),
    (∀ p, M.ric p - κ • Einstein.symmPart (M.stress p) = φ p • Einstein.eta) →
    (∀ p, M.divStress p = 0) →
    ∀ p q, φ p + κ / 2 * Einstein.trace (Einstein.symmPart (M.stress p)) =
      φ q + κ / 2 * Einstein.trace (Einstein.symmPart (M.stress q))

/-- **The Leibniz rule for a flow** (`hleib`): where the stress tensor at `p` is `ρ v_a v_b`, with
`v` the four-velocity of matter (`v·v = −1`) or the direction of light (`v·v = 0`), its divergence
is `∇^a T_ab = D v_b + ρ A_b`, with `D = ∇_a(ρv^a)` and `A_b = v^a∇_a v_b` the acceleration of the
flow, here `A`; and `A_b v^b = ½v^a∇_a(v^b v_b) = 0`, since `v·v` is the same along the flow
[R. M. Wald, *General Relativity* (1984), Sec. 4.3].  Mathematics of the covariant derivative. -/
def leibniz (M : Einstein.Spacetime) (p : M.Pt) (v A : Fin 4 → ℝ) : Prop :=
  (∀ ρ : ℝ, Einstein.symmPart (M.stress p) =
      ρ • Matrix.vecMulVec (Matrix.mulVec Einstein.eta v) (Matrix.mulVec Einstein.eta v) →
    ∃ D : ℝ, M.divStress p = D • Matrix.mulVec Einstein.eta v + ρ • A) ∧
  dotProduct A v = 0

/-- the Leibniz rule (`leibniz`) along the worldlines `wl r` of the bodies on the orbits of radius
`r`, at every time `t`, for their four-velocities `u r t` and accelerations `A r t` (`hleib`) -/
def leibniz_orbits (M : Einstein.Spacetime) (wl : ℝ → ℝ → M.Pt) (u A : ℝ → ℝ → Fin 4 → ℝ) :
    Prop :=
  ∀ r t, leibniz M (wl r t) (u r t) (A r t)

/-- **Geodesic motion in a static weak field** (`hmotion`): a slow body that moves on a geodesic
(acceleration `A = 0` along its worldline) in a static weak field has the acceleration of the
field, `g` toward the center: `ẍ = −(g/r) x` for its position `x` in the plane of its orbit, `r`
from the center [R. M. Wald, *General Relativity* (1984), Sec. 4.4a, the Newtonian limit of the
geodesic equation].  Here for the bodies on the orbits `x r` of radius `r`, in the field `g r`. -/
def newtonian_motion (A : ℝ → ℝ → Fin 4 → ℝ) (x : ℝ → ℝ → ℝ × ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → (∀ t, A r t = 0) → ∀ t, deriv (deriv (x r)) t = (-(g r / r)) • x r t

/-- **A body at rest, alone: the static, spherically symmetric solution** (`hss`).  About a
spherical body at rest, alone, the solution is static and spherically symmetric: outside the body
its metric is `−e^{2α(r)}c²dt² + e^{2β(r)}dr² + r²dΩ²`, with `r` the areal radius, which grows
outward, so that Nariai's solution, whose spheres do not grow, is not this one [R. M. Wald,
*General Relativity* (1984), Sec. 6.1].  At the point `pt r` at the radius `r`, `a < r < b`, the
Ricci tensor in the frame of the observers at rest is that metric's, `Schwarzschild.ricSS α β r`,
the textbook formula; `α` and `β` are differentiable, the manifold being smooth (Sec. II).  The
situation is a condition of the result; the curvature is mathematics of the metric. -/
def static_spherical (M : Einstein.Spacetime) (pt : ℝ → M.Pt) (α β : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ r ∈ Set.Ioo a b, DifferentiableAt ℝ α r ∧ DifferentiableAt ℝ β r ∧
    M.ric (pt r) = Schwarzschild.ricSS α β r

/-- **The static weak field** (linearized gravity): about matter at rest in a static weak field,
`ds² = −(1 + 2Φ/c²)c²dt² + (1 − 2Ψ/c²)dx²`, the Ricci tensor is `R₀₀ = ∇²Φ/c²` and
`Rᵢⱼ = (∂ᵢ∂ⱼ(Φ − Ψ) + δᵢⱼ∇²Ψ)/c²`; the field equations up to a multiple of the metric
(`Einstein.TraceFree`), whose spatial part without its trace has no source from matter at rest, give
`Φ = Ψ` for fields that vanish far from the matter; so at a point `p` of it the Ricci tensor is
`A = ∇²Φ/c²` times the identity (`hweak`) [R. M. Wald, *General Relativity* (1984), Sec. 4.4a;
S. Weinberg, *Gravitation and Cosmology* (1972), Sec. 7.1]. -/
def weak_field (M : Einstein.Spacetime) (p : M.Pt) (A : ℝ) : Prop :=
  ∀ κ : ℝ, Einstein.TraceFree M κ → M.ric p = A • (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- **The Killing–Hopf theorem for the space at an instant**: a connected Riemannian 3-manifold whose
geometry is the same at every place and in every direction has one constant curvature `K` (Schur's
lemma); if every geodesic closes, it is complete (Hopf–Rinow); and a complete connected
Riemannian 3-manifold of constant curvature is a space form, `Space.SpaceForm` (`hKH`) [J. M. Lee,
*Introduction to Riemannian Manifolds*, 2nd ed. (2018), p. 348; H. Hopf, Math. Ann. **95**, 313
(1926)].  Its inputs are proved or taken from the postulates: the geometry the same at every slot is
proved (`Solution.geometry_same`), and every geodesic closed is Postulate 1's first sentence applied
to the space at an instant (`hclose`, `P1.slice_qubits`).  The dimension three is the paper's, taken
as observed (Sec. IV.D). -/
def space_form {Slot Gm Sp : Type*} (geom : Slot → Gm) (Closes : Slot → Prop) (sp : Sp)
    (embedSp : (K : ℝ) → Space.SpaceForm K → Sp) : Prop :=
  (∀ σ τ : Slot, geom σ = geom τ) → (∀ σ, Closes σ) → ∃ K, ∃ c : Space.SpaceForm K, sp = embedSp K c

/-- **Einstein's constraint on the space at an instant**: the space at an instant of an observer at
rest is totally geodesic, since the geometry about him does not change in time (Sec. II) and the
slices of a static spacetime are [B. O'Neill, *Semi-Riemannian Geometry* (1983), Prop. 7.35 and
Ch. 12]; on a totally geodesic slice without matter the Gauss equation with Einstein's equations
gives the scalar curvature `2Λ` [R. M. Wald, *General Relativity* (1984), Sec. 10.2], and a space form
of curvature `K` has scalar curvature `6K`; so `3K = Λ` (`hcon`).  Its input, the vacuum equations
with `Λ`, is derived (`Einstein.einstein_equations`, `Einstein.vacuum_of_field_equations`). -/
def constraint {Sp : Type*} (M : Einstein.Spacetime) (Λ : ℝ) (sp : Sp)
    (embedSp : (K : ℝ) → Space.SpaceForm K → Sp) : Prop :=
  Einstein.VacuumEinstein M Set.univ Λ → ∀ K (c : Space.SpaceForm K), sp = embedSp K c → 3 * K = Λ

end Geometry

/-! ## Results derived in `Main.lean` from the sources, which other results take by name -/
namespace Derived

/-- Newton's constant from Jacobson's step with the entropy density `η₀` of every local horizon,
whatever its value: `G = c³k_B/(4ℏη₀)` (`hJ`; derived in `Main.jacobson_G_density` from Postulate 2,
thermodynamics and the cited geometry, for the density the register's law has at a cell).  `jacobson_G` and
`jacobson_G_exact` are this at the count's density, at leading order and exactly. -/
def jacobson_G_density (R : Reg) (G η₀ : ℝ) : Prop := G = R.c ^ 3 * R.kB / (4 * R.ℏ * η₀)

/-- Newton's constant from Jacobson's step with the count's entropy density to leading order in
`1/L`, `G = c³k_B/(4ℏη)` (`hJ`; derived in `Main.jacobson_G` from Postulate 2, thermodynamics and the cited geometry, with
the leading-order step `Approx.count_density`).  The results that take it are stated at that order,
as the paper's equations are; `Main.G_leading_order` bounds the step. -/
def jacobson_G (R : Reg) (G : ℝ) : Prop := G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)

/-- Newton's constant from Jacobson's step with the count's exact entropy density, that of its
`L²/4 − L/2 + 1` rings: `G = c³k_B/(4ℏη(1 − 2/L + 4/L²))` (`hJ`; derived in `Main.jacobson_G_exact`). -/
def jacobson_G_exact (R : Reg) (G : ℝ) : Prop :=
  G = R.c ^ 3 * R.kB / (4 * R.ℏ * (R.η * (1 - 2 / R.L + 4 / R.L ^ 2)))

/-- **Jacobson's step at every point** (`hcl`; derived in `Main.jacobson_step` from the Raychaudhuri
equation, the heat that crosses a local horizon and the register's entropy on it): with one entropy
density `η₀ ≠ 0` on every local horizon, `R_ab k^a k^b = κ T_ab k^a k^b` for every null `k` at
every point, with `κ = 2πk_B/(ℏcη₀)`. -/
def clausius (H : Horizon L) (R : Reg) (η : H.Cell → H.Loop → ℝ) (M : Einstein.Spacetime) : Prop :=
  ∀ η₀ : ℝ, η₀ ≠ 0 → (∀ l x, x ∈ H.cells l → η x l = η₀) → ∀ p k, Einstein.IsNull k →
    Einstein.quad (M.ric p) k = (2 * R.pi * R.kB / (R.ℏ * R.c * η₀)) * Einstein.quad (M.stress p) k

/-- The constant `Λ` of a solution has the value that puts the horizon of the solution without a
mass at `R_Λ`, where the de Sitter solution's `f` vanishes: `Λ = 3/R_Λ²` (`hdS`; derived in
`Main.deSitter_horizon` for the solution without a mass, and in `Main.lambda_with_mass` for the
solution about a body at rest, whose constant is the same). -/
def deSitter_horizon (R : Reg) (G Λ : ℝ) : Prop := R.fSdS G 0 Λ R.RL = 0

/-- **The solution about a body at rest is Schwarzschild–de Sitter** (`hsol`; derived in
`Main.schwarzschild_deSitter` from Einstein's equations, which are derived): between the radii `a`
and `b` about the body, the metric `−e^{2α}c²dt² + e^{2β}dr² + r²dΩ²` has `e^{2α} = e^{−2β} = f`,
the metric function `Reg.fSdS G M Λ` with the parameters `M` and `Λ`.  `Main.schwarzschild_deSitter`
concludes it for some `Λ` and some `M`, and `Main.komar_mass` takes it for the parameters that
the metric has. -/
def schwarzschild_deSitter (R : Reg) (G M Λ : ℝ) (α β : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ r ∈ Set.Ioo a b, Real.exp (2 * α r) = R.fSdS G M Λ r ∧ Real.exp (-2 * β r) = R.fSdS G M Λ r

/-- The acceleration is `g_N/b`, Eq. (share): fewer carriers, the same energy, a higher temperature
(`hab`; derived in `Main.carriers_share`).  `Main.scale_mean` and `Main.classical_share` take it
with an alternative threshold or share in place of `b`, and `Main.law_bounds` and
`Main.law_whole_bits` with the carriers' exact fraction. -/
def share_acceleration (a gN b : ℝ) : Prop := a = gN / b

/-- The body's energy per string in units of the mean string's matter (`Reg.matter`) is `g_N/a₀`,
Eq. (f) (`hf`; derived in `Main.fill_fraction`); `Main.scale_mean`, `Main.law_bounds` and
`Main.law_whole_bits` take it. -/
def fill_fraction (R : Reg) (gN TN εs : ℝ) : Prop :=
  2 * R.kB * TN * R.ln2 / R.matter εs = gN / R.a0

/-- The exact amplitude of a body's share at a string of `n` bits (`hh`; derived in
`Main.share_amplitude`), with `E = 2k_BT_N ln 2` the body's energy per string of the sphere
(Eq. (E)) and `u` the matter that a string holds on average (`Reg.matter`).  For a share that
one string can hold, `E ≤ u`, `h` is the amplitude of the whole bits that the share fills
(`P1.share_bits`): `h` is not negative, `h²` is a whole number of bits over `n`, and
`E/u − 1/n < h² ≤ E/u`, so `h²` is the largest such fraction that does not exceed `E/u`.  For a
larger share, `E > u`, `h = √(E/u)`, the paper's definition of `h` on the same scale, which
`Main.share_amplitude` takes as a condition (`Condition.same_scale`).
`Main.share_leading_order` takes the statement and bounds the step from it to `h = √(E/u)`
(`Approx.share_amplitude`), and `Main.law_whole_bits` takes it on a largest ring, `n = L`, and
bounds what that step changes in the law.  Up to v18-69 the files took `h = √(E/u)` as one
premise, `P1.share_amplitude`.  Sec. IV.C: "The strings hold the matter `u` per string, on the `L` bits of one whole qubit, so for `f ≤ 1` a
string's share of the body, `E = fu`, fills the fraction `f` of its bits, to within one bit."
Data availability: "For Sec. IV.C the files count mass energy in bits, each step of the count a
named hypothesis, and derive from it the amplitude of a body's share, where one string's bits
hold the share." -/
def share_amplitude_exact (R : Reg) (n : ℕ) (h TN εs : ℝ) : Prop :=
  (2 * R.kB * TN * R.ln2 ≤ R.matter εs →
    0 ≤ h ∧ (∃ m : ℕ, h ^ 2 = m / n) ∧
      2 * R.kB * TN * R.ln2 / R.matter εs - 1 / n < h ^ 2 ∧
      h ^ 2 ≤ 2 * R.kB * TN * R.ln2 / R.matter εs) ∧
  (R.matter εs < 2 * R.kB * TN * R.ln2 →
    h = Real.sqrt (2 * R.kB * TN * R.ln2 / R.matter εs))

/-- The carriers are the fraction
`b = (1 − e^{−L arcsin(h/L)})(1 + (e^{L arcsin(h/L)} + 1)/(e^{2πL} − 1))` of the sphere's
strings, with `h` the amplitude of the body's share (`hb`).  It is the fraction of the strings
whose phase holds against the share, over every turn of the phase per tick, exactly;
`Main.carriers_exact` derives it from the share's parts per tick, the rule of the phase and the
spread of the strings' energies.  The first factor is the fraction of the strings whose energy
is at most the threshold `(ℏ/t_c) arcsin(h/L)`.  The second factor adds the strings whose turn
per tick lies within `arcsin(h/L)` of one or more whole turns, a fraction below `e^{−3πL/2}`
of the strings.  The leading order of `b` in `1/L` is `1 − e^{−h}`, Eq. (b)
(`Approx.carriers_leading`).  `Main.carriers_leading_order`, `Main.law_bounds` and
`Main.law_whole_bits` take it. -/
def carriers_exact (R : Reg) (b h : ℝ) : Prop :=
  b = (1 - Real.exp (-(R.L * Real.arcsin (h / R.L)))) *
    (1 + (Real.exp (R.L * Real.arcsin (h / R.L)) + 1) / (Real.exp (2 * Real.pi * R.L) - 1))

/-- The acceleration about a mass is that of Eq. (law), `a = g_N/(1 − e^{−√(g_N/a₀)})`, with `g_N`
Newton's field of the mass (`hlaw`; derived in `Main.galactic_law`, with the carriers' fraction
and the amplitude of the body's share to leading order in `1/L`, `Approx.carriers_leading` and
`Approx.share_amplitude`).  `Main.near_limit` and `Main.deep_limit` take it.  `Main.law_bounds`
bounds the step of the carriers' fraction, and `Main.share_leading_order` that of the
amplitude; `Main.law_whole_bits` bounds what the two steps together change in the law. -/
def galactic_law (R : Reg) (a gN : ℝ) : Prop :=
  a = gN / (1 - Real.exp (-Real.sqrt (gN / R.a0)))

/-- The speeds `v r` of the bodies on circular orbits in a static field `g r` toward the center
obey `v² = gr` (`hv`; derived in `Main.rotation_curve` from geodesic motion).  Sec. IV.C takes it
with the field of Eq. (law), and in the deep regime with `g = √(a₀g_N)`. -/
def circular_speeds (g v : ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → v r ^ 2 = g r * r

/-- `Λ = 3/R_Λ²` at every time: the register `Rt s` at the time `s` has its horizon at its `R_Λ`.
By definition it is `deSitter_horizon` for the register at each time.  `Main.deSitter_horizon`
concludes that statement from its premises; a result that takes this one supposes them at every
time, which the build does not check. -/
def deSitter_horizon_in_time (Rt : ℝ → Reg) (G Λ : ℝ → ℝ) : Prop :=
  ∀ s, deSitter_horizon (Rt s) (G s) (Λ s)

/-- `G = c³k_B/4ℏη` at every time, with the register's density at that time.  By definition it is
`jacobson_G` for the register at each time.  `Main.jacobson_G` concludes that statement from its
premises; a result that takes this one supposes them at every time, which the build does not
check. -/
def jacobson_G_in_time (Rt : ℝ → Reg) (G : ℝ → ℝ) : Prop :=
  ∀ s, jacobson_G (Rt s) (G s)

end Derived

/-! ## Conditions that define the quantity a result treats -/
namespace Condition

/-- the register's `L` is the ring's -/
def same_L (R : Reg) (L : ℕ) : Prop := R.L = L

/-- a cell on a ring -/
def on_ring (H : Horizon L) (l₀ : H.Loop) (x₀ : H.Cell) : Prop := x₀ ∈ H.cells l₀

/-- `r_h` is the radius of the horizon of the solution without a mass: `r_h > 0`, and the metric
function `f` vanishes there -/
def horizon_radius (R : Reg) (G Λ rh : ℝ) : Prop := 0 < rh ∧ R.fSdS G 0 Λ rh = 0

/-- a positive number -/
def pos (x : ℝ) : Prop := 0 < x

/-- two cells that are neither equal nor opposite -/
def not_opposite (H : Horizon L) (x y : H.Cell) : Prop := y ≠ x ∧ y ≠ H.opp x

/-- two points of the sphere of radius `ρ` about the origin, neither equal nor antipodal -/
def two_points {E : Type*} [NormedAddCommGroup E] (ρ : ℝ) (p q : E) : Prop :=
  0 < ρ ∧ ‖p‖ = ρ ∧ ‖q‖ = ρ ∧ q ≠ p ∧ q ≠ -p

/-- `L ≥ 6`: the register is a projective plane for `L ≥ 6` (Sec. II) -/
def six_le (L : ℕ) : Prop := 6 ≤ L

/-- the field of the solution about the mass vanishes at the radius `r_z` -/
def zero_field (R : Reg) (G M Λ rz : ℝ) : Prop := R.gSdS G M Λ rz = 0

/-- the premise of the alternative that Sec. IV.C rejects: gravity follows the excess of the
Deser–Levin temperature `T′` of an observer held at an acceleration over the floor `T_dS`, the
horizon's temperature, so that the Unruh temperature `T_N` of Newton's field is that excess,
`T′ − T_dS = T_N`.  The acceleration is no argument of the condition: `Main.temperature_led` takes
`T′` at it in the premise `Thermo.deser_levin`. -/
def temperature_led (T' TdS TN : ℝ) : Prop := T' - TdS = TN

/-- `P` is a distribution on the configurations: nonnegative, of total one -/
def distribution {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) : Prop := (∀ ω, 0 ≤ P ω) ∧ ∑ ω, P ω = 1

/-- `P` has the mean energy of the Gibbs distribution at `β` -/
def same_mean {Ω : Type*} [Fintype Ω] (E : Ω → ℝ) (β : ℝ) (P : Ω → ℝ) : Prop :=
  ∑ ω, P ω * E ω = ∑ ω, Entropy.gibbs E β ω * E ω

/-- the thermal state of the tick written as a mixture of strings, the string `s` with `m s` 1s and
the position `n s`, with the weight `p s` -/
def string_mixture {S : Type*} [Fintype S] (T : Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (m n : S → ℕ)
    (p : S → ℝ) : Prop :=
  T.state β En = ∑ s, (p s : ℂ) • Qubit.proj (Qubit.stringState L (m s) (n s))

/-- a code of distance at least two -/
def two_le (d : ℕ) : Prop := 2 ≤ d

/-- the random state the ceiling is stated for, on `N` logical qubits read through a line code:
every outcome `k` of the earlier logical qubits occurs, the last logical bit is uncertain given it,
and the `2^N` conditional probabilities differ -/
def line_random {K W : Type*} (N : ℕ) (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ) : Prop :=
  1 ≤ N ∧ (∀ k t, 0 < p k t) ∧ (∀ k, ∃ w, κ w = k ∧ g w ≠ 0) ∧
    Function.Injective (fun σ : K × ZMod 2 => Coding.caseProb (p σ.1) σ.2)

/-- the scale factor `a` with its rate `ȧ`, a function, and its second rate `ä` at `t`: `a` and
`ȧ` nonzero, `ȧ` the derivative of `a` and `ä` of `ȧ` -/
def deceleration (a adot : ℝ → ℝ) (addot t : ℝ) : Prop :=
  a t ≠ 0 ∧ adot t ≠ 0 ∧ HasDerivAt a (adot t) t ∧ HasDerivAt adot addot t

/-- a component of the universe with the density `ρ`, in the expanding scale factor `a`, at `t`:
`a` and `ρ` nonzero, the expansion rate `ȧ/a` positive, `ρ̇` and `ȧ` the derivatives -/
def component (ρ a : ℝ → ℝ) (ρdot adot t : ℝ) : Prop :=
  a t ≠ 0 ∧ ρ t ≠ 0 ∧ 0 < adot / a t ∧ HasDerivAt ρ ρdot t ∧ HasDerivAt a adot t

/-- the density's rate of change is bounded, `|ρ̇/ρ| ≤ b` -/
def drift_bound (ρ : ℝ → ℝ) (ρdot t b : ℝ) : Prop := |ρdot / ρ t| ≤ b

/-- `G` and `Λ` have the rates `G′` and `Λ′` at `t`, and neither is zero there -/
def rates_at (G Λ : ℝ → ℝ) (G' Λ' t : ℝ) : Prop :=
  HasDerivAt G G' t ∧ HasDerivAt Λ Λ' t ∧ G t ≠ 0 ∧ Λ t ≠ 0

/-- a block of one cell -/
def one_cell {α : Type*} (B : Finset α) : Prop := B.card = 1

/-- the type `K` of the joint outcomes of the first `N − 1` logical qubits has `2^{N−1}` elements -/
def card_outcomes (K : Type*) [Fintype K] (N : ℕ) : Prop := Fintype.card K = 2 ^ (N - 1)

/-- matter at rest of density `ρ ≠ 0` at the point `p`: the stress tensor there is
`diag(ρc², 0, 0, 0)` -/
def dust (R : Reg) (M : Einstein.Spacetime) (p : M.Pt) (ρ : ℝ) : Prop :=
  ρ ≠ 0 ∧ M.stress p = Matrix.diagonal ![ρ * R.c ^ 2, 0, 0, 0]

/-- Newton's constant `G` is the coefficient of Newton's law of gravitation in the static weak
field, `∇²Φ = 4πGρ`, with `A = ∇²Φ/c²` -/
def newton_G (R : Reg) (G A ρ : ℝ) : Prop := A = 4 * R.pi * G * ρ / R.c ^ 2

/-- the solution without a mass: no matter anywhere -/
def no_matter (M : Einstein.Spacetime) : Prop := ∀ p, M.stress p = 0

/-- `Λ` names the constant of the vacuum equations: `R_ab = Λ g_ab` at some point -/
def vacuum_constant (M : Einstein.Spacetime) (Λ : ℝ) : Prop :=
  ∃ p, M.ric p = Λ • Einstein.eta

/-- the acceleration `a` that the result treats is the pull of the mass at the radius `r`: the field
it adds to the solution without it, at the solution's constant `Λ` (`Reg.pull`) -/
def pull_of (R : Reg) (G M Λ r a : ℝ) : Prop := a = R.pull G M Λ r

/-- the universe expands at the time `t`: the rate `ȧ/a` is not zero -/
def expanding (a : ℝ → ℝ) (adot t : ℝ) : Prop := adot / a t ≠ 0

/-- the scale factor has the derivative `ȧ` at `t` -/
def scale_factor_rate (a : ℝ → ℝ) (adot t : ℝ) : Prop := HasDerivAt a adot t

/-- at least one logical qubit -/
def one_le (N : ℕ) : Prop := 1 ≤ N

/-- matter moving as dust at the point `p`: unit four-velocity `u` (`η(u,u) = −1`), density
`ρ ≠ 0`, stress tensor `ρ u_a u_b` -/
def dust_flow (M : Einstein.Spacetime) (p : M.Pt) (u : Fin 4 → ℝ) (ρ : ℝ) : Prop :=
  Einstein.quad Einstein.eta u = -1 ∧ ρ ≠ 0 ∧
    Einstein.symmPart (M.stress p) =
      ρ • Matrix.vecMulVec (Matrix.mulVec Einstein.eta u) (Matrix.mulVec Einstein.eta u)

/-- **Light whose energy moves with it along its ray, for every observer**, at the point `p`, with
`k` the direction of its ray: the case that `Main.light_rays` treats, as `dust_flow` is the case of
dust (Sec. III.B: "For light whose energy moves with it along its ray, for every observer, the
stress tensor is `ρk_μk_ν`, with `k` the tangent of the ray, and conservation makes its rays null
geodesics").  For every timelike
observer `u` the energy current of the light, `T_ab u^b`, is a multiple of `k_a = η_ab k^b`; light
carries energy, so its stress tensor is not zero; and `p` is a point where this light alone passes,
so that `M.stress p` is its stress tensor.  Sec. II gives energy to a state, the generator of its
tick, and does not place it in cells, so the files do not derive this from the postulates: it is a
condition of the result.  From it `Einstein.null_dust_of_current` derives `T_ab = ρk_ak_b` with
`ρ ≠ 0`. -/
def light_flow (M : Einstein.Spacetime) (p : M.Pt) (k : Fin 4 → ℝ) : Prop :=
  Einstein.symmPart (M.stress p) ≠ 0 ∧
    ∀ u, Einstein.IsTimelike u →
      ∃ s : ℝ, Matrix.mulVec (Einstein.symmPart (M.stress p)) u = s • Matrix.mulVec Einstein.eta k

/-- the bodies on the orbits of radius `r` move as dust (`dust_flow`) along their worldlines
`wl r`, at every time -/
def dust_orbits (M : Einstein.Spacetime) (wl : ℝ → ℝ → M.Pt) (u : ℝ → ℝ → Fin 4 → ℝ)
    (ρ : ℝ → ℝ → ℝ) : Prop :=
  ∀ r t, dust_flow M (wl r t) (u r t) (ρ r t)

/-- the body at the radius `r` moves on the circle of radius `r` at the speed `v r` -/
def circular_orbits (x : ℝ → ℝ → ℝ × ℝ) (v : ℝ → ℝ) : Prop := ∀ r, x r = Motion.circle r (v r)

/-- `ρ(s)` is the areal radius of the sphere about the body at geodesic distance `s` from its
center, from the body's surface at `s = b` out to `r > b`: `ρ(b) > 0`, and, since the radial part
`dr²/f` of the metric of the solution about the body makes a step `ds` of geodesic distance a step
`√f ds` of the areal radius, `dρ/ds = √f(ρ)`, with `f > 0` there, between the horizons.  The metric
is the derived solution's (`Main.schwarzschild_deSitter`): a definition through the derived
solution, no premise beyond it -/
def areal_radius (R : Reg) (G M Λ : ℝ) (ρ : ℝ → ℝ) (b r : ℝ) : Prop :=
  b < r ∧ 0 < ρ b ∧ ∀ s ∈ Set.Icc b r,
    0 < R.fSdS G M Λ (ρ s) ∧ HasDerivAt ρ (Real.sqrt (R.fSdS G M Λ (ρ s))) s

/-- `D(s)` is the shortfall of the sphere at geodesic distance `s`, from the body's surface `b` out
to `r`: it grows at the rate by which the sphere's area `4πρ(s)²` grows more slowly with geodesic
distance than that of a sphere of the same area in the solution without the mass, at the same
`Λ`, whose rate is `8πρ√f₀(ρ)` (`Reg.areaRate`).  Both rates are those of the derived solution's
metric (`Main.schwarzschild_deSitter`): a definition through the derived solution -/
def shortfall (R : Reg) (G Λ : ℝ) (ρ D : ℝ → ℝ) (b r : ℝ) : Prop :=
  ∀ s ∈ Set.Icc b r,
    HasDerivAt D (R.areaRate G 0 Λ (ρ s) - deriv (fun t => 4 * R.pi * ρ t ^ 2) s) s

/-- no matter between the radii `a` and `b` about the body: it lies inside `a` -/
def empty_outside (M : Einstein.Spacetime) (pt : ℝ → M.Pt) (a b : ℝ) : Prop :=
  ∀ r ∈ Set.Ioo a b, M.stress (pt r) = 0

/-- the unit of the time coordinate is Schwarzschild's: `α + β = 0`, so that `g_tt g_rr = −c²`,
at a radius between `a` and `b` -/
def schwarzschild_time (α β : ℝ → ℝ) (a b : ℝ) : Prop := ∃ r ∈ Set.Ioo a b, α r + β r = 0

/-- **A family of bodies at rest whose mass grows from zero** (`hfam`): for `0 ≤ s ≤ s₁`, the
solution about a body of mass `M s` at rest, alone, Schwarzschild–de Sitter with its own constant
`Λ s` (`Main.schwarzschild_deSitter`), with `M 0 = 0`, so that the first is the solution without a
mass; the family varies smoothly, `Λ` continuously on `[0, s₁]` and `M`, `Λ` and the horizon `r`
differentiably inside; and `r s > 0` is the observer's cosmological horizon, a zero of the metric
function `f` where the field `g = (c²/2) f′` points outward, `g < 0`.  The states compared by the
Clausius relation, as thermodynamics compares equilibrium states.  The metric function and the
field are the derived solution's (`Main.schwarzschild_deSitter`). -/
def body_family (R : Reg) (G : ℝ) (M Λ r : ℝ → ℝ) (s₁ : ℝ) : Prop :=
  M 0 = 0 ∧ ContinuousOn Λ (Set.Icc 0 s₁) ∧
    ∀ s ∈ Set.Ioo 0 s₁, DifferentiableAt ℝ M s ∧ DifferentiableAt ℝ Λ s ∧
      DifferentiableAt ℝ r s ∧ 0 < r s ∧ R.fSdS G (M s) (Λ s) (r s) = 0 ∧
        R.gSdS G (M s) (Λ s) (r s) < 0

/-- `s` is one of the family and not an end, `0 < s < s₁` -/
def inside_family (s s₁ : ℝ) : Prop := s ∈ Set.Ioo 0 s₁

/-- `s` is one of the family, `0 ≤ s ≤ s₁` -/
def member (s s₁ : ℝ) : Prop := s ∈ Set.Icc 0 s₁

/-- the mass is small against the radius of the horizon: `13GM/c² < R_Λ` (the paper treats
`GM/c² ≪ R_Λ`) -/
def small_mass (R : Reg) (G M : ℝ) : Prop := 13 * (G * M / R.c ^ 2) < R.RL

/-- `σ` is the proper distance from the observer along a radial line of the solution without a
mass, out to its horizon at `r_h`: `σ(0) = 0` and `dσ/dr = 1/√f`, from the radial part `dr²/f` of
the metric, with `σ` continuous up to the horizon.  The metric is the derived solution's
(`Main.schwarzschild_deSitter`): a definition through the derived solution -/
def radial_distance (R : Reg) (G Λ rh : ℝ) (σ : ℝ → ℝ) : Prop :=
  σ 0 = 0 ∧ ContinuousOn σ (Set.Icc 0 rh) ∧
    ∀ r ∈ Set.Ioo 0 rh, HasDerivAt σ (1 / Real.sqrt (R.fSdS G 0 Λ r)) r

/-- the sphere of the drawing about a point of the three-sphere of radius `R_Λ`, on which a largest
ring, of `L` cells, is a great circle: the points at the distance `s` from it in the space of the
drawing, `0 < s`, no larger than a great sphere, `s² ≤ 2R_Λ²`, with the areal radius `r ≥ 0`,
`r² = s² − s⁴/4R_Λ²`; that this `r` is the areal radius, the sphere being a round sphere of radius
`r` (`Crossing.sphere_round`), is `Main.sphere_areal_radius` -/
def drawn_sphere (R : Reg) (s r : ℝ) : Prop :=
  0 < s ∧ s ^ 2 ≤ 2 * R.RL ^ 2 ∧ r ^ 2 = s ^ 2 - s ^ 4 / (4 * R.RL ^ 2) ∧ 0 ≤ r

/-- a point of the three-sphere of radius `R_Λ`, the space of the drawing, about which the sphere
of the drawing is taken -/
def on_three_sphere (R : Reg) (p : Quaternion ℝ) : Prop := ‖p‖ = R.RL

/-- the property of a random state that the ceilings use: every joint outcome `k` of the other
qubits occurs with either value `v` of the last qubit's bit, `pr k v > 0`.  `pr k v` is the
probability, in the state that the register holds, that the other qubits show `k` and the last
qubit shows `v`.  Sec. IV.A: "each of the `2^{N−1}` joint outcomes of the first `N − 1` qubits
occurs, and given it the last qubit's bit is 1 with probability strictly between 0 and 1".  The
bound "holds for every state in which all `2^N` joint outcomes occur", a product state of
superposed qubits among them.  In `Main.ceiling_logical`, `k` is one of the `2^N` conditional
states of a string, each of which occurs with either value of the string's bit. -/
def random_state {K : Type*} (pr : K → Bool → ℝ) : Prop := ∀ k v, 0 < pr k v

/-- the conditional states of a string's qubit occur in the state that the register holds
(Sec. IV.A: "whether each string has room for the different conditional states of its qubit").
`c ρ` is the conditional state at the reading `ρ` of the earlier bits: the probability that the
string's bit is `1` given `ρ`.  In the results on codes it is computed from the weights of the
state that the circuit calls for.  `pr r v` is the probability, in the state that the register
holds, that the earlier bits read some `ρ` with `c ρ = r` and the string's bit is `v`.  The
statement does not relate the two states.  The condition: every conditional state that is a
superposition, `c ρ` strictly between `0` and `1`, occurs with either value of the bit
(`hcond`).  The condition does not ask that a block's share of 1s equal the state, which is what
holding a state means in `Coding.lean`: the count uses only that both values of the bit occur.
The condition counts by conditional state, not by reading: two readings with one conditional
state ask for it once.  The paper's count for codes agrees with it (Sec. IV.A): the fullest
physical string "has up to `2^N` conditional states to hold", and "Where the equal and the
opposite case both occur and the `2^N` conditional states are superpositions that all differ in
probability, as in a random state, that string needs `2^N` blocks of at least two cells". -/
def conditional_states {Rd : Type*} (pr : ℝ → Bool → ℝ) (c : Rd → ℝ) : Prop :=
  ∀ ρ, 0 < c ρ → c ρ < 1 → 0 < pr (c ρ) true ∧ 0 < pr (c ρ) false

/-- every reading of the rest of the line occurs in both logical states (`Coding.LineCode.Match`),
as in the surface code (`Coding.surfaceCode_match`) -/
def line_match {n : ℕ} (code : Coding.LineCode n) : Prop := code.Match

/-- the premise of the alternative that Sec. IV.D rejects: the horizon is the Hubble radius,
`R_Λ = c/H` at every time, with `H = ȧ/a` the rate of the scale factor -/
def hubble_horizon (Rt : ℝ → Reg) (a adot : ℝ → ℝ) : Prop :=
  ∀ s, (Rt s).RL = (Rt s).c / (adot s / a s)

/-- a radius between `a` and `b` -/
def between (r a b : ℝ) : Prop := r ∈ Set.Ioo a b

/-- the carriers are the fraction `b` of the sphere's `N_s(r)` strings: the definition of `b` -/
def carrier_fraction (R : Reg) (b Ncar r : ℝ) : Prop := Ncar = b * R.Ns r

/-- the rejected alternative of Sec. IV.C: a classical share, the string holding a record of the
body with the probability `f = g_N/a₀` in place of the amplitude, so that the carriers are the
fraction `b = f` far from the body -/
def classical_share (b gN a0 : ℝ) : Prop := b = gN / a0

/-- the strings' energies spread at `μ` times the horizon's thermal energy `ℏ/(Lt_c)`, so that a
string's threshold is exponential with the mean `μ` instead of one qubit: the alternative whose
scale the measured `a₀` fixes (Sec. IV.C) -/
def threshold_mean (R : Reg) (μ : ℝ) (above : ℝ → ℝ) : Prop :=
  ∀ x, 0 ≤ x → above x = Real.exp (-x / (μ * (R.ℏ / (R.L * R.tc))))

/-- `h ≤ 1/2`: the deep regime of Eq. (deep), where the bound of `Main.deep_limit` is stated; and,
taken at `h/L`, the range `h ≤ L/2` in which `Main.carriers_leading_order` bounds the step to
leading order in `1/L` -/
def at_most_half (h : ℝ) : Prop := h ≤ 1 / 2

/-- the amplitude `h` of the body's share is positive and below `L`, `0 < h < L`: the amplitude
`h/L` that one tick adds to a string is then positive and below one, the amplitude of the
string's one whole qubit; the case that `Main.carriers_exact`, `Main.law_bounds` and
`Main.law_whole_bits` treat -/
def share_below_L (R : Reg) (h : ℝ) : Prop := 0 < h ∧ h < R.L

/-- **The same scale beyond one qubit** (`hscale`; Sec. IV.C: "We take its amplitude to keep
growing as the square root of its energy, as a wave's does: we use the same scale for every `f`,"),
the condition on which the law is stated for a share larger than what one string holds.
For a share that one string can hold, `f = E/u ≤ 1`, the count of bits gives the amplitude of
the share (`P1.share_bits`, `Main.share_amplitude`), which is `√f` to leading order in `1/L`
(`Approx.share_amplitude`).  Under `P1.mass_in_bits`, `P2.cells_hold_alike` and
`P1.string_matter_in_bits` a set of `m` of the string's `n` cells holds `(m/n)u`
(`Law.mass_of_cells`), at most the matter `u`, for `u ≥ 0`.  So a share larger than `u` fills
every bit of the string, and the count ends there: for `E > u` no count of bits names a set of the
string's cells, `P1.share_bits` says nothing, and no probability of bits gives an amplitude.  The
paper takes the amplitude of a larger share to keep growing as the square root of its energy, as
a wave's does, and so defines `h` on the same scale, `h = √(E/u)`, Eq. (h).  The statement is that
definition for `E > u`.  It is a condition:
the files do not derive it, and no sentence of the postulates states it.  Where `g_N > a₀` the
share exceeds what one string holds, `f = g_N/a₀ > 1` (`Main.fill_fraction`), and there the law
is stated on this condition.  `P1.share_in_parts` takes `h` as the amplitude of the share whose
parts add up, and `Main.carriers_exact`, `Main.galactic_law`, `Main.law_bounds` and
`Main.law_whole_bits` take that `h`.  `Main.share_amplitude` takes the condition for `E > u`.
Sec. IV.C: "A share larger than `u` fills every bit, and the count ends there."  "We take its
amplitude to keep growing as the square root of its energy, as a wave's does: we use the same
scale for every `f`," Eq. (h).  "On this scale `h = 1` is one whole qubit."
"Near the body, where `g_N > a₀`, `f` and `h` exceed one."  "The body's share is then still held,
since by Eq. (share) each string that carries the body's information holds two Landauer energies
at the sphere's temperature, whatever `f` is."  "So `u` sets the unit of `h`; it does not limit
what a string holds."
Data availability: "That a larger share has its amplitude on the same scale, Eq. (h), is a
condition, which the files do not derive."
Up to v18-69 the files took `h = √(E/u)` at every share as one premise of Postulate 1,
`P1.share_amplitude`. -/
def same_scale (R : Reg) (h TN εs : ℝ) : Prop :=
  R.matter εs < 2 * R.kB * TN * R.ln2 → h = Real.sqrt (2 * R.kB * TN * R.ln2 / R.matter εs)

/-- `φ` is a state: the probabilities `|φ_ω|²` that it gives its outcomes sum to one -/
def normalized {Ω : Type*} [Fintype Ω] (φ : Ω → ℂ) : Prop := ∑ ω, ‖φ ω‖ ^ 2 = 1

/-- **A different conditional state for each joint outcome** (Sec. IV.A: "In the random state
the last qubit has a different conditional state, a superposition, for each joint outcome of the
others, whatever the order of the strings").  `ψ (k, w)` is the amplitude of the state at the
joint outcome `k` of the other qubits and the bit `w` of the last qubit.  The conditional state
of the last qubit given `k` is its two amplitudes `ψ (k, ·)` up to a common factor, so two joint
outcomes `j` and `k` give one conditional state where the amplitudes given `j` are those given
`k` times a factor that is not zero.  The condition is that no two joint outcomes do.  A product
state in which two joint outcomes of the other qubits occur does not meet it: its last qubit has
one conditional state (`Conditional.product_one_state`). -/
def all_differ {K : Type*} (ψ : K × Bool → ℂ) : Prop :=
  ∀ j k, (∃ c : ℂ, c ≠ 0 ∧ ∀ w, ψ (j, w) = c * ψ (k, w)) → j = k

/-- **A label for each conditional state** (Sec. IV.A: "whether each string has room for the
different conditional states of its qubit, its states given the outcomes of the earlier qubits",
and "A block holds the conditional state of its joint outcome, and blocks of different outcomes
may hold the same one").  `ψ (k, w)` is the amplitude of the state at the joint outcome `k` of
the other qubits and the bit `w` of the last qubit, and `χ k` stands for the conditional state
of the last qubit given `k`.  Two joint outcomes `j` and `k` have one label exactly where they
give the last qubit one conditional state, its amplitudes given `j` being those given `k` times
a factor that is not zero.  Joint outcomes that do not occur, `ψ (k, ·) = 0`, share one label of
their own, which stands for no conditional state.  So the labels of the joint outcomes that
occur are as many as the different conditional states of `ψ`: one for each joint outcome where
the conditional states all differ (`all_differ`), and one in all for a product state in which
every joint outcome of the other qubits occurs (`Conditional.product_one_state`).
`Main.overlap_bound` and `Main.return_bound` take Postulate 1's possible outcomes by these
labels, for the last qubit's conditioned outcomes.  The bound of `Main.overlap_bound` uses one
direction, that joint outcomes with one label give one conditional state; the other direction
keeps the labels no finer than the conditional states, so that blocks of different outcomes
that hold one state count as holding it. -/
def state_given {K T : Type*} (ψ : K × Bool → ℂ) (χ : K → T) : Prop :=
  ∀ j k, χ j = χ k ↔ ∃ c : ℂ, c ≠ 0 ∧ ∀ w, ψ (j, w) = c * ψ (k, w)

/-- **A uniform field** (Sec. IV.C: "In the manifold a uniform external field, such as the
Galaxy's across the solar system, is a common acceleration of the body and of local free fall at
the place of every such observer").  `g x` is the acceleration of free fall at the observer's
place `x` and `ab` the body's acceleration without the field; `g' x` and `ab'` are the two with
it.  The condition is that the field changes both by one and the same acceleration.  The paper
takes this to be what a uniform field does, in the manifold.  `Main.frame_of_law` proves that a
field leaves the observer's proper acceleration as it is exactly where it meets the condition,
and that under such a field the temperature of the sphere, the share and Eq. (law) stand as
without it.  That the field of a given source meets the condition across the sphere the files
do not derive. -/
def carried_alike (g g' : (Fin 3 → ℝ) → Fin 3 → ℝ) (x ab ab' : Fin 3 → ℝ) : Prop :=
  ab' - ab = g' x - g x

/-- **A proper acceleration** (Sec. IV.C: "an Unruh temperature is that of a proper acceleration:
the acceleration of an observer held at rest relative to the body, against local free fall").  An
observer held at rest relative to the body has the body's acceleration `ab`; local free fall at
his place `x` has the acceleration `g x`; his proper acceleration is the difference
`ap = ab − g x`, and `a` is its magnitude. -/
def proper_acceleration (g : (Fin 3 → ℝ) → Fin 3 → ℝ) (x ab ap : Fin 3 → ℝ) (a : ℝ) : Prop :=
  ap = ab - g x ∧ a = Real.sqrt (∑ i, ap i ^ 2)

/-- **At rest** (Sec. II: "In the manifold, an observer or a body at rest is unaccelerated"): the
acceleration `ab` of the body vanishes. -/
def at_rest (ab : Fin 3 → ℝ) : Prop := ab = 0

/-- reversing the direction of a ring exchanges the two senses of a string's shift: the sense of
the reversed state `rev σ` is the other one -/
def reverses {State : Type*} (sense : State → Bool) (rev : State → State) : Prop :=
  ∀ σ, sense (rev σ) = !sense σ

/-- the state `σ₀` of a string obeys the law: the law is one that some state obeys -/
def obeys_law {State : Type*} (obeys : State → Prop) (σ₀ : State) : Prop := obeys σ₀


end Condition

/-! ## Steps at leading order, each with its exact form derived -/
namespace Approx

/-- **The count's entropy density on the cosmological horizon, to leading order in `1/L`** (`hcount`;
Sec. III.C): the horizon's entropy, one bit per ring, over its area `4πr_h²`, with the count's
`L²/4` rings in place of its `L²/4 − L/2 + 1` (`Main.count`).  The exact density, with the count's
rings, is `η(1 − 2/L + 4/L²)` at `r_h = R_Λ`: `Main.jacobson_G_exact` derives it from the
horizon's entropy, one bit for each largest ring (`P1.horizon_entropy`, `Bridge.horizon_entropy`),
and the `G` it gives exceeds the leading-order `G` of `Derived.jacobson_G` by less than `8/3L`
of it (`Main.G_leading_order`).  The results that take this step, through `Derived.jacobson_G`, are
stated at leading order, as the paper's equations are ("to leading order in `1/L`", Sec. III.C).
The step fixes the value of the law `η` from the count (derived) over the derived solution's
area. -/
def count_density (H : Horizon L) (R : Reg) (η : H.Cell → H.Loop → ℝ) (l₀ : H.Loop)
    (x₀ : H.Cell) (rh : ℝ) : Prop :=
  η x₀ l₀ = R.kB * (R.Rhor * R.ln2) / (4 * R.pi * rh ^ 2)

/-- **The carriers' fraction, to leading order in `1/L`** (`hb`; Sec. IV.C, Eq. (b)), a step at
leading order.  Sec. IV.C: "To leading order in `1/L` the share can therefore turn the string's
global phase by at most `h/L` per tick."  "A string therefore carries the body's information when
`E_st_c/ℏ ≤ h/L`, that is, when `E_s ≤ h k_BT_dS`, by Eq. (T)."  The step takes the carriers as
the strings whose energy is at most `hℏ/(Lt_c)`, which is `h` times the horizon's thermal energy
`k_BT_dS`, with `h` the amplitude of the body's share (`Derived.share_amplitude_exact`).  So
they are
the fraction `b = 1 − above(hℏ/(Lt_c))` of the sphere's strings, with `above x` the fraction of
the strings whose energy exceeds `x` (`Thermo.energies_thermal`).  The exact carriers are the
strings whose phase holds against the share, whatever the turn of their free tick:
`Main.carriers_exact` derives them from the share's parts per tick and the rule of the phase
(`P1.share_in_parts`, `P1.carriers_hold_phase`).  They are the strings of energy at most the
threshold `(ℏ/t_c) arcsin(h/L)` and the strings whose turn per tick lies within `arcsin(h/L)`
of one or more whole turns.  The step puts `h/L` for `arcsin(h/L)` in the threshold, its leading
order in `1/L`, and it leaves out the strings near the whole turns, a fraction below
`e^{−3πL/2}` of the strings.  With the Gibbs spread the step gives `b = 1 − e^{−h}`, Eq. (b),
where the exact fraction is
`(1 − e^{−L arcsin(h/L)})(1 + (e^{L arcsin(h/L)} + 1)/(e^{2πL} − 1))`
(`Derived.carriers_exact`), and the exact fraction exceeds `1 − e^{−h}` by at most the fraction
`(h/L)² + 5e^{−3πL/2}` of it where `h ≤ L/2` (`Main.carriers_leading_order`).
`Main.galactic_law` and `Main.scale_mean` take this step and are stated at leading order, as the
paper's Eq. (law) is; `Main.law_bounds` bounds what the step changes in the law. -/
def carriers_leading (R : Reg) (b h : ℝ) (above : ℝ → ℝ) : Prop :=
  b = 1 - above (h * (R.ℏ / (R.L * R.tc)))

/-- **The amplitude of a body's share, to leading order in `1/L`** (`hh`; Sec. IV.C, Eq. (h)), a
step at leading order.  The step takes the amplitude of the share as `h = √(E/u)`, with
`E = 2k_BT_N ln 2` the body's energy per string of the sphere (Eq. (E)) and `u` the matter that
a string holds on average (`Reg.matter`).  The exact amplitude is that of the whole bits that
the share fills (`P1.share_bits`).  For a share that one string can hold, `E ≤ u`, on a string
of `n` bits, it has `h² = m/n` with `m` the whole number of bits that the share fills, so that
`E/u − 1/n < h² ≤ E/u`: `Main.share_amplitude` derives it (`Derived.share_amplitude_exact`).
The step puts the fraction `E/u` for the fraction `m/n` of whole bits.  It changes nothing
where the share is a whole number of bits, and nothing for a share larger than `u`, where
`h = √(E/u)` is the paper's definition of `h` on the same scale, a condition
(`Condition.same_scale`).  Otherwise the exact amplitude falls
short of `√(E/u)` by at most `1/√n`, and by at most `1/(n√(E/u))` where the share is at least
one bit; a share below one bit fills no bit, and its exact amplitude is zero
(`Main.share_leading_order`).  On a largest ring `n = L` (`Horizon.card_ring`), so at every
fraction `E/u > 0` the step is the leading order in `1/L`, as the count's density
(`count_density`) and the carriers' fraction (`carriers_leading`) are.  `Main.law_whole_bits`
bounds what the step changes in the law.  With the exact amplitude on a largest ring,
`0 < h < L`, the carriers' exact fraction `b` and `f = E/u`, the acceleration `g_N/b` is at
most that of Eq. (law) over `√(1 − 1/(L·f))` where the share is more than one bit, `f > 1/L`,
and at most `1 + 1/(L·f)` times it where the share is at least two bits, `f ≥ 2/L`.  It is at
least `1 − (√f/L)² − 5e^{−3πL/2}` times that of Eq. (law) where `√f ≤ L/2`.
`Main.fill_fraction`,
`Main.galactic_law`, `Main.law_bounds` and `Main.scale_mean` take this step and are stated at
leading order.  Up to v18-69 the files took `h = √(E/u)` as one premise of Postulate 1,
`P1.share_amplitude`.  Sec. IV.C: "That fraction is the probability of Eq. (raqm), and its amplitude is `√f`, Eq. (qubit)."
"A share larger than `u` fills every bit, and the count ends there."  "We take its amplitude to
keep growing as the square root of its energy, as a wave's does: we use the same scale for every
`f`," Eq. (h).  "On this scale `h = 1` is one whole qubit."
"Near the body, where `g_N > a₀`, `f` and `h` exceed one."  "The body's share is then still held,
since by Eq. (share) each string that carries the body's information holds two Landauer energies
at the sphere's temperature, whatever `f` is."  "So `u` sets the unit of `h`; it does not limit
what a string holds."
Data availability: "The three steps at leading order, the count's density, the share's amplitude,
and the carriers' fraction, are named as such, with their errors bounded in the files." -/
def share_amplitude (R : Reg) (h TN εs : ℝ) : Prop :=
  h = Real.sqrt (2 * R.kB * TN * R.ln2 / R.matter εs)

end Approx

/-! ## Units: the system of units the files state their results in -/
namespace Units

/-- **The defining constants of the SI** (`hconst`): `c`, `ℏ` and `k_B` are the same at every
time.  Since 2019 the SI defines its units by fixing the numerical values of seven constants, among
them the speed of light `c`, which with the second defines the meter, the Planck constant
`h = 2πℏ`, which defines the kilogram, and the Boltzmann constant `k_B`, which defines the kelvin
[BIPM, *The International System of Units (SI)*, 9th ed. (2019), Sec. 2.2].  In those units the
three are the same at every time by the definition of the units, not by a law of nature; the files
state their results in the SI (Appendix A).  What the constancy results say about nature, that `G`,
`Λ` and `ρ_Λ` are constant and `w = −1`, rests on `L` and the cell, the constants of Postulate 1
(`P1.constant_L`, `P1.constant_cell`).  A choice of units, which states nothing about nature and so
is none of the four sources. -/
def si_constants (Rt : ℝ → Reg) : Prop :=
  ∀ s, (Rt s).c = (Rt 0).c ∧ (Rt s).ℏ = (Rt 0).ℏ ∧ (Rt s).kB = (Rt 0).kB

end Units

/-! ## Open: the premises that no source states and the files do not derive

A premise here is none of the four sources, no condition and no choice of units, and the files do
not derive it.  The namespace holds none, as at v18-68.  Up to v18-68 the files took the rule of Sec. IV.C by which a string carries a body's information as one premise
of Postulate 1 (`P1.carriers_by_amplitude`), with the distribution of a string's threshold as a
premise of thermodynamics (`Thermo.max_entropy_threshold`).  The files derive that rule
(`Main.carriers_exact`) from two applications of Postulate 1 (`P1.share_in_parts`,
`P1.carriers_hold_phase`), the spread of the strings' energies (`Thermo.energies_thermal`) and
mathematics that they prove.  The amplitude of the body's share ties `h` to the body where
`Main.law_bounds`, `Main.galactic_law` and `Main.scale_mean` take the rule.  Up to v18-69 the
files took `h = √(E/u)` as one premise, `P1.share_amplitude`.  `Main.share_amplitude` derives the
exact amplitude (`Derived.share_amplitude_exact`) from the count of the bits that the share
fills, where one string can hold the share (`P1.mass_in_bits`, `P2.cells_hold_alike`,
`P1.string_matter_in_bits`, `P1.share_bits`, `P1.ring_bits_alike`).  `h = √(E/u)` is its leading
order in `1/L`, a named step (`Approx.share_amplitude`), with its error bounded in `h`
(`Main.share_leading_order`) and in the law (`Main.law_whole_bits`).  Beyond what one string
holds no count of bits gives an amplitude, and the paper defines `h` on the same scale,
`h = √(E/u)`.  The files take that definition as a condition (`Condition.same_scale`), which
defines the amplitude that the results treat there: they do not derive it, and no sentence of
the postulates states it, so it stands with the conditions and not with the premises of
Postulate 1.
The rule's leading order in `1/L` is a
named step (`Approx.carriers_leading`), with its error bounded
(`Main.carriers_leading_order`).  The check of `#premises` reads the namespace: a result that
took a premise of it would show it in the premise ledger, where its line would be marked
"(OPEN)" and the line `rests on:` of the result would name it after the sources. -/
namespace Open

end Open

end Register.Sources
