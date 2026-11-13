import RegisterGravity

/-! # The axiom ledger

For every main theorem, the axioms its proof depends on.  A physical input is never an axiom
here: a thermodynamic input, Sec. II's definition of energy, or a theorem of geometry is a named hypothesis in
the statement of the theorem that uses it, and so is the thesis of the paper where it is applied:
that the energy inside the horizon is the strings' and nothing else's (`hin` of
`Reg.vacuum_share`; Postulate 1's first sentence, every physical quantity defined by qubits,
`Sources.P1.energy_inside_strings`), that a body's energy is held by the strings that carry its
information (`Sources.P1.energy_in_carriers`), and that the body's share at a string enters as an
amplitude (`Sources.P1.carriers_by_amplitude`).  `Qubit.lean` holds the quantum mechanics of one qubit
that the energy of a free string and the bit per ring rest on: the two outcomes of a free string's
qubit are its two senses, and the free tick keeps each string of one sense up to one and the same
phase (the field `hsense` of `Qubit.Tick`, Sec. II's sentence: the shift leaves a string of one
sense as it is up to its global phase, Postulate 1, and that phase changes alike in either sense,
since no law depends on the ring's direction, Postulate 2): the two senses have one energy, and the
tick, a linear map, is that one factor on all the string's states (`Qubit.eq_diagonal_of_keeps`,
`Qubit.Tick.phase_unique`); the factor is a phase, a global phase being a factor of modulus one
(`Qubit.Tick.norm_scalar`), and any factor `e^{−iθ}` is the factor of a tick (`Qubit.Tick.ofPhase`);
the Gibbs distribution at the horizon's temperature gives the strings the mean energy `k_BT_dS`
(`Law.gibbsMean_eq`, `Reg.string_energy`), Sec. II's definition of energy then makes the tick of that energy
the factor `e^{−i/L}` (`Reg.string_tick`), and a string's heat is `ln 2` of the mean energy, the
vacuum's part, with the rest matter (`Reg.string_split`, `Reg.vacuum_share`); every state of a free string has one
energy, the two senses included, so its thermal state is half the identity, which gives the
outcome `1` the probability `1/2` (`Qubit.Tick.bornProb_state`) and holds one bit, the sense bit
(`Main.string_one_bit`); a string's state, Eq. (qubit) with the share of its bits as the probability of `1` and its position as
the phase (Postulate 1, Eq. (raqm), `Qubit.stringState`), gives `1` the probability of that share
(`Qubit.share_stringState`), so under any mixture of strings the expected share is the Born
probability of `1` in the mixture (`Qubit.expected_share`), and half the bits of a string in the
thermal state are 1s on average (`Qubit.half_bits_thermal`, with `Qubit.half_bits_model`).  The strings of a sphere are counted ring by
ring (`Bridge.sphere_strings`): with the largest rings drawn as great circles of the
three-sphere, averaged over the sphere's position, by Archimedes' hat-box theorem in four
dimensions (`HatBox.hatBox`).  The drawing is derived from the rings as closed geodesics of space
(`Bridge.sphere_strings_deSitter`, `Geodesics.lean`), and so is `Λ > 0`.  That a largest ring
is a closed geodesic of space, made of its cells as segments of length `ℓ_c`, the last sentence of
Postulate 2, is the hypothesis they take: by
itself for the drawing, and in the chain through the admissible drawings (`Symmetry.admissible`) of the
rings of the space at an instant (`Space.SliceIsQubits`) and the rings through the observer's cell
drawn in that space, with Sec. II's cell as a place on them and the same opposite cell halfway
around each (`Space.RingsDrawn`, `Sources.P2.rings_drawn`).  `Bridge.sphere_strings_model` shows that it can be
met.  It matches the register on pairs of cells: two
cells that are neither equal nor opposite lie on exactly one largest ring (Postulate 2), and two
points of space that are neither equal nor antipodal lie on exactly one geodesic
(`TwoCells.geodesic_through_two`).
Averaged over the rotations `x ↦ φ⁻¹(qφ(x))` of the drawing, with `q` a unit quaternion and `φ`
an isometry of the space onto `ℍ`, the count about any point is the average, exactly, in any
four-dimensional space (`Center.strings_rotation_mean_of`, `Center.sphere_strings_centered_of`,
`Center.sphere_strings_of_rings_centered`).  The drawing is no part of the state, since the
postulates fix the rings, not which great circle each one is, and every physical law and quantity
is defined by qubits; with every rotation weighted alike, the count about a given body is defined
as the average over the rotations.  The weighting is derived from Postulate 1's first sentence
applied to it, the premise `Sources.P1.no_rotation_preferred` of `Main.sphere_strings` and
`Main.observer_count`: the drawing is no part of the register, which holds nothing about a rotation
of it, so the weighting, read off nothing, is the same at every rotation, which makes it left
invariant (`Sources.P1.no_rotation_preferred.invariant`); a probability weighting of the rotations
that following every rotation by a fixed one leaves unchanged is the unit sphere's measure,
normalized (`Weighting.eq_toSphere_of_invariant`, from the uniqueness of Haar measure on the unit
quaternions), so the averages over it are those above (`Weighting.integral_normalized`).
The symmetry of space is derived: a law is a function of the
register, space is determined by the rings (Postulate 1's first sentence, every physical law and
quantity defined by qubits: the thesis of the paper), and with two clauses of
Postulate 2 every law is the same at every place and in every direction, whatever the drawing
(`Symmetry.laws_same`, `Symmetry.lawAt_same`).  It gives one entropy density on every local horizon
(`Symmetry.one_density`), and at that density the horizon drawn in by a mass, with the area the
solution gives it, holds `L_M²/4` bits, and a black hole's horizon holds `L'²/4` bits
(`Symmetry.massive_horizon_density`, `Symmetry.black_hole_density`): the area law with a mass is
not a step taken again.  With the state the same at every
crossing (`Solution.state_same`) and the thesis for the geometry (`hgeom`), it gives a geometry the
same at every slot (`Solution.geometry_same`, `Solution.geometry_same_slots`).  The Killing–Hopf
theorem, with every geodesic of the space at an instant closed by a ring (the hypothesis `hclose`),
makes that space a space form (the hypothesis `hKH`, `Space.SpaceForm`).  Jacobson's step
(`Einstein.lean`) gives Einstein's equations up to a multiple of the metric
(`Einstein.eq_smul_eta_of_null`, `Einstein.einstein_up_to_metric`); with the first law for every
observer, the hypothesis `hfirst`, which gives `∇^a T_ab = 0` (`Einstein.eq_zero_of_timelike`), and
the contracted Bianchi identity, the hypothesis `hbianchi`, Einstein's equations with one constant
`Λ`, with matter and without (`Einstein.einstein_equations`, `Einstein.vacuum_of_field_equations`,
`Solution.vacuum_without_mass`); and Newton's constant with the static weak field, the hypothesis
`hweak` (`Einstein.newtonian_coefficient`, `Einstein.G_of_clausius`,
`Solution.jacobson_G_from_sources`), which needs neither.  With the Leibniz rule for a flow, the
hypothesis `hleib`, the first law moves matter and light on geodesics (`Einstein.flow_geodesic`,
`Einstein.null_dust_of_current`, `Einstein.null_geodesic`), and on a circular orbit `v² = gr`
(`Motion.circular_speed`).  About a body at rest, alone, the static, spherically symmetric vacuum
solution is Schwarzschild–de Sitter (`Schwarzschild.static_vacuum`,
`Main.schwarzschild_deSitter`), and as its mass grows from zero the Clausius relation on the
observer's cosmological horizon keeps `Λ` at its value without a mass, `3/R_Λ²`
(`MassHorizon.lean`, `Reg.lambda_with_mass`, `Main.lambda_with_mass`), so the horizon is drawn in by
`GM/c²` (`Main.horizon_drawn_in`).  Einstein's constraint gives `3K = Λ` (`hcon`); the slice's
rings exclude the flat and hyperbolic forms (`Space.slice_sphere`), and with the rings through the
observer's cell drawn in it (`hdrawn`) they exclude every quotient of the three-sphere, so the space at an
instant is the three-sphere itself with `Λ = 3/R_Λ²` (`Space.sphere_rings`,
`Space.cosmological_constant_of_sources`; every link at once in
`Solution.cosmological_constant_from_sources`, whose hypotheses `Solution.cosmological_constant_model`
meets together).
`Pairing.lean` counts what a pairing of strings measured jointly shows (Sec. IV.A): every joint
frequency is a multiple of one over the number of the positions, no pairing shows more than that
many joint outcomes, two strings prepared apart are shown exactly only where `L` divides `m₁m₂`
and are paired within one cell of the product, and every string keeps its own fraction in every
pairing; the probability of a joint outcome is the product, string by string, of the frequencies
of its bits on its blocks (`Pairing.freq_chain`); the strings in a pairing, with their blocks'
phases, are the state whose probabilities the pairing shows (`Pairing.state_of_strings`); a state
that vanishes outside a set of outcomes overlaps any state by at most the probability that the
other gives the set (`Pairing.overlap_le`), which bounds the overlap above the ceiling where the
conditional states all differ (`Main.overlap_bound`, with Postulate 1's possible outcomes for
the last qubit's conditioned outcomes, `Sources.P1.outcomes_at_positions`) and, with the gates
as the premise of quantum mechanics (`Sources.QM.gates`), the return of the random circuit
(`Main.return_bound`).
`Conditional.lean` counts the conditional states of a product state, of a cluster state, of a
stabilizer measurement and of a state that depends on the earlier qubits through a count, with
`Conditional.condState` and, for the stabilizer, `Conditional.stabState`, which is `condState`
up to a sign (`Conditional.stabState_spec`).  It proves that a product
state gives the last qubit one conditional state, so that its conditional states do not all
differ (`Conditional.product_one_state`); that a string with room for its conditional states
can hold each of them with either bit, so that Postulate 1's possible outcomes, taken for the
qubit's conditioned outcomes, are met whatever the register holds
(`Conditional.room_holds`); and that a block of any size holds the fixed bit of a stabilizer
measurement and then shows the product of the neighbors' bits at every position, at every `N`
(`Conditional.stabilizer_held`).  `Strings.lean`
proves Sec. II's sentences on a ring's one string, the lap, the two senses, the sense as a
property of the string's state, the bit that a string keeps and the strings not yet scattered.
`Receiving.lean` proves that a ring which crosses a sphere meets its surface at two points.
`Constant.lean` proves that the inputs of Einstein's equations hold with every value of `Λ`,
that Jacobson's step does not see a vacuum term of the stress tensor, the limit up to which the
solution with a mass has a horizon, and that an accelerated observer's horizon is his own where
his acceleration exceeds `c²/R_Λ`.  `Matter.lean` names the matter a string holds on average, the
unit of Eq. (f), and proves that the proper distance and the areal radius agree near the
observer and that unequal energies of the two senses would take part of a string's bit.
`Interpolation.lean` bounds Milgrom's simple interpolating function against Eq. (law).
`Main.frame_of_law` states the frame of the law of Sec. IV.C: a field leaves a proper
acceleration as it is exactly where it is a common acceleration of the body and of free fall at
the observer's place (`Sources.Condition.carried_alike`), and under such a field the
acceleration, the temperature of the sphere, the share and Eq. (law) stand as without it.
The expected output for every line is `[propext, Classical.choice, Quot.sound]`, the
logical minimum of classical mathematics in Lean, or a part of it (`Symmetry.IsQubits.eq_of_content_eq`
uses none, and Lean prints "does not depend on any axioms"); an unfinished proof would show up as an
extra axiom.
The docstrings name a declaration `name` of a file `File.lean` as `File.name`, or by its Lean name;
the declarations of
`Chain.lean`, `Galactic.lean`, `DeSitter.lean`, `MassHorizon.lean` and `Cosmo.lean`, and those of
`Carriers.lean` outside its two blocks of the namespace `Law`, lie in the
namespace `Register.Reg`, so that `Carriers.law`, say, is printed below as `Register.Reg.law`. -/

-- Sec. II, the count (Postulates 1–2), the projective plane, and a model of the axioms
#print axioms Horizon.two_loops
#print axioms Horizon.finite_of_clauses
#print axioms Horizon.finite_cell_and_loop
#print axioms Horizon.four_le_of_misses
#print axioms Horizon.four_le
#print axioms Horizon.exists_loop_not_mem
#print axioms Horizon.two_mul_card_through
#print axioms Horizon.counts
#print axioms Horizon.even_L
#print axioms Horizon.two_mul_order_add_one
#print axioms Horizon.card_loop_eq_order
#print axioms Horizon.fano
#print axioms Horizon.fanoPositions
#print axioms Horizon.fanoSym
#print axioms Horizon.fano_homogeneous

-- Sec. II, the strings of a sphere counted ring by ring: Archimedes' hat-box theorem in four
-- dimensions, and the rings that cross a sphere
#print axioms HatBox.disk
#print axioms HatBox.annulus
#print axioms HatBox.core
#print axioms HatBox.haar_ratio
#print axioms HatBox.plane_finrank
#print axioms HatBox.plane_norm
#print axioms HatBox.cone_eq
#print axioms HatBox.cone_measure
#print axioms HatBox.hatBox
#print axioms Crossing.crosses_iff
#print axioms Crossing.sphere_round
#print axioms Crossing.Drawing.crosses_center
#print axioms Crossing.Drawing.crossing_fraction
#print axioms Crossing.Drawing.meanStrings_eq
#print axioms Crossing.map_isometry
#print axioms Crossing.toSphere_preserving
#print axioms Crossing.Drawing.rotate
#print axioms Crossing.Drawing.strings_rotate
#print axioms Crossing.Drawing.restrict
#print axioms Crossing.Drawing.strings_le_card
#print axioms Center.leftRot
#print axioms Center.strings_rotation_mean
#print axioms Center.sphere_strings_centered
#print axioms Center.observer_strings_mean
#print axioms Center.sphere_strings_centered_model
#print axioms Center.exists_isometry_quaternion
#print axioms Center.rotOf
#print axioms Center.strings_rotation_mean_of
#print axioms Center.sphere_strings_centered_of
#print axioms Center.sphere_strings_of_rings_centered
#print axioms Center.sphere_strings_of_rings_centered_model

-- Secs. II and IV.C, no rotation of the drawing preferred: a weighting read off nothing is left
-- invariant, and a weighting of the rotations that prefers none is the unit sphere's measure,
-- normalized, so the averages are those above
#print axioms Register.Sources.P1.no_rotation_preferred.invariant
#print axioms Weighting.eq_toSphere_of_invariant
#print axioms Weighting.integral_normalized
#print axioms Weighting.evenWeight
#print axioms Weighting.weighting_model

-- Secs. II and IV.D, a ring as a closed geodesic of space: in de Sitter space every closed
-- spacelike geodesic has one length, and in the space at an instant it is a great circle; with the
-- hyperbola, a geodesic of hyperbolic space (`Space.hyperbolic_space_no_rings`)
#print axioms Geodesic.harmonic_eq
#print axioms Geodesic.IsGeodesic.speed_const
#print axioms Geodesic.IsGeodesic.acc_eq
#print axioms Geodesic.IsGeodesic.circle
#print axioms Geodesic.IsGeodesic.hasLength
#print axioms Geodesic.IsGeodesic.greatCircle
#print axioms Crossing.Drawing.ofRings
#print axioms Geodesic.ofRings_circle
#print axioms Geodesic.circleCurve
#print axioms Geodesic.circleCurve_geodesic
#print axioms Geodesic.circleCurve_spacelike
#print axioms Geodesic.hypCurve

-- Sec. II, the symmetry of space: with two clauses of Postulate 2 every law is the same at every
-- place and in every direction of the space the rings describe, whatever the drawing; Postulate 1's
-- first sentence applied: a quantity that is qubits reads the same where the register holds the
-- same, and a slot lies in the space the admissible drawings describe exactly when a ring can
-- run there
#print axioms Symmetry.laws_same
#print axioms Symmetry.lawAt_eq
#print axioms Symmetry.lawAt_same
#print axioms Symmetry.one_density
#print axioms Symmetry.massive_horizon_density
#print axioms Symmetry.black_hole_density
#print axioms Symmetry.mem_described_admissible
#print axioms Symmetry.IsQubits.eq_of_content_eq
#print axioms Symmetry.laws_same_model

-- Sec. III, Einstein's equations from the Clausius relation and the first law: a form that vanishes
-- on every null vector is a multiple of the metric; the first law for every observer gives
-- `∇^a T_ab = 0`, and with the contracted Bianchi identity the equations hold with one constant `Λ`,
-- with matter and without; matter and light move on geodesics; Newton's constant from the static
-- weak field
#print axioms Register.Einstein.quad_vec
#print axioms Register.Einstein.quad_eta_vec
#print axioms Register.Einstein.isNull_vec
#print axioms Register.Einstein.eq_smul_eta_of_null
#print axioms Register.Einstein.quad_sub
#print axioms Register.Einstein.quad_smul
#print axioms Register.Einstein.symmPart_isSymm
#print axioms Register.Einstein.quad_symmPart
#print axioms Register.Einstein.einstein_up_to_metric
#print axioms Register.Einstein.eta_mulVec_ne_zero
#print axioms Register.Einstein.trace_add
#print axioms Register.Einstein.trace_smul
#print axioms Register.Einstein.trace_eta
#print axioms Register.Einstein.eq_zero_of_timelike
#print axioms Register.Einstein.einstein_equations
#print axioms Register.Einstein.vacuum_of_field_equations
#print axioms Register.Einstein.flow_geodesic
#print axioms Register.Einstein.null_dust_of_current
#print axioms Register.Einstein.null_geodesic
#print axioms Register.Einstein.newtonian_coefficient
#print axioms Register.Einstein.G_of_clausius

-- Secs. III and IV.D, the Schwarzschild–de Sitter solution from the vacuum equations: the static,
-- spherically symmetric metric with `R_ab = Λ g_ab` has `e^{−2β} = 1 − 2m/r − Λr²/3`
#print axioms Register.Schwarzschild.static_vacuum
#print axioms Register.Schwarzschild.time_part

-- Sec. IV.C, circular orbits: the acceleration on a circle, and `v² = gr`
#print axioms Register.Motion.hasDerivAt_circle
#print axioms Register.Motion.deriv_circle
#print axioms Register.Motion.accel_circle
#print axioms Register.Motion.circular_speed

-- Secs. IV.C–IV.D, the constant `Λ` with a mass at rest: the Clausius relation on the cosmological
-- horizon, as the mass grows, keeps `Λ` at its value without a mass
#print axioms Register.Reg.deriv_lambda_zero
#print axioms Register.Reg.clausius_geometric
#print axioms Register.Reg.first_law_extended
#print axioms Register.Reg.clausius_iff
#print axioms Register.Reg.lambda_with_mass
#print axioms Register.Reg.lambda_with_mass_deSitter

-- Sec. IV.D, the space at an instant: the flat and hyperbolic forms without rings; the rings and
-- the rings through the observer's cell, drawn, exclude every quotient of the three-sphere
#print axioms Space.spaceMap
#print axioms Space.sphereSlots_pos
#print axioms Space.RingsDrawn
#print axioms Space.not_spread_space
#print axioms Space.flat_space_no_rings
#print axioms Space.hyperbolic_space_no_rings
#print axioms Space.slice_sphere
#print axioms Space.sphere_rings
#print axioms Space.cosmological_constant_of_sources

-- Sec. IV.D, the solution without a mass: the state is the same at every crossing, so with the
-- thesis applied to the geometry (`hgeom`) the geometry is the same at every slot; the vacuum
-- equations and Newton's constant from Jacobson's step; the space form, the constraint, the
-- rings and the rings through the observer's cell, drawn, give `Λ = 3/R_Λ²`; a model meets the
-- hypotheses together
#print axioms Solution.lawAt_eq_of
#print axioms Solution.lawAt_const
#print axioms Solution.described_univ
#print axioms Solution.state_same
#print axioms Solution.geometry_same
#print axioms Solution.geometry_same_slots
#print axioms Solution.eta_pos
#print axioms Solution.vacuum_without_mass
#print axioms Solution.jacobson_G_from_sources
#print axioms Solution.cosmological_constant_from_sources
#print axioms Solution.chain_from_sources
#print axioms Solution.sphereQuotient_bot
#print axioms Solution.vacuumSpacetime
#print axioms Solution.vacuumSpacetime_clausius
#print axioms Solution.closes_deSitter
#print axioms Solution.modelK_pos
#print axioms Solution.one_div_modelK
#print axioms Solution.modelSp
#print axioms Solution.B0
#print axioms Solution.e4
#print axioms Solution.e4_norm
#print axioms Solution.e4_inner
#print axioms Solution.fano_shared
#print axioms Solution.fanoDir
#print axioms Solution.fanoDir_ne_zero
#print axioms Solution.fanoDir_inj
#print axioms Solution.modelRing
#print axioms Solution.modelPlace
#print axioms Solution.modelPlace_inner
#print axioms Solution.eq_of_cos_sin_eq
#print axioms Solution.sin_mul_pi_div_three_eq_zero
#print axioms Solution.angle_mem_Ico
#print axioms Solution.rings_drawn_model
#print axioms Solution.cosmological_constant_model

-- Sec. IV.D, the rotations of the three-sphere (`exists_rotation_plane`, `exists_plane_not_turned`),
-- the great circles of de Sitter space, and a ring in the trivial quotient as a closed curve
#print axioms Quotients.planeCurve
#print axioms Quotients.planeCurve_isGeodesic
#print axioms Quotients.exists_angle_pos
#print axioms Quotients.exists_rotation_plane
#print axioms Quotients.exists_plane_not_turned
#print axioms Quotients.closesIn_bot

-- Sec. II and the last sentence of Postulate 2: one geodesic of space through two points that are
-- not antipodal, as one largest ring through two cells that are not opposite
#print axioms TwoCells.greatCircle_through
#print axioms TwoCells.greatCircle_unique
#print axioms TwoCells.geodesic_through_two

-- Sec. II, the clause of Postulate 2 that no cell differs from another, and a register with its
-- maps for every prime-power order
#print axioms Horizon.IsPerfectDifferenceSet.existsUnique
#print axioms Horizon.ofDiffSet
#print axioms Horizon.ofDiffSetPositions
#print axioms Horizon.dsSym
#print axioms Horizon.ofDiffSet_homogeneous
#print axioms Horizon.register_of_diffSet
#print axioms Horizon.Singer.mem_range_of_pow_card
#print axioms Horizon.Singer.exists_gen
#print axioms Horizon.Singer.pow_n_mem
#print axioms Horizon.Singer.pt_inj
#print axioms Horizon.Singer.card_nonzero
#print axioms Horizon.Singer.card_points
#print axioms Horizon.Singer.exists_plane
#print axioms Horizon.Singer.exists_pds
#print axioms Horizon.Singer.homogeneous_register
#print axioms Horizon.Singer.homogeneous_register_of_prime_power

-- Secs. II and IV.C, the cyclic order of the rings and where the strings hold their entropy
#print axioms Horizon.Positions.even_of_halfway
#print axioms Horizon.Positions.card_ringDist
#print axioms Horizon.Positions.card_dist_eq
#print axioms Horizon.Positions.dist_opp
#print axioms Horizon.Positions.offset_self
#print axioms Horizon.Positions.offset_opp_self
#print axioms Horizon.Positions.offset_inj
#print axioms Horizon.Positions.exists_offset
#print axioms Horizon.Positions.horizon_weight_ring

-- Secs. IV.A and V, the qubit ceiling
#print axioms Register.Capacity.two_le_card_of_frac
#print axioms Register.Capacity.one_cell_block
#print axioms Register.Capacity.ceiling
#print axioms Register.Capacity.ceiling_by_outcome
#print axioms Register.Capacity.ceiling_in_step
#print axioms Register.Capacity.ceiling_logical
#print axioms Register.Coding.css_conditional_cases
#print axioms Register.Coding.css_conditional
#print axioms Register.Coding.repetition_conditional
#print axioms Register.Coding.LineCode.bit_eq
#print axioms Register.Coding.LineCode.two_mul_card_cosetRest
#print axioms Register.Coding.LineCode.lastGivenRest_eq
#print axioms Register.Coding.LineCode.bitGiven_rest
#print axioms Register.Coding.jointBitGiven_eq
#print axioms Register.Coding.css_conditional_joint
#print axioms Register.Coding.card_condStates_le
#print axioms Register.Coding.card_condStates_repetition
#print axioms Register.Coding.LineCode.jointBitGiven_rest
#print axioms Register.Coding.LineCode.card_lineStates
#print axioms Register.Coding.two_mul_card_states_le
#print axioms Register.Coding.ceiling_both_cases
#print axioms Register.Coding.ceiling_line_code
#print axioms Register.Coding.lineTwo
#print axioms Register.Coding.lineTwo_match
#print axioms Register.Coding.surfaceCode
#print axioms Register.Coding.surfaceCode_match
#print axioms Register.Coding.ceiling_line_code_model
#print axioms Register.Coding.two_cells_each_model
#print axioms Register.Capacity.share_read
#print axioms Register.Capacity.block_fraction_read
#print axioms Register.Capacity.ceiling_soft
#print axioms Register.Capacity.nmax_iff
#print axioms Register.Capacity.palmer_threshold
#print axioms Register.Cluster.ratio_eq_neg_normSq
#print axioms Register.Cluster.moebius_injOn
#print axioms Register.Cluster.moebius_collision
#print axioms Register.Cluster.moebius_ne_zero
#print axioms Register.Cluster.step_ne_zero
#print axioms Register.Cluster.step_card
#print axioms Register.Cluster.chain_card

-- Sec. IV.A, what a pairing of strings measured jointly shows, the state that the strings in a
-- pairing are with their blocks' phases, the conditional states of product and cluster states and
-- of a stabilizer measurement, and the overlap of what the register holds with any state (v18-65)
#print axioms Register.Pairing.freq
#print axioms Register.Pairing.freq_multiple
#print axioms Register.Pairing.shown_le_cells
#print axioms Register.Pairing.sum_freq
#print axioms Register.Pairing.shown_exactly_iff
#print axioms Register.Pairing.pairing_misses
#print axioms Register.Pairing.product_multiple_iff
#print axioms Register.Pairing.product_not_shown
#print axioms Register.Pairing.most_products_not_shown
#print axioms Register.Pairing.pairing_within_one_cell
#print axioms Register.Pairing.pairing_not_fixed
#print axioms Register.Pairing.inStep
#print axioms Register.Pairing.strings_in_step
#print axioms Register.Pairing.blockOf
#print axioms Register.Pairing.freq_chain
#print axioms Register.Pairing.block_resolution
#print axioms Register.Pairing.jointPhase
#print axioms Register.Pairing.state_of_strings
#print axioms Register.Pairing.sample_outcomes_le
#print axioms Register.Pairing.overlap_le
#print axioms Register.Conditional.condState
#print axioms Register.Conditional.card_product_states_le_one
#print axioms Register.Conditional.clusterSign
#print axioms Register.Conditional.clusterSign_eq
#print axioms Register.Conditional.factor_depends
#print axioms Register.Conditional.card_cluster_states_le_two
#print axioms Register.Conditional.stabAmp
#print axioms Register.Conditional.stabState
#print axioms Register.Conditional.stabState_spec
#print axioms Register.Conditional.stabilizer_bit
#print axioms Register.Conditional.card_stab_states_le_two
#print axioms Register.Conditional.stab_prob
#print axioms Register.Conditional.card_states_by_count
#print axioms Register.Conditional.two_cells_fit
#print axioms Register.Conditional.product_one_state
#print axioms Register.Conditional.room_holds
#print axioms Register.Conditional.stabilizer_held

-- Sec. II, a ring's one string, the lap, the two senses, the sense as a property of the state,
-- the bit that a string keeps, the strings not yet scattered, and the two radii near the observer;
-- Sec. IV.B, an accelerated observer's own horizon; Sec. IV.C, the two points where a ring crosses
-- a sphere, the matter a string holds on average, the bit that unequal energies would take, and
-- Milgrom's simple interpolating function against Eq. (law); Secs. III and IV.D, the constant `Λ`
-- free in the equations, a vacuum term unseen by Jacobson's step, and the limit up to which the
-- solution has a horizon (v18-65)
#print axioms Horizon.ringStrings
#print axioms Horizon.card_ring
#print axioms Horizon.Positions.lap
#print axioms Horizon.Positions.two_senses
#print axioms Register.Strings.sense_of_state
#print axioms Register.Strings.bit_kept
#print axioms Register.Strings.unscattered
#print axioms Crossing.two_crossings
#print axioms Register.Reg.matter
#print axioms Register.Reg.matter_eq
#print axioms Register.Reg.split_not_stringwise
#print axioms Register.Reg.radii_agree
#print axioms Register.Qubit.entropy_lt_of_energies_ne
#print axioms Register.Interpolation.sq_le_exp
#print axioms Register.Interpolation.exp_le_of_one_le
#print axioms Register.Interpolation.simple_root
#print axioms Register.Interpolation.simple_within
#print axioms Register.Einstein.quad_add_smul_eta_of_null
#print axioms Register.Einstein.vacuumModel
#print axioms Register.Einstein.any_constant_model
#print axioms Register.Reg.La_lt_L
#print axioms Register.Reg.horizon_limit

-- Secs. II–III, the chain
#print axioms Register.Reg.one_bit
#print axioms Register.Reg.area_in_cells
#print axioms Register.Reg.counts_leading_order
#print axioms Register.Reg.shares
#print axioms Register.Reg.lap_time
#print axioms Register.Reg.quarter_lap
#print axioms Register.Reg.bulk_counts
#print axioms Register.Reg.ratio_of_areas
#print axioms Register.Reg.observer_rings
#print axioms Register.Reg.T_ring
#print axioms Register.Reg.T_dS
#print axioms Register.Reg.La_lap
#print axioms Register.Reg.T_Unruh
#print axioms Register.Reg.eta_eq
#print axioms Register.Reg.clausius
#print axioms Register.Reg.G_eq
#print axioms Register.Reg.count_factor_pos
#print axioms Register.Reg.G_exact_bound
#print axioms Register.Reg.cell_from_G
#print axioms Register.Reg.entropy_quarter
#print axioms Register.Reg.quarter_any_count
#print axioms Register.Reg.G_mul_eta

-- Secs. III–IV, the solution about a mass and what follows from it
#print axioms Register.Reg.hasDerivAt_fSdS
#print axioms Register.Reg.gSdS_eq
#print axioms Register.Reg.pull_eq
#print axioms Register.Reg.deSitter
#print axioms Register.Reg.horizon_radius_eq
#print axioms Register.Reg.newton
#print axioms Register.Reg.equipartition_in_cells
#print axioms Register.Reg.fdS_eq
#print axioms Register.Reg.proper_distance_exists
#print axioms Register.Reg.proper_distance
#print axioms Register.Reg.sds_outer_horizon
#print axioms Register.Reg.horizon_period
#print axioms Register.Reg.horizon_temperature
#print axioms Register.Reg.surface_gravity_eq
#print axioms Register.Reg.thermal_lap

-- Sec. IV.C, the string
#print axioms Register.Reg.shift_in_cells
#print axioms Register.Reg.entropy_removed
#print axioms Register.Reg.massive_horizon_count
#print axioms Register.Reg.temperature_floor
#print axioms Register.Reg.SM_in_cells
#print axioms Register.Reg.area_deficit
#print axioms Register.Reg.shortfall_sum
#print axioms Register.Reg.removed_rings
#print axioms Register.Reg.removed_fraction
#print axioms Register.Reg.shortfall_removes
#print axioms Register.Reg.temperature_led

-- Sec. IV.C, the carriers and the law (Carriers.lean)
#print axioms Register.Law.share_of_equipartition
#print axioms Register.Law.exp_neg_taylor
#print axioms Register.Reg.ln2_lt_one
#print axioms Register.Reg.a0_pos
#print axioms Register.Reg.a0_depends_on_product
#print axioms Register.Reg.newton_share
#print axioms Register.Reg.share_acceleration
#print axioms Register.Law.gibbsMean_eq
#print axioms Register.Law.gibbsLadder_eq
#print axioms Register.Law.gibbsLadder_within_step
#print axioms Register.Reg.string_energy
#print axioms Register.Reg.fill_fraction
#print axioms Register.Reg.law
#print axioms Register.Reg.law_scale_mean
#print axioms Register.Reg.scale_over_time
#print axioms Register.Reg.Lambda_from_a0
#print axioms Register.Law.near_limit
#print axioms Register.Law.deep_limit
#print axioms Register.Law.classical_limit
#print axioms Register.Law.tully_fisher
#print axioms Register.Reg.radial_acceleration_relation
#print axioms Register.Reg.hypotheses_consistent

-- Secs. II and IV.C, the count and the chain joined
#print axioms Register.Bridge.counts_exact
#print axioms Register.Bridge.horizonWeight_quarter
#print axioms Register.Bridge.horizon_entropy_count
#print axioms Horizon.Positions.crossesHorizon
#print axioms Register.Bridge.horizon_counts_every_ring
#print axioms Register.Entropy.shannon_jointProb
#print axioms Register.Entropy.correlation_jointProb
#print axioms Register.Entropy.shannon_le_shannon_gibbs
#print axioms Register.Entropy.gibbs_two_equal
#print axioms Register.Bridge.horizonEntropy_eq_sum
#print axioms Register.Bridge.horizon_entropy

-- Secs. II and IV.E, the qubit of a free string: the tick keeps each string of one sense up to one
-- and the same phase (Postulate 1; alike in either sense, Postulate 2), so the two senses have one
-- energy and
-- the tick's phase is one for all the string's states (linearity); its thermal state is half the
-- identity, the Born rule gives either outcome the probability 1/2, and the string holds one bit
#print axioms Register.Qubit.eq_diagonal_of_keeps
#print axioms Register.Qubit.eq_smul_one_of_keeps
#print axioms Register.Qubit.Tick.phase_unique
#print axioms Register.Qubit.Tick.norm_scalar
#print axioms Register.Qubit.Tick.ofPhase
#print axioms Register.Qubit.thermal_of_equal
#print axioms Register.Qubit.bornProb_half
#print axioms Register.Qubit.bornProb_thermal
#print axioms Register.Qubit.prob_thermal
#print axioms Register.Qubit.entropy_thermal
#print axioms Register.Qubit.Tick.mulVec_e₁
#print axioms Register.Qubit.Tick.mulVec_e₂
#print axioms Register.Qubit.Tick.factor_eq
#print axioms Register.Qubit.Tick.energy_eq
#print axioms Register.Qubit.Tick.state_eq
#print axioms Register.Qubit.Tick.bornProb_state
#print axioms Register.Qubit.Tick.prob_state
#print axioms Register.Qubit.Tick.entropy_state
#print axioms Register.Qubit.share_stringState
#print axioms Register.Qubit.expected_share
#print axioms Register.Qubit.half_bits_thermal
#print axioms Register.Qubit.half_bits_model

-- Sec. II, the strings of a sphere and one ring through two cells, with the models of the sphere's
-- strings and of the count's distance to the horizon
#print axioms Register.Bridge.sphere_strings
#print axioms Register.Bridge.sphere_strings_of_rings
#print axioms Register.Bridge.sphere_strings_deSitter
#print axioms Register.Bridge.regSix
#print axioms Register.Bridge.sphere_strings_model
#print axioms Register.Bridge.ring_through_two_cells
#print axioms Register.Bridge.ring_distance_model

-- Secs. IV.D, V and VI: the ring, the pins and the equation of state
#print axioms Register.Reg.L_from_horizon
#print axioms Register.Reg.G_Lambda
#print axioms Register.Reg.black_hole_quarter
#print axioms Register.Reg.EΛ_eq
#print axioms Register.Reg.vacuum_per_string
#print axioms Register.Reg.string_tick
#print axioms Register.Reg.string_split
#print axioms Register.Reg.vacuum_share
#print axioms Register.Reg.vacuum_energy
#print axioms Register.Reg.ρΛ_eq
#print axioms Register.Reg.vacuum_ratio
#print axioms Register.Reg.komar_misner_sharp
#print axioms Register.Reg.EMS_exact
#print axioms Register.Reg.EMS_per_ring
#print axioms Register.Reg.komar_mass
#print axioms Register.Reg.push
#print axioms Register.Reg.hubble
#print axioms Register.Reg.zero_gravity
#print axioms Register.Reg.zero_gravity_mass
#print axioms Register.Reg.G_drift
#print axioms Register.Reg.constancy_of_Lambda
#print axioms Register.Reg.fluid_equation
#print axioms Register.Reg.w_exact
#print axioms Register.Reg.GLambda_constant
#print axioms Register.Reg.horizon_constant
#print axioms Register.Reg.Lambda_constant
#print axioms Register.Reg.G_constant
#print axioms Register.Reg.rhoΛ_constant
#print axioms Register.Reg.w_exact_in_time
#print axioms Register.Reg.Lambda_rate_in_time
#print axioms Register.Reg.w_bound

-- The paper's results from the sources and nothing else (`Main.lean`), whose hypotheses `#premises`
-- checks against `Sources.lean`
#print axioms Register.Main.count
#print axioms Register.Main.horizon_entropy
#print axioms Register.Main.jacobson_step
#print axioms Register.Main.jacobson_G_density
#print axioms Register.Main.jacobson_G
#print axioms Register.Main.jacobson_G_exact
#print axioms Register.Main.G_leading_order
#print axioms Register.Main.chain
#print axioms Register.Main.deSitter_horizon
#print axioms Register.Main.cell_from_G
#print axioms Register.Main.entropy_quarter
#print axioms Register.Main.newton
#print axioms Register.Main.entropy_removed
#print axioms Register.Main.entropy_removed_sphere
#print axioms Register.Main.entropy_removed_leading_order
#print axioms Register.Main.G_Lambda
#print axioms Register.Main.vacuum_density
#print axioms Register.Main.komar_misner_sharp
#print axioms Register.Main.black_hole_quarter
#print axioms Register.Main.string_energy
#print axioms Register.Main.vacuum_share
#print axioms Register.Main.horizon_quarter
#print axioms Register.Main.temperature_floor
#print axioms Register.Main.equation_of_state
#print axioms Register.Main.ceiling
#print axioms Register.Main.einstein
#print axioms Register.Main.matter_geodesic
#print axioms Register.Main.light_rays
#print axioms Register.Main.rotation_curve
#print axioms Register.Main.schwarzschild_deSitter
#print axioms Register.Main.lambda_with_mass
#print axioms Register.Main.horizon_drawn_in
#print axioms Register.Main.register_in_band
-- the paper's statements restated from the sources (v18-40)
#print axioms Register.Main.register_finite
#print axioms Register.Main.register_even
#print axioms Register.Main.ring_through_two_cells
#print axioms Register.Main.projective_plane
#print axioms Register.Main.rings_cross_horizon
#print axioms Register.Main.opposite_halfway
#print axioms Register.Main.string_one_bit
#print axioms Register.Main.share_of_bits
#print axioms Register.Main.area_in_cells
#print axioms Register.Main.L_from_horizon
#print axioms Register.Main.temperature_in_cells
#print axioms Register.Main.newton_in_cells
#print axioms Register.Main.quarter_any_count
#print axioms Register.Main.G_mul_eta
#print axioms Register.Main.komar_mass
#print axioms Register.Main.ceiling_in_step
#print axioms Register.Main.ceiling_logical
#print axioms Register.Main.one_cell_block
#print axioms Register.Main.coding_step
#print axioms Register.Main.repetition_code
#print axioms Register.Main.line_code
#print axioms Register.Main.surface_code
#print axioms Register.Main.massive_horizon
#print axioms Register.Main.black_hole_horizon
#print axioms Register.Main.temperature_led
#print axioms Register.Main.carriers_share
#print axioms Register.Main.fill_fraction
#print axioms Register.Main.galactic_law
#print axioms Register.Main.near_limit
#print axioms Register.Main.deep_limit
#print axioms Register.Main.tully_fisher
#print axioms Register.Main.classical_share
#print axioms Register.Main.scale_mean
#print axioms Register.Main.scale
#print axioms Register.Main.push
#print axioms Register.Main.zero_gravity
#print axioms Register.Main.hubble
#print axioms Register.Main.G_drift
#print axioms Register.Main.constants_in_time
#print axioms Register.Main.lambda_rate
#print axioms Register.Main.w_bound
#print axioms Register.Main.first_law_extended
#print axioms Register.Main.block_fraction
#print axioms Register.Main.gibbs
#print axioms Register.Main.sphere_strings
#print axioms Register.Main.observer_count
#print axioms Register.Main.observer_rings
#print axioms Register.Main.sphere_areal_radius
-- the sentences that the files had not stated (v18-65)
#print axioms Register.Main.ring_one_string
#print axioms Register.Main.lap
#print axioms Register.Main.two_senses
#print axioms Register.Main.sense_of_state
#print axioms Register.Main.free_tick_hidden
#print axioms Register.Main.bit_kept
#print axioms Register.Main.joint_frequency
#print axioms Register.Main.product_state
#print axioms Register.Main.strings_in_step
#print axioms Register.Main.overlap_bound
#print axioms Register.Main.return_bound
#print axioms Register.Main.vacuum_energy_unseen
#print axioms Register.Main.G_Lambda_bits
#print axioms Register.Main.frame_of_law
#print axioms Register.Main.pull_and_push
#print axioms Register.Main.simple_interpolation

-- The numbers (Table I, text, Appendix A), and the chain for these inputs
#print axioms Register.Numerics.reg_RL
#print axioms Register.Numerics.reg_deSitter
#print axioms Register.Numerics.reg_jacobson
#print axioms Register.Numerics.reg_cell
#print axioms Register.Numerics.reg_a0
#print axioms Register.Numerics.Gof_Lcos
#print axioms Register.Numerics.reg_temperature
#print axioms Register.Numerics.reg_clock
#print axioms Register.Numerics.reg_entropy
#print axioms Register.Numerics.reg_αs
#print axioms Register.Numerics.reg_sun_entropy
#print axioms Register.Numerics.reg_newton_earth
#print axioms Register.Numerics.cell_val
#print axioms Register.Numerics.cell_units
#print axioms Register.Numerics.observer_fraction_1m
#print axioms Register.Numerics.horizon_val
#print axioms Register.Numerics.Lcos_val
#print axioms Register.Numerics.log2_Lcos
#print axioms Register.Numerics.ceiling_cos
#print axioms Register.Numerics.nmax_cos
#print axioms Register.Numerics.logical_ceiling_cos
#print axioms Register.Numerics.ceiling_margins
#print axioms Register.Numerics.ceiling_entropy_range
#print axioms Register.Numerics.soft_ceilings
#print axioms Register.Numerics.average_block
#print axioms Register.Numerics.missing_fraction
#print axioms Register.Numerics.shots_fraction
#print axioms Register.Numerics.porter_thomas_bound
#print axioms Register.Numerics.log2_L73
#print axioms Register.Numerics.log2_planck_band
#print axioms Register.Numerics.Lof_box
#print axioms Register.Numerics.witness_in_band
#print axioms Register.Numerics.Gof_antitone
#print axioms Register.Numerics.ceiling_above_204
#print axioms Register.Numerics.powers_of_two
#print axioms Register.Numerics.palmer_211
#print axioms Register.Numerics.palmer_range
#print axioms Register.Numerics.horizon_counts
#print axioms Register.Numerics.davies
#print axioms Register.Numerics.lnN_val
#print axioms Register.Numerics.scatter_1MeV
#print axioms Register.Numerics.energy_today
#print axioms Register.Numerics.G_bracket
#print axioms Register.Numerics.Gof_factor_four
#print axioms Register.Numerics.sun_counts
#print axioms Register.Numerics.cosmic_mass_beyond_nariai
#print axioms Register.Numerics.earth_orbit
#print axioms Register.Numerics.solar_tests
#print axioms Register.Numerics.phase_grid
#print axioms Register.Numerics.a0_val
#print axioms Register.Numerics.a0_uncertainty
#print axioms Register.Numerics.a0_sigmas
#print axioms Register.Numerics.a0_local_H0
#print axioms Register.Numerics.threshold_mean_from_data
#print axioms Register.Numerics.two_pins
#print axioms Register.Numerics.coefficient_measured
#print axioms Register.Numerics.string_matter
#print axioms Register.Numerics.heat_per_string
#print axioms Register.Numerics.energy_inside_horizon
#print axioms Register.Numerics.vacuum_share
#print axioms Register.Numerics.tully_fisher_speeds
#print axioms Register.Numerics.deep_radii
#print axioms Register.Numerics.solar_system
#print axioms Register.Numerics.neptune_departure
#print axioms Register.Numerics.rar_table
#print axioms Register.Numerics.cassini_total_field
#print axioms Register.Numerics.galactic_tide
#print axioms Register.Numerics.test_body_excess
#print axioms Register.Numerics.temperature_led_numbers
#print axioms Register.Numerics.EΛ_val
#print axioms Register.Numerics.ρΛ_val
#print axioms Register.Numerics.GΛ_val
#print axioms Register.Numerics.temperature_and_clock
#print axioms Register.Numerics.zero_gravity_radius
#print axioms Register.Numerics.zero_gravity_masses
#print axioms Register.Numerics.vacuum_orders
#print axioms Register.Numerics.redshift_one
#print axioms Register.Numerics.constancy_numbers
