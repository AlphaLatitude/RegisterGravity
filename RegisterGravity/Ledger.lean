import RegisterGravity

/-! # The axiom ledger

For every main theorem, the axioms its proof depends on.  A physical input is never an axiom
here: it is a named hypothesis in the statement of the theorem that uses it (see `Chain.lean`).
The expected output for every line is `[propext, Classical.choice, Quot.sound]`, the
logical minimum of classical mathematics in Lean; an unfinished proof would show up as an extra axiom. -/

-- Sec. II, the count (Postulates 1–2), the projective plane, and a model of the axioms
#print axioms Horizon.exists_loop_not_mem
#print axioms Horizon.two_mul_card_through
#print axioms Horizon.counts
#print axioms Horizon.even_L
#print axioms Horizon.two_mul_order_add_one
#print axioms Horizon.card_loop_eq_order
#print axioms Horizon.order_count_consistent
#print axioms Horizon.fano
#print axioms Horizon.fano_counts
#print axioms Horizon.fano_order
-- Sec. II, the dimension of space from the incidence of the rings
#print axioms Register.Dimension.planes_meet
#print axioms Register.Dimension.disjoint_planes_exist
#print axioms Register.Dimension.dimension_three
#print axioms Horizon.fanoPositions
#print axioms Horizon.fano_even

-- Secs. II and IV.C, the cyclic order of the rings and where the strings hold their entropy
#print axioms Horizon.Positions.even_of_halfway
#print axioms Horizon.Positions.card_ringDist
#print axioms Horizon.Positions.card_dist_eq
#print axioms Horizon.Positions.card_dist_le
#print axioms Horizon.Positions.dist_opp
#print axioms Horizon.Positions.sphere_count
#print axioms Horizon.Positions.per_distance_count
#print axioms Horizon.Positions.horizon_weight_ring
#print axioms Horizon.Positions.route_B_fraction

-- Secs. IV.A and V, the qubit ceiling
#print axioms Register.Capacity.two_le_card_of_frac
#print axioms Register.Capacity.one_cell_block
#print axioms Register.Capacity.product_state
#print axioms Register.Capacity.ceiling
#print axioms Register.Capacity.ceiling_soft
#print axioms Register.Capacity.nmax_iff
#print axioms Register.Capacity.palmer_threshold

-- Secs. II–III, the chain
#print axioms Register.Reg.one_bit
#print axioms Register.Reg.area_in_cells
#print axioms Register.Reg.counts_leading_order
#print axioms Register.Reg.shares
#print axioms Register.Reg.lap_time
#print axioms Register.Reg.quarter_lap
#print axioms Register.Reg.bulk_counts
#print axioms Register.Reg.ratio_of_areas
#print axioms Register.Reg.T_ring
#print axioms Register.Reg.T_dS
#print axioms Register.Reg.La_lap
#print axioms Register.Reg.T_Unruh
#print axioms Register.Reg.temperature_is_quantum_over_two_pi
#print axioms Register.Reg.eta_eq
#print axioms Register.Reg.clausius
#print axioms Register.Reg.einstein_coefficient
#print axioms Register.Reg.G_eq
#print axioms Register.Reg.cell_from_G
#print axioms Register.Reg.entropy_quarter
#print axioms Register.Reg.quarter_any_count
#print axioms Register.Reg.G_mul_eta

-- Secs. III–IV, the solution about a mass and what follows from it
#print axioms Register.Reg.hasDerivAt_fSdS
#print axioms Register.Reg.gSdS_eq
#print axioms Register.Reg.gSdS_mass
#print axioms Register.Reg.deSitter
#print axioms Register.Reg.newton
#print axioms Register.Reg.equipartition_in_cells
#print axioms Register.Reg.gauss
#print axioms Register.Reg.fdS_eq
#print axioms Register.Reg.proper_distance_exists
#print axioms Register.Reg.proper_distance
#print axioms Register.Reg.sds_horizon_shift
#print axioms Register.Reg.sds_outer_horizon
#print axioms Register.Reg.horizon_period
#print axioms Register.Reg.horizon_temperature
#print axioms Register.Reg.horizon_radius

-- Sec. IV.C, the string
#print axioms Register.Reg.shift_in_cells
#print axioms Register.Reg.entropy_removed
#print axioms Register.Reg.temperature_floor
#print axioms Register.Reg.SM_in_cells
#print axioms Register.Reg.area_deficit
#print axioms Register.Reg.shortfall_sum
#print axioms Register.Reg.removed_rings
#print axioms Register.Reg.shortfall_removes
#print axioms Register.Reg.string_share
#print axioms Register.Reg.Sin_share
#print axioms Register.Reg.Sin_eq
#print axioms Register.Reg.crossing
#print axioms Register.Reg.V0_eq
#print axioms Register.Reg.VM_linear
#print axioms Register.Reg.differentiate_equality
#print axioms Register.Reg.elastic
#print axioms Register.Reg.deep_bound
#print axioms Register.Reg.deep_regime_upper_bound
#print axioms Register.Reg.aM_values
#print axioms Register.Reg.apparent_mass
#print axioms Register.Reg.tully_fisher
#print axioms Register.Reg.galactic_pin
#print axioms Register.Reg.galactic_bound
#print axioms Register.Reg.temperature_led

-- Secs. II and IV.C, the count and the chain joined
#print axioms Register.Bridge.counts_exact
#print axioms Register.Bridge.Sin_from_count

-- Secs. IV.D and V, the ring and the pins
#print axioms Register.Reg.L_from_horizon
#print axioms Register.Reg.G_Lambda
#print axioms Register.Reg.EΛ_eq
#print axioms Register.Reg.ρΛ_eq
#print axioms Register.Reg.vacuum_ratio
#print axioms Register.Reg.komar_misner_sharp
#print axioms Register.Reg.komar_mass
#print axioms Register.Reg.push
#print axioms Register.Reg.hubble
#print axioms Register.Reg.zero_gravity
#print axioms Register.Reg.zero_gravity_mass
#print axioms Register.Reg.crossover
#print axioms Register.Reg.crossover_speed
#print axioms Register.Reg.Lambda_from_aM
#print axioms Register.Reg.pins_ratio
#print axioms Register.Reg.aM_depends_on_product
#print axioms Register.Reg.G_drift
#print axioms Register.Reg.constancy_of_Lambda
#print axioms Register.Reg.fluid_equation
#print axioms Register.Reg.w_exact
#print axioms Register.Reg.w_bound

-- The numbers (Table I, text, Appendix A), and the chain for these inputs
#print axioms Register.Numerics.reg_RL
#print axioms Register.Numerics.reg_deSitter
#print axioms Register.Numerics.reg_jacobson
#print axioms Register.Numerics.reg_cell
#print axioms Register.Numerics.reg_aM
#print axioms Register.Numerics.Gof_Lcos
#print axioms Register.Numerics.reg_temperature
#print axioms Register.Numerics.reg_clock
#print axioms Register.Numerics.reg_entropy
#print axioms Register.Numerics.reg_αs
#print axioms Register.Numerics.reg_sun_entropy
#print axioms Register.Numerics.reg_newton_earth
#print axioms Register.Numerics.reg_aM_val
#print axioms Register.Numerics.cell_val
#print axioms Register.Numerics.cell_units
#print axioms Register.Numerics.horizon_val
#print axioms Register.Numerics.Lcos_val
#print axioms Register.Numerics.log2_Lcos
#print axioms Register.Numerics.ceiling_cos
#print axioms Register.Numerics.nmax_cos
#print axioms Register.Numerics.ceiling_margins
#print axioms Register.Numerics.log2_L73
#print axioms Register.Numerics.log2_planck_band
#print axioms Register.Numerics.Gof_antitone
#print axioms Register.Numerics.ceiling_above_204
#print axioms Register.Numerics.powers_of_two
#print axioms Register.Numerics.palmer_211
#print axioms Register.Numerics.palmer_range
#print axioms Register.Numerics.horizon_counts
#print axioms Register.Numerics.davies
#print axioms Register.Numerics.G_bracket
#print axioms Register.Numerics.Gof_factor_four
#print axioms Register.Numerics.sun_counts
#print axioms Register.Numerics.earth_orbit
#print axioms Register.Numerics.solar_tests
#print axioms Register.Numerics.phase_grid
#print axioms Register.Numerics.sun_crossing
#print axioms Register.Numerics.aM_val
#print axioms Register.Numerics.aM_vs_observation
#print axioms Register.Numerics.coefficients
#print axioms Register.Numerics.Lgal_val
#print axioms Register.Numerics.log2_Lgal
#print axioms Register.Numerics.pins_agree
#print axioms Register.Numerics.temperature_led_numbers
#print axioms Register.Numerics.tully_fisher_speed
#print axioms Register.Numerics.EΛ_val
#print axioms Register.Numerics.ρΛ_val
#print axioms Register.Numerics.GΛ_val
#print axioms Register.Numerics.temperature_and_clock
#print axioms Register.Numerics.zero_gravity_masses
#print axioms Register.Numerics.crossover_radius
#print axioms Register.Numerics.vacuum_orders
#print axioms Register.Numerics.redshift_one
#print axioms Register.Numerics.constancy_numbers
