import RegisterGravity
import RegisterGravity.Models

/-! # The axiom ledger

For every main theorem, the axioms its proof depends on.  A physical input is never an axiom
here: it is a named hypothesis in the statement of the theorem that uses it (see `Chain.lean`).
The expected output for every line is `[propext, Classical.choice, Quot.sound]`, the
logical minimum of classical mathematics in Lean; `sorryAx` would flag an unfinished proof. -/

-- Sec. II, the count (Postulates 1–2), and a model of its axioms
#print axioms Horizon.fano
#print axioms Horizon.fano_counts
#print axioms Horizon.fano_order
#print axioms Horizon.counts
#print axioms Horizon.even_L
#print axioms Horizon.two_mul_order_add_one
#print axioms Horizon.card_loop_eq_order
#print axioms Horizon.order_count_consistent

-- Sec. II–III, algebra of the chain
#print axioms Register.Reg.shares
#print axioms Register.Reg.lap_time
#print axioms Register.Reg.quarter_lap
#print axioms Register.Reg.bulk_counts
#print axioms Register.Reg.ratio_of_areas
#print axioms Register.Reg.T_dS
#print axioms Register.Reg.T_Unruh
#print axioms Register.Reg.eta_eq
#print axioms Register.Reg.area_per_heat
#print axioms Register.Reg.G_eq
#print axioms Register.Reg.cell_from_G
#print axioms Register.Reg.entropy_quarter
#print axioms Register.Reg.entropy_misprint
#print axioms Register.Reg.G_mul_eta

-- Secs. III–IV, the solution about a mass and what follows from it
#print axioms Register.Reg.hasDerivAt_fSdS
#print axioms Register.Reg.gSdS_eq
#print axioms Register.Reg.gSdS_mass
#print axioms Register.Reg.deSitter
#print axioms Register.Reg.newton
#print axioms Register.Reg.gauss

-- Sec. IV.C, the string
#print axioms Register.Reg.sds_horizon_shift
#print axioms Register.Reg.shift_in_cells
#print axioms Register.Reg.entropy_removed
#print axioms Register.Reg.temperature_floor
#print axioms Register.Reg.SM_in_cells
#print axioms Register.Reg.area_deficit
#print axioms Register.Reg.removed_rings
#print axioms Register.Reg.string_share
#print axioms Register.Reg.Sin_share
#print axioms Register.Reg.Sin_eq
#print axioms Register.Reg.crossing
#print axioms Register.Reg.V0_eq
#print axioms Register.Reg.VM_linear
#print axioms Register.Reg.elastic
#print axioms Register.Reg.aM_values
#print axioms Register.Reg.apparent_mass
#print axioms Register.Reg.tully_fisher
#print axioms Register.Reg.galactic_pin
#print axioms Register.Reg.temperature_led

-- Sec. IV.D and V, the ring and the pins
#print axioms Register.Reg.L_from_horizon
#print axioms Register.Reg.G_Lambda
#print axioms Register.Reg.EΛ_eq
#print axioms Register.Reg.ρΛ_eq
#print axioms Register.Reg.push
#print axioms Register.Reg.hubble
#print axioms Register.Reg.zero_velocity
#print axioms Register.Reg.crossover
#print axioms Register.Reg.Lambda_from_aM
#print axioms Register.Reg.pins_ratio
#print axioms Register.Reg.aM_depends_on_product
#print axioms Register.Reg.G_drift
#print axioms Register.Reg.fluid_equation
#print axioms Register.Reg.w_exact
#print axioms Register.Reg.w_bound

-- Numbers (Table I, text, Appendix A)
#print axioms Register.Numerics.reg_jacobson
#print axioms Register.Numerics.reg_RL
#print axioms Register.Numerics.reg_deSitter
#print axioms Register.Numerics.reg_aM
#print axioms Register.Numerics.Gof_Lcos
#print axioms Register.Numerics.reg_temperature
#print axioms Register.Numerics.lc_val
#print axioms Register.Numerics.lP_val
#print axioms Register.Numerics.cell_units
#print axioms Register.Numerics.Hinf_val
#print axioms Register.Numerics.RL_val
#print axioms Register.Numerics.Lambda_val
#print axioms Register.Numerics.surface_gravity
#print axioms Register.Numerics.Lcos_val
#print axioms Register.Numerics.capacity
#print axioms Register.Numerics.ceiling_cos
#print axioms Register.Numerics.nmax_cos
#print axioms Register.Numerics.log2_Lcos
#print axioms Register.Numerics.palmer_211
#print axioms Register.Numerics.horizon_counts
#print axioms Register.Numerics.davies
#print axioms Register.Numerics.G_bracket
#print axioms Register.Numerics.G_mid
#print axioms Register.Numerics.sun_counts
#print axioms Register.Numerics.earth_orbit
#print axioms Register.Numerics.solar_tests
#print axioms Register.Numerics.phase_grid
#print axioms Register.Numerics.aM_val
#print axioms Register.Numerics.reg_aM_val
#print axioms Register.Numerics.aM_vs_observation
#print axioms Register.Numerics.coefficients
#print axioms Register.Numerics.Lgal_val
#print axioms Register.Numerics.nmax_gal
#print axioms Register.Numerics.pins_agree
#print axioms Register.Numerics.temperature_led_numbers
#print axioms Register.Numerics.tully_fisher_speed
#print axioms Register.Numerics.EΛ_val
#print axioms Register.Numerics.ρΛ_val
#print axioms Register.Numerics.GΛ_val
#print axioms Register.Numerics.temperature_and_clock
#print axioms Register.Numerics.zero_velocity_radii
#print axioms Register.Numerics.crossover_radius
#print axioms Register.Numerics.redshift_one
#print axioms Register.Numerics.constancy_numbers
