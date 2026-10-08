import RegisterGravity.Chain

/-!
# The strings of a sphere, from the symmetry of space (Sec. II, "Counting in the bulk")

Earlier versions of the paper listed the area law of a screen, that a sphere holds one string for
each ring's share of its area, as a reading of the postulates.  Here it is derived from the
symmetry of space, the input Sec. II names.  The strings are described at one point only, a cell
`P` of the sphere, where the effects of gravitation are seen; the count does not say where a ring
runs in the manifold.

The cell `P` lies on `L/2` rings (`Horizon.two_mul_card_through`).  A horizon gives the area of a
cell, since every cell lies on some horizon.  An observer's horizon is the cells that lie `⌊L/4⌋`
steps from his cell, two on each of the `L/2` rings through it: `L` cells
(`Horizon.Positions.card_dist_eq`, `Bridge.horizon_cells`).  They share the area `A_hor = L²ℓ_c²/π`
(`area_in_cells`).  By the symmetry of space no part of the horizon is preferred, so each cell takes
`Lℓ_c²/π` of area (`cellArea`, `cellArea_eq`).  The strings that cross the sphere at `P` therefore
number `π/2ℓ_c²` per unit of area (`crossingDensity`, `crossingDensity_eq`), and the same holds at
every cell of the sphere.  That is the hypothesis `hsym`.  A string that enters a sphere leaves it,
so it crosses the sphere twice (the hypothesis `htwice`), and the sphere holds one string for each
`4ℓ_c²/π` of its area.  The number of strings held by a sphere of areal radius `r`, the `r` for
which its area is `4πr²`, is therefore the horizon's number of strings, `L²/4`, times the ratio of
the sphere's area to the horizon's: `Ns r`, Eq. (N) (`strings_from_symmetry`).  The strings per unit
area are the same on every sphere (`density_uniform`); the paper uses that on every surface,
Sec. III on every local horizon and Sec. IV.C on spheres about a mass.  At the horizon's own radius
the sphere holds every ring, which the register gives on its own
(`Horizon.Positions.horizon_weight_ring`, `Bridge.horizon_entropy_count`): the two counts agree on
the horizon's entropy (Sec. IV.C).  `symmetry_model` shows that the hypotheses can be met, so no
theorem here holds vacuously.

`cellArea` is the area of one of the `L` cells of a horizon.  It is not `cellShare` of
`Chain.lean`, the horizon's area over all the register's `L²/2` cells, which the paper does not
use.
-/

namespace Register
namespace Reg

variable (R : Reg)

/-- **The area of a cell** (Sec. II, "Counting in the bulk").  An observer's horizon is the `L`
cells that lie `⌊L/4⌋` steps from his cell (`Horizon.Positions.card_dist_eq`,
`Bridge.horizon_cells`).  They share the area `A_hor`, and by the symmetry of space no part of the
horizon is preferred, so each cell takes `A_hor/L` of area. -/
noncomputable def cellArea : ℝ := R.Ahor / R.L

/-- A cell takes `Lℓ_c²/π` of area, and the `L` cells of a horizon make up its area. -/
theorem cellArea_eq : R.cellArea = R.L * R.ℓc ^ 2 / R.pi ∧ R.L * R.cellArea = R.Ahor := by
  reg_facts R
  unfold cellArea
  rw [R.area_in_cells]
  constructor
  · field_simp
  · field_simp

/-- the strings that cross a unit of area, counted at a cell: the `L/2` rings through it
(`Horizon.two_mul_card_through`) over the area it takes -/
noncomputable def crossingDensity : ℝ := (R.L / 2) / R.cellArea

/-- **Strings cross a surface `π/2ℓ_c²` times per unit of its area**: `L` cancels; that is two
crossings for each ring's share `4ℓ_c²/π`; on the horizon it is two for each of the register's
`L²/4` rings; and on a sphere of areal radius `r` it is `N_c(r) = 2N_s(r)` crossings. -/
theorem crossingDensity_eq :
    R.crossingDensity = R.pi / (2 * R.ℓc ^ 2) ∧ R.crossingDensity = 2 / R.ringShare ∧
    R.crossingDensity * R.Ahor = 2 * R.Rhor ∧
    ∀ r : ℝ, R.crossingDensity * (4 * R.pi * r ^ 2) = R.Nc r := by
  reg_facts R
  have h1 : R.crossingDensity = R.pi / (2 * R.ℓc ^ 2) := by
    unfold crossingDensity
    rw [(R.cellArea_eq).1]
    field_simp
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h1, (R.shares).2]
    field_simp
    ring
  · rw [h1, R.area_in_cells]
    unfold Rhor
    field_simp
    ring
  · intro r
    rw [h1, (R.bulk_counts r).1]
    unfold n
    field_simp
    ring

/-- **The strings of a sphere, from the symmetry of space** (Sec. II, "Counting in the bulk").
`crossings A` is the number of times strings cross a closed surface of area `A`, and `strings r`
the number of strings of the sphere of areal radius `r`.  The symmetry of space is the hypothesis
`hsym`: no part of a horizon is preferred, so each cell takes `Lℓ_c²/π` of area, and with `L/2`
rings through a cell the strings that cross a surface number `crossingDensity` per unit of its
area, the same at every cell of it.  `htwice` is that a string that enters a sphere leaves it, so
it crosses the sphere twice.  Then the number of strings held by the sphere of areal radius `r` is
the horizon's number of strings times the ratio of the sphere's area to the horizon's,
`R_hor (r/R_Λ)²`, which is `Ns r`, Eq. (N).  This is the area law of a screen; here it is derived.
At the horizon's own radius the sphere holds every ring, which the register gives on its own
(`Bridge.horizon_entropy_count`). -/
theorem strings_from_symmetry (crossings strings : ℝ → ℝ)
    (hsym : ∀ A, 0 ≤ A → crossings A = R.crossingDensity * A)
    (htwice : ∀ r, 0 ≤ r → crossings (4 * R.pi * r ^ 2) = 2 * strings r)
    (r : ℝ) (hr : 0 ≤ r) :
    strings r = R.Ns r ∧ strings r = R.Rhor * (r / R.RL) ^ 2 ∧
    crossings (4 * R.pi * r ^ 2) = R.Nc r ∧ strings R.RL = R.Rhor := by
  reg_facts R
  have hRL := R.RL_pos
  have key : ∀ ρ, 0 ≤ ρ → strings ρ = R.Ns ρ := by
    intro ρ hρ
    have hA : 0 ≤ 4 * R.pi * ρ ^ 2 := by positivity
    have h2 : 2 * strings ρ = 2 * R.Ns ρ := by
      rw [← htwice ρ hρ, hsym _ hA, (R.crossingDensity_eq).2.2.2 ρ]
      rfl
    linarith
  refine ⟨key r hr, ?_, ?_, ?_⟩
  · rw [key r hr]
    exact (R.ratio_of_areas r).1
  · have hA : 0 ≤ 4 * R.pi * r ^ 2 := by positivity
    rw [hsym _ hA]
    exact (R.crossingDensity_eq).2.2.2 r
  · rw [key R.RL hRL.le, (R.ratio_of_areas R.RL).1, div_self hRL.ne']
    ring

/-- **The strings per unit area are the same on every sphere** (Sec. II; the paper uses it on
every surface, Sec. III on every local horizon and Sec. IV.C on spheres about a mass): with
`strings_from_symmetry`, the sphere of areal radius `r`, of area `4πr²`, holds `R_hor/A_hor`
strings per unit area, one for each ring's share `4ℓ_c²/π`, whatever `r > 0` is. -/
theorem density_uniform (crossings strings : ℝ → ℝ)
    (hsym : ∀ A, 0 ≤ A → crossings A = R.crossingDensity * A)
    (htwice : ∀ r, 0 ≤ r → crossings (4 * R.pi * r ^ 2) = 2 * strings r)
    (r : ℝ) (hr : 0 < r) :
    strings r / (4 * R.pi * r ^ 2) = R.Rhor / R.Ahor ∧
    strings r / (4 * R.pi * r ^ 2) = 1 / R.ringShare := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  have hRh : R.Rhor ≠ 0 := by unfold Rhor; positivity
  have hr' := hr.ne'
  rw [(R.strings_from_symmetry crossings strings hsym htwice r hr.le).2.1]
  constructor
  · unfold Ahor
    field_simp
  · unfold ringShare Ahor
    field_simp

/-- **The hypotheses are met**, so no theorem above holds vacuously: the crossings
`crossingDensity · A` of a surface of area `A` and the strings `Ns r` of a sphere meet `hsym` and
`htwice`. -/
theorem symmetry_model :
    (∀ A, 0 ≤ A → (fun A => R.crossingDensity * A) A = R.crossingDensity * A) ∧
    (∀ r, 0 ≤ r → (fun A => R.crossingDensity * A) (4 * R.pi * r ^ 2) = 2 * R.Ns r) := by
  refine ⟨fun _ _ => rfl, fun r _ => ?_⟩
  show R.crossingDensity * (4 * R.pi * r ^ 2) = 2 * R.Ns r
  rw [(R.crossingDensity_eq).2.2.2 r]
  rfl

end Reg
end Register
