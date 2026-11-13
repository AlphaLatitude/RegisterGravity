import RegisterGravity.Sources
import RegisterGravity.Premises
import RegisterGravity.Numerics
import RegisterGravity.Singer
import RegisterGravity.TwoCells
import RegisterGravity.Pairing
import RegisterGravity.Interpolation
import RegisterGravity.Strings
import RegisterGravity.Constant

/-!
# The paper's results, from the sources and nothing else (Secs. II–VI)

Each theorem here is one of the paper's results, stated with the definitions of `Sources.lean` as
its only hypotheses: a sentence of Postulate 1 or 2 or a definition of Sec. II (`P1.`, `P2.`), a
statement of thermodynamics (`Thermo.`), the gates of quantum mechanics (`QM.`) or a theorem of
the manifold's geometry, mathematics cited (`Geometry.`), a condition that defines
the quantity the result treats (`Condition.`), a result derived here from those (`Derived.`,
each with its own theorem below, or that theorem at every time), a step at leading order in `1/L`
whose exact form a theorem below
derives (`Approx.`), or the units the results are stated in (`Units.`); no premise is listed as open
(`Open.`).  The gates of Sec. IV.A, the paper's input from quantum mechanics, are the premise
of `return_bound`.
The proofs apply
the theorems of the other files, with short arguments joining them.

The command `#premises` at the end checks every theorem of this file at build time: each hypothesis
must be a definition of `Sources.lean` (or the class `NeZero` or `Nonempty`), and each object's type
must be one
of the types listed in `Premises.lean`.  Its output is the file `premises_output.txt`, which the
continuous integration compares with the output of the build.  The command also checks that every
result takes something from a source: a premise of Postulate 1 or 2, of thermodynamics, of quantum
mechanics or of the cited geometry, a derived statement, or an object of a structure that carries
clauses of the postulates.  A result that takes nothing and states no instance of such a
structure fails the build, and `register_in_band` is the one result that states an instance.  The
command checks that every derived statement is the conclusion of a result that takes something
from a source, or is such a statement at every time, and that every theorem of this file's
namespace that stands before the command is among the results it is given.  It checks that no
result names a measured number: a constant of `Numerics.lean`, a decimal or a whole number above
100, in its statement or in a definition under it, but for `register_in_band`, which states an
instance.  These checks read
what a result takes.  Whether the conclusion needs a premise depends on the statement, and no
check tests it.  A result may state, beside what its premises give, a step of mathematics that
needs none of them, as `coding_step` states the count of a code's conditional states and
`ring_through_two_cells` the geodesic through two points.  Where a part of a result is known to
need no premise, its docstring says so.  A side condition states the case that the paper treats,
a positive radius or at least one qubit (`1 ≤ N`), and some conclusions hold beyond their
conditions, as the field of `hubble` does at every `r`.
-/

open Horizon Finset Filter Topology Register.Sources

namespace Register.Main

variable {L : ℕ}

/-- **The count** (Sec. II, Eq. (counts)): `L/2` largest rings through every cell, `2C + 2L = L² + 4`
cells, `4R + 2L = L² + 4` largest rings, `C = 2R`.  Sources: Postulate 2's clauses on incidence
(the structure `Horizon`), whose fourth gives `4 ≤ L` (`Horizon.four_le`). -/
theorem count (H : Horizon L) :
    (∀ P : H.Cell, 2 * (H.through P).card = L) ∧
    2 * Fintype.card H.Cell + 2 * L = L ^ 2 + 4 ∧
    4 * Fintype.card H.Loop + 2 * L = L ^ 2 + 4 ∧
    Fintype.card H.Cell = 2 * Fintype.card H.Loop :=
  H.counts H.four_le

/-- **The horizon's entropy is one bit per ring** (Sec. II, Eq. (S)).  The second part writes the
count of the rings (`count`) with `S_hor`; it takes the structure and the condition `R.L = L`, and
no premise of thermodynamics.  Sources: the thermal state of free strings, the product of their
own, and the senses' probabilities from each string's (thermodynamics; `hfree`, `hq`), the two
senses with one energy (Postulate 2 on the tick, in `Tick`), one qubit per string (Postulate 1, in
`Tick`); Postulate 2's fourth clause, which gives `4 ≤ L` (`Horizon.four_le`); and the condition
`R.L = L`. -/
theorem horizon_entropy (H : Horizon L) (R : Reg) (hRL : Condition.same_L R L) [NeZero L] (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ)
    (P : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) (hfree : Thermo.free_strings H P q)
    (hq : Thermo.sense_from_state H T β En q) :
    Bridge.horizonEntropy H P = Fintype.card H.Loop * Real.log 2 ∧
    (Fintype.card H.Loop : ℝ) * Real.log 2 = R.Shor * (1 - 2 / R.L + 4 / R.L ^ 2) :=
  Bridge.horizon_entropy H R H.four_le hRL T β En P q hfree hq

/-- **Jacobson's step at every point** (Sec. III): with one entropy density `η₀ ≠ 0` on every
local horizon, `R_ab k^a k^b = κ T_ab k^a k^b` for every null `k` at every point, with
`κ = 2πk_B/(ℏcη₀)`.  The local Rindler horizon through a point, generated by `k` and held by the
boost of acceleration `a`, changes its area as the Raychaudhuri equation says, `R_ab k^a k^b` per
unit of `−λ dλ dA` (`Geometry.raychaudhuri`); its entropy changes as `η₀` times its area
(`P1.local_entropy`); and the energy that crosses it, the boost-energy flux of matter,
`(a/c²) T_ab k^a k^b` per unit, is heat at the temperature of its period (`Thermo.local_clausius`).
At `a = 1` that temperature is `ℏ/(2πck_B)` (`Reg.La_lap`), and the acceleration cancels in any
case.  Sources: the Raychaudhuri equation (Lorentzian geometry); the register's
entropy on a local horizon (Postulate 1's first sentence applied to the local horizon's entropy),
for a density that is the same on every local horizon, which the conclusion takes as its
hypothesis and `jacobson_G` and `einstein` meet with Postulate 2's clauses; the energy that
crosses a local horizon is heat at its temperature (thermodynamics). -/
theorem jacobson_step {H : Horizon L} (R : Reg) (η : H.Cell → H.Loop → ℝ)
    (M : Einstein.Spacetime) (dA dS : M.Pt → (Fin 4 → ℝ) → ℝ) (hray : Geometry.raychaudhuri M dA)
    (hent : P1.local_entropy H η M dS dA) (hcl : Thermo.local_clausius R M dS) :
    Derived.clausius H R η M := by
  intro η₀ hη0 hη p k hk
  reg_facts R
  -- the boost of acceleration `1`, at the temperature of its period
  have hT : Thermo.horizon_thermal R 1 (R.ℏ / (R.La 1 * R.tc) / R.kB) := by
    show R.kB * (R.ℏ / (R.La 1 * R.tc) / R.kB) = R.ℏ / (R.La 1 * R.tc)
    field_simp
  have h1 := hcl 1 _ one_pos hT p k hk
  rw [show dS p k = η₀ * dA p k from hent η₀ hη p k hk, hray p k hk, R.La_lap 1 one_pos] at h1
  -- `(1/c²) T(k, k) = (ℏ/2πck_B) η₀ R(k, k)`
  have hT0 : R.ℏ / (2 * R.pi * R.c / 1) / R.kB ≠ 0 := by positivity
  have hR : Einstein.quad (M.ric p) k = 1 / R.c ^ 2 * Einstein.quad (M.stress p) k /
      (R.ℏ / (2 * R.pi * R.c / 1) / R.kB * η₀) := by
    rw [h1]; field_simp
  rw [hR]
  field_simp

/-- **Newton's constant from Jacobson's step, for any entropy density** (Sec. III): with one
entropy density on every local horizon, the register's law `η` read at a cell, positive, Jacobson's
step gives `G = c³k_B/(4ℏη(x₀, l₀))`, whatever the density's value.  `jacobson_G` and
`jacobson_G_exact` give it at the count's density, at leading order and exactly;
`lambda_with_mass` takes it for any density.  Sources: Postulate 2's two clauses on laws, for the
entropy density; Jacobson's step at every point (`Derived`, `jacobson_step`); the static weak field
(Lorentzian geometry); and the conditions: a cell on a ring, where the density is read, the density
positive, matter at rest at the point, Newton's law defining `G`. -/
theorem jacobson_G_density {H : Horizon L} (R : Reg) (G : ℝ)
    (η : H.Cell → H.Loop → ℝ) (hsym : P2.homogeneous H η) (hdir : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀) (hη : Condition.pos (η x₀ l₀))
    (M : Einstein.Spacetime) (hcl : Derived.clausius H R η M) (p : M.Pt) (A ρ : ℝ)
    (hweak : Geometry.weak_field M p A) (hdust : Condition.dust R M p ρ)
    (hN : Condition.newton_G R G A ρ) :
    Derived.jacobson_G_density R G (η x₀ l₀) :=
  Solution.jacobson_G_from_sources R G η hsym hdir h₀ _
    (show (0 : ℝ) < η x₀ l₀ from hη).ne' rfl M hcl p A ρ hweak hdust.1 hdust.2 hN

/-- **Newton's constant from Jacobson's step with the count's density, at leading order in `1/L`**
(Sec. III): `G = c³k_B/(4ℏη)`.  The density is that of the horizon of the solution without a mass,
whose radius is `R_Λ` (`Reg.horizon_radius_eq`), with the count's `L²/4` rings (`Approx`).
Sources: Postulate 2's two clauses on laws, for the entropy density; Jacobson's step at every point
(`Derived`, `jacobson_step`), without the conservation law; the static weak field (Lorentzian
geometry); the constant of the solution without a mass (`Derived`); the count's density at leading
order (`Approx`);
and the conditions: the crossing `(x₀, l₀)` is one (`h₀`), the horizon's radius, matter at rest at
the point, Newton's law defining `G`. -/
theorem jacobson_G {H : Horizon L} (R : Reg) (G : ℝ) (η : H.Cell → H.Loop → ℝ)
    (hsym : P2.homogeneous H η) (hdir : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀) (Λ rh : ℝ)
    (hdS : Derived.deSitter_horizon R G Λ) (hrh : Condition.horizon_radius R G Λ rh)
    (hcount : Approx.count_density H R η l₀ x₀ rh)
    (M : Einstein.Spacetime) (hcl : Derived.clausius H R η M) (p : M.Pt) (A ρ : ℝ)
    (hweak : Geometry.weak_field M p A) (hdust : Condition.dust R M p ρ)
    (hN : Condition.newton_G R G A ρ) :
    Derived.jacobson_G R G := by
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  have hc : η x₀ l₀ = R.kB * (R.Rhor * R.ln2) / (4 * R.pi * rh ^ 2) := hcount
  have hη : η x₀ l₀ = R.η := by rw [hc, hr]; rfl
  exact Solution.jacobson_G_from_sources R G η hsym hdir h₀ R.η (Solution.eta_pos R).ne' hη
    M hcl p A ρ hweak hdust.1 hdust.2 hN

/-- **Newton's constant from Jacobson's step with the count's exact density** (Sec. III.C):
`G = c³k_B/(4ℏη(1 − 2/L + 4/L²))`, with the count's `L²/4 − L/2 + 1` rings on the horizon of the
solution without a mass (`Bridge.counts_exact`, `Reg.horizon_radius_eq`).  Sources: those of
`jacobson_G`, with the count's exact density derived in place of the leading-order step, from
Postulate 1's first sentence for the horizon's entropy (`hhor`), the thermal state of free strings
with the senses' probabilities from it (thermodynamics; `hfree`, `hq`) and the tick of a free
string (Postulates 1 and 2, in `Tick`), which give the horizon one bit for each largest ring
(`Bridge.horizon_entropy`); Postulate 2's fourth clause, which gives the count's `4 ≤ L`
(`Horizon.four_le`); and the condition `R.L = L`. -/
theorem jacobson_G_exact {H : Horizon L} (R : Reg) (G : ℝ)
    (η : H.Cell → H.Loop → ℝ) (hsym : P2.homogeneous H η) (hdir : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀)
    (hRL : Condition.same_L R L) (Λ rh : ℝ)
    (hdS : Derived.deSitter_horizon R G Λ) (hrh : Condition.horizon_radius R G Λ rh)
    [NeZero L] (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ)
    (P : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) (hfree : Thermo.free_strings H P q)
    (hq : Thermo.sense_from_state H T β En q) (hhor : P1.horizon_entropy H R η l₀ x₀ rh P)
    (M : Einstein.Spacetime) (hcl : Derived.clausius H R η M) (p : M.Pt) (A ρ : ℝ)
    (hweak : Geometry.weak_field M p A) (hdust : Condition.dust R M p ρ)
    (hN : Condition.newton_G R G A ρ) :
    Derived.jacobson_G_exact R G := by
  have hL : 4 ≤ L := H.four_le
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  -- the horizon's entropy, one bit for each largest ring, over its area
  have hS := (Bridge.horizon_entropy H R hL hRL T β En P q hfree hq).1
  have hA : 4 * R.pi * rh ^ 2 ≠ 0 := by
    have := R.pi_pos; have := hrh.1; positivity
  have hc : η x₀ l₀ = R.kB * (Fintype.card H.Loop * R.ln2) / (4 * R.pi * rh ^ 2) := by
    have h : η x₀ l₀ * (4 * R.pi * rh ^ 2) = R.kB * Bridge.horizonEntropy H P := hhor
    rw [hS] at h
    rw [eq_div_iff hA, h, R.ln2_def]
  have hη : η x₀ l₀ = R.η * (1 - 2 / R.L + 4 / R.L ^ 2) := by
    rw [hc, hr, (Bridge.counts_exact H R hL hRL).1]
    unfold Reg.η Reg.Shor Reg.Ahor
    ring
  have hne : R.η * (1 - 2 / R.L + 4 / R.L ^ 2) ≠ 0 :=
    (mul_pos (Solution.eta_pos R) R.count_factor_pos).ne'
  exact Solution.jacobson_G_from_sources R G η hsym hdir h₀ _ hne hη M hcl p A ρ hweak
    hdust.1 hdust.2 hN

/-- **`G` at leading order** (Sec. III.C): the `G` of the count's exact density
(`Derived.jacobson_G_exact`) times `1 − 2/L + 4/L²` is the leading-order `G` of `Derived.jacobson_G`,
and it exceeds that `G` by at most `8/3L` of it, about one part in `10⁶¹`: so much the step
`Approx.count_density` changes `G`.  Sources: `G` from the exact density (`Derived`); Postulate 2's
fourth clause, which gives the count's `4 ≤ L` (`Horizon.four_le`); and the condition `R.L = L`. -/
theorem G_leading_order (H : Horizon L) (R : Reg) (G : ℝ) (hRL : Condition.same_L R L)
    (hJ : Derived.jacobson_G_exact R G) :
    G * (1 - 2 / R.L + 4 / R.L ^ 2) = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) ∧
    0 ≤ G - R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) ∧
    G - R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)
      ≤ 8 / (3 * R.L) * (R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) := by
  have h4 : (4 : ℝ) ≤ R.L := by
    have hL' : 4 ≤ L := H.four_le
    have hRL' : R.L = L := hRL
    rw [hRL']; exact_mod_cast hL'
  exact R.G_exact_bound G h4 hJ

/-- **The chain** (Secs. II–IV.D): `Λ = 3/R_Λ²`, `G = c³ℓ_c²/(πℏ ln 2)`, `GΛ = 12πc³/(ℏL² ln 2)`,
`k_BT = E_c/L`, and the horizon's heat is the vacuum's energy `E_Λ` to relative order `2/L`.
Sources: Postulate 2's clauses on laws (for the laws and for the entropy density); the thermal
state, free strings and the senses' probabilities (thermodynamics); the bits as outcomes
(Postulate 1); Postulate 1's first sentence applied to the geometry and to the space at an instant;
Sec. II's cell and Postulate 2's last sentence, with its first clause, for the rings through the
observer's cell drawn in space;
Jacobson's step at every point (`Derived`,
`jacobson_step`); the first law for every observer and the horizon of the solution without a mass
thermal at the temperature of its period, for its surface gravity (thermodynamics); the Killing–Hopf
theorem, Einstein's
constraint, the contracted Bianchi identity and the static weak field (Riemannian and Lorentzian
geometry); the count's density at leading order in `1/L` (`Approx`); Postulate 2's fourth clause
in the paper's words, which gives `4 ≤ L` (`Horizon.four_le`); and the conditions: `R.L = L`, the
crossing `(x₀, l₀)` is one (`h₀`), the radius of the horizon of the solution without a mass, no
matter without a mass, `Λ` the vacuum's constant, matter at rest in the weak field, Newton's law
defining `G`. -/
theorem chain {H : Horizon L} {Slot V Gm Sp : Type*} (R : Reg) {Λ : ℝ} (P : H.Positions)
    (f : H.Cell → H.Loop → V) (hsym : P2.homogeneous H f) (hdir : P2.directions H f)
    [NeZero L] (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (ρ : H.Loop → Qubit.Op)
    (hthermal : Thermo.thermal_state H T β En ρ) (Pst : (H.Loop → Bool) → ℝ)
    (q : H.Loop → ℝ) (hfree : Thermo.free_strings H Pst q)
    (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ) (halike : P1.bits_alike H read)
    (geom : Slot → Gm) (hgeom : P1.geometry_qubits H f ρ read Pst geom)
    (Closes : Slot → Prop) (hclose : P1.slice_qubits H Closes)
    (sp : Sp) (embedSp : (K : ℝ) → Space.SpaceForm K → Sp)
    (hKH : Geometry.space_form geom Closes sp embedSp)
    (η : H.Cell → H.Loop → ℝ) (hsymη : P2.homogeneous H η) (hdirη : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀) (rh : ℝ)
    (hcount : Approx.count_density H R η l₀ x₀ rh)
    (M : Einstein.Spacetime) (hcl : Derived.clausius H R η M)
    (hfirst : Thermo.first_law_local M) (hbianchi : Geometry.bianchi M) (hnm : Condition.no_matter M)
    (hΛ : Condition.vacuum_constant M Λ) (hcon : Geometry.constraint M Λ sp embedSp)
    (hslice : P1.slice_form_qubits H R sp embedSp)
    (hdrawn : P2.rings_drawn H P R sp embedSp x₀)
    (G : ℝ) (Mw : Einstein.Spacetime) (hclw : Derived.clausius H R η Mw) (pw : Mw.Pt) (A ρw : ℝ)
    (hweak : Geometry.weak_field Mw pw A) (hdust : Condition.dust R Mw pw ρw)
    (hN : Condition.newton_G R G A ρw) (hrh : Condition.horizon_radius R G Λ rh)
    (Temp : ℝ) (I1 : Thermo.horizon_thermal R (-R.gSdS G 0 Λ rh) Temp)
    (hRL : Condition.same_L R L) (hq : Thermo.sense_from_state H T β En q) :
    Λ = 3 / R.RL ^ 2 ∧ G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ * R.ln2) ∧
    G * Λ = 12 * R.pi * R.c ^ 3 / (R.ℏ * R.L ^ 2 * R.ln2) ∧
    R.kB * Temp = R.Ec / R.L ∧
    R.kB * Temp * Bridge.horizonEntropy H Pst = R.EΛ * (1 - 2 / R.L + 4 / R.L ^ 2) :=
  Solution.chain_from_sources R P f hsym hdir T β En ρ hthermal Pst q hfree read halike geom
    hgeom Closes hclose sp embedSp hKH η hsymη hdirη h₀ rh hcount M hcl hfirst hbianchi hnm hΛ hcon
    hslice hdrawn G Mw hclw pw A ρw hweak hdust.1 hdust.2 hN hrh Temp I1 H.four_le hRL hq

/-- **The horizon of the solution without a mass is at `R_Λ`** (Sec. IV.D): from `Λ = 3/R_Λ²`
(`Solution.cosmological_constant_from_sources`), the de Sitter solution's `f` vanishes at `R_Λ`.
Sources: those of `chain` for `Λ`, among them the free strings (Postulate 1 with thermodynamics),
which make the state at every crossing the same, no string correlated with another
(`Solution.state_same`); the value of the entropy density does not enter, since there is no
matter, only that it is positive (a condition), as Jacobson's step needs.  The rings through the
observer's cell, drawn (`hdrawn`), close with `Lℓ_c` and every great circle with `R.L ℓ_c`
(`hslice`), so the two together give `L = R.L`, the condition `chain` takes as `hRL`. -/
theorem deSitter_horizon {H : Horizon L} {Slot V Gm Sp : Type*} (R : Reg)
    {Λ : ℝ} (P : H.Positions) (f : H.Cell → H.Loop → V) (hsym : P2.homogeneous H f)
    (hdir : P2.directions H f)
    [NeZero L] (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (ρ : H.Loop → Qubit.Op)
    (hthermal : Thermo.thermal_state H T β En ρ) (Pst : (H.Loop → Bool) → ℝ)
    (q : H.Loop → ℝ) (hfree : Thermo.free_strings H Pst q)
    (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ) (halike : P1.bits_alike H read)
    (geom : Slot → Gm) (hgeom : P1.geometry_qubits H f ρ read Pst geom)
    (Closes : Slot → Prop) (hclose : P1.slice_qubits H Closes)
    (sp : Sp) (embedSp : (K : ℝ) → Space.SpaceForm K → Sp)
    (hKH : Geometry.space_form geom Closes sp embedSp)
    (η : H.Cell → H.Loop → ℝ) (hsymη : P2.homogeneous H η) (hdirη : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀) (hη : Condition.pos (η x₀ l₀))
    (M : Einstein.Spacetime) (hcl : Derived.clausius H R η M)
    (hfirst : Thermo.first_law_local M) (hbianchi : Geometry.bianchi M) (hnm : Condition.no_matter M)
    (hΛ : Condition.vacuum_constant M Λ) (hcon : Geometry.constraint M Λ sp embedSp)
    (hslice : P1.slice_form_qubits H R sp embedSp)
    (hdrawn : P2.rings_drawn H P R sp embedSp x₀) (G : ℝ) :
    Derived.deSitter_horizon R G Λ :=
  (R.deSitter G Λ).2 (Solution.cosmological_constant_from_sources R P f hsym hdir T β En ρ
    hthermal Pst q hfree read halike geom hgeom Closes hclose sp embedSp hKH η hsymη hdirη h₀
    (show (0 : ℝ) < η x₀ l₀ from hη).ne' M hcl hfirst hbianchi hnm hΛ hcon hslice hdrawn)

/-- **The cell from Newton's constant** (Sec. III.C): `ℓ_c = √(π ln 2 · ℏG/c³) = √(π ln 2) ℓ_P`.
Source: `G` from Jacobson's step with the count (`Derived.jacobson_G`). -/
theorem cell_from_G (R : Reg) (G : ℝ) (hJ : Derived.jacobson_G R G) :
    R.ℓc = Real.sqrt (R.pi * R.ln2 * R.ℏ * G / R.c ^ 3) ∧
    R.ℓc = Real.sqrt (R.pi * R.ln2) * R.ℓP G :=
  R.cell_from_G G hJ

/-- **Bekenstein and Hawking's quarter is one bit per ring** (Sec. III.C).  The first part writes
`S_hor` with `R_Λ` by their definitions and takes no premise.  Source: `G` from Jacobson's step
with the count (`Derived.jacobson_G`). -/
theorem entropy_quarter (R : Reg) (G : ℝ) (hJ : Derived.jacobson_G R G) :
    R.Shor = R.pi ^ 2 * R.RL ^ 2 * R.ln2 / R.ℓc ^ 2 ∧
    R.Shor = R.pi * R.RL ^ 2 / R.ℓP G ^ 2 ∧
    R.Shor = R.Ahor / (4 * R.ℓP G ^ 2) ∧ R.ringShare = 4 * R.ℓP G ^ 2 * R.ln2 :=
  R.entropy_quarter G hJ

/-- **Newton's law and Padmanabhan's equipartition** (Secs. III.C and IV.B): about a mass at rest
its pull, the field it adds to the solution at the solution's constant `Λ` (`Reg.pull`), is
`GM/r²` at every `Λ`; and `Mc² = 2N_s(r) k_BT_a ln 2`, two Landauer energies per string of the
sphere, at the Unruh temperature of the pull.  The first part follows from the condition by the
definitions `gSdS` and `pull` and takes no premise.  Sources: `G` (`Derived`), the
Schwarzschild–de Sitter field (the derived solution, the definitions `gSdS` and `pull`), the
horizon thermal at the acceleration `a` (thermodynamics); and the condition: `a` is the pull. -/
theorem newton (R : Reg) (G M Λ r a T : ℝ) (hr : Condition.pos r) (ha0 : Condition.pos a)
    (hJ : Derived.jacobson_G R G) (ha : Condition.pull_of R G M Λ r a)
    (I1 : Thermo.horizon_thermal R a T) :
    a = G * M / r ^ 2 ∧ M * R.c ^ 2 = 2 * R.Ns r * (R.kB * T * R.ln2) ∧
    a / R.ac = (M / R.mc) / (R.pi * R.n r ^ 2 * R.ln2) :=
  R.newton G M Λ r a T hr ha0 hJ ha I1

/-- **The entropy a mass removes** (Sec. IV.C): `Lα`, `2πMcR_Λ/ℏ`.  The first part takes `G`, and
the fourth takes the thermal horizon with the constant.  The second, third and fifth parts are
arithmetic with the definitions of `α` and `R_Λ` and take no premise.  Sources: `G` and the
constant `Λ = 3/R_Λ²` (`Derived`); the horizon of the solution without a mass thermal at the
temperature of its period, for its surface gravity `−g(r_h)` (thermodynamics), which the constant
makes the lap (`Reg.thermal_lap`); and the condition: `r_h` the radius of that horizon. -/
theorem entropy_removed (R : Reg) (G M Λ rh T : ℝ) (hJ : Derived.jacobson_G R G)
    (hdS : Derived.deSitter_horizon R G Λ) (hrh : Condition.horizon_radius R G Λ rh)
    (I1 : Thermo.horizon_thermal R (-R.gSdS G 0 Λ rh) T) :
    2 * R.pi * (G * M / R.c ^ 2) / R.ℓc = 2 * R.α M / R.ln2 ∧
    (R.L / 2) * (2 * R.α M / R.ln2) * R.ln2 = R.L * R.α M ∧
    R.L ^ 2 / 4 * R.ln2 - (R.L - 2 * R.α M / R.ln2) ^ 2 / 4 * R.ln2
      = R.L * R.α M - R.α M ^ 2 / R.ln2 ∧
    R.L * R.α M = M * R.c ^ 2 / (R.kB * T) ∧
    R.L * R.α M = 2 * R.pi * M * R.c * R.RL / R.ℏ :=
  R.entropy_removed G M T hJ (R.thermal_lap G Λ rh T hdS hrh.1 hrh.2 I1)

/-- **The entropy a mass removes within a sphere** (Sec. III.C, after Eq. (newton)): about a body of
mass `M` at rest, in the solution with its constant `Λ = 3/R_Λ²`, let `ρ(s)` be the areal radius of
the sphere at geodesic distance `s` from the body's center, from its surface at `s = b` out to `r`,
and `D(s)` the sphere's shortfall in area against a sphere of the same area in the solution without
the mass, at the same `Λ`.  At a ring's share, one bit per ring, the shortfall removes between
`S_M(r − b)` and `S_M(r − b)/√f_min`, with `f_min` the smaller value of the metric function at the
two ends (`Reg.shortfall_removes`): to first order in `GM/c²ρ(b)` and `ρ(r)²/R_Λ²`, far outside the
body, it removes `S_M(r) = 2πnα = 2πMcr/ℏ`, the fraction `2GM/c²r` of the strings' entropy
`N_s(r) ln 2` (`Reg.removed_fraction`).  The paper reads this as the mass lowering the count of
Eq. (N) by that fraction, so that Eq. (newton) holds to first order; that reading is no part of
the statement.  At `r = R_Λ` the formula gives Eq. (SM), `Lα`.  The third, fourth and sixth parts
are arithmetic with the definitions of `S_M`, `α` and `R_Λ` and take no premise.  Sources: `G`
and the constant of the solution without a mass (`Derived`); and the conditions: `M > 0`, `ρ` the
areal radius along a radial geodesic, and `D` the shortfall.  The metric function of the solution
about the body enters the two conditions as the definition `Reg.fSdS`, which
`Main.schwarzschild_deSitter` derives, and that solution has the same constant
(`Main.lambda_with_mass`); neither is a hypothesis here. -/
theorem entropy_removed_sphere (R : Reg) (G M Λ b r : ℝ) (ρ D : ℝ → ℝ)
    (hM : Condition.pos M) (hJ : Derived.jacobson_G R G) (hdS : Derived.deSitter_horizon R G Λ)
    (hρ : Condition.areal_radius R G M Λ ρ b r) (hD : Condition.shortfall R G Λ ρ D b r) :
    R.SM M (r - b) ≤ (D r - D b) / R.ringShare * R.ln2 ∧
    (D r - D b) / R.ringShare * R.ln2
      ≤ R.SM M (r - b) / Real.sqrt (min (R.fSdS G M Λ (ρ b)) (R.fSdS G M Λ (ρ r))) ∧
    R.SM M (r - b) = R.SM M r - R.SM M b ∧
    R.SM M r = 2 * R.pi * R.n r * R.α M ∧
    R.SM M r = 2 * G * M / (R.c ^ 2 * r) * (R.Ns r * R.ln2) ∧
    R.SM M R.RL = R.L * R.α M := by
  obtain ⟨hbr, hρb, hgeo⟩ := hρ
  have hΛ : 0 ≤ Λ := by
    rw [(R.deSitter G Λ).1 hdS]; have := R.RL_pos; positivity
  -- the radius grows outward: `dρ/ds = √f ≥ 0`
  have hmono : MonotoneOn ρ (Set.Icc b r) := by
    have hcont : ContinuousOn ρ (Set.Icc b r) := fun s hs =>
      (hgeo s hs).2.continuousAt.continuousWithinAt
    refine monotoneOn_of_deriv_nonneg (convex_Icc b r) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun s hs =>
        (hgeo s (Set.Ioo_subset_Icc_self hs)).2.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hgeo s (Set.Ioo_subset_Icc_self hs)).2.deriv]
      exact Real.sqrt_nonneg _
  have hb : b ∈ Set.Icc b r := ⟨le_rfl, hbr.le⟩
  have hr : r ∈ Set.Icc b r := ⟨hbr.le, le_rfl⟩
  have hρ' : ∀ s ∈ Set.Icc b r, ρ b ≤ ρ s ∧ ρ s ≤ ρ r := fun s hs =>
    ⟨hmono hb hs hs.1, hmono hs hr hs.2⟩
  -- the sphere's area `4πρ²` grows at the rate `8πρ√f`, `areaRate`
  have harea : ∀ s ∈ Set.Icc b r,
      deriv (fun t => 4 * R.pi * ρ t ^ 2) s = R.areaRate G M Λ (ρ s) := by
    intro s hs
    have h2 := (hgeo s hs).2.mul (hgeo s hs).2
    have h : HasDerivAt (fun t => 4 * R.pi * ρ t ^ 2)
        (4 * R.pi * (Real.sqrt (R.fSdS G M Λ (ρ s)) * ρ s + ρ s * Real.sqrt (R.fSdS G M Λ (ρ s))))
        s := by
      convert h2.const_mul (4 * R.pi) using 1
      funext t; simp only [Pi.mul_apply]; ring
    rw [h.deriv]
    unfold Reg.areaRate
    ring
  have hD' : ∀ s ∈ Set.Icc b r,
      HasDerivAt D (R.areaRate G 0 Λ (ρ s) - R.areaRate G M Λ (ρ s)) s := by
    intro s hs
    rw [← harea s hs]; exact hD s hs
  obtain ⟨h1, h2, h3⟩ := R.shortfall_removes G M Λ b r ρ D hbr hJ (le_of_lt hM) hΛ hρb hρ'
    (hgeo b hb).1 (hgeo r hr).1 hD'
  exact ⟨h1, h2, h3, R.SM_in_cells M r, R.removed_fraction G M r hJ,
    (R.removed_rings G M r hJ).2.2⟩

/-- **The step to `S_M(r) = 2πnα`, bounded** (Sec. III.C): the entropy the mass removes between the
body's surface `b` and `r`, `(D(r) − D(b))` at one bit per ring's share, exceeds `S_M(r − b)` by
at most the fraction `1/√f_min − 1` of it, with `f_min` the smaller value of the metric function
at the two ends, which is first order in `GM/c²ρ(b)` and in `ρ(r)²/R_Λ²`: the error of the paper's
first-order statement, as `G_leading_order` bounds that of `Approx.count_density`.  Sources: as
`entropy_removed_sphere`. -/
theorem entropy_removed_leading_order (R : Reg) (G M Λ b r : ℝ) (ρ D : ℝ → ℝ)
    (hM : Condition.pos M) (hJ : Derived.jacobson_G R G) (hdS : Derived.deSitter_horizon R G Λ)
    (hρ : Condition.areal_radius R G M Λ ρ b r) (hD : Condition.shortfall R G Λ ρ D b r) :
    0 ≤ (D r - D b) / R.ringShare * R.ln2 - R.SM M (r - b) ∧
    (D r - D b) / R.ringShare * R.ln2 - R.SM M (r - b)
      ≤ R.SM M (r - b) * (1 / Real.sqrt (min (R.fSdS G M Λ (ρ b)) (R.fSdS G M Λ (ρ r))) - 1) := by
  obtain ⟨h1, h2, -⟩ := entropy_removed_sphere R G M Λ b r ρ D hM hJ hdS hρ hD
  refine ⟨by linarith, ?_⟩
  have : R.SM M (r - b) * (1 / Real.sqrt (min (R.fSdS G M Λ (ρ b)) (R.fSdS G M Λ (ρ r))) - 1)
      = R.SM M (r - b) / Real.sqrt (min (R.fSdS G M Λ (ρ b)) (R.fSdS G M Λ (ρ r)))
        - R.SM M (r - b) := by ring
  rw [this]; linarith

/-- **`GΛ` and `Λ`** (Sec. IV.D): `GΛ = 12πc³/(ℏL² ln 2)` and `Λ = 12π²/(L²ℓ_c²)`.  Sources: `G`
and the horizon at `R_Λ` (`Derived`). -/
theorem G_Lambda (R : Reg) (G Λ : ℝ) (hJ : Derived.jacobson_G R G)
    (hdS : Derived.deSitter_horizon R G Λ) :
    G * Λ = 12 * R.pi * R.c ^ 3 / (R.ℏ * R.L ^ 2 * R.ln2) ∧
    Λ = 12 * R.pi ^ 2 / (R.L ^ 2 * R.ℓc ^ 2) :=
  R.G_Lambda G Λ hJ hdS

/-- **The vacuum's energy density** (Sec. IV.D): `ρ_Λ = 3π²ρ_c ln 2/(2L²) = Λc⁴/(8πG)`.  The first
part writes `ρ_Λ` in the cell's units by its definition and takes no premise.  Sources: `G` from
Jacobson's step with the count, and the horizon at `R_Λ` (`Derived`). -/
theorem vacuum_density (R : Reg) (G Λ : ℝ) (hJ : Derived.jacobson_G R G)
    (hdS : Derived.deSitter_horizon R G Λ) :
    R.ρΛ = 3 * R.pi ^ 2 * R.ρc * R.ln2 / (2 * R.L ^ 2) ∧
    R.ρΛ = Λ * R.c ^ 4 / (8 * R.pi * G) :=
  R.ρΛ_eq G Λ hJ hdS

/-- **The Misner–Sharp and Komar energies of the horizon** (Sec. IV.D): `E_MS = E_Λ`,
`E_K = −2E_Λ`.  Sources: `G` and the horizon at `R_Λ` (`Derived`); the two energies are the
geometry's definitions (`Reg.EMS`, `Reg.EK`). -/
theorem komar_misner_sharp (R : Reg) (G Λ : ℝ) (hJ : Derived.jacobson_G R G)
    (hdS : Derived.deSitter_horizon R G Λ) :
    R.EMS G Λ R.RL = R.EΛ ∧ R.EK G Λ R.RL = -2 * R.EΛ :=
  R.komar_misner_sharp G Λ hJ hdS

/-- **A black hole's horizon holds `L'²/4` bits, the quarter** (Sec. IV.D).  The second part is
arithmetic, the horizon's area `4π(2GM/c²)²` over `4ℓ_P²`, and takes no premise.  Source: `G` from
Jacobson's step with the count (`Derived.jacobson_G`). -/
theorem black_hole_quarter (R : Reg) (G M : ℝ) (hJ : Derived.jacobson_G R G) :
    (4 * R.pi * G * M / (R.c ^ 2 * R.ℓc)) ^ 2 / 4 * R.ln2
      = R.pi * (2 * G * M / R.c ^ 2) ^ 2 / R.ℓP G ^ 2 ∧
    R.pi * (2 * G * M / R.c ^ 2) ^ 2 / R.ℓP G ^ 2
      = 4 * R.pi * (2 * G * M / R.c ^ 2) ^ 2 / (4 * R.ℓP G ^ 2) :=
  R.black_hole_quarter G M hJ

/-- **The strings' mean energy is one thermal energy of the horizon, and the mean decrease of the
global phase per tick is `1/L`** (Sec. IV.E).  A string's energy is the same for all its states and
differs from string to string with the mass the string holds.  The strings' energies are spread at
the horizon's temperature and do not change (`hGibbs`), so their mean is the mean of the Gibbs
distribution at that temperature, the thermal energy `k_BT_dS` (`Law.gibbsMean_eq`,
`Carriers.string_energy`), with `I1` for the horizon of the solution without a mass, whose surface
gravity `−g(r_h)` the constant makes `a_Λ` and whose period is then the lap (`Reg.thermal_lap`): `ℏ`
over the lap time, so on average a string's global phase decreases by one radian in a lap.  By Sec.
II's definition of energy the free tick of a string of energy `E` is the factor `e^{−iEt_c/ℏ}` on
every state (`hEs`), so the strings' ticks are factors `e^{−iφ}`, each a decrease of the global
phase by `φ`, and the `φ` have the mean `1/L`; a string's factor is one for all its states, so its
energy adds no state.  The heat of a string, the horizon's temperature times its one bit, is `ln 2`
of the mean energy and equals the vacuum's energy per string of the horizon (`Reg.string_split`,
`Reg.vacuum_per_string`); the rest, `1 − ln 2`, is matter.  Sources: the strings' energies spread at
the horizon's temperature, and the horizon of the solution without a mass thermal at the temperature
of its period (thermodynamics); the strings' energies by Sec. II's definition of energy (Postulate 1
with Sec. II's definitions); the constant `Λ = 3/R_Λ²` (`Derived`); and the conditions: `r_h` the
radius of that horizon. -/
theorem string_energy (H : Horizon L) (R : Reg) (G Λ rh T : ℝ)
    (hdS : Derived.deSitter_horizon R G Λ)
    (hrh : Condition.horizon_radius R G Λ rh) (I1 : Thermo.horizon_thermal R (-R.gSdS G 0 Λ rh) T)
    (τ : H.Loop → Qubit.Tick L) (Es : H.Loop → ℝ)
    (hGibbs : Thermo.energies_thermal R T ((∑ l, Es l) / Fintype.card H.Loop))
    (hEs : P1.string_energies H R τ Es) :
    (∑ l, Es l) / Fintype.card H.Loop = R.kB * T ∧
    (∑ l, Es l) / Fintype.card H.Loop = R.ℏ / (R.L * R.tc) ∧
    (∃ φ : H.Loop → ℝ,
      (∀ l, (τ l).U = Complex.exp (-((φ l : ℝ) : ℂ) * Complex.I) • (1 : Qubit.Op)) ∧
      (∑ l, φ l) / Fintype.card H.Loop = 1 / R.L) ∧
    R.ln2 * (R.kB * T) = R.EΛ / R.Rhor ∧ 0 < (1 - R.ln2) * (R.kB * T) := by
  have I1' := R.thermal_lap G Λ rh T hdS hrh.1 hrh.2 I1
  have hE : (∑ l, Es l) / Fintype.card H.Loop = R.kB * T := R.string_energy _ T hGibbs I1'
  refine ⟨hE, hE.trans I1', ⟨fun l => Es l * R.tc / R.ℏ, fun l => hEs l, ?_⟩,
    (R.string_split T (R.kB * T) I1' rfl).1, (R.string_split T (R.kB * T) I1' rfl).2.2⟩
  -- the mean decrease of the global phase per tick is the mean energy times `t_c/ℏ`: `1/L`
  reg_facts R
  have htc : R.tc ≠ 0 := by unfold Reg.tc; positivity
  have hsum : ∑ l, Es l * R.tc / R.ℏ = (∑ l, Es l) * R.tc / R.ℏ := by
    rw [Finset.sum_mul, Finset.sum_div]
  have hmean : (∑ l, Es l) * R.tc / R.ℏ / Fintype.card H.Loop
      = (∑ l, Es l) / Fintype.card H.Loop * (R.tc / R.ℏ) := by ring
  show (∑ l, Es l * R.tc / R.ℏ) / Fintype.card H.Loop = 1 / R.L
  rw [hsum, hmean, hE, I1']
  field_simp

/-- **The vacuum's share is `ln 2`** (Sec. IV.E).  The energy inside the horizon is the strings' and
nothing else's (Postulate 1's first sentence, `hin`), the strings holding `k_BT_dS` on average, the
mean of the Gibbs distribution at the horizon's temperature (`hGibbs`; `string_energy`), and the
vacuum's energy, the Misner–Sharp energy of the horizon of the solution without a mass, is
`k_BT_dS ln 2` for each of the same strings (`Reg.EMS_per_ring`, with `G` from the count's exact
density, so that no step is at leading order).  So the vacuum's share of the energy inside the
horizon is `Ω_Λ = ln 2`, which Planck's `Ω_Λ` tests (`Numerics.vacuum_share`).  Sources: Postulate
1's first sentence applied to the energy inside the horizon; the strings' energies spread at the
horizon's temperature, and the horizon thermal at the temperature of its period (thermodynamics);
`G` from the exact density and the horizon at `R_Λ` (`Derived`); Postulate 2's fourth clause,
which gives the count's `4 ≤ L` (`Horizon.four_le`); and the conditions: `R.L = L`, `r_h` the
radius of that horizon. -/
theorem vacuum_share (H : Horizon L) (R : Reg)
    (hRL : Condition.same_L R L) (G Λ rh T Ein : ℝ)
    (hJ : Derived.jacobson_G_exact R G) (hdS : Derived.deSitter_horizon R G Λ)
    (hrh : Condition.horizon_radius R G Λ rh) (I1 : Thermo.horizon_thermal R (-R.gSdS G 0 Λ rh) T)
    (Es : H.Loop → ℝ)
    (hGibbs : Thermo.energies_thermal R T ((∑ l, Es l) / Fintype.card H.Loop))
    (hin : P1.energy_inside_strings H Ein Es) :
    R.EMS G Λ R.RL / Ein = R.ln2 := by
  have hL : 4 ≤ L := H.four_le
  have I1' := R.thermal_lap G Λ rh T hdS hrh.1 hrh.2 I1
  have hE := R.string_energy _ T hGibbs I1'
  exact R.vacuum_share H hL hRL G Λ T Ein hJ hdS I1' Es hE hin

/-- **The count's horizon is a quarter lap out** (Secs. IV.C and IV.D).  The count's horizon, `x`
cells out along a ring through the body, is the solution's, at the proper distance of its horizon
(`P2.ring_distance`); the solution puts it a quarter lap out, `πR_Λ/2 = Lℓ_c/4`
(`Reg.proper_distance`), so `x = L/4`, and a cell's weight inside that horizon, `1` inside, `1/2` on
it, `0` beyond, is the count's (`Bridge.horizonWeight_quarter`), with which every largest ring has
half its cells inside the horizon (`rings_cross_horizon`, `Horizon.Positions.horizon_weight_ring`).
Sources: the constant of the solution without a mass (`Derived`); Postulate 2's last sentence (a
ring's cells, segments of length `ℓ_c` of its geodesic, measure proper distance along it); and the
conditions: `R.L = L`, the radius of the horizon, the proper distance along a radial line. -/
theorem horizon_quarter (R : Reg) (hRL : Condition.same_L R L) (G Λ rh x : ℝ) (σ : ℝ → ℝ)
    (hdS : Derived.deSitter_horizon R G Λ) (hrh : Condition.horizon_radius R G Λ rh)
    (hσ : Condition.radial_distance R G Λ rh σ) (hx : P2.ring_distance R σ rh x) :
    x = R.L / 4 ∧ ∀ d : ℕ, Bridge.horizonWeight x d = Horizon.Positions.weight (L := L) d := by
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  obtain ⟨hσ0, hσc, hσd⟩ := hσ
  have hx' : x * R.ℓc = σ rh := hx
  rw [hr] at hσc hσd hx'
  have hq := (R.proper_distance G Λ hdS σ hσ0 hσc hσd).2
  have hxL : x = R.L / 4 := by
    have h4 : x * R.ℓc = R.L / 4 * R.ℓc := by rw [hx', hq]; ring
    exact mul_right_cancel₀ R.ℓc_pos.ne' h4
  refine ⟨hxL, fun d => ?_⟩
  have hRL' : R.L = L := hRL
  rw [hxL, hRL']
  exact Bridge.horizonWeight_quarter d

/-- **The temperature floor** (Sec. IV.C): no observer in de Sitter space sees a temperature below
the horizon's, `E_c/L`.  Sources: the Deser–Levin temperature, with the surface gravity of the
horizon of the solution without a mass (thermodynamics on the derived solution); the constant
`Λ = 3/R_Λ²` (`Derived`), which makes that surface gravity `a_Λ` (`Reg.surface_gravity_eq`); and
the condition: `r_h` the radius of that horizon. -/
theorem temperature_floor (R : Reg) (G Λ rh a T' : ℝ) (hdS : Derived.deSitter_horizon R G Λ)
    (hrh : Condition.horizon_radius R G Λ rh) (hDL : Thermo.deser_levin R G Λ rh a T') :
    R.Ec / R.L ≤ R.kB * T' := by
  have h : R.kB * T' = R.ℏ / (2 * R.pi * R.c) * Real.sqrt (a ^ 2 + (-R.gSdS G 0 Λ rh) ^ 2) := hDL
  rw [R.surface_gravity_eq G Λ rh hdS hrh.1 hrh.2] at h
  exact R.temperature_floor a T' h

/-- **The equation of state** (Sec. VI): `w = −1` exactly, at every time.  Sources: the first law
for the cosmic fluid (thermodynamics), `L` and the cell constant (Postulate 1), and `c`, `ℏ`, `k_B`
the defining constants of the SI (the units), with the universe expanding (conditions). -/
theorem equation_of_state (Rt : ℝ → Reg) (hL : P1.constant_L Rt) (hℓc : P1.constant_cell Rt)
    (hconst : Units.si_constants Rt) (a : ℝ → ℝ) (adot w t : ℝ)
    (hH : Condition.expanding a adot t) (hA : Condition.scale_factor_rate a adot t)
    (first_law : Thermo.first_law Rt a w t) :
    w = -1 :=
  Reg.w_exact_in_time Rt hL hℓc hconst a adot w t hH hA first_law

/-- **The qubit ceiling** (Sec. IV.A): a random state of `N` qubits needs `2^N ≤ L`.  The string of
the last qubit lies on a ring of at most `L` cells (Postulate 1, `hL`), and each cell is paired
with a joint outcome of the other qubits (`e`).  In a random state every joint outcome occurs,
with either value of the last qubit's bit (`hrandom`).  A joint outcome that occurs is the outcome
at a position (Postulate 1, `hout`), so the block of each of the `2^{N−1}` joint outcomes of the
other qubits has a cell that reads `1` and a cell that reads `−1`.  Two cells for each block give
`2^N ≤ L` (`Capacity.frac_pos_lt_one`, `Capacity.ceiling_by_outcome`).  The bound holds for every
state in which all `2^N` joint outcomes occur.  Sources: three sentences of Postulate 1, "No ring
has more than `L` cells" (`hL`), and "The bits are the possible outcomes of one measurement of
the qubit" with "Any two qubits can be measured jointly", which Sec. IV.A reads together
(`hout`); the conditions: `1 ≤ N` and the random state. -/
theorem ceiling {Cell : Type*} [Fintype Cell] (N L : ℕ) (hN : Condition.one_le N)
    (hL : P1.ring_cells Cell L) (e : Cell → Fin (2 ^ (N - 1))) (b : Cell → Bool)
    (pr : Fin (2 ^ (N - 1)) → Bool → ℝ) (hout : P1.outcomes_at_positions pr e b)
    (hrandom : Condition.random_state pr) : 2 ^ N ≤ L :=
  (Capacity.ceiling_by_outcome N (Fintype.card Cell) hN rfl e b fun k => by
    obtain ⟨x, hx, hbx⟩ := hout k true (hrandom k true)
    obtain ⟨y, hy, hby⟩ := hout k false (hrandom k false)
    exact Capacity.frac_pos_lt_one b _ (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩) hbx
      (Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩) hby).trans hL

/-- **Einstein's equations** (Sec. III, Eq. (einstein)): with `κ = 2πk_B/(ℏcη)` for the entropy
density `η` of every local horizon, there is one constant `Λ` with `R_ab − ½R g_ab + Λ g_ab = κT_ab`
at every point, with matter and without.  The density is one law, the same on every local horizon
(Postulate 2), whatever its value, provided it is positive; the count gives the value, and with it
`G` (`jacobson_G`, `jacobson_G_exact`).  Sources: Postulate 2's two clauses on laws, for the entropy
density; Jacobson's step at every point (`Derived`, `jacobson_step`); the first law for every
observer (thermodynamics); the contracted Bianchi identity (Lorentzian geometry); and the
conditions: a cell on a ring, where the density is read, and the density positive. -/
theorem einstein {H : Horizon L} (R : Reg) (η : H.Cell → H.Loop → ℝ)
    (hsym : P2.homogeneous H η) (hdir : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀) (hη : Condition.pos (η x₀ l₀))
    (M : Einstein.Spacetime) (hcl : Derived.clausius H R η M) (hfirst : Thermo.first_law_local M)
    (hbianchi : Geometry.bianchi M) :
    ∃ Λ, Einstein.FieldEquations M (2 * R.pi * R.kB / (R.ℏ * R.c * η x₀ l₀)) Λ :=
  Einstein.einstein_equations M _ (hcl _ (show (0 : ℝ) < η x₀ l₀ from hη).ne'
    (Symmetry.one_density η hsym hdir h₀ (η x₀ l₀) rfl)) hfirst (hbianchi _)

/-- **Matter moves on geodesics** (Sec. III): where matter moves as dust, its acceleration is zero.
Sources: the first law for every observer (thermodynamics); the Leibniz rule for the flow
(Lorentzian geometry); and the condition: matter moving as dust. -/
theorem matter_geodesic (M : Einstein.Spacetime) (p : M.Pt) (u A : Fin 4 → ℝ) (ρ : ℝ)
    (hdust : Condition.dust_flow M p u ρ) (hfirst : Thermo.first_law_local M)
    (hleib : Geometry.leibniz M p u A) : A = 0 := by
  obtain ⟨hu, hρ, hT⟩ := hdust
  obtain ⟨D, hD⟩ := hleib.1 ρ hT
  exact Einstein.flow_geodesic hu hρ hD hleib.2 (Einstein.eq_zero_of_timelike _ (hfirst p))

/-- **Light moves on null geodesics** (Sec. III): where light passes, the direction `k` of its ray
is null (restated from the premise), and its change along the ray is a multiple of `k` itself, so
the rays are null geodesics.
Its stress tensor is `ρ k_a k_b` (`Einstein.null_dust_of_current`, from the energy current along
the ray for every observer), and the first law makes the rays geodesics (`Einstein.null_geodesic`).
Sources: light crossing a cell in one tick in every direction, with its energy moving with it
(Postulate 1, with Postulate 2's last sentence; `P1.light`); the first law for every observer
(thermodynamics); the Leibniz rule for the flow (Lorentzian geometry). -/
theorem light_rays (M : Einstein.Spacetime) (p : M.Pt) (k A : Fin 4 → ℝ)
    (hlight : P1.light M p k) (hfirst : Thermo.first_law_local M) (hleib : Geometry.leibniz M p k A) :
    Einstein.IsNull k ∧ ∃ l : ℝ, A = l • Matrix.mulVec Einstein.eta k := by
  obtain ⟨hnull, hk, hT0, hcur⟩ := hlight
  refine ⟨hnull, ?_⟩
  obtain ⟨ρ, hρ⟩ := Einstein.null_dust_of_current (Einstein.symmPart_isSymm _)
    (Einstein.eta_mulVec_ne_zero hk) fun u hu => (hcur u hu).imp fun _ hs => hs
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hT0 (by rw [hρ, zero_smul])
  obtain ⟨D, hD⟩ := hleib.1 ρ hρ
  exact ⟨_, Einstein.null_geodesic hρ0 hD (Einstein.eq_zero_of_timelike _ (hfirst p))⟩

/-- **The rotation curve: `v² = gr` on circular orbits** (Sec. IV.C): the bodies on the circular
orbits about a galaxy move as dust, so on geodesics (`Einstein.flow_geodesic`); in a static weak
field `g r` toward the center, a body on a geodesic has the acceleration of the field; and on a
circle of radius `r` at the speed `v` that acceleration is `v²/r` (`Motion.circular_speed`).
Sec. IV.C applies it with the field of Eq. (law), and in the deep regime with `g = √(a₀g_N)`
(`tully_fisher`).  Sources: the first law for every observer (thermodynamics); the Leibniz rule for
the flow and the Newtonian limit of geodesic motion (Lorentzian geometry); and the conditions: the
bodies move as dust on circular orbits. -/
theorem rotation_curve (M : Einstein.Spacetime) (wl : ℝ → ℝ → M.Pt)
    (u A : ℝ → ℝ → Fin 4 → ℝ) (ρ : ℝ → ℝ → ℝ) (hdust : Condition.dust_orbits M wl u ρ)
    (hfirst : Thermo.first_law_local M) (hleib : Geometry.leibniz_orbits M wl u A)
    (g : ℝ → ℝ) (x : ℝ → ℝ → ℝ × ℝ) (v : ℝ → ℝ) (horbit : Condition.circular_orbits x v)
    (hmotion : Geometry.newtonian_motion A x g) :
    Derived.circular_speeds g v := by
  intro r hr
  have hA : ∀ t, A r t = 0 := fun t => by
    obtain ⟨hu, hρ, hT⟩ := hdust r t
    obtain ⟨D, hD⟩ := (hleib r t).1 (ρ r t) hT
    exact Einstein.flow_geodesic hu hρ hD (hleib r t).2
      (Einstein.eq_zero_of_timelike _ (hfirst (wl r t)))
  have hacc := hmotion r hr hA
  rw [horbit r] at hacc
  exact Motion.circular_speed hr hacc

/-- **The solution about a body at rest is Schwarzschild–de Sitter** (Secs. III, IV.B and IV.D): between
the radii `a` and `b` about a spherical body at rest, alone, with Schwarzschild's time,
`e^{2α} = e^{−2β} = f(r) = 1 − 2GM/c²r − Λr²/3`, with `Λ` the constant of Einstein's equations and
`M` the mass that Newton's law reads off far from the body, where the potential `c²(f − 1)/2` is
`−GM/r`; the value of the entropy density does not enter, since there is no matter there, only
that it is positive.  Einstein's equations (`einstein`) without matter outside the body are the vacuum
equations, which for the static, spherically symmetric metric `Schwarzschild.static_vacuum`
solves.  Sources: those of `einstein`; the static, spherically symmetric solution about a body at
rest, with the curvature of its metric (Lorentzian geometry); and the conditions: the density
positive, no matter between `a > 0` and `b`, Schwarzschild's unit of time, `G > 0`. -/
theorem schwarzschild_deSitter {H : Horizon L} (R : Reg)
    (η : H.Cell → H.Loop → ℝ) (hsym : P2.homogeneous H η) (hdir : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀) (hη : Condition.pos (η x₀ l₀))
    (M : Einstein.Spacetime) (hcl : Derived.clausius H R η M) (hfirst : Thermo.first_law_local M)
    (hbianchi : Geometry.bianchi M) (pt : ℝ → M.Pt) (α β : ℝ → ℝ) (a b : ℝ) (ha : Condition.pos a)
    (hss : Geometry.static_spherical M pt α β a b) (hempty : Condition.empty_outside M pt a b)
    (htime : Condition.schwarzschild_time α β a b) (G : ℝ) (hG : Condition.pos G) :
    ∃ Λ Mb : ℝ, Derived.schwarzschild_deSitter R G Mb Λ α β a b := by
  obtain ⟨Λ, hE⟩ := Einstein.einstein_equations M _
    (hcl _ (show (0 : ℝ) < η x₀ l₀ from hη).ne' (Symmetry.one_density η hsym hdir h₀ (η x₀ l₀) rfl))
    hfirst (hbianchi _)
  have hV := Einstein.vacuum_of_field_equations M _ Λ hE {p | ∃ r ∈ Set.Ioo a b, p = pt r}
    (by rintro p ⟨r, hr, rfl⟩; exact hempty r hr)
  have hric : ∀ r ∈ Set.Ioo a b, Schwarzschild.ricSS α β r = Λ • Einstein.eta := fun r hr => by
    rw [← (hss r hr).2.2]; exact hV (pt r) ⟨r, hr, rfl⟩
  obtain ⟨m, c₀, hsol⟩ := Schwarzschild.static_vacuum ha (fun r hr => (hss r hr).1)
    (fun r hr => (hss r hr).2.1) hric
  obtain ⟨r₀, hr₀, h0⟩ := htime
  have hc₀ : c₀ = 0 := by rw [← (hsol r₀ hr₀).1, h0]
  have hc := R.c_pos
  have hG0 : (0 : ℝ) < G := hG
  refine ⟨Λ, R.c ^ 2 * m / G, fun r hr => ?_⟩
  have hr0 : 0 < r := (show (0 : ℝ) < a from ha).trans hr.1
  have hf : R.fSdS G (R.c ^ 2 * m / G) Λ r = 1 - 2 * m / r - Λ * r ^ 2 / 3 := by
    unfold Register.Reg.fSdS
    field_simp
  obtain ⟨hsum, hβ⟩ := hsol r hr
  refine ⟨?_, by rw [hf, hβ]⟩
  rw [Schwarzschild.time_part hsum, hc₀, hf, hβ]
  simp

/-- **A mass at rest leaves `Λ` unchanged** (Secs. IV.C–IV.D): along a family of solutions about a
body at rest, alone, whose mass grows from zero, each Schwarzschild–de Sitter with its own constant
`Λ s` (`schwarzschild_deSitter`), the Clausius relation on the observer's cosmological horizon keeps
`Λ` at the value of the solution without a mass, `3/R_Λ²` (`Reg.lambda_with_mass`); the field about
the body is then the pull of the mass less the push of the ring's content, `GM/r² − c²r/R_Λ²`.
The relation takes all the energy that crosses the horizon as heat: with `Λ` free the geometry
gives `d(Mc²) = −T dS + V dP` (`Reg.first_law_extended`), so it holds exactly when the work `V dP`
is zero, that is when `dΛ = 0` (`Reg.clausius_iff`).
The entropy density `η₀` of the horizons is free, so the result holds with the count's density at
leading order (`jacobson_G`) and exactly (`jacobson_G_exact`).  Sources: Jacobson's `G` for the
density `η₀` (`jacobson_G_density`) and the constant of the solution without a mass (`Derived`);
the cosmological horizon thermal at the temperature of its period, and the Clausius relation on it
with the same density (thermodynamics); and the conditions: the density positive, the family of
bodies at rest, and `s` one of them. -/
theorem lambda_with_mass (R : Reg) (G η₀ : ℝ) (M Λ r T : ℝ → ℝ) (s₁ : ℝ)
    (hη₀ : Condition.pos η₀) (hJ : Derived.jacobson_G_density R G η₀)
    (hdS : Derived.deSitter_horizon R G (Λ 0))
    (hfam : Condition.body_family R G M Λ r s₁)
    (I1 : Thermo.horizon_thermal_family R G M Λ r T s₁)
    (hcl : Thermo.horizon_clausius R η₀ M r T s₁) (s : ℝ) (hs : Condition.member s s₁) :
    Derived.deSitter_horizon R G (Λ s) ∧
      ∀ x, 0 < x → R.gSdS G (M s) (Λ s) x = G * M s / x ^ 2 - R.c ^ 2 * x / R.RL ^ 2 := by
  obtain ⟨-, hcont, hfam'⟩ := hfam
  exact R.lambda_with_mass_deSitter G η₀ M Λ r T s₁ hη₀ hJ hdS hcont
    (fun s hs => ⟨(hfam' s hs).1, (hfam' s hs).2.1, (hfam' s hs).2.2.1⟩)
    (fun s hs => (hfam' s hs).2.2.2) I1 hcl s hs

/-- **A mass draws the horizon in by `GM/c²`** (Sec. IV.C): about a body of mass `M` at rest, with
the constant `Λ = 3/R_Λ²` (`Derived.deSitter_horizon`, which `lambda_with_mass` derives for the
solution about the body), the cosmological horizon lies below `R_Λ − GM/c²` and within
`2(GM/c²)²/R_Λ` of it (`Reg.sds_outer_horizon`).  Sources: the constant (`Derived`); and the
conditions: `GM/c² > 0`, and the mass small, `13GM/c² < R_Λ`. -/
theorem horizon_drawn_in (R : Reg) (G M Λ : ℝ) (hΛ : Derived.deSitter_horizon R G Λ)
    (hε : Condition.pos (G * M / R.c ^ 2)) (h13 : Condition.small_mass R G M) :
    (∃ r ∈ Set.Ioo (R.RL - G * M / R.c ^ 2 - 2 * (G * M / R.c ^ 2) ^ 2 / R.RL)
        (R.RL - G * M / R.c ^ 2), R.fSdS G M Λ r = 0) ∧
      ∀ r, R.RL - G * M / R.c ^ 2 ≤ r → R.fSdS G M Λ r < 0 :=
  R.sds_outer_horizon G M Λ hΛ hε h13

/-- **A register with an `L` in Planck's band** (Sec. II): a register with Postulate 2's incidence
and the maps of its clause that no cell differs from another exists for `L = 2(52289¹³ + 1) = 4.36882 × 10⁶¹`, and
this `L` lies between the least and the greatest `L_cos` over the box of Planck's
`H₀ = 67.4 ± 0.5 km/s/Mpc` and `Ω_Λ = 0.685 ± 0.007` (`Numerics.Lof_box`,
`Numerics.witness_in_band`).  `52289` is prime, so `L/2 − 1 = 52289¹³` is a prime power, and
Singer's theorem gives the register (`Singer.homogeneous_register_of_prime_power`).  It is one
example among many: near `L_cos`, `L/2 − 1` is prime for about one even `L` in `141`, so about
`4 × 10⁵⁷` allowed values lie in the band, by Dusart's bounds on the number of primes, which the
files do not prove.  Sources: Postulate 2's clauses on incidence and its clause that no cell
differs from another, as the structures `Horizon` and `Horizon.Positions` carry them, with the maps
of `Horizon.Symmetry` in `Horizon.Homogeneous`: the result is that a register which meets them
exists.  The rest is mathematics, with the inputs of Appendix A (`c`, `ℏ`, `G`, and Planck's `H₀`
and `Ω_Λ` with their errors). -/
theorem register_in_band :
    (∃ H : Horizon (2 * (52289 ^ 13 + 1)), Nonempty H.Positions ∧ H.Homogeneous) ∧
    Numerics.LcosMin < ((2 * (52289 ^ 13 + 1) : ℕ) : ℝ) ∧
      ((2 * (52289 ^ 13 + 1) : ℕ) : ℝ) < Numerics.LcosMax := by
  have : Fact (Nat.Prime 52289) := ⟨Numerics.witness_in_band.1⟩
  obtain ⟨H, hP, hhom, -⟩ := Singer.homogeneous_register_of_prime_power 52289 13 (by norm_num)
  exact ⟨⟨H, hP, hhom⟩, Numerics.witness_in_band.2⟩

/-! ## The paper's statements restated from the sources

The statements below are made in the paper and were proved in the other files; here each is
stated with the definitions of `Sources.lean` as its only hypotheses, so that the premise ledger
covers it (the verification of 29 October: a result proved outside this file is outside the
ledger).  Each applies the theorem of the other file that proves it.  Where that theorem is
mathematics about the definitions of the files, the statement here takes the premise that makes it
a statement about the horizon, a string or the law.  The horizon's radius takes the derived
constant of the solution without a mass.  A string's room takes three sentences of Postulate 1:
no ring has more than `L` cells, and the bits as the possible outcomes with the joint
measurement, which Sec. IV.A reads together, so that a joint outcome that occurs is the outcome
at a position.  The limits of the law take the derived law. -/

/-! ### Sec. II: the register and its count -/

/-- **The clauses make the register finite** (Sec. II; the Data availability): the cells and the
rings are finite types, from the clauses with `4 ≤ L`.  The structure `Horizon` has finiteness
among its fields, so the statement as it stands here also follows from those fields.  The theorem
that the clauses force finiteness, for types not assumed finite, is `Horizon.finite_of_clauses`,
which the proof applies.  Sources: Postulate 2's clauses on incidence (the structure `Horizon`),
the fourth giving `4 ≤ L`. -/
theorem register_finite (H : Horizon L) : Finite H.Cell ∧ Finite H.Loop :=
  H.finite_cell_and_loop H.four_le

/-- **`L` is even** (Sec. II): an opposite lies halfway around a ring of `L` cells.  This is the
paper's argument, and it takes the positions along the rings (`P`).  The conclusion also follows
from the clauses on incidence alone, since twice the number of largest rings through a cell is `L`
(`Horizon.even_L`), so the statement holds without `P`.  Sources: Postulate 2's "the same cell
halfway around every largest ring through it" (`Positions`) and its fourth clause, for a ring
with a cell. -/
theorem register_even (H : Horizon L) (P : H.Positions) : Even L := by
  obtain ⟨l₁, -, -⟩ := H.two_loops
  have hL := H.four_le
  have hne : (H.cells l₁).Nonempty := by
    rw [← Finset.card_pos, H.card_cells]; omega
  obtain ⟨y, hy⟩ := hne
  exact P.even_of_halfway (by omega) l₁ y hy

open scoped Quaternion in
/-- **Two cells that are not opposite lie on exactly one largest ring** (Sec. II), Postulate 2's
second clause as the structure carries it; and **two points of the space at an instant that are not
antipodal lie on exactly one geodesic**, which Sec. II matches with it: on the three-sphere of
radius `ρ`, a closed spacelike geodesic of length `2πρ` through both exists, and any two have the
same path (Riemannian geometry, `TwoCells.geodesic_through_two`, in four dimensions).  The second
and third parts are that geometry, proved in the files, and take no premise.  Sources: the clause;
the conditions: the two cells, or the two points, neither equal nor opposite. -/
theorem ring_through_two_cells (H : Horizon L) (x y : H.Cell)
    (hxy : Condition.not_opposite H x y) {ρ : ℝ} {p q : ℍ} (hpq : Condition.two_points ρ p q) :
    (∃! l : H.Loop, x ∈ H.cells l ∧ y ∈ H.cells l) ∧
    (∃ γ : Geodesic.Curve ℝ ℍ, Geodesic.IsGeodesic (ρ ^ 2) γ ∧ Geodesic.IsSpacelike γ ∧
      Geodesic.InSpace γ ∧ Geodesic.HasLength γ (2 * Real.pi * ρ) ∧
      p ∈ Set.range (fun t => (γ.pos t).2) ∧ q ∈ Set.range (fun t => (γ.pos t).2)) ∧
    ∀ γ₁ γ₂ : Geodesic.Curve ℝ ℍ,
      Geodesic.IsGeodesic (ρ ^ 2) γ₁ → Geodesic.IsSpacelike γ₁ → Geodesic.InSpace γ₁ →
      p ∈ Set.range (fun t => (γ₁.pos t).2) → q ∈ Set.range (fun t => (γ₁.pos t).2) →
      Geodesic.IsGeodesic (ρ ^ 2) γ₂ → Geodesic.IsSpacelike γ₂ → Geodesic.InSpace γ₂ →
      p ∈ Set.range (fun t => (γ₂.pos t).2) → q ∈ Set.range (fun t => (γ₂.pos t).2) →
      Set.range (fun t => (γ₁.pos t).2) = Set.range (fun t => (γ₂.pos t).2) := by
  obtain ⟨hρ, hp, hq, hqp, hqp'⟩ := hpq
  obtain ⟨h1, h2⟩ := TwoCells.geodesic_through_two (E := ℍ) hρ hp hq hqp hqp'
  exact ⟨Bridge.ring_through_two_cells H x y hxy.1 hxy.2, h1, h2⟩

/-- **The register is a finite projective plane of order `L/2 − 1`, with `R` points and `R` lines**
(Sec. II), for `L ≥ 6`: with a cell and its opposite as a point and a largest ring as a line, the
incidence clauses are those of a projective plane (`Horizon.projectivePlane`), of order
`q = L/2 − 1`, with `q² + q + 1` lines and as many points.  Sources: Postulate 2's clauses in the
structure; the condition `L ≥ 6`. -/
theorem projective_plane (H : Horizon L) (h6 : Condition.six_le L) :
    2 * (H.order h6 + 1) = L ∧
    Fintype.card H.Loop = H.order h6 ^ 2 + H.order h6 + 1 ∧
    Fintype.card H.Pt = Fintype.card H.Loop :=
  ⟨H.two_mul_order_add_one h6, H.card_loop_eq_order h6⟩

/-- **Every ring crosses every observer's horizon, with half its cells inside** (Sec. II, Eq. (S);
the Data availability): with the horizon `L/4` cells from the observer's cell, every largest ring
crosses it, the weights of its cells sum to `L/2`, and the horizon's entropy, one bit per ring, is
`S_hor(1 − 2/L + 4/L²)` with the count's rings.  The first two parts take the structures alone,
and the third takes thermodynamics.  Sources: Postulate 2's clauses on incidence (the structure
`Horizon`), whose fourth gives `4 ≤ L`, and the positions along the rings (`Positions`); the
thermal state of free strings and the senses from it (thermodynamics); the condition `R.L = L`. -/
theorem rings_cross_horizon [NeZero L] (H : Horizon L) (Pos : H.Positions) (R : Reg)
    (hRL : Condition.same_L R L) (B : H.Cell)
    (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (P : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ)
    (hfree : Thermo.free_strings H P q) (hq : Thermo.sense_from_state H T β En q) :
    (∀ l, Pos.CrossesHorizon B l) ∧
    (∀ l : H.Loop, ∑ X ∈ H.cells l, Horizon.Positions.weight (L := L) (Pos.dist B X) = (L : ℝ) / 2) ∧
    Bridge.horizonEntropy H P = R.Shor * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  have hL := H.four_le
  obtain ⟨hc, he⟩ := Bridge.horizon_counts_every_ring H R Pos hL hRL B T β En P q hfree hq
  exact ⟨hc, (Bridge.horizon_entropy_count H R Pos hL hRL B).1, he⟩

/-- **The opposite of a cell lies `L/2` steps on along every largest ring through the cell**
(Postulate 2, first clause: "Every cell has one opposite, the same cell halfway around every
largest ring through it"): the register fact behind the drawing of the rings through the
observer's cell (`P2.rings_drawn`), where, with Sec. II's cell as a place, it excludes the antipodal
quotient of the three-sphere (`Space.sphere_rings`).  Sources: Postulate 2's clauses on incidence
(the structure `Horizon`) and the positions along the rings (`Positions`); and the condition: the
cell lies on the ring. -/
theorem opposite_halfway (H : Horizon L) (Pos : H.Positions) (B : H.Cell) (l : H.Loop)
    (hB : Condition.on_ring H l B) :
    Pos.offset l B (H.opp B) = L / 2 :=
  Pos.offset_opp_self H.four_le l B hB

/-- **A free string holds one bit, either sense with the probability `1/2`** (Sec. II): the tick
multiplies the strings of both senses by one factor, so the senses have one energy
(`Qubit.Tick.energy_eq`), and the string's thermal state, the Gibbs state over the two senses
(`Qubit.Tick.state`), gives each the probability `1/2`, with the entropy `ln 2`, the most a qubit
holds (thermodynamics as mathematics, on the qubit).  The third part, the bound `ln 2` on the
entropy of a qubit's two outcomes, is mathematics and takes no premise.  Sources: Sec. II's
sentence on the tick of a string of one sense (Postulates 1 and 2; the field `hsense` of `Tick`);
the objects are the tick, the inverse temperature and the energy as a function of the tick's
factor. -/
theorem string_one_bit (T : Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) :
    Qubit.bornProb (T.state β En) Qubit.e₁ = 1 / 2 ∧
    Qubit.entropy (Qubit.prob (T.state β En) 0) = Real.log 2 ∧
    ∀ p, Qubit.entropy p ≤ Real.log 2 :=
  ⟨T.bornProb_state β En, T.entropy_state β En,
    (Qubit.entropy_thermal β (T.energy En true)).2⟩

/-- **The probability of the outcome `1` is the share of the bits** (Sec. II, Eq. (raqm)): in the
state of a string with `m` 1s and the position `n`, the Born probability of `1` is `m/L`; and
**half the bits of a string in the thermal state are 1s on average** (Sec. II): over the mixture
of strings that the thermal state is, the expected share of 1s is `1/2`.  The first part holds by
the definition of the string's state, Postulate 1's qubit with Eqs. (qubit) and (raqm), and takes
no premise.  Sources, for the second part: Sec. II's sentence on the tick of a string of one sense
(Postulates 1 and 2; the field `hsense` of `Tick`), which makes the thermal state half the
identity; the condition: the thermal state as a mixture of strings. -/
theorem share_of_bits [NeZero L] (m n : ℕ) {S : Type*} [Fintype S] (T : Qubit.Tick L)
    (β : ℝ) (En : ℂ → ℝ) (ms ns : S → ℕ) (p : S → ℝ) (hmix : Condition.string_mixture T β En ms ns p) :
    Qubit.bornProb (Qubit.proj (Qubit.stringState L m n)) Qubit.e₁ = m / L ∧
    ∑ s, p s * (ms s / L) = 1 / 2 :=
  ⟨Qubit.share_stringState L m n, Qubit.half_bits_thermal T β En ms ns p hmix⟩

/-- **The horizon's radius and area in cells** (Secs. II and IV.D, Eq. (ident)): the solution
without a mass has its horizon at `R_Λ` (`hdS`), so a radius `r_h > 0` at which its metric function
vanishes (`hrh`) is that of a circle of a largest ring's length, `r_h = R_Λ = Lℓ_c/2π`, and the
horizon's area is `4πr_h² = A_hor = L²ℓ_c²/π`.  Sources: the constant of the solution without a
mass, `Λ = 3/R_Λ²` (`Derived`; `deSitter_horizon` derives it, with Postulate 2's last sentence for
the rings drawn in space among its sources); and the condition: `r_h` the radius of that
horizon. -/
theorem area_in_cells (R : Reg) (G Λ rh : ℝ) (hdS : Derived.deSitter_horizon R G Λ)
    (hrh : Condition.horizon_radius R G Λ rh) :
    rh = R.RL ∧ 4 * R.pi * rh ^ 2 = R.Ahor ∧
      4 * R.pi * rh ^ 2 = R.L ^ 2 * R.ℓc ^ 2 / R.pi := by
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  have hA : 4 * R.pi * rh ^ 2 = R.Ahor := by
    show 4 * R.pi * rh ^ 2 = 4 * R.pi * R.RL ^ 2
    rw [hr]
  exact ⟨hr, hA, hA.trans R.area_in_cells⟩

/-- **Eq. (Lcos)** (Sec. IV.D): `L = 2πr_h/ℓ_c`, with `r_h = √(3/Λ)` the radius of the horizon of
the solution without a mass, Eq. (ident) read backwards: the measured `Λ` and the cell give `L`,
and the horizon's radius pins the cell and `L` only through their product, `Lℓ_c = 2πr_h`.
The second part, `r_h = √(3/Λ)`, follows from the condition by the definition of the metric
function and takes no premise.  Sources: the constant of the solution without a mass (`Derived`);
and the condition: `r_h` the radius of that horizon. -/
theorem L_from_horizon (R : Reg) (G Λ rh : ℝ) (hdS : Derived.deSitter_horizon R G Λ)
    (hrh : Condition.horizon_radius R G Λ rh) :
    R.L = 2 * R.pi * rh / R.ℓc ∧ rh = Real.sqrt (3 / Λ) ∧ R.L * R.ℓc = 2 * R.pi * rh := by
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  have hΛ := (R.deSitter G Λ).1 hdS
  have hRL := R.RL_pos
  have e : Real.sqrt (3 / Λ) = R.RL := by
    rw [hΛ, show 3 / (3 / R.RL ^ 2) = R.RL ^ 2 by field_simp, Real.sqrt_sq hRL.le]
  refine ⟨by rw [hr]; exact R.L_from_horizon, by rw [hr, e], ?_⟩
  rw [hr]
  linarith [R.quarter_lap]

/-! ### Sec. III: temperature, heat and Newton's constant -/

/-- **The temperature of a horizon in cells, Eq. (T), and Unruh's temperature** (Secs. III.A and
III.B): a
horizon whose period is `L_a` ticks, `L_a = 2πc²/aℓ_c` for the horizon of an observer accelerating
at `a`, has `k_BT = E_c/L_a = ℏa/2πc`; and **the Clausius relation with the register's entropy,
Eq. (clausius)**: `k_BT_a ln 2 = ℏa ln 2/2πc` per ring, so the heat `δQ` adds the area
`[8ℓ_c²c/(ℏa ln 2)] δQ`, a ring's share for each bit.  Sources: the horizon thermal at the
temperature of its period (thermodynamics); the condition `a > 0`. -/
theorem temperature_in_cells (R : Reg) (a T δQ : ℝ) (ha : Condition.pos a)
    (I1 : Thermo.horizon_thermal R a T) :
    R.kB * T = R.Ec / R.La a ∧ R.kB * T * R.ln2 = R.ℏ * a * R.ln2 / (2 * R.pi * R.c) ∧
    (δQ / (R.kB * T * R.ln2)) * R.ringShare = (8 * R.ℓc ^ 2 * R.c / (R.ℏ * a * R.ln2)) * δQ := by
  have hLa : 0 < R.La a := by unfold Reg.La; reg_facts R; have : (0 : ℝ) < a := ha; positivity
  exact ⟨R.T_ring (R.La a) T hLa I1, (R.clausius a T δQ ha I1).1, (R.clausius a T δQ ha I1).2⟩

/-- **Newton's law in cells, Eq. (newton)** (Sec. III.C): `Mc² = 2N_s(r) k_BT_a ln 2`, two Landauer
energies per string at the Unruh temperature of the pull `a`, is `πn² ln 2 · ℏa/c`.  Sources: the
horizon thermal (thermodynamics); the condition `a > 0`. -/
theorem newton_in_cells (R : Reg) (a T r : ℝ) (ha : Condition.pos a)
    (I1 : Thermo.horizon_thermal R a T) :
    2 * R.Ns r * (R.kB * T * R.ln2) = R.pi * R.n r ^ 2 * R.ln2 * R.ℏ * a / R.c :=
  R.equipartition_in_cells a T r ha I1

/-- **The quarter follows for any count** (Sec. III.C): whatever entropy per unit area `η'` a count
assigns, Jacobson's `G = c³k_B/4ℏη'` makes it `k_B/4ℓ_P²`, Bekenstein and Hawking's quarter; the
count fixes the cell.  Sources: Jacobson's step for any density (`Derived`); the conditions `G > 0`,
`η' > 0`. -/
theorem quarter_any_count (R : Reg) (G η' : ℝ) (hG : Condition.pos G) (hη : Condition.pos η')
    (hJ : Derived.jacobson_G_density R G η') : η' = R.kB / (4 * R.ℓP G ^ 2) :=
  R.quarter_any_count G η' hG hη hJ

/-- **`G` and the entropy density are tied inversely** (Sec. III.C: "Without cells there is no
count, and `η` stays free"): Jacobson's coefficient gives `G · η = c³k_B/4ℏ`, so that the relation
fixes neither without a count.  Sources: `G` (`Derived`). -/
theorem G_mul_eta (R : Reg) (G : ℝ) (hJ : Derived.jacobson_G R G) :
    G * R.η = R.c ^ 3 * R.kB / (4 * R.ℏ) :=
  R.G_mul_eta G hJ

/-- **The Komar energy the mass adds is `Mc²`** (Sec. III.C, Eq. (newton)): about a body at rest
the solution is Schwarzschild–de Sitter, `e^{2α} = e^{−2β} = f` between the radii `a` and `b`
(`hsol`), and for such a metric Komar's energy inside the sphere of radius `r` is `c⁴r²f′/2G`, the
geometry's definition (`Reg.EK` is that of the solution without a mass).  That energy, less the
Komar energy of the solution without the mass at the same `Λ`, is `Mc²`, the energy that
gravitates.  The Komar energy enters as the geometry's definition, not as a hypothesis, and the
result uses the first half of `hsol`, `e^{2α} = f`.  Sources:
the solution about the body (`Derived`, `schwarzschild_deSitter`); the conditions: `a > 0`,
`G > 0`, and `r` between `a` and `b`. -/
theorem komar_mass (R : Reg) (G M Λ : ℝ) (α β : ℝ → ℝ) (a b r : ℝ) (ha : Condition.pos a)
    (hG : Condition.pos G) (hsol : Derived.schwarzschild_deSitter R G M Λ α β a b)
    (hr : Condition.between r a b) :
    R.c ^ 4 * r ^ 2 * deriv (fun x => Real.exp (2 * α x)) r / (2 * G) - R.EK G Λ r =
      M * R.c ^ 2 := by
  have hr0 : 0 < r := (show (0 : ℝ) < a from ha).trans hr.1
  have hev : (fun x => Real.exp (2 * α x)) =ᶠ[nhds r] R.fSdS G M Λ := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx using (hsol x hx).1
  rw [hev.deriv_eq, ← R.komar_mass G M Λ r hr0 (ne_of_gt hG)]
  unfold Reg.EK
  ring

/-! ### Sec. IV.A: the ceiling and the coding step -/

/-- **The ceiling for strings read in step, Eq. (nmax)** (Sec. IV.A): `N` strings read in step, on
rings of at most `L` cells, need `2^N ≤ L` when every joint outcome of the `N` qubits occurs
(`hall`).  The pairing is the strings' own, their bits at each position (`Capacity.jointOutcome`,
the definition that reads "The outcome at a position is the bits there").  A joint outcome that
occurs is the outcome at a position (Postulate 1, `hout`), so each joint outcome of the first
`N − 1` strings has a position where the last string reads `1` and one where it reads `−1`.
Sources: Postulate 1's "No ring has more than `L` cells" (`hL`), and its sentence on the bits as
the possible outcomes of one measurement, with its sentence that any two qubits can be measured
jointly (`hout`); the conditions: `1 ≤ N`, and every joint outcome occurs. -/
theorem ceiling_in_step {Cell : Type*} [Fintype Cell] (N L : ℕ) (hN : Condition.one_le N)
    (hL : P1.ring_cells Cell L) (bits : Fin N → Cell → Bool)
    (pr : (Fin (N - 1) → Bool) → Bool → ℝ)
    (hout : P1.outcomes_at_positions pr (Capacity.jointOutcome bits)
      (bits ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩))
    (hall : Condition.random_state pr) : 2 ^ N ≤ L :=
  (Capacity.ceiling_in_step N (Fintype.card Cell) hN rfl bits fun ω => by
    obtain ⟨x, hx, hbx⟩ := hout ω true (hall ω true)
    obtain ⟨y, hy, hby⟩ := hout ω false (hall ω false)
    exact Capacity.frac_pos_lt_one _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩) hbx
      (Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩) hby).trans hL

/-- **The ceiling for logical qubits, `2^{N+1} ≤ L`** (Sec. IV.A: "that string needs `2^N` blocks
of at least two cells"): a string, on a ring of at most `L` cells, with `2^N` conditional states
to hold, each a superposition.  Each cell is paired with one of `2^N` labels (`e`), which stand
for the conditional states, and each label occurs with either value of the string's bit
(`hall`).  A label that occurs with a value of the bit is at a position with that value
(Postulate 1, `hout`), so each label has a cell that reads `1` and a cell that reads `−1`.  The
statement is `ceiling` for `N + 1` qubits, and nothing in it says that the labels are
conditional states.  That the fullest physical string of
`N` logical qubits in the surface code has `2^N` distinct conditional states is `surface_code`,
which carries the ceiling for that code.  Sources: Postulate 1's "No ring has more than `L`
cells" (`hL`), and its sentence on the bits as the possible outcomes of one measurement, with
its sentence that any two qubits can be measured jointly (`hout`); the condition: every label
occurs with either value of the bit. -/
theorem ceiling_logical {Cell : Type*} [Fintype Cell] (N L : ℕ) (hL : P1.ring_cells Cell L)
    (e : Cell → Fin (2 ^ N)) (b : Cell → Bool) (pr : Fin (2 ^ N) → Bool → ℝ)
    (hout : P1.outcomes_at_positions pr e b) (hall : Condition.random_state pr) :
    2 ^ (N + 1) ≤ L :=
  (Capacity.ceiling_logical N (Fintype.card Cell) rfl e b fun k => by
    obtain ⟨x, hx, hbx⟩ := hout k true (hall k true)
    obtain ⟨y, hy, hby⟩ := hout k false (hall k false)
    exact Capacity.frac_pos_lt_one b _ (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩) hbx
      (Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩) hby).trans hL

/-- **A block of one cell holds no superposition** (Sec. IV.A): a joint outcome `k` whose block
has one cell does not occur with both values of the string's bit.  A joint outcome that occurs is
the outcome at a position (Postulate 1, `hout`), so both values would put a `1` and a `−1` on the
block, and a block of one cell has the fraction `0` or `1` (`Capacity.one_cell_block`).  So in a
state that the register holds on blocks of one cell, a joint outcome occurs with at most one
value of the string's bit, as in a state of the Greenberger–Horne–Zeilinger type: "blocks of
fraction 0 or 1, one cell each".  Sources: Postulate 1's sentence on the bits as the possible
outcomes of one measurement, with its sentence that any two qubits can be measured jointly
(`hout`); the condition: the block has one cell. -/
theorem one_cell_block {Cell K : Type*} [Fintype Cell] [DecidableEq K] (e : Cell → K)
    (b : Cell → Bool) (pr : K → Bool → ℝ) (hout : P1.outcomes_at_positions pr e b) (k : K)
    (h : Condition.one_cell (Capacity.block e id k)) : ¬(0 < pr k true ∧ 0 < pr k false) := by
  rintro ⟨h1, h0⟩
  obtain ⟨x, hx, hbx⟩ := hout k true h1
  obtain ⟨y, hy, hby⟩ := hout k false h0
  have hf := Capacity.frac_pos_lt_one b (Capacity.block e id k)
    (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩) hbx
    (Finset.mem_filter.2 ⟨Finset.mem_univ y, hy⟩) hby
  rcases Capacity.one_cell_block b _ h with h' | h'
  · rw [h'] at hf
    exact lt_irrefl _ hf.1
  · rw [h'] at hf
    exact lt_irrefl _ hf.2

/-- **The coding step, and the room it asks** (Sec. IV.A): in a Calderbank–Shor–Steane code
holding `N` logical qubits, a physical bit, given the earlier physical bits, is fixed, balanced,
or equal or opposite to the logical bit; so a physical string has at most `2^N` conditional states
to hold, those strictly between `0` and `1`; and its string, on a ring of at most `L` cells, has
two cells for each of them (`Coding.two_mul_card_states_le`).  The first two parts are coding
theory, which needs none of the premises.  The third is the room of the paper's step: "their
strings must have room for its conditional states as well".  Each cell of the string is paired
with a reading of the earlier bits (`e`: the word of the earlier blocks and a word of the last
block, read on the positions `P`), and the reading gives the string's qubit a conditional state.
In the state that the register holds, each conditional state that is a superposition occurs with
either value of the string's bit (`hcond`).  A conditional state that occurs with a value of the
bit is at a position with that value (Postulate 1, `hout`).  So the block of each such state, the
cells whose readings give it, has a cell that reads `1` and a cell that reads `−1`
(`Coding.shows_of_outcomes`).  The count is by conditional state, two cells for each.  The
paper's count for codes agrees with it: the fullest physical string "has up to `2^N` conditional
states to hold", and "Where the equal and the opposite case both occur and the `2^N` conditional
states are superpositions that all differ in probability, as in a random state, that string
needs `2^N` blocks of at least two cells".  Two cells for each state meet the two hypotheses
(`Coding.two_cells_each_model`).  Sources: Postulate 1's "No ring has more than `L` cells"
(`hL`), and its sentence on the bits as the possible outcomes of one measurement, with its
sentence that any two qubits can be measured jointly (`hout`); the conditions: `1 ≤ N`,
`2^{N−1}` joint outcomes of the first `N − 1` logical qubits, and `hcond`, as above. -/
theorem coding_step {n : ℕ} (C₀ : AddSubgroup (Coding.Word n)) (v : Coding.Word n)
    {K W Cell : Type*} [Fintype K] [Fintype W] [Fintype Cell] (N L : ℕ) (hN : Condition.one_le N)
    (hK : Condition.card_outcomes K N) (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ)
    (P : Finset (Fin n)) (w : W) (u : Coding.Word n) (j : Fin n)
    (hL : P1.ring_cells Cell L) (e : Cell → W × Coding.Word n) (b : Cell → Bool)
    (pr : ℝ → Bool → ℝ)
    (hout : P1.outcomes_at_positions pr
      (fun x => Coding.jointBitGiven C₀ v p κ g P (e x).1 (e x).2 j) b)
    (hcond : Condition.conditional_states pr
      (fun wu : W × Coding.Word n => Coding.jointBitGiven C₀ v p κ g P wu.1 wu.2 j)) :
    (Coding.jointBitGiven C₀ v p κ g P w u j = 0 ∨ Coding.jointBitGiven C₀ v p κ g P w u j = 1 ∨
      Coding.jointBitGiven C₀ v p κ g P w u j = 1 / 2 ∨
      Coding.jointBitGiven C₀ v p κ g P w u j = p (κ w) 1 / (p (κ w) 0 + p (κ w) 1) ∨
      Coding.jointBitGiven C₀ v p κ g P w u j = p (κ w) 0 / (p (κ w) 0 + p (κ w) 1)) ∧
    (Coding.condStates C₀ v p κ g P j).card ≤ 2 ^ N ∧
    2 * (Coding.condStates C₀ v p κ g P j).card ≤ L := by
  classical
  exact ⟨Coding.css_conditional_joint C₀ v p κ g P w u j,
    Coding.card_condStates_le C₀ v N hN hK p κ g P j,
    (Coding.two_mul_card_states_le _ e b (Coding.shows_of_outcomes e b pr hcond hout)).trans hL⟩

/-- **The repetition code** (Sec. IV.A): only the fixed and the equal case occur, so a physical
string has no more conditional states to hold than a logical string, `2^{N−1}`; and its string, on
a ring of at most `L` cells, has two cells for each.  The first two parts are coding theory, which
needs none of the premises; the third is the room of `coding_step` for this code.  The paper's
"the ceiling stays `204`" rests on the second part: two cells for each of at most `2^{N−1}` states
are no more than a logical string asks.  Sources: as `coding_step`, without the condition
`1 ≤ N`. -/
theorem repetition_code {n : ℕ} {K W Cell : Type*} [Fintype K] [Fintype W] [Fintype Cell]
    (N L : ℕ) (hK : Condition.card_outcomes K N) (q : ZMod 2 → ℝ) (p : K → ZMod 2 → ℝ)
    (κ : W → K) (g : W → ℝ) (P : Finset (Fin n)) (u : Coding.Word n) (j : Fin n)
    (hL : P1.ring_cells Cell L) (e : Cell → W × Coding.Word n) (b : Cell → Bool)
    (pr : ℝ → Bool → ℝ)
    (hout : P1.outcomes_at_positions pr
      (fun x => Coding.jointBitGiven ⊥ (fun _ => 1) p κ g P (e x).1 (e x).2 j) b)
    (hcond : Condition.conditional_states pr
      (fun wu : W × Coding.Word n => Coding.jointBitGiven ⊥ (fun _ => 1) p κ g P wu.1 wu.2 j)) :
    (Coding.bitGiven ⊥ (fun _ => 1) q P u j = 0 ∨ Coding.bitGiven ⊥ (fun _ => 1) q P u j = 1 ∨
      Coding.bitGiven ⊥ (fun _ => 1) q P u j = q 1 / (q 0 + q 1)) ∧
    (Coding.condStates ⊥ (fun _ => 1) p κ g P j).card ≤ 2 ^ (N - 1) ∧
    2 * (Coding.condStates ⊥ (fun _ => 1) p κ g P j).card ≤ L := by
  classical
  exact ⟨Coding.repetition_conditional q P u j,
    Coding.card_condStates_repetition N hK p κ g P j,
    (Coding.two_mul_card_states_le _ e b (Coding.shows_of_outcomes e b pr hcond hout)).trans hL⟩

/-- **A logical qubit read as the parity of a line: the ceiling is `2^{N+1} ≤ L`** (Sec. IV.A).  In
every code whose logical bit is the parity of a line of physical bits, the last bit of the line,
given the parity of the rest, is the logical bit or its opposite
(`Coding.LineCode.lastGivenRest_eq`; this first part holds in every line code and needs none of
the hypotheses).  Where every reading of the rest of the line occurs in both logical states
(`hm`), the last bit, given the earlier blocks and the rest of the line, is the last logical bit
or its opposite, so both cases occur.  For `N` logical qubits in a random state it then has
exactly `2^N` conditional states strictly between `0` and `1`, twice a logical string's.  Its
string, on a ring of at most `L` cells, has two cells for each of them, as in `coding_step`, so
`2^{N+1} ≤ L` (`Coding.ceiling_line_code`).  The first three parts are coding theory, which takes
none of the premises; the fourth is the room.  Sources: Postulate 1's "No ring has more than `L`
cells" (`hL`), and its sentence on the bits as the possible outcomes of one measurement, with
its sentence that any two qubits can be measured jointly (`hout`); the conditions: every reading
of the rest of the line in both logical states (`hm`), `2^{N−1}` outcomes of the earlier logical
qubits, the random state, and `hcond`: each conditional state that is a superposition occurs
with either value of the bit. -/
theorem line_code {n : ℕ} {K W Cell : Type*} [Fintype K] [Fintype W] [Fintype Cell]
    (code : Coding.LineCode n) (q : ZMod 2 → ℝ) (s : ZMod 2) (hm : Condition.line_match code)
    (N L : ℕ) (hK : Condition.card_outcomes K N) (p : K → ZMod 2 → ℝ) (κ : W → K) (g : W → ℝ)
    (hrand : Condition.line_random N p κ g)
    (hL : P1.ring_cells Cell L) (e : Cell → W × Coding.Word n) (b : Cell → Bool)
    (pr : ℝ → Bool → ℝ)
    (hout : P1.outcomes_at_positions pr (fun x =>
      Coding.jointBitGiven code.C₀ code.v p κ g (code.S.erase code.j) (e x).1 (e x).2 code.j) b)
    (hcond : Condition.conditional_states pr (fun wu : W × Coding.Word n =>
      Coding.jointBitGiven code.C₀ code.v p κ g (code.S.erase code.j) wu.1 wu.2 code.j)) :
    code.lastGivenRest q s = Coding.caseProb q s ∧
    (∀ (w : W) (u : Coding.Word n), g w ≠ 0 →
      Coding.jointBitGiven code.C₀ code.v p κ g (code.S.erase code.j) w u code.j =
        Coding.caseProb (p (κ w)) (code.rest u)) ∧
    (Coding.condStates code.C₀ code.v p κ g (code.S.erase code.j) code.j).card = 2 ^ N ∧
    2 ^ (N + 1) ≤ L := by
  classical
  exact ⟨code.lastGivenRest_eq q s, fun w u hg => code.jointBitGiven_rest hm p κ g w u hg,
    code.card_lineStates hm N hrand.1 hK p hrand.2.1 κ g hrand.2.2.1 hrand.2.2.2,
    (Coding.ceiling_line_code N (Fintype.card Cell) hrand.1 rfl hK code hm p hrand.2.1 κ g
      hrand.2.2.1 hrand.2.2.2 e b (Coding.shows_of_outcomes e b pr hcond hout)).trans hL⟩

/-- **In the surface code the ceiling is `2^{N+1} ≤ L`** (Sec. IV.A, the ceiling of `203` logical
qubits): the surface code of every distance `d ≥ 2` is a line code in which every reading of the
rest of the row occurs in both logical states (`Coding.surfaceCode_match`, the first part, which
is coding theory), so for `N` logical qubits in a random state the last bit of the row has exactly
`2^N` conditional states to hold, and its string, on a ring of at most `L` cells, needs
`2^{N+1} ≤ L`: the ceiling for logical qubits is one below the physical one
(`Coding.ceiling_line_code`).  The first two parts are coding theory, which takes none of the
premises; the third is the room, as in `coding_step`.  Two cells for each conditional state meet
its two hypotheses (`Coding.two_cells_each_model`), and the second part counts `2^N` of them.
Sources: Postulate 1's "No ring has more than `L` cells" (`hL`), and its sentence on the bits as
the possible outcomes of one measurement, with its sentence that any two qubits can be measured
jointly (`hout`); the conditions: `d ≥ 2`, `2^{N−1}` outcomes of the earlier logical qubits, the
random state, and `hcond`: each conditional state that is a superposition occurs with either
value of the bit. -/
theorem surface_code {K W Cell : Type*} [Fintype K] [Fintype W] [Fintype Cell] (d : ℕ)
    (hd : Condition.two_le d) (N L : ℕ) (hK : Condition.card_outcomes K N) (p : K → ZMod 2 → ℝ)
    (κ : W → K) (g : W → ℝ) (hrand : Condition.line_random N p κ g)
    (hL : P1.ring_cells Cell L) (e : Cell → W × Coding.Word (d * d)) (b : Cell → Bool)
    (pr : ℝ → Bool → ℝ)
    (hout : P1.outcomes_at_positions pr (fun x =>
      Coding.jointBitGiven (Coding.surfaceCode d hd).C₀ (Coding.surfaceCode d hd).v p κ g
        ((Coding.surfaceCode d hd).S.erase (Coding.surfaceCode d hd).j) (e x).1 (e x).2
        (Coding.surfaceCode d hd).j) b)
    (hcond : Condition.conditional_states pr (fun wu : W × Coding.Word (d * d) =>
      Coding.jointBitGiven (Coding.surfaceCode d hd).C₀ (Coding.surfaceCode d hd).v p κ g
        ((Coding.surfaceCode d hd).S.erase (Coding.surfaceCode d hd).j) wu.1 wu.2
        (Coding.surfaceCode d hd).j)) :
    (Coding.surfaceCode d hd).Match ∧
    (Coding.condStates (Coding.surfaceCode d hd).C₀ (Coding.surfaceCode d hd).v p κ g
      ((Coding.surfaceCode d hd).S.erase (Coding.surfaceCode d hd).j)
      (Coding.surfaceCode d hd).j).card = 2 ^ N ∧
    2 ^ (N + 1) ≤ L := by
  classical
  exact ⟨Coding.surfaceCode_match d hd,
    (Coding.surfaceCode d hd).card_lineStates (Coding.surfaceCode_match d hd) N hrand.1 hK p
      hrand.2.1 κ g hrand.2.2.1 hrand.2.2.2,
    (Coding.ceiling_line_code N (Fintype.card Cell) hrand.1 rfl hK (Coding.surfaceCode d hd)
      (Coding.surfaceCode_match d hd) p hrand.2.1 κ g hrand.2.2.1 hrand.2.2.2 e b
      (Coding.shows_of_outcomes e b pr hcond hout)).trans hL⟩

/-! ### Sec. IV.C: the horizon with a mass, the carriers, the law (with a black hole's horizon,
Sec. IV.D, and the scale at every epoch, Secs. V and VI) -/

/-- **The horizon with a mass inside holds `L_M²/4` bits** (Sec. IV.C): the mass draws the horizon
in by `GM/c²`, to `R_Λ − GM/c²` to first order, and the entropy density, the law `η` at any
crossing, one value by Postulate 2's two clauses and the count's at leading order, gives that area
`L_M²/4` bits with `L_M = L − 2α/ln 2`, the count `N_s` of that sphere.  Sources:
Postulate 2's two clauses on laws (one density); `G` (`Derived`); the constant of the solution
without a mass (`Derived`); the count's density at leading order (`Approx`); the conditions: the
two crossings are crossings, the horizon's radius. -/
theorem massive_horizon {H : Horizon L} (R : Reg) (G M Λ rh : ℝ)
    (η : H.Cell → H.Loop → ℝ) (hsym : P2.homogeneous H η) (hdir : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀)
    (hJ : Derived.jacobson_G R G) (hdS : Derived.deSitter_horizon R G Λ)
    (hrh : Condition.horizon_radius R G Λ rh) (hcount : Approx.count_density H R η l₀ x₀ rh)
    (l : H.Loop) (x : H.Cell) (hx : Condition.on_ring H l x) :
    R.Ns (R.RL - G * M / R.c ^ 2) = (R.L - 2 * R.α M / R.ln2) ^ 2 / 4 ∧
    η x l * (4 * R.pi * (R.RL - G * M / R.c ^ 2) ^ 2)
      = R.kB * ((R.L - 2 * R.α M / R.ln2) ^ 2 / 4) * R.ln2 := by
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  have hc : η x₀ l₀ = R.kB * (R.Rhor * R.ln2) / (4 * R.pi * rh ^ 2) := hcount
  have hη : η x₀ l₀ = R.η := by rw [hc, hr]; rfl
  obtain ⟨hone, harea⟩ := Symmetry.massive_horizon_density R G M η hsym hdir h₀ hη hJ
  exact ⟨R.massive_horizon_count G M hJ, by rw [hone l x hx]; exact harea⟩

/-- **A black hole's horizon holds `L'²/4` bits at the register's one density** (Sec. IV.D): the
area `4πr_s²`, `r_s = 2GM/c²`, at the entropy density, the law `η` at any crossing, one value by
Postulate 2's two clauses and the count's at leading order, gives `(L'²/4) ln 2` with
`L' = 4πGM/c²ℓ_c` cells around it.  Sources: Postulate 2's two clauses on laws; the count's
density at leading order (`Approx`); the constant of the solution without a mass (`Derived`); the
conditions: the two crossings are crossings, the horizon's radius. -/
theorem black_hole_horizon {H : Horizon L} (R : Reg) (G M Λ rh : ℝ)
    (η : H.Cell → H.Loop → ℝ) (hsym : P2.homogeneous H η) (hdir : P2.directions H η)
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : Condition.on_ring H l₀ x₀)
    (hdS : Derived.deSitter_horizon R G Λ) (hrh : Condition.horizon_radius R G Λ rh)
    (hcount : Approx.count_density H R η l₀ x₀ rh)
    (l : H.Loop) (x : H.Cell) (hx : Condition.on_ring H l x) :
    η x l * (4 * R.pi * (2 * G * M / R.c ^ 2) ^ 2)
      = R.kB * ((4 * R.pi * G * M / (R.c ^ 2 * R.ℓc)) ^ 2 / 4) * R.ln2 := by
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  have hc : η x₀ l₀ = R.kB * (R.Rhor * R.ln2) / (4 * R.pi * rh ^ 2) := hcount
  have hη : η x₀ l₀ = R.η := by rw [hc, hr]; rfl
  obtain ⟨hone, harea⟩ := Symmetry.black_hole_density R G M η hsym hdir h₀ hη
  rw [hone l x hx]; exact harea

/-- **Why the temperature cannot lead** (Sec. IV.C): were gravity the excess of the Deser–Levin
temperature over the floor, the Unruh temperature of Newton's field `g_N` being `T′ − T_dS`
(`hled`, the rejected alternative's premise), then `√(a² + a_Λ²) − a_Λ = g_N`, so
`a² = g_N² + 2a_Λ g_N`, the deep form with `a_M = 2a_Λ = 2c²/r_h`, nine times the observed value
(`Numerics.temperature_led_numbers`).
Sources: the Deser–Levin temperature and the thermal horizons, the cosmological one and that of
`g_N` (thermodynamics); the constant `Λ = 3/R_Λ²` (`Derived`), which makes the surface gravity of
the horizon `a_Λ` (`Reg.surface_gravity_eq`); and the conditions: `g_N > 0`, `r_h` the radius of
the horizon, and the alternative's premise. -/
theorem temperature_led (R : Reg) (G Λ rh a gN T' TdS TN : ℝ) (hgN : Condition.pos gN)
    (hdS : Derived.deSitter_horizon R G Λ) (hrh : Condition.horizon_radius R G Λ rh)
    (hDL : Thermo.deser_levin R G Λ rh a T')
    (I1dS : Thermo.horizon_thermal R (-R.gSdS G 0 Λ rh) TdS)
    (I1N : Thermo.horizon_thermal R gN TN) (hled : Condition.temperature_led T' TdS TN) :
    a ^ 2 = gN ^ 2 + 2 * R.aΛ * gN ∧ 2 * R.aΛ = 2 * R.c ^ 2 / rh := by
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  have hsg := R.surface_gravity_eq G Λ rh hdS hrh.1 hrh.2
  reg_facts R
  have haΛ : 0 < R.aΛ := by unfold Reg.aΛ; have := R.RL_pos; positivity
  -- the three temperatures: Deser–Levin's, the floor, and Unruh's at `g_N`
  have h1 : R.kB * T' = R.ℏ / (2 * R.pi * R.c) * Real.sqrt (a ^ 2 + R.aΛ ^ 2) := by
    have h : R.kB * T' =
        R.ℏ / (2 * R.pi * R.c) * Real.sqrt (a ^ 2 + (-R.gSdS G 0 Λ rh) ^ 2) := hDL
    rwa [hsg] at h
  have h2 : R.kB * TdS = R.ℏ * R.aΛ / (2 * R.pi * R.c) := by
    have h : R.kB * TdS = R.ℏ / (R.La (-R.gSdS G 0 Λ rh) * R.tc) := I1dS
    rw [hsg] at h
    exact R.T_Unruh R.aΛ TdS haΛ h
  have h3 : R.kB * TN = R.ℏ * gN / (2 * R.pi * R.c) := R.T_Unruh gN TN hgN I1N
  have hled' : T' - TdS = TN := hled
  have hk : R.ℏ / (2 * R.pi * R.c) ≠ 0 := by positivity
  have h4 : R.ℏ / (2 * R.pi * R.c) * (Real.sqrt (a ^ 2 + R.aΛ ^ 2) - R.aΛ) =
      R.ℏ / (2 * R.pi * R.c) * gN := by
    have h : R.kB * T' - R.kB * TdS = R.kB * TN := by rw [← hled']; ring
    rw [h1, h2, h3] at h
    linear_combination h
  obtain ⟨e1, e2⟩ := R.temperature_led a gN (mul_left_cancel₀ hk h4)
  exact ⟨e1, by rw [e2, hr]⟩

/-- **The share of a body's energy among its carriers, Eq. (share)** (Sec. IV.C).  The body's
energy is held by the carriers (`hcar`, Postulate 1), the fraction `b` of the sphere's strings
(`hNcar`), each at the share `κT_a` of equipartition (`hκ`), and Newton's equal share, Eq. (E), is
`κT_N` for each string of the sphere (`hκN`); with `I1` for the Unruh temperatures of `g_N` and of
`a`, and Jacobson's `G`, `κ = 2k_B ln 2`, two Landauer energies per string, and `a = g_N/b`.  Each
carrier then holds `ε_c = E/b`, with `E = Mc²/N_s` the body's energy per string of the sphere,
and that is at least `E` where `b ≤ 1` (Sec. IV.C: "those strings then hold the larger share
`E/b` of Eq. (share)").  It is two Landauer energies at the sphere's temperature,
`ε_c = 2k_BT_a ln 2`, and no premise or condition of the statement compares `E` with the matter
`u` that a string holds on average ("The body's share is then still held, since by Eq. (share)
each string that carries the body's information holds two Landauer energies at the sphere's
temperature, whatever `f` is.  So `u` sets the unit of `h`; it does not limit what a string
holds").
Sources: Postulate 1's first sentence for a body's energy; equipartition and the thermal horizons
(thermodynamics); `G` (`Derived`); and the conditions: `M, r, a > 0`, the carrier fraction. -/
theorem carriers_share (R : Reg) (G M r a TN Ta b Ncar εc κ : ℝ)
    (hM : Condition.pos M) (hr : Condition.pos r) (ha : Condition.pos a)
    (hJ : Derived.jacobson_G R G)
    (I1N : Thermo.horizon_thermal R (G * M / r ^ 2) TN) (I1a : Thermo.horizon_thermal R a Ta)
    (hcar : P1.energy_in_carriers R M Ncar εc) (hNcar : Condition.carrier_fraction R b Ncar r)
    (hκ : Thermo.equipartition κ εc Ta) (hκN : Thermo.equipartition κ (M * R.c ^ 2 / R.Ns r) TN) :
    Derived.share_acceleration a (G * M / r ^ 2) b ∧ κ = 2 * R.kB * R.ln2 ∧
    M * R.c ^ 2 = 2 * R.Ns r * (R.kB * TN * R.ln2) ∧
    εc = M * R.c ^ 2 / R.Ns r / b ∧ εc = 2 * R.kB * Ta * R.ln2 ∧
    (b ≤ 1 → M * R.c ^ 2 / R.Ns r ≤ εc) := by
  reg_facts R
  have hr' : 0 < r := hr
  have hM' : 0 < M := hM
  have hG := (R.G_eq G hJ).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * M / r ^ 2 := by positivity
  have hN := R.newton_share G M r TN hr' hM' hJ I1N
  have hNs : 0 < R.Ns r := by rw [R.bulk_counts r]; unfold Reg.n; positivity
  have hTN : 0 < R.kB * TN := by rw [R.T_Unruh _ TN hgN I1N]; positivity
  have hTN' : TN ≠ 0 := by
    intro h
    rw [h, mul_zero] at hTN
    exact lt_irrefl 0 hTN
  have hκN' : M * R.c ^ 2 = R.Ns r * (κ * TN) := by
    have h : M * R.c ^ 2 / R.Ns r = κ * TN := hκN
    rw [← h]; field_simp
  have hκv : κ = 2 * R.kB * R.ln2 := by
    have e : R.Ns r * (κ * TN) = R.Ns r * (2 * R.kB * R.ln2 * TN) := by
      rw [← hκN', hN]
      ring
    exact mul_right_cancel₀ hTN' (mul_left_cancel₀ hNs.ne' e)
  have hK : M * R.c ^ 2 = 2 * (b * R.Ns r) * (R.kB * Ta * R.ln2) := by
    have h1 : M * R.c ^ 2 = Ncar * εc := hcar
    have h2 : Ncar = b * R.Ns r := hNcar
    have h3 : εc = κ * Ta := hκ
    rw [h1, h2, h3, hκv]
    ring
  have hbpos : 0 < b := by
    have ha' : 0 < a := ha
    have hTa : 0 < R.kB * Ta := by rw [R.T_Unruh a Ta ha' I1a]; positivity
    have hMc : 0 < M * R.c ^ 2 := by positivity
    rw [hK] at hMc
    have : 0 < b * R.Ns r := by
      by_contra hcon
      push Not at hcon
      have : 2 * (b * R.Ns r) * (R.kB * Ta * R.ln2) ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg
        · linarith
        · positivity
      linarith
    exact pos_of_mul_pos_left this hNs.le
  have hεc : εc = M * R.c ^ 2 / R.Ns r / b := by
    have h1 : M * R.c ^ 2 = Ncar * εc := hcar
    have h2 : Ncar = b * R.Ns r := hNcar
    rw [h1, h2]
    field_simp
  have hεT : εc = 2 * R.kB * Ta * R.ln2 := by
    have h3 : εc = κ * Ta := hκ
    rw [h3, hκv]
    ring
  have hlarger : b ≤ 1 → M * R.c ^ 2 / R.Ns r ≤ εc := by
    intro hb1
    have hE : 0 < M * R.c ^ 2 / R.Ns r := by positivity
    rw [hεc, le_div_iff₀ hbpos]
    nlinarith
  exact ⟨R.share_acceleration M (R.Ns r) b TN Ta (G * M / r ^ 2) a hNs hbpos hgN ha hN hK I1N I1a,
    hκv, hN, hεc, hεT, hlarger⟩

/-- **What reaches a string, Eqs. (E), (u) and (f)** (Sec. IV.C): the body's energy per string of the
sphere, two Landauer energies at the Unruh temperature of `g_N` (`I1N`), in units of the mean
string's matter `u = (1 − ln 2)ε_s` (`Reg.matter`: "The body is a mass, and a mass is matter, not
heat, so we count the body's energy per string of the sphere in units of the matter a string
holds on average"), with the strings' mean energy `ε_s = k_BT_dS`, the mean of the
Gibbs distribution at the horizon's temperature (`hGibbs`; `Carriers.string_energy`), is
`f = g_N/a₀` with `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`, Eq. (f).  The second part is the definition of
`a₀` and takes no premise.  The third part: the body's energy per string exceeds the matter a
string holds on average exactly where `g_N > a₀` ("Nearer the body `f > 1`, and farther out
`f < 1`").  Sources: the strings' energies spread at the horizon's temperature,
and the thermal horizons (thermodynamics); the constant `Λ = 3/R_Λ²` (`Derived`); and the
conditions: `g_N > 0`, `r_h` the radius of the horizon. -/
theorem fill_fraction (R : Reg) (G Λ rh gN TN TdS εs : ℝ) (hgN : Condition.pos gN)
    (hdS : Derived.deSitter_horizon R G Λ) (hrh : Condition.horizon_radius R G Λ rh)
    (I1N : Thermo.horizon_thermal R gN TN) (I1dS : Thermo.horizon_thermal R (-R.gSdS G 0 Λ rh) TdS)
    (hGibbs : Thermo.energies_thermal R TdS εs) :
    Derived.fill_fraction R gN TN εs ∧
    R.a0 = (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * R.RL) ∧
    (R.a0 < gN ↔ R.matter εs < 2 * R.kB * TN * R.ln2) := by
  have I1' := R.thermal_lap G Λ rh TdS hdS hrh.1 hrh.2 I1dS
  have hεs := R.string_energy εs TdS hGibbs I1'
  have hff : 2 * R.kB * TN * R.ln2 / R.matter εs = gN / R.a0 :=
    R.fill_fraction gN TN TdS εs hgN I1N I1' hεs
  refine ⟨hff, rfl, ?_⟩
  have hu : 0 < R.matter εs := by
    reg_facts R
    have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
    have hT := (R.T_dS TdS I1').2
    have hTpos : 0 < R.kB * TdS := by rw [hT]; have := R.RL_pos; positivity
    unfold Reg.matter
    rw [hεs]
    exact mul_pos hm hTpos
  rw [← one_lt_div R.a0_pos, ← hff, one_lt_div hu]

/-- **The galactic law, Eq. (law)** (Sec. IV.C), from its sources and nothing else: about all the
mass `M` inside a sphere of radius `r`, the acceleration is `a = g_N/(1 − e^{−√(g_N/a₀)})` with
`g_N = GM/r²` and `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`, `R_Λ = √(3/Λ)`; Newton's equal share is
Eq. (newton) at `g_N`; and a string's share is `κT` with `κ = 2k_B ln 2`
(`Reg.radial_acceleration_relation`).  Sources: `G` (`Derived`, Jacobson); the constant
`Λ = 3/R_Λ²` (`Derived`); the thermal horizons, the cosmological one and those of `g_N` and of `a`
(thermodynamics); the strings' energies spread at the horizon's temperature (thermodynamics); a
body's energy held by its carriers, and the carriers as the strings whose threshold the amplitude
exceeds (Postulate 1); maximum entropy for the threshold and equipartition (thermodynamics); and
the conditions:
`M, r, a > 0`, `r_h` the radius of the horizon, the carrier fraction. -/
theorem galactic_law (R : Reg) (G Λ rh M r a TdS TN Ta εs b Ncar εc κ : ℝ)
    (surv : ℝ → ℝ) (hM : Condition.pos M) (hr : Condition.pos r) (ha : Condition.pos a)
    (hJ : Derived.jacobson_G R G) (hdS : Derived.deSitter_horizon R G Λ)
    (hrh : Condition.horizon_radius R G Λ rh)
    (I1dS : Thermo.horizon_thermal R (-R.gSdS G 0 Λ rh) TdS)
    (I1N : Thermo.horizon_thermal R (G * M / r ^ 2) TN) (I1a : Thermo.horizon_thermal R a Ta)
    (hGibbs : Thermo.energies_thermal R TdS εs)
    (hME : Thermo.max_entropy_threshold surv) (hb : P1.carriers_by_amplitude R b TN εs surv)
    (hcar : P1.energy_in_carriers R M Ncar εc) (hNcar : Condition.carrier_fraction R b Ncar r)
    (hκ : Thermo.equipartition κ εc Ta) (hκN : Thermo.equipartition κ (M * R.c ^ 2 / R.Ns r) TN) :
    Derived.galactic_law R a (G * M / r ^ 2) ∧
    R.a0 = (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * Real.sqrt (3 / Λ)) ∧
    M * R.c ^ 2 = 2 * R.Ns r * (R.kB * TN * R.ln2) ∧ κ = 2 * R.kB * R.ln2 := by
  have I1' := R.thermal_lap G Λ rh TdS hdS hrh.1 hrh.2 I1dS
  have hNs : 0 < R.Ns r := by
    reg_facts R; have hr' : 0 < r := hr
    rw [R.bulk_counts r]; unfold Reg.n; positivity
  have hκN' : M * R.c ^ 2 = R.Ns r * (κ * TN) := by
    have h : M * R.c ^ 2 / R.Ns r = κ * TN := hκN
    rw [← h]; field_simp
  exact R.radial_acceleration_relation G hJ Λ hdS TdS I1' εs hGibbs M r hM hr TN I1N a Ta
    ha I1a surv hME b hb Ncar εc κ hcar hNcar hκ hκN'

/-- **Near the body** (Sec. IV.C): with `h = √(g_N/a₀)`, the acceleration of the law, Eq. (law)
(`hlaw`), exceeds Newton's by `g_N e^{−h}/(1 − e^{−h})`, more than `g_N e^{−h}`, and
`a − g_N(1 + e^{−h}) = g_N e^{−2h}/(1 − e^{−h})`: Newton's law returns exponentially.  Sources: the
law (`Derived`, `galactic_law`); the condition `g_N > 0`. -/
theorem near_limit (R : Reg) (a gN : ℝ) (hgN : Condition.pos gN)
    (hlaw : Derived.galactic_law R a gN) :
    a - gN = gN * (Real.exp (-Real.sqrt (gN / R.a0)) / (1 - Real.exp (-Real.sqrt (gN / R.a0)))) ∧
    gN * Real.exp (-Real.sqrt (gN / R.a0)) < a - gN ∧
    a - gN * (1 + Real.exp (-Real.sqrt (gN / R.a0))) =
      gN * Real.exp (-Real.sqrt (gN / R.a0)) ^ 2 / (1 - Real.exp (-Real.sqrt (gN / R.a0))) := by
  have hh : 0 < Real.sqrt (gN / R.a0) := Real.sqrt_pos.2 (div_pos hgN R.a0_pos)
  have hlaw' : a = gN / (1 - Real.exp (-Real.sqrt (gN / R.a0))) := hlaw
  rw [hlaw']
  exact Law.near_limit gN _ hgN hh

/-- **Far from the body, Eq. (deep)** (Sec. IV.C): where `h = √(g_N/a₀) ≤ 1/2`, the acceleration of
the law, Eq. (law) (`hlaw`), lies within `a₀h³` of `√(a₀g_N) + g_N/2`.  Sources: the law
(`Derived`, `galactic_law`); the conditions `g_N > 0` and `h ≤ 1/2`. -/
theorem deep_limit (R : Reg) (a gN : ℝ) (hgN : Condition.pos gN)
    (hh2 : Condition.at_most_half (Real.sqrt (gN / R.a0)))
    (hlaw : Derived.galactic_law R a gN) :
    Real.sqrt (R.a0 * gN) + gN / 2 - R.a0 * Real.sqrt (gN / R.a0) ^ 3 ≤ a ∧
    a ≤ Real.sqrt (R.a0 * gN) + gN / 2 + R.a0 * Real.sqrt (gN / R.a0) ^ 3 := by
  have ha0 := R.a0_pos
  have hgN' : 0 < gN := hgN
  have hh : 0 < Real.sqrt (gN / R.a0) := Real.sqrt_pos.2 (div_pos hgN' ha0)
  have hsq : Real.sqrt (gN / R.a0) ^ 2 = gN / R.a0 := Real.sq_sqrt (div_pos hgN' ha0).le
  -- `a₀h² = g_N` and `a₀h = √(a₀g_N)`
  have e1 : R.a0 * Real.sqrt (gN / R.a0) ^ 2 = gN := by
    rw [hsq]; field_simp
  have hnn : 0 ≤ R.a0 * Real.sqrt (gN / R.a0) := by positivity
  have e2 : Real.sqrt (R.a0 * gN) = R.a0 * Real.sqrt (gN / R.a0) := by
    have h : R.a0 * gN = (R.a0 * Real.sqrt (gN / R.a0)) ^ 2 := by
      rw [mul_pow, hsq]; field_simp
    rw [h, Real.sqrt_sq hnn]
  have hlaw' : a = gN / (1 - Real.exp (-Real.sqrt (gN / R.a0))) := hlaw
  obtain ⟨hlo, hhi⟩ := Law.deep_limit R.a0 (Real.sqrt (gN / R.a0)) ha0 hh hh2
  rw [e1] at hlo hhi
  rw [hlaw', e2]
  exact ⟨hlo, hhi⟩

/-- **The baryonic Tully–Fisher relation, Eq. (btfr)** (Sec. IV.C): in the deep regime, where the
field is `√(a₀g_N)` with `g_N = GM/r²`, the speeds on circular orbits (`hv`, `rotation_curve`) obey
`v⁴ = a₀GM` at every radius: flat rotation curves.  Sources: the speeds on circular orbits
(`Derived`); the conditions `a₀, G, M, r > 0`. -/
theorem tully_fisher (a0 G M r : ℝ) (v : ℝ → ℝ) (ha0 : Condition.pos a0) (hG : Condition.pos G)
    (hM : Condition.pos M) (hr : Condition.pos r)
    (hv : Derived.circular_speeds (fun s => Real.sqrt (a0 * (G * M / s ^ 2))) v) :
    v r ^ 4 = a0 * G * M :=
  Law.tully_fisher a0 G M r (v r) ha0 hG hM hr (hv r hr)

/-- **A classical share would make rotation speeds rise** (Sec. IV.C): were the carriers the
fraction `f = g_N/a₀` (`Condition.classical_share`, the rejected alternative), the acceleration
`g_N/b` would be `a₀` and `v² = a₀r` on circular orbits.  Sources: the speeds on circular orbits
and `a = g_N/b` (`Derived`); the conditions: `g_N > 0`, `r > 0` and the alternative's premise. -/
theorem classical_share (a0 gN a b r : ℝ) (v : ℝ → ℝ) (hgN : Condition.pos gN)
    (hb : Condition.classical_share b gN a0) (hab : Derived.share_acceleration a gN b)
    (hv : Derived.circular_speeds (fun _ => a) v) (hr : Condition.pos r) :
    a = a0 ∧ v r ^ 2 = a0 * r :=
  Law.classical_limit a0 gN a b r (v r) hgN hb hab (hv r hr)

/-- **The scale goes as the square of the threshold's mean** (Sec. IV.C): with the threshold
exponential of mean `μ` (`Condition.threshold_mean`) in place of one qubit, the law keeps its form
with the scale `μ²a₀`, so the measured scale fixes `μ`.  Sources: Postulate 1 for the carriers by
amplitude; Eq. (f) and `a = g_N/b` (`Derived`); the conditions: `μ > 0` and the threshold's mean. -/
theorem scale_mean (R : Reg) (gN a b μ TN εs : ℝ) (surv : ℝ → ℝ) (hμ : Condition.pos μ)
    (hME : Condition.threshold_mean μ surv) (hb : P1.carriers_by_amplitude R b TN εs surv)
    (hf : Derived.fill_fraction R gN TN εs) (hab : Derived.share_acceleration a gN b) :
    a = gN / (1 - Real.exp (-Real.sqrt (gN / (μ ^ 2 * R.a0)))) := by
  have hb' : b = 1 - surv (Real.sqrt (gN / R.a0)) := by
    have h1 : b = 1 - surv (Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs))) := hb
    have h2 : 2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs) = gN / R.a0 := hf
    rw [h1, h2]
  exact R.law_scale_mean gN a b μ hμ surv hME hb' hab

/-- **The scale at every epoch, and `Λ` from it** (Secs. V and VI): with Jacobson's `G` and the
constant `Λ = 3/R_Λ²`, `a₀ = (1 − ln 2)√π/((ln 2)^{3/2}L) · √(c⁷/ℏG)`, a fixed fraction of the Planck
acceleration, and `Λ = 12πc³/(L²ℏG ln 2)`; the same formula with another `G'` gives twice the scale
only if `G' = G/4`; **only the product `Lℓ_c` enters `a₀`**, `a₀ = (1 − ln 2)πc²/(ln 2 · Lℓ_c)`
(Sec. IV.C, after Eq. (f)); and **`Λ` from `a₀`**, `R_Λ = (1 − ln 2)c²/(2 ln 2 a₀)` and
`Λ = 12(ln 2)²a₀²/((1 − ln 2)²c⁴)`.  The product form of `a₀` and `R_Λ` from `a₀` restate the
definition of `a₀` and take no premise.  Sources: `G` and the constant (`Derived`). -/
theorem scale (R : Reg) (G Λ : ℝ) (hJ : Derived.jacobson_G R G)
    (hdS : Derived.deSitter_horizon R G Λ) :
    (R.a0 = (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
        Real.sqrt (R.c ^ 7 / (R.ℏ * G)) ∧
      Λ = 12 * R.pi * R.c ^ 3 / (R.L ^ 2 * R.ℏ * G * R.ln2) ∧
      ∀ G' : ℝ, 0 < G' →
        (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
          Real.sqrt (R.c ^ 7 / (R.ℏ * G')) = 2 * R.a0 → G' = G / 4) ∧
    R.a0 = (1 - R.ln2) * R.pi * R.c ^ 2 / (R.ln2 * (R.L * R.ℓc)) ∧
    R.RL = (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * R.a0) ∧
    Λ = 12 * R.ln2 ^ 2 * R.a0 ^ 2 / ((1 - R.ln2) ^ 2 * R.c ^ 4) :=
  ⟨R.scale_over_time G Λ hJ ((R.deSitter G Λ).1 hdS), R.a0_depends_on_product,
    (R.Lambda_from_a0 G Λ hdS).1, (R.Lambda_from_a0 G Λ hdS).2⟩

/-! ### Sec. IV.D: the push, the zero-gravity radius, the expansion -/

/-- **Eq. (push)** (Sec. IV.D): with the constant of the solution without a mass, the field about a
mass is `g = GM/r² − c²r/R_Λ²`, the pull less the push, in cells
`a/a_c = α/(πn² ln 2) − 4π²n/L²`.  Sources: `G` and the constant (`Derived`); the condition
`r > 0`. -/
theorem push (R : Reg) (G M Λ r : ℝ) (hr : Condition.pos r) (hJ : Derived.jacobson_G R G)
    (hdS : Derived.deSitter_horizon R G Λ) :
    R.gSdS G M Λ r = G * M / r ^ 2 - R.c ^ 2 * r / R.RL ^ 2 ∧
    R.gSdS G M Λ r / R.ac = R.α M / (R.pi * R.n r ^ 2 * R.ln2) - 4 * R.pi ^ 2 * R.n r / R.L ^ 2 :=
  R.push G M Λ r hr hJ hdS

/-- **The zero-gravity radius** (Sec. IV.D): where the field vanishes, `r_z³ = GMR_Λ²/c²`, pull and
push each `c²r_z/R_Λ²`, which is below the scale `a₀` exactly when `r_z < (1 − ln 2)R_Λ/(2 ln 2)`,
so that the pull that meets the push is in the deep regime.  The last part compares the push with
the definition of `a₀` and takes no premise.  Sources: the constant `Λ = 3/R_Λ²` (`Derived`); the
conditions: `r_z > 0` and the field zero there. -/
theorem zero_gravity (R : Reg) (G M Λ rz : ℝ) (hrz : Condition.pos rz)
    (hdS : Derived.deSitter_horizon R G Λ) (hz : Condition.zero_field R G M Λ rz) :
    rz ^ 3 = G * M * R.RL ^ 2 / R.c ^ 2 ∧ G * M / rz ^ 2 = R.c ^ 2 * rz / R.RL ^ 2 ∧
    (R.c ^ 2 * rz / R.RL ^ 2 < R.a0 ↔ rz < (1 - R.ln2) * R.RL / (2 * R.ln2)) :=
  R.zero_gravity G M Λ rz hrz hdS hz

/-- **De Sitter expansion at `H_∞ = c/R_Λ`, `2π` over the lap time** (Sec. IV.D, Eq. (clock)): in
the solution without a mass the field at the distance `r` is the push alone, `g = −H_∞²r`, with
`H_∞ = c/R_Λ` and with `H_∞ = 2π/(Lt_c)`, `2π` over the lap time of a largest ring.  The paper
reads the field as the acceleration with which a free body at that distance recedes, as in an
expansion at the rate `H_∞`.  The statement gives only the field.  Sources: the constant of the
solution without a mass (`Derived`); the condition `r > 0`. -/
theorem hubble (R : Reg) (G Λ r : ℝ) (hr : Condition.pos r)
    (hdS : Derived.deSitter_horizon R G Λ) :
    R.gSdS G 0 Λ r = -((R.c / R.RL) ^ 2 * r) ∧
      R.gSdS G 0 Λ r = -((2 * R.pi / (R.L * R.tc)) ^ 2 * r) := by
  have hr' : r ≠ 0 := (show (0 : ℝ) < r from hr).ne'
  have h1 : R.gSdS G 0 Λ r = -((R.c / R.RL) ^ 2 * r) := by
    rw [R.gSdS_eq G 0 Λ r hr', (R.deSitter G Λ).1 hdS]
    ring
  exact ⟨h1, by rw [← R.hubble]; exact h1⟩

/-- **The drift of `G` with a Hubble-radius horizon** (Sec. IV.D): Eqs. (ident) and (G) tie the
cell to the horizon's radius and `G` to the square of that radius,
`G = 4πc³R_Λ²/(ℏL² ln 2)` (`Reg.G_eq`).  Were
the horizon the Hubble radius `c/H` at every time (`hH`, the rejected alternative's premise), with
`L` fixed (Postulate 1) and `c` and `ℏ` those of the units, `G ∝ R_H²` would drift at
`Ġ/G = 2H(1 + q)`, with `H = ȧ/a` and `q = −äa/ȧ²`.  Sources: `L` constant (Postulate 1); the
units; `G` from Jacobson's step with the count at every time (`Derived`); the conditions: the
scale factor with its rates, and the alternative's premise. -/
theorem G_drift (Rt : ℝ → Reg) (G : ℝ → ℝ) (hL : P1.constant_L Rt)
    (hconst : Units.si_constants Rt) (hJ : Derived.jacobson_G_in_time Rt G) (a adot : ℝ → ℝ)
    (addot t : ℝ) (hq : Condition.deceleration a adot addot t)
    (hH : Condition.hubble_horizon Rt a adot) :
    HasDerivAt G (2 * (adot t / a t) * (1 + -(addot * a t / adot t ^ 2)) * G t) t := by
  have hG : G = fun s => (Rt 0).GHubble (adot s / a s) := by
    funext s
    obtain ⟨hc, hℏ, -⟩ := hconst s
    have hpi : (Rt s).pi = (Rt 0).pi := rfl
    have hln2 : (Rt s).ln2 = (Rt 0).ln2 := rfl
    unfold Reg.GHubble
    rw [((Rt s).G_eq (G s) (hJ s)).2, hH s, hc, hℏ, hL s, hpi, hln2]
  rw [hG]
  exact (Rt 0).G_drift a adot addot t hq.1 hq.2.1 hq.2.2.1 hq.2.2.2

/-! ### Secs. IV.D and VI: constancy in time; then the first law of the horizon with `Λ` free
(Sec. IV.D) and a block's fraction as a probability (Sec. IV.A) -/

/-- **`G`, `Λ`, `GΛ` and `a₀` are constant in time** (Sec. IV.D, Eq. (Lambda)): with `L` and the
cell constant, in the SI units, `G = c³ℓ_c²/πℏ ln 2` and `Λ = 3/R_Λ²` are the same at every time,
and `GΛ = 12πc³/ℏL² ln 2` is fixed by `L` alone.  So is `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`, with
the radius constant ("`G`, `a₀`, and `Λ` are all constant").  Sources: `L` and the cell constant
(Postulate 1); the units; `G` and the constant of the solution at every time (`Derived`). -/
theorem constants_in_time (Rt : ℝ → Reg) (G Λ : ℝ → ℝ) (hL : P1.constant_L Rt)
    (hℓc : P1.constant_cell Rt) (hconst : Units.si_constants Rt)
    (hdS : Derived.deSitter_horizon_in_time Rt G Λ) (hJ : Derived.jacobson_G_in_time Rt G) :
    (∀ s, G s = G 0) ∧ (∀ s, Λ s = Λ 0) ∧
    (∀ s, G s * Λ s = 12 * (Rt 0).pi * (Rt 0).c ^ 3 / ((Rt 0).ℏ * (Rt 0).L ^ 2 * (Rt 0).ln2)) ∧
    ∀ s, (Rt s).a0 = (Rt 0).a0 := by
  refine ⟨Reg.G_constant Rt G hconst hℓc hJ, Reg.Lambda_constant Rt G Λ hL hℓc hdS,
    Reg.GLambda_constant Rt G Λ hL hconst hdS hJ, fun s => ?_⟩
  have hconst' : ∀ s, (Rt s).c = (Rt 0).c ∧ (Rt s).ℏ = (Rt 0).ℏ ∧ (Rt s).kB = (Rt 0).kB := hconst
  have hc := (hconst' s).1
  have hR : (Rt s).RL = (Rt 0).RL := Reg.horizon_constant Rt hL hℓc s
  have hln2 : (Rt s).ln2 = (Rt 0).ln2 := rfl
  unfold Reg.a0
  rw [hc, hR, hln2]

/-- **`Λ̇/Λ = −Ġ/G`** (Sec. VI): with `GΛ` constant, the rates of change of `G` and `Λ` are
opposite, so the lunar bound on `Ġ/G` bounds `Λ̇/Λ`.  Sources: `L` constant (Postulate 1); the
units; `G` and the constant of the solution at every time (`Derived`); the condition: the rates of
`G` and `Λ` at `t`, both nonzero. -/
theorem lambda_rate (Rt : ℝ → Reg) (G Λ : ℝ → ℝ) (hL : P1.constant_L Rt)
    (hconst : Units.si_constants Rt) (hdS : Derived.deSitter_horizon_in_time Rt G Λ)
    (hJ : Derived.jacobson_G_in_time Rt G) (G' Λ' t : ℝ)
    (hrates : Condition.rates_at G Λ G' Λ' t) : Λ' / Λ t = -(G' / G t) :=
  Reg.Lambda_rate_in_time Rt G Λ hL hconst hdS hJ G' Λ' t hrates.1 hrates.2.1 hrates.2.2.1
    hrates.2.2.2

/-- **The bound on the equation of state** (Sec. VI): a component whose density's rate of change
is bounded by `b` has `|1 + w| ≤ b/3H`, since `ρ̇/ρ = −3H(1 + w)` by its first law.  Sources: the
first law for a component (thermodynamics); the conditions: the component in the expanding scale
factor, and the bound. -/
theorem w_bound (ρ a : ℝ → ℝ) (ρdot adot w b t : ℝ) (hc : Condition.component ρ a ρdot adot t)
    (first_law : Thermo.first_law_component ρ a w t) (hb : Condition.drift_bound ρ ρdot t b) :
    |1 + w| ≤ b / (3 * (adot / a t)) :=
  Reg.w_bound ρ a ρdot adot w b t hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 first_law hb

/-- **The first law of the cosmological horizon with `Λ` free, and the Clausius relation exactly
when `Λ` does not change** (Sec. IV.D): along the family of bodies at rest whose mass grows, with
the horizon thermal at its period, `d(Mc²) = −T dS + V dP` with `S = η₀·4πr²`, `V = 4πr³/3` and
`P = −Λc⁴/8πG`; so `d(Mc²) = −T dS`, the Clausius relation, holds exactly when `dΛ = 0`.  Sources:
the horizon thermal (thermodynamics); Jacobson's `G` for the density (`Derived`); the conditions:
the family, `s` inside it, `η₀ > 0`. -/
theorem first_law_extended (R : Reg) (G η₀ : ℝ) (M Λ r T : ℝ → ℝ) (s₁ : ℝ)
    (hη₀ : Condition.pos η₀) (hJ : Derived.jacobson_G_density R G η₀)
    (hfam : Condition.body_family R G M Λ r s₁)
    (I1 : Thermo.horizon_thermal_family R G M Λ r T s₁) (s : ℝ)
    (hs : Condition.inside_family s s₁) :
    deriv (fun t => M t * R.c ^ 2) s = -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s
        + 4 * R.pi * r s ^ 3 / 3 * deriv (fun t => -(Λ t) * R.c ^ 4 / (8 * R.pi * G)) s ∧
    (deriv (fun t => M t * R.c ^ 2) s = -(T s) * deriv (fun t => η₀ * (4 * R.pi * r t ^ 2)) s ↔
      deriv Λ s = 0) := by
  obtain ⟨-, -, hfam'⟩ := hfam
  obtain ⟨hM, hΛ, hr, hpos, -, hg⟩ := hfam' s hs
  have hhor : ∀ᶠ t in nhds s, R.fSdS G (M t) (Λ t) (r t) = 0 := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact (hfam' t ht).2.2.2.2.1
  exact ⟨R.first_law_extended G η₀ hη₀ hJ hM hΛ hr hpos hg hhor (I1 s hs),
    R.clausius_iff G η₀ hη₀ hJ hM hΛ hr hpos hg hhor (I1 s hs)⟩

/-- **A block's fraction is a conditional probability** (Sec. IV.A: "The fraction of 1s on a block
is the probability of the outcome 1 given the block's joint outcome").  With each cell's bit one
possible outcome of the qubit's measurement, the bits alike (`halike`), the probability that the
outcome is `1`, given that it is the bit of a cell of the block `B` (`Capacity.condProb`), is the
fraction of 1s on `B`.  The ceilings and `one_cell_block` do not take the equal weights: they take
only that a joint outcome that occurs is the outcome at a position
(`P1.outcomes_at_positions`).  Sources: Postulate 1's bits as the possible outcomes, alike, on
the ring of one string. -/
theorem block_fraction {Cell : Type*} [Fintype Cell] (read : Cell → ℝ)
    (halike : P1.ring_bits_alike read) (b : Cell → Bool) (B : Finset Cell) :
    Capacity.condProb read b B = Capacity.frac b B :=
  Capacity.block_fraction_read read halike b B

/-! ### Sec. IV.E: the thermal distribution of a free string -/

/-- **The Gibbs distribution has the most entropy** (Sec. IV.E; the Data availability): of all
distributions on a finite set of distinguishable configurations with the mean energy of the Gibbs
distribution at `β`, the Gibbs distribution has the most entropy; and **a free string's is
`1/2, 1/2`**: its two senses have one energy (the tick multiplies both by one factor, and the
energy of a string of one sense is the energy of its factor, `Qubit.Tick.energy_eq`), so the
Gibbs distribution on them is `1/2, 1/2` at every temperature.  The first part is Gibbs'
inequality under the conditions, mathematics that takes no premise, and the second part takes the
tick.  Sources: Sec. II's sentence on the tick of a string of one sense (Postulates 1 and 2; the
field `hsense` of `Tick`); the conditions: `P` a distribution with that mean energy. -/
theorem gibbs {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → ℝ) (β : ℝ) (P : Ω → ℝ)
    (hP : Condition.distribution P) (hmean : Condition.same_mean E β P)
    (T : Qubit.Tick L) (En : ℂ → ℝ) (β' : ℝ) :
    Entropy.shannon P ≤ Entropy.shannon (Entropy.gibbs E β) ∧
    ∀ b, Entropy.gibbs (T.energy En) β' b = 1 / 2 :=
  ⟨Entropy.shannon_le_shannon_gibbs E β P hP.1 hP.2 hmean,
    fun b => Entropy.gibbs_two_equal (T.energy En) β' (T.energy_eq En) b⟩

/-! ### Sec. II: the count of a sphere's strings and the observer's own rings -/

open scoped Quaternion in
/-- **The strings a sphere holds, Eq. (N)** (Sec. II): with every largest ring a closed
spacelike geodesic of de Sitter space of length `Lℓ_c`, the constant is `Λ = 3/R_Λ²`, the rings
draw as great circles of the three-sphere, and the sphere of the drawing about any point, at the
distance `s` with the areal radius `r`, holds on average over the rotations of the drawing, with
any weighting that prefers no rotation, `N_s(r)(1 − 2/L + 4/L²)` strings, `N_s(r) = (L²/4)(r/R_Λ)²`.
Sources: Postulate 2's last sentence with Sec. II's largest ring (the rings as geodesics);
Postulate 1's first sentence applied to the count (no rotation of the drawing preferred);
Postulate 2's fourth clause, which gives `4 ≤ L`; the conditions `R.L = L` and the sphere of the
drawing. -/
theorem sphere_strings (H : Horizon L) (R : Reg) (hRL : Condition.same_L R L)
    (ν : MeasureTheory.Measure (Metric.sphere (0 : ℍ) 1)) (hν : P1.no_rotation_preferred ν)
    {Λ : ℝ} (γ : H.Loop → Geodesic.Curve ℝ ℍ) (hrings : P2.rings_geodesics H R Λ γ)
    {s r : ℝ} (hsph : Condition.drawn_sphere R s r) (ξ₀ : {q : ℍ // q ∈ Metric.sphere (0 : ℍ) 1}) :
    0 < Λ ∧ Λ = 3 / R.RL ^ 2 ∧
    ∃ D : Crossing.Drawing H.Loop ℍ R.RL,
      (∀ l, Crossing.greatCircle (D.a l) (D.b l) = Set.range (fun t => ((γ l).pos t).2)) ∧
      ∫ q, ((D.rotate (Center.leftRot q)).strings (R.RL • (ξ₀ : ℍ)) s : ℝ) ∂ν
        = R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  have := hν.1
  have := hν.invariant
  obtain ⟨hΛ, hΛeq, D, hD, -⟩ := Bridge.sphere_strings_deSitter H R H.four_le hRL
    MeasureTheory.Measure.addHaar Quaternion.finrank_eq_four γ (fun l => (hrings l).1)
    (fun l => (hrings l).2.1) (fun l => (hrings l).2.2.1) (fun l => (hrings l).2.2.2) hsph.1
    hsph.2.1 hsph.2.2.1
  refine ⟨hΛ, hΛeq, D, hD, ?_⟩
  rw [Weighting.eq_toSphere_of_invariant MeasureTheory.Measure.addHaar ν,
    Weighting.integral_normalized]
  exact Center.sphere_strings_centered MeasureTheory.Measure.addHaar H R H.four_le hRL D hsph.1
    hsph.2.1 hsph.2.2.1 ξ₀

open scoped Quaternion in
/-- **The strings of a sphere that an observer counts** (Sec. II, after Eq. (N)): the
count of `sphere_strings` is the average over the drawing's rotations.  For an observer at rest at
the cell `B`, the `L/2` rings through his cell pass through his place (Sec. II),
so they are not turned with the rest of the drawing; the other rings, whose position relative to
his place is no part of the state, are turned about the center with a weighting that prefers no
rotation, as the whole drawing is, and keep the average.  His count is the average
`N_s(r)(1 − 2/L + 4/L²)`, plus the number of his rings that cross the sphere, less `(L/2)(r/R_Λ)²`
(`Center.observer_strings_mean`): each of his rings counts at most once, whereas the average gives
it the weight `(r/R_Λ)²`, so his count exceeds the average by at most `(L/2)(1 − r²/R_Λ²)`.
Sources: Postulate 1's first sentence applied to the count (no rotation preferred); Postulate 2's
fourth clause, which gives `4 ≤ L`; the conditions `R.L = L` and the sphere of the drawing. -/
theorem observer_count (H : Horizon L) (R : Reg) (hRL : Condition.same_L R L)
    (ν : MeasureTheory.Measure (Metric.sphere (0 : ℍ) 1)) (hν : P1.no_rotation_preferred ν)
    (D : Crossing.Drawing H.Loop ℍ R.RL) (B : H.Cell) {s r : ℝ}
    (hsph : Condition.drawn_sphere R s r) (ξ₀ : {q : ℍ // q ∈ Metric.sphere (0 : ℍ) 1}) :
    ((D.restrict (· ∈ H.through B)).strings (R.RL • (ξ₀ : ℍ)) s : ℝ) +
        ∫ q, (((D.restrict (· ∉ H.through B)).rotate (Center.leftRot q)).strings
          (R.RL • (ξ₀ : ℍ)) s : ℝ) ∂ν =
      R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) +
        (D.restrict (· ∈ H.through B)).strings (R.RL • (ξ₀ : ℍ)) s - R.L / 2 * (r / R.RL) ^ 2 ∧
    ((D.restrict (· ∈ H.through B)).strings (R.RL • (ξ₀ : ℍ)) s : ℝ) +
        ∫ q, (((D.restrict (· ∉ H.through B)).rotate (Center.leftRot q)).strings
          (R.RL • (ξ₀ : ℍ)) s : ℝ) ∂ν ≤
      R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) + R.L / 2 * (1 - r ^ 2 / R.RL ^ 2) := by
  have := hν.1
  have := hν.invariant
  rw [Weighting.eq_toSphere_of_invariant MeasureTheory.Measure.addHaar ν,
    Weighting.integral_normalized]
  obtain ⟨h1, h2⟩ := Center.observer_strings_mean MeasureTheory.Measure.addHaar H H.four_le D B
    R.RL_pos hsph.1 hsph.2.1 hsph.2.2.1 ξ₀
  rw [Center.sphere_strings_centered MeasureTheory.Measure.addHaar H R H.four_le hRL D hsph.1
    hsph.2.1 hsph.2.2.1 ξ₀] at h1
  have hRL' : R.L = L := hRL
  rw [← hRL'] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h1, div_pow]
  linarith

open scoped Quaternion in
/-- **The observer's own rings on a sphere** (Sec. II, after Eq. (N)): the count of an observer at
rest exceeds the average `N_s(r)(1 − 2/L + 4/L²)` of `sphere_strings` by at most
`(L/2)(1 − r²/R_Λ²)` (`observer_count`), which is at most the fraction `R_Λℓ_c/πr²` of `N_s(r)`
(the arithmetic of `Reg.observer_rings`; `1.3×10⁻⁹` at `r = 1 m`,
`Numerics.observer_fraction_1m`).  The statement is the bound that results: his count is at most
`N_s(r)(1 − 2/L + 4/L²) + N_s(r) R_Λℓ_c/πr²`.  Sources: those of `observer_count`: Postulate 1's
first sentence applied to the count (no rotation preferred); Postulate 2's fourth clause, which
gives `4 ≤ L`; the conditions `R.L = L` and the sphere of the drawing. -/
theorem observer_rings (H : Horizon L) (R : Reg) (hRL : Condition.same_L R L)
    (ν : MeasureTheory.Measure (Metric.sphere (0 : ℍ) 1)) (hν : P1.no_rotation_preferred ν)
    (D : Crossing.Drawing H.Loop ℍ R.RL) (B : H.Cell) {s r : ℝ}
    (hsph : Condition.drawn_sphere R s r) (ξ₀ : {q : ℍ // q ∈ Metric.sphere (0 : ℍ) 1}) :
    ((D.restrict (· ∈ H.through B)).strings (R.RL • (ξ₀ : ℍ)) s : ℝ) +
        ∫ q, (((D.restrict (· ∉ H.through B)).rotate (Center.leftRot q)).strings
          (R.RL • (ξ₀ : ℍ)) s : ℝ) ∂ν ≤
      R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) + R.RL * R.ℓc / (R.pi * r ^ 2) * R.Ns r := by
  have hcount := (observer_count H R hRL ν hν D B hsph ξ₀).2
  obtain ⟨hs0, hs2, hr2, hr0⟩ := hsph
  have hRLp := R.RL_pos
  -- the areal radius is positive: `r² = s²(1 − s²/4R_Λ²) ≥ s²/2`
  have hsq : 0 < s ^ 2 := by positivity
  have h4 : s ^ 4 / (4 * R.RL ^ 2) ≤ s ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hs2 hsq.le]
  have hr2pos : 0 < r ^ 2 := by rw [hr2]; linarith
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hr2pos
      norm_num at hr2pos
    · exact h
  have hNs : 0 < R.Ns r := by
    reg_facts R
    rw [R.bulk_counts r]; unfold Reg.n; positivity
  have hfrac := (R.observer_rings r hrpos).2.1
  rw [div_le_iff₀ hNs] at hfrac
  linarith

open scoped Quaternion in
/-- **The sphere of the drawing is a round sphere of areal radius `r`** (Sec. II: "a sphere of
areal radius `r`, the `r` for which the sphere's area is `4πr²`").  With every largest ring a
closed spacelike geodesic of de Sitter space with the constant `Λ`, of length `Lℓ_c` (`hrings`),
the constant is `Λ = 3/R_Λ²` (as in `sphere_strings`), so the space at an instant, the points `x`
with `‖x‖² = 3/Λ`, is the three-sphere of radius `R_Λ` on which the rings are drawn.  About a
point `p` of it the points of space at the distance `s` from `p` are the points `κp + y` with `y`
orthogonal to `p` and `‖y‖ = r`, `κ = 1 − s²/2R_Λ²`, a round sphere of radius `r` in the
three-dimensional hyperplane through `κp` orthogonal to `p`, whose area is `4πr²`, the area of a
round sphere, which the files do not compute (`Crossing.sphere_round`).  The premise gives the
radius of the space, `√(3/Λ) = R_Λ`, and the description of the sphere in it is geometry that
takes no premise.  Sources: Postulate 2's last sentence with Sec. II's largest ring (the rings as
geodesics); Postulate 2's fourth clause, which gives `4 ≤ L`; the conditions: `R.L = L`, the
sphere of the drawing, and `p` on the three-sphere of radius `R_Λ`. -/
theorem sphere_areal_radius (H : Horizon L) (R : Reg) (hRL : Condition.same_L R L) {Λ : ℝ}
    (γ : H.Loop → Geodesic.Curve ℝ ℍ) (hrings : P2.rings_geodesics H R Λ γ) {s r : ℝ}
    (hsph : Condition.drawn_sphere R s r) (p : ℍ) (hp : Condition.on_three_sphere R p) :
    {x : ℍ | ‖x‖ = Real.sqrt (3 / Λ) ∧ ‖x - p‖ = s} =
      {x | ∃ y : ℍ, inner ℝ y p = 0 ∧ ‖y‖ = r ∧ x = (1 - s ^ 2 / (2 * R.RL ^ 2)) • p + y} := by
  obtain ⟨-, hΛeq, -⟩ := Bridge.sphere_strings_deSitter H R H.four_le hRL
    MeasureTheory.Measure.addHaar Quaternion.finrank_eq_four γ (fun l => (hrings l).1)
    (fun l => (hrings l).2.1) (fun l => (hrings l).2.2.1) (fun l => (hrings l).2.2.2) hsph.1
    hsph.2.1 hsph.2.2.1
  have hRLp := R.RL_pos
  have e : Real.sqrt (3 / Λ) = R.RL := by
    rw [hΛeq, show 3 / (3 / R.RL ^ 2) = R.RL ^ 2 by field_simp, Real.sqrt_sq hRLp.le]
  rw [e]
  exact Crossing.sphere_round R.RL_pos.ne' hp hsph.1.le hsph.2.2.2 hsph.2.2.1

/-! ## The sentences that the files had not stated (v18-65)

The results below state sentences of the paper that the files took in words up to v18-64: the
three-page site of the derivation marked them "No Lean statement" or "Not stated in Lean".  Each
takes its premises as the results above do. -/

/-! ### Sec. II: a ring's string, the lap, the two senses, the hidden phase, the bit kept -/

/-- **Every ring carries exactly one string, of `L` bits** (Sec. II: "By the definition of a
cell, every ring carries exactly one string: each of its cells holds one bit of it, and those bits
form a string of Postulate 1").  A cell holds one bit of each ring through it, so the cells hold a
bit for every pair of a cell and a ring through it.  These bits correspond one to one to a family
of strings, one for each ring (`Horizon.ringStrings`), and the string of a ring has one bit on
each of the ring's `L` cells.  The statement is of the register alone and names no state of the
strings, so it holds in every state, with a mass, which is a state of strings, or without one
(Sec. IV.A: "Nor does a mass shorten the rings").  Sources: Sec. II's definitions of a cell and
of a largest ring, as the structure `Horizon` carries them. -/
theorem ring_one_string (H : Horizon L) :
    Nonempty (({p : H.Cell × H.Loop // p.1 ∈ H.cells p.2} → Bool) ≃
      (∀ l : H.Loop, {x // x ∈ H.cells l} → Bool)) ∧
    ∀ l : H.Loop, Fintype.card {x // x ∈ H.cells l} = L :=
  ⟨⟨H.ringStrings⟩, H.card_ring⟩

/-- **`L` ticks of the shift make one lap** (Sec. II: "`L` ticks of the shift make one lap of a
largest ring: the lap time is `Lt_c`").  The shift moves a bit one cell along its ring per tick
(Postulate 1), one position on.  A bit at the cell `x` of the ring `l` is back at the position of
`x` after `L` ticks and after no smaller number of ticks.  The lap time is then `L` ticks,
`Lt_c` (`Reg.lap_time` gives it as `2πR_Λ/c`).  Sources: Postulate 1's shift and "the string's
cyclic position on its ring", as the structure `Positions` carries them. -/
theorem lap (H : Horizon L) (P : H.Positions) (l : H.Loop) (x : H.Cell) :
    Horizon.Positions.shift^[L] (P.pos l x) = P.pos l x ∧
      ∀ k, 0 < k → k < L → Horizon.Positions.shift^[k] (P.pos l x) ≠ P.pos l x :=
  P.lap l x

/-- **A translation along a ring can go two ways** (Sec. II: "The shift (Postulate 1) is a
translation along the ring, and a translation along a ring can go two ways, with the ring or
against it: the two senses").  A cell `y` is one step from a cell `x` along the ring `l` exactly
when its position is one ahead of the position of `x` or one behind it, and these are two
different positions.  Sources: Postulate 1's cyclic position (the structure `Positions`) and
Postulate 2's fourth clause, which gives `4 ≤ L`. -/
theorem two_senses (H : Horizon L) (P : H.Positions) (l : H.Loop) (x y : H.Cell) :
    (P.ringDist l x y = 1 ↔ P.pos l y = P.pos l x + 1 ∨ P.pos l y = P.pos l x - 1) ∧
      P.pos l x + 1 ≠ P.pos l x - 1 :=
  P.two_senses H.four_le l x y

/-- **The sense is a property of the string's state** (Sec. II: "No law fixes the sense, since
none depends on the direction in which a ring passes through a cell (Postulate 2), so the sense is
a property of the string's state, and reading it is a measurement with two values").  `obeys σ`
says that the state `σ` of a string obeys a law, and `sense σ` is the sense of the shift in that
state, a function of the state.  Reversing the direction of the ring exchanges the two senses
(`hrev`), and the law says of the reversed state what it says of the state (`hdir`).  Then under
a law that some state obeys (`h₀`), either sense occurs in a state that obeys it: the law does
not fix the sense, the state does, and the sense takes both of its two values.  Sources:
Postulate 2's sentence on directions; the conditions: the reversal exchanges the senses, and some
state obeys the law. -/
theorem sense_of_state {State : Type*} (obeys : State → Prop) (sense : State → Bool)
    (rev : State → State) (σ₀ : State) (hdir : P2.direction_free obeys rev)
    (hrev : Condition.reverses sense rev) (h₀ : Condition.obeys_law obeys σ₀) :
    ∀ v : Bool, ∃ σ, obeys σ ∧ sense σ = v :=
  fun v => Strings.sense_of_state obeys sense rev hrev hdir σ₀ h₀ v

/-- **No law reads a free tick** (Sec. II: "So no bit moves and no free tick changes the relative
phase: what changes from tick to tick is the global phase", with Postulate 1's "The global phase
of a state is hidden: no law depends on its value").  The free tick multiplies every state of a
string by one factor, a phase (`Qubit.Tick.phase_unique`, `Qubit.Tick.norm_scalar`), so a law that
does not depend on the global phase (`hhidden`) reads the same off a state after the tick as
before it.  Sources: Postulate 1's sentence on the global phase; Sec. II's sentence on the tick of
a string of one sense (the structure `Tick`). -/
theorem free_tick_hidden {α : Type*} (T : Qubit.Tick L) (law : Qubit.Vec → α)
    (hhidden : P1.phase_hidden law) (v : Qubit.Vec) : law (Matrix.mulVec T.U v) = law v := by
  obtain ⟨γ, hγ⟩ := (Complex.norm_eq_one_iff T.scalar).1 T.norm_scalar
  have h : Matrix.mulVec T.U v = Complex.exp ((γ : ℂ) * Complex.I) • v := by
    rw [T.scalar_spec, Matrix.smul_mulVec, Matrix.one_mulVec, hγ]
  rw [h]
  exact hhidden γ v

/-- **A string keeps its bit** (Sec. II: "Every string has kept its bit since: an interaction
changes its sense without making either likelier, and no law favors a sense (Postulate 2)").
The string is in the thermal state of a bath at any inverse temperature `β` (`T.state β En`),
which gives either sense the probability `1/2`: "Any bath, not only the horizon, weights the two
senses equally, since their energy is the same at every temperature".  The hot early universe
was such a bath, an observation.  `flip s` is the probability that an interaction changes the
sense `s`, with `true` the sense with the ring.  It is a law of the string, and reversing the
direction of the ring exchanges the two senses, so it is the same for both (`hflip`).  After the
interaction either sense still has the probability `1/2`, so the string still holds one bit.
Sources: Postulate 2's sentence on directions, for the law of the interaction; Sec. II's
sentence on the tick of a string of one sense (the structure `Tick`). -/
theorem bit_kept (T : Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (flip : Bool → ℝ)
    (hflip : P2.direction_free flip (fun s => !s)) :
    Qubit.bornProb (T.state β En) Qubit.e₁ * (1 - flip true)
        + Qubit.bornProb (T.state β En) Qubit.e₂ * flip false = 1 / 2 ∧
      Qubit.bornProb (T.state β En) Qubit.e₂ * (1 - flip false)
        + Qubit.bornProb (T.state β En) Qubit.e₁ * flip true = 1 / 2 := by
  have he₂ : star Qubit.e₂ ⬝ᵥ Qubit.e₂ = 1 := by
    simp [Qubit.e₂, dotProduct, Fin.sum_univ_two]
  have h₂ : Qubit.bornProb (T.state β En) Qubit.e₂ = 1 / 2 := by
    rw [T.state_eq]
    exact Qubit.bornProb_half Qubit.e₂ he₂
  have hf : flip true = flip false := hflip false
  exact Strings.bit_kept
    (fun s => if s then Qubit.bornProb (T.state β En) Qubit.e₁
      else Qubit.bornProb (T.state β En) Qubit.e₂) flip
    ⟨T.bornProb_state β En, h₂⟩ hf

/-! ### Sec. IV.A: the pairing of strings, the overlap and the return above the ceiling -/

/-- **The probability of a joint outcome is the share of the positions that show it**
(Sec. IV.A: "A joint measurement is one measurement, so its possible outcomes are the `L`
positions", and "no pairing of `L` positions shows more than `L` joint outcomes, so none shows
every joint outcome of a state that has more than `L` of them").  `e x` is the joint outcome at
the position `x`, the pairing, and `read x` the probability that the measurement's outcome is
the position `x`.  Each position is one possible outcome among the ring's (`halike`), and the
probability of a set of positions is the sum of theirs, so the probability that the measurement
shows the joint outcome `k` is the share of the positions that show it, `Pairing.freq e k`, a
multiple of one over the number of the positions, with a multiplier of at most `L`.  At most `L` joint outcomes have a frequency above
zero, and where more than `L` joint outcomes occur in a state, with `p k > 0`, the pairing gives
one of them the frequency zero.  The last two parts are counting and take only that no ring has
more than `L` cells (`hL`).  Sources: Postulate 1's bits as the possible outcomes, alike, on the
ring of one string, and no ring with more than `L` cells. -/
theorem joint_frequency {Cell K : Type*} [Fintype Cell] [Fintype K] [DecidableEq K] (L : ℕ)
    (read : Cell → ℝ) (e : Cell → K) (halike : P1.ring_bits_alike read)
    (hL : P1.ring_cells Cell L) :
    (∀ k, ∑ x ∈ univ.filter (fun x => e x = k), read x = Pairing.freq e k ∧
      ∃ n : ℕ, n ≤ L ∧ Pairing.freq e k = n / Fintype.card Cell) ∧
    (univ.filter (fun k => 0 < Pairing.freq e k)).card ≤ L ∧
    ∀ p : K → ℝ, L < (univ.filter (fun k => 0 < p k)).card →
      ∃ k, 0 < p k ∧ Pairing.freq e k = 0 := by
  have hL' : Fintype.card Cell ≤ L := hL
  refine ⟨fun k => ⟨Capacity.share_read read halike _, ?_⟩,
    (Pairing.shown_le_cells e).trans hL',
    fun p hp => Pairing.pairing_misses p (lt_of_le_of_lt hL' hp) e⟩
  obtain ⟨n, hn, hf⟩ := Pairing.freq_multiple e k
  exact ⟨n, hn.trans hL', hf⟩

/-- **Two qubits prepared apart: strings exact, pairing approximate** (Sec. IV.A: "Most product
states are not held exactly even at small `N`: two qubits prepared apart, with the fractions
`m₁/L` and `m₂/L`, have the joint frequency `m₁m₂/L²` for the outcome `(1,1)`, a multiple of `1/L`
only when `L` divides `m₁m₂`.  Postulate 1 fixes each string exactly, its fraction and position,
and the pairing only up to its `L` positions; such a state is held with its strings exact and its
pairing approximate").  `A` and `B` are the cells where the two strings read `1`, `m₁` and `m₂`
in number, each string fixed, and `L` here is the number of the ring's cells.  A pairing is a
one-to-one map `π` of the positions: the cell `x` of the first string is read with the cell `π x`
of the second.  With the bits alike (`halike`), in every pairing each string shows `1` with the
probability of its own fraction, exactly, and the outcome `(1,1)` has the probability of the
share of the positions where both read `1`, which is the product of the two fractions only if
`L` divides `m₁m₂`.  Some pairing brings that share within `1/L`, one cell, of the product, and
to the product where `L` divides `m₁m₂`.  Which pairing the register holds the postulates do not
say: two pairings of the same strings can differ (`Pairing.pairing_not_fixed`).  For most
fractions `L` does not divide the product (`Pairing.most_products_not_shown`).  Sources:
Postulate 1's bits as the possible outcomes, alike, on the ring of one string. -/
theorem product_state {Cell : Type*} [Fintype Cell] [DecidableEq Cell] [Nonempty Cell]
    (read : Cell → ℝ) (A B : Finset Cell) (halike : P1.ring_bits_alike read) :
    (∀ π : Equiv.Perm Cell,
      (∑ x ∈ A, read x = A.card / Fintype.card Cell ∧
        ∑ x ∈ univ.filter (fun x => π x ∈ B), read x = B.card / Fintype.card Cell) ∧
      ∑ x ∈ A.filter (fun x => π x ∈ B), read x
        = ((A.filter (fun x => π x ∈ B)).card : ℝ) / Fintype.card Cell ∧
      (∑ x ∈ A.filter (fun x => π x ∈ B), read x
          = ((A.card : ℝ) / Fintype.card Cell) * (B.card / Fintype.card Cell) →
        Fintype.card Cell ∣ A.card * B.card)) ∧
    ∃ π : Equiv.Perm Cell,
      |∑ x ∈ A.filter (fun x => π x ∈ B), read x
        - ((A.card : ℝ) / Fintype.card Cell) * (B.card / Fintype.card Cell)|
          < 1 / Fintype.card Cell ∧
      (Fintype.card Cell ∣ A.card * B.card → ∑ x ∈ A.filter (fun x => π x ∈ B), read x
        = ((A.card : ℝ) / Fintype.card Cell) * (B.card / Fintype.card Cell)) := by
  have hL : 0 < Fintype.card Cell := Fintype.card_pos
  have hshare := Capacity.share_read read halike
  refine ⟨fun π => ⟨⟨hshare A, ?_⟩, hshare _, fun h => ?_⟩, ?_⟩
  · rw [hshare, Pairing.card_paired B π]
  · rw [hshare] at h
    exact Pairing.product_not_shown A B π hL h
  · obtain ⟨π, hnear, hexact⟩ := Pairing.pairing_within_one_cell A B hL
    exact ⟨π, by rw [hshare]; exact hnear, fun hdvd => by rw [hshare]; exact hexact hdvd⟩

/-- **`N` exact strings read in step** (Sec. IV.A: "The register therefore holds, at any `N`,
something definite in kind: `N` exact strings read in step, in some pairing, with a phase on each
block").  `bits i x` is the bit of the string `i` at the position `x`, and the pairing is the
bits of the `N` strings at each position (`Pairing.inStep`).  With the bits alike (`halike`), the
probability of a joint outcome `σ` is the share of the positions that show it, a multiple of one
over the number of the positions; these probabilities sum to one; and on each string the outcome
`1` has the probability of the string's own fraction of 1s, in the pairing and by the string
alone, so every string is exact whatever the pairing.  The phase on each block is one of the
block's cyclic positions (`Pairing.BlockPhase`); where the frequencies are those of a state, the
frequencies and the blocks' phases give the state (`Pairing.state_of_strings`).  Sources:
Postulate 1's bits as the possible outcomes, alike, on the ring of one string. -/
theorem strings_in_step {Cell : Type*} [Fintype Cell] [Nonempty Cell] (N : ℕ)
    (read : Cell → ℝ) (bits : Fin N → Cell → Bool) (halike : P1.ring_bits_alike read) :
    (∀ σ, ∑ x ∈ univ.filter (fun x => Pairing.inStep bits x = σ), read x
        = Pairing.freq (Pairing.inStep bits) σ ∧
      ∃ n : ℕ, Pairing.freq (Pairing.inStep bits) σ = n / Fintype.card Cell) ∧
    ∑ σ, Pairing.freq (Pairing.inStep bits) σ = 1 ∧
    ∀ i, ∑ σ ∈ univ.filter (fun σ : Fin N → Bool => σ i = true),
        Pairing.freq (Pairing.inStep bits) σ = Capacity.frac (bits i) univ ∧
      ∑ x ∈ univ.filter (fun x => bits i x = true), read x = Capacity.frac (bits i) univ := by
  have hL : 0 < Fintype.card Cell := Fintype.card_pos
  obtain ⟨hmult, hsum, hmarg⟩ := Pairing.strings_in_step bits hL
  refine ⟨fun σ => ⟨Capacity.share_read read halike _, hmult σ⟩, hsum, fun i => ⟨hmarg i, ?_⟩⟩
  rw [Capacity.share_read read halike]
  unfold Capacity.frac
  rw [card_univ]

/-- **The overlap above the ceiling** (Sec. IV.A: "In the random state the last qubit has a
different conditional state, a superposition, for each joint outcome of the others, whatever the
order of the strings, and above `log₂L` its string has too few cells to hold them all", and
"What the register holds instead gives the missing outcomes probability zero, so its overlap with
the random state is at most the probability that the random state gives the outcomes that
remain").  `held ω` is the amplitude that the state the register holds gives the joint outcome
`ω = (k, v)`, the other qubits showing `k` and the last qubit the bit `v`, and `ψ` is the state
that the circuit calls for.  `χ k` stands for the conditional state that `ψ` gives the last
qubit given `k` (`hχ`).  `e x` is the joint outcome of the other qubits at the position `x`, and
`b x` is the last qubit's bit there.  The block of `e x` is taken to hold the conditional state
`χ (e x)` that `ψ` gives its joint outcome, as the paper's sentence has the string hold the
random state's conditional states: the labels are those of `ψ`, not of `held`.  The premise is
Postulate 1's possible outcomes for the measurement of the last qubit given the others, its
conditioned outcomes (`hout`): a conditional state that occurs with a bit in what the register
holds, the probabilities `|held (k, v)|²` of the joint outcomes `k` that give the state summing
to more than zero, has that bit at a cell of a block that holds the state.  The results on codes
take the premise so, with the conditional states of the state that the circuit calls for and the
probabilities of the state that the register holds.  A conditioned outcome is not a joint
outcome: several joint outcomes may give the last qubit one conditional state, and a product
state gives it one for all that occur (`Conditional.product_one_state`).  Where every joint
outcome has a conditional state of its own in `ψ` (`hdiff`), a conditioned outcome is one joint
outcome, and the premise is then that a joint outcome which occurs in what the register holds is
the outcome at a position.  So the outcomes that occur lie in a set `S` of at most `L`, since
the ring has at most `L` cells (`hL`): `held` vanishes outside `S`, and
`|⟨ψ|held⟩|² ≤ ∑_{ω ∈ S} |ψ_ω|²`.  The Porter–Thomas distribution, cited in the paper, gives the
right side its numbers for a random state (`Numerics.porter_thomas_bound`).  A product state in
which two or more joint outcomes of the other qubits occur does not meet `hdiff`, and the bound
does not follow for it: with two cells for each label its last string can meet the premise
whatever the register holds (`Conditional.room_holds`).  Sources: Postulate 1's bits as the
possible outcomes, for the last qubit's conditioned outcomes, and no ring with more than `L`
cells; the conditions: `χ` stands for the conditional states of `ψ`, they all differ, and `held`
is a state, its probabilities summing to one. -/
theorem overlap_bound {Cell K T : Type*} [Fintype Cell] [Fintype K] [DecidableEq K]
    [DecidableEq T] (L : ℕ) (held ψ : K × Bool → ℂ) (χ : K → T) (e : Cell → K)
    (b : Cell → Bool) (hL : P1.ring_cells Cell L)
    (hout : P1.outcomes_at_positions
      (fun s v => ∑ k ∈ univ.filter (fun k => χ k = s), ‖held (k, v)‖ ^ 2)
      (fun x => χ (e x)) b)
    (hχ : Condition.state_given ψ χ) (hdiff : Condition.all_differ ψ)
    (hnorm : Condition.normalized held) :
    ∃ S : Finset (K × Bool), S.card ≤ L ∧ (∀ ω, ω ∉ S → held ω = 0) ∧
      ‖∑ ω, (starRingEnd ℂ) (ψ ω) * held ω‖ ^ 2 ≤ ∑ ω ∈ S, ‖ψ ω‖ ^ 2 := by
  have hL' : Fintype.card Cell ≤ L := hL
  have hvanish : ∀ ω, ω ∉ univ.image (fun x => (e x, b x)) → held ω = 0 := by
    rintro ⟨k, v⟩ hω
    by_contra hne
    have hpos : 0 < ∑ j ∈ univ.filter (fun j => χ j = χ k), ‖held (j, v)‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hne) 2)
        (single_le_sum (f := fun j => ‖held (j, v)‖ ^ 2) (fun j _ => sq_nonneg _)
          (mem_filter.2 ⟨mem_univ k, rfl⟩))
    obtain ⟨x, hx, hbx⟩ := hout (χ k) v hpos
    have hk : e x = k := hdiff (e x) k ((hχ (e x) k).1 hx)
    exact hω (mem_image.2 ⟨x, mem_univ x, by rw [hk, hbx]⟩)
  exact ⟨univ.image (fun x => (e x, b x)),
    (card_image_le.trans (by rw [card_univ])).trans hL', hvanish,
    Pairing.overlap_le held ψ _ hvanish (le_of_eq hnorm)⟩

/-- **The return above the ceiling, and where the register holds the state** (Sec. IV.A: "A
circuit acts on what the register holds as it acts on any state, an input of Sec. III, so the
state returns with at most that fraction of the gate fidelity"; "In quantum mechanics the state
returns to the initial one with the gate fidelity, the probability of a run without error"; and
"Where the register holds such a state, it returns as in quantum mechanics").  The test of
Sec. IV.A runs a circuit and then its inverse.  Without error the inverse `V` takes the state `ψ`
that the circuit calls for back to the initial state `init` and keeps the overlap of every two
states; the gates act on what the register holds, `held`, as on any state; and a run is without
error with the probability `F`, the gate fidelity, so the test returns the initial state with
the probability `ret = F |⟨init|V held⟩|²` (`hgates`).  The overlap of `V held` with the initial
state is the overlap of `held` with `ψ`.  The first part: where every joint outcome has a
conditional state of its own in `ψ`, as in a random state, `ret` is at most `F` times the
probability that `ψ` gives a set `S` of at most `L` outcomes (`overlap_bound`), which is `0.12`
at `210` qubits (`Numerics.porter_thomas_bound`).  The second part: where the register holds the
state `ψ` itself and the initial state is a state, the test returns with the probability `F`, as
in quantum mechanics.  Whether the register holds `ψ` the statement does not say: the premise
`hout`, Postulate 1's possible outcomes for the last qubit's conditioned outcomes, with the
conditional states those of `ψ`, allows it wherever the string has room for them
(`Conditional.room_holds`), and where the conditional states all differ it allows it only for a
`ψ` of at most `L` outcomes, by `overlap_bound`, whose `held` vanishes outside `S`.  Sources:
the gates (quantum mechanics); Postulate 1's bits as the possible outcomes, for the last qubit's
conditioned outcomes, and no ring with more than `L` cells; the conditions: `χ` stands for the
conditional states of `ψ`, and `held` is a state. -/
theorem return_bound {Cell K T : Type*} [Fintype Cell] [Fintype K] [DecidableEq K]
    [DecidableEq T] (L : ℕ) (held ψ init : K × Bool → ℂ) (V : (K × Bool → ℂ) → K × Bool → ℂ)
    (χ : K → T) (e : Cell → K) (b : Cell → Bool) (F ret : ℝ) (hL : P1.ring_cells Cell L)
    (hout : P1.outcomes_at_positions
      (fun s v => ∑ k ∈ univ.filter (fun k => χ k = s), ‖held (k, v)‖ ^ 2)
      (fun x => χ (e x)) b)
    (hχ : Condition.state_given ψ χ) (hnorm : Condition.normalized held)
    (hgates : QM.gates V ψ init held F ret) :
    (Condition.all_differ ψ →
      ∃ S : Finset (K × Bool), S.card ≤ L ∧ ret ≤ F * ∑ ω ∈ S, ‖ψ ω‖ ^ 2) ∧
    (held = ψ → Condition.normalized init → ret = F) := by
  obtain ⟨hkeep, hback, hF, hret⟩ := hgates
  refine ⟨fun hdiff => ?_, fun hheld hinit => ?_⟩
  · obtain ⟨S, hS, -, hov⟩ := overlap_bound L held ψ χ e b hL hout hχ hdiff hnorm
    refine ⟨S, hS, ?_⟩
    rw [hret]
    apply mul_le_mul_of_nonneg_left _ hF
    rw [← hback, hkeep ψ held]
    exact hov
  · have hinit' : ∑ ω, ‖init ω‖ ^ 2 = 1 := hinit
    have hsum : ∑ ω, (starRingEnd ℂ) (init ω) * init ω = ((∑ ω, ‖init ω‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [hret, hheld, hback, hsum, hinit']
    simp

/-! ### Sec. III and IV.C–IV.D: the vacuum term, the frame of the law, the pull and the push -/

/-- **Jacobson's step does not see a vacuum energy** (Sec. IV.D: "The zero-point energy of the
fields does not set `Λ`, which enters Einstein's equations as an integration constant").  Add to
the stress tensor a term `c g_ab`, the energy of a vacuum, whatever `c`.  Jacobson's step takes
the stress tensor on null vectors alone, where the term vanishes
(`Einstein.quad_add_smul_eta_of_null`), so the step holds for the new stress tensor as it holds
for the old one: no such term fixes `Λ`, which the equations leave free
(`Einstein.any_constant_model`) and the rings fix (`deSitter_horizon`).  Sources: Jacobson's step
at every point (`Derived`, `jacobson_step`). -/
theorem vacuum_energy_unseen {H : Horizon L} (R : Reg) (η : H.Cell → H.Loop → ℝ)
    (M : Einstein.Spacetime) (c : ℝ) (hcl : Derived.clausius H R η M) :
    Derived.clausius H R η
      { Pt := M.Pt, ric := M.ric, stress := fun p => M.stress p + c • Einstein.eta,
        divStress := M.divStress, ric_symm := M.ric_symm } := by
  intro η₀ hη₀ hall p k hk
  show Einstein.quad (M.ric p) k
    = (2 * R.pi * R.kB / (R.ℏ * R.c * η₀)) * Einstein.quad (M.stress p + c • Einstein.eta) k
  rw [Einstein.quad_add_smul_eta_of_null _ c k hk]
  exact hcl η₀ hη₀ hall p k hk

/-- **`G` and `GΛ` with `s` bits per ring** (Sec. VI: "With `s` bits per ring, Eqs. (G) and
(Lambda) would carry `s ln 2` in place of `ln 2`, so only a change in `s` could change `GΛ`").
With the entropy `s` times one bit for each ring, the count's density is `sη`, and Jacobson's `G`
for that density (`hJ`) with the constant `Λ = 3/R_Λ²` gives `G = c³ℓ_c²/(πℏ s ln 2)` and
`GΛ = 12πc³/(ℏL² s ln 2)`.  Sources: Jacobson's step for any density, and the constant
(`Derived`); the condition `s > 0`. -/
theorem G_Lambda_bits (R : Reg) (G Λ s : ℝ) (hs : Condition.pos s)
    (hJ : Derived.jacobson_G_density R G (s * R.η)) (hdS : Derived.deSitter_horizon R G Λ) :
    G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ * (s * R.ln2)) ∧
    G * Λ = 12 * R.pi * R.c ^ 3 / (R.ℏ * R.L ^ 2 * (s * R.ln2)) := by
  reg_facts R
  have hs' : (0 : ℝ) < s := hs
  have hs0 := hs'.ne'
  have hJ' : G = R.c ^ 3 * R.kB / (4 * R.ℏ * (s * R.η)) := hJ
  have hΛ := (R.deSitter G Λ).1 hdS
  have hG : G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ * (s * R.ln2)) := by
    rw [hJ', R.eta_eq]
    field_simp
  refine ⟨hG, ?_⟩
  rw [hG, hΛ]
  unfold Reg.RL
  field_simp
  ring

/-- **The frame of the law** (Sec. IV.C: "an Unruh temperature is that of a proper acceleration:
the acceleration of an observer held at rest relative to the body, against local free fall.  In
the manifold a uniform external field, such as the Galaxy's across the solar system, is a common
acceleration of the body and of local free fall at the place of every such observer.  So it
changes no proper acceleration, and hence neither the sphere's temperature nor the share"; then
Eq. (law) "therefore holds in the body's freely falling frame as for an isolated body, and of an
external field only its tide, the variation across the sphere, enters").  The law reads proper
accelerations alone.  `g x` is the acceleration of free fall at the observer's place `x` and `ab`
the body's acceleration; `g' x` and `ab'` are the two in a second situation, with an external
field.  An observer held at rest relative to the body has the body's acceleration, so his proper
acceleration, against local free fall, is `ap = ab − g x` in the first situation and
`ap' = ab' − g' x` in the second (`hap`, `hap'`), with the magnitudes `a` and `a'`.  The first
part restates the definition: free fall at `x`, relative to the body, is `−ap`, and for a body at
rest, unaccelerated (Sec. II), `ap = −g x`.  The second part: the field changes the proper
acceleration by the difference between what it does to the body and what it does to free fall at
`x`.  The third part: the proper acceleration is unchanged exactly where the field is a common
acceleration of the body and of free fall at `x`, the uniform field of
`Condition.carried_alike`.  The fourth part: under such a field the magnitude is unchanged, and
so are the temperature of the sphere there, which is the Unruh temperature of that acceleration
(`I1a`, `I1a'`), and the share `b = g_N/a` of the strings that carry the body's information
(`hb`, `hb'`); and Eq. (law), which holds for the proper acceleration without the field
(`hlaw`), holds for the proper acceleration with it: the law stands in the body's freely falling
frame as for a body alone ("For a test body in the field of a mass the law stands, with no
external-field effect").  That the field of a given source is a common acceleration of the body
and of free fall across the sphere is the condition; the files do not derive it.  The first
three parts are kinematics and take no premise of a source.  Sources: the law and `a = g_N/b`
(`Derived`, `galactic_law`, `carriers_share`); the thermal horizons of the accelerations
(thermodynamics); the conditions: the proper accelerations, `g_N > 0`. -/
theorem frame_of_law (R : Reg) (g g' : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x ab ab' ap ap' : Fin 3 → ℝ) (a a' T T' gN b b' : ℝ) (hgN : Condition.pos gN)
    (hap : Condition.proper_acceleration g x ab ap a)
    (hap' : Condition.proper_acceleration g' x ab' ap' a')
    (I1a : Thermo.horizon_thermal R a T) (I1a' : Thermo.horizon_thermal R a' T')
    (hb : Derived.share_acceleration a gN b) (hb' : Derived.share_acceleration a' gN b')
    (hlaw : Derived.galactic_law R a gN) :
    (g x - ab = -ap ∧ (Condition.at_rest ab → ap = -g x)) ∧
    ap' - ap = (ab' - ab) - (g' x - g x) ∧
    (Condition.carried_alike g g' x ab ab' ↔ ap' = ap) ∧
    (Condition.carried_alike g g' x ab ab' →
      a' = a ∧ T' = T ∧ b' = b ∧ Derived.galactic_law R a' gN) := by
  obtain ⟨hp, ha⟩ := hap
  obtain ⟨hp', ha'⟩ := hap'
  have htide : ap' - ap = (ab' - ab) - (g' x - g x) := by
    rw [hp', hp]
    abel
  have hiff : Condition.carried_alike g g' x ab ab' ↔ ap' = ap := by
    constructor
    · intro hunif
      have hunif' : ab' - ab = g' x - g x := hunif
      have h := htide
      rw [hunif', sub_self] at h
      exact sub_eq_zero.1 h
    · intro hsame
      show ab' - ab = g' x - g x
      have h := htide
      rw [hsame, sub_self] at h
      exact sub_eq_zero.1 h.symm
  refine ⟨⟨by rw [hp]; abel, fun h0 => ?_⟩, htide, hiff, fun hunif => ?_⟩
  · have h0' : ab = 0 := h0
    rw [hp, h0', zero_sub]
  · have hsame : ap' = ap := hiff.1 hunif
    have haa : a' = a := by rw [ha', ha, hsame]
    refine ⟨haa, ?_, ?_, ?_⟩
    · have h1 : R.kB * T = R.ℏ / (R.La a * R.tc) := I1a
      have h2 : R.kB * T' = R.ℏ / (R.La a' * R.tc) := I1a'
      rw [haa] at h2
      exact mul_left_cancel₀ R.kB_pos.ne' (h2.trans h1.symm)
    · have h1 : a = gN / b := hb
      have h2 : a' = gN / b' := hb'
      have hg0 : gN ≠ 0 := (show (0 : ℝ) < gN from hgN).ne'
      rw [haa, h1, div_eq_mul_inv, div_eq_mul_inv] at h2
      exact (inv_inj.1 (mul_left_cancel₀ hg0 h2)).symm
    · rw [haa]
      exact hlaw

/-- **The pull of Eq. (law) and the push** (Sec. IV.C: Eq. (law) is the pull of the mass, and
"the push of the vacuum (Sec. IV.D) is to be subtracted, and it meets the pull only far beyond any
galaxy").  The acceleration `a` of Eq. (law) (`hlaw`) is at least Newton's pull `GM/r²`.  So the
field with the pull of Eq. (law), `a − c²r/R_Λ²`, the pull less the push, is at least the field
of the solution, and it is positive, toward the mass, at every radius inside the radius
`r_z³ = GMR_Λ²/c²` at which the push would balance Newton's pull (`zero_gravity`): the push meets
the pull of Eq. (law) only beyond `r_z`, which is `1.1` Mpc for a galaxy of `10¹² M☉`
(`Numerics.zero_gravity_radius`).  Sources: the law, `G` and the constant (`Derived`); the
conditions `M > 0`, `r > 0`. -/
theorem pull_and_push (R : Reg) (G M Λ r a : ℝ) (hM : Condition.pos M) (hr : Condition.pos r)
    (hJ : Derived.jacobson_G R G) (hdS : Derived.deSitter_horizon R G Λ)
    (hlaw : Derived.galactic_law R a (G * M / r ^ 2)) :
    G * M / r ^ 2 ≤ a ∧ R.gSdS G M Λ r ≤ a - R.c ^ 2 * r / R.RL ^ 2 ∧
    (r ^ 3 < G * M * R.RL ^ 2 / R.c ^ 2 → 0 < a - R.c ^ 2 * r / R.RL ^ 2) := by
  reg_facts R
  have hr' : (0 : ℝ) < r := hr
  have hM' : (0 : ℝ) < M := hM
  have hRL := R.RL_pos
  have hG0 : 0 < G := by rw [(R.G_eq G hJ).1]; positivity
  have hgN : 0 < G * M / r ^ 2 := by positivity
  have hh : 0 < Real.sqrt (G * M / r ^ 2 / R.a0) := Real.sqrt_pos.2 (div_pos hgN R.a0_pos)
  have hb1 : Real.exp (-Real.sqrt (G * M / r ^ 2 / R.a0)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hb0 : 0 < 1 - Real.exp (-Real.sqrt (G * M / r ^ 2 / R.a0)) := by linarith
  have hble : 1 - Real.exp (-Real.sqrt (G * M / r ^ 2 / R.a0)) ≤ 1 := by
    linarith [Real.exp_pos (-Real.sqrt (G * M / r ^ 2 / R.a0))]
  have hlaw' : a = G * M / r ^ 2 / (1 - Real.exp (-Real.sqrt (G * M / r ^ 2 / R.a0))) := hlaw
  have hpull : G * M / r ^ 2 ≤ a := by
    rw [hlaw', le_div_iff₀ hb0]
    nlinarith
  have hfield := (R.push G M Λ r hr' hJ hdS).1
  refine ⟨hpull, by rw [hfield]; linarith, fun hz => ?_⟩
  have hpush : R.c ^ 2 * r / R.RL ^ 2 < G * M / r ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : r ^ 3 * R.c ^ 2 < G * M * R.RL ^ 2 := by
      rwa [lt_div_iff₀ (by positivity)] at hz
    nlinarith
  linarith

/-- **Milgrom's simple interpolating function against the law** (Sec. IV.C: "Other functions fit
the data too; Milgrom's simple interpolating function differs from Eq. (law) by at most `5%` at
every acceleration").  With the scale `a₀` of the law in both, the acceleration that the simple
function `μ(x) = x/(1 + x)` gives for Newton's field `g_N`, the positive root of
`a μ(a/a₀) = g_N` (`Interpolation.simple`), is at least the acceleration `a` of Eq. (law)
(`hlaw`) and at most `21/20` of it, at every `g_N > 0`.  The first two parts state that the simple
function's acceleration is that root and take no premise.  Sources: the law (`Derived`,
`galactic_law`); the condition `g_N > 0`. -/
theorem simple_interpolation (R : Reg) (a gN : ℝ) (hgN : Condition.pos gN)
    (hlaw : Derived.galactic_law R a gN) :
    0 < Interpolation.simple R.a0 gN ∧
    Interpolation.simple R.a0 gN *
      ((Interpolation.simple R.a0 gN / R.a0) / (1 + Interpolation.simple R.a0 gN / R.a0)) = gN ∧
    a ≤ Interpolation.simple R.a0 gN ∧ Interpolation.simple R.a0 gN ≤ 21 / 20 * a := by
  have hlaw' : a = gN / (1 - Real.exp (-Real.sqrt (gN / R.a0))) := hlaw
  obtain ⟨h1, h2⟩ := Interpolation.simple_within R.a0 gN R.a0_pos hgN
  obtain ⟨h3, h4⟩ := Interpolation.simple_root R.a0 gN R.a0_pos hgN
  rw [hlaw']
  exact ⟨h3, h4, h1, h2⟩

end Register.Main

#premises Register.Main.count Register.Main.horizon_entropy Register.Main.jacobson_step
  Register.Main.jacobson_G_density
  Register.Main.jacobson_G
  Register.Main.jacobson_G_exact Register.Main.G_leading_order
  Register.Main.chain Register.Main.deSitter_horizon Register.Main.cell_from_G
  Register.Main.entropy_quarter Register.Main.newton Register.Main.entropy_removed Register.Main.entropy_removed_sphere
  Register.Main.entropy_removed_leading_order
  Register.Main.G_Lambda Register.Main.vacuum_density Register.Main.komar_misner_sharp
  Register.Main.black_hole_quarter Register.Main.string_energy Register.Main.vacuum_share
  Register.Main.horizon_quarter Register.Main.temperature_floor Register.Main.equation_of_state
  Register.Main.ceiling Register.Main.einstein
  Register.Main.matter_geodesic Register.Main.light_rays Register.Main.rotation_curve
  Register.Main.schwarzschild_deSitter Register.Main.lambda_with_mass Register.Main.horizon_drawn_in
  Register.Main.register_in_band
  Register.Main.register_finite Register.Main.register_even Register.Main.ring_through_two_cells
  Register.Main.projective_plane Register.Main.rings_cross_horizon
  Register.Main.opposite_halfway Register.Main.string_one_bit
  Register.Main.share_of_bits Register.Main.area_in_cells Register.Main.L_from_horizon
  Register.Main.temperature_in_cells Register.Main.newton_in_cells Register.Main.quarter_any_count
  Register.Main.G_mul_eta Register.Main.komar_mass
  Register.Main.ceiling_in_step Register.Main.ceiling_logical Register.Main.one_cell_block
  Register.Main.coding_step Register.Main.repetition_code Register.Main.line_code
  Register.Main.massive_horizon Register.Main.black_hole_horizon
  Register.Main.temperature_led Register.Main.carriers_share Register.Main.fill_fraction
  Register.Main.galactic_law Register.Main.near_limit Register.Main.deep_limit
  Register.Main.tully_fisher Register.Main.classical_share Register.Main.scale_mean
  Register.Main.scale
  Register.Main.push Register.Main.zero_gravity Register.Main.hubble Register.Main.G_drift
  Register.Main.constants_in_time Register.Main.lambda_rate Register.Main.w_bound
  Register.Main.gibbs Register.Main.sphere_strings
  Register.Main.observer_count Register.Main.observer_rings
  Register.Main.sphere_areal_radius
  Register.Main.first_law_extended Register.Main.block_fraction Register.Main.surface_code
  Register.Main.ring_one_string Register.Main.lap Register.Main.two_senses
  Register.Main.sense_of_state Register.Main.free_tick_hidden Register.Main.bit_kept
  Register.Main.joint_frequency Register.Main.product_state Register.Main.strings_in_step
  Register.Main.overlap_bound Register.Main.return_bound Register.Main.vacuum_energy_unseen
  Register.Main.G_Lambda_bits Register.Main.frame_of_law Register.Main.pull_and_push
  Register.Main.simple_interpolation
