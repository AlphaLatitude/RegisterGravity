import RegisterGravity.Models
import RegisterGravity.Galactic

/-!
# The symmetry of space, and space determined by the rings (Secs. II and IV.D)

The thesis of the paper, that gravitation follows from the two postulates and thermodynamics,
rests on the first sentence of Postulate 1: every physical law and quantity is defined
by qubits.  So the register is all there is to describe: a law or a quantity that depended on
anything else would not be defined by qubits.

**Postulate 1's first sentence, as the files take it** (`Sources.lean` states it as the premise;
the README repeats it).  "Every physical law and quantity is defined by qubits" quantifies over laws
and quantities, and the files give each the form it has in them, so that the sentence is stated for
each and applied by unfolding.  A law is a function of the register's crossings, the type of `f`
below.  A quantity that varies over the register's items, the crossings or the slots of space, is a
function of what the register holds there, the laws and the state (`IsQubits`,
`Sources.P1.qubits`).  A quantity to which another description, the manifold or thermodynamics,
assigns a value has the register's value (`Sources.P1.physical`).  And the geometry of space being a
quantity, a ring runs along every geodesic of space (`ringsAlong`, `Sources.P1.rings_along`;
`Space.SliceIsQubits` for the space at an instant), since a
geodesic with no ring along it would be a feature of a quantity not defined by qubits.  The
sentence so applied is a hypothesis of the theorem that uses it, and it is the sentence itself, not
a further premise: it asserts of the named law or quantity exactly what the sentence asserts of
every one, that it is defined by the register, and nothing more; what follows from it is proved
(`IsQubits.eq_of_content_eq`, `Solution.geometry_same`, `Space.slice_sphere`,
`Space.sphere_rings`).  The instances, each named where it is taken, and no others: the
geometry of space at a slot is defined by the laws and the state there (`hgeom : IsQubits …`
of `Solution.geometry_same` and `Solution.cosmological_constant_from_sources`); every geodesic of
the space at an instant of an observer at rest is one along which a ring runs (`hclose` and
`hslice` of `Solution.cosmological_constant_from_sources`; `described`); the entropy of a local horizon, the entropy of Clausius' relation, is its strings', the law
`η` times its area (`hent` of `Main.jacobson_step`, `Sources.P1.local_entropy`, a `physical`, with
Sec. II's count and Postulate 2's clauses, which make the density the same on every horizon,
`one_density`); the entropy of the cosmological horizon, its entropy per unit area times its area,
is `k_B` times the entropy of the state of the register's strings (`hhor` of
`Main.jacobson_G_exact`, `Sources.P1.horizon_entropy`, a `physical`); the energy inside the horizon
is the energy of its strings (`hin` of `Main.vacuum_share`, `P1.energy_inside_strings`); a body's energy is
held by the strings that carry its information (`hcar` of `Main.carriers_share` and
`Main.galactic_law`, `Sources.P1.energy_in_carriers`); the energy of light goes with the light, its current along its ray for every observer
(`hlight` of `Main.light_rays`, `Sources.P1.light`, a `physical` whose register side is the ray's
direction only, with Postulate 1's light crossing a cell in one tick); a law is a function of the register, of the crossing of a ring with a cell (the type
of `f` in `laws_same`, Sec. II's definition of a law, of which Postulate 2's clauses speak); a
horizon's state is a state of its strings and of nothing else (the type of `Bridge.horizonEntropy`,
Postulate 1's second sentence); and the number of strings a sphere holds about a body does not
depend on the drawing, which is no part of the register, so
it is the average over its rotations with a weighting that no rotation changes (`Center.lean`,
`Weighting.lean`, `Sources.P1.no_rotation_preferred`).

This file applies that sentence three times, each time as an instance, in what an object is a
function of:

* A **law** is a function `f` of the register: `f x l` is the law where ring `l` crosses cell
  `x`.
* **Space** is determined by the rings.  Space is the cells of the rings, and the manifold
  describes that space (Sec. II).  A **slot** is a geodesic of space, given
  by a place and a direction there.  A **drawing** `D` puts the crossing of each ring `l` with each
  of its cells `x` at a slot `D x l`, the geodesic along which it draws the ring; it does not record
  where on that geodesic the cell lies, which the count does not use (the cells are the geodesic's
  segments of length `ℓ_c`, Postulate 2's last sentence), and which rings share a cell the manifold
  does not describe (Sec. II).  The postulates fix the rings, not which closed geodesics of
  space they are, so the drawing is free.  The space the rings describe, `described 𝒟`, is the set
  of slots along which some drawing runs a ring; a geodesic along which no ring runs would be a
  feature of space that the rings do not describe.  The law at a slot of that space,
  `lawAt 𝒟 f`, is the law at a crossing that some drawing puts there.
* **A ring runs along every geodesic of space**, by an admissible drawing, one that the last
  sentence of Postulate 2 allows (`admissible H Ring`: every ring along one geodesic that closes
  with a largest ring's length): along every geodesic of the space at an instant of an observer at
  rest (`Space.SliceIsQubits`).  Were it not so, some geodesic would have no ring along it, a
  feature of space that is not qubits.  `Space.lean` derives from this, with the rings through the
  observer's cell drawn in space (Sec. II's cell a place on them, the same opposite cell halfway
  around each), that the space at an instant of the solution without a mass is the three-sphere
  itself.

`Bridge.horizonEntropy` applies the thesis in the same way: a horizon's thermal state is a state
of the strings alone.

The two clauses of Postulate 2 that concern laws are the hypotheses `hsym`, that some symmetry of
the register carries any cell to any other and leaves every law unchanged, and `hdir`, that no law
depends on the direction in which a ring passes through a cell.  From them:

* `laws_same`: every law is the same at every crossing of a ring with a cell.
* `lawAt_eq`, `lawAt_same`: so the law at a slot of space does not depend on the drawing, and it is
  the same at every place and in every direction of the space the rings describe.  This is the
  symmetry of space.
* `one_density`: the entropy density of a local horizon is a law, so it is the same on every local
  horizon, the value the count gives on the cosmological horizon; with it Jacobson's step, the
  Clausius relation at every point, gives `G = c³k_B/(4ℏη)` with the count's `η`, the hypothesis
  `hJ` of `Chain.lean`, with Newton's law (`Solution.jacobson_G_from_sources`).
* `massive_horizon_density`, `black_hole_density`: at that one density, the horizon drawn in by a
  mass, whose area the solution gives, holds `L_M²/4` bits, and a black hole's horizon holds
  `L'²/4` bits; so the area law with a mass (Secs. IV.C and IV.D) follows from the one density and
  the solution's areas.

Apart from the two clauses, `mem_described_admissible` shows that a slot lies in the space the
admissible drawings describe exactly when a ring can run there, that is, when it closes with a
largest ring's length.

The step from the symmetry to the solution is in `Solution.lean` and `Space.lean`.  Without a
mass, the strings free and so uncorrelated, the state is the same at every crossing too
(`Solution.state_same`).  The geometry of space at
a slot, the curvature of the plane normal to the slot's direction and the rate at which that
curvature changes, is qubits (`IsQubits`, the sentence applied to the geometry): it is read off the
laws and the state there.  So it is the same at every slot (`Solution.geometry_same`, by
`IsQubits.eq_of_content_eq`): space has constant curvature and expands alike in every direction.
With a ring along every geodesic of the space at an instant, that space is a space form (the
Killing–Hopf theorem, `Sources.Geometry.space_form`), the three-sphere divided by a group
(`Space.slice_sphere`), and with the rings through the observer's cell drawn in it
(`Space.RingsDrawn`) the three-sphere itself (`Space.sphere_rings`).

`laws_same_model` shows that the two clauses can be met, in the Fano register, with a drawing that
runs a ring along every slot.
-/

open Horizon

namespace Symmetry

variable {L : ℕ} {H : Horizon L} {Slot V : Type*}

/-! ### Postulate 1's first sentence, applied -/

/-- **Is qubits** (Postulate 1's first sentence, "every physical law and quantity is defined by
qubits", for a quantity that varies over the register's items; Sec. II).  A quantity `q` on a kind
`ι` of items, the crossings of rings with cells or the slots of the space the rings describe, is
defined by qubits when it is read off what the register holds at the item, `content i`, the laws
and the state there: it is `F (content i)` for one function `F`.  Such a quantity depends on
nothing the register does not hold.  `Sources.P1.qubits` states the premise in this form; the
geometry of space is taken so in `Solution.geometry_same` (`hgeom`); for space itself the sentence
takes the form `ringsAlong` (`Space.SliceIsQubits`). -/
def IsQubits {ι C α : Type*} (content : ι → C) (q : ι → α) : Prop :=
  ∃ F : C → α, ∀ i, q i = F (content i)

/-- **A quantity that is qubits reads the same at two items the register holds alike**
(Sec. IV.D: "The geometry of space is a quantity, defined by qubits (Postulate 1), so the laws
and the state alone set it").  What the register holds at an item sets the quantity there, so
the quantity has one value at two items where the register holds the same. -/
theorem IsQubits.eq_of_content_eq {ι C α : Type*} {content : ι → C} {q : ι → α}
    (h : IsQubits content q) {i j : ι} (hij : content i = content j) : q i = q j := by
  obtain ⟨F, hF⟩ := h
  rw [hF i, hF j, hij]

/-- **The space the rings describe** (Sec. II): the slots, the geodesics of space, along which some
drawing in `𝒟` runs a ring.  Space is determined by the rings (the thesis): it is the cells of
the rings, so a geodesic along which no ring runs would be a feature of space that the rings do
not describe. -/
def described (𝒟 : Set (H.Cell → H.Loop → Slot)) : Set Slot :=
  {σ | ∃ D ∈ 𝒟, ∃ l, ∃ x ∈ H.cells l, D x l = σ}

/-- membership in the space the rings describe, unfolded -/
lemma mem_described {𝒟 : Set (H.Cell → H.Loop → Slot)} {σ : Slot} :
    σ ∈ described 𝒟 ↔ ∃ D ∈ 𝒟, ∃ l, ∃ x ∈ H.cells l, D x l = σ := Iff.rfl

/-- **The law at a slot of the space the rings describe** (Sec. II): a law is a function `f` of
the register (the thesis), of the crossing of a ring with a cell, and the law at a slot is the law
at one crossing that some drawing puts there, chosen by `Classical.choose`; `lawAt_eq` shows that
the choice does not matter. -/
noncomputable def lawAt (𝒟 : Set (H.Cell → H.Loop → Slot)) (f : H.Cell → H.Loop → V)
    (σ : described 𝒟) : V :=
  f (Classical.choose (Classical.choose_spec (Classical.choose_spec (mem_described.1 σ.2)).2))
    (Classical.choose (Classical.choose_spec (mem_described.1 σ.2)).2)

/-- **The admissible drawings** (Postulate 2): a drawing that runs ring `l` along a geodesic puts
every crossing of `l` at that geodesic, and the admissible drawings run every ring along one
geodesic where `Ring` holds.  With `Ring σ` saying that `σ` closes with a largest ring's length,
these are the drawings the last sentence of Postulate 2 allows: every largest ring is a closed
geodesic of space, made of its cells as segments of length `ℓ_c`.  The postulates ask nothing more
of a drawing, which does not show which rings
share a cell (Sec. II); it may run several rings along one geodesic. -/
def admissible (H : Horizon L) (Ring : Slot → Prop) : Set (H.Cell → H.Loop → Slot) :=
  {D | ∀ l, ∀ x ∈ H.cells l, Ring (D x l) ∧ ∀ y ∈ H.cells l, D y l = D x l}

/-- **A largest ring runs along every geodesic** (Postulate 1's first sentence applied to a space;
Secs. II and IV.D): along every geodesic `σ` of the set `S` some admissible drawing runs a ring,
which closes there with a largest ring's length, `Closes σ`.  A geodesic along which no ring runs
would be a feature of space that the strings do not describe.  The one form of the sentence for
the space the files treat: the space at an instant (`Sources.P1.slice_qubits`) and its space form
(`Space.SliceIsQubits`) are this definition at their sets of geodesics. -/
def ringsAlong (H : Horizon L) (S : Set Slot) (Closes : Slot → Prop) : Prop :=
  ∀ σ ∈ S, σ ∈ described (admissible H fun τ => τ ∈ S ∧ Closes τ)

/-- **Every law is the same at every crossing of a ring with a cell** (Sec. II, Postulate 2).
Take two crossings.  Some symmetry carries the first cell to the second and leaves the law
unchanged (`hsym`), and the law is the same on every ring through the second cell (`hdir`). -/
theorem laws_same (f : H.Cell → H.Loop → V)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l') :
    ∀ l x, x ∈ H.cells l → ∀ l' y, y ∈ H.cells l' → f x l = f y l' := by
  intro l x hx l' y hy
  obtain ⟨s, hs, hF⟩ := hsym x y
  have h1 : s.cellMap x ∈ H.cells (s.loopMap l) := (s.mem_iff l x).1 hx
  rw [hs] at h1
  calc f x l = f (s.cellMap x) (s.loopMap l) := (hF l x hx).symm
    _ = f y (s.loopMap l) := by rw [hs]
    _ = f y l' := hdir y _ _ h1 hy

/-- **No law depends on the drawing** (Sec. II): the law at a slot is the law at every crossing
of a ring with a cell, whether or not a drawing puts that crossing at the slot, since the law is
the same at every crossing (`laws_same`). -/
theorem lawAt_eq (𝒟 : Set (H.Cell → H.Loop → Slot)) (f : H.Cell → H.Loop → V)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l')
    (σ : described 𝒟) (l : H.Loop) (x : H.Cell) (hx : x ∈ H.cells l) :
    lawAt 𝒟 f σ = f x l := by
  have h := mem_described.1 σ.2
  have hl := Classical.choose_spec h
  have hx' := Classical.choose_spec (Classical.choose_spec hl.2)
  exact laws_same f hsym hdir _ _ hx'.1 l x hx

/-- **The symmetry of space: every law is the same at every place and in every direction of the
space the rings describe** (Sec. II). -/
theorem lawAt_same (𝒟 : Set (H.Cell → H.Loop → Slot)) (f : H.Cell → H.Loop → V)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l')
    (σ τ : described 𝒟) : lawAt 𝒟 f σ = lawAt 𝒟 f τ := by
  obtain ⟨-, -, l, x, hx, -⟩ := mem_described.1 τ.2
  rw [lawAt_eq 𝒟 f hsym hdir σ l x hx, lawAt_eq 𝒟 f hsym hdir τ l x hx]

/-- **One entropy density on every local horizon** (Secs. II and III): the entropy density of the
local horizon at a crossing is a law, so at every crossing it has the value `η₀` that it has at a
crossing `(x₀, l₀)` of the cosmological horizon, where the count gives it (`laws_same`). -/
theorem one_density (η : H.Cell → H.Loop → ℝ)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, η (s.cellMap z) (s.loopMap l) = η z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → η x l = η x l')
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : x₀ ∈ H.cells l₀) (η₀ : ℝ) (hη : η x₀ l₀ = η₀) :
    ∀ l x, x ∈ H.cells l → η x l = η₀ := fun l x hx =>
  (laws_same η hsym hdir l x hx l₀ x₀ h₀).trans hη

/-- **The area law with a mass** (Secs. III and IV.C).  The entropy density is one law, the same on
every local horizon (`one_density`, the two clauses of Postulate 2), the count's `η` on the
cosmological horizon to leading order in `1/L` (`hcount`), and Jacobson's step ties `G` to it
(`hJ`, thermodynamics).  With a
mass inside, the horizon lies at `R_Λ − GM/c²` to first order (`Reg.sds_outer_horizon`, the
Schwarzschild–de Sitter solution), and at that density its entropy, the density times its area, is
`k_B ln 2` times `L_M²/4` with `L_M = L − 2α/ln 2`: the horizon holds `L_M²/4` bits, the number
`Galactic.massive_horizon_count` reads from `Ns`.  So the count with a mass follows from the one
density and the solution's area; the area law, one bit per ring's share of area, is derived without
a mass (`Bridge.sphere_strings`) and is not a step taken again with the mass. -/
theorem massive_horizon_density (R : Register.Reg) (G M : ℝ) (η : H.Cell → H.Loop → ℝ)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, η (s.cellMap z) (s.loopMap l) = η z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → η x l = η x l')
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : x₀ ∈ H.cells l₀) (hcount : η x₀ l₀ = R.η)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    (∀ l x, x ∈ H.cells l → η x l = R.η) ∧
    R.η * (4 * R.pi * (R.RL - G * M / R.c ^ 2) ^ 2) =
      R.kB * ((R.L - 2 * R.α M / R.ln2) ^ 2 / 4) * R.ln2 := by
  refine ⟨one_density η hsym hdir h₀ R.η hcount, ?_⟩
  have h1 := R.massive_horizon_count G M hJ
  have h2 := (R.ratio_of_areas (R.RL - G * M / R.c ^ 2)).2
  rw [← h1, h2, R.shares.2, R.eta_eq]
  have := R.ℓc_pos; have := R.pi_pos
  field_simp

/-- **A black hole's horizon at the one density** (Sec. IV.D, on the circles at the horizons):
its area is `4πr_s²` with `r_s = 2GM/c²` (Schwarzschild's solution, derived), and at the
one density (`one_density`) its entropy is `k_B ln 2` times `L'²/4` with `L' = 4πGM/c²ℓ_c` cells on
its great circles: `L'²/4` bits, the number `Reg.black_hole_quarter` reads from the area law. -/
theorem black_hole_density (R : Register.Reg) (G M : ℝ) (η : H.Cell → H.Loop → ℝ)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, η (s.cellMap z) (s.loopMap l) = η z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → η x l = η x l')
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : x₀ ∈ H.cells l₀) (hcount : η x₀ l₀ = R.η) :
    (∀ l x, x ∈ H.cells l → η x l = R.η) ∧
    R.η * (4 * R.pi * (2 * G * M / R.c ^ 2) ^ 2) =
      R.kB * ((4 * R.pi * G * M / (R.c ^ 2 * R.ℓc)) ^ 2 / 4) * R.ln2 := by
  refine ⟨one_density η hsym hdir h₀ R.η hcount, ?_⟩
  rw [R.eta_eq]
  have := R.ℓc_pos; have := R.pi_pos; have := R.c_pos
  field_simp
  ring

/-- **A slot lies in the space the admissible drawings describe exactly when a ring can run there**
(Secs. II and IV.D): the slot of a drawn ring satisfies `Ring`, by admissibility; conversely, where
`Ring` holds, the drawing that runs every ring along that slot is admissible, and it puts there the
crossing of a ring with one of its cells, which every register has (`Horizon.two_loops`,
`Horizon.loops_meet`). The space the admissible drawings describe therefore does not depend on the
register, only on `Ring`. -/
theorem mem_described_admissible (Ring : Slot → Prop) (σ : Slot) :
    σ ∈ described (admissible H Ring) ↔ Ring σ := by
  constructor
  · rintro ⟨D, hD, l, x, hx, rfl⟩
    exact (hD l x hx).1
  · intro hσ
    obtain ⟨l₀, -, -⟩ := H.two_loops
    obtain ⟨x₀, h₀, -⟩ := H.loops_meet l₀ l₀
    exact ⟨fun _ _ => σ, fun _ _ _ => ⟨hσ, fun _ _ => rfl⟩, l₀, x₀, h₀, rfl⟩

/-- **The clauses of Postulate 2 on laws can be met, with a drawing that runs a ring along every
slot**, so `laws_same` and `lawAt_same` do not hold vacuously: in the Fano register, whose
symmetries carry any cell to any other (`Horizon.fano_homogeneous`), take a constant law, the
crossings of a ring with a cell as the slots, and the one drawing that puts each crossing at its own
slot. -/
theorem laws_same_model :
    ∃ (f : fano.Cell → fano.Loop → ℝ)
      (𝒟 : Set (fano.Cell → fano.Loop → {p : fano.Cell × fano.Loop // p.1 ∈ fano.cells p.2})),
      (∀ x y : fano.Cell, ∃ s : fano.Symmetry, s.cellMap x = y ∧
        ∀ l, ∀ z ∈ fano.cells l, f (s.cellMap z) (s.loopMap l) = f z l) ∧
      (∀ x l l', x ∈ fano.cells l → x ∈ fano.cells l' → f x l = f x l') ∧
      described 𝒟 = Set.univ := by
  let l₀ : fano.Loop := (0 : Fin 7)
  let x₀ : fano.Cell := ((0 : Fin 7), false)
  have h₀ : x₀ ∈ fano.cells l₀ := by
    change ((0 : Fin 7), false) ∈ fanoLines (0 : Fin 7) ×ˢ (Finset.univ : Finset Bool)
    decide
  let D₀ : fano.Cell → fano.Loop → {p : fano.Cell × fano.Loop // p.1 ∈ fano.cells p.2} :=
    fun x l => if h : x ∈ fano.cells l then ⟨(x, l), h⟩ else ⟨(x₀, l₀), h₀⟩
  refine ⟨fun _ _ => 1, {D₀},
    fun x y => (fano_homogeneous x y).imp fun _ hs => ⟨hs, fun _ _ _ => rfl⟩,
    fun _ _ _ _ _ => rfl, Set.eq_univ_of_forall fun σ => ?_⟩
  refine ⟨D₀, rfl, σ.1.2, σ.1.1, σ.2, ?_⟩
  simp [D₀, σ.2]

end Symmetry
