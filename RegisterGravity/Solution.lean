import RegisterGravity.Symmetry
import RegisterGravity.Bridge
import RegisterGravity.Capacity
import RegisterGravity.Qubit
import RegisterGravity.Cosmo
import RegisterGravity.Space

/-!
# The solution without a mass, from the symmetry of space (Sec. IV.D)

Section IV.D finds the solution of Einstein's equations without a mass from the symmetry of space.
This file states each link: as a theorem, as the first sentence of Postulate 1 applied (every
physical law and quantity is defined by qubits, the thesis of the paper), or as a cited theorem of
geometry, with its inputs proved or taken from the postulates.

* **The state is the same at every crossing** (`state_same`, a theorem).  Without a mass every
  string's qubit is in the thermal state of its tick, at one inverse temperature `β` (`hthermal`,
  `Qubit.Tick.state`, thermodynamics); this is where "without a mass" enters.  The two senses are
  the qubit's two outcomes (Sec. II), and they have one energy, since the tick's phase changes
  alike in either sense, by the clause of Postulate 2 on directions (`hsense` of `Qubit.Tick`):
  the tick multiplies both by one factor, and a string's energy is the energy of its factor
  (`Qubit.Tick.factor_eq`, `Qubit.Tick.energy_eq`).  So the thermal state, the Gibbs state over
  the two senses at their energies (the definition `Qubit.Tick.state`), is half the identity
  (`Qubit.Tick.state_eq`): each sense has the probability `1/2`.  Each cell's bit is one possible outcome among the `L` (`halike`,
  Postulate 1).  So the state seen where a ring crosses a cell (`crossingState`) is the same at
  every crossing.  That state is the string's thermal state with the cell's bit as one possible
  outcome, and the string's correlation with the other strings, which free strings make zero
  (`hfree`, `Entropy.correlation_jointProb`).  `crossingState` names what it leaves out, and why:
  the string's bits, its phase and its own energy.  That half the bits of a string in that state
  are 1s, on average, is `Qubit.half_bits_thermal`.
* **The geometry is the same at every place and in every direction** (`geometry_same`, a theorem).
  The geometry of space at a slot, the curvature of the plane normal to the slot's direction and
  the rate at which that curvature changes, is qubits: it is read off the laws and the state at the
  slot (`hgeom : IsQubits …`).  This is Postulate 1's first sentence, every physical law and
  quantity defined by qubits, for the geometry of space (`Symmetry.IsQubits`, `Sources.P1.qubits`;
  `Symmetry.lean` lists every instance the files take): a geometry that depended on anything else
  would be a quantity the strings do not define.  The laws are the same at every slot (`Symmetry.lawAt_same`), and so is
  the state (`state_same`, `lawAt_const`), so the geometry is too
  (`Symmetry.IsQubits.eq_of_content_eq`): space has constant curvature and expands alike in every
  direction.
* **The vacuum equations and Newton's constant** (`vacuum_without_mass`, `jacobson_G_from_sources`,
  theorems).  The entropy density is a law, the same on every local horizon (`Symmetry.one_density`),
  and not zero.  Jacobson's step at every point (`hcl`, which `Main.jacobson_step` derives from the
  Raychaudhuri equation, the heat that crosses a local horizon and the register's entropy on it)
  gives the field equations up to a multiple of the metric (`Einstein.einstein_up_to_metric`); the first law (`hfirst`) and the contracted
  Bianchi identity (`hbianchi`) make them Einstein's equations with one constant `Λ`
  (`Einstein.einstein_equations`), which without matter are the vacuum equations; with matter at
  rest in a static weak field (`hweak`) Newton's law gives `G = c³k_B/(4ℏη)`
  (`Einstein.G_of_clausius`).
* **The three-sphere itself** (`cosmological_constant_from_sources`, a theorem; the links are in
  `Space.lean`).  Every geodesic of the space at an instant of an observer at rest has a ring along
  it (`hclose`, `hslice`, Postulate 1's first sentence applied to that space), so it closes; with
  the geometry the same at every slot, that space is a space form (`hKH`: Schur's lemma,
  Hopf–Rinow and the Killing–Hopf theorem), with `3K = Λ` by Einstein's constraint (`hcon`), and its rings make it a quotient of the
  three-sphere (`Space.slice_sphere`).  Its rings close with one length, which leaves only the
  three-sphere and its antipodal quotient, and the rings through the observer's cell, drawn in
  space (`hdrawn`, Sec. II's cell and Postulate 2's last sentence with its first clause,
  `Sources.P2.rings_drawn`), exclude the latter: the space is the three-sphere itself, its great
  circles of length `2π√(1/K)` (`Space.sphere_rings`), and `Λ = 3/R_Λ²`
  (`Space.cosmological_constant_of_sources`).  Lean has no Riemannian geometry in which to
  prove the cited theorems the route uses.  The space at an instant is a term `sp` of a type `Sp`,
  and `embedSp` places the space forms among the spaces.  Each cited theorem is a named hypothesis
  that asserts the theorem for these terms (`Sources.Geometry`).

`cosmological_constant_model` shows that the hypotheses of `cosmological_constant_from_sources` can
be met together, in the Fano register with `Bridge.regSix`; those on the entropy density it does
not list, and any constant nonzero `η` meets them, the model's Jacobson relation holding at every
`κ`.

-/

open Horizon Finset Symmetry Quotients

namespace Solution

variable {L : ℕ} {H : Horizon L}

/-- **A quantity that is the same at every crossing has that value at every slot**: its value at a
slot of the space the rings describe, `Symmetry.lawAt`, is its value at any crossing, whatever the
drawing.  `Symmetry.lawAt_eq` is the case of a law, which the two clauses of Postulate 2 make the
same at every crossing (`Symmetry.laws_same`). -/
lemma lawAt_eq_of {Slot W : Type*} (𝒟 : Set (H.Cell → H.Loop → Slot)) (s : H.Cell → H.Loop → W)
    (hs : ∀ l x, x ∈ H.cells l → ∀ l' y, y ∈ H.cells l' → s x l = s y l')
    (σ : described 𝒟) (l : H.Loop) (x : H.Cell) (hx : x ∈ H.cells l) :
    lawAt 𝒟 s σ = s x l := by
  have h := mem_described.1 σ.2
  have hl := Classical.choose_spec h
  have hx' := Classical.choose_spec (Classical.choose_spec hl.2)
  exact hs _ _ hx'.1 l x hx

/-- **A quantity that is the same at every crossing is the same at every slot** of the space the
rings describe. -/
lemma lawAt_const {Slot W : Type*} (𝒟 : Set (H.Cell → H.Loop → Slot)) (s : H.Cell → H.Loop → W)
    (hs : ∀ l x, x ∈ H.cells l → ∀ l' y, y ∈ H.cells l' → s x l = s y l')
    (σ τ : described 𝒟) : lawAt 𝒟 s σ = lawAt 𝒟 s τ := by
  obtain ⟨-, -, l, x, hx, -⟩ := mem_described.1 τ.2
  rw [lawAt_eq_of 𝒟 s hs σ l x hx, lawAt_eq_of 𝒟 s hs τ l x hx]

/-- **Every slot is reached by some drawing**: when every drawing counts, not only the admissible
ones, the space the rings describe is every slot.  The drawing that puts every crossing at one slot
puts some crossing there (`Horizon.two_loops`, `Horizon.loops_meet`). -/
lemma described_univ {Slot : Type*} :
    described (Set.univ : Set (H.Cell → H.Loop → Slot)) = Set.univ := by
  ext σ
  simp only [Set.mem_univ, iff_true]
  obtain ⟨l₀, -, -⟩ := H.two_loops
  obtain ⟨x₀, h₀, -⟩ := H.loops_meet l₀ l₀
  exact ⟨fun _ _ => σ, Set.mem_univ _, l₀, x₀, h₀, rfl⟩

/-- **The state seen where ring `l` crosses cell `x`** (Secs. II and IV.A).  Without a mass the
string on ring `l` is in the horizon's thermal state (thermodynamics), and the function `F` of
`hgeom` (`Symmetry.IsQubits`), which gives the geometry, reads that thermal state with the cell's bit as one of the possible outcomes
of a measurement of the string.  So the entries are what every string in that state shares, which
`state_same` proves:

* the thermal state `ρ l` of its qubit, a density matrix on the two outcomes, which are the two
  senses (Sec. II); its diagonal entries are the probabilities of the senses (`Qubit.prob`, the
  Born probabilities of the basis outcomes), so the sense needs no entry of its own;
* the probability `read l x` that a measurement's outcome is the bit of the cell `x`; off the
  ring, where the string has no cell, this entry is `0`;
* the string's correlation with the other strings, `Entropy.correlation Pst l`: the joint
  distribution `Pst` of all the strings' senses, the horizon's thermal state, less the product of
  the string's own distribution and that of the others.  Free strings, whose joint distribution is
  the product of their own (`hfree`, Postulate 1 with thermodynamics), make it zero
  (`Entropy.correlation_jointProb`).

A quantity that is the same for every string, such as the inverse temperature, needs no entry,
since `F` may depend on it directly.  A quantity that varies within the thermal state enters only
through its distribution, which is also the same for every string.  So three things are left
out, each for a reason stated here.

* The string's bits, and so the bit the cell `x` shows, are left out because they are the
  possible outcomes of a measurement of the string, whose probabilities its state `ρ l` gives
  (Postulate 1), not a property of the crossing: half of them are 1s on average
  (`Qubit.half_bits_thermal`).
* The string's position on its ring, which is the qubit's phase (Postulate 1), is left out because
  the thermal state holds no phase: it is half the identity (`Qubit.Tick.state_eq`), since every
  state of a free string has one energy.
* The string's own energy is left out
  because it adds no state: the tick's factor multiplies both states of the string alike (Sec. IV.E,
  `Qubit.Tick.phase_unique`), so its two senses have one energy (`Qubit.Tick.energy_eq`), and the
  thermal state of the string's qubit, the Gibbs state over the two senses (`Qubit.Tick.state`),
  is the same whatever that energy is (`Qubit.Tick.state_eq`).  The
  energy differs from string to string with the mass a string holds (Sec. IV.E; its mean over the
  strings is one thermal energy of the horizon, `Main.string_energy`); `hthermal` of `state_same`
  gives each string the energy of its own tick's factor, `En` of it, whatever the function `En`. -/
noncomputable def crossingState (ρ : H.Loop → Register.Qubit.Op)
    (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ) (Pst : (H.Loop → Bool) → ℝ) (x : H.Cell)
    (l : H.Loop) : Register.Qubit.Op × ℝ × ((H.Loop → Bool) → ℝ) :=
  (ρ l, if h : x ∈ H.cells l then read l ⟨x, h⟩ else 0, Register.Entropy.correlation Pst l)

/-- **Without a mass the state is the same at every crossing** (Secs. II and IV.A).  Without a mass
every string's qubit is in the thermal state of its tick (`hthermal`); this is where "without a
mass" enters.

* The string's qubit is in the thermal state of its tick `T l` (`hthermal`, `Qubit.Tick.state`,
  thermodynamics).  Its two outcomes are the two senses (Sec. II), which have one energy, since the
  tick's phase changes alike in either sense, no law depending on the direction in which a ring
  passes through a cell (Postulate 2, `hsense` of `Qubit.Tick`): the tick multiplies both by one
  factor, and a string's energy is the energy of its factor (`Qubit.Tick.factor_eq`,
  `Qubit.Tick.energy_eq`); the thermal state, the Gibbs state over the two senses at their
  energies (`Qubit.Tick.state`), is half the identity (`Qubit.Tick.state_eq`):
  each sense has the probability `1/2` (`Qubit.Tick.prob_state`).
* The bits of the string's cells are the possible outcomes of one measurement of the qubit
  (Postulate 1): the outcome is the bit of the cell `x` with the probability `read l x`, each
  cell's bit one possible outcome among the `L` (`halike`).
* Between interactions the strings are free (Sec. II; Postulate 1 says what an interaction is), so
  the horizon's thermal state is the
  product of the strings' own (`hfree`), and no string is correlated with the others
  (`Entropy.correlation_jointProb`).

So the state seen at every crossing, `crossingState`, is `(1/2 · 1, 1/L, 0)`.  Half the bits of a
string in that state are 1s, on average (`Qubit.half_bits_thermal`). -/
theorem state_same [NeZero L] (T : H.Loop → Register.Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ)
    (ρ : H.Loop → Register.Qubit.Op) (hthermal : ∀ l, ρ l = (T l).state β En)
    (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ) (halike : ∀ l x, read l x = 1 / (L : ℝ))
    (Pst : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) (hfree : Pst = Register.Entropy.jointProb q) :
    ∀ l x, x ∈ H.cells l →
      crossingState ρ read Pst x l = ((1 / 2 : ℂ) • (1 : Register.Qubit.Op), 1 / (L : ℝ), 0) := by
  intro l x hx
  have hc : Register.Entropy.correlation Pst l = 0 := by
    funext ω
    rw [hfree]
    exact Register.Entropy.correlation_jointProb q l ω
  simp only [crossingState, hx, ↓reduceDIte, hthermal, (T l).state_eq, halike, hc]

/-- **The geometry is the same at every place and in every direction of the space the rings
describe** (Sec. IV.D).  The geometry of space at a slot, `geom`, is the curvature of the plane
normal to the slot's direction and the rate at which that curvature changes.  By Postulate 1's
first sentence applied to it, it is qubits (`hgeom`, `Symmetry.IsQubits`): it is read off the laws
and the state at the slot, as `Symmetry.lawAt` reads them.  The two clauses of Postulate 2 make
every law the same at every slot (`hsym`, `hdir`, `Symmetry.lawAt_same`).  The state is the same at
every crossing (`hs`, which `state_same` gives without a mass), so it is the same at every slot too
(`lawAt_const`).  So the geometry is the same at every slot of `described 𝒟`, the space the rings
describe (`Symmetry.IsQubits.eq_of_content_eq`): space has constant curvature and expands alike in
every direction. -/
theorem geometry_same {Slot V W G : Type*} (𝒟 : Set (H.Cell → H.Loop → Slot))
    (f : H.Cell → H.Loop → V)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l')
    (s : H.Cell → H.Loop → W)
    (hs : ∀ l x, x ∈ H.cells l → ∀ l' y, y ∈ H.cells l' → s x l = s y l')
    (geom : Slot → G)
    (hgeom : IsQubits (fun σ : described 𝒟 => (lawAt 𝒟 f σ, lawAt 𝒟 s σ))
      fun σ : described 𝒟 => geom σ)
    (σ τ : described 𝒟) : geom σ = geom τ :=
  hgeom.eq_of_content_eq (i := σ) (j := τ)
    (Prod.ext (lawAt_same 𝒟 f hsym hdir σ τ) (lawAt_const 𝒟 s hs σ τ))

/-- **The geometry is the same at every slot of the space at an instant** (Sec. IV.D).  The laws are
the same at every crossing by the two clauses of Postulate 2 (`hsym`, `hdir`); the state is the same
at every crossing (`hs`, which `state_same` gives without a mass); and by Postulate 1's first
sentence applied to it the geometry at a slot is qubits, read off the laws and the state there
(`hgeom`, `Symmetry.IsQubits`).  Here every drawing counts, not only the admissible ones
(`Set.univ`), so every slot is reached (`described_univ`).  Which crossing a drawing puts at a slot
does not matter, since the laws and the state are the same at every crossing (`lawAt_eq_of`).  This
is the input of the Killing–Hopf theorem, the geometry the same at every place and in every
direction (`Sources.Geometry.space_form`). -/
theorem geometry_same_slots {Slot V W G : Type*} (f : H.Cell → H.Loop → V)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l')
    (s : H.Cell → H.Loop → W)
    (hs : ∀ l x, x ∈ H.cells l → ∀ l' y, y ∈ H.cells l' → s x l = s y l')
    (geom : Slot → G)
    (hgeom : IsQubits (fun σ : described (Set.univ : Set (H.Cell → H.Loop → Slot)) =>
      (lawAt Set.univ f σ, lawAt Set.univ s σ)) fun σ => geom σ) :
    ∀ σ τ : Slot, geom σ = geom τ := by
  intro σ τ
  have hσ : σ ∈ described (Set.univ : Set (H.Cell → H.Loop → Slot)) := by
    rw [described_univ]
    trivial
  have hτ : τ ∈ described (Set.univ : Set (H.Cell → H.Loop → Slot)) := by
    rw [described_univ]
    trivial
  exact geometry_same Set.univ f hsym hdir s hs geom hgeom ⟨σ, hσ⟩ ⟨τ, hτ⟩

/-- the count's entropy density is positive -/
lemma eta_pos (R : Register.Reg) : 0 < R.η := by
  have := R.Ahor_pos
  have := R.ln2_pos
  have := R.kB_pos
  have := R.L_pos
  unfold Register.Reg.η Register.Reg.Shor Register.Reg.Rhor
  positivity

/-- **The vacuum equations, from Jacobson's step and the first law** (Sec. III).  The entropy density
is a law, the same on every local horizon (`Symmetry.one_density`, the two clauses of Postulate 2),
its value at one crossing, whatever that value is: without matter the value does not enter.
Jacobson's step at every point (`hcl`, thermodynamics) gives `R(k,k) = κT(k,k)` for every null
`k`, with `κ = 2πk_B/(ℏcη)`; with the first law (`hfirst`) and the contracted Bianchi identity
(`hbianchi`), Einstein's equations hold with one constant (`Einstein.einstein_equations`).  Without
matter (`hnm`) they are the vacuum equations (`Einstein.vacuum_of_field_equations`), and their
constant is `Λ`, the one that the Ricci tensor shows at a point (`hΛ`). -/
theorem vacuum_without_mass (R : Register.Reg) (η : H.Cell → H.Loop → ℝ)
    (hsymη : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, η (s.cellMap z) (s.loopMap l) = η z l)
    (hdirη : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → η x l = η x l')
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : x₀ ∈ H.cells l₀) (hη0 : η x₀ l₀ ≠ 0)
    (M : Register.Einstein.Spacetime)
    (hcl : ∀ η₀ : ℝ, η₀ ≠ 0 → (∀ l x, x ∈ H.cells l → η x l = η₀) → ∀ p k,
      Register.Einstein.IsNull k → Register.Einstein.quad (M.ric p) k =
        (2 * R.pi * R.kB / (R.ℏ * R.c * η₀)) * Register.Einstein.quad (M.stress p) k)
    (hfirst : ∀ p u, Register.Einstein.IsTimelike u → dotProduct (M.divStress p) u = 0)
    (hbianchi : ∀ (κ : ℝ) (φ : M.Pt → ℝ),
      (∀ p, M.ric p - κ • Register.Einstein.symmPart (M.stress p) = φ p • Register.Einstein.eta) →
      (∀ p, M.divStress p = 0) →
      ∀ p q, φ p + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress p)) =
        φ q + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress q)))
    (hnm : ∀ p, M.stress p = 0) (Λ : ℝ) (hΛ : ∃ p, M.ric p = Λ • Register.Einstein.eta) :
    Register.Einstein.VacuumEinstein M Set.univ Λ := by
  have hη := one_density η hsymη hdirη h₀ (η x₀ l₀) rfl
  obtain ⟨Λ', hE⟩ := Register.Einstein.einstein_equations M _ (hcl _ hη0 hη) hfirst (hbianchi _)
  have hV := Register.Einstein.vacuum_of_field_equations M _ Λ' hE Set.univ fun p _ => hnm p
  obtain ⟨p₀, hp₀⟩ := hΛ
  have e : Λ' = Λ := by
    have h1 := hV p₀ trivial
    rw [hp₀] at h1
    have h00 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 0) h1
    simp [Register.Einstein.eta, Matrix.diagonal] at h00
    linarith
  rw [← e]
  exact hV

/-- **Newton's constant from Jacobson's step, without the conservation law** (Sec. III):
`G = c³k_B/(4ℏη₀)`.  The entropy density is one law, `η₀` on every local horizon (`one_density`);
the count gives its value, at leading order in `1/L` (`Main.jacobson_G`) or exactly
(`Main.jacobson_G_exact`).
Jacobson's step (`hcl`) gives Einstein's equations up to a multiple of the metric
(`Einstein.einstein_up_to_metric`), and with them the static weak field of matter at rest at the
point `p` has the Ricci tensor `A = ∇²Φ/c²` times the identity (`hweak`, Lorentzian geometry).
There the stress tensor is `diag(ρc², 0, 0, 0)` (`hdust`), and Newton's law `∇²Φ = 4πGρ` defines
`G` (`hN`); the null vector `(1, 1, 0, 0)` gives `κ = 8πG/c⁴` (`Einstein.G_of_clausius`). -/
theorem jacobson_G_from_sources (R : Register.Reg) (G : ℝ) (η : H.Cell → H.Loop → ℝ)
    (hsymη : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, η (s.cellMap z) (s.loopMap l) = η z l)
    (hdirη : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → η x l = η x l')
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : x₀ ∈ H.cells l₀) (η₀ : ℝ) (hη₀ : η₀ ≠ 0)
    (hcount : η x₀ l₀ = η₀)
    (M : Register.Einstein.Spacetime)
    (hcl : ∀ η₀ : ℝ, η₀ ≠ 0 → (∀ l x, x ∈ H.cells l → η x l = η₀) → ∀ p k,
      Register.Einstein.IsNull k → Register.Einstein.quad (M.ric p) k =
        (2 * R.pi * R.kB / (R.ℏ * R.c * η₀)) * Register.Einstein.quad (M.stress p) k)
    (p : M.Pt) (A ρ : ℝ)
    (hweak : ∀ κ : ℝ, Register.Einstein.TraceFree M κ →
      M.ric p = A • (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (hρ : ρ ≠ 0) (hdust : M.stress p = Matrix.diagonal ![ρ * R.c ^ 2, 0, 0, 0])
    (hN : A = 4 * R.pi * G * ρ / R.c ^ 2) :
    G = R.c ^ 3 * R.kB / (4 * R.ℏ * η₀) := by
  have hη := one_density η hsymη hdirη h₀ η₀ hcount
  have h := hcl η₀ hη₀ hη
  have hR := hweak _ (Register.Einstein.einstein_up_to_metric M _ h)
  exact Register.Einstein.G_of_clausius hη₀ R.ℏ_pos.ne' R.c_pos.ne' hρ hR hdust (h p) hN

/-- **The cosmological constant, from the sources** (Sec. IV.D), every link named; the route of
`Space.cosmological_constant_of_sources`, with its first inputs derived here.

* The geometry of the space at an instant is the same at every slot (`geometry_same_slots`, from
  the two clauses of Postulate 2, the state without a mass, `state_same`, and Postulate 1's first
  sentence applied to the geometry, `hgeom`).
* Every geodesic of that space has a ring along it (`hclose`, Postulate 1's first sentence applied
  to the space at an instant), so it closes; with the geometry the same everywhere, Schur's lemma,
  Hopf–Rinow and the Killing–Hopf theorem make the space a space form (`hKH`, Riemannian geometry).
* The vacuum equations hold without a mass (`vacuum_without_mass`: Jacobson's step `hcl`, the first
  law `hfirst`, the contracted Bianchi identity `hbianchi`, no matter `hnm`, and `Λ` the vacuum's
  constant `hΛ`), and Einstein's constraint on the slice gives `3K = Λ` (`hcon`).
* The slice's rings make the form the sphere (`hslice`), and with the rings through the
  observer's cell `x₀` drawn in it (`hdrawn`, Sec. II's cell and Postulate 2's last sentence with
  its first clause) they make its group trivial (`Space.sphere_rings`).

Then `Λ = 3/R_Λ²`.  The drawn rings close with `Lℓ_c` and every great circle with `R.L ℓ_c`, so
`hdrawn` and `hslice` together give `L = R.L`; where that fails they cannot both hold. -/
theorem cosmological_constant_from_sources {Slot V Gm Sp : Type*} (R : Register.Reg) {Λ : ℝ}
    (P : H.Positions) (f : H.Cell → H.Loop → V)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l')
    [NeZero L] (T : H.Loop → Register.Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (ρ : H.Loop → Register.Qubit.Op)
    (hthermal : ∀ l, ρ l = (T l).state β En)
    (Pst : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) (hfree : Pst = Register.Entropy.jointProb q)
    (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ) (halike : ∀ l x, read l x = 1 / (L : ℝ))
    (geom : Slot → Gm)
    (hgeom : IsQubits (fun σ : described (Set.univ : Set (H.Cell → H.Loop → Slot)) =>
      (lawAt Set.univ f σ, lawAt Set.univ (crossingState ρ read Pst) σ)) fun σ => geom σ)
    (Closes : Slot → Prop) (hclose : ringsAlong H Set.univ Closes)
    (sp : Sp) (embedSp : (K : ℝ) → Space.SpaceForm K → Sp)
    (hKH : (∀ σ τ : Slot, geom σ = geom τ) → (∀ σ, Closes σ) →
      ∃ K, ∃ c : Space.SpaceForm K, sp = embedSp K c)
    (η : H.Cell → H.Loop → ℝ)
    (hsymη : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, η (s.cellMap z) (s.loopMap l) = η z l)
    (hdirη : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → η x l = η x l')
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : x₀ ∈ H.cells l₀) (hη0 : η x₀ l₀ ≠ 0)
    (M : Register.Einstein.Spacetime)
    (hcl : ∀ η₀ : ℝ, η₀ ≠ 0 → (∀ l x, x ∈ H.cells l → η x l = η₀) → ∀ p k,
      Register.Einstein.IsNull k → Register.Einstein.quad (M.ric p) k =
        (2 * R.pi * R.kB / (R.ℏ * R.c * η₀)) * Register.Einstein.quad (M.stress p) k)
    (hfirst : ∀ p u, Register.Einstein.IsTimelike u → dotProduct (M.divStress p) u = 0)
    (hbianchi : ∀ (κ : ℝ) (φ : M.Pt → ℝ),
      (∀ p, M.ric p - κ • Register.Einstein.symmPart (M.stress p) = φ p • Register.Einstein.eta) →
      (∀ p, M.divStress p = 0) →
      ∀ p q, φ p + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress p)) =
        φ q + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress q)))
    (hnm : ∀ p, M.stress p = 0) (hΛ : ∃ p, M.ric p = Λ • Register.Einstein.eta)
    (hcon : Register.Einstein.VacuumEinstein M Set.univ Λ →
      ∀ K (c : Space.SpaceForm K), sp = embedSp K c → 3 * K = Λ)
    (hslice : ∀ K (c : Space.SpaceForm K), sp = embedSp K c →
      Space.SliceIsQubits H (R.L * R.ℓc) c)
    (hdrawn : ∀ K Γ (hK : 0 < K) (hΓ : Space.SphereQuotient (1 / K) Γ),
      sp = embedSp K (Space.SpaceForm.sphere Γ hK hΓ) → Space.RingsDrawn H P (1 / K) Γ R.ℓc x₀) :
    Λ = 3 / R.RL ^ 2 := by
  have hstate := state_same T β En ρ hthermal read halike Pst q hfree
  have hs : ∀ l x, x ∈ H.cells l → ∀ l' y, y ∈ H.cells l' →
      crossingState ρ read Pst x l = crossingState ρ read Pst y l' :=
    fun l x hx l' y hy => (hstate l x hx).trans (hstate l' y hy).symm
  have hsame := geometry_same_slots f hsym hdir _ hs geom hgeom
  have hvac := vacuum_without_mass R η hsymη hdirη h₀ hη0 M hcl hfirst hbianchi hnm Λ hΛ
  exact Space.cosmological_constant_of_sources H P x₀ R geom hsame Closes hclose sp embedSp hKH M
    hvac hcon hslice hdrawn

/-- **Newton's constant, the cosmological constant, the horizon's temperature and the vacuum's
energy, from the sources** (Secs. III and IV.D).  The theorems of the chain keep three hypotheses
for brevity, and this theorem derives each from the sources and applies it.

* The horizon at `R_Λ` (`hdS`): `Λ = 3/R_Λ²` (`cosmological_constant_from_sources`), so the de
  Sitter solution's `f` vanishes at `R_Λ` (`Reg.deSitter`).
* Newton's constant (`hJ`): Jacobson's step without the conservation law, with Newton's law in the
  static weak field (`jacobson_G_from_sources`), at the count's density to leading order in `1/L`
  on the horizon of the solution without a mass (`hcount`), whose radius `rh` (`hrh`) the first
  link puts at `R_Λ` (`Reg.horizon_radius_eq`).
* The horizon's temperature in cells (`I1` in the form of the lap): a horizon is thermal with
  `k_BT = ℏ/τ`, `τ` the Gibbons–Hawking period `2πc/a` for its surface gravity `a` (`I1`,
  thermodynamics), taken at the horizon of the solution without a mass, `a = −g(r_h)`; the first
  link makes that surface gravity `a_Λ` (`Reg.surface_gravity_eq`) and the period the lap time
  `Lt_c` (`Reg.horizon_period`).

Then `G = c³ℓ_c²/(πℏ ln 2)`, `Λ = 3/R_Λ²`, `GΛ = 12πc³/(ℏL² ln 2)`, `k_BT = E_c/L`, and the
horizon's heat, its temperature times the entropy of its thermal state, is the vacuum's energy `E_Λ`
to relative order `2/L` (`Cosmo.vacuum_energy`, with the free strings `hfree` and the senses'
probabilities read off the strings' thermal states, `hq`). -/
theorem chain_from_sources {Slot V Gm Sp : Type*} (R : Register.Reg) {Λ : ℝ}
    (P : H.Positions) (f : H.Cell → H.Loop → V)
    (hsym : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, f (s.cellMap z) (s.loopMap l) = f z l)
    (hdir : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → f x l = f x l')
    [NeZero L] (T : H.Loop → Register.Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (ρ : H.Loop → Register.Qubit.Op)
    (hthermal : ∀ l, ρ l = (T l).state β En)
    (Pst : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) (hfree : Pst = Register.Entropy.jointProb q)
    (read : ∀ l : H.Loop, {X // X ∈ H.cells l} → ℝ) (halike : ∀ l x, read l x = 1 / (L : ℝ))
    (geom : Slot → Gm)
    (hgeom : IsQubits (fun σ : described (Set.univ : Set (H.Cell → H.Loop → Slot)) =>
      (lawAt Set.univ f σ, lawAt Set.univ (crossingState ρ read Pst) σ)) fun σ => geom σ)
    (Closes : Slot → Prop) (hclose : ringsAlong H Set.univ Closes)
    (sp : Sp) (embedSp : (K : ℝ) → Space.SpaceForm K → Sp)
    (hKH : (∀ σ τ : Slot, geom σ = geom τ) → (∀ σ, Closes σ) →
      ∃ K, ∃ c : Space.SpaceForm K, sp = embedSp K c)
    (η : H.Cell → H.Loop → ℝ)
    (hsymη : ∀ x y : H.Cell, ∃ s : H.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ H.cells l, η (s.cellMap z) (s.loopMap l) = η z l)
    (hdirη : ∀ x l l', x ∈ H.cells l → x ∈ H.cells l' → η x l = η x l')
    {l₀ : H.Loop} {x₀ : H.Cell} (h₀ : x₀ ∈ H.cells l₀) (rh : ℝ)
    (hcount : η x₀ l₀ = R.kB * (R.Rhor * R.ln2) / (4 * R.pi * rh ^ 2))
    (M : Register.Einstein.Spacetime)
    (hcl : ∀ η₀ : ℝ, η₀ ≠ 0 → (∀ l x, x ∈ H.cells l → η x l = η₀) → ∀ p k,
      Register.Einstein.IsNull k → Register.Einstein.quad (M.ric p) k =
        (2 * R.pi * R.kB / (R.ℏ * R.c * η₀)) * Register.Einstein.quad (M.stress p) k)
    (hfirst : ∀ p u, Register.Einstein.IsTimelike u → dotProduct (M.divStress p) u = 0)
    (hbianchi : ∀ (κ : ℝ) (φ : M.Pt → ℝ),
      (∀ p, M.ric p - κ • Register.Einstein.symmPart (M.stress p) = φ p • Register.Einstein.eta) →
      (∀ p, M.divStress p = 0) →
      ∀ p q, φ p + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress p)) =
        φ q + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress q)))
    (hnm : ∀ p, M.stress p = 0) (hΛ : ∃ p, M.ric p = Λ • Register.Einstein.eta)
    (hcon : Register.Einstein.VacuumEinstein M Set.univ Λ →
      ∀ K (c : Space.SpaceForm K), sp = embedSp K c → 3 * K = Λ)
    (hslice : ∀ K (c : Space.SpaceForm K), sp = embedSp K c →
      Space.SliceIsQubits H (R.L * R.ℓc) c)
    (hdrawn : ∀ K Γ (hK : 0 < K) (hΓ : Space.SphereQuotient (1 / K) Γ),
      sp = embedSp K (Space.SpaceForm.sphere Γ hK hΓ) → Space.RingsDrawn H P (1 / K) Γ R.ℓc x₀)
    (G : ℝ) (Mw : Register.Einstein.Spacetime)
    (hclw : ∀ η₀ : ℝ, η₀ ≠ 0 → (∀ l x, x ∈ H.cells l → η x l = η₀) → ∀ p k,
      Register.Einstein.IsNull k → Register.Einstein.quad (Mw.ric p) k =
        (2 * R.pi * R.kB / (R.ℏ * R.c * η₀)) * Register.Einstein.quad (Mw.stress p) k)
    (pw : Mw.Pt) (A ρw : ℝ)
    (hweak : ∀ κ : ℝ, Register.Einstein.TraceFree Mw κ →
      Mw.ric pw = A • (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (hρw : ρw ≠ 0) (hdust : Mw.stress pw = Matrix.diagonal ![ρw * R.c ^ 2, 0, 0, 0])
    (hN : A = 4 * R.pi * G * ρw / R.c ^ 2) (hrh : 0 < rh ∧ R.fSdS G 0 Λ rh = 0)
    (Temp : ℝ) (I1 : R.kB * Temp = R.ℏ / (R.La (-R.gSdS G 0 Λ rh) * R.tc))
    (hL : 4 ≤ L) (hRL : R.L = L)
    (hq : ∀ l, q l = Register.Qubit.prob ((T l).state β En) 0) :
    Λ = 3 / R.RL ^ 2 ∧ G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ * R.ln2) ∧
    G * Λ = 12 * R.pi * R.c ^ 3 / (R.ℏ * R.L ^ 2 * R.ln2) ∧
    R.kB * Temp = R.Ec / R.L ∧
    R.kB * Temp * Register.Bridge.horizonEntropy H Pst = R.EΛ * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  -- the count's density on the horizon is not zero
  have hη0 : η x₀ l₀ ≠ 0 := by
    rw [hcount]
    have := hrh.1; have := R.kB_pos; have := R.ln2_pos; have := R.pi_pos; have := R.L_pos
    unfold Register.Reg.Rhor
    positivity
  have hΛ' := cosmological_constant_from_sources R P f hsym hdir T β En ρ hthermal Pst q hfree
    read halike geom hgeom Closes hclose sp embedSp hKH η hsymη hdirη h₀ hη0 M hcl hfirst hbianchi
    hnm hΛ hcon hslice hdrawn
  have hdS := (R.deSitter G Λ).2 hΛ'
  -- the horizon of the solution without a mass is at `R_Λ`, so the count's density there is `η`
  have hr := R.horizon_radius_eq G Λ rh hdS hrh.1 hrh.2
  have hη : η x₀ l₀ = R.η := by rw [hcount, hr]; rfl
  have hJ := jacobson_G_from_sources R G η hsymη hdirη h₀ R.η (eta_pos R).ne' hη Mw hclw pw
    A ρw hweak hρw hdust hN
  -- the horizon's surface gravity, `−g(r_h)`, is `a_Λ`
  rw [R.surface_gravity_eq G Λ rh hdS hrh.1 hrh.2] at I1
  have hT := (R.horizon_temperature G Λ Temp hdS I1).2.1
  have hlap : R.kB * Temp = R.ℏ / (R.L * R.tc) := by
    rw [hT]
    unfold Register.Reg.tc Register.Reg.Ec
    have := R.c_pos; have := R.ℓc_pos; have := R.L_pos
    field_simp
  exact ⟨hΛ', (R.G_eq G hJ).1, (R.G_Lambda G Λ hJ hdS).1, hT,
    R.vacuum_energy H hL hRL Temp hlap T β En Pst q hfree hq⟩

/-! ### The hypotheses of the route can be met together -/

section Model

open Geodesic RealInnerProductSpace

/-- the Fano register's rings, with their decidable equality and finiteness in view for `decide` -/
instance : DecidableEq Horizon.fano.Loop := inferInstanceAs (DecidableEq (Fin 7))

instance : Fintype Horizon.fano.Loop := inferInstanceAs (Fintype (Fin 7))

/-- the trivial group is a quotient of the three-sphere -/
lemma sphereQuotient_bot (k : ℝ) :
    Space.SphereQuotient k
      (⊥ : Subgroup ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4)))) where
  iso g hg x y := by rw [Subgroup.mem_bot] at hg; subst hg; rfl
  time g hg x := by rw [Subgroup.mem_bot] at hg; subst hg; rfl
  free g hg _ _ _ := Subgroup.mem_bot.1 hg
  finite := by
    rw [Subgroup.coe_bot]
    exact Set.finite_singleton 1

/-- **A spacetime without matter in which the vacuum equations hold with `Λ`**, of one point. -/
noncomputable def vacuumSpacetime (Λ : ℝ) : Register.Einstein.Spacetime where
  Pt := Unit
  ric _ := Λ • Register.Einstein.eta
  stress _ := 0
  divStress _ := 0
  ric_symm _ := by
    unfold Matrix.IsSymm Register.Einstein.eta
    rw [Matrix.transpose_smul, Matrix.diagonal_transpose]

/-- in the vacuum spacetime both sides of Jacobson's relation vanish on every null vector -/
lemma vacuumSpacetime_clausius (Λ κ : ℝ) (p : (vacuumSpacetime Λ).Pt) (k : Fin 4 → ℝ)
    (hk : Register.Einstein.IsNull k) :
    Register.Einstein.quad ((vacuumSpacetime Λ).ric p) k =
      κ * Register.Einstein.quad ((vacuumSpacetime Λ).stress p) k := by
  show Register.Einstein.quad (Λ • Register.Einstein.eta) k = κ * Register.Einstein.quad 0 k
  rw [Register.Einstein.quad_smul, show Register.Einstein.quad Register.Einstein.eta k = 0 from hk]
  simp [Register.Einstein.quad]

/-- every spacelike geodesic of de Sitter space of radius `R_Λ` closes in the trivial quotient
with the length `Lℓ_c` (`Geodesic.IsGeodesic.hasLength`, `Quotients.closesIn_bot`) -/
lemma closes_deSitter (R : Register.Reg) {γ : Curve ℝ (EuclideanSpace ℝ (Fin 4))}
    (hg : IsGeodesic (R.RL ^ 2) γ) (hsp : IsSpacelike γ) :
    ClosesIn ((⊥ : Subgroup ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin 4)))) : Set ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ]
        (ℝ × EuclideanSpace ℝ (Fin 4)))) γ.pos (speed γ) (R.L * R.ℓc) := by
  have hRL := R.RL_pos
  have h := hg.hasLength (by positivity) hsp
  rw [Real.sqrt_sq hRL.le] at h
  have e : 2 * Real.pi * R.RL = R.L * R.ℓc := by
    have := R.pi_pos
    unfold Register.Reg.RL
    rw [R.pi_def]
    field_simp
  rw [e] at h
  exact closesIn_bot.2 h

/-- the curvature of the model's space at an instant, `1/R_Λ²` -/
noncomputable def modelK : ℝ := 1 / Register.Bridge.regSix.RL ^ 2

lemma modelK_pos : 0 < modelK := by
  have := Register.Bridge.regSix.RL_pos
  unfold modelK
  positivity

lemma one_div_modelK : 1 / modelK = Register.Bridge.regSix.RL ^ 2 := by
  unfold modelK
  rw [one_div_one_div]

/-- the model's space at an instant: the three-sphere of radius `R_Λ`, with the trivial group -/
noncomputable def modelSp : Σ K : ℝ, Space.SpaceForm K :=
  ⟨modelK, Space.SpaceForm.sphere ⊥ modelK_pos (sphereQuotient_bot _)⟩

/-! #### The rings through a cell of the Fano register, drawn -/

/-- the observer's cell of the model, `(0, false)` -/
def B0 : Horizon.fano.Cell := ((0 : Fin 7), false)

/-- the unit vector `e_i` of `ℝ⁴` -/
noncomputable def e4 (i : Fin 4) : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single i (1 : ℝ)

/-- two different rings through `B0` share only it and its opposite, `(0, true)` (stated on the
lines themselves, `Horizon.fanoLines`, for `decide`; a hypothesis `B0 ∈ fano.cells l` is one by
definition) -/
lemma fano_shared (l l' : Fin 7) (hne : l ≠ l')
    (hl : ((0 : Fin 7), false) ∈ Horizon.fanoLines l ×ˢ (univ : Finset Bool))
    (hl' : ((0 : Fin 7), false) ∈ Horizon.fanoLines l' ×ˢ (univ : Finset Bool)) (X : Fin 7 × Bool)
    (hX : X ∈ Horizon.fanoLines l ×ˢ (univ : Finset Bool))
    (hX' : X ∈ Horizon.fanoLines l' ×ˢ (univ : Finset Bool)) :
    X = ((0 : Fin 7), false) ∨ X = ((0 : Fin 7), true) := by
  revert l l' X; decide

/-- the direction of each ring through `B0`: `e₁`, `e₂`, `e₃` for the lines `0`, `4`, `6` -/
def fanoDir (l : Horizon.fano.Loop) : Fin 4 :=
  if Fin.val l = 0 then 1 else if Fin.val l = 4 then 2 else 3

lemma fanoDir_ne_zero (l : Horizon.fano.Loop) : fanoDir l ≠ 0 := by
  unfold fanoDir; split_ifs <;> decide

lemma fanoDir_inj (l l' : Horizon.fano.Loop)
    (hl : ((0 : Fin 7), false) ∈ Horizon.fanoLines l ×ˢ (univ : Finset Bool))
    (hl' : ((0 : Fin 7), false) ∈ Horizon.fanoLines l' ×ˢ (univ : Finset Bool))
    (h : fanoDir l = fanoDir l') : l = l' := by
  revert l l'; decide

lemma e4_norm (i : Fin 4) : ‖e4 i‖ = 1 := by simp [e4]

lemma e4_inner (i j : Fin 4) : ⟪e4 i, e4 j⟫ = if i = j then 1 else 0 := by
  simp [e4, EuclideanSpace.inner_single_left, PiLp.single_apply]

/-- the great circle of the model's ring `l` through `B0`: through `R_Λe₀` in the direction
`e_{fanoDir l}`, at the speed `R_Λ` -/
noncomputable def modelRing (l : Horizon.fano.Loop) : Curve ℝ (EuclideanSpace ℝ (Fin 4)) :=
  planeCurve ((0 : ℝ), Register.Bridge.regSix.RL • e4 0)
    ((0 : ℝ), Register.Bridge.regSix.RL • e4 (fanoDir l))

/-- the place of the cell `X` of the model's ring `l`: the point of its great circle at the angle
`jπ/3` from `R_Λe₀`, `j` the steps from `B0` along `l` -/
noncomputable def modelPlace (l : Horizon.fano.Loop) (X : Horizon.fano.Cell) :
    EuclideanSpace ℝ (Fin 4) :=
  Register.Bridge.regSix.RL •
    (Real.cos ((Horizon.fanoPositions.offset l B0 X : ℝ) * (Real.pi / 3)) • e4 0 +
      Real.sin ((Horizon.fanoPositions.offset l B0 X : ℝ) * (Real.pi / 3)) • e4 (fanoDir l))

/-- the component along `e_m` of a point of the model's ring `l` at the angle `θ` -/
lemma modelPlace_inner (l : Horizon.fano.Loop) (θ : ℝ) (m : Fin 4) :
    ⟪Register.Bridge.regSix.RL • (Real.cos θ • e4 0 + Real.sin θ • e4 (fanoDir l)), e4 m⟫ =
      Register.Bridge.regSix.RL * (Real.cos θ * (if (0 : Fin 4) = m then 1 else 0) +
        Real.sin θ * (if fanoDir l = m then 1 else 0)) := by
  rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, e4_inner,
    e4_inner]

/-- two angles in `[0, 2π)` with the same cosine and sine are one angle -/
lemma eq_of_cos_sin_eq {x y : ℝ} (hx : x ∈ Set.Ico 0 (2 * Real.pi))
    (hy : y ∈ Set.Ico 0 (2 * Real.pi)) (hc : Real.cos x = Real.cos y)
    (hs : Real.sin x = Real.sin y) : x = y := by
  have h1 : Real.cos (x - y) = 1 := by
    rw [Real.cos_sub, hc, hs, ← sq, ← sq, Real.cos_sq_add_sin_sq]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1
  have hpi := Real.pi_pos
  have h2 : (n : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by
    rw [hn]; linarith [hx.1, hx.2, hy.1, hy.2]
  have h3 : (-1 : ℝ) * (2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by
    rw [hn]; linarith [hx.1, hx.2, hy.1, hy.2]
  have hn1 : (n : ℝ) < 1 := lt_of_mul_lt_mul_right h2 (by positivity)
  have hn2 : (-1 : ℝ) < n := lt_of_mul_lt_mul_right h3 (by positivity)
  have hn0 : n = 0 := by
    have : n < 1 := by exact_mod_cast hn1
    have : -1 < n := by exact_mod_cast hn2
    omega
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul] at hn
  linarith

/-- `sin(jπ/3) = 0` with `j < 6` only for `j = 0` or `j = 3` -/
lemma sin_mul_pi_div_three_eq_zero {j : ℕ} (hj : j < 6)
    (h : Real.sin ((j : ℝ) * (Real.pi / 3)) = 0) : j = 0 ∨ j = 3 := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
  have h3 : ((3 * n : ℤ) : ℝ) * Real.pi = (j : ℝ) * Real.pi := by
    push_cast
    linear_combination 3 * hn
  have h3' : ((3 * n : ℤ) : ℝ) = (j : ℝ) := mul_right_cancel₀ Real.pi_ne_zero h3
  have h3'' : 3 * n = (j : ℤ) := by exact_mod_cast h3'
  omega

/-- the angle `jπ/3` of a cell `j < 6` steps on lies in `[0, 2π)` -/
lemma angle_mem_Ico {j : ℕ} (hj : j < 6) : (j : ℝ) * (Real.pi / 3) ∈ Set.Ico 0 (2 * Real.pi) := by
  have hpi := Real.pi_pos
  have hj5 : (j : ℝ) ≤ 5 := by exact_mod_cast (show j ≤ 5 by omega)
  constructor
  · positivity
  · have := mul_le_mul_of_nonneg_right hj5 (show (0 : ℝ) ≤ Real.pi / 3 by positivity)
    linarith

/-- **The rings through a cell of the Fano register, drawn on the three-sphere of radius `R_Λ`**
(`Space.RingsDrawn`, for `cosmological_constant_model`): the three largest rings through `B0`
run along the great circles through `R_Λe₀` in the directions `e₁`, `e₂`, `e₃` (`modelRing`), each
of length `6ℓ_c = 2πR_Λ`, with their cells at the angles `jπ/3`, `j` the steps from `B0`
(`modelPlace`).  Distinct cells sit at distinct points: on one circle the angles differ, and two
of the circles meet only at `±R_Λe₀`, the places of `B0` and of its opposite, the two cells they
share. -/
theorem rings_drawn_model :
    Space.RingsDrawn Horizon.fano Horizon.fanoPositions (1 / modelK)
      (⊥ : Subgroup ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
      Register.Bridge.regSix.ℓc B0 := by
  have hρ : 0 < Register.Bridge.regSix.RL := Register.Bridge.regSix.RL_pos
  have hℓ : Register.Bridge.regSix.ℓc = 1 := rfl
  have hL6 : Register.Bridge.regSix.L = 6 := rfl
  have hRL : Register.Bridge.regSix.RL = 3 / Real.pi := by
    unfold Register.Reg.RL
    rw [Register.Reg.pi_def, hℓ, hL6]
    have := Real.pi_pos
    field_simp
    ring
  -- the unit vectors
  have hform : ∀ i : Fin 4, form (((0 : ℝ), Register.Bridge.regSix.RL • e4 i) :
      ℝ × EuclideanSpace ℝ (Fin 4)) ((0 : ℝ), Register.Bridge.regSix.RL • e4 i) =
      Register.Bridge.regSix.RL ^ 2 := fun i => by
    rw [form_zero_zero, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      e4_norm]
    ring
  have hform' : ∀ i j : Fin 4, i ≠ j → form (((0 : ℝ), Register.Bridge.regSix.RL • e4 i) :
      ℝ × EuclideanSpace ℝ (Fin 4)) ((0 : ℝ), Register.Bridge.regSix.RL • e4 j) = 0 :=
    fun i j hij => by
      rw [form_zero_zero, real_inner_smul_left, real_inner_smul_right, e4_inner]
      simp [hij]
  -- the circles: geodesics of the sphere of radius `R_Λ`, spacelike, in space, at the speed `R_Λ`
  have hgeo : ∀ l, IsGeodesic (Register.Bridge.regSix.RL ^ 2) (modelRing l) := fun l =>
    planeCurve_isGeodesic (hform 0) (hform _) (hform' 0 _ (fanoDir_ne_zero l).symm)
  have hsp : ∀ l, IsSpacelike (modelRing l) := fun l =>
    planeCurve_spacelike (by positivity) (hform 0) (hform _) (hform' 0 _ (fanoDir_ne_zero l).symm)
  have hin : ∀ l, InSpace (modelRing l) := fun l t => by
    show (Real.cos t • (((0 : ℝ), Register.Bridge.regSix.RL • e4 0) : ℝ × EuclideanSpace ℝ (Fin 4)) +
      Real.sin t • ((0 : ℝ), Register.Bridge.regSix.RL • e4 (fanoDir l))).1 = 0
    simp
  have hspeed : ∀ l, speed (modelRing l) 0 = Register.Bridge.regSix.RL := fun l => by
    unfold speed modelRing
    rw [planeCurve_speed (hform 0) (hform _) (hform' 0 _ (fanoDir_ne_zero l).symm),
      Real.sqrt_sq hρ.le]
  have hpos : ∀ l t, (modelRing l).pos t =
      ((0 : ℝ), Register.Bridge.regSix.RL • (Real.cos t • e4 0 + Real.sin t • e4 (fanoDir l))) :=
    fun l t => by
      show Real.cos t • (((0 : ℝ), Register.Bridge.regSix.RL • e4 0) : ℝ × EuclideanSpace ℝ (Fin 4)) +
        Real.sin t • ((0 : ℝ), Register.Bridge.regSix.RL • e4 (fanoDir l)) = _
      refine Prod.ext (by simp) ?_
      simp only [Prod.snd_add, Prod.smul_snd]
      module
  -- the cell `j` steps on sits at the angle `jℓ_c/R_Λ = jπ/3`
  have hangle : ∀ l (j : ℕ), (j : ℝ) * Register.Bridge.regSix.ℓc / speed (modelRing l) 0 =
      j * (Real.pi / 3) := fun l j => by
    rw [hspeed, hRL, hℓ]
    have := Real.pi_pos
    field_simp
  -- in the trivial group two places are one when they are equal
  have hbot : ∀ u v : EuclideanSpace ℝ (Fin 4),
      (∃ g ∈ (⊥ : Subgroup ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4)))),
        ((0 : ℝ), u) = g ((0 : ℝ), v)) ↔ u = v := by
    intro u v
    constructor
    · rintro ⟨g, hg, e⟩
      rw [Subgroup.mem_bot] at hg
      subst hg
      exact (Prod.ext_iff.1 e).2
    · rintro rfl
      exact ⟨1, Subgroup.one_mem _, rfl⟩
  -- the angles of `B0` and of its opposite on any of its rings
  have hoB : ∀ l, Horizon.fanoPositions.offset l B0 ((0 : Fin 7), false) = 0 := fun l =>
    Horizon.fanoPositions.offset_self l B0
  have hoO : ∀ l, B0 ∈ Horizon.fano.cells l →
      Horizon.fanoPositions.offset l B0 ((0 : Fin 7), true) = 3 := fun l hl =>
    Horizon.fanoPositions.offset_opp_self (by norm_num) l B0 hl
  have e0 : ((0 : ℕ) : ℝ) * (Real.pi / 3) = 0 := by simp
  have e3 : ((3 : ℕ) : ℝ) * (Real.pi / 3) = Real.pi := by push_cast; ring
  refine ⟨fun l _ => modelRing l, fun l _ X => modelPlace l X, fun l _ => ⟨?_, ?_⟩, ?_, ?_⟩
  · -- a great circle of the sphere of radius `√(1/K) = R_Λ`
    rw [one_div_modelK]
    exact ⟨hgeo l, hin l, hsp l⟩
  · -- closing with `6ℓ_c = Lℓ_c`
    have h := closes_deSitter Register.Bridge.regSix (hgeo l) (hsp l)
    rw [hL6] at h
    exact_mod_cast h
  · -- the cell `j` steps from `B0` sits at its place
    intro l _ X _
    dsimp only
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hangle, hpos]
    rfl
  · -- distinct cells, distinct places
    intro l hl l' hl' X hX Y hY
    dsimp only
    rw [hbot]
    unfold modelPlace
    have hj := Horizon.fanoPositions.offset_lt l B0 X
    have hj' := Horizon.fanoPositions.offset_lt l' B0 Y
    constructor
    · intro h
      -- the components along `e₀`, `e_{fanoDir l}` and `e_{fanoDir l'}`
      have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => ⟪v, e4 0⟫) h
      have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => ⟪v, e4 (fanoDir l)⟫) h
      have hi' := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => ⟪v, e4 (fanoDir l')⟫) h
      simp only [modelPlace_inner] at h0 hi hi'
      simp only [fanoDir_ne_zero l, fanoDir_ne_zero l', ite_true, ite_false, mul_one, mul_zero,
        add_zero] at h0
      have hc : Real.cos ((Horizon.fanoPositions.offset l B0 X : ℝ) * (Real.pi / 3)) =
          Real.cos ((Horizon.fanoPositions.offset l' B0 Y : ℝ) * (Real.pi / 3)) :=
        mul_left_cancel₀ hρ.ne' h0
      by_cases hll' : l = l'
      · -- one circle: the angles are one, so the steps are, so the cells are
        subst hll'
        simp only [(fanoDir_ne_zero l).symm, ite_true, ite_false, mul_one, mul_zero, zero_add] at hi
        have hs := mul_left_cancel₀ hρ.ne' hi
        have hθ := eq_of_cos_sin_eq (angle_mem_Ico hj) (angle_mem_Ico hj') hc hs
        have hjj : (Horizon.fanoPositions.offset l B0 X : ℝ) =
            Horizon.fanoPositions.offset l B0 Y :=
          mul_right_cancel₀ (by positivity) hθ
        exact Horizon.fanoPositions.offset_inj l hX hY (by exact_mod_cast hjj)
      · -- two circles, meeting only at `±R_Λe₀`: both cells are `B0` or both its opposite
        have hdir : fanoDir l ≠ fanoDir l' := fun e => hll' (fanoDir_inj l l' hl hl' e)
        simp only [(fanoDir_ne_zero l).symm, (fanoDir_ne_zero l').symm, hdir, hdir.symm, ite_true,
          ite_false, mul_one, mul_zero, add_zero, zero_add] at hi hi'
        have hs : Real.sin ((Horizon.fanoPositions.offset l B0 X : ℝ) * (Real.pi / 3)) = 0 :=
          (mul_eq_zero.1 hi).resolve_left hρ.ne'
        have hs' : Real.sin ((Horizon.fanoPositions.offset l' B0 Y : ℝ) * (Real.pi / 3)) = 0 :=
          (mul_eq_zero.1 hi'.symm).resolve_left hρ.ne'
        rcases sin_mul_pi_div_three_eq_zero hj hs with h3 | h3 <;>
          rcases sin_mul_pi_div_three_eq_zero hj' hs' with h3' | h3'
        · rw [Horizon.fanoPositions.offset_inj l hX hl (h3.trans (hoB l).symm),
            Horizon.fanoPositions.offset_inj l' hY hl' (h3'.trans (hoB l').symm)]
        · exfalso
          rw [h3, h3', e0, e3, Real.cos_zero, Real.cos_pi] at hc
          norm_num at hc
        · exfalso
          rw [h3, h3', e0, e3, Real.cos_zero, Real.cos_pi] at hc
          norm_num at hc
        · rw [Horizon.fanoPositions.offset_inj l hX (Horizon.fano.opp_mem l _ hl)
            (h3.trans (hoO l hl).symm),
            Horizon.fanoPositions.offset_inj l' hY (Horizon.fano.opp_mem l' _ hl')
            (h3'.trans (hoO l' hl').symm)]
    · -- the same cell on two of the rings is `B0` or its opposite, at `±R_Λe₀`
      rintro rfl
      by_cases hll' : l = l'
      · subst hll'; rfl
      · rcases fano_shared l l' hll' hl hl' X hX hY with rfl | rfl
        · rw [hoB, hoB, e0, Real.sin_zero, zero_smul, zero_smul]
        · rw [hoO l hl, hoO l' hl', e3, Real.sin_pi, zero_smul, zero_smul]

/-- **The hypotheses of `cosmological_constant_from_sources` can be met together**, so it does not
hold vacuously.  The setting is the Fano register (`Horizon.fano`, `L = 6`, with its positions and
symmetries) and the register `Bridge.regSix`, with `Λ = 3/R_Λ²`.  The law is constant, and so is
the geometry, on the slots of `Unit`; each string's tick is the identity, in its thermal state at
`β = 1`; every slot closes.  The space at an instant is the three-sphere of radius `R_Λ` with the
trivial group (`modelSp`, in the type of all space forms); the spacetime is one point where the
Ricci tensor is `Λ` times the metric and there is no matter (`vacuumSpacetime`).  Every hypothesis
the statement lists then holds, and the four on the entropy density, which it does not list
(`hsymη`, `hdirη`, `h₀`, `hη0`), hold for any constant nonzero `η`, since Jacobson's relation is
proved here at every `κ`: that relation, with both sides zero on every null vector; the first law, with no
divergence; the contracted Bianchi identity, on one point; the vacuum's constant `Λ`; the
Killing–Hopf theorem and Einstein's constraint, `3/R_Λ² = Λ`; the rings of the slice, every great
circle closing with `Lℓ_c` (`closes_deSitter`); and the rings through the cell `(0, false)` drawn
along three great circles through `R_Λe₀`, their cells at the angles `jπ/3`, distinct cells at
distinct points (`rings_drawn_model`). -/
theorem cosmological_constant_model :
    let R := Register.Bridge.regSix
    let Λ : ℝ := 3 / R.RL ^ 2
    let f : fano.Cell → fano.Loop → ℝ := fun _ _ => 0
    let β : ℝ := 1
    let read : ∀ l : fano.Loop, {X // X ∈ fano.cells l} → ℝ := fun _ _ => 1 / (6 : ℝ)
    let T : fano.Loop → Register.Qubit.Tick 6 := fun _ =>
      ⟨1, ⟨1, by simp, by simp, by simp⟩⟩
    let ρ : fano.Loop → Register.Qubit.Op := fun l => (T l).state β (fun _ => 1)
    let q : fano.Loop → ℝ := fun _ => 1 / 2
    let Pst : (fano.Loop → Bool) → ℝ := Register.Entropy.jointProb q
    let geom : Unit → ℝ := fun _ => 0
    let Closes : Unit → Prop := fun _ => True
    let embedSp : (K : ℝ) → Space.SpaceForm K → (Σ K : ℝ, Space.SpaceForm K) := fun K c => ⟨K, c⟩
    let M := vacuumSpacetime Λ
    (∀ x y : fano.Cell, ∃ s : fano.Symmetry, s.cellMap x = y ∧
      ∀ l, ∀ z ∈ fano.cells l, f (s.cellMap z) (s.loopMap l) = f z l) ∧
    (∀ x l l', x ∈ fano.cells l → x ∈ fano.cells l' → f x l = f x l') ∧
    (∀ l, ρ l = (T l).state β (fun _ => 1)) ∧
    Pst = Register.Entropy.jointProb q ∧
    (∀ l x, read l x = 1 / ((6 : ℕ) : ℝ)) ∧
    IsQubits (fun σ : described (Set.univ : Set (fano.Cell → fano.Loop → Unit)) =>
      (lawAt Set.univ f σ, lawAt Set.univ (crossingState ρ read Pst) σ)) (fun σ => geom σ) ∧
    ringsAlong fano Set.univ Closes ∧
    ((∀ σ τ : Unit, geom σ = geom τ) → (∀ σ, Closes σ) →
      ∃ K, ∃ c : Space.SpaceForm K, modelSp = embedSp K c) ∧
    (∀ κ : ℝ, ∀ p k, Register.Einstein.IsNull k →
      Register.Einstein.quad (M.ric p) k = κ * Register.Einstein.quad (M.stress p) k) ∧
    (∀ p u, Register.Einstein.IsTimelike u → dotProduct (M.divStress p) u = 0) ∧
    (∀ (κ : ℝ) (φ : M.Pt → ℝ),
      (∀ p, M.ric p - κ • Register.Einstein.symmPart (M.stress p) = φ p • Register.Einstein.eta) →
      (∀ p, M.divStress p = 0) →
      ∀ p q, φ p + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress p)) =
        φ q + κ / 2 * Register.Einstein.trace (Register.Einstein.symmPart (M.stress q))) ∧
    (∀ p, M.stress p = 0) ∧ (∃ p, M.ric p = Λ • Register.Einstein.eta) ∧
    (Register.Einstein.VacuumEinstein M Set.univ Λ →
      ∀ K (c : Space.SpaceForm K), modelSp = embedSp K c → 3 * K = Λ) ∧
    (∀ K (c : Space.SpaceForm K), modelSp = embedSp K c → Space.SliceIsQubits fano (R.L * R.ℓc) c) ∧
    (∀ K Γ (hK : 0 < K) (hΓ : Space.SphereQuotient (1 / K) Γ),
      modelSp = embedSp K (Space.SpaceForm.sphere Γ hK hΓ) →
      Space.RingsDrawn fano fanoPositions (1 / K) Γ R.ℓc B0) := by
  intro R Λ f β read T ρ q Pst geom Closes embedSp M
  have hRL := R.RL_pos
  have h3 : 3 * modelK = Λ := by
    show 3 * (1 / R.RL ^ 2) = 3 / R.RL ^ 2
    ring
  refine ⟨fun x y => (fano_homogeneous x y).imp fun _ hs => ⟨hs, fun _ _ _ => rfl⟩,
    fun _ _ _ _ _ => rfl, fun _ => rfl, rfl, fun _ _ => by norm_num [read],
    ⟨fun _ => 0, fun _ => rfl⟩, fun σ _ => (mem_described_admissible _ σ).2 ⟨trivial, trivial⟩,
    fun _ _ => ⟨_, _, rfl⟩, fun κ p k hk => vacuumSpacetime_clausius Λ κ p k hk,
    fun _ u _ => zero_dotProduct u, fun _ _ _ _ _ _ => rfl, fun _ => rfl, ⟨(), rfl⟩, ?_, ?_, ?_⟩
  · intro _ K c hc
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hc
    exact h3
  · intro K c hc
    obtain ⟨rfl, hc'⟩ := Sigma.mk.inj_iff.1 hc
    rw [← eq_of_heq hc']
    intro γ hγ
    have hγ' : γ ∈ Space.sphereSlots (R.RL ^ 2) := by
      rw [← one_div_modelK]; exact hγ
    exact (mem_described_admissible _ γ).2 ⟨hγ, closes_deSitter R hγ'.1 hγ'.2.2⟩
  · rintro K Γ hK hΓ hc
    obtain ⟨rfl, hc'⟩ := Sigma.mk.inj_iff.1 hc
    have hΓ' := eq_of_heq hc'
    injection hΓ' with hΓeq
    subst hΓeq
    exact rings_drawn_model

end Model

end Solution
