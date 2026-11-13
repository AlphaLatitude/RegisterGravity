import RegisterGravity.Galactic
import RegisterGravity.RouteB
import RegisterGravity.Crossing
import RegisterGravity.Geodesics
import RegisterGravity.Models
import RegisterGravity.DeSitter
import RegisterGravity.Entropy
import RegisterGravity.Qubit

/-!
# The count and the chain, joined

`Horizon.lean` and `RouteB.lean` count the cells and rings of a `Horizon L`, with `L` a natural
number.  `Chain.lean` and `Galactic.lean` derive the laws over a register `Reg` whose `L` is a
positive real, with the horizon's counts entered as `L²/2` and `L²/4`.  The theorems here join them
for any register whose `L` is that of the horizon:

* `counts_exact`: the rings and cells of the horizon number the chain's `R_hor = L²/4` and
  `C_hor = L²/2` times `1 − 2/L + 4/L²` (Eq. (counts) with `Reg.counts_leading_order`), so the
  chain's counts are the horizon's to relative order `2/L`;
* `horizonWeight`, `horizonWeight_quarter`: with its horizon `x` cells from the body
  (`horizonWeight`), the count's horizon taken to be the solution's, at the proper distance
  `Lℓ_c/4` (`Reg.proper_distance`), since a ring's cells, segments of length `ℓ_c` of its geodesic,
  measure proper distance along it (`hx` of `Main.horizon_quarter`; Postulate 2's last sentence):
  then `x = L/4` (`Main.horizon_quarter`), and a cell's weight inside that horizon is the count's
  (`horizonWeight_quarter`); `ring_distance_model` shows
  that the hypotheses can be met.
* `horizon_entropy_count`: every largest ring has half its cells inside any observer's horizon,
  and at one bit per ring the horizon's entropy, `card Loop · ln 2`, is the chain's `S_hor` to
  relative order `2/L`; a ring's share of the horizon's area is that area over this count.
* `horizon_entropy`: the bit per ring, Eq. (S).  The two senses of a free string have the same
  energy (Postulate 2, no law depends on the direction), so the horizon's Boltzmann weighting
  weights them equally, and the strings on the rings hold `card Loop · ln 2`.  A free string's
  own thermal state is half the identity (`Qubit.Tick.state_eq`: every state of a free string has
  one energy), so each of its two outcomes has the probability `1/2` and it holds exactly one bit
  (`Main.string_one_bit`).
* `sphere_strings`: the strings of a sphere (Sec. II, "Counting in the bulk").  With the largest
  rings drawn as great circles of the three-sphere of radius `R_Λ`, a sphere of areal radius `r`
  holds, averaged over its position, the number of rings times `(r/R_Λ)²`
  (`Crossing.Drawing.meanStrings_eq`, Archimedes' hat-box theorem in four dimensions).  With the
  register's count of rings this is the chain's `N_s(r) = (L²/4)(r/R_Λ)²`, Eq. (N), times
  `1 − 2/L + 4/L²`: on average, one string for each ring's share of the sphere's area, `4ℓ_c²/π`,
  at every radius.  The count about a given position depends on how the rings are drawn, which the
  postulates do not fix; the average does not.  Averaged over the rotations `x ↦ φ⁻¹(qφ(x))` of the
  drawing, with `q` a unit quaternion and `φ` an isometry of the space onto `ℍ`, the count about any
  point is the average, exactly, in any four-dimensional space (`Center.sphere_strings_centered_of`,
  `Center.sphere_strings_of_rings_centered`).
* `sphere_strings_of_rings`, `sphere_strings_deSitter`: the same count with the drawing derived.
  If every largest ring is a closed geodesic of the space at an instant of de Sitter space with the
  cosmological constant `Λ`, then `Λ > 0`, since a spacelike ring needs that space, the quadric
  `form X X = 3/Λ`, to be a sphere; `Λ = 3/R_Λ²`, that space is the three-sphere of radius `R_Λ`,
  and the rings are its great circles (`Geodesics.lean`).  `sphere_strings_model` shows that the
  hypotheses of `sphere_strings_of_rings` can be met together.
* `ring_through_two_cells`: the last sentence of Postulate 2, that every largest ring is a closed
  geodesic of space, matches the register on pairs of cells: two cells that are not opposite lie on
  exactly one largest ring, and two points of space that are not antipodal lie on exactly one
  geodesic (`TwoCells.geodesic_through_two`).

The paper's definition of a cell, one bit of each ring through it, gives each largest ring exactly
one string, a bit on each of its cells; so the horizon's state is one sense, or one outcome, for
each ring, the type `H.Loop → Bool` of `horizon_entropy`, and the entropy sums one bit for each
ring.
-/

open Finset

namespace Register
namespace Bridge

variable {L : ℕ} (H : Horizon L) (R : Reg)

/-- **The exact counts in the chain's terms** (Sec. II, Eq. (counts)).  For a register whose `L`
is that of the horizon `H`, `L ≥ 4`, the largest rings of `H` number `R_hor (1 − 2/L + 4/L²)` and
its cells `C_hor (1 − 2/L + 4/L²)`, with the chain's `R_hor = L²/4` and `C_hor = L²/2`. -/
theorem counts_exact (hL : 4 ≤ L) (hRL : R.L = L) :
    (Fintype.card H.Loop : ℝ) = R.Rhor * (1 - 2 / R.L + 4 / R.L ^ 2) ∧
    (Fintype.card H.Cell : ℝ) = R.Chor * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  obtain ⟨-, hC, hR, -⟩ := H.counts hL
  have hC' : 2 * (Fintype.card H.Cell : ℝ) + 2 * L = (L : ℝ) ^ 2 + 4 := by exact_mod_cast hC
  have hR' : 4 * (Fintype.card H.Loop : ℝ) + 2 * L = (L : ℝ) ^ 2 + 4 := by exact_mod_cast hR
  obtain ⟨h1, h2⟩ := R.counts_leading_order
  rw [← h1, ← h2, hRL]
  constructor <;> linarith

/-- **Half of every ring lies inside every horizon** (Sec. II, "What the manifold contributes";
Sec. IV.D).  Every largest ring has half its cells inside any observer's horizon, counting a cell on
it as half (`Horizon.Positions.horizon_weight_ring`), so every ring crosses the horizon
(`Horizon.Positions.crossesHorizon`), and the horizon counts every ring
(`horizon_counts_every_ring`).  At one bit per ring (`horizon_entropy`) the horizon's entropy is
`card Loop · ln 2`, which is the chain's `S_hor = (L²/4) ln 2` times `1 − 2/L + 4/L²`
(`counts_exact`).  A ring's share of the horizon's area, `A_hor/R` (`Reg.ringShare`), is then the
solution's area over this count, a quotient, not an identification. -/
theorem horizon_entropy_count [NeZero L] (P : H.Positions) (hL : 4 ≤ L) (hRL : R.L = L)
    (B : H.Cell) :
    (∀ l : H.Loop,
      ∑ X ∈ H.cells l, Horizon.Positions.weight (L := L) (P.dist B X) = (L : ℝ) / 2) ∧
    (Fintype.card H.Loop : ℝ) * R.ln2 = R.Shor * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  refine ⟨fun l => P.horizon_weight_ring hL B l, ?_⟩
  rw [(counts_exact H R hL hRL).1]
  unfold Reg.Shor
  ring

/-- **A horizon's entropy** (Sec. II, "The entropy"; Sec. III): the Shannon entropy of the
horizon's state `P`.  A horizon is thermal, so its entropy is that of its thermal state
(thermodynamics, Sec. III).  That state is a state of the strings and of nothing else: the
horizon's entropy depends only on strings.  This is Postulate 1's second sentence, a state a linear
combination of outcomes of its qubits, with the first, every physical law and quantity defined by
qubits (the thesis of the paper): a horizon's state that depended on anything else would not be
defined by qubits.  It enters here as the type of the state.  `P` is a distribution on the strings' senses, `H.Loop → Bool`; the probability of a
string's first sense is the weight of its first outcome in the thermal state of its tick, the
senses being the outcomes (`hq` of `horizon_entropy`, thermodynamics with Sec. II's reading); on
a string's own thermal state, in the basis of its outcomes, the entropy is the same, one bit
(`Main.string_one_bit`), so the type loses nothing.  The state is the whole register's, so it is a distribution on the senses of every string,
`l : H.Loop`: no string is left out.  What the state is, the product of the strings' own thermal
states, is the hypothesis of `horizon_entropy`. -/
noncomputable def horizonEntropy (P : (H.Loop → Bool) → ℝ) : ℝ := Entropy.shannon P

/-- **The entropy of the strings adds** (known mathematics, `Entropy.shannon_jointProb`): the
entropy of a state that is the product of one distribution per string, the strings independent, is
the sum over the strings of the binary entropy of each string's sense probability. -/
theorem horizonEntropy_eq_sum (q : H.Loop → ℝ) :
    horizonEntropy H (Entropy.jointProb q) = ∑ l, Real.binEntropy (q l) :=
  Entropy.shannon_jointProb q

/-- **The bit per ring**, Eq. (S) (Sec. II, "The entropy").  A horizon's entropy is that of its
state, a state of the strings alone (`horizonEntropy`).  Between interactions the strings are
free, so the state is the product of the strings' own thermal states (`hfree`, Sec. II), and it
is the sum of their binary entropies (`horizonEntropy_eq_sum`).  A free string's two senses are
the two outcomes of its qubit (Sec. II), and the qubit is in the thermal state of its tick
(`Qubit.Tick.state`, thermodynamics), so the probability of the first sense is that state's weight
on the first outcome (`hq`).  The tick keeps each string of one sense up to one and the same
factor, since the shift leaves it as it is up to its global phase and that phase changes alike in
either sense, no law depending on the ring's direction (Sec. II, Postulates 1 and 2; `hsense` of
`Qubit.Tick`), so the two senses have one energy and the thermal state is half the identity: each
sense has the
probability `1/2` (`Qubit.Tick.prob_state`), and two senses weighted equally hold one bit
(`Reg.one_bit`).  On a string's own thermal state the entropy is the same (`Main.string_one_bit`).
So the entropy is `card Loop · ln 2`, which is the chain's `S_hor = (L²/4) ln 2` times
`1 − 2/L + 4/L²` (`counts_exact`); the definition `Reg.Shor` is the entropy of the strings to
relative order `2/L`. -/
theorem horizon_entropy (hL : 4 ≤ L) (hRL : R.L = L) [NeZero L] (T : H.Loop → Qubit.Tick L)
    (β : ℝ) (En : ℂ → ℝ) (P : (H.Loop → Bool) → ℝ) (q : H.Loop → ℝ) (hfree : P = Entropy.jointProb q)
    (hq : ∀ l, q l = Qubit.prob ((T l).state β En) 0) :
    horizonEntropy H P = Fintype.card H.Loop * Real.log 2 ∧
    (Fintype.card H.Loop : ℝ) * Real.log 2 = R.Shor * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  constructor
  · rw [hfree, horizonEntropy_eq_sum]
    have h : ∀ l, Real.binEntropy (q l) = Real.log 2 := by
      intro l
      rw [hq l, Qubit.Tick.prob_state]
      exact Reg.one_bit.1
    rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · rw [(counts_exact H R hL hRL).1, ← R.ln2_def]
    unfold Reg.Shor
    ring

/-- **The horizon counts every ring**, Eq. (S) (Sec. II, "What the manifold contributes" and "The
entropy").  A horizon's entropy is that of its state, a state of the whole register, so of every
string (`horizonEntropy`).  Each string holds one bit, its two senses being the two outcomes of
its qubit, which have one energy (`hsense` of `Qubit.Tick`) and so equal thermal weight
(`horizon_entropy`), so the entropy is `card Loop · ln 2`,
the chain's `S_hor = (L²/4) ln 2` times `1 − 2/L + 4/L²`.  The count and the horizon also agree
ring by ring: every ring crosses every observer's horizon, with half its cells inside
(`Horizon.Positions.crossesHorizon`), so no string lies wholly inside a horizon or wholly beyond
it. -/
theorem horizon_counts_every_ring [NeZero L] (Pos : H.Positions) (hL : 4 ≤ L) (hRL : R.L = L)
    (B : H.Cell) (T : H.Loop → Qubit.Tick L) (β : ℝ) (En : ℂ → ℝ) (P : (H.Loop → Bool) → ℝ)
    (q : H.Loop → ℝ) (hfree : P = Entropy.jointProb q)
    (hq : ∀ l, q l = Qubit.prob ((T l).state β En) 0) :
    (∀ l, Pos.CrossesHorizon B l) ∧
    horizonEntropy H P = R.Shor * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  refine ⟨fun l => Pos.crossesHorizon hL B l, ?_⟩
  obtain ⟨h1, h2⟩ := horizon_entropy H R hL hRL T β En P q hfree hq
  rw [h1, h2]

/-- **The strings of a sphere**, Eq. (N) (Sec. II, "Counting in the bulk").  Let the register's
largest rings be drawn as great circles of the three-sphere of radius `R_Λ`, the solution's space
at an instant (`Crossing.Drawing`, Sec. IV.D), in a four-dimensional real inner product space `E`
with a Haar measure `μ`.  Let the sphere be the points at distance `s` from a point of the
three-sphere, no larger than a great sphere, `0 < s` and `s² ≤ 2R_Λ²`, with areal radius `r`,
`r² = s² − s⁴/4R_Λ²` (`Crossing.Drawing.meanStrings_eq`).  Averaged over the sphere's position, with no
position preferred, it holds the number of rings times `(r/R_Λ)²`
(`Crossing.Drawing.meanStrings_eq`), and the rings of `H` number `R_hor (1 − 2/L + 4/L²)`
(`counts_exact`).  So, averaged over its position, the sphere holds the chain's
`N_s(r) = R_hor (r/R_Λ)²` strings, Eq. (N), times `1 − 2/L + 4/L²`: one for each ring's share of
its area, `4πr²/ringShare`, the same average density at every radius.  The drawing keeps only the
rings, as great circles; where on them the cells lie it does not use.  At the horizon's own radius, `s² = 2R_Λ²` and `r = R_Λ`, the
sphere holds every ring from almost every position, which the register gives on its own
(`horizon_entropy_count`).  With `R.pi` the real `π`, a great circle of radius `R_Λ` has the length
`Lℓ_c` of a largest ring and `4πr²` is the sphere's area; the equalities hold for any `R.pi`. -/
theorem sphere_strings (hL : 4 ≤ L) (hRL : R.L = L) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (hE : Module.finrank ℝ E = 4)
    (D : Crossing.Drawing H.Loop E R.RL) {s r : ℝ} (hs0 : 0 < s) (hs : s ^ 2 ≤ 2 * R.RL ^ 2)
    (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * R.RL ^ 2)) :
    D.meanStrings μ s = R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) ∧
    D.meanStrings μ s = R.Rhor * (r / R.RL) ^ 2 * (1 - 2 / R.L + 4 / R.L ^ 2) ∧
    D.meanStrings μ s = 4 * R.pi * r ^ 2 / R.ringShare * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  rw [D.meanStrings_eq μ hE R.RL_pos hs0 hs hr, (counts_exact H R hL hRL).1]
  obtain ⟨h1, h3⟩ := R.ratio_of_areas r
  refine ⟨?_, by ring, ?_⟩
  · rw [h1]
    ring
  · rw [← h3, h1]
    ring

/-- **The strings of a sphere, with the rings as closed geodesics of space** (Sec. II, "Counting in
the bulk"; Sec. IV.D).  Let every largest ring of `H`, of length `Lℓ_c`, be a closed spacelike
geodesic of the space at an instant of de Sitter space of radius `ρ` (`Geodesic.IsGeodesic`,
`Geodesic.InSpace`, `Geodesic.HasLength`), in a four-dimensional real inner product space `E` with a
Haar measure `μ`.  Then `ρ = R_Λ`, with `R.pi` the real `π`, since every such geodesic has the
length `2πρ` (`Geodesic.IsGeodesic.hasLength`); the rings are great circles of the three-sphere of
radius `R_Λ` (`Crossing.Drawing.ofRings`, `Geodesic.ofRings_circle`); and, averaged over its
position, a sphere of areal radius `r` holds `N_s(r)(1 − 2/L + 4/L²)` strings
(`sphere_strings`). -/
theorem sphere_strings_of_rings (hL : 4 ≤ L) (hRL : R.L = L)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (hE : Module.finrank ℝ E = 4) {ρ : ℝ} (hρ : 0 < ρ) (γ : H.Loop → Geodesic.Curve ℝ E)
    (hgeo : ∀ l, Geodesic.IsGeodesic (ρ ^ 2) (γ l)) (hsp : ∀ l, Geodesic.IsSpacelike (γ l))
    (hin : ∀ l, Geodesic.InSpace (γ l)) (hlen : ∀ l, Geodesic.HasLength (γ l) (R.L * R.ℓc))
    {s r : ℝ} (hs0 : 0 < s) (hs : s ^ 2 ≤ 2 * ρ ^ 2) (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * ρ ^ 2)) :
    ρ = R.RL ∧
    (Crossing.Drawing.ofRings hρ γ hgeo hsp hin).meanStrings μ s =
      R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  -- a ring exists
  obtain ⟨-, -, hR, -⟩ := H.counts hL
  have hpos : 0 < Fintype.card H.Loop := by
    rcases Nat.eq_zero_or_pos (Fintype.card H.Loop) with h0 | h0
    · rw [h0] at hR
      nlinarith
    · exact h0
  obtain ⟨l₀⟩ := Fintype.card_pos_iff.1 hpos
  -- its length gives the radius of space
  have h1 := (hlen l₀).unique ((hgeo l₀).hasLength (by positivity) (hsp l₀))
  rw [Real.sqrt_sq hρ.le] at h1
  have hρeq : ρ = R.RL := by
    have := R.pi_pos
    unfold Reg.RL
    rw [R.pi_def, h1]
    field_simp
  refine ⟨hρeq, ?_⟩
  subst hρeq
  exact (sphere_strings H R hL hRL μ hE _ hs0 hs hr).1

open RealInnerProductSpace in
/-- **The strings of a sphere in de Sitter space with the cosmological constant `Λ`** (Secs. II and
IV.D).  Let every largest ring of `H`, of length `Lℓ_c`, be a closed spacelike geodesic of the space
at an instant of de Sitter space with the cosmological constant `Λ`, the quadric `form X X = 3/Λ`
of `ℝ × E`, as the last sentence of Postulate 2 says.  Then `Λ > 0`, since in the space at an
instant the quadric is the sphere `‖x‖² = 3/Λ`, on which a spacelike ring needs `3/Λ > 0`; and
`Λ = 3/R_Λ²`; the rings are the great circles of a drawing on the
three-sphere of radius `R_Λ`, each the path of its geodesic; and, averaged over its position, a
sphere of areal radius `r` holds `N_s(r)(1 − 2/L + 4/L²)` strings (`sphere_strings_of_rings`).  The
theorem takes de Sitter space as the solution. -/
theorem sphere_strings_deSitter (hL : 4 ≤ L) (hRL : R.L = L)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (hE : Module.finrank ℝ E = 4) {Λ : ℝ} (γ : H.Loop → Geodesic.Curve ℝ E)
    (hgeo : ∀ l, Geodesic.IsGeodesic (3 / Λ) (γ l)) (hsp : ∀ l, Geodesic.IsSpacelike (γ l))
    (hin : ∀ l, Geodesic.InSpace (γ l)) (hlen : ∀ l, Geodesic.HasLength (γ l) (R.L * R.ℓc))
    {s r : ℝ} (hs0 : 0 < s) (hs : s ^ 2 ≤ 2 * R.RL ^ 2)
    (hr : r ^ 2 = s ^ 2 - s ^ 4 / (4 * R.RL ^ 2)) :
    0 < Λ ∧ Λ = 3 / R.RL ^ 2 ∧
    ∃ D : Crossing.Drawing H.Loop E R.RL,
      (∀ l, Crossing.greatCircle (D.a l) (D.b l) = Set.range (fun t => ((γ l).pos t).2)) ∧
      D.meanStrings μ s = R.Ns r * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  -- a ring exists
  obtain ⟨-, -, hR, -⟩ := H.counts hL
  have hpos : 0 < Fintype.card H.Loop := by
    rcases Nat.eq_zero_or_pos (Fintype.card H.Loop) with h0 | h0
    · rw [h0] at hR
      nlinarith
    · exact h0
  obtain ⟨l₀⟩ := Fintype.card_pos_iff.1 hpos
  -- `Λ > 0`: in the space at an instant the quadric is the sphere `‖x‖² = 3/Λ`, and a ring moves
  have hk : 0 < 3 / Λ := by
    by_contra hneg0
    have hneg : 3 / Λ ≤ 0 := not_lt.1 hneg0
    have hx : ∀ t, ((γ l₀).pos t).2 = 0 := fun t => by
      have e := (hgeo l₀).1 t
      unfold Geodesic.form at e
      rw [hin l₀ t, inner_zero_left, neg_zero, zero_add] at e
      have h0 : ⟪((γ l₀).pos t).2, ((γ l₀).pos t).2⟫ = 0 :=
        le_antisymm (e ▸ hneg) real_inner_self_nonneg
      exact inner_self_eq_zero.1 h0
    have hv : ((γ l₀).vel 0).2 = 0 := by
      have d := (γ l₀).hpos2 0
      rw [show (fun u => ((γ l₀).pos u).2) = fun _ => (0 : E) from funext hx] at d
      exact d.unique (hasDerivAt_const 0 0)
    have := hsp l₀ 0
    unfold Geodesic.form at this
    rw [(hin l₀).vel_fst 0, hv] at this
    simp at this
  have hΛ : 0 < Λ := (div_pos_iff_of_pos_left (by norm_num)).1 hk
  -- the radius of space
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, Real.sqrt (3 / Λ) = ρ := ⟨_, rfl⟩
  have hρ : 0 < ρ := hρdef ▸ Real.sqrt_pos.2 hk
  have hρ2 : ρ ^ 2 = 3 / Λ := by rw [← hρdef, Real.sq_sqrt hk.le]
  have hgeo' : ∀ l, Geodesic.IsGeodesic (ρ ^ 2) (γ l) := fun l => by rw [hρ2]; exact hgeo l
  have h1 := (hlen l₀).unique ((hgeo' l₀).hasLength (by positivity) (hsp l₀))
  rw [Real.sqrt_sq hρ.le] at h1
  have hρeq : ρ = R.RL := by
    have := R.pi_pos
    unfold Reg.RL
    rw [R.pi_def, h1]
    field_simp
  subst hρeq
  refine ⟨hΛ, ?_, Crossing.Drawing.ofRings hρ γ hgeo' hsp hin,
    Geodesic.ofRings_circle hρ γ hgeo' hsp hin, ?_⟩
  · rw [hρ2]
    field_simp
  · exact (sphere_strings_of_rings H R hL hRL μ hE hρ γ hgeo' hsp hin hlen hs0 hs hr).2

/-- **Two cells that are not opposite lie on exactly one largest ring** (Postulate 2, second
clause), as two points of space that are not antipodal lie on exactly one geodesic of space
(`TwoCells.geodesic_through_two`): the register's side of the match that Sec. II notes for the last
sentence of Postulate 2. -/
theorem ring_through_two_cells (x y : H.Cell) (hyx : y ≠ x) (hyo : y ≠ H.opp x) :
    ∃! l : H.Loop, x ∈ H.cells l ∧ y ∈ H.cells l := by
  obtain ⟨l, hx, hy⟩ := H.exists_loop x y hyx hyo
  exact ⟨l, ⟨hx, hy⟩, fun l' h' => H.unique_loop x y l' l hyx hyo h'.1 h'.2 hx hy⟩

/-- the share of a cell inside a horizon `x` cells from the body: `1` inside, `1/2` on it, `0`
beyond; the count's `Horizon.Positions.weight` is the case `x = L/4` (`horizonWeight_quarter`) -/
noncomputable def horizonWeight (x : ℝ) (d : ℕ) : ℝ :=
  if (d : ℝ) < x then 1 else if (d : ℝ) = x then 1 / 2 else 0

/-- With the horizon `L/4` cells out, `horizonWeight` is the count's `weight`. -/
lemma horizonWeight_quarter (d : ℕ) :
    horizonWeight ((L : ℝ) / 4) d = Horizon.Positions.weight (L := L) d := by
  have h1 : ((d : ℝ) < (L : ℝ) / 4) ↔ 4 * d < L := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    constructor
    · intro h
      have h' : ((4 * d : ℕ) : ℝ) < L := by push_cast; linarith
      exact_mod_cast h'
    · intro h
      have h' : ((4 * d : ℕ) : ℝ) < L := by exact_mod_cast h
      push_cast at h'
      linarith
  have h2 : ((d : ℝ) = (L : ℝ) / 4) ↔ 4 * d = L := by
    rw [eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]
    constructor
    · intro h
      have h' : ((4 * d : ℕ) : ℝ) = L := by push_cast; linarith
      exact_mod_cast h'
    · intro h
      have h' : ((4 * d : ℕ) : ℝ) = L := by exact_mod_cast h
      push_cast at h'
      linarith
  unfold horizonWeight Horizon.Positions.weight
  simp only [h1, h2]

/-! ### A model of the count -/

section Model

open MeasureTheory RealInnerProductSpace

/-- **A register with `L = 6`**, the length of the Fano model's largest rings (`Horizon.fano`), with
the cell as the unit of length, time and energy. -/
noncomputable def regSix : Reg where
  c := 1
  ℏ := 1
  kB := 1
  ℓc := 1
  L := 6
  c_pos := one_pos
  ℏ_pos := one_pos
  kB_pos := one_pos
  ℓc_pos := one_pos
  L_pos := by norm_num

/-- the Borel sets of `ℝ⁴`, for the model below -/
noncomputable local instance : MeasurableSpace (EuclideanSpace ℝ (Fin 4)) := borel _

local instance : BorelSpace (EuclideanSpace ℝ (Fin 4)) := ⟨rfl⟩

/-- **The hypotheses of `sphere_strings_of_rings` can be met together**, so it does not hold
vacuously: the Fano model's rings (`Horizon.fano`, `L = 6`), the register `regSix` with the same `L`
and the real `π`, the Euclidean space `ℝ⁴` with its Borel sets and a Haar measure, every ring the
great circle through `R_Λ e₀` and `R_Λ e₁` of the space at an instant of de Sitter space of radius
`R_Λ` (`Geodesic.circleCurve`), each of length `Lℓ_c`, and the sphere at distance `s = R_Λ`.  The
average it returns is positive. -/
theorem sphere_strings_model :
    ∃ (γ : Horizon.fano.Loop → Geodesic.Curve ℝ (EuclideanSpace ℝ (Fin 4)))
      (hgeo : ∀ l, Geodesic.IsGeodesic (regSix.RL ^ 2) (γ l))
      (hsp : ∀ l, Geodesic.IsSpacelike (γ l)) (hin : ∀ l, Geodesic.InSpace (γ l)),
      (∀ l, Geodesic.HasLength (γ l) (regSix.L * regSix.ℓc)) ∧
      0 < (Crossing.Drawing.ofRings regSix.RL_pos γ hgeo hsp hin).meanStrings Measure.addHaar
        regSix.RL := by
  have hRL := regSix.RL_pos
  have hab : ⟪regSix.RL • EuclideanSpace.single (0 : Fin 4) (1 : ℝ),
      regSix.RL • EuclideanSpace.single (1 : Fin 4) (1 : ℝ)⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, EuclideanSpace.inner_single_left]
    simp
  have hn : ∀ j : Fin 4, ‖regSix.RL • EuclideanSpace.single j (1 : ℝ)‖ = regSix.RL := fun j => by
    simp [norm_smul, abs_of_pos hRL]
  have hgeo := Geodesic.circleCurve_geodesic (ω := 1) hab (hn 0) (hn 1)
  have hsp := Geodesic.circleCurve_spacelike (ω := 1) hab (hn 0) (hn 1) hRL one_ne_zero
  have hlen : Geodesic.HasLength
      (Geodesic.circleCurve (regSix.RL • EuclideanSpace.single (0 : Fin 4) (1 : ℝ))
        (regSix.RL • EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) 1) (regSix.L * regSix.ℓc) := by
    have h := hgeo.hasLength (by positivity) hsp
    have e : 2 * Real.pi * Real.sqrt (regSix.RL ^ 2) = regSix.L * regSix.ℓc := by
      rw [Real.sqrt_sq hRL.le]
      unfold Reg.RL
      simp only [regSix, Reg.pi_def]
      field_simp
    rwa [e] at h
  refine ⟨fun _ => _, fun _ => hgeo, fun _ => hsp, fun _ => Geodesic.circleCurve_inSpace,
    fun _ => hlen, ?_⟩
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : (regSix.RL * (Real.sqrt 3 / 2)) ^ 2 =
      regSix.RL ^ 2 - regSix.RL ^ 4 / (4 * regSix.RL ^ 2) := by
    field_simp
    nlinarith [h3]
  have hs : regSix.RL ^ 2 ≤ 2 * regSix.RL ^ 2 := by nlinarith
  rw [Crossing.Drawing.meanStrings_eq Measure.addHaar (by simp) _ hRL hRL hs hr]
  have : 0 < Fintype.card Horizon.fano.Loop := by decide
  positivity

/-- **The hypotheses of `Main.horizon_quarter` on the count's horizon can be met**: the Fano model with
its positions, the register `regSix`, Newton's constant from Jacobson's step, `G = c³k_B/4ℏη`,
`Λ = 3/R_Λ²`, the proper distance `R_Λ arcsin(r/R_Λ)` (`Reg.proper_distance_exists`), the count's
horizon at `x = s(R_Λ)/ℓ_c`, and a cell `Q` one step from the body's cell. -/
theorem ring_distance_model :
    ∃ (G Λ x : ℝ) (s : ℝ → ℝ) (Q : Horizon.fano.Cell),
      regSix.L = ((6 : ℕ) : ℝ) ∧
      G = regSix.c ^ 3 * regSix.kB / (4 * regSix.ℏ * regSix.η) ∧
      regSix.fSdS G 0 Λ regSix.RL = 0 ∧ s 0 = 0 ∧ ContinuousOn s (Set.Icc 0 regSix.RL) ∧
      (∀ r ∈ Set.Ioo 0 regSix.RL, HasDerivAt s (1 / Real.sqrt (regSix.fSdS G 0 Λ r)) r) ∧
      x * regSix.ℓc = s regSix.RL ∧
      Horizon.fanoPositions.dist ((0 : Fin 7), false) Q = 1 := by
  have hL : (4 : ℕ) ≤ 6 := by norm_num
  set G : ℝ := regSix.c ^ 3 * regSix.kB / (4 * regSix.ℏ * regSix.η) with hG
  have hdS : regSix.fSdS G 0 (3 / regSix.RL ^ 2) regSix.RL = 0 := (regSix.deSitter G _).2 rfl
  obtain ⟨hs0, hcont, hds⟩ := regSix.proper_distance_exists G _ hdS
  have hcard := Horizon.fanoPositions.card_dist_eq hL ((0 : Fin 7), false) (d := 1)
    (by norm_num) (by norm_num)
  obtain ⟨Q, hQ⟩ := Finset.card_pos.1 (by rw [hcard]; norm_num :
    0 < (Finset.univ.filter (fun X => Horizon.fanoPositions.dist ((0 : Fin 7), false) X = 1)).card)
  refine ⟨G, 3 / regSix.RL ^ 2, regSix.sdS regSix.RL / regSix.ℓc, regSix.sdS, Q, by simp [regSix],
    hG, hdS, hs0, hcont, hds, ?_, (Finset.mem_filter.1 hQ).2⟩
  field_simp [regSix.ℓc_pos.ne']

end Model

end Bridge
end Register
