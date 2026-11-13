import RegisterGravity.Symmetry
import RegisterGravity.Quotients
import RegisterGravity.Einstein
import RegisterGravity.RouteB

/-!
# The space at an instant, and the solution it determines (Sec. IV.D)

Section IV.D finds the solution without a mass from its space at an instant.  This file carries
the step without taking completeness as a separate premise, and without the solution itself: the
space at an instant is complete because every geodesic of it closes along a ring (`hclose`,
Postulate 1's first sentence applied to space; the first link below), and its rings, with the
rings through the observer's cell drawn in it, make it the three-sphere, from which Einstein's
constraint gives `Λ`.  Starting from the spacetime would need its completeness as a premise, since
a homogeneous spacetime of constant curvature need not be
complete: the steady-state half of de Sitter space is one, and it is a quotient of none of the
three maximally symmetric spacetimes.  The step runs instead through the space at an instant of an
observer at rest, `Σ`, in three links.

* **The space forms** (`SpaceForm`).  `Σ` is totally geodesic, since the geometry about an observer
  at rest does not change in time (Sec. II); its geometry is the same at every place and in every
  direction (`Solution.geometry_same`), so its curvature is one number `K` (Schur's lemma); and it is
  complete, since a ring runs along every geodesic of space (Postulate 1's first sentence applied to
  `Σ`), so every geodesic closes.  By the Killing–Hopf theorem, `Σ` is the three-sphere of curvature
  `K`, Euclidean space or hyperbolic space, divided by a group `Γ` of isometries acting freely and
  properly discontinuously (`Sources.Geometry.space_form`); by Einstein's constraint on a time-symmetric
  slice without matter, `3K = Λ` (`Sources.Geometry.constraint`).
* **The slice's rings exclude the flat and hyperbolic forms** (`flat_space_no_rings`,
  `hyperbolic_space_no_rings`): a ring along every geodesic of `Σ`, of one length, would carry the
  center of a ball onto every point of a sphere about it by the group's maps, which a group acting
  properly discontinuously cannot do (`not_spread_space`).  So `K > 0` (`slice_sphere`).
* **The slice's rings exclude every quotient of the three-sphere** (`sphere_rings`).  Every great
  circle closes in the quotient with one length, so every map of `Γ` is `±1` on space: a map that
  is neither turns some plane by an angle below `2π` (`Quotients.exists_rotation_plane`), and the
  circle of that plane would close sooner than the circle of a plane that no map but `±1` turns
  onto itself (`Quotients.exists_plane_not_turned`).  And `−1` is excluded by the rings through the
  observer's cell, drawn in space (`RingsDrawn`, `Sources.P2.rings_drawn`: Sec. II's cell, a place
  on a ring, and Postulate 2's last sentence, with its first clause, the same opposite cell halfway
  around every largest ring through a cell).  With the antipodal points identified every ring
  closes after half a turn, so the opposite cell, halfway along, is a quarter turn from the
  observer's cell on every ring through it; two rings drawn through the one place of the observer's
  cell and the one place of its opposite lie on one great circle, and the cell one step on from the
  observer's cell along one falls on the place of the cell one step on, or back, along the other:
  two cells at one place, so one cell on both, while two rings through a cell share only it and its
  opposite.  So `Γ` is trivial, the space is the three-sphere itself, and every
  great circle has the length `2π√(1/K)`.

`cosmological_constant_of_sources` puts the links together: `Lℓ_c = 2π√(1/K) = 2π√(3/Λ)`, so
`Λ = 3/R_Λ²`.
-/

open Geodesic Quotients Symmetry RealInnerProductSpace

namespace Space

/-! ### Quotients of the three-sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A quotient of the three-sphere** of radius `√k`, the waist of de Sitter space `form X X = k`
of `ℝ × E`, by a finite group `Γ` of rotations of space: its maps are linear maps of `ℝ × E` that
keep the form and the time of every point, so each rotates space and leaves time alone; those other
than the identity fix no point of the sphere; and there are finitely many, as a group acting
properly discontinuously on a compact sphere has. -/
structure SphereQuotient (k : ℝ) (Γ : Subgroup ((ℝ × E) ≃ₗ[ℝ] (ℝ × E))) : Prop where
  iso : ∀ g ∈ Γ, ∀ x y : ℝ × E, form (g x) (g y) = form x y
  time : ∀ g ∈ Γ, ∀ x : ℝ × E, (g x).1 = x.1
  free : ∀ g ∈ Γ, ∀ y : E, ‖y‖ ^ 2 = k → g ((0 : ℝ), y) = ((0 : ℝ), y) → g = 1
  finite : (Γ : Set ((ℝ × E) ≃ₗ[ℝ] (ℝ × E))).Finite

/-- the map of space that a map of `ℝ × E` makes: `y ↦ (g (0, y)).2`, the map `g` makes of the
places when it leaves time alone -/
def spaceMap (g : (ℝ × E) ≃ₗ[ℝ] (ℝ × E)) : E →ₗ[ℝ] E :=
  LinearMap.snd ℝ ℝ E ∘ₗ ((g : (ℝ × E) →ₗ[ℝ] (ℝ × E)) ∘ₗ LinearMap.inr ℝ ℝ E)

lemma spaceMap_apply (g : (ℝ × E) ≃ₗ[ℝ] (ℝ × E)) (y : E) : spaceMap g y = (g ((0 : ℝ), y)).2 := rfl

lemma spaceMap_one (y : E) : spaceMap (1 : (ℝ × E) ≃ₗ[ℝ] (ℝ × E)) y = y := rfl

end Sphere

/-! ### The flat and hyperbolic space forms have no rings -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A group acting properly discontinuously on space does not carry a point onto every point of a
sphere about it**: the maps that do, one for each
unit vector `u`, are infinitely many, since the points `r u` are, and each carries the center `0` of
the ball of radius `r` into the ball. -/
theorem not_spread_space (hE : 2 ≤ Module.finrank ℝ E) {Γ : Set (Equiv.Perm E)}
    (hprop : ProperOn Γ) {r : ℝ} (hr : 0 < r)
    (h : ∀ u : E, ‖u‖ = 1 → ∃ g ∈ Γ, g 0 = r • u) : False := by
  obtain ⟨f₁, f₂, h1, h2, h12⟩ := exists_orthonormal_pair hE
  have hu : ∀ θ : ℝ, ‖Real.cos θ • f₁ + Real.sin θ • f₂‖ = 1 := fun θ => by
    have h := Crossing.norm_comb_sq h12 h1 h2 (Real.cos θ) (Real.sin θ)
    rw [Real.cos_sq_add_sin_sq, one_pow, one_mul] at h
    rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_one]
  choose G hGΓ hG using fun θ : ℝ => h _ (hu θ)
  have hK : IsCompact (Metric.closedBall (0 : E) r) := isCompact_closedBall _ _
  have hinj : Set.InjOn G (Set.Icc 0 Real.pi) := by
    intro θ hθ θ' hθ' hGG
    have e : r • (Real.cos θ • f₁ + Real.sin θ • f₂) = r • (Real.cos θ' • f₁ + Real.sin θ' • f₂) := by
      rw [← hG θ, ← hG θ', hGG]
    have e2 := congrArg (fun p : E => ⟪f₁, p⟫) e
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, h1, h12] at e2
    apply Real.injOn_cos hθ hθ'
    have := mul_left_cancel₀ hr.ne' e2
    linarith
  have hmaps : Set.MapsTo G (Set.Icc 0 Real.pi)
      {g | g ∈ Γ ∧ ((⇑g) '' Metric.closedBall (0 : E) r ∩ Metric.closedBall 0 r).Nonempty} := by
    intro θ _
    refine ⟨hGΓ θ, G θ 0, ⟨0, Metric.mem_closedBall_self hr.le, rfl⟩, ?_⟩
    rw [hG θ, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      hu, mul_one]
  exact Set.infinite_of_injOn_mapsTo hinj hmaps (Set.Icc_infinite Real.pi_pos) (hprop _ hK)

/-- **Euclidean space has no quotient with rings** (Sec. IV.D): if every straight line closed in
the quotient by `Γ` with the length `len`, the line from `0` along each unit vector `u` would close
after `len`, at `len u`, which `not_spread_space` excludes.  Only that `Γ` acts properly
discontinuously is used. -/
theorem flat_space_no_rings (hE : 2 ≤ Module.finrank ℝ E) {Γ : Set (Equiv.Perm E)}
    (hprop : ProperOn Γ) {len : ℝ}
    (hring : ∀ u : E, ‖u‖ = 1 → ClosesIn Γ (fun t : ℝ => t • u) (fun _ => (1 : ℝ)) len) :
    False := by
  obtain ⟨f₁, -, hf₁, -, -⟩ := exists_orthonormal_pair hE
  obtain ⟨P₀, hP₀, -, -, hlen₀⟩ := hring f₁ hf₁
  have hlen : 0 < len := by rw [← hlen₀ 0, one_mul]; exact hP₀
  refine not_spread_space hE hprop hlen fun u hu => ?_
  obtain ⟨P, -, ⟨g, hg, hgP⟩, -, hlenP⟩ := hring u hu
  have hPeq : P = len := by rw [← hlenP 0, one_mul]
  refine ⟨g, hg, ?_⟩
  have h0 := hgP 0
  simp only [zero_add, zero_smul] at h0
  rw [← h0, hPeq]

/-- **Hyperbolic space has no quotient with rings** (Sec. IV.D).  Hyperbolic space of radius `ℓ` is
the upper sheet of the quadric `form X X = −ℓ²` of `ℝ × E`, and the projection to `E` is a chart of
it on which `Γ` acts.  If every geodesic closed in the quotient with the length `len`, the geodesic
from the lowest point along each unit vector `u`, `t ↦ (ℓ cosh t, ℓ sinh t · u)`, of speed `ℓ`,
would close after `len/ℓ`, at `ℓ sinh(len/ℓ) · u` in the chart, which `not_spread_space` excludes.
Only that `Γ` acts properly discontinuously is used. -/
theorem hyperbolic_space_no_rings (hE : 2 ≤ Module.finrank ℝ E) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Γ : Set (Equiv.Perm E)} (hprop : ProperOn Γ) {len : ℝ}
    (hring : ∀ γ : Curve ℝ E, IsGeodesic (-(ℓ ^ 2)) γ → 0 < (γ.pos 0).1 →
      ClosesIn Γ (fun t => (γ.pos t).2) (speed γ) len) : False := by
  have hlift : ∀ u : E, ‖u‖ = 1 →
      ClosesIn Γ (fun t => (ℓ * Real.sinh t) • u) (fun _ => ℓ) len := by
    intro u hu
    have ha : ‖(ℓ : ℝ)‖ = ℓ := by rw [Real.norm_eq_abs, abs_of_pos hℓ]
    have hb : ‖ℓ • u‖ = ℓ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, hu, mul_one]
    have hspeed : ∀ t, speed (hypCurve (ℓ : ℝ) (ℓ • u)) t = ℓ := fun t => by
      show Real.sqrt (-⟪Real.sinh t • (ℓ : ℝ), Real.sinh t • (ℓ : ℝ)⟫ +
        ⟪Real.cosh t • (ℓ • u), Real.cosh t • (ℓ • u)⟫) = ℓ
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul (Real.sinh t),
        norm_smul (Real.cosh t), ha, hb, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
        sq_abs, sq_abs]
      have e : -(Real.sinh t ^ 2 * ℓ ^ 2) + Real.cosh t ^ 2 * ℓ ^ 2 = ℓ ^ 2 := by
        nlinarith [Real.cosh_sq t]
      rw [e, Real.sqrt_sq hℓ.le]
    have h0 : 0 < ((hypCurve (ℓ : ℝ) (ℓ • u)).pos 0).1 := by
      show 0 < Real.cosh 0 • (ℓ : ℝ)
      rw [Real.cosh_zero, one_smul]
      exact hℓ
    have hpos : (fun t => ((hypCurve (ℓ : ℝ) (ℓ • u)).pos t).2) = fun t => (ℓ * Real.sinh t) • u :=
      funext fun t => by
        show Real.sinh t • (ℓ • u) = (ℓ * Real.sinh t) • u
        rw [smul_smul, mul_comm]
    have hsp : speed (hypCurve (ℓ : ℝ) (ℓ • u)) = fun _ => ℓ := funext hspeed
    have hc := hring _ (hypCurve_geodesic ha hb) h0
    rw [hpos, hsp] at hc
    exact hc
  obtain ⟨f₁, -, hf₁, -, -⟩ := exists_orthonormal_pair hE
  obtain ⟨P₀, hP₀, -, -, hlen₀⟩ := hlift f₁ hf₁
  have hlen : 0 < len := by rw [← hlen₀ 0]; exact mul_pos hℓ hP₀
  have hsinh : 0 < Real.sinh (len / ℓ) := by
    rw [Real.sinh_eq]
    have := Real.exp_lt_exp.2 (show -(len / ℓ) < len / ℓ by linarith [div_pos hlen hℓ])
    linarith
  refine not_spread_space hE hprop (mul_pos hℓ hsinh) fun u hu => ?_
  obtain ⟨P, -, ⟨g, hg, hgP⟩, -, hlenP⟩ := hlift u hu
  have hPeq : P = len / ℓ := by
    rw [← hlenP 0]
    field_simp
  refine ⟨g, hg, ?_⟩
  have h0 := hgP 0
  simp only [zero_add, Real.sinh_zero, mul_zero, zero_smul] at h0
  rw [← h0, hPeq]

end Space

/-! ### The space forms of the space at an instant -/

/-- **The space forms of dimension three** (Sec. IV.D): by the Killing–Hopf theorem a complete,
connected Riemannian 3-manifold of constant curvature `K` is the three-sphere of curvature `K`,
Euclidean space or hyperbolic space, divided by a group `Γ` of isometries acting freely and properly
discontinuously [J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed. (2018), p. 348;
H. Hopf, Math. Ann. **95**, 313 (1926)].  The sphere is the waist of de Sitter space
`form X X = 1/K` of `ℝ × ℝ⁴`, and `Γ` a finite group of rotations of space kept as maps of
`ℝ × ℝ⁴` (`SphereQuotient`); Euclidean space is `ℝ³`; hyperbolic space is the upper sheet of
`form X X = 1/K` of `ℝ × ℝ³`, on whose chart `ℝ³` the group acts. -/
inductive SpaceForm (K : ℝ) : Type
  /-- the three-sphere of curvature `K`, divided by `Γ` -/
  | sphere (Γ : Subgroup ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
      (hK : 0 < K) (hΓ : SphereQuotient (1 / K) Γ)
  /-- Euclidean space, divided by `Γ` -/
  | flat (Γ : Subgroup (Equiv.Perm (EuclideanSpace ℝ (Fin 3)))) (hK : K = 0)
      (hΓ : ProperOn (Γ : Set (Equiv.Perm (EuclideanSpace ℝ (Fin 3)))))
  /-- hyperbolic space of curvature `K`, divided by `Γ` -/
  | hyperbolic (Γ : Subgroup (Equiv.Perm (EuclideanSpace ℝ (Fin 3)))) (hK : K < 0)
      (hΓ : ProperOn (Γ : Set (Equiv.Perm (EuclideanSpace ℝ (Fin 3)))))

/-- the great circles of the waist of de Sitter space `form X X = k`: the geodesics of the
three-sphere of radius `√k` -/
def sphereSlots (k : ℝ) : Set (Curve ℝ (EuclideanSpace ℝ (Fin 4))) :=
  {γ | IsGeodesic k γ ∧ InSpace γ ∧ IsSpacelike γ}

/-- the straight lines of Euclidean space, each by a point and a velocity -/
def lineSlots : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) := {pv | pv.2 ≠ 0}

/-- the geodesics of hyperbolic space, the upper sheet of the quadric `form X X = k < 0` -/
def hypSlots (k : ℝ) : Set (Curve ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {γ | IsGeodesic k γ ∧ 0 < (γ.pos 0).1}

/-- the slots of a space form, the type in which the files name its geodesics: curves of the
three-sphere's ambient space, lines of Euclidean space by a point and a velocity, curves of the
hyperboloid -/
def SpaceForm.Slot {K : ℝ} : SpaceForm K → Type
  | .sphere _ _ _ => Curve ℝ (EuclideanSpace ℝ (Fin 4))
  | .flat _ _ _ => EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
  | .hyperbolic _ _ _ => Curve ℝ (EuclideanSpace ℝ (Fin 3))

/-- the geodesics of a space form: `sphereSlots`, `lineSlots` or `hypSlots` -/
def SpaceForm.slots {K : ℝ} : (c : SpaceForm K) → Set c.Slot
  | .sphere _ _ _ => sphereSlots (1 / K)
  | .flat _ _ _ => lineSlots
  | .hyperbolic _ _ _ => hypSlots (1 / K)

/-- a geodesic of a space form closes in the quotient by its group with the length `len` -/
def SpaceForm.closes {K : ℝ} (len : ℝ) : (c : SpaceForm K) → c.Slot → Prop
  | .sphere Γ _ _ => fun γ =>
      ClosesIn (Γ : Set ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
        γ.pos (speed γ) len
  | .flat Γ _ _ => fun pv =>
      ClosesIn (Γ : Set (Equiv.Perm (EuclideanSpace ℝ (Fin 3)))) (fun t => pv.1 + t • pv.2)
        (fun _ => ‖pv.2‖) len
  | .hyperbolic Γ _ _ => fun γ =>
      ClosesIn (Γ : Set (Equiv.Perm (EuclideanSpace ℝ (Fin 3)))) (fun t => (γ.pos t).2) (speed γ) len

variable {L : ℕ}

/-- **Postulate 1's first sentence applied to the space at an instant** (Secs. II and IV.D): along
every geodesic of the space form some admissible drawing runs a ring, one that closes in the
quotient with a largest ring's length `len` (`Symmetry.ringsAlong` at the form's geodesics,
`SpaceForm.slots`, with `SpaceForm.closes`): a geodesic of space along which no ring runs would be
a feature of space that the strings do not describe. -/
def SliceIsQubits (H : Horizon L) (len : ℝ) {K : ℝ} (c : SpaceForm K) : Prop :=
  ringsAlong H c.slots (c.closes len)

/-- **The space at an instant with rings is a quotient of the three-sphere** (Sec. IV.D): the flat
and hyperbolic forms have no rings along every geodesic (`flat_space_no_rings`,
`hyperbolic_space_no_rings`), so the form is the sphere and `K > 0`. -/
theorem slice_sphere {H : Horizon L} {len K : ℝ} (c : SpaceForm K) (h : SliceIsQubits H len c) :
    ∃ Γ hK hΓ, c = SpaceForm.sphere Γ hK hΓ := by
  have hE : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  cases c with
  | sphere Γ hK hΓ => exact ⟨Γ, hK, hΓ, rfl⟩
  | flat Γ hK hΓ =>
    exfalso
    refine flat_space_no_rings hE hΓ (len := len) fun u hu => ?_
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have hm := (mem_described_admissible _ _).1 (h ((0 : EuclideanSpace ℝ (Fin 3)), u) hu0)
    have hc : ClosesIn (Γ : Set (Equiv.Perm (EuclideanSpace ℝ (Fin 3))))
        (fun t => (0 : EuclideanSpace ℝ (Fin 3)) + t • u) (fun _ => ‖u‖) len := hm.2
    simpa [hu] using hc
  | hyperbolic Γ hK hΓ =>
    exfalso
    have hpos : 0 < -(1 / K) := by
      have : 1 / K < 0 := one_div_neg.2 hK
      linarith
    have hℓ : 0 < Real.sqrt (-(1 / K)) := Real.sqrt_pos.2 hpos
    have hk : -(Real.sqrt (-(1 / K)) ^ 2) = 1 / K := by
      rw [Real.sq_sqrt hpos.le]
      ring
    refine hyperbolic_space_no_rings hE hℓ hΓ (len := len) fun γ hg h0 => ?_
    rw [hk] at hg
    exact ((mem_described_admissible _ _).1 (h γ ⟨hg, h0⟩)).2

/-! ### The rings of the space at an instant exclude every quotient of the three-sphere -/

/-- **A great circle of the waist, in the places**: `pos t = cos(vt/√k) a + sin(vt/√k) b`, with
`a ⊥ b` of norm `√k` and `v` the circle's speed (`Geodesic.IsGeodesic.circle`,
`Geodesic.IsGeodesic.greatCircle`). -/
lemma sphereSlots_pos {k : ℝ} (hk : 0 < k) {γ : Curve ℝ (EuclideanSpace ℝ (Fin 4))}
    (hγ : γ ∈ sphereSlots k) :
    ∃ a b : EuclideanSpace ℝ (Fin 4), ‖a‖ = Real.sqrt k ∧ ‖b‖ = Real.sqrt k ∧ ⟪a, b⟫ = 0 ∧
      ∀ t, (γ.pos t).2 = Real.cos (speed γ 0 / Real.sqrt k * t) • a +
        Real.sin (speed γ 0 / Real.sqrt k * t) • b := by
  obtain ⟨hg, hin, hsp⟩ := hγ
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  have hk' : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
  have hg' : IsGeodesic (Real.sqrt k ^ 2) γ := by rw [hk']; exact hg
  obtain ⟨hab, ha, hb, -⟩ := hg'.greatCircle hs hsp hin
  have hω : Real.sqrt (form (γ.vel 0) (γ.vel 0) / k) = speed γ 0 / Real.sqrt k := by
    unfold speed
    rw [Real.sqrt_div' _ hk.le]
  have hfreq : γ.freq (Real.sqrt k ^ 2) = speed γ 0 / Real.sqrt k := by
    unfold Curve.freq
    rw [hk', hω]
  refine ⟨(γ.pos 0).2, (γ.freq (Real.sqrt k ^ 2))⁻¹ • (γ.vel 0).2, ha, hb, hab, fun t => ?_⟩
  have hcirc := hg.circle hk (hsp 0) t
  rw [hcirc, Prod.snd_add, Prod.smul_snd, Prod.smul_snd, Prod.smul_snd, hω, hfreq]

/-- **The rings through the cell `B`, drawn in the space at an instant** (Sec. II and Postulate 2
at the observer's cell; `Sources.P2.rings_drawn`), the space being the three-sphere of radius `√k`
divided by `Γ`.  "A ring is a closed line of translation in space; a cell is a place on a ring"
(Sec. II), and "every largest ring is a closed geodesic of space, made of its cells as segments of
length `ℓ_c`" (Postulate 2): each largest ring `l` through `B` runs along a great circle `γ l` that
closes in the quotient with the length `Lℓ_c`, `L` its number of cells, and the cell `j` steps
from `B` along `l` (`Horizon.Positions.offset`) is placed at the point of `γ l` at the arc length
`jℓ_c`, its place `pl l X`, up to `Γ`, where its segment begins.  Any other point of the segment
would do, by starting `γ l` elsewhere: the proof uses differences of arc length only.  The cells
of the drawn rings are places, Sec. II's "a cell is a place" read as an identity, in both
directions: the same cell drawn on two of the rings is at one place (`←`), and two cells are two
places (`→`).  The cells that two of the rings share are `B` itself and its opposite, "one
opposite, the same cell halfway around every largest ring through it" (Postulate 2, first clause;
`Horizon.Positions.offset_opp_self`); `→` is the direction with which `sphere_rings` excludes the
antipodal quotient.  So at the observer's cell the files take a cell's place to be a point of the
manifold, for the rings through it, as Sec. II states: "For an observer at rest, the manifold
describes the register's incidence, that is, which rings share a cell, only for the rings through
his cell".  Every cell lies on a ring through `B`
(`Horizon.exists_loop_through`), so every cell is drawn, at one place.  Nothing is said of the
rings off `B`: drawn through the places of their cells as well, the rings would draw the register's
incidence with its cells as points and its rings as great circles, which the Sylvester–Gallai
theorem forbids for `L ≥ 6` [P. Erdős, Problem 4065, Amer. Math. Monthly 50, 65 (1943);
R. Steinberg, solution, ibid. 51, 169 (1944)]; the rings of one cell are all that `sphere_rings`
uses. -/
def RingsDrawn (H : Horizon L) (P : H.Positions) (k : ℝ)
    (Γ : Subgroup ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
    (ℓc : ℝ) (B : H.Cell) : Prop :=
  ∃ (γ : (l : H.Loop) → B ∈ H.cells l → Curve ℝ (EuclideanSpace ℝ (Fin 4)))
    (pl : (l : H.Loop) → B ∈ H.cells l → H.Cell → EuclideanSpace ℝ (Fin 4)),
    (∀ l hl, γ l hl ∈ sphereSlots k ∧
      ClosesIn (Γ : Set ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
        (γ l hl).pos (speed (γ l hl)) ((L : ℝ) * ℓc)) ∧
    (∀ l hl, ∀ X ∈ H.cells l, ∃ g ∈ Γ,
      (γ l hl).pos ((P.offset l B X : ℝ) * ℓc / speed (γ l hl) 0) = g ((0 : ℝ), pl l hl X)) ∧
    (∀ l hl l' hl', ∀ X ∈ H.cells l, ∀ Y ∈ H.cells l',
      ((∃ g ∈ Γ, ((0 : ℝ), pl l hl X) = g ((0 : ℝ), pl l' hl' Y)) ↔ X = Y))

/-- **The rings of the space at an instant exclude every quotient of the three-sphere** (Sec. IV.D).
Let the space be the three-sphere of radius `√k` divided by a finite group `Γ` of rotations acting
freely (`SphereQuotient`), let every great circle close in the quotient with the length `len`
(`hring`), and let the rings through the cell `B` be drawn in it (`hdrawn`, `RingsDrawn`).  Then
`Γ` is trivial and `len = 2π√k`.
* Every map of `Γ` is `±1` on space.  A great circle's least period is `len/√k`, the same for all.
  A map `g` other than `±1` turns some plane of space by an angle `0 < θ < 2π`
  (`Quotients.exists_rotation_plane`), so the circle in that plane returns after `θ`: `len/√k ≤ θ`.
  Some plane is turned onto itself by no map of `Γ` other than `±1`
  (`Quotients.exists_plane_not_turned`), and its circle returns only by `1`, after a multiple of
  `2π`, or by `−1`, after `π` and then `len/√k ≥ π`; in the first case `len/√k ≥ 2π > θ`.  In the
  second, `−g` is in `Γ` and turns the plane of `g` by `θ + π`, so `len/√k ≤ θ ± π < π` unless
  `θ = π`, when `−g` fixes a vector of the plane, which a map of `Γ` other than `1` cannot, and
  `g = −1`.
* No map of `Γ` is `−1` on space.  Were one, every great circle would return after `π` and by
  `±1` at its least period, so `len = π√k`, and the places of a drawn ring would be up to sign.
  A drawn ring closes with `Lℓ_c`, the one length, so its cell `j` steps from `B` sits at the angle
  `jπ/L` from `B`'s place, and its opposite cell, `L/2` steps on
  (`Horizon.Positions.offset_opp_self`), a quarter turn on.  Two different rings through `B`
  (`Horizon.two_mul_card_through`) are drawn through the one place of `B`, up to sign, and the one
  place of its opposite, up to sign, so they lie on one great circle, one the other reflected or
  not.  Then the cell one step from `B` on the second falls on the place of the cell one step from
  `B` on the first, or of the cell one step back, up to sign; two cells at one place are one cell
  (`RingsDrawn`), on both rings, and not `B` or its opposite, while two rings through `B` share
  only `B` and its opposite (`Horizon.unique_loop`).
So every map of `Γ` is `1` on space and hence `1`: `Γ = ⊥`, and a great circle returns only after a
multiple of `2π` and at `2π`: `len = 2π√k`. -/
theorem sphere_rings {k : ℝ} (hk : 0 < k)
    {Γ : Subgroup ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4)))}
    (hΓ : SphereQuotient k Γ) {len : ℝ}
    (hring : ∀ γ ∈ sphereSlots k,
      ClosesIn (Γ : Set ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
        γ.pos (speed γ) len)
    (H : Horizon L) [NeZero L] (P : H.Positions) {ℓc : ℝ} (B : H.Cell)
    (hdrawn : RingsDrawn H P k Γ ℓc B) :
    Γ = ⊥ ∧ len = 2 * Real.pi * Real.sqrt k := by
  have hE : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt k := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hk
  have hs2 : s ^ 2 = k := by rw [hsdef]; exact Real.sq_sqrt hk.le
  -- the map of space that a map of `Γ` makes
  have hAy : ∀ g ∈ Γ, ∀ y : EuclideanSpace ℝ (Fin 4), g ((0 : ℝ), y) = ((0 : ℝ), spaceMap g y) :=
    fun g hg y => Prod.ext (hΓ.time g hg _) rfl
  have hAmul : ∀ g h : ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))),
      g ∈ Γ → h ∈ Γ → ∀ y, spaceMap (g * h) y = spaceMap g (spaceMap h y) := fun g h hg hh y => by
    rw [spaceMap_apply, LinearEquiv.mul_apply, hAy h hh, hAy g hg]
  have hA : ∀ g ∈ Γ, ∀ x y, ⟪spaceMap g x, spaceMap g y⟫ = ⟪x, y⟫ := fun g hg x y => by
    rw [← form_zero_zero, ← form_zero_zero, ← hAy g hg, ← hAy g hg, hΓ.iso g hg]
  have hAfix : ∀ g ∈ Γ, g ≠ 1 → ∀ y, spaceMap g y = y → y = 0 := by
    intro g hg hg1 y hy
    by_contra hy0
    have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hz : ‖(s / ‖y‖) • y‖ ^ 2 = k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hs0 hyn), div_mul_cancel₀ _ hyn.ne', hs2]
    exact hg1 (hΓ.free g hg _ hz (by rw [hAy g hg, map_smul, hy]))
  -- the great circles of the waist, of speed `s`
  have hform : ∀ u : EuclideanSpace ℝ (Fin 4), ‖u‖ = 1 →
      form (((0 : ℝ), s • u) : ℝ × EuclideanSpace ℝ (Fin 4)) ((0 : ℝ), s • u) = k := fun u hu => by
    rw [form_zero_zero, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hu,
      ← hs2]
    ring
  have hform' : ∀ u w : EuclideanSpace ℝ (Fin 4), ⟪u, w⟫ = 0 →
      form (((0 : ℝ), s • u) : ℝ × EuclideanSpace ℝ (Fin 4)) ((0 : ℝ), s • w) = 0 := fun u w huw => by
    rw [form_zero_zero, real_inner_smul_left, real_inner_smul_right, huw]
    ring
  have hpos : ∀ (u w : EuclideanSpace ℝ (Fin 4)) (r : ℝ),
      (planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)).pos r =
        ((0 : ℝ), s • (Real.cos r • u + Real.sin r • w)) := fun u w r => by
    show Real.cos r • (((0 : ℝ), s • u) : ℝ × EuclideanSpace ℝ (Fin 4)) +
      Real.sin r • ((0 : ℝ), s • w) = _
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add, Prod.smul_snd]
    module
  have hcurve : ∀ u w : EuclideanSpace ℝ (Fin 4), ‖u‖ = 1 → ‖w‖ = 1 → ⟪u, w⟫ = 0 →
      planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w) ∈ sphereSlots k ∧
      ∀ t, speed (planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)) t = s := by
    intro u w hu hw huw
    refine ⟨⟨planeCurve_isGeodesic (hform u hu) (hform w hw) (hform' u w huw), fun t => ?_,
      planeCurve_spacelike hk (hform u hu) (hform w hw) (hform' u w huw)⟩, fun t => ?_⟩
    · rw [hpos]
    · show Real.sqrt (form ((planeCurve _ _).vel t) ((planeCurve _ _).vel t)) = s
      rw [planeCurve_speed (hform u hu) (hform w hw) (hform' u w huw), hsdef]
  -- a return of such a circle after `P` is a turn of its plane by `P`, and conversely
  have hret : ∀ u w : EuclideanSpace ℝ (Fin 4), ∀ g ∈ Γ, ∀ P : ℝ,
      (∀ t, (planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)).pos (t + P) =
        g ((planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)).pos t)) →
      spaceMap g u = Real.cos P • u + Real.sin P • w ∧
        spaceMap g w = (-Real.sin P) • u + Real.cos P • w := by
    intro u w g hg P h
    have key : ∀ t, spaceMap g (Real.cos t • u + Real.sin t • w) =
        Real.cos (t + P) • u + Real.sin (t + P) • w := by
      intro t
      have e := h t
      rw [hpos, hpos, hAy g hg, map_smul] at e
      exact (smul_right_injective _ hs0.ne' (Prod.ext_iff.1 e).2).symm
    constructor
    · have := key 0
      rwa [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, zero_add] at this
    · have := key (Real.pi / 2)
      rwa [Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul, zero_add,
        add_comm (Real.pi / 2) P, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at this
  have hturn : ∀ u w : EuclideanSpace ℝ (Fin 4), ∀ g ∈ Γ, ∀ θ : ℝ,
      spaceMap g u = Real.cos θ • u + Real.sin θ • w →
      spaceMap g w = (-Real.sin θ) • u + Real.cos θ • w →
      ∀ t, (planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)).pos (t + θ) =
        g ((planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)).pos t) := by
    intro u w g hg θ hAu hAw t
    rw [hpos, hpos, hAy g hg, map_smul, map_add, map_smul, map_smul, hAu, hAw, Real.cos_add,
      Real.sin_add]
    refine Prod.ext rfl ?_
    simp only
    module
  -- the least period of every great circle is `len/s`
  have hP : ∀ u w : EuclideanSpace ℝ (Fin 4), ‖u‖ = 1 → ‖w‖ = 1 → ⟪u, w⟫ = 0 →
      0 < len / s ∧
      Returns (Γ : Set ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
        (planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)).pos (len / s) ∧
      ∀ P', 0 < P' →
        Returns (Γ : Set ((ℝ × EuclideanSpace ℝ (Fin 4)) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 4))))
          (planeCurve ((0 : ℝ), s • u) ((0 : ℝ), s • w)).pos P' → len / s ≤ P' := by
    intro u w hu hw huw
    obtain ⟨P, hP0, hPret, hleast, hPlen⟩ := hring _ (hcurve u w hu hw huw).1
    have e : P = len / s := by
      rw [← hPlen 0, (hcurve u w hu hw huw).2 0]
      field_simp
    rw [e] at hP0 hPret hleast
    exact ⟨hP0, hPret, hleast⟩
  -- every map of `Γ` is `±1` on space
  have hpm : ∀ g ∈ Γ, g = 1 ∨ ∀ y, spaceMap g y = -y := by
    intro g hg
    by_contra hcon
    push Not at hcon
    obtain ⟨hg1, hgneg⟩ := hcon
    -- the plane that `g` turns, by `θ`
    obtain ⟨u, w, hu, hw, huw, c, s', hcs, hc1, hAu, hAw⟩ :=
      exists_rotation_plane hE (spaceMap g) (hA g hg) (hAfix g hg hg1)
    obtain ⟨θ, hθ0, hθ2, hcos, hsin⟩ := exists_angle_pos hcs hc1
    rw [← hcos, ← hsin] at hAu hAw
    obtain ⟨hP0, -, hleast⟩ := hP u w hu hw huw
    have hPθ : len / s ≤ θ := hleast θ hθ0 ⟨g, hg, hturn u w g hg θ hAu hAw⟩
    -- a plane that no map of `Γ` other than `±1` turns onto itself
    obtain ⟨S, hSdef⟩ : ∃ S : Set (EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4)),
      S = spaceMap '' {h | h ∈ Γ ∧ h ≠ 1 ∧ ∃ y, spaceMap h y ≠ -y} := ⟨_, rfl⟩
    have hSfin : S.Finite := by
      rw [hSdef]
      exact (hΓ.finite.subset fun h hh => hh.1).image _
    obtain ⟨u₂, v₂, hu₂, hv₂, huv₂, hgen⟩ := exists_plane_not_turned
      (EuclideanSpace.basisFun (Fin 4) ℝ) hSfin
      (by rw [hSdef]; rintro _ ⟨h, ⟨hh, -, -⟩, rfl⟩; exact hA h hh)
      (by rw [hSdef]; rintro _ ⟨h, ⟨hh, hh1, -⟩, rfl⟩; exact hAfix h hh hh1)
      (by rw [hSdef]; rintro _ ⟨h, ⟨-, -, hy⟩, rfl⟩; exact hy)
    obtain ⟨-, ⟨h, hh, hhP⟩, -⟩ := hP u₂ v₂ hu₂ hv₂ huv₂
    obtain ⟨h1, h2⟩ := hret u₂ v₂ h hh _ hhP
    have hh' : h = 1 ∨ ∀ y, spaceMap h y = -y := by
      by_contra hc'
      push Not at hc'
      exact hgen (spaceMap h) (by rw [hSdef]; exact ⟨h, ⟨hh, hc'.1, hc'.2⟩, rfl⟩) _ _ h1 h2
    have hcosP : Real.cos (len / s) = ⟪spaceMap h u₂, u₂⟫ := by
      rw [h1, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hu₂, real_inner_comm, huv₂]
      ring
    rcases hh' with rfl | hneg
    · -- the plane returns only after a full turn: `len/s ≥ 2π > θ`
      rw [spaceMap_one, real_inner_self_eq_norm_sq, hu₂, one_pow] at hcosP
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcosP
      have hpos' : (0 : ℝ) < n * (2 * Real.pi) := by rw [hn]; exact hP0
      have hn1 : (1 : ℝ) ≤ n := by
        have : (0 : ℝ) < n := pos_of_mul_pos_left hpos' (by positivity)
        exact_mod_cast (show (0 : ℤ) < n by exact_mod_cast this)
      have : 2 * Real.pi ≤ len / s := by
        rw [← hn]
        nlinarith [Real.pi_pos]
      linarith
    · -- `−1` is in `Γ`: the plane returns after `π` at the soonest, so `len/s ≥ π`
      rw [hneg, inner_neg_left, real_inner_self_eq_norm_sq, hu₂, one_pow] at hcosP
      obtain ⟨n, hn⟩ := Real.cos_eq_neg_one_iff.1 hcosP
      have hPπ : Real.pi ≤ len / s := by
        rw [← hn]
        have hn0 : (0 : ℝ) ≤ n := by
          by_contra hlt
          push Not at hlt
          have h' : n < 0 := by exact_mod_cast hlt
          have h'' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
          rw [← hn] at hP0
          nlinarith [Real.pi_pos]
        nlinarith [Real.pi_pos]
      -- `h * g` is in `Γ`, is `−g` on space, and turns the plane of `g` by `θ + π`
      have hhg : h * g ∈ Γ := Γ.mul_mem hh hg
      have hAhg : ∀ y, spaceMap (h * g) y = -(spaceMap g y) := fun y => by
        rw [hAmul h g hh hg, hneg]
      have hAu' : spaceMap (h * g) u = Real.cos (θ + Real.pi) • u + Real.sin (θ + Real.pi) • w := by
        rw [hAhg, hAu, Real.cos_add_pi, Real.sin_add_pi]
        module
      have hAw' : spaceMap (h * g) w =
          (-Real.sin (θ + Real.pi)) • u + Real.cos (θ + Real.pi) • w := by
        rw [hAhg, hAw, Real.cos_add_pi, Real.sin_add_pi]
        module
      rcases lt_trichotomy θ Real.pi with hlt | heq | hgt
      · linarith
      · -- `θ = π`: `h * g` fixes `u`, so `h * g = 1` and `g = −1` on space
        have hfixu : spaceMap (h * g) u = u := by
          rw [hAu', heq, ← two_mul, Real.cos_two_pi, Real.sin_two_pi, one_smul, zero_smul, add_zero]
        have hhg1 : h * g = 1 := by
          by_contra hne
          have := hAfix (h * g) hhg hne u hfixu
          rw [this, norm_zero] at hu
          exact zero_ne_one hu
        apply hgneg.elim
        intro y hy
        have := hAhg y
        rw [hhg1, spaceMap_one] at this
        exact hy (neg_eq_iff_eq_neg.1 this.symm)
      · -- `θ > π`: the plane returns after `θ − π < π`
        have hAu'' : spaceMap (h * g) u =
            Real.cos (θ - Real.pi) • u + Real.sin (θ - Real.pi) • w := by
          rw [hAu', Real.cos_sub_pi, Real.sin_sub_pi, Real.cos_add_pi, Real.sin_add_pi]
        have hAw'' : spaceMap (h * g) w =
            (-Real.sin (θ - Real.pi)) • u + Real.cos (θ - Real.pi) • w := by
          rw [hAw', Real.cos_sub_pi, Real.sin_sub_pi, Real.cos_add_pi, Real.sin_add_pi]
        have := hleast (θ - Real.pi) (by linarith)
          ⟨h * g, hhg, hturn u w (h * g) hhg _ hAu'' hAw''⟩
        linarith
  -- no map of `Γ` is `−1` on space: the rings through `B` are drawn through one place of `B` and
  -- one place of its opposite
  have hone : ∀ g ∈ Γ, g = 1 := by
    intro g hg
    rcases hpm g hg with h | hneg
    · exact h
    · exfalso
      obtain ⟨b, hbdef⟩ : ∃ b : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)),
        b = EuclideanSpace.basisFun (Fin 4) ℝ := ⟨_, rfl⟩
      have hb : ∀ i j, ⟪b i, b j⟫ = if i = j then 1 else 0 := orthonormal_iff_ite.1 b.orthonormal
      have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
      have hb12 : ⟪b 1, b 2⟫ = 0 := by rw [hb]; simp
      -- every great circle returns after `π`: `len/s ≤ π`
      obtain ⟨hP0, ⟨h₁, hh₁, hh₁P⟩, hleast⟩ := hP (b 1) (b 2) (hbn 1) (hbn 2) hb12
      have hPπ : len / s ≤ Real.pi := hleast Real.pi Real.pi_pos ⟨g, hg, hturn _ _ g hg Real.pi
        (by rw [hneg, Real.cos_pi, Real.sin_pi]; module)
        (by rw [hneg, Real.cos_pi, Real.sin_pi]; module)⟩
      -- and the return after the least period `len/s` is by `±1`, so `len/s = π`
      obtain ⟨h1, -⟩ := hret (b 1) (b 2) h₁ hh₁ _ hh₁P
      have hcosP : Real.cos (len / s) = ⟪spaceMap h₁ (b 1), b 1⟫ := by
        rw [h1, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq, hbn 1, real_inner_comm, hb12]
        ring
      have hlen : len = Real.pi * s := by
        rcases hpm h₁ hh₁ with rfl | hneg₁
        · rw [spaceMap_one, real_inner_self_eq_norm_sq, hbn 1, one_pow] at hcosP
          obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcosP
          have hpos' : (0 : ℝ) < n * (2 * Real.pi) := by rw [hn]; exact hP0
          have hn1 : (1 : ℝ) ≤ n := by
            have : (0 : ℝ) < n := pos_of_mul_pos_left hpos' (by positivity)
            exact_mod_cast (show (0 : ℤ) < n by exact_mod_cast this)
          exfalso
          nlinarith [Real.pi_pos]
        · rw [hneg₁, inner_neg_left, real_inner_self_eq_norm_sq, hbn 1, one_pow] at hcosP
          obtain ⟨n, hn⟩ := Real.cos_eq_neg_one_iff.1 hcosP
          have h0 : (0 : ℝ) < Real.pi + n * (2 * Real.pi) := by rw [hn]; exact hP0
          have h1' : Real.pi + n * (2 * Real.pi) ≤ Real.pi := by rw [hn]; exact hPπ
          have hlt : (-1 : ℝ) < 2 * n := by nlinarith [Real.pi_pos]
          have hle : (2 * n : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
          have hlt' : (-1 : ℤ) < 2 * n := by exact_mod_cast hlt
          have hle' : 2 * n ≤ (0 : ℤ) := by exact_mod_cast hle
          have hn0 : n = 0 := by omega
          rw [hn0] at hn
          simp only [Int.cast_zero, zero_mul, add_zero] at hn
          rw [hn]
          field_simp
      -- two different largest rings through `B`
      have hL : 4 ≤ L := H.four_le
      obtain ⟨l, l', hl, hl', hll'⟩ : ∃ l l' : H.Loop, B ∈ H.cells l ∧ B ∈ H.cells l' ∧ l ≠ l' := by
        have hcard := H.two_mul_card_through hL B
        obtain ⟨l, hl, l', hl', hne⟩ :=
          Finset.one_lt_card.1 (show 1 < (H.through B).card by omega)
        exact ⟨l, l', H.mem_through.1 hl, H.mem_through.1 hl', hne⟩
      obtain ⟨γ, pl, hrings, hcells, hplaces⟩ := hdrawn
      -- in this quotient a place is given up to sign
      have hsign : ∀ y z : EuclideanSpace ℝ (Fin 4),
          (∃ g' ∈ Γ, ((0 : ℝ), y) = g' ((0 : ℝ), z)) ↔ (y = z ∨ y = -z) := by
        intro y z
        constructor
        · rintro ⟨g', hg', e⟩
          rw [hAy g' hg'] at e
          rcases hpm g' hg' with rfl | hneg'
          · left; rw [spaceMap_one] at e; exact (Prod.ext_iff.1 e).2
          · right; rw [hneg'] at e; exact (Prod.ext_iff.1 e).2
        · rintro (rfl | rfl)
          · exact ⟨1, Γ.one_mem, rfl⟩
          · exact ⟨g, hg, by rw [hAy g hg, hneg]⟩
      have hcomb : ∀ {y z w : EuclideanSpace ℝ (Fin 4)},
          (y = z ∨ y = -z) → (z = w ∨ z = -w) → (y = w ∨ y = -w) := by
        rintro y z w (rfl | rfl) (rfl | rfl) <;> simp
      have hsymm : ∀ {y z : EuclideanSpace ℝ (Fin 4)}, (y = z ∨ y = -z) → (z = y ∨ z = -y) := by
        rintro y z (rfl | rfl) <;> simp
      have hnegl : ∀ {y z : EuclideanSpace ℝ (Fin 4)}, (-y = z ∨ -y = -z) → (y = z ∨ y = -z) := by
        rintro y z (h | h)
        · right; rw [← h, neg_neg]
        · left; exact neg_inj.1 h
      -- a drawn ring: its cell `j` steps from `B` sits at the angle `jπ/L` from `B`'s place
      have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
      have hcircle : ∀ (l₁ : H.Loop) (hl₁ : B ∈ H.cells l₁),
          ∃ a c : EuclideanSpace ℝ (Fin 4), ‖a‖ = s ∧ ‖c‖ = s ∧ ⟪a, c⟫ = 0 ∧
            ∀ X ∈ H.cells l₁, (Real.cos ((P.offset l₁ B X : ℝ) * Real.pi / L) • a +
              Real.sin ((P.offset l₁ B X : ℝ) * Real.pi / L) • c = pl l₁ hl₁ X) ∨
              (Real.cos ((P.offset l₁ B X : ℝ) * Real.pi / L) • a +
              Real.sin ((P.offset l₁ B X : ℝ) * Real.pi / L) • c = -pl l₁ hl₁ X) := by
        intro l₁ hl₁
        obtain ⟨hslot, hclose⟩ := hrings l₁ hl₁
        obtain ⟨a, c, ha, hc, hac, hpos'⟩ := sphereSlots_pos hk hslot
        rw [← hsdef] at ha hc hpos'
        -- the drawn ring closes with `Lℓ_c`, the one length `len`
        have hLℓ : (L : ℝ) * ℓc = len := by
          obtain ⟨P₁, hP₁, hret₁, hmin₁, hlen₁⟩ := hclose
          obtain ⟨P₂, hP₂, hret₂, hmin₂, hlen₂⟩ := hring _ hslot
          have e : P₁ = P₂ := le_antisymm (hmin₁ P₂ hP₂ hret₂) (hmin₂ P₁ hP₁ hret₁)
          rw [← hlen₁ 0, ← hlen₂ 0, e]
        have hv : 0 < speed (γ l₁ hl₁) 0 := Real.sqrt_pos.2 (hslot.2.2 0)
        refine ⟨a, c, ha, hc, hac, fun X hX => ?_⟩
        obtain ⟨g', hg', e⟩ := hcells l₁ hl₁ X hX
        have hin : ((γ l₁ hl₁).pos ((P.offset l₁ B X : ℝ) * ℓc / speed (γ l₁ hl₁) 0)).1 = 0 :=
          hslot.2.1 _
        have e' : ((0 : ℝ), ((γ l₁ hl₁).pos ((P.offset l₁ B X : ℝ) * ℓc / speed (γ l₁ hl₁) 0)).2)
            = g' ((0 : ℝ), pl l₁ hl₁ X) := by
          rw [← e]; exact Prod.ext hin.symm rfl
        have hℓ : ℓc = Real.pi * s / L := by rw [eq_div_iff hL0.ne', mul_comm, hLℓ, hlen]
        have hang : speed (γ l₁ hl₁) 0 / s * ((P.offset l₁ B X : ℝ) * ℓc / speed (γ l₁ hl₁) 0)
            = (P.offset l₁ B X : ℝ) * Real.pi / L := by
          rw [hℓ]
          field_simp
        have := (hsign _ _).1 ⟨g', hg', e'⟩
        rw [hpos', hang] at this
        exact this
      obtain ⟨a, c, ha, hc, hac, hA⟩ := hcircle l hl
      obtain ⟨a', c', ha', hc', hac', hA'⟩ := hcircle l' hl'
      -- the angles of `B`, of its opposite, and of the cells one step from `B`, on and back
      have hθ0 : ∀ l₁, (P.offset l₁ B B : ℝ) * Real.pi / L = 0 := fun l₁ => by
        rw [P.offset_self]; simp
      obtain ⟨hf, hL2, hh⟩ := H.exists_half hL
      have hθh : ∀ l₁ (hl₁ : B ∈ H.cells l₁),
          (P.offset l₁ B (H.opp B) : ℝ) * Real.pi / L = Real.pi / 2 := fun l₁ hl₁ => by
        rw [P.offset_opp_self hL l₁ B hl₁, hh]
        have hL' : (L : ℝ) = 2 * hf := by exact_mod_cast hL2
        have hf0 : (hf : ℝ) ≠ 0 := by exact_mod_cast (show hf ≠ 0 by omega)
        rw [hL']
        field_simp
      have hθ1 : ((1 : ℕ) : ℝ) * Real.pi / L = Real.pi / L := by simp
      have hθL : ((L - 1 : ℕ) : ℝ) * Real.pi / L = Real.pi - Real.pi / L := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        field_simp
      -- `B` is drawn at one place on both rings: `a' = ±a`
      have hBl := hA B hl
      have hBl' := hA' B hl'
      rw [hθ0, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] at hBl hBl'
      have hBB : pl l hl B = pl l' hl' B ∨ pl l hl B = -pl l' hl' B :=
        (hsign _ _).1 ((hplaces l hl l' hl' B hl B hl').2 rfl)
      have haa : a' = a ∨ a' = -a := hcomb hBl' (hcomb (hsymm hBB) (hsymm hBl))
      -- and so is its opposite, a quarter turn on: `c' = ±c`
      have hOl := hA (H.opp B) (H.opp_mem l B hl)
      have hOl' := hA' (H.opp B) (H.opp_mem l' B hl')
      rw [hθh l hl, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add] at hOl
      rw [hθh l' hl', Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul,
        zero_add] at hOl'
      have hOO : pl l hl (H.opp B) = pl l' hl' (H.opp B) ∨
          pl l hl (H.opp B) = -pl l' hl' (H.opp B) :=
        (hsign _ _).1 ((hplaces l hl l' hl' _ (H.opp_mem l B hl) _ (H.opp_mem l' B hl')).2 rfl)
      have hcc : c' = c ∨ c' = -c := hcomb hOl' (hcomb (hsymm hOO) (hsymm hOl))
      -- the cell one step from `B` on `l'`, and the cells one step from `B` on `l`, on and back
      obtain ⟨X', hX', hoX'⟩ := P.exists_offset l' B 1 (by omega)
      obtain ⟨X₁, hX₁, hoX₁⟩ := P.exists_offset l B 1 (by omega)
      obtain ⟨Y, hY, hoY⟩ := P.exists_offset l B (L - 1) (by omega)
      have hpX' := hA' X' hX'
      have hpX₁ := hA X₁ hX₁
      have hpY := hA Y hY
      rw [hoX', hθ1] at hpX'
      rw [hoX₁, hθ1] at hpX₁
      rw [hoY, hθL, Real.cos_pi_sub, Real.sin_pi_sub] at hpY
      -- two cells at one place are one cell, on both rings, and not `B` or its opposite
      have hcontra : ∀ Z ∈ H.cells l, Z ∈ H.cells l' → P.offset l B Z ≠ 0 →
          P.offset l B Z ≠ L / 2 → False := by
        intro Z hZ hZ' h0 hh'
        have hZB : Z ≠ B := fun e => h0 (by rw [e, P.offset_self])
        have hZO : Z ≠ H.opp B := fun e => hh' (by rw [e, P.offset_opp_self hL l B hl])
        exact hll' (H.unique_loop B Z l l' hZB hZO hl hZ hl' hZ')
      have hsame : ∀ Z ∈ H.cells l,
          (pl l hl Z = pl l' hl' X' ∨ pl l hl Z = -pl l' hl' X') → Z = X' :=
        fun Z hZ h => (hplaces l hl l' hl' Z hZ X' hX').1 ((hsign _ _).2 h)
      rcases haa with haa | haa <;> rcases hcc with hcc | hcc <;> rw [haa, hcc] at hpX'
      · -- the same circle, run the same way: `X'` falls on the cell one step on
        have hX₁X' : X₁ = X' := hsame X₁ hX₁ (hcomb (hsymm hpX₁) hpX')
        exact hcontra X₁ hX₁ (hX₁X' ▸ hX') (by omega) (by omega)
      · -- the same circle, run the other way: `X'` falls on the cell one step back
        have e : Real.cos (Real.pi / L) • a + Real.sin (Real.pi / L) • -c =
            -((-Real.cos (Real.pi / L)) • a + Real.sin (Real.pi / L) • c) := by module
        rw [e] at hpX'
        have hYX' : Y = X' := hsame Y hY (hcomb (hsymm hpY) (hnegl hpX'))
        exact hcontra Y hY (hYX' ▸ hX') (by omega) (by omega)
      · have e : Real.cos (Real.pi / L) • -a + Real.sin (Real.pi / L) • c =
            (-Real.cos (Real.pi / L)) • a + Real.sin (Real.pi / L) • c := by module
        rw [e] at hpX'
        have hYX' : Y = X' := hsame Y hY (hcomb (hsymm hpY) hpX')
        exact hcontra Y hY (hYX' ▸ hX') (by omega) (by omega)
      · have e : Real.cos (Real.pi / L) • -a + Real.sin (Real.pi / L) • -c =
            -(Real.cos (Real.pi / L) • a + Real.sin (Real.pi / L) • c) := by module
        rw [e] at hpX'
        have hX₁X' : X₁ = X' := hsame X₁ hX₁ (hcomb (hsymm hpX₁) (hnegl hpX'))
        exact hcontra X₁ hX₁ (hX₁X' ▸ hX') (by omega) (by omega)
  -- `Γ` is trivial, and a great circle returns only after a full turn
  have hbot : Γ = ⊥ := (Subgroup.eq_bot_iff_forall Γ).2 hone
  refine ⟨hbot, ?_⟩
  obtain ⟨f₁, f₂, hf₁, hf₂, hf₁₂⟩ := exists_orthonormal_pair hE
  obtain ⟨hP0, ⟨g, hg, hgP⟩, hleast⟩ := hP f₁ f₂ hf₁ hf₂ hf₁₂
  have hP2 : len / s ≤ 2 * Real.pi := hleast _ Real.two_pi_pos ⟨1, Γ.one_mem, hturn _ _ 1 Γ.one_mem
    (2 * Real.pi) (by rw [spaceMap_one, Real.cos_two_pi, Real.sin_two_pi]; module)
    (by rw [spaceMap_one, Real.cos_two_pi, Real.sin_two_pi]; module)⟩
  obtain rfl := hone g hg
  obtain ⟨h1, -⟩ := hret f₁ f₂ 1 Γ.one_mem _ hgP
  have hcosP : Real.cos (len / s) = 1 := by
    have e := congrArg (fun x => ⟪x, f₁⟫) h1
    simp only [spaceMap_one, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hf₁,
      one_pow, mul_one, real_inner_comm f₁ f₂, hf₁₂, mul_zero, add_zero] at e
    exact e.symm
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcosP
  have hpos' : (0 : ℝ) < n * (2 * Real.pi) := by rw [hn]; exact hP0
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℝ) < n := pos_of_mul_pos_left hpos' (by positivity)
    exact_mod_cast (show (0 : ℤ) < n by exact_mod_cast this)
  have hP2' : 2 * Real.pi ≤ len / s := by
    rw [← hn]
    nlinarith [Real.pi_pos]
  have e : len / s = 2 * Real.pi := le_antisymm hP2 hP2'
  rw [← hsdef, ← e]
  field_simp

/-! ### The cosmological constant -/

/-- **The cosmological constant from the sources** (Sec. IV.D), every link named.

* The geometry of the space at an instant is the same at every slot (`hsame`, proved in
  `Solution` from Postulate 1's first sentence applied to the geometry), and every geodesic of that
  space closes (`hclose`, Postulate 1's first sentence applied to the space at an instant, a ring
  along every geodesic).  By Schur's lemma, Hopf–Rinow and the Killing–Hopf theorem the space is a
  space form (`hKH`, Riemannian geometry, `Sources.Geometry.space_form`).
* Without matter the vacuum equations hold with `Λ` (`hvac`, derived in
  `Einstein.einstein_equations` and `Einstein.vacuum_of_field_equations`), and on the
  time-symmetric slice of an observer at rest Einstein's constraint gives `3K = Λ`
  (`hcon`, `Sources.Geometry.constraint`).
* The slice's rings make the form the sphere (`hslice`, `slice_sphere`), and with the rings
  through the observer's cell `B` drawn in it (`hdrawn`, Sec. II's cell and Postulate 2's last
  sentence with its first clause, `Sources.P2.rings_drawn`) they make its group trivial and its
  great circles of length `2π√(1/K)` (`sphere_rings`).

Then `len = 2π√(1/K) = 2π√(3/Λ)`, and with `len = Lℓ_c = 2πR_Λ`, `Λ = 3/R_Λ²`.  The drawn rings
close with `Lℓ_c`, `L` the register's number of cells per ring, and every great circle with
`R.L ℓ_c` (`hslice`), so the two hypotheses together give `L = R.L` (`Condition.same_L`), which
`sphere_rings` uses through the uniqueness of a closed curve's least period; where `L ≠ R.L` they
cannot both hold. -/
theorem cosmological_constant_of_sources {Slot Gm Sp : Type*} (H : Horizon L) [NeZero L]
    (P : H.Positions) (B : H.Cell)
    (R : Register.Reg) {Λ : ℝ} (geom : Slot → Gm) (hsame : ∀ σ τ : Slot, geom σ = geom τ)
    (Closes : Slot → Prop) (hclose : ringsAlong H Set.univ Closes)
    (sp : Sp) (embedSp : (K : ℝ) → SpaceForm K → Sp)
    (hKH : (∀ σ τ : Slot, geom σ = geom τ) → (∀ σ, Closes σ) →
      ∃ K, ∃ c : SpaceForm K, sp = embedSp K c)
    (M : Register.Einstein.Spacetime) (hvac : Register.Einstein.VacuumEinstein M Set.univ Λ)
    (hcon : Register.Einstein.VacuumEinstein M Set.univ Λ →
      ∀ K (c : SpaceForm K), sp = embedSp K c → 3 * K = Λ)
    (hslice : ∀ K (c : SpaceForm K), sp = embedSp K c → SliceIsQubits H (R.L * R.ℓc) c)
    (hdrawn : ∀ K Γ (hK : 0 < K) (hΓ : SphereQuotient (1 / K) Γ),
      sp = embedSp K (SpaceForm.sphere Γ hK hΓ) → RingsDrawn H P (1 / K) Γ R.ℓc B) :
    Λ = 3 / R.RL ^ 2 := by
  have hcl : ∀ σ, Closes σ := fun σ =>
    ((mem_described_admissible _ σ).1 (hclose σ (Set.mem_univ σ))).2
  obtain ⟨K, c, hc⟩ := hKH hsame hcl
  have h3K := hcon hvac K c hc
  obtain ⟨Γ, hK, hΓ, rfl⟩ := slice_sphere c (hslice K c hc)
  have hk : 0 < 1 / K := one_div_pos.2 hK
  have hS := hslice K _ hc
  obtain ⟨-, hlen⟩ := sphere_rings hk hΓ
    (fun γ hγ => ((mem_described_admissible _ _).1 (hS γ hγ)).2) H P B (hdrawn K Γ hK hΓ hc)
  -- `Lℓ_c = 2πR_Λ = 2π√(1/K)`, so `1/K = R_Λ²` and `Λ = 3K = 3/R_Λ²`
  have hRL := R.RL_pos
  have e : R.L * R.ℓc = 2 * Real.pi * R.RL := by
    unfold Register.Reg.RL
    rw [R.pi_def]
    field_simp
  rw [e] at hlen
  have hsq : Real.sqrt (1 / K) = R.RL := by
    have := Real.pi_pos
    nlinarith [hlen]
  have hK' : 1 / K = R.RL ^ 2 := by
    rw [← hsq, Real.sq_sqrt hk.le]
  rw [← h3K]
  field_simp
  rw [one_div] at hK'
  have : K = 1 / R.RL ^ 2 := by
    rw [← inv_inv K, hK', one_div]
  rw [this]
  field_simp

end Space
