import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

/-!
# Einstein's equations from the Clausius relation and the first law (Sec. III)

Jacobson's step [T. Jacobson, Phys. Rev. Lett. **75**, 1260 (1995)] applies the Clausius relation
`δQ = T dS` to every local Rindler horizon through every point.  With the Unruh temperature, one
entropy density `η₀` on every local horizon, the heat the boost-energy flux of matter, and the
Raychaudhuri equation for the change of the horizon's area, it gives, at every point and for every
null vector `k` there,

  `R_ab k^a k^b = κ T_ab k^a k^b`, with `κ = 2πk_B/(ℏcη₀)`.

That relation is `Sources.Derived.clausius`, which `Main.jacobson_step` derives from the
Raychaudhuri equation (`Sources.Geometry.raychaudhuri`), the register's entropy on a local horizon
(`Sources.P1.local_entropy`) and the heat that crosses it (`Sources.Thermo.local_clausius`).  It
fixes Einstein's equations only up to
a term proportional to the metric, since a stress tensor proportional to the metric has no flux
through a null surface.  Jacobson fixes that term with the local conservation of energy and
momentum, `∇^a T_ab = 0`; here that law is the first law of thermodynamics, applied to every small
region and for every observer (`Sources.Thermo.first_law_local`).

* `eq_smul_eta_of_null`: a symmetric form that vanishes on every null vector is a multiple of the
  metric (linear algebra).  So at every point `R_ab − κT_ab = φ g_ab` for some number `φ` there
  (`einstein_up_to_metric`): Einstein's equations up to a multiple of the metric, `TraceFree`.
* `eq_zero_of_timelike`: the first law for every observer `u`, `(∇^a T_ab) u^b = 0`, gives
  `∇^a T_ab = 0`, since the timelike vectors span the space of vectors.
* `einstein_equations`: with `∇^a T_ab = 0`, the contracted Bianchi identity makes `φ + ½κT` one
  number on the spacetime (`Sources.Geometry.bianchi`), the cosmological constant `Λ`, and Einstein's
  equations `R_ab − ½R g_ab + Λ g_ab = κ T_ab` hold at every point (`FieldEquations`).  Without
  matter they are the vacuum equations `R_ab = Λ g_ab` (`vacuum_of_field_equations`).
* `newtonian_coefficient`: in the static weak field of matter at rest, where the Ricci tensor is
  `∇²Φ/c²` times the identity (`Sources.Geometry.weak_field`), the relation gives `∇²Φ = κc⁴ρ/2`; Newton's
  law `∇²Φ = 4πGρ`, which defines `G`, then gives `κ = 8πG/c⁴`.  With Jacobson's `κ`,
  `G = c³k_B/(4ℏη₀)` (`G_of_clausius`).
* `flow_geodesic`, `null_dust_of_current`, `null_geodesic`: the conservation law moves matter and
  light on geodesics.  For matter moving as dust, `T_ab = ρ u_a u_b`, the Leibniz rule makes
  `∇^a T_ab = D u_b + ρ A_b`, with `A` the acceleration of the flow, orthogonal to `u`; conservation
  then gives `A = 0`.  Light moves at `c`, so its energy current lies along a null `k` for every
  observer and its stress tensor is `ρ k_a k_b`; conservation then gives an acceleration along `k`,
  so the rays are null geodesics.

The components are those in a local inertial frame at the point, where the metric is
`η = diag(−1, 1, 1, 1)` (`eta`); the time coordinate is `ct`.
-/

namespace Register.Einstein

open Matrix

/-- **The metric in a local inertial frame**, `diag(−1, 1, 1, 1)`. -/
def eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

/-- the value of the form with matrix `S` on the vector `k`, `S_ab k^a k^b` -/
def quad (S : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : ℝ := k ⬝ᵥ (S *ᵥ k)

/-- **A null vector** of the frame: `η_ab k^a k^b = 0`. -/
def IsNull (k : Fin 4 → ℝ) : Prop := quad eta k = 0

/-- the form on a vector given by its four components -/
lemma quad_vec (S : Matrix (Fin 4) (Fin 4) ℝ) (a b c d : ℝ) :
    quad S ![a, b, c, d] =
      a * (S 0 0 * a + S 0 1 * b + S 0 2 * c + S 0 3 * d) +
      b * (S 1 0 * a + S 1 1 * b + S 1 2 * c + S 1 3 * d) +
      c * (S 2 0 * a + S 2 1 * b + S 2 2 * c + S 2 3 * d) +
      d * (S 3 0 * a + S 3 1 * b + S 3 2 * c + S 3 3 * d) := by
  simp [quad, dotProduct, mulVec, Fin.sum_univ_four]

/-- the metric on a vector given by its four components, `−a² + b² + c² + d²` -/
lemma quad_eta_vec (a b c d : ℝ) :
    quad eta ![a, b, c, d] = -(a * a) + b * b + c * c + d * d := by
  rw [quad_vec]
  simp [eta, diagonal]

/-- the vector of four components is null exactly when `−a² + b² + c² + d² = 0` -/
lemma isNull_vec (a b c d : ℝ) :
    IsNull ![a, b, c, d] ↔ -(a * a) + b * b + c * c + d * d = 0 := by
  unfold IsNull
  rw [quad_eta_vec]

/-- **A symmetric form that vanishes on every null vector is a multiple of the metric**: if
`S_ab k^a k^b = 0` for every null `k`, then `S = −S₀₀ η`.  The null vectors `(1, ±e_i)` give
`S₀ᵢ = 0` and `Sᵢᵢ = −S₀₀`; the null vectors `(5, 3, 4, 0)`, `(5, 3, 0, 4)` and `(5, 0, 3, 4)` give
`Sᵢⱼ = 0` for `i ≠ j`. -/
theorem eq_smul_eta_of_null (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : S.IsSymm)
    (h : ∀ k, IsNull k → quad S k = 0) : S = (-(S 0 0)) • eta := by
  have hs : ∀ i j, S j i = S i j := fun i j => hS.apply i j
  have q : ∀ a b c d : ℝ, -(a * a) + b * b + c * c + d * d = 0 →
      a * (S 0 0 * a + S 0 1 * b + S 0 2 * c + S 0 3 * d) +
      b * (S 1 0 * a + S 1 1 * b + S 1 2 * c + S 1 3 * d) +
      c * (S 2 0 * a + S 2 1 * b + S 2 2 * c + S 2 3 * d) +
      d * (S 3 0 * a + S 3 1 * b + S 3 2 * c + S 3 3 * d) = 0 := by
    intro a b c d hn
    rw [← quad_vec]
    exact h _ ((isNull_vec a b c d).2 hn)
  have e1 := q 1 1 0 0 (by norm_num)
  have e1' := q 1 (-1) 0 0 (by norm_num)
  have e2 := q 1 0 1 0 (by norm_num)
  have e2' := q 1 0 (-1) 0 (by norm_num)
  have e3 := q 1 0 0 1 (by norm_num)
  have e3' := q 1 0 0 (-1) (by norm_num)
  have e12 := q 5 3 4 0 (by norm_num)
  have e13 := q 5 3 0 4 (by norm_num)
  have e23 := q 5 0 3 4 (by norm_num)
  have s10 := hs 0 1
  have s20 := hs 0 2
  have s30 := hs 0 3
  have s21 := hs 1 2
  have s31 := hs 1 3
  have s32 := hs 2 3
  have h01 : S 0 1 = 0 := by linarith
  have h02 : S 0 2 = 0 := by linarith
  have h03 : S 0 3 = 0 := by linarith
  have h11 : S 1 1 = -S 0 0 := by linarith
  have h22 : S 2 2 = -S 0 0 := by linarith
  have h33 : S 3 3 = -S 0 0 := by linarith
  have h12 : S 1 2 = 0 := by linarith
  have h13 : S 1 3 = 0 := by linarith
  have h23 : S 2 3 = 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, diagonal] <;> linarith

/-- the form of a difference -/
lemma quad_sub (A B : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    quad (A - B) k = quad A k - quad B k := by
  simp [quad, sub_mulVec, dotProduct_sub]

/-- the form of a multiple -/
lemma quad_smul (c : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    quad (c • A) k = c * quad A k := by
  simp [quad, smul_mulVec, dotProduct_smul]

/-- the symmetric part of a matrix -/
noncomputable def symmPart (S : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (S + Sᵀ)

lemma symmPart_isSymm (S : Matrix (Fin 4) (Fin 4) ℝ) : (symmPart S).IsSymm := by
  unfold symmPart Matrix.IsSymm
  rw [transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- a form and its symmetric part have the same values -/
lemma quad_symmPart (S : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    quad (symmPart S) k = quad S k := by
  simp only [symmPart, quad_smul]
  simp [quad, dotProduct, mulVec, Fin.sum_univ_four, transpose_apply]
  ring

/-- **A spacetime as the files see it**: its points, and at each point, in a local inertial frame
there, the components of its Ricci tensor, of the stress tensor of matter and of its divergence.  The Ricci tensor is
symmetric (`ric_symm`), as the Ricci tensor of the Levi-Civita connection is [R. M. Wald, *General
Relativity* (1984), Sec. 3.2].  Only the values `T_ab k^a k^b` of the stress tensor enter, so its
symmetric part is what the relations fix (`symmPart`). -/
structure Spacetime where
  /-- the points -/
  Pt : Type
  /-- the Ricci tensor at a point, in a local inertial frame there -/
  ric : Pt → Matrix (Fin 4) (Fin 4) ℝ
  /-- the stress tensor of matter at a point, in the same frame -/
  stress : Pt → Matrix (Fin 4) (Fin 4) ℝ
  /-- the divergence `∇^a T_ab` of the stress tensor at a point, in the same frame -/
  divStress : Pt → Fin 4 → ℝ
  /-- the Ricci tensor is symmetric -/
  ric_symm : ∀ p, (ric p).IsSymm

/-- **Einstein's equations up to a multiple of the metric**, with the coefficient `κ`: at every
point `R_ab − κT_ab = φ g_ab` for some number `φ` there. -/
def TraceFree (M : Spacetime) (κ : ℝ) : Prop :=
  ∀ p, ∃ φ : ℝ, M.ric p - κ • symmPart (M.stress p) = φ • eta

/-- **The Clausius relation on every null vector gives Einstein's equations up to a multiple of the
metric**: if `R(k,k) = κT(k,k)` for every null `k` at every point, then `R − κT = φη` at every
point (`eq_smul_eta_of_null`). -/
theorem einstein_up_to_metric (M : Spacetime) (κ : ℝ)
    (h : ∀ p k, IsNull k → quad (M.ric p) k = κ * quad (M.stress p) k) : TraceFree M κ := by
  intro p
  refine ⟨-((M.ric p - κ • symmPart (M.stress p)) 0 0), eq_smul_eta_of_null _ ?_ fun k hk => ?_⟩
  · unfold Matrix.IsSymm
    rw [transpose_sub, transpose_smul, (M.ric_symm p).eq, (symmPart_isSymm _).eq]
  · rw [quad_sub, quad_smul, quad_symmPart, h p k hk, sub_self]

/-- **The vacuum equations with a cosmological constant** on a region `V`: `R_ab = Λ g_ab`. -/
def VacuumEinstein (M : Spacetime) (V : Set M.Pt) (Λ : ℝ) : Prop := ∀ p ∈ V, M.ric p = Λ • eta

/-- lowering the index of a nonzero vector gives a nonzero covector: `η k = (−k⁰, k¹, k², k³)` -/
lemma eta_mulVec_ne_zero {k : Fin 4 → ℝ} (hk : k ≠ 0) : eta *ᵥ k ≠ 0 := by
  intro h
  apply hk
  ext i
  have := congrFun h i
  fin_cases i <;> simp [eta, mulVec, diagonal, dotProduct] at this ⊢ <;> linarith

/-- **The trace with the metric**, `η^{ab} S_ab = −S₀₀ + S₁₁ + S₂₂ + S₃₃`: the scalar curvature `R`
for the Ricci tensor, the trace `T` for the stress tensor. -/
def trace (S : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -S 0 0 + S 1 1 + S 2 2 + S 3 3

lemma trace_add (A B : Matrix (Fin 4) (Fin 4) ℝ) : trace (A + B) = trace A + trace B := by
  simp only [trace, Matrix.add_apply]
  ring

lemma trace_smul (c : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) : trace (c • A) = c * trace A := by
  simp only [trace, Matrix.smul_apply, smul_eq_mul]
  ring

lemma trace_eta : trace eta = 4 := by
  simp [trace, eta, diagonal]
  norm_num

/-- **A timelike vector** of the frame, the four-velocity of an observer up to its length:
`η_ab u^a u^b < 0`. -/
def IsTimelike (u : Fin 4 → ℝ) : Prop := quad eta u < 0

/-- **The first law for every observer gives the conservation of energy and momentum** (Sec. III):
a covector `d` with `d_b u^b = 0` for every timelike `u` is zero, since `(1, 0, 0, 0)` and the
vectors `(1, ½e_i)` are timelike and span the space of vectors.  For `d = ∇^a T_ab`, the first law
for every observer gives `∇^a T_ab = 0`. -/
theorem eq_zero_of_timelike (d : Fin 4 → ℝ) (h : ∀ u, IsTimelike u → d ⬝ᵥ u = 0) : d = 0 := by
  have t : ∀ a b c e : ℝ, -(a * a) + b * b + c * c + e * e < 0 → d 0 * a + d 1 * b + d 2 * c + d 3 * e = 0 := by
    intro a b c e hn
    have := h ![a, b, c, e] (by unfold IsTimelike; rw [quad_eta_vec]; exact hn)
    simpa [dotProduct, Fin.sum_univ_four] using this
  have h0 := t 1 0 0 0 (by norm_num)
  have h1 := t 1 (1 / 2) 0 0 (by norm_num)
  have h2 := t 1 0 (1 / 2) 0 (by norm_num)
  have h3 := t 1 0 0 (1 / 2) (by norm_num)
  ext i
  fin_cases i <;> simp <;> linarith

/-- **Einstein's equations with the cosmological constant `Λ`** (Eq. (einstein)): at every point
`R_ab − ½R g_ab + Λ g_ab = κ T_ab`, the stress tensor taken by its symmetric part. -/
def FieldEquations (M : Spacetime) (κ Λ : ℝ) : Prop :=
  ∀ p, M.ric p - (trace (M.ric p) / 2) • eta + Λ • eta = κ • symmPart (M.stress p)

/-- **Einstein's equations, with matter** (Sec. III).  The Clausius relation on every null vector
(`h`, Jacobson's step) gives `R_ab − κT_ab = φ g_ab` at every point (`eq_smul_eta_of_null`).  The
first law for every observer (`hfirst`) gives `∇^a T_ab = 0` (`eq_zero_of_timelike`).  The
contracted Bianchi identity, `∇^a R_ab = ½∇_b R`, then gives `∇_b(φ + ½κT) = κ∇^a T_ab = 0`, so
`φ + ½κT` is one number `Λ` on the spacetime (`hbianchi`).  Since `R = κT + 4φ`, the multiple of the
metric is `φ = ½R − Λ`, and `R_ab − ½R g_ab + Λ g_ab = κ T_ab` at every point. -/
theorem einstein_equations (M : Spacetime) (κ : ℝ)
    (h : ∀ p k, IsNull k → quad (M.ric p) k = κ * quad (M.stress p) k)
    (hfirst : ∀ p u, IsTimelike u → M.divStress p ⬝ᵥ u = 0)
    (hbianchi : ∀ φ : M.Pt → ℝ, (∀ p, M.ric p - κ • symmPart (M.stress p) = φ p • eta) →
      (∀ p, M.divStress p = 0) → ∀ p q, φ p + κ / 2 * trace (symmPart (M.stress p)) =
        φ q + κ / 2 * trace (symmPart (M.stress q))) :
    ∃ Λ, FieldEquations M κ Λ := by
  set φ : M.Pt → ℝ := fun p => -((M.ric p - κ • symmPart (M.stress p)) 0 0) with hφdef
  have hφ : ∀ p, M.ric p - κ • symmPart (M.stress p) = φ p • eta := fun p => by
    refine eq_smul_eta_of_null _ ?_ fun k hk => ?_
    · unfold Matrix.IsSymm
      rw [transpose_sub, transpose_smul, (M.ric_symm p).eq, (symmPart_isSymm _).eq]
    · rw [quad_sub, quad_smul, quad_symmPart, h p k hk, sub_self]
  have hc := hbianchi φ hφ fun p => eq_zero_of_timelike _ (hfirst p)
  by_cases hne : Nonempty M.Pt
  · obtain ⟨p₀⟩ := hne
    refine ⟨φ p₀ + κ / 2 * trace (symmPart (M.stress p₀)), fun p => ?_⟩
    have hp := hc p p₀
    have e : M.ric p = κ • symmPart (M.stress p) + φ p • eta := by
      rw [← hφ p]; abel
    rw [← hp, e, trace_add, trace_smul, trace_smul, trace_eta]
    module
  · exact ⟨0, fun p => (hne ⟨p⟩).elim⟩

/-- **Without matter, Einstein's equations are the vacuum equations**: with `T = 0` the trace gives
`R = 4Λ`, so `R_ab = Λ g_ab`. -/
theorem vacuum_of_field_equations (M : Spacetime) (κ Λ : ℝ) (hE : FieldEquations M κ Λ)
    (V : Set M.Pt) (hvac : ∀ p ∈ V, M.stress p = 0) : VacuumEinstein M V Λ := by
  intro p hp
  have e := hE p
  rw [hvac p hp] at e
  simp only [symmPart, transpose_zero, add_zero, smul_zero] at e
  have e' : M.ric p = (trace (M.ric p) / 2 - Λ) • eta := by
    rw [sub_smul, ← sub_eq_zero, ← e]; abel
  have ht : trace (M.ric p) = 4 * Λ := by
    have := congrArg trace e'
    rw [trace_smul, trace_eta] at this
    linarith
  rw [e', ht]
  congr 1
  ring

/-- **Matter moving as dust moves on geodesics** (Sec. III).  Let the stress tensor at a point be
`ρ u_a u_b`, with `u` the unit four-velocity of the matter (`η(u,u) = −1`) and `ρ ≠ 0`.  By the
Leibniz rule its divergence is `∇^a T_ab = D u_b + ρ A_b`, with `D = ∇_a(ρu^a)` and `A_b = u^a∇_a u_b`
the acceleration of the flow (`hleib`), and `A_b u^b = 0`, since `u^b u_b = −1` along the flow
(`horth`).  If `∇^a T_ab = 0` (`hdiv`), its product with `u` gives `−D = 0`, so `ρA = 0` and `A = 0`:
the matter moves on geodesics. -/
theorem flow_geodesic {div u A : Fin 4 → ℝ} {ρ D : ℝ} (hu : quad eta u = -1) (hρ : ρ ≠ 0)
    (hleib : div = D • (eta *ᵥ u) + ρ • A) (horth : A ⬝ᵥ u = 0) (hdiv : div = 0) : A = 0 := by
  have hD : D = 0 := by
    have e := congrArg (fun w => w ⬝ᵥ u) hleib
    simp only [hdiv, zero_dotProduct, add_dotProduct, smul_dotProduct, horth, smul_eq_mul,
      mul_zero, add_zero] at e
    have hq : (eta *ᵥ u) ⬝ᵥ u = -1 := by rw [dotProduct_comm]; exact hu
    rw [hq] at e
    linarith
  rw [hdiv, hD, zero_smul, zero_add] at hleib
  exact (smul_eq_zero.1 hleib.symm).resolve_left hρ

/-- **The stress tensor of light** (Sec. III): a symmetric form `T` whose energy current `T_ab u^b`
lies along one covector `k` for every observer `u` is `ρ k_a k_b`.  The observers `(1, 0, 0, 0)`
and `(1, ½e_i)` make every column of `T` a multiple of `k`, `T_ab = k_a c_b`; symmetry gives
`k_a c_b = c_a k_b`, so `c = ρk`. -/
theorem null_dust_of_current {T : Matrix (Fin 4) (Fin 4) ℝ} (hT : T.IsSymm) {k : Fin 4 → ℝ}
    (hk : k ≠ 0) (h : ∀ u, IsTimelike u → ∃ s : ℝ, T *ᵥ u = s • k) :
    ∃ ρ : ℝ, T = ρ • vecMulVec k k := by
  have t : ∀ a b c e : ℝ, -(a * a) + b * b + c * c + e * e < 0 →
      ∃ s : ℝ, ∀ j, T j 0 * a + T j 1 * b + T j 2 * c + T j 3 * e = s * k j := by
    intro a b c e hn
    obtain ⟨s, hs⟩ := h ![a, b, c, e] (by unfold IsTimelike; rw [quad_eta_vec]; exact hn)
    refine ⟨s, fun j => ?_⟩
    have := congrFun hs j
    simpa [mulVec, dotProduct, Fin.sum_univ_four] using this
  obtain ⟨s0, h0⟩ := t 1 0 0 0 (by norm_num)
  obtain ⟨s1, h1⟩ := t 1 (1 / 2) 0 0 (by norm_num)
  obtain ⟨s2, h2⟩ := t 1 0 (1 / 2) 0 (by norm_num)
  obtain ⟨s3, h3⟩ := t 1 0 0 (1 / 2) (by norm_num)
  set c : Fin 4 → ℝ := ![s0, 2 * (s1 - s0), 2 * (s2 - s0), 2 * (s3 - s0)] with hc
  have hcol : ∀ i j, T j i = c i * k j := by
    intro i j
    have e0 := h0 j; have e1 := h1 j; have e2 := h2 j; have e3 := h3 j
    fin_cases i <;> simp [hc] <;> linarith
  obtain ⟨i₀, hi₀⟩ : ∃ i, k i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
    exact ⟨i, hi⟩
  have hsym : ∀ i j, c j * k i = c i * k j := fun i j => by
    rw [← hcol j i, ← hcol i j]; exact (hT.apply i j).symm
  refine ⟨c i₀ / k i₀, ?_⟩
  ext a b
  rw [hcol b a]
  simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  have hcb : c b = c i₀ / k i₀ * k b := by
    rw [div_mul_eq_mul_div, eq_div_iff hi₀]
    linarith [hsym i₀ b]
  rw [hcb]
  ring

/-- **Light moves on null geodesics** (Sec. III).  Let the stress tensor at a point be `ρ k_a k_b`,
`ρ ≠ 0`, with `k` the null direction of the light.  By the Leibniz rule its divergence is
`∇^a T_ab = D k_b + ρ A_b`, with `A_b = k^a∇_a k_b` the change of `k` along the ray (`hleib`).  If
`∇^a T_ab = 0`, then `A = −(D/ρ) k`: `k` changes along the ray only by its length, so the rays are
null geodesics. -/
theorem null_geodesic {div k A : Fin 4 → ℝ} {ρ D : ℝ} (hρ : ρ ≠ 0)
    (hleib : div = D • (eta *ᵥ k) + ρ • A) (hdiv : div = 0) :
    A = (-(D / ρ)) • (eta *ᵥ k) := by
  rw [hdiv] at hleib
  have e : ρ • A = (-D) • (eta *ᵥ k) := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hleib.symm
  calc A = ρ⁻¹ • (ρ • A) := by rw [smul_smul, inv_mul_cancel₀ hρ, one_smul]
    _ = (-(D / ρ)) • (eta *ᵥ k) := by
        rw [e, smul_smul]; congr 1; field_simp

/-- **Newton's law fixes the coefficient** (Sec. III): in the static weak field of matter at rest
the Ricci tensor is `A = ∇²Φ/c²` times the identity and the stress tensor is `diag(ρc², 0, 0, 0)`.
If `R(k,k) = κT(k,k)` for every null `k` there, the null vector `(1, 1, 0, 0)` gives `2A = κρc²`;
with Newton's law `∇²Φ = 4πGρ`, `A = 4πGρ/c²`, this is `G = κc⁴/8π`. -/
theorem newtonian_coefficient {κ A ρ c G : ℝ} (hρ : ρ ≠ 0) (hc : c ≠ 0)
    {Ric T : Matrix (Fin 4) (Fin 4) ℝ} (hR : Ric = A • (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (hT : T = Matrix.diagonal ![ρ * c ^ 2, 0, 0, 0])
    (h : ∀ k, IsNull k → quad Ric k = κ * quad T k) (hN : A = 4 * Real.pi * G * ρ / c ^ 2) :
    G = κ * c ^ 4 / (8 * Real.pi) := by
  have e := h ![1, 1, 0, 0] ((isNull_vec 1 1 0 0).2 (by norm_num))
  rw [quad_vec, quad_vec, hR, hT] at e
  simp [diagonal] at e
  rw [hN] at e
  have hpi := Real.pi_pos
  field_simp at e ⊢
  linarith

/-- **Newton's constant from the Clausius relation** (Sec. III): with Jacobson's coefficient
`κ = 2πk_B/(ℏcη₀)`, Newton's law in the static weak field gives `G = κc⁴/8π = c³k_B/(4ℏη₀)`
(`newtonian_coefficient`).  No conservation law is used. -/
theorem G_of_clausius {kB ℏ c η₀ A ρ G : ℝ} (hη : η₀ ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hρ : ρ ≠ 0)
    {Ric T : Matrix (Fin 4) (Fin 4) ℝ} (hR : Ric = A • (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (hT : T = Matrix.diagonal ![ρ * c ^ 2, 0, 0, 0])
    (h : ∀ k, IsNull k → quad Ric k = (2 * Real.pi * kB / (ℏ * c * η₀)) * quad T k)
    (hN : A = 4 * Real.pi * G * ρ / c ^ 2) :
    G = c ^ 3 * kB / (4 * ℏ * η₀) := by
  rw [newtonian_coefficient hρ hc hR hT h hN]
  have hpi := Real.pi_pos
  field_simp
  ring

end Register.Einstein
