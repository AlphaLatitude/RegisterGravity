import RegisterGravity.DiffSet
import Mathlib.FieldTheory.Finite.Extension

/-!
# Singer's theorem: a register for every prime-power order (Sec. II, "The count")

**Singer's theorem** [J. Singer, Trans. Amer. Math. Soc. 43, 377 (1938)]: for a finite field `K` of
`q` elements there is a perfect difference set of `q + 1` residues mod `n = q² + q + 1`
(`exists_pds`).  The proof here is Singer's.  Let `E` be the cubic extension of `K`
(`FiniteField.Extension K p 3`, of `q³` elements, a vector space of dimension 3 over `K`), `ω` a
generator of its units, of order `q³ − 1 = (q − 1)n`, and `W` a plane of `E`, a `K`-subspace of
dimension 2.  Then `ω ^ n` lies in `K` (`pow_n_mem`), the nonzero vectors of `E` are the points
`ω ^ k`, `0 ≤ k < n`, times the nonzero elements of `K`, each in one way (`card_nonzero`), and a
subspace of dimension `d` holds `(q^d − 1)/(q − 1)` points (`card_points`).  Let `D` be the `k` for
which `ω ^ k` lies in `W`: `q + 1` of them.  A pair `(d, d')` of `D` with `d − d' = t` is a point of
`W` that `ω ^ t` carries into `W`, a point of `W ∩ ω^{−t}W`.  Two planes of a space of dimension 3
share at least a line, so every nonzero `t` is a difference at least once; and the differences of
distinct elements of `D` number `|D|(|D| − 1) = q² + q = n − 1`, one for each nonzero `t`.  So each
nonzero `t` is a difference exactly once.

With `DiffSet.lean`, a register of `L = 2(q + 1)` whose cells and rings meet the first four
clauses of Postulate 2, with the maps of the clause that no cell differs from another, exists for
every finite field (`homogeneous_register`), so for every prime power `q`
(`homogeneous_register_of_prime_power`).  It is the only file that imports Mathlib's extensions of
finite fields (`Mathlib.FieldTheory.Finite.Extension`).
-/

open Finset Polynomial

namespace Horizon

namespace Singer

variable {K : Type} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- the cubic extension of `K` -/
abbrev Ext (K : Type) [Field K] [Fintype K] (p : ℕ) [Fact p.Prime] [CharP K p] : Type :=
  FiniteField.Extension K p 3

noncomputable instance : Fintype (Ext K p) := Fintype.ofFinite _

noncomputable instance : DecidableEq (Ext K p) := Classical.decEq _

lemma two_le_card : 2 ≤ Fintype.card K := Fintype.one_lt_card

lemma card_ext : Fintype.card (Ext K p) = Fintype.card K ^ 3 := by
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact FiniteField.natCard_extension K p 3

lemma finrank_ext : Module.finrank K (Ext K p) = 3 := FiniteField.finrank_extension K p 3

/-- `q³ − 1 = (q − 1)(q² + q + 1)` -/
lemma cube_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  zify [hq, h3]
  ring

/-- the units of the cubic extension number `q³ − 1` -/
lemma card_units_ext : Fintype.card (Ext K p)ˣ = Fintype.card K ^ 3 - 1 := by
  rw [Fintype.card_units, card_ext]

/-- An element of the extension with `x ^ q = x` comes from `K`. -/
lemma mem_range_of_pow_card (x : Ext K p) (hx : x ^ Fintype.card K = x) :
    ∃ a : K, algebraMap K (Ext K p) a = x := by
  classical
  by_contra hno
  push Not at hno
  set q := Fintype.card K
  have hq := two_le_card (K := K)
  set S : Finset (Ext K p) := univ.image (algebraMap K (Ext K p))
  have hS : S.card = q := by
    rw [card_image_of_injective _ (algebraMap K (Ext K p)).injective, card_univ]
  have hxS : x ∉ S := by
    simp only [S, mem_image, mem_univ, true_and, not_exists]
    exact hno
  set P : (Ext K p)[X] := X ^ q - X
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (Ext K p) (by omega)
  have hdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq (Ext K p) (by omega)
  have hroots : (insert x S).val ⊆ P.roots := by
    intro z hz
    rw [mem_roots hP0]
    simp only [IsRoot, P, eval_sub, eval_pow, eval_X]
    have hz' : z ∈ insert x S := hz
    rw [mem_insert] at hz'
    rcases hz' with rfl | hzS
    · rw [hx, sub_self]
    · simp only [S, mem_image, mem_univ, true_and] at hzS
      obtain ⟨a, rfl⟩ := hzS
      rw [← map_pow, FiniteField.pow_card, sub_self]
  have hle := card_le_degree_of_subset_roots hroots
  rw [card_insert_of_notMem hxS, hS, hdeg] at hle
  omega


/-! ### The Singer cycle -/

variable (K) in
/-- `n = q² + q + 1`, the number of points of the plane of order `q` -/
abbrev nPts : ℕ := Fintype.card K ^ 2 + Fintype.card K + 1

/-- A generator of the units of the cubic extension, of order `q³ − 1 = (q − 1)n`. -/
lemma exists_gen : ∃ ω : (Ext K p)ˣ, (∀ x, x ∈ Subgroup.zpowers ω) ∧
    orderOf ω = (Fintype.card K - 1) * nPts K := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := (Ext K p)ˣ)
  refine ⟨ω, hω, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hω, Nat.card_eq_fintype_card, card_units_ext]
  exact cube_sub_one _ (by have := two_le_card (K := K); omega)

section Gen

variable {ω : (Ext K p)ˣ} (hω : ∀ x, x ∈ Subgroup.zpowers ω)
  (hord : orderOf ω = (Fintype.card K - 1) * nPts K)

include hord in
/-- `ω ^ n` lies in `K`, and is not zero. -/
lemma pow_n_mem : ∃ a : K, a ≠ 0 ∧ algebraMap K (Ext K p) a = (ω : Ext K p) ^ nPts K := by
  set q := Fintype.card K
  have hq := two_le_card (K := K)
  have h1 : ((ω : Ext K p) ^ nPts K) ^ (q - 1) = 1 := by
    rw [← pow_mul, mul_comm, ← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hpow : ((ω : Ext K p) ^ nPts K) ^ q = (ω : Ext K p) ^ nPts K := by
    have : q = (q - 1) + 1 := by omega
    rw [this, pow_succ, h1, one_mul]
  obtain ⟨a, ha⟩ := mem_range_of_pow_card _ hpow
  refine ⟨a, ?_, ha⟩
  rintro rfl
  rw [map_zero] at ha
  exact (pow_ne_zero _ ω.ne_zero) ha.symm

variable (ω) in
/-- the point `k` of the plane: `ω ^ k`, `0 ≤ k < n` -/
noncomputable def pt (k : ZMod (nPts K)) : Ext K p := (ω : Ext K p) ^ k.val

include hord in
/-- `ω ^ m` is the point `m mod n` times a nonzero element of `K`. -/
lemma pow_split (m : ℕ) : ∃ b : K, b ≠ 0 ∧
    (ω : Ext K p) ^ m = b • pt ω (m : ZMod (nPts K)) := by
  obtain ⟨a, ha0, ha⟩ := pow_n_mem hord
  refine ⟨a ^ (m / nPts K), pow_ne_zero _ ha0, ?_⟩
  rw [pt, ZMod.val_natCast, Algebra.smul_def, map_pow, ha, ← pow_mul, ← pow_add,
    Nat.div_add_mod m (nPts K)]

include hord in
/-- `ω ^ m` lies in a `K`-subspace exactly when the point `m mod n` does. -/
lemma pow_mem_iff (V : Submodule K (Ext K p)) (m : ℕ) :
    (ω : Ext K p) ^ m ∈ V ↔ pt ω (m : ZMod (nPts K)) ∈ V := by
  obtain ⟨b, hb0, hb⟩ := pow_split hord m
  rw [hb, Submodule.smul_mem_iff _ hb0]

lemma pt_ne_zero (k : ZMod (nPts K)) : pt ω k ≠ 0 := pow_ne_zero _ ω.ne_zero

include hord in
/-- If the point `k` is the point `k'` times an element of `K`, with `k'` not after `k`, they are
the same point. -/
lemma pt_inj_aux {k k' : ZMod (nPts K)} (hle : k'.val ≤ k.val) {b : K}
    (h : pt ω k = b • pt ω k') : k = k' := by
  set q := Fintype.card K
  have hq := two_le_card (K := K)
  set j := k.val - k'.val with hj
  have hjn : j < nPts K := by
    have := ZMod.val_lt k
    omega
  have hsplit : pt ω k = (ω : Ext K p) ^ j * pt ω k' := by
    rw [pt, pt, ← pow_add]
    congr 1
    omega
  rw [hsplit, Algebra.smul_def] at h
  have hωj : (ω : Ext K p) ^ j = algebraMap K (Ext K p) b :=
    mul_right_cancel₀ (pt_ne_zero k') h
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hωj
    exact pow_ne_zero _ ω.ne_zero hωj
  have hunit : (ω ^ j) ^ (q - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hωj, ← map_pow,
      FiniteField.pow_card_sub_one_eq_one b hb0, map_one, Units.val_one]
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord, mul_comm j] at hunit
  have hdvd : nPts K ∣ j := Nat.dvd_of_mul_dvd_mul_left (by omega) hunit
  have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hjn
  apply ZMod.val_injective
  omega

include hord in
/-- If the point `k` is the point `k'` times an element of `K`, they are the same point. -/
lemma pt_inj {k k' : ZMod (nPts K)} {b : K} (h : pt ω k = b • pt ω k') : k = k' := by
  rcases le_total k'.val k.val with hle | hle
  · exact pt_inj_aux hord hle h
  · have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h
      exact pt_ne_zero k h
    refine (pt_inj_aux hord hle (b := b⁻¹) ?_).symm
    rw [h, smul_smul, inv_mul_cancel₀ hb0, one_smul]

open Classical in
include hω hord in
/-- **Every nonzero vector of a subspace is a point of it times a nonzero element of `K`**, in
exactly one way: the nonzero vectors number `(q − 1)` times the points. -/
lemma card_nonzero (V : Submodule K (Ext K p)) :
    (univ.filter (fun x : Ext K p => x ∈ V ∧ x ≠ 0)).card =
      (univ.filter (fun k : ZMod (nPts K) => pt ω k ∈ V)).card * (Fintype.card K - 1) := by
  classical
  set A := (univ.filter (fun k : ZMod (nPts K) => pt ω k ∈ V)) ×ˢ (univ : Finset Kˣ)
  have hA : A.card =
      (univ.filter (fun k : ZMod (nPts K) => pt ω k ∈ V)).card * (Fintype.card K - 1) := by
    rw [card_product, card_univ, Fintype.card_units]
  rw [← hA]
  symm
  apply Finset.card_nbij (fun pr => ((pr.2 : K)) • pt ω pr.1)
  · intro pr hpr
    have h1 : pt ω pr.1 ∈ V := (Finset.mem_filter.mp (Finset.mem_product.mp hpr).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, V.smul_mem _ h1,
      smul_ne_zero pr.2.ne_zero (pt_ne_zero _)⟩
  · intro pr _ pr' _ h
    simp only at h
    have hk : pr.1 = pr'.1 := by
      apply pt_inj hord (b := ((pr.2 : K))⁻¹ * (pr'.2 : K))
      rw [← smul_smul, ← h, smul_smul, inv_mul_cancel₀ pr.2.ne_zero, one_smul]
    rw [hk] at h
    have ha : (pr.2 : K) = pr'.2 := smul_left_injective K (pt_ne_zero pr'.1) h
    exact Prod.ext hk (Units.ext ha)
  · intro x hx
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨hxV, hx0⟩ := hx'.2
    have hmem : Units.mk0 x hx0 ∈ Submonoid.powers ω :=
      (mem_powers_iff_mem_zpowers).2 (hω _)
    obtain ⟨m, hm⟩ := hmem
    have hxm : x = (ω : Ext K p) ^ m := by
      have := congrArg Units.val hm
      simpa using this.symm
    obtain ⟨b, hb0, hb⟩ := pow_split hord m
    refine ⟨((m : ZMod (nPts K)), Units.mk0 b hb0), ?_, ?_⟩
    · refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩)
      rw [← pow_mem_iff hord, ← hxm]
      exact hxV
    · simp only [Units.val_mk0]
      rw [hxm, hb]

open Classical in
include hω hord in
/-- **The points of a subspace**: `(q − 1)` times their number is `q^{dim} − 1`. -/
lemma card_points (V : Submodule K (Ext K p)) :
    (univ.filter (fun k : ZMod (nPts K) => pt ω k ∈ V)).card * (Fintype.card K - 1) =
      Fintype.card K ^ Module.finrank K V - 1 := by
  classical
  rw [← card_nonzero hω hord V]
  have hV : (univ.filter (fun x : Ext K p => x ∈ V)).card = Fintype.card K ^ Module.finrank K V := by
    rw [← Module.card_eq_pow_finrank (K := K) (V := V)]
    rw [Fintype.card_subtype]
  have herase : univ.filter (fun x : Ext K p => x ∈ V ∧ x ≠ 0) =
      (univ.filter (fun x : Ext K p => x ∈ V)).erase 0 := by
    ext x
    simp [and_comm]
  rw [herase, card_erase_of_mem (by simp [V.zero_mem]), hV]

include hord in
/-- multiplying the point `k` by the point `t` lands in a subspace exactly when the point
`t + k` does -/
lemma mul_pt_mem_iff (V : Submodule K (Ext K p)) (t k : ZMod (nPts K)) :
    pt ω t * pt ω k ∈ V ↔ pt ω (t + k) ∈ V := by
  rw [pt, pt, ← pow_add, pow_mem_iff hord, Nat.cast_add, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

end Gen

variable (K p) in
/-- **A plane of the cubic extension**: a `K`-subspace of dimension 2, the kernel of a coordinate. -/
lemma exists_plane : ∃ W : Submodule K (Ext K p), Module.finrank K W = 2 := by
  let b : Module.Basis (Fin 3) K (Ext K p) := Module.finBasisOfFinrankEq K _ finrank_ext
  refine ⟨LinearMap.ker (b.coord 2), ?_⟩
  have hsurj : Function.Surjective (b.coord 2) := fun a => ⟨a • b 2, by simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker (b.coord 2)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, finrank_ext] at h
  omega

open Classical in
/-- **Singer's theorem**: for a finite field `K` of `q` elements there is a perfect difference set
of `q + 1` residues mod `q² + q + 1`, the exponents `k` for which `ω ^ k` lies in a plane `W` of
the cubic extension, `ω` a generator of its units. -/
theorem exists_pds_aux (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ D : Finset (ZMod (nPts K)), IsPerfectDifferenceSet D ∧ D.card = Fintype.card K + 1 := by
  obtain ⟨ω, hω, hord⟩ := exists_gen (K := K) (p := p)
  obtain ⟨W, hW⟩ := exists_plane K p
  set q := Fintype.card K with hqdef
  have hq := two_le_card (K := K)
  set D := univ.filter (fun k : ZMod (nPts K) => pt ω k ∈ W) with hDdef
  -- the number of points of `W`
  have hcard : D.card = q + 1 := by
    have h := card_points hω hord W
    rw [hW] at h
    have h2 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this, (by omega : 1 ≤ q)]
      ring
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  -- the plane `W` moved by the point `t`
  let u : ZMod (nPts K) → (Ext K p)ˣ := fun t => Units.mk0 (pt ω t) (pt_ne_zero t)
  let Wt : ZMod (nPts K) → Submodule K (Ext K p) := fun t =>
    W.map (((u t)⁻¹.mulLeftLinearEquiv K (Ext K p)) : Ext K p →ₗ[K] Ext K p)
  have hmemWt : ∀ t x, x ∈ Wt t ↔ pt ω t * x ∈ W := by
    intro t x
    show x ∈ W.map (((u t)⁻¹.mulLeftLinearEquiv K (Ext K p)) : Ext K p →ₗ[K] Ext K p) ↔ _
    rw [Submodule.mem_map_equiv, Units.symm_mulLeftLinearEquiv, inv_inv,
      Units.mulLeftLinearEquiv_apply]
    rfl
  have hfinWt : ∀ t, Module.finrank K (Wt t) = 2 := by
    intro t
    show Module.finrank K (W.map (((u t)⁻¹.mulLeftLinearEquiv K (Ext K p)) :
      Ext K p →ₗ[K] Ext K p)) = 2
    rw [LinearEquiv.finrank_map_eq, hW]
  -- the pairs with difference `t` are the points of `W ⊓ Wt t`
  have hcount : ∀ t, ((D ×ˢ D).filter (fun pr => pr.1 - pr.2 = t)).card =
      (univ.filter (fun k : ZMod (nPts K) => pt ω k ∈ W ⊓ Wt t)).card := by
    intro t
    apply Finset.card_nbij (fun pr => pr.2)
    · intro pr hpr
      obtain ⟨hpr1, hpr2⟩ := Finset.mem_filter.mp hpr
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpr1
      have h1' : pt ω pr.1 ∈ W := (Finset.mem_filter.mp h1).2
      have h2' : pt ω pr.2 ∈ W := (Finset.mem_filter.mp h2).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.mem_inf.mpr ⟨h2', ?_⟩⟩
      show pt ω pr.2 ∈ Wt t
      rw [hmemWt, mul_pt_mem_iff hord]
      have : t + pr.2 = pr.1 := by rw [← hpr2]; ring
      rw [this]
      exact h1'
    · intro pr hpr pr' hpr' h
      simp only at h
      have e1 := (Finset.mem_filter.mp hpr).2
      have e2 := (Finset.mem_filter.mp hpr').2
      refine Prod.ext ?_ h
      rw [← sub_add_cancel pr.1 pr.2, ← sub_add_cancel pr'.1 pr'.2, e1, e2, h]
    · intro k hk
      have hk' := (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2
      obtain ⟨hkW, hkWt⟩ := Submodule.mem_inf.mp hk'
      rw [hmemWt, mul_pt_mem_iff hord] at hkWt
      refine ⟨(t + k, k), Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩), rfl⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkWt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkW⟩⟩
      · simp only
        ring
  -- each nonzero difference occurs at least once
  have hge : ∀ t, 1 ≤ ((D ×ˢ D).filter (fun pr => pr.1 - pr.2 = t)).card := by
    intro t
    rw [hcount]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W (Wt t)
    have hle := Submodule.finrank_le (W ⊔ Wt t)
    rw [hW, hfinWt, finrank_ext] at *
    have hdim1 : 1 ≤ Module.finrank K ↥(W ⊓ Wt t) := by omega
    have h := card_points hω hord (W ⊓ Wt t)
    have hpow : Fintype.card K ≤ Fintype.card K ^ Module.finrank K ↥(W ⊓ Wt t) := by
      calc Fintype.card K = Fintype.card K ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) hdim1
    by_contra hcon
    push Not at hcon
    have h0 : (univ.filter (fun k : ZMod (nPts K) => pt ω k ∈ W ⊓ Wt t)).card = 0 := by omega
    rw [h0, zero_mul] at h
    omega
  -- and in all, the nonzero differences occur `|D|(|D| − 1) = n − 1` times
  have hsum : ∑ t ∈ (univ : Finset (ZMod (nPts K))).erase 0,
      ((D ×ˢ D).filter (fun pr => pr.1 - pr.2 = t)).card =
      ∑ t ∈ (univ : Finset (ZMod (nPts K))).erase 0, 1 := by
    have hfib := Finset.card_eq_sum_card_fiberwise (s := D.offDiag)
      (t := (univ : Finset (ZMod (nPts K))).erase 0) (f := fun pr => pr.1 - pr.2)
      (by
        intro pr hpr
        obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hpr
        exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hne, Finset.mem_univ _⟩)
    have hfilt : ∀ t ∈ (univ : Finset (ZMod (nPts K))).erase 0,
        (D.offDiag.filter (fun pr => pr.1 - pr.2 = t)) =
          ((D ×ˢ D).filter (fun pr => pr.1 - pr.2 = t)) := by
      intro t ht
      have ht0 := (Finset.mem_erase.mp ht).1
      ext pr
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
      constructor
      · rintro ⟨⟨h1, h2, -⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2, ?_⟩, h3⟩
        intro heq
        rw [heq, sub_self] at h3
        exact ht0 h3.symm
    rw [Finset.sum_congr rfl (fun t ht => by rw [← hfilt t ht]), ← hfib, Finset.offDiag_card,
      hcard, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
    have h1 : (q + 1) * (q + 1) - (q + 1) = q ^ 2 + q := by
      have : q + 1 ≤ (q + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
      zify [this]
      ring
    rw [h1]
    show q ^ 2 + q = q ^ 2 + q + 1 - 1
    omega
  refine ⟨D, ?_, hcard⟩
  intro t ht
  have := (Finset.sum_eq_sum_iff_of_le (fun t _ => hge t)).mp hsum.symm
  exact (this t (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ _⟩)).symm

variable (K) in
/-- **Singer's theorem**: for a finite field `K` of `q` elements there is a perfect difference set
of `q + 1` residues mod `q² + q + 1`. -/
theorem exists_pds :
    ∃ D : Finset (ZMod (nPts K)), IsPerfectDifferenceSet D ∧ D.card = Fintype.card K + 1 := by
  have : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  exact exists_pds_aux (ringChar K)

/-- **A register for every finite field**: with `q = |K|`, a register of `L = 2(q + 1)`, with a
cyclic order on each ring, whose cells and rings meet the first four clauses of Postulate 2, with
the maps of the clause that no cell differs from another; its order as a projective plane is
`q`. -/
theorem homogeneous_register (K : Type) [Field K] [Fintype K] :
    ∃ H : Horizon (2 * (Fintype.card K + 1)), Nonempty H.Positions ∧ H.Homogeneous ∧
      ∀ hL : 6 ≤ 2 * (Fintype.card K + 1), H.order hL = Fintype.card K := by
  obtain ⟨D, hD, hcard⟩ := exists_pds K
  have h3 : 3 ≤ D.card := by
    rw [hcard]
    have := two_le_card (K := K)
    omega
  obtain ⟨H, hP, hhom, hord⟩ := register_of_diffSet hD h3
  rw [← hcard]
  refine ⟨H, hP, hhom, fun hL => ?_⟩
  rw [hord hL, hcard]
  rfl

/-- **A register for every prime power**: for every prime `p` and `n ≥ 1` there is a register of
`L = 2(pⁿ + 1)`, with a cyclic order on each ring, whose cells and rings meet the first four
clauses of Postulate 2, with the maps of the clause that no cell differs from another; its order as
a projective plane is `pⁿ`. -/
theorem homogeneous_register_of_prime_power (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    ∃ H : Horizon (2 * (p ^ n + 1)), Nonempty H.Positions ∧ H.Homogeneous ∧
      ∀ hL : 6 ≤ 2 * (p ^ n + 1), H.order hL = p ^ n := by
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n hn
  have key := homogeneous_register (GaloisField p n)
  rw [hq] at key
  exact key

end Singer

end Horizon
