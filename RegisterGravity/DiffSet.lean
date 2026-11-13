import RegisterGravity.Homogeneous
import RegisterGravity.Projective

/-!
# A register from a perfect difference set (Sec. II, "The count")

A **perfect difference set** mod `n` is a set `D` of residues such that every nonzero residue is
the difference `d − d'` of exactly one ordered pair of its elements.  With `|D| = k`, it is the
Singer form of a projective plane of order `k − 1`: the points are the residues mod `n`, and the
lines are the translates `D + l`.  Doubling each point into a cell and its opposite gives a
register of `L = 2k` (`ofDiffSet`): a cell is (point, side), its opposite flips the side, and the
ring `l` holds both sides of the points `d + l`, `d ∈ D`, running through them in the order of `D`
on one side and back through them on the other (`ofDiffSetPositions`), so that the opposite of a
cell lies `k` steps, half the ring, on.  That its cells and rings meet the first four clauses of
Postulate 2 follows from the difference property.

**The register has the maps of the clause of Postulate 2 that no cell differs from another**
(`ofDiffSet_homogeneous`): the translation `p ↦ p + t`, which carries the ring `l` to the ring
`l + t`, and the swap of sides are symmetries (`dsSym`), and together they carry any cell to any
other.  `register_of_diffSet` states
the result, with the register's order as a projective plane (`Projective.lean`), `k − 1`.  `Singer.lean`
supplies a perfect difference set of `q + 1` residues mod `q² + q + 1` for every prime power `q`.
-/

open Finset

namespace Horizon

/-- flipping the side of every cell, or not -/
def xorEquiv (f : Bool) : Bool ≃ Bool where
  toFun b := xor b f
  invFun b := xor b f
  left_inv b := by cases b <;> cases f <;> rfl
  right_inv b := by cases b <;> cases f <;> rfl

/-- **A perfect difference set** mod `n`: every nonzero residue is the difference of exactly one
ordered pair of its elements. -/
def IsPerfectDifferenceSet {n : ℕ} (D : Finset (ZMod n)) : Prop :=
  ∀ t : ZMod n, t ≠ 0 → ((D ×ˢ D).filter (fun pr => pr.1 - pr.2 = t)).card = 1

/-- In a perfect difference set, each nonzero residue is the difference of one ordered pair. -/
lemma IsPerfectDifferenceSet.existsUnique {n : ℕ} {D : Finset (ZMod n)}
    (hD : IsPerfectDifferenceSet D) {t : ZMod n} (ht : t ≠ 0) :
    ∃! pr : ZMod n × ZMod n, pr.1 ∈ D ∧ pr.2 ∈ D ∧ pr.1 - pr.2 = t := by
  obtain ⟨pr, hpr⟩ := Finset.card_eq_one.mp (hD t ht)
  have hmem : ∀ x, x ∈ (D ×ˢ D).filter (fun pr => pr.1 - pr.2 = t) ↔ x = pr := by
    intro x
    rw [hpr, Finset.mem_singleton]
  refine ⟨pr, ?_, ?_⟩
  · have := (hmem pr).2 rfl
    simp only [mem_filter, mem_product] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · intro y hy
    apply (hmem y).1
    simp only [mem_filter, mem_product]
    exact ⟨⟨hy.1, hy.2.1⟩, hy.2.2⟩

section DiffSet

variable {n : ℕ} [NeZero n] (D : Finset (ZMod n))

/-- the cells of the ring `l`: the points `d + l`, `d ∈ D`, each on both sides -/
def dsCells (l : ZMod n) : Finset (ZMod n × Bool) :=
  (D.map (Equiv.addRight l).toEmbedding) ×ˢ univ

omit [NeZero n] in
lemma mem_dsCells {l : ZMod n} {x : ZMod n × Bool} : x ∈ dsCells D l ↔ x.1 - l ∈ D := by
  simp only [dsCells, mem_product, mem_univ, and_true, Finset.mem_map_equiv,
    Equiv.addRight_symm, Equiv.coe_addRight, ← sub_eq_add_neg]

omit [NeZero n] in
lemma fst_ne_of_ne {x y : ZMod n × Bool} (h1 : y ≠ x) (h2 : y ≠ (x.1, !x.2)) : x.1 ≠ y.1 := by
  intro h
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at h
  subst h
  cases b <;> cases d <;> simp_all

variable {D}

/-- **The register of a perfect difference set**: cells are (point, side), the opposite flips the
side, and the ring `l` holds both sides of the points `d + l`, `d ∈ D`. -/
def ofDiffSet (hD : IsPerfectDifferenceSet D) (h3 : 3 ≤ D.card) : Horizon (2 * D.card) where
  Cell := ZMod n × Bool
  Loop := ZMod n
  opp x := (x.1, !x.2)
  cells l := dsCells D l
  opp_opp := by intro x; simp
  opp_ne := by
    intro x h
    have := congrArg Prod.snd h
    simp at this
  card_cells := by
    intro l
    rw [dsCells, card_product, card_map, card_univ, Fintype.card_bool]
    ring
  opp_mem := by
    intro l x hx
    rw [mem_dsCells] at hx ⊢
    exact hx
  exists_loop := by
    intro x y h1 h2
    have hne := fst_ne_of_ne h1 h2
    obtain ⟨⟨d, d'⟩, ⟨hd, hd', hdd⟩, -⟩ := hD.existsUnique (sub_ne_zero.mpr hne)
    refine ⟨x.1 - d, ?_, ?_⟩
    · rw [mem_dsCells, sub_sub_cancel]
      exact hd
    · rw [mem_dsCells]
      have : y.1 - (x.1 - d) = d' := by
        simp only at hdd
        linear_combination hdd
      rw [this]
      exact hd'
  unique_loop := by
    intro x y l₁ l₂ h1 h2 hx1 hy1 hx2 hy2
    have hne := fst_ne_of_ne h1 h2
    rw [mem_dsCells] at hx1 hy1 hx2 hy2
    obtain ⟨pr, -, huniq⟩ := hD.existsUnique (sub_ne_zero.mpr hne)
    have e1 := huniq (x.1 - l₁, y.1 - l₁) ⟨hx1, hy1, by simp⟩
    have e2 := huniq (x.1 - l₂, y.1 - l₂) ⟨hx2, hy2, by simp⟩
    have := congrArg Prod.fst (e1.trans e2.symm)
    simpa using this
  loops_meet := by
    intro l₁ l₂
    by_cases h : l₁ = l₂
    · subst h
      obtain ⟨d, hd⟩ := card_pos.mp (by omega : 0 < D.card)
      refine ⟨(d + l₁, false), ?_, ?_⟩ <;> rw [mem_dsCells, add_sub_cancel_right] <;> exact hd
    · obtain ⟨⟨d, d'⟩, ⟨hd, hd', hdd⟩, -⟩ := hD.existsUnique (sub_ne_zero.mpr (Ne.symm h))
      refine ⟨(d + l₁, false), ?_, ?_⟩
      · rw [mem_dsCells, add_sub_cancel_right]
        exact hd
      · rw [mem_dsCells]
        have : d + l₁ - l₂ = d' := by
          simp only at hdd
          linear_combination hdd
        rw [this]
        exact hd'
  misses := by
    intro l
    have hn : 3 ≤ n := by
      have := card_le_univ D
      rw [ZMod.card] at this
      omega
    have : Fact (1 < n) := ⟨by omega⟩
    -- a residue off `D`: were every residue in `D`, the residue `1` would be `1 − 0` and `2 − 1`
    obtain ⟨r, hr⟩ : ∃ r : ZMod n, r ∉ D := by
      by_contra hall
      push Not at hall
      obtain ⟨pr, -, huniq⟩ := hD.existsUnique (one_ne_zero : (1 : ZMod n) ≠ 0)
      have e1 := huniq (1, 0) ⟨hall 1, hall 0, by simp⟩
      have e2 := huniq (2, 1) ⟨hall 2, hall 1, by norm_num⟩
      have := congrArg Prod.snd (e1.trans e2.symm)
      exact zero_ne_one this
    refine ⟨(r + l, false), ?_⟩
    rw [mem_dsCells, add_sub_cancel_right]
    exact hr
  exists_ring := ⟨0⟩

variable (D) in
open Classical in
/-- the place of a point of `D`, `0, …, |D| − 1` -/
noncomputable def dsIdx (x : ZMod n) : ℕ :=
  if h : x ∈ D then (D.equivFin ⟨x, h⟩ : ℕ) else 0

omit [NeZero n] in
lemma dsIdx_lt (hD0 : 0 < D.card) (x : ZMod n) : dsIdx D x < D.card := by
  classical
  unfold dsIdx
  split_ifs with h
  · exact Fin.isLt _
  · exact hD0

omit [NeZero n] in
lemma dsIdx_inj {x y : ZMod n} (hx : x ∈ D) (hy : y ∈ D) (h : dsIdx D x = dsIdx D y) : x = y := by
  classical
  simp only [dsIdx, hx, hy, dite_true] at h
  have := D.equivFin.injective (Fin.ext h)
  exact congrArg Subtype.val this


variable (D) in
/-- the position of the cell `x` on the ring `l`: the place of `x.1 − l` in `D`, plus `|D|` on the
other side -/
noncomputable def dsPos (l : ZMod n) (x : ZMod n × Bool) : ZMod (2 * D.card) :=
  ((dsIdx D (x.1 - l) + if x.2 then D.card else 0 : ℕ) : ZMod (2 * D.card))

omit [NeZero n] in
lemma dsPos_inj (h0 : 0 < D.card) (l : ZMod n) (x y : ZMod n × Bool) (hx : x ∈ dsCells D l)
    (hy : y ∈ dsCells D l) (hxy : dsPos D l x = dsPos D l y) : x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  have ha : a - l ∈ D := (mem_dsCells D).1 hx
  have hc : c - l ∈ D := (mem_dsCells D).1 hy
  have h1 := dsIdx_lt h0 (a - l)
  have h2 := dsIdx_lt h0 (c - l)
  unfold dsPos at hxy
  simp only at hxy
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by split_ifs <;> omega),
    Nat.mod_eq_of_lt (by split_ifs <;> omega)] at hxy
  have hbd : b = d := by
    cases b <;> cases d <;> simp at hxy <;> first | rfl | omega
  subst hbd
  have hi : dsIdx D (a - l) = dsIdx D (c - l) := by
    cases b <;> (simp at hxy; omega)
  have := dsIdx_inj ha hc hi
  rw [sub_left_inj] at this
  rw [this]

/-- the side term of a position, `|D|` on one side and `0` on the other -/
lemma side_xor (k : ℕ) (b f : Bool) :
    (if xor b f = true then ((k : ℕ) : ZMod (2 * k)) else 0) =
      (if b = true then ((k : ℕ) : ZMod (2 * k)) else 0) +
        (if f = true then ((k : ℕ) : ZMod (2 * k)) else 0) := by
  have h0 : ((2 * k : ℕ) : ZMod (2 * k)) = 0 := ZMod.natCast_self _
  push_cast at h0
  cases b <;> cases f
  · simp
  · simp
  · simp
  · simp only [Bool.xor_self, Bool.false_eq_true, ite_false, ite_true]
    linear_combination -h0

omit [NeZero n] in
lemma dsPos_flip (l : ZMod n) (x : ZMod n × Bool) :
    dsPos D l (x.1, !x.2) = dsPos D l x + (((2 * D.card) / 2 : ℕ) : ZMod (2 * D.card)) := by
  have hhalf : (2 * D.card) / 2 = D.card := by omega
  rw [hhalf]
  unfold dsPos
  push_cast
  have h := side_xor D.card x.2 true
  simp only [Bool.xor_true, ite_true] at h
  rw [h]
  ring

omit [NeZero n] in
lemma dsCells_shift (l t : ZMod n) (f : Bool) (x : ZMod n × Bool) :
    x ∈ dsCells D l ↔ (x.1 + t, xor x.2 f) ∈ dsCells D (l + t) := by
  rw [mem_dsCells, mem_dsCells, add_sub_add_right_eq_sub]

variable (hD : IsPerfectDifferenceSet D) (h3 : 3 ≤ D.card)

/-- **Positions on it**: the ring `l` runs through the points `d + l`, `d ∈ D`, on one side, at
`0, …, |D| − 1` in the order of `D`, and back through them on the other, at `|D|, …, 2|D| − 1`. -/
noncomputable def ofDiffSetPositions : (ofDiffSet hD h3).Positions where
  pos l x := dsPos D l x
  pos_inj l x y hx hy hxy := dsPos_inj (by omega) l x y hx hy hxy
  pos_opp l x _ := dsPos_flip l x

/-- **The translations, with or without the swap of sides, are symmetries**: `p ↦ p + t` on the
points, `l ↦ l + t` on the rings, and every side flipped or not. -/
noncomputable def dsSym (t : ZMod n) (f : Bool) : (ofDiffSet hD h3).Symmetry where
  cellMap := ((Equiv.addRight t).prodCongr (xorEquiv f) : ZMod n × Bool ≃ ZMod n × Bool)
  loopMap := (Equiv.addRight t : ZMod n ≃ ZMod n)
  mem_iff l x := dsCells_shift l t f x

/-- **The register of a perfect difference set has the maps of the clause of Postulate 2 that no
cell differs from another**: the translations and the swap of sides carry any cell to any other. -/
theorem ofDiffSet_homogeneous : (ofDiffSet hD h3).Homogeneous := by
  intro x y
  refine ⟨dsSym hD h3 (y.1 - x.1) (xor x.2 y.2), ?_⟩
  show (x.1 + (y.1 - x.1), xor x.2 (xor x.2 y.2)) = y
  refine Prod.ext ?_ ?_
  · show x.1 + (y.1 - x.1) = y.1
    abel
  · show xor x.2 (xor x.2 y.2) = y.2
    cases x.2 <;> cases y.2 <;> rfl

include hD h3 in
/-- **A perfect difference set of `k ≥ 3` residues gives a register of `L = 2k`**, with a cyclic
order on each ring, whose cells and rings meet the first four clauses of Postulate 2, with the
maps of the clause that no cell differs from another; the register's order as a projective plane
is `k − 1`. -/
theorem register_of_diffSet :
    ∃ H : Horizon (2 * D.card), Nonempty H.Positions ∧ H.Homogeneous ∧
      ∀ hL : 6 ≤ 2 * D.card, H.order hL = D.card - 1 := by
  refine ⟨ofDiffSet hD h3, ⟨ofDiffSetPositions hD h3⟩, ofDiffSet_homogeneous hD h3, fun hL => ?_⟩
  have h := (ofDiffSet hD h3).two_mul_order_add_one hL
  omega

end DiffSet

end Horizon

