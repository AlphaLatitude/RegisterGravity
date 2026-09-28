import RegisterGravity.Horizon
import Mathlib.Combinatorics.Configuration

/-!
# The register is a finite projective plane of order `L/2 − 1`

Sec. II of the paper: "With a cell and its opposite taken as a point and a largest ring as a line,
the register is a finite projective plane of order `L/2 − 1`, with `R` points and `R` lines."

Points are the opposite pairs, `Horizon.Pt`, a quotient of the cells; lines are the largest rings.
We build the `Configuration.ProjectivePlane` instance of Mathlib from the fields of `Horizon` (this
needs `6 ≤ L`, three opposite pairs on a ring, for Mathlib's non-degeneracy condition) and read off
the order from the number of rings through a point, `ρ = L/2 = order + 1`.  Mathlib's counting
theorems then return `R = order² + order + 1` for both points and lines, which agrees with the
direct count of `Horizon.counts`.

Which orders a finite projective plane can have is the question the paper cites Bruck and Ryser
for: their theorem excludes orders `1` or `2` modulo `4` that are not sums of two squares.  It is a
citation, and no derivation uses it.
-/

open Finset Configuration

namespace Horizon

variable {L : ℕ} (H : Horizon L)

/-- Cells modulo "opposite". -/
def pairSetoid : Setoid H.Cell where
  r x y := y = x ∨ y = H.opp x
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        intro x y h
        rcases h with h | h
        · exact Or.inl h.symm
        · right; rw [h, H.opp_opp]
      trans := by
        intro x y z hxy hyz
        rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
        · exact Or.inl (hyz.trans hxy)
        · right; rw [hyz, hxy]
        · right; rw [hyz, hxy]
        · left; rw [hyz, hxy, H.opp_opp] }

/-- The points of the horizon: opposite pairs of cells. -/
abbrev Pt : Type := Quotient H.pairSetoid

/-- The point of a cell. -/
def pt (x : H.Cell) : H.Pt := Quotient.mk H.pairSetoid x

lemma pt_eq_pt_iff {x y : H.Cell} : H.pt x = H.pt y ↔ y = x ∨ y = H.opp x :=
  Quotient.eq

lemma pt_surjective : Function.Surjective H.pt := Quotient.mk_surjective

noncomputable instance : Fintype H.Pt := by
  classical
  exact Quotient.fintype H.pairSetoid

/-- A point lies on a ring when its cells do (well defined by `opp_mem`). -/
instance : Membership H.Pt H.Loop :=
  ⟨fun l p => Quotient.liftOn p (fun x => x ∈ H.cells l) (by
    intro x y hxy
    rcases hxy with h | h
    · rw [h]
    · rw [h]; exact propext (H.opp_mem_iff l x).symm)⟩

lemma pt_mem_iff (x : H.Cell) (l : H.Loop) : H.pt x ∈ l ↔ x ∈ H.cells l := Iff.rfl

lemma exists_line_of_ne {p q : H.Pt} (h : p ≠ q) : ∃ l : H.Loop, p ∈ l ∧ q ∈ l := by
  revert h
  refine Quotient.inductionOn₂ p q ?_
  intro x y h
  have h' : ¬ (y = x ∨ y = H.opp x) := fun hxy => h (Quotient.sound hxy)
  push Not at h'
  obtain ⟨l, hx, hy⟩ := H.exists_loop x y h'.1 h'.2
  exact ⟨l, (H.pt_mem_iff x l).2 hx, (H.pt_mem_iff y l).2 hy⟩

/-- The non-degeneracy conditions of Mathlib's configurations. -/
theorem nondegenerate (hL : 4 ≤ L) : Configuration.Nondegenerate H.Pt H.Loop := by
  refine { exists_point := ?_, exists_line := ?_, eq_or_eq := ?_ }
  · intro l
    obtain ⟨x, hx⟩ := H.exists_cell_not_mem hL l
    exact ⟨H.pt x, fun h => hx ((H.pt_mem_iff x l).1 h)⟩
  · intro p
    refine Quotient.inductionOn p ?_
    intro x
    obtain ⟨E, hE⟩ := H.exists_loop_not_mem hL x
    exact ⟨E, fun h => hE ((H.pt_mem_iff x E).1 h)⟩
  · intro p₁ p₂ l₁ l₂
    refine Quotient.inductionOn₂ p₁ p₂ ?_
    intro x y h₁ h₂ h₃ h₄
    by_cases hxy : y = x ∨ y = H.opp x
    · exact Or.inl (Quotient.sound hxy)
    · push Not at hxy
      exact Or.inr (H.unique_loop x y l₁ l₂ hxy.1 hxy.2 ((H.pt_mem_iff x l₁).1 h₁)
        ((H.pt_mem_iff y l₁).1 h₂) ((H.pt_mem_iff x l₂).1 h₃) ((H.pt_mem_iff y l₂).1 h₄))

/-- Mathlib's `ProjectivePlane` structure on the horizon (needs `6 ≤ L`). -/
@[instance_reducible]
noncomputable def projectivePlane (hL : 6 ≤ L) : Configuration.ProjectivePlane H.Pt H.Loop :=
  have hL4 : 4 ≤ L := by omega
  { H.nondegenerate hL4 with
    mkPoint := fun {l₁ l₂} _ => H.pt (Classical.choose (H.loops_meet l₁ l₂))
    mkPoint_ax := fun {l₁ l₂} _ =>
      ⟨(H.pt_mem_iff _ l₁).2 (Classical.choose_spec (H.loops_meet l₁ l₂)).1,
       (H.pt_mem_iff _ l₂).2 (Classical.choose_spec (H.loops_meet l₁ l₂)).2⟩
    mkLine := fun {p₁ p₂} h => Classical.choose (H.exists_line_of_ne h)
    mkLine_ax := fun {p₁ p₂} h => Classical.choose_spec (H.exists_line_of_ne h)
    exists_config := by
      -- a ring `l₁`, a cell `q` off it, three cells `a b c` of `l₁` in distinct pairs
      obtain ⟨l₁, -, -⟩ := H.two_loops
      obtain ⟨q, hq⟩ := H.exists_cell_not_mem hL4 l₁
      have hq' : H.opp q ∉ H.cells l₁ := fun h => hq ((H.opp_mem_iff l₁ q).1 h)
      obtain ⟨a, ha, -, -⟩ := H.exists_mem_notMem_pair hL4 l₁ q q
      obtain ⟨b, hb, hba, hba'⟩ := H.exists_mem_notMem_pair hL4 l₁ a (H.opp a)
      have hlt : ({a, H.opp a, b, H.opp b} : Finset H.Cell).card < (H.cells l₁).card := by
        rw [H.card_cells]; exact lt_of_le_of_lt card_le_four (by omega)
      obtain ⟨c, hc, hc'⟩ := exists_mem_notMem_of_card_lt_card hlt
      simp only [mem_insert, mem_singleton, not_or] at hc'
      obtain ⟨hca, hca', hcb, hcb'⟩ := hc'
      -- lines through `q` and `a`, and through `q` and `b`
      have haq : a ≠ q := fun h => hq (h ▸ ha)
      have haq' : a ≠ H.opp q := fun h => hq' (h ▸ ha)
      have hbq : b ≠ q := fun h => hq (h ▸ hb)
      have hbq' : b ≠ H.opp q := fun h => hq' (h ▸ hb)
      obtain ⟨l₂, hql₂, hal₂⟩ := H.exists_loop q a haq haq'
      obtain ⟨l₃, hql₃, hbl₃⟩ := H.exists_loop q b hbq hbq'
      -- a cell `s` of `l₂` outside the pairs of `q` and `a`
      have hlt₂ : ({q, H.opp q, a, H.opp a} : Finset H.Cell).card < (H.cells l₂).card := by
        rw [H.card_cells]; exact lt_of_le_of_lt card_le_four (by omega)
      obtain ⟨s, hs, hs'⟩ := exists_mem_notMem_of_card_lt_card hlt₂
      simp only [mem_insert, mem_singleton, not_or] at hs'
      obtain ⟨hsq, hsq', hsa, hsa'⟩ := hs'
      -- the two lines through `q` differ from `l₁`
      have hl₂₁ : l₂ ≠ l₁ := fun h => hq (h ▸ hql₂)
      have hl₃₁ : l₃ ≠ l₁ := fun h => hq (h ▸ hql₃)
      refine ⟨H.pt c, H.pt q, H.pt s, l₁, l₂, l₃, ?_, ?_,
        fun h => hq ((H.pt_mem_iff q l₁).1 h), (H.pt_mem_iff q l₂).2 hql₂,
        (H.pt_mem_iff q l₃).2 hql₃, ?_, (H.pt_mem_iff s l₂).2 hs, ?_⟩
      · -- `c ∉ l₂`: else `l₁` and `l₂` share `a` and `c`
        intro hcl₂
        rw [pt_mem_iff] at hcl₂
        exact hl₂₁ (H.unique_loop a c l₂ l₁ hca hca' hal₂ hcl₂ ha hc)
      · -- `c ∉ l₃`: else `l₁` and `l₃` share `b` and `c`
        intro hcl₃
        rw [pt_mem_iff] at hcl₃
        exact hl₃₁ (H.unique_loop b c l₃ l₁ hcb hcb' hbl₃ hcl₃ hb hc)
      · -- `s ∉ l₁`: else `l₁` and `l₂` share `a` and `s`
        intro hsl₁
        rw [pt_mem_iff] at hsl₁
        exact hl₂₁ (H.unique_loop a s l₂ l₁ hsa hsa' hal₂ hs ha hsl₁)
      · -- `s ∉ l₃`: else `l₂ = l₃`, and then `l₃ ∋ a, b` forces `l₃ = l₁`
        intro hsl₃
        rw [pt_mem_iff] at hsl₃
        have h23 : l₂ = l₃ := H.unique_loop q s l₂ l₃ hsq hsq' hql₂ hs hql₃ hsl₃
        have hal₃ : a ∈ H.cells l₃ := h23 ▸ hal₂
        exact hl₃₁ (H.unique_loop a b l₃ l₁ hba hba' hal₃ hbl₃ ha hb) }

/-- The order of the horizon as a projective plane. -/
noncomputable def order (hL : 6 ≤ L) : ℕ :=
  @ProjectivePlane.order H.Pt H.Loop _ (H.projectivePlane hL)

/-- The number of rings through a point is the number of rings through either of its cells. -/
lemma lineCount_pt (x : H.Cell) : lineCount H.Loop (H.pt x) = (H.through x).card := by
  classical
  rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext l
  simp [through, pt_mem_iff]

/-- **The order.**  With `q = order`, `2(q + 1) = L`, that is, `q = L/2 − 1`. -/
theorem two_mul_order_add_one (hL : 6 ≤ L) : 2 * (H.order hL + 1) = L := by
  let _ : ProjectivePlane H.Pt H.Loop := H.projectivePlane hL
  obtain ⟨P⟩ := H.exists_cell (by omega)
  unfold order
  rw [← ProjectivePlane.lineCount_eq H.Loop (H.pt P), lineCount_pt]
  exact H.two_mul_card_through (by omega) P

/-- **R points and R lines.**  The number of largest rings is `q² + q + 1` with `q = L/2 − 1`,
and there are as many points (opposite pairs) as rings. -/
theorem card_loop_eq_order (hL : 6 ≤ L) :
    Fintype.card H.Loop = H.order hL ^ 2 + H.order hL + 1 ∧
    Fintype.card H.Pt = Fintype.card H.Loop := by
  let _ : ProjectivePlane H.Pt H.Loop := H.projectivePlane hL
  exact ⟨ProjectivePlane.card_lines H.Pt H.Loop,
    ProjectivePlane.card_points_eq_card_lines H.Pt H.Loop⟩

/-- Cross-check: Mathlib's `q² + q + 1` and the direct count `4R = L² − 2L + 4` of
`Horizon.counts` agree. -/
theorem order_count_consistent (hL : 6 ≤ L) :
    4 * (H.order hL ^ 2 + H.order hL + 1) + 2 * L = L ^ 2 + 4 := by
  have h := H.two_mul_order_add_one hL
  set q := H.order hL
  zify at h ⊢
  linear_combination (2 * (q : ℤ) + (L : ℤ)) * h

end Horizon
