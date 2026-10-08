import RegisterGravity.Projective
import RegisterGravity.RouteB

/-!
# The axioms of `Horizon` and `Positions` have a model

A theorem proved from contradictory axioms would hold vacuously, so the axioms of `Horizon L` need
a model.  The smallest is `L = 6`: the Fano plane, the projective plane of order `2 = L/2 − 1`,
with each point doubled into a cell and its opposite; it is an incidence structure, not a drawing,
and like every finite projective plane of order at least 2 it has no drawing with straight lines or
great circles (`Horizon.lean`).  Every axiom is checked by `decide`, and the
counts of `Horizon.counts` come out as `14 = L²/2 − L + 2` cells and `7 = L²/4 − L/2 + 1` rings.
The cyclic order of `RouteB.lean` has a model on it too: each ring runs through its three points
on one side and back through them on the other, so that the opposite of a cell lies three steps,
half the ring, on.

The same doubling works for every finite projective plane (Sec. II: "every plane of order `k`
gives a register of `L = 2(k + 1)`, each point doubled into a cell and its opposite"), each line
becoming a ring through its points on one side and back through them on the other, which the paper
leaves to these files: `Horizon.double` and `Horizon.doublePositions`
build the register of `L = 2(q + 1)` and its cyclic order from a plane of order `q`, Mathlib's
`Configuration.ProjectivePlane`, and `register_of_plane` states the result, the register's own
order being `q` again.  `Planes.lean`
supplies a plane of every prime-power order.
-/

open Finset

namespace Horizon

/-- The seven lines of the Fano plane on the points `0, …, 6`. -/
def fanoLines : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

/-- **A horizon with `L = 6`**: cells are (point, side), the opposite flips the side, and a largest
ring is a Fano line with both sides of each of its three points. -/
def fano : Horizon 6 where
  Cell := Fin 7 × Bool
  Loop := Fin 7
  opp x := (x.1, !x.2)
  cells l := fanoLines l ×ˢ univ
  opp_opp := by decide
  opp_ne := by decide
  card_cells := by decide
  opp_mem := by decide
  exists_loop := by decide
  unique_loop := by decide
  loops_meet := by decide
  two_loops := by decide

/-- The counts of Eq. (counts) for the model: `14` cells, `7` rings, `ρ = 3` rings per cell. -/
theorem fano_counts :
    Fintype.card fano.Cell = 14 ∧ Fintype.card fano.Loop = 7 ∧
    2 * Fintype.card fano.Cell + 2 * 6 = 6 ^ 2 + 4 ∧
    4 * Fintype.card fano.Loop + 2 * 6 = 6 ^ 2 + 4 := by
  have h := fano.counts (by norm_num)
  refine ⟨by decide, by decide, h.2.1, h.2.2.1⟩

/-- The three points of each Fano line, in order. -/
def fanoList : Fin 7 → Fin 3 → Fin 7 :=
  ![![0, 1, 2], ![0, 3, 4], ![0, 5, 6], ![1, 3, 5], ![1, 4, 6], ![2, 3, 6], ![2, 4, 5]]

/-- the place of a point on a Fano line, `0`, `1` or `2` -/
def fanoIdx (l p : Fin 7) : ZMod 6 :=
  if fanoList l 0 = p then 0 else if fanoList l 1 = p then 1 else 2

/-- **Positions on the Fano horizon**: a ring runs through the three points of its line on one
side, at the positions `0, 1, 2`, and back through them on the other, at `3, 4, 5`; the opposite of
a cell lies three steps, half the ring, on. -/
def fanoPositions : fano.Positions where
  pos l x := fanoIdx l x.1 + (if x.2 then 3 else 0)
  pos_inj := by decide
  pos_opp := by decide

/-- The model is a projective plane of order `2 = L/2 − 1`. -/
theorem fano_order : fano.order (by norm_num) = 2 := by
  have h := fano.two_mul_order_add_one (by norm_num)
  omega

/-- In the model, `L = 6` is even because the opposite lies halfway around
(`Positions.even_of_halfway`). -/
theorem fano_even : Even 6 := by
  have hx : (((0 : Fin 7), false) : fano.Cell) ∈ fano.cells (0 : Fin 7) := by
    show ((0 : Fin 7), false) ∈ fanoLines 0 ×ˢ (univ : Finset Bool)
    decide
  exact fanoPositions.even_of_halfway (by norm_num) _ _ hx

/-! ## Every finite projective plane gives a register

The converse of `Projective.lean`.  A finite projective plane of order `q` (Mathlib's
`Configuration.ProjectivePlane`, whose order is at least `2`) gives a register of
`L = 2(q + 1)`: each point is split into a cell and its opposite, and each line becomes a largest
ring that runs through its `q + 1` points on one side and back through them on the other, so that
the opposite of a cell lies `q + 1` steps, half the ring, on.  The Fano model above is `q = 2`. -/

section Doubling

open Configuration

variable (P Ln : Type) [Membership P Ln] [Fintype P] [Fintype Ln] [ProjectivePlane P Ln]

open Classical in
/-- The points of a line. -/
noncomputable def pts (l : Ln) : Finset P := univ.filter (fun p => p ∈ l)

omit [Fintype Ln] [ProjectivePlane P Ln] in
lemma mem_pts {l : Ln} {p : P} : p ∈ pts P Ln l ↔ p ∈ l := by
  classical
  simp [pts]

lemma card_pts (l : Ln) : (pts P Ln l).card = ProjectivePlane.order P Ln + 1 := by
  classical
  rw [← ProjectivePlane.pointCount_eq P l, pointCount, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rfl

open Classical in
/-- **The doubled plane.**  Cells are (point, side); the opposite flips the side; the largest ring
of a line holds both sides of each of its points. -/
noncomputable def double : Horizon (2 * (ProjectivePlane.order P Ln + 1)) where
  Cell := P × Bool
  Loop := Ln
  opp x := (x.1, !x.2)
  cells l := pts P Ln l ×ˢ univ
  opp_opp := by intro x; simp
  opp_ne := by
    intro x h
    have := congrArg Prod.snd h
    simp at this
  card_cells := by
    intro l
    rw [card_product, card_pts, card_univ, Fintype.card_bool]
    ring
  opp_mem := by
    intro l x hx
    simp only [mem_product, mem_univ, and_true] at hx ⊢
    exact hx
  exists_loop := by
    intro x y h1 h2
    have hne : x.1 ≠ y.1 := by
      intro h
      obtain ⟨a, b⟩ := x
      obtain ⟨c, d⟩ := y
      simp only at h
      subst h
      cases b <;> cases d <;> simp_all
    refine ⟨HasLines.mkLine hne, ?_, ?_⟩
    · simp only [mem_product, mem_univ, and_true, mem_pts]
      exact (HasLines.mkLine_ax hne).1
    · simp only [mem_product, mem_univ, and_true, mem_pts]
      exact (HasLines.mkLine_ax hne).2
  unique_loop := by
    intro x y l₁ l₂ h1 h2 hx1 hy1 hx2 hy2
    have hne : x.1 ≠ y.1 := by
      intro h
      obtain ⟨a, b⟩ := x
      obtain ⟨c, d⟩ := y
      simp only at h
      subst h
      cases b <;> cases d <;> simp_all
    simp only [mem_product, mem_univ, and_true, mem_pts] at hx1 hy1 hx2 hy2
    exact (Nondegenerate.eq_or_eq hx1 hy1 hx2 hy2).resolve_left hne
  loops_meet := by
    intro l₁ l₂
    by_cases h : l₁ = l₂
    · subst h
      have hc : 0 < (pts P Ln l₁).card := by rw [card_pts]; omega
      obtain ⟨p, hp⟩ := card_pos.mp hc
      exact ⟨(p, false), by simp [mem_product, hp], by simp [mem_product, hp]⟩
    · refine ⟨(HasPoints.mkPoint h, false), ?_, ?_⟩
      · simp only [mem_product, mem_univ, and_true, mem_pts]
        exact (HasPoints.mkPoint_ax h).1
      · simp only [mem_product, mem_univ, and_true, mem_pts]
        exact (HasPoints.mkPoint_ax h).2
  two_loops := by
    obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, -, -, -, -⟩ :=
      @ProjectivePlane.exists_config P Ln _ _
    exact ⟨l₁, l₂, fun h => h₂₁ (h ▸ h₂₂)⟩

open Classical in
/-- the place of a point on a line, `0, …, q` -/
noncomputable def idx (l : Ln) (p : P) : ℕ :=
  if h : p ∈ pts P Ln l then ((pts P Ln l).equivFin ⟨p, h⟩ : ℕ) else 0

lemma idx_lt (l : Ln) (p : P) : idx P Ln l p < ProjectivePlane.order P Ln + 1 := by
  classical
  unfold idx
  split_ifs with h
  · rw [← card_pts P Ln l]
    exact Fin.isLt _
  · omega

omit [Fintype Ln] [ProjectivePlane P Ln] in
lemma idx_inj (l : Ln) {p p' : P} (hp : p ∈ pts P Ln l) (hp' : p' ∈ pts P Ln l)
    (h : idx P Ln l p = idx P Ln l p') : p = p' := by
  classical
  simp only [idx, hp, hp', dite_true] at h
  have := (pts P Ln l).equivFin.injective (Fin.ext h)
  exact congrArg Subtype.val this

/-- **Positions on the doubled plane**: a ring runs through the points of its line on one side,
at `0, …, q`, and back through them on the other, at `q + 1, …, 2q + 1`. -/
noncomputable def doublePositions : (double P Ln).Positions where
  pos l x := ((idx P Ln l x.1 + if x.2 then ProjectivePlane.order P Ln + 1 else 0 : ℕ) :
    ZMod (2 * (ProjectivePlane.order P Ln + 1)))
  pos_inj := by
    intro l x y hx hy hxy
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    have ha : a ∈ pts P Ln l := (Finset.mem_product.mp hx).1
    have hc : c ∈ pts P Ln l := (Finset.mem_product.mp hy).1
    have h1 := idx_lt P Ln l a
    have h2 := idx_lt P Ln l c
    set q := ProjectivePlane.order P Ln
    simp only at hxy
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by split_ifs <;> omega),
      Nat.mod_eq_of_lt (by split_ifs <;> omega)] at hxy
    have hbd : b = d := by
      cases b <;> cases d <;> simp at hxy <;> first | rfl | omega
    subst hbd
    have hi : idx P Ln l a = idx P Ln l c := by
      cases b <;> simp at hxy <;> omega
    rw [idx_inj P Ln l ha hc hi]
  pos_opp := by
    intro l x hx
    obtain ⟨a, b⟩ := x
    set q := ProjectivePlane.order P Ln
    have hhalf : (2 * (q + 1)) / 2 = q + 1 := by omega
    show ((idx P Ln l a + if (!b) then q + 1 else 0 : ℕ) : ZMod (2 * (q + 1))) =
      ((idx P Ln l a + if b then q + 1 else 0 : ℕ) : ZMod (2 * (q + 1))) +
        (((2 * (q + 1)) / 2 : ℕ) : ZMod (2 * (q + 1)))
    rw [hhalf]
    cases b
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, add_zero]
      push_cast
      have h0 : ((2 * (q + 1) : ℕ) : ZMod (2 * (q + 1))) = 0 := ZMod.natCast_self _
      push_cast at h0
      linear_combination -h0

/-- **A plane of order `q` gives a register of `L = 2(q + 1)`**, with its cyclic order, and the
register's order as a projective plane (`Projective.lean`) is `q` again. -/
theorem register_of_plane :
    ∃ H : Horizon (2 * (ProjectivePlane.order P Ln + 1)), Nonempty H.Positions ∧
      ∀ hL : 6 ≤ 2 * (ProjectivePlane.order P Ln + 1), H.order hL = ProjectivePlane.order P Ln := by
  refine ⟨double P Ln, ⟨doublePositions P Ln⟩, fun hL => ?_⟩
  have h := (double P Ln).two_mul_order_add_one hL
  omega

/-- The order of a finite projective plane is at least `2`, so its register has `L ≥ 6`. -/
theorem six_le_double : 6 ≤ 2 * (ProjectivePlane.order P Ln + 1) := by
  have := ProjectivePlane.one_lt_order P Ln
  omega

end Doubling

end Horizon
