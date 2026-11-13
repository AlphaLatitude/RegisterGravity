import RegisterGravity.RouteB
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A ring's string, the lap, the two senses, and the bit a string keeps (Sec. II)

Formal counterpart of five sentences of Sec. II that the other files took in words.

* `Horizon.ringStrings`, `Horizon.card_ring`: "By the definition of a cell, every ring carries
  exactly one string: each of its cells holds one bit of it, and those bits form a string of
  Postulate 1".  A cell holds one bit of each ring through it (Sec. II's definition of a cell), so
  what the cells hold is a bit for every pair of a cell and a ring through it.  That is the same
  as a family of strings, one for each ring, each with one bit on each of the ring's `L` cells.
* `Horizon.Positions.lap`: "`L` ticks of the shift make one lap of a largest ring".  The shift
  moves a bit one cell along its ring per tick (Postulate 1), so after `k` ticks the bit that was
  at the position `p` is at `p + k`.  It is back at its cell after `L` ticks and not before.
* `Horizon.Positions.two_senses`: "a translation along a ring can go two ways, with the ring or
  against it: the two senses".  The cells one step from a cell along a ring are the two at the
  positions one ahead and one behind, and these are different cells.
* `Register.Strings.sense_of_state`: "No law fixes the sense, since none depends on the direction
  in which a ring passes through a cell (Postulate 2), so the sense is a property of the string's
  state, and reading it is a measurement with two values".
* `Register.Strings.bit_kept`: "Every string has kept its bit since: an interaction changes its
  sense without making either likelier, and no law favors a sense (Postulate 2)".
* `Register.Strings.unscattered`: "the fraction of strings not yet scattered after `t` such times
  is `e^{−t}`, so after `ln R ≈ 282` of them fewer than one of the `R` strings is out of
  equilibrium".
-/

namespace Horizon

variable {L : ℕ} (H : Horizon L)

/-- **Every ring carries exactly one string** (Sec. II: "By the definition of a cell, every ring
carries exactly one string: each of its cells holds one bit of it, and those bits form a string of
Postulate 1").  "A cell is a place on a ring, holding one bit of each ring through it" (Sec. II),
so the cells hold one bit for every pair of a cell and a ring through it.  These bits are the
same thing as a family of strings, one for each ring `l`: the bits of the cells of `l` that
belong to `l`.  The two descriptions correspond one to one. -/
def ringStrings :
    ({p : H.Cell × H.Loop // p.1 ∈ H.cells p.2} → Bool) ≃
      (∀ l : H.Loop, {x // x ∈ H.cells l} → Bool) where
  toFun f l x := f ⟨(x.1, l), x.2⟩
  invFun g p := g p.1.2 ⟨p.1.1, p.2⟩
  left_inv f := by
    funext p
    rfl
  right_inv g := by
    funext l x
    rfl

/-- **A ring's string has `L` bits**: one on each of the ring's `L` cells (Postulate 1: "Every
qubit is a string of bits, one on each cell of a ring"; Sec. II's largest ring of `L` cells). -/
theorem card_ring (l : H.Loop) : Fintype.card {x // x ∈ H.cells l} = L := by
  rw [Fintype.card_coe, H.card_cells]

namespace Positions

/-- **The shift** (Postulate 1: "The shift moves every bit of a string one cell along its ring per
tick"), on the positions of a ring: the bit at the position `p` is at `p + 1` one tick later. -/
def shift {L : ℕ} (p : ZMod L) : ZMod L := p + 1

/-- after `k` ticks the bit that was at the position `p` is at `p + k` -/
lemma shift_iterate {L : ℕ} (k : ℕ) (p : ZMod L) : shift^[k] p = p + k := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold shift
    push_cast
    ring

variable {H} (P : H.Positions)

/-- **`L` ticks of the shift make one lap** (Sec. II: "`L` ticks of the shift make one lap of a
largest ring: the lap time is `Lt_c`").  A bit at the cell `x` of the ring `l` is back at the
position of `x` after `L` ticks of the shift, and after no smaller number of ticks. -/
theorem lap (l : H.Loop) (x : H.Cell) :
    shift^[L] (P.pos l x) = P.pos l x ∧
      ∀ k, 0 < k → k < L → shift^[k] (P.pos l x) ≠ P.pos l x := by
  refine ⟨by rw [shift_iterate, ZMod.natCast_self, add_zero], fun k hk hkL h => ?_⟩
  rw [shift_iterate] at h
  have h0 : (k : ZMod L) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact absurd (Nat.le_of_dvd hk h0) (not_le.2 hkL)

/-- **A translation along a ring can go two ways** (Sec. II: "The shift (Postulate 1) is a
translation along the ring, and a translation along a ring can go two ways, with the ring or
against it: the two senses").  On a ring of at least four cells, a cell `y` is one step from a
cell `x` along the ring `l` exactly when its position is one ahead of the position of `x` or one
behind it, and the two positions are different. -/
theorem two_senses (hL : 4 ≤ L) (l : H.Loop) (x y : H.Cell) :
    (P.ringDist l x y = 1 ↔ P.pos l y = P.pos l x + 1 ∨ P.pos l y = P.pos l x - 1) ∧
      P.pos l x + 1 ≠ P.pos l x - 1 := by
  have : NeZero L := ⟨by omega⟩
  have hone : ((1 : ℕ) : ZMod L).val = 1 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have hlast : ((L - 1 : ℕ) : ZMod L).val = L - 1 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have hneg : ((L - 1 : ℕ) : ZMod L) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  obtain ⟨d, hd⟩ : ∃ d : ZMod L, P.pos l y - P.pos l x = d := ⟨_, rfl⟩
  have hdval : d.val < L := ZMod.val_lt d
  have h1 : d.val = 1 ↔ d = 1 := by
    constructor
    · intro h
      rw [← ZMod.natCast_zmod_val d, h, Nat.cast_one]
    · intro h
      rw [h, ← Nat.cast_one, hone]
  have h2 : d.val = L - 1 ↔ d = -1 := by
    constructor
    · intro h
      rw [← ZMod.natCast_zmod_val d, h, hneg]
    · intro h
      rw [h, ← hneg, hlast]
  have e1 : P.pos l y = P.pos l x + 1 ↔ d = 1 := by
    rw [← hd]
    constructor
    · intro h
      rw [h]
      ring
    · intro h
      rw [← h]
      ring
  have e2 : P.pos l y = P.pos l x - 1 ↔ d = -1 := by
    rw [← hd]
    constructor
    · intro h
      rw [h]
      ring
    · intro h
      have : P.pos l y = P.pos l x + (P.pos l y - P.pos l x) := by ring
      rw [this, h]
      ring
  refine ⟨?_, ?_⟩
  · rw [e1, e2, ← h1, ← h2]
    unfold ringDist offset
    rw [hd]
    omega
  · intro h
    have h' : (1 : ZMod L) = -1 := by
      have := congrArg (fun z => z - P.pos l x) h
      simpa using this
    have hv : (1 : ZMod L).val = (-1 : ZMod L).val := by rw [← h']
    rw [← Nat.cast_one, hone, Nat.cast_one, ← hneg, hlast] at hv
    omega

end Positions

end Horizon

namespace Register
namespace Strings

/-- **The sense is a property of the string's state** (Sec. II: "No law fixes the sense, since
none depends on the direction in which a ring passes through a cell (Postulate 2), so the sense is
a property of the string's state, and reading it is a measurement with two values").  `obeys σ`
says that the state `σ` of a string obeys a law, `sense σ` is the sense of the shift in that
state, and `rev σ` is the state with the direction of the ring reversed, which has the other
sense (`hrev`).  The law does not depend on the direction: it says of the reversed state what it
says of the state (`hdir`, Postulate 2).  Then under a law that some state obeys, either sense
occurs: the law does not fix the sense, the state does, and the sense takes both of its two
values. -/
theorem sense_of_state {State : Type*} (obeys : State → Prop) (sense : State → Bool)
    (rev : State → State) (hrev : ∀ σ, sense (rev σ) = !sense σ)
    (hdir : ∀ σ, obeys (rev σ) = obeys σ) (σ₀ : State) (h₀ : obeys σ₀)
    (v : Bool) : ∃ σ, obeys σ ∧ sense σ = v := by
  by_cases h : sense σ₀ = v
  · exact ⟨σ₀, h₀, h⟩
  · refine ⟨rev σ₀, by rw [hdir σ₀]; exact h₀, ?_⟩
    rw [hrev]
    cases hs : sense σ₀ <;> cases v <;> simp_all

/-- **A string keeps its bit** (Sec. II: "Every string has kept its bit since: an interaction
changes its sense without making either likelier, and no law favors a sense (Postulate 2)").
`p s` is the probability of the sense `s` before an interaction, and `flip s` the probability that
the interaction changes the sense `s`, the same for the two senses (`hflip`).  A string whose two
senses are equally likely (`hp`) then has them equally likely after the interaction: it still
holds one bit. -/
theorem bit_kept (p flip : Bool → ℝ) (hp : p true = 1 / 2 ∧ p false = 1 / 2)
    (hflip : flip true = flip false) :
    p true * (1 - flip true) + p false * flip false = 1 / 2 ∧
      p false * (1 - flip false) + p true * flip true = 1 / 2 := by
  obtain ⟨h1, h2⟩ := hp
  rw [h1, h2, hflip]
  constructor <;> ring

/-- **The strings not yet scattered** (Sec. II: "the fraction of strings not yet scattered after
`t` such times is `e^{−t}`, so after `ln R ≈ 282` of them fewer than one of the `R` strings is out
of equilibrium").  `f t` is the fraction of the strings not yet scattered after `t` scattering
times.  Scattering at the rate of one per scattering time takes from it at the rate `f` itself,
`f′ = −f`, from `f(0) = 1`, so `f(t) = e^{−t}`.  Of `R` strings fewer than one is then left,
`R e^{−t} < 1`, exactly when `t > ln R`. -/
theorem unscattered (f : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (-f t) t) (h0 : f 0 = 1) :
    (∀ t, f t = Real.exp (-t)) ∧
      ∀ R t : ℝ, 0 < R → (R * f t < 1 ↔ Real.log R < t) := by
  have hg : ∀ t, HasDerivAt (fun t => f t * Real.exp t) 0 t := by
    intro t
    have h := (hf t).mul (Real.hasDerivAt_exp t)
    have h0' : -f t * Real.exp t + f t * Real.exp t = 0 := by ring
    rwa [h0'] at h
  have hft : ∀ t, f t = Real.exp (-t) := by
    intro t
    have hd : Differentiable ℝ (fun t => f t * Real.exp t) := fun t => (hg t).differentiableAt
    have h := is_const_of_deriv_eq_zero hd (fun x => (hg x).deriv) t 0
    have h1 : f t * Real.exp t = 1 := by simpa [h0] using h
    rw [Real.exp_neg]
    exact eq_inv_of_mul_eq_one_left h1
  refine ⟨hft, fun R t hR => ?_⟩
  rw [hft t]
  have hRe : R * Real.exp (-t) = Real.exp (Real.log R - t) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hR]
  rw [hRe, Real.exp_lt_one_iff]
  constructor <;> intro h <;> linarith

end Strings
end Register
