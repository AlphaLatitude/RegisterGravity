import RegisterGravity.Galactic
import RegisterGravity.RouteB

/-!
# The count and the chain, joined

`Horizon.lean` and `RouteB.lean` count the cells and rings of a `Horizon L`, with `L` a natural
number.  `Chain.lean` and `Galactic.lean` derive the laws over a register `Reg` whose `L` is a
positive real, with the horizon's counts entered as `L²/2` and `L²/4` and the share of a sphere's
strings inside it as `4n/L`.  The two theorems here join them for any register whose `L` is that
of the horizon:

* `counts_exact`: the rings and cells of the horizon number the chain's `R_hor = L²/4` and
  `C_hor = L²/2` times `1 − 2/L + 4/L²` (Eq. (counts) with `Reg.counts_leading_order`), so the
  chain's counts are the horizon's to relative order `2/L`;
* `Sin_from_count`: for a cell `Q` of the sphere at distance `n` from the body's cell, the chain's
  `S_in(r) = Sin 4 r` at `r = nℓ_c` is the fraction that `route_B_fraction` counts, without its
  correction `1 + 1/2n`, times the sphere's `N_s(r)` bits.  So Eq. (volume) is the count of
  Sec. IV.C to leading order in `1/n`, and the `κ = 4` of `Sin` is the count's.
* `horizon_entropy_count`: every largest ring has half its cells inside any observer's horizon,
  so the horizon counts every ring of the register at one bit each, `card Loop · ln 2`, the chain's
  `S_hor` to relative order `2/L`; a ring's share of the horizon's area is that area over this
  count.

`Strings` is the state of the rings of a `Horizon L` that the paper's definition of a cell gives: a
cell holds one bit of each ring through it, so each largest ring carries exactly one string, a bit
on each of its cells.
-/

open Finset

namespace Register
namespace Bridge

variable {L : ℕ} (H : Horizon L) (R : Reg)

/-- **The strings on the rings** (Sec. II).  A cell holds one bit of each ring through it (the
paper's definition of a cell), so the bits on a ring's cells form one string of Postulate 1: every
largest ring carries exactly one, and a second string would need a second bit on each of its
cells.  `Strings` is that state, a bit for each ring and each of its cells.  What can change in a
free string is which way it moves, a doublet, whose entropy is one bit (`Reg.one_bit`,
`Reg.entropy_per_ring`). -/
def Strings : Type := ∀ l : H.Loop, {X // X ∈ H.cells l} → Bool

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

/-- **Every ring is counted on every horizon** (Sec. II, "The horizon's area"; Sec. IV.D).  Every
largest ring has half its cells inside any observer's horizon, counting a cell on it as half
(`Horizon.Positions.horizon_weight_ring`), so every one of the register's rings carries its bit on
the horizon: at one bit per ring the horizon's entropy is `card Loop · ln 2`, which is the chain's
`S_hor = (L²/4) ln 2` times `1 − 2/L + 4/L²` (`counts_exact`).  A ring's share of the horizon's
area, `A_hor/R` (`Reg.ringShare`), is then the solution's area over this count, a quotient, not an
identification. -/
theorem horizon_entropy_count [NeZero L] (P : H.Positions) (hL : 4 ≤ L) (hRL : R.L = L)
    (B : H.Cell) :
    (∀ l : H.Loop,
      ∑ X ∈ H.cells l, Horizon.Positions.weight (L := L) (P.dist B X) = (L : ℝ) / 2) ∧
    (Fintype.card H.Loop : ℝ) * R.ln2 = R.Shor * (1 - 2 / R.L + 4 / R.L ^ 2) := by
  refine ⟨fun l => P.horizon_weight_ring hL B l, ?_⟩
  rw [(counts_exact H R hL hRL).1]
  unfold Reg.Shor
  ring

/-- **Eq. (volume) from the count** (Sec. IV.C).  Let the largest rings of `H` carry the cyclic
order `P`, let `B` be the body's cell and `Q` a cell of the sphere at distance `n` from it, with
`1 ≤ n` and `4n < L`, and let the register `R` have the same `L`.  On the rings through `Q`, the
fraction of the cells inside the horizon that lie within the sphere is `(4n/L)(1 + 1/2n)`
(`route_B_fraction`).  Without its correction `1 + 1/2n`, and times the `N_s(r)` bits of the
sphere of radius `r = nℓ_c`, it is the chain's `S_in(r) = Sin 4 r`. -/
theorem Sin_from_count [NeZero L] (P : H.Positions) (hL : 4 ≤ L) (B Q : H.Cell) {n : ℕ}
    (hQ : P.dist B Q = n) (hn1 : 1 ≤ n) (hn : 4 * n < L) (hRL : R.L = L) :
    R.Sin 4 (n * R.ℓc)
      = ((∑ l ∈ H.through Q, ((H.cells l).filter (fun X => P.dist B X ≤ n)).card : ℕ) : ℝ)
          / (∑ l ∈ H.through Q, ∑ X ∈ H.cells l, Horizon.Positions.weight (L := L) (P.dist B X))
          / (1 + 1 / (2 * n)) * R.Ns (n * R.ℓc) * R.ln2 := by
  obtain ⟨hfrac, hcorr⟩ := P.route_B_fraction hL B Q hQ hn1 hn
  rw [hfrac, hcorr]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hc : (1 : ℝ) + 1 / (2 * n) ≠ 0 := by positivity
  have hℓ : R.ℓc ≠ 0 := R.ℓc_pos.ne'
  have hL0 : (L : ℝ) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    exact this.ne'
  unfold Reg.Sin Reg.n
  rw [hRL]
  field_simp

end Bridge
end Register
