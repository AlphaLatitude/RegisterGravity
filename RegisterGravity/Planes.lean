import RegisterGravity.Models
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# A register for every prime power

Sec. II of the paper: "every plane of order `k` gives a register of `L = 2(k + 1)`, each point
doubled into a cell and its opposite, as the Lean files prove.  Since planes exist for every
prime-power order [Veblen and Bussey] and primes lie close together [Dusart], many values of `L`
... have a register".  The first sentence is `Horizon.register_of_plane`
(`Models.lean`).  For the second, Mathlib has the projective plane over any field `K`, the
projectivization `ℙ K (Fin 3 → K)` with incidence by orthogonality, and the finite field
`GaloisField p n` of `pⁿ` elements for every prime `p` and `n ≥ 1`.  The plane over a field of `q`
elements has `q² + q + 1` points, so its order is `q`, and its doubling is a register of
`L = 2(q + 1)`.

Which values of `L` near `L_cos` are of this form rests on the distribution of primes, for which
the paper cites Dusart; the files do not prove it, and no theorem uses it.
-/

open Configuration

open scoped LinearAlgebra.Projectivization

namespace Horizon

/-- **The plane over a finite field of `q` elements has order `q`**: it has `q² + q + 1` points,
which is `order² + order + 1`. -/
theorem fieldPlane_order (K : Type) [Field K] [Fintype K] [DecidableEq K] :
    ProjectivePlane.order (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) = Fintype.card K := by
  classical
  have : Fintype (ℙ K (Fin 3 → K)) := Fintype.ofFinite _
  have h1 := ProjectivePlane.card_points (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K))
  have h2 : Nat.card (ℙ K (Fin 3 → K)) = ∑ i ∈ Finset.range 3, Nat.card K ^ i :=
    Projectivization.card_of_finrank K (Fin 3 → K) (by simp)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h2
  set o := ProjectivePlane.order (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K))
  set q := Fintype.card K
  have h : (o : ℤ) ^ 2 + o = (q : ℤ) ^ 2 + q := by
    have : o ^ 2 + o + 1 = 1 + q + q ^ 2 := h1.symm.trans h2
    have : (o : ℤ) ^ 2 + o + 1 = 1 + q + (q : ℤ) ^ 2 := by exact_mod_cast this
    linarith
  have hfac : ((o : ℤ) - q) * ((o : ℤ) + q + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h3 | h3
  · omega
  · have : (0 : ℤ) < (o : ℤ) + q + 1 := by positivity
    linarith

/-- **A register for every prime power**: for every prime `p` and `n ≥ 1` there is a register of
`L = 2(pⁿ + 1)`, with its cyclic order. -/
theorem register_of_prime_power (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    ∃ H : Horizon (2 * (p ^ n + 1)), Nonempty H.Positions := by
  classical
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have : Fintype (ℙ (GaloisField p n) (Fin 3 → GaloisField p n)) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n hn
  have ho := fieldPlane_order (GaloisField p n)
  rw [hq] at ho
  have key := register_of_plane (ℙ (GaloisField p n) (Fin 3 → GaloisField p n))
    (ℙ (GaloisField p n) (Fin 3 → GaloisField p n))
  rw [ho] at key
  obtain ⟨H, hP, -⟩ := key
  exact ⟨H, hP⟩

end Horizon
