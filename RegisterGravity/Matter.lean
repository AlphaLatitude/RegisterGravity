import RegisterGravity.Cosmo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Matter and heat in a string's energy (Secs. IV.C and IV.E)

Sec. IV.E splits the energy that a string holds on average, `ε_s = k_BT_dS`, in two.  The
string's heat, the horizon's temperature times the string's one bit, is `ε_s ln 2`, the vacuum's
energy per string (`Reg.string_split`, `Reg.vacuum_per_string`).  The rest is matter,

  `u = (1 − ln 2) ε_s`  (Eq. (u), `Reg.matter`).

Sec. IV.C counts a body's energy per string of the sphere in this unit: "The body is a mass, and
a mass is matter, not heat, so we count the body's energy per string of the sphere in units of the
matter a string holds on average, `f = E/u`".  The premise for the carriers and the derived
Eq. (f) are stated with `Reg.matter` (`Sources.P1.carriers_by_amplitude`,
`Sources.Derived.fill_fraction`), so the unit is named where it enters.

* `Reg.matter`, `Reg.matter_eq`: the matter a string holds on average is its mean energy less its
  heat.
* `Reg.radii_agree`: "For `r ≪ R_Λ` the two agree" (Sec. II).  In the solution without a mass the
  proper distance from the observer along a radial line lies between the areal radius `r` and
  `r/√(1 − r²/R_Λ²)`.
* `Qubit.entropy_lt_of_energies_ne`: "The two senses have the same energy (Sec. II), and making
  them differ would take from each string part of the bit" (Sec. IV.C).  A qubit whose two states
  have different energies holds less than one bit in its thermal state.
* `Reg.split_not_stringwise`: "The split is of the strings' energy as a whole, not string by
  string" (Sec. IV.E).  A string of energy `E` has the heat `k_BT_dS ln 2` of its one bit, so what
  it holds beyond its heat is `E − k_BT_dS ln 2`.  That is the fraction `1 − ln 2` of `E` only for
  a string whose energy is the mean, `E = k_BT_dS`.
-/

namespace Register
namespace Reg

variable (R : Reg)

/-- **Matter** (Secs. IV.C and IV.E, Eq. (u)): of the energy `ε_s` that a string holds on average,
the part that is not heat, `u = (1 − ln 2) ε_s`.  The string's heat, the horizon's temperature
times its one bit, is `ε_s ln 2`, the vacuum's energy per string (`string_split`).  A body is a
mass, and a mass is matter, not heat, so the body's energy per string of a sphere is counted in
this unit (`Sources.P1.carriers_by_amplitude`, `Sources.Derived.fill_fraction`). -/
noncomputable def matter (εs : ℝ) : ℝ := (1 - R.ln2) * εs

/-- the matter a string holds on average is its mean energy less its heat -/
theorem matter_eq (εs : ℝ) : R.matter εs = εs - R.ln2 * εs := by
  unfold matter
  ring

/-- **The split is of the strings' energy as a whole, not string by string** (Sec. IV.E, in these
words).  Every string has the heat `k_BT ln 2`, the horizon's temperature times its one bit, while
its energy `E` differs from string to string.  What a string of energy `E` holds beyond its heat,
`E − k_BT ln 2`, is the fraction `1 − ln 2` of `E` exactly when `E` is the mean energy `k_BT`. -/
theorem split_not_stringwise (T E : ℝ) :
    E - R.kB * T * R.ln2 = (1 - R.ln2) * E ↔ E = R.kB * T := by
  have h := R.ln2_pos
  constructor
  · intro h1
    have h2 : R.ln2 * (E - R.kB * T) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 h.ne'
    · linarith
  · intro h1
    rw [h1]
    ring

/-- **Proper distance and areal radius agree near the observer** (Sec. II: "For `r ≪ R_Λ` the two
agree").  In the solution without a mass the proper distance from the observer along a radial
line is `s(r) = R_Λ arcsin(r/R_Λ)` (`sdS`, with `proper_distance_exists` and `proper_distance`).
It lies between the areal radius `r` and `r/√(1 − r²/R_Λ²)`, so the two differ by at most the
factor `1/√(1 − r²/R_Λ²)`, which is one for `r ≪ R_Λ`. -/
theorem radii_agree (r : ℝ) (hr0 : 0 ≤ r) (hr : r < R.RL) :
    r ≤ R.sdS r ∧ R.sdS r ≤ r / Real.sqrt (1 - (r / R.RL) ^ 2) := by
  have hRL := R.RL_pos
  have hx0 : 0 ≤ r / R.RL := div_nonneg hr0 hRL.le
  have hx1 : r / R.RL < 1 := (div_lt_one hRL).2 hr
  have hy0 : 0 ≤ Real.arcsin (r / R.RL) := Real.arcsin_nonneg.2 hx0
  have hy1 : Real.arcsin (r / R.RL) < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hx1
  have hsin : Real.sin (Real.arcsin (r / R.RL)) = r / R.RL :=
    Real.sin_arcsin (by linarith) hx1.le
  constructor
  · have h := Real.sin_le hy0
    rw [hsin] at h
    unfold sdS
    calc r = R.RL * (r / R.RL) := by field_simp
      _ ≤ R.RL * Real.arcsin (r / R.RL) := mul_le_mul_of_nonneg_left h hRL.le
  · have h := Real.le_tan hy0 hy1
    rw [Real.tan_arcsin] at h
    unfold sdS
    calc R.RL * Real.arcsin (r / R.RL)
        ≤ R.RL * (r / R.RL / Real.sqrt (1 - (r / R.RL) ^ 2)) :=
          mul_le_mul_of_nonneg_left h hRL.le
      _ = r / Real.sqrt (1 - (r / R.RL) ^ 2) := by
          rw [← mul_div_assoc, mul_div_cancel₀ r hRL.ne']

end Reg

namespace Qubit

/-- **Unequal energies would take part of the bit** (Sec. IV.C: "The two senses have the same
energy (Sec. II), and making them differ would take from each string part of the bit").  A qubit
whose two states have different energies, at an inverse temperature `β ≠ 0`, has a thermal weight
other than `1/2` on each, and its entropy is below `ln 2`, one bit. -/
theorem entropy_lt_of_energies_ne (β E₁ E₂ : ℝ) (hβ : β ≠ 0) (hE : E₁ ≠ E₂) :
    weight β E₁ E₂ ≠ 1 / 2 ∧ entropy (weight β E₁ E₂) < Real.log 2 := by
  have h1 := Real.exp_pos (-(β * E₁))
  have h2 := Real.exp_pos (-(β * E₂))
  have hne : weight β E₁ E₂ ≠ 1 / 2 := by
    unfold weight
    intro h
    rw [div_eq_iff (by positivity)] at h
    have he : Real.exp (-(β * E₁)) = Real.exp (-(β * E₂)) := by linarith
    have hmul : β * E₁ = β * E₂ := by
      have := Real.exp_injective he
      linarith
    exact hE (mul_left_cancel₀ hβ hmul)
  refine ⟨hne, ?_⟩
  unfold entropy
  rw [Real.binEntropy_lt_log_two]
  rwa [← one_div]

end Qubit
end Register
