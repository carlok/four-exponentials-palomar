module

public import Mathlib
public import Diaz.Mirror.exp_e_or_exp_e_sq_transcendental
public import Diaz.Mirror.four_exponentials_trdeg_one
public import Diaz.Mirror.two_algebraically_independent_of_exp_column

public section

/-!
# Proved solution

The proved counterparts of the declarations stated in `Challenge.lean`. Comparator checks that
each has the same name and type as its counterpart there and depends on no axiom beyond
`propext`, `Quot.sound` and `Classical.choice`. Each is the library theorem named beside it,
whose statement is the same up to unfolding the library's abbreviations.

* `FourExponentials.four_exponentials_trdeg_one`: `Diaz.four_exponentials_trdeg_one`
* `FourExponentials.exp_e_or_exp_e_sq_transcendental`: `Transcendence.exp_e_or_exp_e_sq_transcendental`
* `FourExponentials.two_algebraically_independent_of_exp_column`: `Diaz.two_algebraically_independent_of_exp_column`
-/

namespace FourExponentials

theorem four_exponentials_trdeg_one :
    ∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ,
      IsAlgebraic ℚ (Complex.exp l₁₁) → IsAlgebraic ℚ (Complex.exp l₁₂) →
      IsAlgebraic ℚ (Complex.exp l₂₁) → IsAlgebraic ℚ (Complex.exp l₂₂) →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 →
      l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0)
      ∨ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) :=
  Diaz.four_exponentials_trdeg_one

theorem exp_e_or_exp_e_sq_transcendental :
    Transcendental ℚ (Complex.exp (Complex.exp 1)) ∨
      Transcendental ℚ (Complex.exp (Complex.exp 1 ^ 2)) :=
  Transcendence.exp_e_or_exp_e_sq_transcendental

theorem two_algebraically_independent_of_exp_column :
    ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      ∃ a ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
          Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
        ∃ b ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
            Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
          AlgebraicIndependent ℚ ![a, b] :=
  Diaz.two_algebraically_independent_of_exp_column

end FourExponentials
