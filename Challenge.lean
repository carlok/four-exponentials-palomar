module

public import Mathlib

public section

/-!
# The four exponentials theorem in transcendence degree one, and Schneider's eighth problem

The statements below are the results this repository registers. Each is stated with Mathlib's
own notions and nothing defined here; each `sorry` is deliberate, and `Solution.lean` proves
the same statement from the library under `Diaz/`.

## `FourExponentials.four_exponentials_trdeg_one`

**The four exponentials theorem in transcendence degree one** (Waldschmidt 1973; Brownawell
1974). Let `lᵢⱼ` be four non-zero logarithms of algebraic numbers with `l₁₁ l₂₂ = l₁₂ l₂₁`. If
the field they generate has transcendence degree at most one over `ℚ`, then the rows or the
columns of the matrix `(lᵢⱼ)` are linearly dependent over `ℚ`.

* The four `exp lᵢⱼ` are algebraic over `ℚ` and the `lᵢⱼ` are non-zero.
* `l₁₁ * l₂₂ = l₁₂ * l₂₁` says the matrix has rank one; `Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ
  {l₁₁, l₁₂, l₂₁, l₂₂}) ≤ 1` is the transcendence-degree hypothesis.
* The conclusion gives rationals `a, b`, not both zero, annihilating the two columns, or the
  two rows.
* Source: Waldschmidt 1973; Brownawell 1974.

## `FourExponentials.exp_e_or_exp_e_sq_transcendental`

**Schneider's eighth problem** (Waldschmidt 1973; Brownawell 1974): one of `e^e` and `e^{e²}`
is transcendental.

* `Complex.exp (Complex.exp 1)` is `e^e` and `Complex.exp (Complex.exp 1 ^ 2)` is `e^{e²}`;
  `Transcendental ℚ` is Mathlib's "not algebraic over `ℚ`".
* Source: Waldschmidt 1973 (solution of Schneider's eighth problem); Brownawell 1974.

## `FourExponentials.two_algebraically_independent_of_exp_column`

If `x₁, x₂` and `y₁, y₂` are each linearly independent over `ℚ` and `exp (x₁ y₂)`, `exp (x₂
y₂)` are algebraic, then two of the eight numbers `xᵢ, yⱼ, exp (xᵢ yⱼ)` are algebraically
independent over `ℚ` (Waldschmidt 1973; Brownawell 1974).

* The hypotheses fix one column of the matrix `(exp (xᵢ yⱼ))` as algebraic.
* The conclusion picks `a, b` from the eight-element set and asserts `AlgebraicIndependent ℚ
  ![a, b]`; in particular `a ≠ b`.
* Source: Waldschmidt 1973; Brownawell 1974.
-/

namespace FourExponentials

/-- **The four exponentials theorem in transcendence degree one** (Waldschmidt 1973; Brownawell
1974). Let `lᵢⱼ` be four non-zero logarithms of algebraic numbers with `l₁₁ l₂₂ = l₁₂ l₂₁`. If
the field they generate has transcendence degree at most one over `ℚ`, then the rows or the
columns of the matrix `(lᵢⱼ)` are linearly dependent over `ℚ`. -/
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
          (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) := by
  sorry

/-- **Schneider's eighth problem** (Waldschmidt 1973; Brownawell 1974): one of `e^e` and `e^{e²}`
is transcendental. -/
theorem exp_e_or_exp_e_sq_transcendental :
    Transcendental ℚ (Complex.exp (Complex.exp 1)) ∨
      Transcendental ℚ (Complex.exp (Complex.exp 1 ^ 2)) := by
  sorry

/-- If `x₁, x₂` and `y₁, y₂` are each linearly independent over `ℚ` and `exp (x₁ y₂)`, `exp (x₂
y₂)` are algebraic, then two of the eight numbers `xᵢ, yⱼ, exp (xᵢ yⱼ)` are algebraically
independent over `ℚ` (Waldschmidt 1973; Brownawell 1974). -/
theorem two_algebraically_independent_of_exp_column :
    ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      ∃ a ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
          Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
        ∃ b ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
            Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
          AlgebraicIndependent ℚ ![a, b] := by
  sorry

end FourExponentials
