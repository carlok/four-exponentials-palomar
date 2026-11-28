/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Diaz.Mirror.length_mul_le

/-!
# Length of a sum

For every finite family $(f_i)_{i\in s}$ in $\mathbb{Z}[X][Y]$,
$$ L\Bigl(\sum_{i\in s}f_i\Bigr)\le\sum_{i\in s}L(f_i). $$

Source: Standard.

## Proof outline

For a size function `ν : R → ℕ` on a semiring `R` and `p ∈ R[X]`, let `λ_ν(p) = ∑ₙ ν(pₙ)`, the
sum running over the support of `p`. The length of `P ∈ ℤ[X][Y]` is `λ_{λ_ν}(P)` with `ν = |·|`.

If `ν(0) = 0` and `ν` is subadditive, then so is `λ_ν`: both sides may be summed over the union
of the two supports, since a coefficient outside the support is `0` and has size `0`, and there
the inequality holds termwise. Applied first to `|·|` on `ℤ` and then to `λ_{|·|}` on `ℤ[X]`, this
makes the length subadditive, and induction on the finset gives the claim.

From `Diaz/Mirror/length_sum_le.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `Transcendence.length_sum_le`.
-/

@[expose] public section

namespace Transcendence

open LengthMulLe in
/-- **Length of a sum.** For every finite family $(f_i)_{i\in s}$ in $\mathbb{Z}[X][Y]$,
$$ L\Bigl(\sum_{i\in s}f_i\Bigr)\le\sum_{i\in s}L(f_i). $$ -/
theorem length_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial ℤ)) :
    ∑ k ∈ (∑ i ∈ s, f i).support, ∑ j ∈ ((∑ i ∈ s, f i).coeff k).support,
        (((∑ i ∈ s, f i).coeff k).coeff j).natAbs ≤
      ∑ i ∈ s, ∑ k ∈ (f i).support, ∑ j ∈ ((f i).coeff k).support,
        (((f i).coeff k).coeff j).natAbs := by
  exact Finset.le_sum_of_subadditive (lam (lam Int.natAbs))
      (lam_zero (lam Int.natAbs)).le
    (lam_add_le (lam Int.natAbs) (lam_zero Int.natAbs)
      (lam_add_le Int.natAbs Int.natAbs_zero Int.natAbs_add_le)) s f

end Transcendence
