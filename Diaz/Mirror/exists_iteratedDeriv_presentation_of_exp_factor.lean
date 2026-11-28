/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Diaz.Mirror.length_mul_le
public import Diaz.Mirror.length_sum_le
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Diaz.Mirror.presentation_size

/-!
# Integer presentations of the derivatives, from a presented exponential factor

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `δ = φ(D)`, `β = j x₁ + k x₂` and `ζ = a y₁ + b y₂`.
The exponential factor is given: integer polynomials `U_{jk}` with `φ(U_{jk}) = Λ₁ e^(βζ)`, of
length at most `L` and degrees at most `d`.

* **Leibniz.** `(z^i e^(βz))⁽ᵐ⁾(ζ) = ∑_{l ≤ m} C(m,l) i(i-1)⋯(i-l+1) ζ^(i-l) β^(m-l) e^(βζ)`,
  and the `m`-th derivative is linear in the coefficients `f_{ijk}`.
* **Polynomial factors.** Since `δβ = φ(j E₀ + k E₁)` and `δζ = φ(a G₀ + b G₁)`, for `l ≤ i < S`
  the number `δ^(m+S) ζ^(i-l) β^(m-l) Λ₁ e^(βζ)` is `φ` of
  `D^l (j E₀ + k E₁)^(m-l) (a G₀ + b G₁)^(i-l) D^(S-i+l) U_{jk}`. For `l > i` the Leibniz term
  vanishes.
* **Sizes.** Lengths are controlled by `len(PQ) ≤
  len(P)
  len(Q)` and
  `len(∑ Pᵢ) ≤ ∑
  len(Pᵢ)`; the
  degrees in `X` and `Y` add up under products. If `c₀` bounds the lengths and degrees of `D`, `E`
  and `G`, the lengths of the `P_{ijk}` are at most `K^(4m+S) L` with `K = 2(1+m+S+T+a+b)c₀`,
  and their degrees at most `(2m+S)c₀ + d`. For `c = 2c₀ + 4`,
  `K^(4m+S) ≤ c^(c(1+m+S)) (1+m+S+T+a+b)^(c(1+m+S))`.

The helpers are those of the accepted proof of `exists_iteratedDeriv_presentation`, which
is this statement with the exponential factor presented from four algebraic exponentials.

From `Diaz/Mirror/exists_iteratedDeriv_presentation_of_exp_factor.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.exists_iteratedDeriv_presentation_of_exp_factor`.
-/

@[expose] public section

namespace Diaz

namespace ExistsIteratedDerivPresentationOfExpFactor

open Polynomial PresentationSize

/-! ### Length and size of integer polynomials in two variables -/

/-! ### Values of integer polynomials -/

lemma exists_iteratedDeriv_presentation_of_exp_factor_sz_lin {U V : ℤ[X][X]} {c : ℕ} (hU :
    Sz U c c) (hV :
        Sz V c c) (p q : ℕ) :
    Sz (C (C (p : ℤ)) * U + C (C (q : ℤ)) * V) ((p +
        q) * c) c :=
  sz_mono
      (sz_add
          (sz_mul
              (sz_CN p) hU)
                  (sz_mul
                      (sz_CN q) hV)) (Nat.add_mul p
                          q c).symm.le
    (Nat.zero_add c).le

/-! ### The presentation of the derivative -/

lemma exists_iteratedDeriv_presentation_of_exp_factor_sz_pres {Dp Bp Zp ep : ℤ[X][X]} {K c E dE S m
    i : ℕ} (hD : Sz Dp K c) (hB :
        Sz Bp K c)
    (hZ : Sz Zp K c) (he :
        Sz ep E dE) (hi : i < S) (hK : 2 * (i + 1) ≤
            K) :
    Sz
        (pres Dp Bp Zp ep S m i) (K ^ (4 * m + S) *
            E) ((2 * m + S) * c + dE) := by
  have hK0 : 0 < K := by omega
  have hcoef : ∀ l, l ≤ m → m.choose l * i.descFactorial l ≤ K ^ m := fun l hl =>
    calc m.choose l * i.descFactorial l ≤ 2 ^ m * (i + 1) ^ m :=
          Nat.mul_le_mul (Nat.choose_le_two_pow m l)
            ((Nat.descFactorial_le_pow i l).trans ((Nat.pow_le_pow_left (Nat.le_succ i) l).trans
              (Nat.pow_le_pow_right (Nat.succ_pos i) hl)))
      _ = (2 * (i + 1)) ^ m := (Nat.mul_pow 2 (i + 1) m).symm
      _ ≤ K ^ m := Nat.pow_le_pow_left hK m
  have h : Sz
      (pres Dp Bp Zp ep S m i) ((Finset.range (m +
          1)).card * (K ^ (3 * m + S) * E))
      ((2 * m + S) * c + dE) :=
    sz_sum (Finset.range (m + 1)) _ fun l hl => by
      have hl' := Finset.mem_range.1 hl
      refine sz_mono
          (sz_mul
              (sz_mul
                  (sz_CN _)
                      (sz_mul
                          (sz_mul
                              (sz_mul
                                  (sz_pow hD l)
        (sz_pow hB (m -
            l))) (sz_pow hZ (i -
                l))) (sz_pow hD (S - i +
                    l)))) he) ?_ ?_
      · refine Nat.mul_le_mul_right E ?_
        rw [← pow_add, ← pow_add, ← pow_add]
        calc m.choose l * i.descFactorial l * K ^ (l + (m - l) + (i - l) + (S - i + l))
            ≤ K ^ m * K ^ (2 * m + S) :=
              Nat.mul_le_mul (hcoef l (by omega)) (Nat.pow_le_pow_right hK0 (by omega))
          _ = K ^ (3 * m + S) := by rw [← pow_add, show m + (2 * m + S) = 3 * m + S by omega]
      · rw [Nat.zero_add, ← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right c (by omega)) dE
  refine sz_mono h ?_ le_rfl
  rw [Finset.card_range]
  calc (m + 1) * (K ^ (3 * m + S) * E) ≤ K ^ m * (K ^ (3 * m + S) * E) :=
        Nat.mul_le_mul_right _ ((succ_le_two_pow
            m).trans (Nat.pow_le_pow_left (by omega) m))
    _ = K ^ (4 * m + S) * E := by
        rw [← Nat.mul_assoc, ← pow_add, show m + (3 * m + S) = 4 * m + S by omega]

/-! ### The presentation, from a presented exponential factor -/

/-- The polynomial `P_{ijk}`, from the polynomial `ep = U_{jk}` presenting the exponential
factor. -/
noncomputable def existsIteratedDerivPresentationOfExpFactorPpol (D : ℤ[X][X]) (E G : Fin 2 →
    ℤ[X][X]) (ep : ℤ[X][X]) (S a b m i j k : ℕ) :
    ℤ[X][X] :=
  pres D (C (C (j : ℤ)) * E 0 + C (C (k : ℤ)) *
      E 1) (C (C (a : ℤ)) * G 0 + C (C (b : ℤ)) * G 1)
    ep S m i

/-- The statement, for an arbitrary ring homomorphism `φ : ℤ[X][Y] → ℂ`. -/
theorem exists_iteratedDeriv_presentation_of_exp_factor_main (x₁ x₂ y₁ y₂ : ℂ) (φ : ℤ[X][X] →+* ℂ)
    (D : ℤ[X][X]) (E G : Fin 2 → ℤ[X][X])
    (hE : ∀ i, ![x₁, x₂] i * φ D = φ (E i)) (hG : ∀ j, ![y₁, y₂] j * φ D = φ (G j)) :
    ∃ c : ℕ, ∀ (S T a b m : ℕ) (Λ₁ : ℂ) (L d : ℕ) (U : Fin T → Fin T → ℤ[X][X]),
      (∀ j k, len (U j k) ≤ L) → (∀ j k r,
          ((U j k).coeff r).natDegree ≤ d) →
      (∀ j k, (U j k).natDegree ≤ d) →
      (∀ j k : Fin T, φ (U j k) = Λ₁ * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) *
        ((a : ℂ) * y₁ + (b : ℂ) * y₂))) →
      ∃ P : Fin S → Fin T → Fin T → ℤ[X][X],
        (∀ i j k, len (P i j k) ≤
          c ^ (c * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) * L) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S) + d) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S) + d) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          φ D ^ (m + S) * Λ₁ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T,
              ∑ k : Fin T, f i j k * z ^ (i : ℕ) *
                Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, f i j k * φ (P i j k) := by
  -- a common size `c₀` for the data
  obtain ⟨cD, hcD⟩ := sz_exists D
  obtain ⟨cE, hcE⟩ := sz_exists_fam E
  obtain ⟨cG, hcG⟩ := sz_exists_fam G
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = cD + cE + cG + 1 := ⟨_, rfl⟩
  have hD0 : Sz D c₀ c₀ :=
      sz_mono hcD (by omega) (by omega)
  have hE0 : ∀ p, Sz (E p) c₀ c₀ :=
      fun p => sz_mono (hcE p) (by omega) (by omega)
  have hG0 : ∀ q, Sz (G q) c₀ c₀ :=
      fun q => sz_mono (hcG q) (by omega) (by omega)
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * c₀ + 4 := ⟨_, rfl⟩
  refine ⟨c, fun S T a b m Λ₁ L d U hUl hUx hUy hU => ?_⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 + m + S + T + a + b := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * Q * c₀ := ⟨_, rfl⟩
  rw [← hQ]
  -- elementary inequalities
  have hQK : 2 * Q ≤ K := by
    rw [hK]
    calc 2 * Q = 2 * Q * 1 := (Nat.mul_one _).symm
      _ ≤ 2 * Q * c₀ := Nat.mul_le_mul_left _ (by omega)
  have hc₀K : c₀ ≤ K := by
    rw [hK]
    calc c₀ = 1 * c₀ := (Nat.one_mul _).symm
      _ ≤ 2 * Q * c₀ := Nat.mul_le_mul_right _ (by omega)
  have hmS : 4 * m + S ≤ c * (1 + m + S) := by
    have : 4 * (1 + m + S) ≤ c * (1 + m + S) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdeg : (2 * m + S) * c₀ + d ≤ c * (1 + m + S) + d := by
    have e1 : (2 * m + S) * c₀ ≤ (2 * m + 2 * S) * c₀ := Nat.mul_le_mul_right c₀ (by omega)
    have e2 : (2 * m + 2 * S) * c₀ = 2 * c₀ * (m + S) := by ring
    have e3 : 2 * c₀ * (m + S) ≤ c * (m + S) := Nat.mul_le_mul_right (m + S) (by omega)
    have e4 : c * (1 + m + S) = c + c * (m + S) := by ring
    omega
  -- sizes of the `P_{ijk}`
  have hsz : ∀ (i : Fin S) (j k : Fin T),
      Sz
          (existsIteratedDerivPresentationOfExpFactorPpol D E G (U j k) S a b m i j k)
      (K ^ (4 * m + S) * L) ((2 * m + S) * c₀ + d) := fun i j k =>
    exists_iteratedDeriv_presentation_of_exp_factor_sz_pres
        (sz_mono hD0 hc₀K le_rfl)
      (sz_mono
          (exists_iteratedDeriv_presentation_of_exp_factor_sz_lin (hE0 0) (hE0 1) (j : ℕ) (k : ℕ))
        (by rw [hK]; exact Nat.mul_le_mul_right c₀ (by omega)) le_rfl)
      (sz_mono
          (exists_iteratedDeriv_presentation_of_exp_factor_sz_lin (hG0 0) (hG0 1) a b)
        (by rw [hK]; exact Nat.mul_le_mul_right c₀ (by omega)) le_rfl)
      ⟨hUl j k, hUx j k, hUy j k⟩ i.2 (by have := i.2; omega)
  refine ⟨fun i j k => existsIteratedDerivPresentationOfExpFactorPpol D E G (U j k) S a b m i
      j k, fun i j k => ?_,
    fun i j k r => ((hsz i j k).2.1 r).trans hdeg, fun i j k => (hsz i j k).2.2.trans hdeg,
    fun f => ?_⟩
  · -- the length of `P_{ijk}`
    calc len
           (existsIteratedDerivPresentationOfExpFactorPpol D E G (U j k) S a b m i j k)
        ≤ K ^ (4 * m + S) * L := (hsz i j k).1
      _ = (2 * c₀) ^ (4 * m + S) * Q ^ (4 * m + S) * L := by rw [hK]; ring
      _ ≤ c ^ (c * (1 + m + S)) * Q ^ (c * (1 + m + S)) * L :=
          Nat.mul_le_mul_right L (Nat.mul_le_mul
            ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hmS))
            (Nat.pow_le_pow_right (by omega) hmS))
  · -- the identity, by Leibniz's rule
    rw [iteratedDeriv_expPoly S T m x₁ x₂ f,
        Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [existsIteratedDerivPresentationOfExpFactorPpol]
    rw [pres_eval φ
        (lin_eval φ (u := x₁) (v :=
            x₂) (hE 0) (hE 1) (j : ℕ) (k : ℕ))
      (lin_eval φ (u := y₁) (v :=
          y₂) (hG 0) (hG 1) a b) (hU j k) i.2]
    exact mul_left_comm _ _ _

end ExistsIteratedDerivPresentationOfExpFactor

open ExistsIteratedDerivPresentationOfExpFactor PresentationSize in
/-- **Presentations from the exponential factor.** Let
$x_1,x_2,y_1,y_2,\omega,\omega_1\in\mathbb{C}$, let $\varphi$ be evaluation at $(\omega,\omega_1)$,
and let $D,E_i,G_j\in\mathbb{Z}[X][Y]$ with $x_i\varphi(D)=\varphi(E_i)$ and
$y_j\varphi(D)=\varphi(G_j)$. There is $c\in\mathbb{N}$ with the following property. Let
$S,T,a,b,m,L,\delta\in\mathbb{N}$ and $\Lambda_1\in\mathbb{C}$, and let $U_{jh}\in\mathbb{Z}[X][Y]$
($j,h<T$), of length at most $L$ and of degree at most $\delta$ in $X$ and in $Y$, satisfy
$$ \varphi(U_{jh})=\Lambda_1\,e^{(jx_1+hx_2)(ay_1+by_2)}. $$
Then there are $P_{ijh}\in\mathbb{Z}[X][Y]$ ($i<S$, $j,h<T$), of length at most
$c^{c(1+m+S)}(1+m+S+T+a+b)^{c(1+m+S)}L$ and of degree at most $c(1+m+S)+\delta$ in $X$ and in $Y$,
such that for all $f_{ijh}\in\mathbb{C}$
$$ \varphi(D)^{m+S}\,\Lambda_1
\cdot\frac{d^{m}}{dz^{m}}\Bigl(\sum_{i,j,h}f_{ijh}\,z^{i}e^{(jx_1+hx_2)z}\Bigr) \Big|_{z =ay_1+by_2}
=\sum_{i,j,h}f_{ijh}\,\varphi(P_{ijh}). $$ -/
theorem exists_iteratedDeriv_presentation_of_exp_factor
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (D : Polynomial (Polynomial ℤ))
    (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j)) :
    ∃ c : ℕ, ∀ (S T a b m : ℕ) (Λ₁ : ℂ) (L d : ℕ)
      (U : Fin T → Fin T → Polynomial (Polynomial ℤ)),
      (∀ j k, ∑ r ∈ (U j k).support, ∑ h ∈ ((U j k).coeff r).support,
          (((U j k).coeff r).coeff h).natAbs ≤ L) →
      (∀ j k r, ((U j k).coeff r).natDegree ≤ d) →
      (∀ j k, (U j k).natDegree ≤ d) →
      (∀ j k : Fin T, Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (U j k) =
        Λ₁ * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) *
          ((a : ℂ) * y₁ + (b : ℂ) * y₂))) →
      ∃ P : Fin S → Fin T → Fin T → Polynomial (Polynomial ℤ),
        (∀ i j k, ∑ r ∈ (P i j k).support, ∑ h ∈ ((P i j k).coeff r).support,
            (((P i j k).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) * L) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S) + d) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S) + d) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ^ (m + S) * Λ₁ *
              iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
                f i j k * z ^ (i : ℕ) *
                  Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
            ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k *
                Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k) := by
  exact exists_iteratedDeriv_presentation_of_exp_factor_main x₁ x₂ y₁ y₂
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁) D E G hE hG

end Diaz
