/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Diaz.Mirror.exists_int_pow_repr
public import Diaz.Mirror.length_mul_le
public import Diaz.Mirror.length_sum_le
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Diaz.Mirror.presentation_size
public import Diaz.Mirror.exists_iteratedDeriv_presentation_of_exp_factor

/-!
# Integer presentations of the derivatives of the auxiliary exponential polynomial

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `δ = φ(D)`, `β = j x₁ + k x₂` and `ζ = a y₁ + b y₂`.

The Leibniz expansion of the derivatives and the presentation of each of its terms are
`exists_iteratedDeriv_presentation_of_exp_factor`, which needs only a presented exponential factor.

* **Exponential factor.** `e^(βζ) = α₀₀^(ja) α₀₁^(jb) α₁₀^(ka) α₁₁^(kb)` with `α_{pq} = e^(x_p y_q)`
  algebraic. For each `α_{pq}` there are `ℓ`, `A` and an integer `L ≠ 0` with
  `Lⁿ αⁿ = ∑_{t<ℓ} r_t α^t` and `|r_t| ≤ Aⁿ`. As `δα = φ(H)`, the number
  `δ^(ℓ-1) L^N αⁿ = L^(N-n) ∑_t r_t (δα)^t δ^(ℓ-1-t)` (for `n ≤ N`) is `φ` of an integer polynomial
  of length at most `|L|^(N-n) ℓ Aⁿ c^(ℓ-1)` and degrees at most `(ℓ-1) c`, where `c` bounds the
  data. With `N = T(a+b)` the four factors present `Λ' e^(βζ)`, `Λ' = ∏ δ^(ℓ_{pq}-1) L_{pq}^N`,
  and `Λ = δ^(m+S) Λ'`.
* **Sizes.** The factor has length at most `W^(4(N+1))` and degrees at most `4W`, with `W`
  depending only on the data, which gives the bounds of the statement.

From `Diaz/Mirror/exists_iteratedDeriv_presentation.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.exists_iteratedDeriv_presentation`. The accepted proof
repeats the Leibniz expansion; here it is shared with the column case.
-/

@[expose] public section

namespace Diaz

namespace ExistsIteratedDerivPresentation

open Polynomial PresentationSize

/-! ### Length and size of integer polynomials in two variables -/

lemma exists_bound_fin2 (w : Fin 2 → Fin 2 → ℕ) : ∃ W, ∀ p q, w p q ≤ W :=
  ⟨∑ p, ∑ q, w p q, fun p q =>
    (Finset.single_le_sum (f := fun q' => w p q') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p' => ∑ q', w p' q') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ p))⟩

/-! ### Values of integer polynomials -/

/-! ### The four exponential factors -/

lemma sz_fac (ℓ : ℕ) (r : ℕ → ℕ → ℤ) (Lc : ℤ) {Hp Dp : ℤ[X][X]} {c A W : ℕ}
    (hH : Sz Hp c c) (hD : Sz Dp c c) (hr : ∀ n t, (r n t).natAbs ≤ A ^ n)
    (hW : ℓ * c ^ (ℓ - 1) ≤ W ∧ (ℓ - 1) * c ≤ W ∧ Lc.natAbs ≤ W ∧ A ≤ W) {N n : ℕ}
    (hn : n ≤ N) : Sz (fac ℓ r Lc Hp Dp N n) (W ^ (N + 1)) W := by
  refine sz_mono (sz_mul (sz_CC _) (sz_expPres ℓ (r n) hH hD (hr n))) ?_
    ((Nat.zero_add _).trans_le hW.2.1)
  rw [Int.natAbs_pow]
  calc Lc.natAbs ^ (N - n) * (ℓ * (A ^ n * c ^ (ℓ - 1)))
      = Lc.natAbs ^ (N - n) * A ^ n * (ℓ * c ^ (ℓ - 1)) := by ring
    _ ≤ W ^ (N - n) * W ^ n * W :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hW.2.2.1 _)
        (Nat.pow_le_pow_left hW.2.2.2 _)) hW.1
    _ = W ^ (N + 1) := by rw [← pow_add, Nat.sub_add_cancel hn, pow_succ]

/-- The product of the four factors, presenting `Λ' e^((j x₁ + k x₂)(a y₁ + b y₂))`. -/
noncomputable def epart (ℓ : Fin 2 → Fin 2 → ℕ) (r : Fin 2 → Fin 2 → ℕ → ℕ → ℤ)
    (L : Fin 2 → Fin 2 → ℤ) (H : Fin 2 → Fin 2 → ℤ[X][X]) (Dp : ℤ[X][X]) (N a b j k : ℕ) :
    ℤ[X][X] :=
  fac (ℓ 0 0) (r 0 0) (L 0 0) (H 0 0) Dp N (j * a) *
    fac (ℓ 0 1) (r 0 1) (L 0 1) (H 0 1) Dp N (j * b) *
    fac (ℓ 1 0) (r 1 0) (L 1 0) (H 1 0) Dp N (k * a) *
    fac (ℓ 1 1) (r 1 1) (L 1 1) (H 1 1) Dp N (k * b)

/-- The constant `Λ' = ∏_{p,q} δ^(ℓ_{pq}-1) L_{pq}^N`. -/
noncomputable def existsIteratedDerivPresentationLam (δ : ℂ) (ℓ : Fin 2 → Fin 2 → ℕ) (L : Fin 2 →
    Fin 2 → ℤ) (N : ℕ) : ℂ :=
  δ ^ (ℓ 0 0 - 1) * (L 0 0 : ℂ) ^ N * (δ ^ (ℓ 0 1 - 1) * (L 0 1 : ℂ) ^ N) *
    (δ ^ (ℓ 1 0 - 1) * (L 1 0 : ℂ) ^ N) * (δ ^ (ℓ 1 1 - 1) * (L 1 1 : ℂ) ^ N)

lemma epart_eval (φ : ℤ[X][X] →+* ℂ) (x₁ x₂ y₁ y₂ : ℂ) (ℓ : Fin 2 → Fin 2 → ℕ)
    (r : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (L : Fin 2 → Fin 2 → ℤ) (H : Fin 2 → Fin 2 → ℤ[X][X])
    (Dp : ℤ[X][X]) (hH : ∀ p q, Complex.exp (![x₁, x₂] p * ![y₁, y₂] q) * φ Dp = φ (H p q))
    (hr : ∀ p q n, (L p q : ℂ) ^ n * Complex.exp (![x₁, x₂] p * ![y₁, y₂] q) ^ n =
      ∑ t ∈ Finset.range (ℓ p q), (r p q n t : ℂ) * Complex.exp (![x₁, x₂] p * ![y₁, y₂] q) ^ t)
    {N a b j k : ℕ} (h1 : j * a ≤ N) (h2 : j * b ≤ N) (h3 : k * a ≤ N) (h4 : k * b ≤ N) :
    φ (epart ℓ r L H Dp N a b j k) = existsIteratedDerivPresentationLam (φ Dp) ℓ L N *
      Complex.exp (((j : ℂ) * x₁ + (k : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) := by
  rw [epart, map_mul φ, map_mul φ, map_mul φ,
    fac_eval φ _ _ _ _ _ (hH 0 0) (hr 0 0) h1, fac_eval φ _ _ _ _ _ (hH 0 1) (hr 0 1) h2,
    fac_eval φ _ _ _ _ _ (hH 1 0) (hr 1 0) h3, fac_eval φ _ _ _ _ _ (hH 1 1) (hr 1 1) h4,
    exp_split x₁ x₂ y₁ y₂ a b j k, existsIteratedDerivPresentationLam]
  ring

lemma sz_epart (ℓ : Fin 2 → Fin 2 → ℕ) (r : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (L : Fin 2 → Fin 2 → ℤ)
    (A : Fin 2 → Fin 2 → ℕ) {H : Fin 2 → Fin 2 → ℤ[X][X]} {Dp : ℤ[X][X]} {c W : ℕ}
    (hH : ∀ p q, Sz (H p q) c c) (hD : Sz Dp c c)
    (hr : ∀ p q n t, (r p q n t).natAbs ≤ A p q ^ n)
    (hW : ∀ p q, ℓ p q * c ^ (ℓ p q - 1) ≤ W ∧ (ℓ p q - 1) * c ≤ W ∧ (L p q).natAbs ≤ W ∧
      A p q ≤ W)
    {N a b j k : ℕ} (h1 : j * a ≤ N) (h2 : j * b ≤ N) (h3 : k * a ≤ N) (h4 : k * b ≤ N) :
    Sz (epart ℓ r L H Dp N a b j k) (W ^ (4 * (N + 1))) (4 * W) := by
  have hf : ∀ p q n, n ≤ N → Sz (fac (ℓ p q) (r p q) (L p q) (H p q) Dp N n) (W ^ (N + 1)) W :=
    fun p q n hn => sz_fac (ℓ p q) (r p q) (L p q) (hH p q) hD (hr p q) (hW p q) hn
  exact sz_mono (sz_mul (sz_mul (sz_mul (hf 0 0 _ h1) (hf 0 1 _ h2)) (hf 1 0 _ h3)) (hf 1 1 _ h4))
    (le_of_eq (by ring)) (by omega)

lemma lam_ne_zero {δ : ℂ} (hδ : δ ≠ 0) (ℓ : Fin 2 → Fin 2 → ℕ) {L : Fin 2 → Fin 2 → ℤ}
    (hL : ∀ p q, L p q ≠ 0) (N : ℕ) : existsIteratedDerivPresentationLam δ ℓ L N ≠ 0 := by
  have hf : ∀ p q, δ ^ (ℓ p q - 1) * (L p q : ℂ) ^ N ≠ 0 := fun p q =>
    mul_ne_zero (pow_ne_zero _ hδ) (pow_ne_zero _ (Int.cast_ne_zero.2 (hL p q)))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hf 0 0) (hf 0 1)) (hf 1 0)) (hf 1 1)

lemma norm_lam_le {δ : ℂ} {C : ℝ} (hδ : ‖δ‖ ≤ C) (ℓ : Fin 2 → Fin 2 → ℕ)
    {L : Fin 2 → Fin 2 → ℤ} (hL : ∀ p q, ‖(L p q : ℂ)‖ ≤ C) (N : ℕ) :
    ‖existsIteratedDerivPresentationLam δ ℓ L N‖ ≤
      C ^ (ℓ 0 0 - 1 + N + (ℓ 0 1 - 1 + N) + (ℓ 1 0 - 1 + N) + (ℓ 1 1 - 1 + N)) := by
  have hf : ∀ p q, ‖δ ^ (ℓ p q - 1) * (L p q : ℂ) ^ N‖ ≤ C ^ (ℓ p q - 1 + N) := fun p q =>
    norm_mul_le_pow (norm_pow_le_pow hδ _) (norm_pow_le_pow (hL p q) N)
  exact norm_mul_le_pow (norm_mul_le_pow (norm_mul_le_pow (hf 0 0) (hf 0 1)) (hf 1 0)) (hf 1 1)

end ExistsIteratedDerivPresentation

open ExistsIteratedDerivPresentation PresentationSize

/-- **Derivatives at a grid point, presented.** Let $x_1,x_2,y_1,y_2\in\mathbb{C}$ with every
$e^{x_iy_j}$ algebraic. Let $\omega,\omega_1\in\mathbb{C}$, let $\varphi$ be evaluation at
$(\omega,\omega_1)$, and let $D,E_i,G_j,H_{ij}\in\mathbb{Z}[X][Y]$ with $\varphi(D)\neq0$,
$x_i\varphi(D)=\varphi(E_i)$, $y_j\varphi(D)=\varphi(G_j)$ and
$e^{x_iy_j}\varphi(D)=\varphi(H_{ij})$. There is $c\in\mathbb{N}$ such that for all
$S,T,a,b,m\in\mathbb{N}$ there are $\Lambda\in\mathbb{C}$, $\Lambda\neq0$, with $|\Lambda|\le
c^{\,c(1+m+S+T(a+b))}$, and $P_{ijh}\in\mathbb{Z}[X][Y]$ ($i<S$, $j,h<T$) of degree at most
$c(1+m+S)$ in $X$ and in $Y$ and of length at most
$$ c^{\,c(1+m+S+T(a+b))}\,(1+m+S+T+a+b)^{c(1+m+S)}, $$
such that for all $f_{ijh}\in\mathbb{C}$
$$ \Lambda \cdot\frac{d^{m}}{dz^{m}}\Bigl(\sum_{i,j,h}f_{ijh}\,z^{i}e^{(jx_1+hx_2)z}\Bigr) \Big|_{z
=ay_1+by_2} =\sum_{i,j,h}f_{ijh}\,\varphi(P_{ijh}). $$ -/
theorem exists_iteratedDeriv_presentation
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (ω ω₁ : ℂ) (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0)
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) *
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ c : ℕ, ∀ S T a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧ ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ P : Fin S → Fin T → Fin T → Polynomial (Polynomial ℤ),
        (∀ i j k, ∑ r ∈ (P i j k).support, ∑ h ∈ ((P i j k).coeff r).support,
            (((P i j k).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S)) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S)) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
            f i j k * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k)
                := by
  -- the shared node, and `φ` as a ring homomorphism
  obtain ⟨c₁, hSH⟩ :=
    exists_iteratedDeriv_presentation_of_exp_factor x₁ x₂ y₁ y₂ ω ω₁ D E G hE hG
  obtain ⟨φ, hφ⟩ : ∃ φ : Polynomial (Polynomial ℤ) →+* ℂ, ∀ P,
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ P = φ P :=
    ⟨Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁, fun _ => rfl⟩
  simp only [hφ] at hD hH hSH ⊢
  -- integer relations for the powers of the four algebraic exponentials
  choose ℓ A Lc hLc hr using fun p q : Fin 2 => Transcendence.exists_int_pow_repr
    (α := Complex.exp (![x₁, x₂] p * ![y₁, y₂] q)) (hexp p q)
  choose r hr1 hr2 using hr
  -- a common size `c₀` for `D` and `H`, and the constants of the four factors
  obtain ⟨cD, hcD⟩ := sz_exists D
  obtain ⟨cH, hcH⟩ := sz_exists_fam (fun pq : Fin 2 × Fin 2 => H pq.1 pq.2)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = cD + cH + 1 := ⟨_, rfl⟩
  have hD0 : Sz D c₀ c₀ := sz_mono hcD (by omega) (by omega)
  have hH0 : ∀ p q, Sz (H p q) c₀ c₀ := fun p q => sz_mono (hcH (p, q)) (by omega) (by omega)
  obtain ⟨W, hW⟩ := exists_bound_fin2 fun p q =>
    ℓ p q * c₀ ^ (ℓ p q - 1) + (ℓ p q - 1) * c₀ + (Lc p q).natAbs + A p q + ℓ p q
  have hW' : ∀ p q, ℓ p q * c₀ ^ (ℓ p q - 1) ≤ W ∧ (ℓ p q - 1) * c₀ ≤ W ∧
      (Lc p q).natAbs ≤ W ∧ A p q ≤ W ∧ ℓ p q ≤ W := fun p q => by
    have h : ℓ p q * c₀ ^ (ℓ p q - 1) + (ℓ p q - 1) * c₀ + (Lc p q).natAbs + A p q + ℓ p q ≤ W :=
      hW p q
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨CL, hCL⟩ := exists_bound_fin2 fun p q => ⌈‖(Lc p q : ℂ)‖⌉₊
  obtain ⟨c, hc⟩ : ∃ c, c = c₁ + 4 * (W + c₀ + CL + ⌈‖φ D‖⌉₊ + 1) := ⟨_, rfl⟩
  refine ⟨c, fun S T a b m => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = T * (a + b) := ⟨_, rfl⟩
  rw [← hN]
  have hja : ∀ j : Fin T, (j : ℕ) * a ≤ N := fun j => by
    rw [hN]
    exact (Nat.mul_le_mul_right a j.2.le).trans (Nat.mul_le_mul_left T (Nat.le_add_right a b))
  have hjb : ∀ j : Fin T, (j : ℕ) * b ≤ N := fun j => by
    rw [hN]
    exact (Nat.mul_le_mul_right b j.2.le).trans (Nat.mul_le_mul_left T (Nat.le_add_left b a))
  -- the exponential factor, presented
  have hszU : ∀ j k : Fin T, Sz (epart ℓ r Lc H D N a b j k) (W ^ (4 * (N + 1))) (4 * W) :=
    fun j k => sz_epart ℓ r Lc A hH0 hD0 hr2
      (fun p q => ⟨(hW' p q).1, (hW' p q).2.1, (hW' p q).2.2.1, (hW' p q).2.2.2.1⟩)
      (hja j) (hjb j) (hja k) (hjb k)
  obtain ⟨P, hPl, hPx, hPy, hPid⟩ :=
    hSH S T a b m (existsIteratedDerivPresentationLam (φ D) ℓ Lc N) _ _
      (fun j k => epart ℓ r Lc H D N a b j k) (fun j k => (hszU j k).1)
      (fun j k => (hszU j k).2.1) (fun j k => (hszU j k).2.2)
      (fun j k => epart_eval φ x₁ x₂ y₁ y₂ ℓ r Lc H D hH hr1 (hja j) (hjb j) (hja k) (hjb k))
  have hdeg : c₁ * (1 + m + S) + 4 * W ≤ c * (1 + m + S) := by
    have e2 : (c₁ + 4 * W) * (1 + m + S) ≤ c * (1 + m + S) := Nat.mul_le_mul_right _ (by omega)
    have e3 : (c₁ + 4 * W) * (1 + m + S) = c₁ * (1 + m + S) + 4 * W * (1 + m + S) := by ring
    have e4 : 4 * W ≤ 4 * W * (1 + m + S) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  refine ⟨φ D ^ (m + S) * existsIteratedDerivPresentationLam (φ D) ℓ Lc N,
    mul_ne_zero (pow_ne_zero _ hD) (lam_ne_zero hD ℓ hLc N), ?_, P, fun i j k => ?_,
    fun i j k r' => (hPx i j k r').trans hdeg, fun i j k => (hPy i j k).trans hdeg, hPid⟩
  · -- the size of `Λ`
    have h1 : (1 : ℝ) ≤ c := Nat.one_le_cast.2 (by omega)
    have hδc : ‖φ D‖ ≤ (c : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 (by omega))
    have hLc' : ∀ p q, ‖(Lc p q : ℂ)‖ ≤ (c : ℝ) := fun p q =>
      (Nat.le_ceil _).trans (Nat.cast_le.2 ((hCL p q).trans (by omega)))
    refine (norm_mul_le_pow (norm_pow_le_pow hδc (m + S)) (norm_lam_le hδc ℓ hLc' N)).trans
      (pow_le_pow_right₀ h1 ?_)
    have e1 : c * (1 + m + S + N) = c + c * (m + S + N) := by ring
    have e2 : 4 * (m + S + N) ≤ c * (m + S + N) := Nat.mul_le_mul_right _ (by omega)
    have := (hW' 0 0).2.2.2.2
    have := (hW' 0 1).2.2.2.2
    have := (hW' 1 0).2.2.2.2
    have := (hW' 1 1).2.2.2.2
    omega
  · -- the length of `P_{ijk}`
    have hc1 : 1 ≤ c := by omega
    have hY : 1 ≤ 1 + m + S + T + a + b := by omega
    have hexp' : c₁ * (1 + m + S) + 4 * (N + 1) ≤ c * (1 + m + S + N) := by
      have f1 : c * (1 + m + S + N) = c * (1 + m + S) + c * N := by ring
      have f2 : (c₁ + 4) * (1 + m + S) ≤ c * (1 + m + S) := Nat.mul_le_mul_right _ (by omega)
      have f3 : (c₁ + 4) * (1 + m + S) = c₁ * (1 + m + S) + 4 * (1 + m + S) := by ring
      have f4 : 4 * N ≤ c * N := Nat.mul_le_mul_right _ (by omega)
      omega
    calc len (P i j k)
        ≤ c₁ ^ (c₁ * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c₁ * (1 + m + S)) *
            W ^ (4 * (N + 1)) := hPl i j k
      _ ≤ c ^ (c₁ * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) *
            c ^ (4 * (N + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
            (Nat.pow_le_pow_right hY (Nat.mul_le_mul_right _ (by omega))))
            (Nat.pow_le_pow_left (by omega) _)
      _ = c ^ (c₁ * (1 + m + S) + 4 * (N + 1)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) := by
          rw [pow_add]; ring
      _ ≤ c ^ (c * (1 + m + S + N)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hc1 hexp')

end Diaz
