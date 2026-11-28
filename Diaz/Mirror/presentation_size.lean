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

/-!
# Sizes of integer presentations

The length `len P` of `P ∈ ℤ[X][Y]` (the sum of the absolute values of its coefficients), the
size predicate `Sz P b d` (length at most `b`, degrees at most `d` in `X` and in `Y`), and the
presentations and estimates that `exists_iteratedDeriv_presentation`,
`exists_iteratedDeriv_presentation_of_exp_factor` and `exists_iteratedDeriv_presentation_column`
share: the Leibniz expansion of the derivatives of `z^i e^(βz)`, the polynomial presenting each
of its terms, and the size bounds for sums, products and powers.

From `Diaz/Mirror/exists_iteratedDeriv_presentation.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where these
helpers are repeated in each of the three modules.
-/

@[expose] public section

namespace Diaz

namespace PresentationSize

open Polynomial

/-- The length of `P ∈ ℤ[X][Y]`: the sum of the absolute values of all its integer coefficients. -/
noncomputable def len (P : ℤ[X][X]) : ℕ :=
  ∑ r ∈ P.support, ∑ h ∈ (P.coeff r).support, ((P.coeff r).coeff h).natAbs

lemma len_mul (P Q : ℤ[X][X]) : len (P * Q) ≤ len P * len Q :=
  Transcendence.length_mul_le P Q

lemma len_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) :
    len (∑ i ∈ s, f i) ≤ ∑ i ∈ s, len (f i) :=
  Transcendence.length_sum_le s f

lemma len_add (P Q : ℤ[X][X]) : len (P + Q) ≤ len P + len Q := by
  have h := len_sum (Finset.univ : Finset (Fin 2)) ![P, Q]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  exact h

lemma len_CC (z : ℤ) : len (C (C z)) = z.natAbs := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [Polynomial.C_0, Polynomial.C_0, len, Polynomial.support_zero, Finset.sum_empty,
      Int.natAbs_zero]
  · rw [len, Polynomial.support_C (Polynomial.C_ne_zero.2 hz), Finset.sum_singleton,
      Polynomial.coeff_C_zero, Polynomial.support_C hz, Finset.sum_singleton,
      Polynomial.coeff_C_zero]

/-- `P` has length at most `b`, and degrees at most `d` in `X` and in `Y`. -/
def Sz (P : ℤ[X][X]) (b d : ℕ) : Prop :=
  len P ≤ b ∧ (∀ r, (P.coeff r).natDegree ≤ d) ∧ P.natDegree ≤ d

lemma sz_mono {P : ℤ[X][X]} {b b' d d' : ℕ} (h : Sz P b d) (hb : b ≤ b') (hd : d ≤ d') :
    Sz P b' d' :=
  ⟨h.1.trans hb, fun r => (h.2.1 r).trans hd, h.2.2.trans hd⟩

lemma sz_mul {P Q : ℤ[X][X]} {b₁ b₂ d₁ d₂ : ℕ} (hP : Sz P b₁ d₁) (hQ : Sz Q b₂ d₂) :
    Sz (P * Q) (b₁ * b₂) (d₁ + d₂) := by
  refine ⟨(len_mul P Q).trans (Nat.mul_le_mul hP.1 hQ.1), fun r => ?_,
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP.2.2 hQ.2.2)⟩
  rw [Polynomial.coeff_mul]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ =>
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP.2.1 x.1) (hQ.2.1 x.2))

lemma sz_add {P Q : ℤ[X][X]} {b₁ b₂ d : ℕ} (hP : Sz P b₁ d) (hQ : Sz Q b₂ d) :
    Sz (P + Q) (b₁ + b₂) d := by
  refine ⟨(len_add P Q).trans (Nat.add_le_add hP.1 hQ.1), fun r => ?_,
    (Polynomial.natDegree_add_le P Q).trans (max_le hP.2.2 hQ.2.2)⟩
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP.2.1 r) (hQ.2.1 r))

lemma sz_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X][X]) {b d : ℕ}
    (h : ∀ i ∈ s, Sz (f i) b d) : Sz (∑ i ∈ s, f i) (s.card * b) d := by
  refine ⟨(len_sum s f).trans ?_, fun r => ?_,
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => (h i hi).2.2⟩
  · rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => (h i hi).1
  · rw [Polynomial.finsetSum_coeff]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => (h i hi).2.1 r

lemma sz_CC (z : ℤ) : Sz (C (C z)) z.natAbs 0 := by
  refine ⟨(len_CC z).le, fun r => ?_, (Polynomial.natDegree_C _).le⟩
  rw [Polynomial.coeff_C]
  split_ifs
  · exact (Polynomial.natDegree_C z).le
  · exact Polynomial.natDegree_zero.le

lemma sz_CN (n : ℕ) : Sz (C (C (n : ℤ))) n 0 :=
  sz_CC (n : ℤ)

lemma sz_one : Sz 1 1 0 := by
  have h := sz_CC 1
  rw [Polynomial.C_1, Polynomial.C_1] at h
  exact h

lemma sz_pow {P : ℤ[X][X]} {b d : ℕ} (h : Sz P b d) : ∀ n : ℕ, Sz (P ^ n) (b ^ n) (n * d)
  | 0 => by
    rw [pow_zero, pow_zero, Nat.zero_mul]
    exact sz_one
  | n + 1 => by
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact sz_mul (sz_pow h n) h

lemma sz_exists (P : ℤ[X][X]) : ∃ c, Sz P c c := by
  refine ⟨len P + (∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k).natDegree) + P.natDegree,
    by omega, fun r => ?_, by omega⟩
  by_cases hr : r ≤ P.natDegree
  · have : (P.coeff r).natDegree ≤ ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k).natDegree :=
      Finset.single_le_sum (f := fun k => (P.coeff k).natDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hr))
    omega
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hr), Polynomial.natDegree_zero]
    exact Nat.zero_le _

lemma sz_exists_fam {ι : Type*} [Finite ι] (F : ι → ℤ[X][X]) : ∃ c, ∀ i, Sz (F i) c c := by
  have := Fintype.ofFinite ι
  choose c hc using fun i => sz_exists (F i)
  have hle : ∀ i, c i ≤ ∑ i', c i' := fun i =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact ⟨∑ i, c i, fun i => sz_mono (hc i) (hle i) (hle i)⟩

lemma succ_le_two_pow : ∀ m : ℕ, m + 1 ≤ 2 ^ m
  | 0 => le_rfl
  | m + 1 => by
    have := succ_le_two_pow m
    rw [pow_succ]
    omega

lemma phi_CC (φ : ℤ[X][X] →+* ℂ) (z : ℤ) : φ (C (C z)) = (z : ℂ) :=
  eq_intCast (φ.comp ((C : ℤ[X] →+* ℤ[X][X]).comp (C : ℤ →+* ℤ[X]))) z

/-- If `u φ(D) = φ(U)` and `v φ(D) = φ(V)`, then `(p u + q v) φ(D) = φ(p U + q V)`. -/
lemma lin_eval (φ : ℤ[X][X] →+* ℂ) {u v : ℂ} {Dp U V : ℤ[X][X]} (hU : u * φ Dp = φ U)
    (hV : v * φ Dp = φ V) (p q : ℕ) :
    ((p : ℂ) * u + (q : ℂ) * v) * φ Dp = φ (C (C (p : ℤ)) * U + C (C (q : ℤ)) * V) := by
  rw [map_add φ, map_mul φ, map_mul φ, phi_CC φ, phi_CC φ, ← hU, ← hV, Int.cast_natCast,
    Int.cast_natCast]
  ring

/-- With `r` the coordinates of `Lⁿ αⁿ` in the basis `1, α, …, α^(ℓ-1)` and `φ(H) = α φ(D)`, this
integer polynomial takes the value `φ(D)^(ℓ-1) Lⁿ αⁿ`. -/
noncomputable def expPres (ℓ : ℕ) (r : ℕ → ℤ) (Hp Dp : ℤ[X][X]) : ℤ[X][X] :=
  ∑ t ∈ Finset.range ℓ, C (C (r t)) * Hp ^ t * Dp ^ (ℓ - 1 - t)

lemma expPres_eval (φ : ℤ[X][X] →+* ℂ) (ℓ : ℕ) (r : ℕ → ℤ) (Hp Dp : ℤ[X][X]) {α : ℂ}
    (hH : α * φ Dp = φ Hp) :
    φ (expPres ℓ r Hp Dp) = φ Dp ^ (ℓ - 1) * ∑ t ∈ Finset.range ℓ, (r t : ℂ) * α ^ t := by
  rw [expPres, map_sum φ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have hsplit : φ Dp ^ (ℓ - 1) = φ Dp ^ t * φ Dp ^ (ℓ - 1 - t) := by
    rw [← pow_add]
    congr 1
    omega
  rw [map_mul φ, map_mul φ, map_pow φ, map_pow φ, ← hH, phi_CC φ, hsplit, mul_pow]
  ring

lemma sz_expPres (ℓ : ℕ) (r : ℕ → ℤ) {Hp Dp : ℤ[X][X]} {c R : ℕ} (hH : Sz Hp c c)
    (hD : Sz Dp c c) (hr : ∀ t, (r t).natAbs ≤ R) :
    Sz (expPres ℓ r Hp Dp) (ℓ * (R * c ^ (ℓ - 1))) ((ℓ - 1) * c) := by
  have h : Sz (expPres ℓ r Hp Dp) ((Finset.range ℓ).card * (R * c ^ (ℓ - 1))) ((ℓ - 1) * c) :=
    sz_sum (Finset.range ℓ) _ fun t ht => by
      have ht' := Finset.mem_range.1 ht
      have he : t + (ℓ - 1 - t) = ℓ - 1 := by omega
      refine sz_mono (sz_mul (sz_mul (sz_CC (r t)) (sz_pow hH t)) (sz_pow hD (ℓ - 1 - t))) ?_ ?_
      · rw [Nat.mul_assoc, ← pow_add, he]
        exact Nat.mul_le_mul_right _ (hr t)
      · rw [Nat.zero_add, ← Nat.add_mul, he]
  rw [Finset.card_range] at h
  exact h

/-- `φ(D)^(ℓ-1) L^N αⁿ` as an integer polynomial, for `n ≤ N`. -/
noncomputable def fac (ℓ : ℕ) (r : ℕ → ℕ → ℤ) (Lc : ℤ) (Hp Dp : ℤ[X][X]) (N n : ℕ) : ℤ[X][X] :=
  C (C (Lc ^ (N - n))) * expPres ℓ (r n) Hp Dp

lemma fac_eval (φ : ℤ[X][X] →+* ℂ) (ℓ : ℕ) (r : ℕ → ℕ → ℤ) (Lc : ℤ) (Hp Dp : ℤ[X][X]) {α : ℂ}
    (hH : α * φ Dp = φ Hp)
    (hr : ∀ n, (Lc : ℂ) ^ n * α ^ n = ∑ t ∈ Finset.range ℓ, (r n t : ℂ) * α ^ t)
    {N n : ℕ} (hn : n ≤ N) :
    φ (fac ℓ r Lc Hp Dp N n) = φ Dp ^ (ℓ - 1) * (Lc : ℂ) ^ N * α ^ n := by
  rw [fac, map_mul φ, phi_CC φ, expPres_eval φ ℓ (r n) Hp Dp hH, ← hr n, Int.cast_pow]
  have hsplit : (Lc : ℂ) ^ N = (Lc : ℂ) ^ (N - n) * (Lc : ℂ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  ring

lemma exp_split (x₁ x₂ y₁ y₂ : ℂ) (a b j k : ℕ) :
    Complex.exp (((j : ℂ) * x₁ + (k : ℂ) * x₂) * ((a : ℂ) * y₁ + (b : ℂ) * y₂)) =
      Complex.exp (![x₁, x₂] 0 * ![y₁, y₂] 0) ^ (j * a) *
        Complex.exp (![x₁, x₂] 0 * ![y₁, y₂] 1) ^ (j * b) *
        Complex.exp (![x₁, x₂] 1 * ![y₁, y₂] 0) ^ (k * a) *
        Complex.exp (![x₁, x₂] 1 * ![y₁, y₂] 1) ^ (k * b) := by
  change _ = Complex.exp (x₁ * y₁) ^ (j * a) * Complex.exp (x₁ * y₂) ^ (j * b) *
    Complex.exp (x₂ * y₁) ^ (k * a) * Complex.exp (x₂ * y₂) ^ (k * b)
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_mul_le_pow {x y : ℂ} {C : ℝ} {p q : ℕ} (hx : ‖x‖ ≤ C ^ p) (hy : ‖y‖ ≤ C ^ q) :
    ‖x * y‖ ≤ C ^ (p + q) := by
  rw [norm_mul, pow_add]
  exact mul_le_mul hx hy (norm_nonneg y) ((norm_nonneg x).trans hx)

lemma norm_pow_le_pow {x : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (n : ℕ) : ‖x ^ n‖ ≤ C ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg x) hx n

/-- Leibniz's rule for the exponential polynomial, linearly in its coefficients. -/
lemma iteratedDeriv_expPoly (S T m : ℕ) (x₁ x₂ : ℂ) (f : Fin S → Fin T → Fin T → ℂ) (w : ℂ) :
    iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
        f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z)) w =
      ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, f i j k *
        ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) *
          (((i : ℕ).descFactorial l : ℂ) * w ^ ((i : ℕ) - l)) *
          ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) ^ (m - l) *
            Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * w)) := by
  have key : ∀ (i : Fin S) (j k : Fin T), iteratedDeriv m (fun z : ℂ =>
      f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z)) w =
      f i j k * ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) *
        (((i : ℕ).descFactorial l : ℂ) * w ^ ((i : ℕ) - l)) *
          ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) ^ (m - l) *
            Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * w)) := by
    intro i j k
    have h1 : ContDiffAt ℂ m (fun z : ℂ => z ^ (i : ℕ)) w := (contDiff_id.pow _).contDiffAt
    have h2 : ContDiffAt ℂ m (fun z : ℂ =>
        Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z)) w := by fun_prop
    simp_rw [mul_assoc (f i j k)]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul h1 h2]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [iteratedDeriv_pow, iteratedDeriv_cexp_const_mul]
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_fun_sum (fun j _ => by fun_prop)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDeriv_fun_sum (fun k _ => by fun_prop)]
  exact Finset.sum_congr rfl fun k _ => key i j k

/-- The integer polynomial `∑_{l ≤ m} C(m,l) i(i-1)⋯(i-l+1) D^l B^(m-l) Z^(i-l) D^(S-i+l) e`. -/
noncomputable def pres (Dp Bp Zp ep : ℤ[X][X]) (S m i : ℕ) : ℤ[X][X] :=
  ∑ l ∈ Finset.range (m + 1), C (C ((m.choose l * i.descFactorial l : ℕ) : ℤ)) *
    (Dp ^ l * Bp ^ (m - l) * Zp ^ (i - l) * Dp ^ (S - i + l)) * ep

lemma pres_eval (φ : ℤ[X][X] →+* ℂ) {Dp Bp Zp ep : ℤ[X][X]} {β ζ Λ' e : ℂ}
    (hB : β * φ Dp = φ Bp) (hZ : ζ * φ Dp = φ Zp) (he : φ ep = Λ' * e) {S m i : ℕ} (hi : i < S) :
    φ (pres Dp Bp Zp ep S m i) = φ Dp ^ (m + S) * Λ' *
      ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * ((i.descFactorial l : ℂ) * ζ ^ (i - l)) *
        (β ^ (m - l) * e) := by
  rw [pres, map_sum φ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  simp only [map_mul φ, map_pow φ]
  rw [← hB, ← hZ, he, phi_CC φ, Int.cast_natCast, Nat.cast_mul]
  rcases Nat.lt_or_ge i l with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h, Nat.cast_zero]
    ring
  · have hδ : φ Dp ^ (m + S) =
        φ Dp ^ l * φ Dp ^ (m - l) * φ Dp ^ (i - l) * φ Dp ^ (S - i + l) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [hδ, mul_pow, mul_pow]
    ring

end PresentationSize

end Diaz
