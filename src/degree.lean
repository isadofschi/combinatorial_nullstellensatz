/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.variables
import algebra.algebra.basic
import data.mv_polynomial.comm_ring
import data.nat.basic

universes u v

variables {α : Type v}

open set function finsupp add_monoid_algebra


open_locale big_operators 

-- check https://github.com/leanprover-community/flt-regular/blob/master/src/ring_theory/polynomial/homogenization.lean
-- and https://github.com/leanprover-community/mathlib/pull/10429/files for useful lemmas

namespace multiset

lemma count_sup' {α : Type*} [decidable_eq α] (x : α) (s t : multiset α) :
count x (s ⊔ t) = max (count x s) (count x t) := by simp

end multiset


namespace mv_polynomial 

variables {R : Type*} {σ : Type*} 

/-

  Basic: support, coeff, etc

-/

local attribute [instance] classical.prop_decidable

lemma support_sum [comm_semiring R]{ α : Type}{s : finset α}
  {f : α → mv_polynomial σ R} {m : σ →₀ ℕ} (h : m ∈ (∑ x in s, f x).support) :
  ∃ x ∈ s, m ∈ (f x).support :=
begin
  revert h,
  apply finset.cons_induction_on s,
  intro h,
  exfalso,
  simpa using h,
  intros a s a_notin_s h h',
  rw finset.sum_cons at h',
  cases (@finset.mem_union _ _ m (f a).support  (s.sum f).support).1 (finset.mem_of_subset _ h')
  with h1 h2,
  use a,
  apply and.intro,
  simp only [finset.mem_insert, finset.cons_eq_insert],
  left,
  refl,
  exact h1,
  have t := h h2,
  cases t with x hx,
  cases hx with hx1 hx2,
  use x,
  apply and.intro,
  simp only [finset.mem_insert, finset.cons_eq_insert],
  right,
  exact hx1,
  exact hx2,
  convert @support_add R σ _ (f a) (s.sum f),
end

lemma mem_support_iff_nonzero_coeff [comm_semiring R] -- do we really need this? Do we already have this?
(p : mv_polynomial σ R) (m : σ →₀ ℕ): m ∈ p.support ↔ coeff m p ≠ 0 := by simp

lemma support_sub {R : Type*}{n : ℕ}[comm_ring R]
(p q : mv_polynomial σ R): 
(p - q).support ⊆ p.support ∪ q.support := 
begin
  rw [sub_eq_add_neg, ← @support_neg R σ _ q],
  convert @support_add R σ _ p (-q),
end

-- Compare with https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L1129
lemma support_mul' {R : Type*}[comm_ring R]
 {f g : mv_polynomial σ R}{m : σ →₀ ℕ}(m ∈ (f * g).support):
 ∃ m' m'', m' ∈ f.support ∧ m'' ∈ g.support ∧ m = m' + m'' :=
begin
  sorry -- use support_mul
end 

-- requiring field here seems too strong, we only need 1 ≠ 0 in R
lemma X_ne_zero {R σ : Type*} [field R] (j : σ) : (X j : mv_polynomial σ R) ≠ 0
:= begin
  rw ne_zero_iff,
  use single j 1,
  simp,
end

/-

  Degree: degree_of, total_degree
  
-/

lemma degree_of_eq_sup { n : ℕ } {F : Type u} [field F] 
(j : fin n) (f : mv_polynomial (fin n) F) (d : ℕ):
degree_of j f = f.support.sup (λ m , m j) :=
begin
  sorry
end

lemma degree_of_lt_iff { n : ℕ } {F : Type u} [field F]  {j : fin n} {f : mv_polynomial (fin n) F}
 {d : ℕ} (h : 0 < d):  degree_of j f < d ↔ ∀ m : fin n →₀ ℕ, m ∈ f.support → m j < d :=
begin
  rw degree_of_eq_sup j f d,
  rwa finset.sup_lt_iff,
end

lemma degree_of_C {σ : Type*} {R : Type*} [comm_semiring R] (a : R) (x : σ): 
  degree_of x (C a : mv_polynomial σ R) = 0 := by simp [degree_of, degrees_C]

lemma degree_of_add_le {σ : Type*} {R : Type*} [comm_semiring R]
 (x : σ) (f g : mv_polynomial σ R): 
 degree_of x (f + g) ≤ max (degree_of x f) (degree_of x g) := 
begin
  repeat {rw degree_of},
  apply (multiset.count_le_of_le x (degrees_add f g)).trans,
  rw multiset.count_sup',
end

lemma degree_of_sub_aux {σ : Type*} {R : Type*} [comm_ring R]
  (x : σ) (f g : mv_polynomial σ R) (k : ℕ)
  (h1 : ∀ (m : σ →₀ ℕ), m ∈ f.support → (k ≤ m x) → coeff m f = coeff m g) 
  (h2 : ∀ (m : σ →₀ ℕ), m ∈ g.support → (k ≤ m x) → coeff m f = coeff m g) : 
  degree_of x (f - g) < k := 
begin
   sorry
end

lemma monomial_le_degree_of {σ : Type*} {R : Type*} [comm_ring R]
  (i : σ) {f : mv_polynomial σ R}
  {m : σ →₀ ℕ} (h_m : m ∈ f.support) :
  m i ≤ degree_of i f :=
begin
  sorry
end

lemma degree_of_mul_X_ne  {σ : Type*} {R : Type*} [comm_ring R]
  {i j : σ} (f : mv_polynomial σ R) (h : i ≠ j) :
  degree_of i (f * X j)  = degree_of i f := sorry

/- in the following we have equality iff f ≠ 0 -/
lemma degree_of_mul_X_eq  {σ : Type*} {R : Type*} [comm_ring R]
  (j : σ) (f : mv_polynomial σ R) :
  degree_of j (f * X j)  ≤ degree_of j f + 1 := 
begin
  sorry,
end

-- This is https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L774
lemma total_degree_mul' { n : ℕ } {F : Type u} [field F] {f g : mv_polynomial (fin n) F} (hf : f ≠ 0) (hg : g ≠ 0):
total_degree (f * g) = total_degree f + total_degree g :=
begin
  sorry
end

lemma total_degree_add_monomial  { n : ℕ } {F : Type u} [field F] (f : mv_polynomial (fin n) F) 
(a : fin n →₀ ℕ) (b : F) (h : a ∉ f.support) (h_b: b ≠ 0) :
total_degree (single a b + f) = linear_order.max (total_degree (single a b)) (total_degree f) :=
begin
  sorry
end

lemma total_degree_mul_X_le  { n : ℕ } {F : Type u} [field F] 
(f : mv_polynomial (fin n) F)(j : fin n) :
total_degree (f * X j) ≤ total_degree f + 1 := 
begin
  apply (total_degree_mul f (X j)).trans,
  simp,
end

lemma total_degree_mul_X { n : ℕ } {F : Type u} [field F] {f : mv_polynomial (fin n) F} (h : f ≠ 0)
  (j : fin n) : total_degree (f * X j) = total_degree f + 1 :=
  by simp [total_degree_mul' h (X_ne_zero j)]

lemma total_degree_sum {σ : Type*} {R : Type*} [comm_semiring R]
(s : finset α) (p : α → mv_polynomial σ R) :
total_degree (∑ i : α in s, p i) ≤ s.sup (λ i , total_degree(p i))
:= sorry

/- 
  
  New definitions: monomial_degree, max_degree_monomial, dominant_monomial

-/

-- Generalize more!

/-
def max : multiset ℕ  → ℕ :=
multiset.foldr (max) (λ x y z, by simp [max_left_comm]) 0
-/

def monomial_degree {s : Type} (t : s →₀ ℕ) : ℕ := t.sum (λ _ e, e) --∑ i in t.support, t i

lemma le_monomial_degree  {s : Type} (t : s →₀ ℕ) (j : s) : t j ≤ monomial_degree t :=
begin
  sorry
end

lemma monomial_degree_sub  {σ : Type*} {m m' :  σ →₀ ℕ} (h : m' ≤ m) : 
  monomial_degree (m-m') = monomial_degree m - monomial_degree m' := 
begin
  sorry
end

lemma total_degree_monomial_eq_monomial_degree  {σ R : Type*}[comm_semiring R] {m :  σ →₀ ℕ} {a : R} (h : a ≠ 0):
total_degree (monomial m a) = monomial_degree m :=
begin
  -- TODO: this proof was taken from flt-regular:
  -- https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L200
  -- Use total_degree_monomial once its merged into mathlib
  rw monomial_degree,
  classical,
  simp [total_degree, support_monomial, if_neg, h],
end

lemma monomial_degree_single {σ : Type*} {j : σ} {d : ℕ}:
monomial_degree (single j d) = d :=
begin
  sorry
end

lemma monomial_degree_le_total_degree {σ R : Type*}[comm_semiring R] {m :  σ →₀ ℕ} {f  : mv_polynomial σ R} 
  (h : m ∈ f.support) : monomial_degree m ≤ total_degree f :=
begin
  sorry
end

lemma coeff_zero_of_degree_greater_than_total_degree { n : ℕ } {F : Type u} [field F] 
(t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) :
monomial_degree t > total_degree f → coeff t f = 0 :=
begin
  sorry
end

/-
-- Would it be better to use this alternative definition?:
def max_degree_monomial  { n : ℕ } {F : Type u} [field F] 
(t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) : Prop := 
t ∈ f.support ∧ monomial_degree t = total_degree f
-/

def max_degree_monomial  { n : ℕ } {F : Type u} [field F] 
(t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) : Prop := 
(coeff t f ≠ 0) ∧ (∀ t' : fin n →₀ ℕ, monomial_degree t' > monomial_degree t → coeff t' f = 0)

def dominant_monomial { n : ℕ } {F : Type u} [field F] 
(t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) : Prop := 
  max_degree_monomial t f 
  ∧  (∀ t' : fin n →₀ ℕ, monomial_degree t' = monomial_degree t → coeff t' f ≠ 0 → t = t')

lemma max_degree_monomial_iff_nonzero_coeff_and_realizes_total_degree { n : ℕ } {F : Type u} [field F] 
(t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) :
max_degree_monomial t f ↔ (coeff t f ≠ 0 ∧ total_degree f = monomial_degree t) :=
begin
  sorry
end

lemma max_degree_monomial_iff_support_coff 
{ n : ℕ } {F : Type u} [field F] (t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) :
max_degree_monomial t f ↔ (coeff t f ≠ 0 ∧ ∀ t' ∈ f.support,  monomial_degree t' ≤ monomial_degree t) :=
begin
  sorry
end

lemma max_degree_monomial_iff_nonzero_coef_and_le { n : ℕ } {F : Type u} [field F] 
(t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) :
max_degree_monomial t f ↔ (coeff t f ≠ 0 ∧ total_degree f ≤ monomial_degree t) :=
begin
  sorry
end

lemma dominant_monomial_of_factor_is_factor_of_max_degree_monomial
  { n : ℕ } {F : Type u} [field F] (S : finset F) (t t' : fin n →₀ ℕ ) 
  (f g : mv_polynomial (fin n) F) (hfg : max_degree_monomial t (f*g))
  (hf : f ≠ 0) (hg : dominant_monomial t' g) : ∀ i : fin n, t' i ≤ t i :=
begin
  sorry,
end

end mv_polynomial