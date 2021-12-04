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
-- for these lemmas before proving!

namespace mv_polynomial 

lemma degree_of_C {σ : Type*} {R : Type*} [comm_semiring R] (a : R) (x : σ): 
  degree_of x (C a : mv_polynomial σ R) = 0 := 
begin
  rw degree_of,
  rw degrees_C,
  simp,
end

lemma degree_of_add_le {σ : Type*} {R : Type*} [comm_semiring R]
 (x : σ) (f g : mv_polynomial σ R): 
 degree_of x (f + g) ≤ max (degree_of x f) (degree_of x g) := 
begin
  rw degree_of,
  -- rw degrees,
  -- have h : multiset.count x (f + g).degrees ≤ multiset.count x (f.degrees ⊔ g.degrees),
  -- rw degrees_add,
  -- congr,
  sorry
end

lemma degree_of_sub_aux {σ : Type*} {R : Type*} [comm_ring R]
  (x : σ) (f g : mv_polynomial σ R) (k : ℕ)
  (h1 : ∀ (m : σ →₀ ℕ), m ∈ f.support → (k ≤ m x) → coeff m f = coeff m g) 
  (h2 : ∀ (m : σ →₀ ℕ), m ∈ g.support → (k ≤ m x) → coeff m f = coeff m g) : 
  degree_of x (f - g) < k := 
begin
   sorry
end

lemma should_be_in_mathlib {σ : Type*} {R : Type*} [comm_ring R]
  (i : σ) {f : mv_polynomial σ R}
  {m : σ →₀ ℕ} (h_m : m ∈ f.support) :
  m i ≤ degree_of i f := sorry

lemma degree_of_mul_X_ne  {σ : Type*} {R : Type*} [comm_ring R]
  {i j : σ} (f : mv_polynomial σ R) (h : i ≠ j) :
  degree_of i (f * X j)  = degree_of i f := sorry

/- in the following we have equality iff f ≠ 0 -/
lemma degree_of_mul_X_eq  {σ : Type*} {R : Type*} [comm_ring R]
  (j : σ) (f : mv_polynomial σ R) :
  degree_of j (f * X j)  ≤ degree_of j f + 1 := sorry


/- Todo esto se puede hacer con mas generalidad! -/

def max : multiset ℕ  → ℕ :=
multiset.foldr (max) (λ x y z, by simp [max_left_comm]) 0

def monomial_degree {s : Type} (t : s →₀ ℕ) : ℕ := ∑ i in t.support, t i

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
  sorry
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

-- hay que pedir f neq 0 y g neq 0 o f*g neq 0!!
lemma total_degree_mul' { n : ℕ } {F : Type u} [field F] (f g : mv_polynomial (fin n) F) :
total_degree (f*g) = total_degree f + total_degree g :=
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
  sorry
end

lemma total_degree_mul_X  { n : ℕ } {F : Type u} [field F] 
{f : mv_polynomial (fin n) F} (h : f ≠ 0) (j : fin n) :
total_degree (f * X j) = total_degree f + 1 := 
begin
  sorry
end

lemma coeff_zero_of_degree_greater_than_total_degree { n : ℕ } {F : Type u} [field F] 
(t : fin n →₀ ℕ) (f : mv_polynomial (fin n) F) :
monomial_degree t > total_degree f → coeff t f = 0 :=
begin
  sorry
end

lemma total_degree_sum {σ : Type*} {R : Type*} [comm_semiring R]
(s : finset α) (p : α → mv_polynomial σ R) :
total_degree (∑ i : α in s, p i) ≤ s.sup (λ i , total_degree(p i))
:= sorry


/-
-- seria mejor usar esta definicion:
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
  (hf : f≠ 0) (hg : dominant_monomial t' g) : ∀ i : fin n, t' i ≤ t i :=
begin
  sorry,
end

end mv_polynomial