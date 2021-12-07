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
import degree

universes u v

variables {α : Type v}

open set function finsupp add_monoid_algebra


open_locale big_operators 

-- check https://github.com/leanprover-community/flt-regular/blob/master/src/ring_theory/polynomial/homogenization.lean
-- and https://github.com/leanprover-community/mathlib/pull/10429/files for useful lemmas

namespace mv_polynomial 

variables {R : Type*} {σ : Type*} 

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

-- This depends on flt-regular. Use total_degree_monomial once its merged into mathlib
lemma total_degree_monomial_eq_monomial_degree  {σ R : Type*}[comm_semiring R] {m :  σ →₀ ℕ} {a : R} (h : a ≠ 0):
total_degree (monomial m a) = monomial_degree m := by  convert total_degree_monomial m h

-- Use monomial instead of single!
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