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
  sorry
end

/- Todo esto se puede hacer con mas generalidad! -/

def max : multiset ℕ  → ℕ :=
multiset.foldr (max) (λ x y z, by simp [max_left_comm]) 0

def monomial_degree {s : Type} (t : s →₀ ℕ) : ℕ := ∑ i in t.support, t i

-- ¿ que pasa con el grado del polinomio 0 ?
#eval total_degree (0 : mv_polynomial (fin 3) ℚ) 
-- #eval total_degree ( single (λ i:(fin 3), 1)  0 : mv_polynomial (fin 3) ℚ) 

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

/-
  Ver si se puede generalizar más esta parte
-/

lemma lemita1 { n : ℕ } {F : Type u} [field F] (S : finset F) (t : fin n →₀ ℕ ) (i : fin n) :
  dominant_monomial (finsupp.single i (S.card)) (∏ s in S, (X i - C s)) :=
begin
  sorry,
end

lemma lemita4 { n : ℕ } {F : Type u} [field F] (S : finset F) (t : fin n →₀ ℕ ) (i : fin n) :
  total_degree (∏ s in S, (X i - C s)) = S.card :=
begin
  sorry
end

lemma eval_is_zero { n : ℕ } {F : Type u} [field F]
  (S : finset F)
  (hS : 0 < S.card) 
  (s : fin n → F)
  (i : fin n)
  (h_s : s i ∈ S) :
  eval s (∏ s in S, (X i - C s)) = 0
:= begin
  sorry,
end

end mv_polynomial