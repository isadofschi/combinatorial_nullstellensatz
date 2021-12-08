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

-- this def is also given in flt-regular
def monomial_degree {s : Type*} (t : s →₀ ℕ) : ℕ := t.sum (λ _ e, e) --∑ i in t.support, t i

lemma nat.term_le_sum {s : finset α } (f : α → ℕ){j : α} (hj : j ∈ s) : f j ≤ s.sum f :=
begin
  revert j,
  apply finset.cons_induction_on s,
  simp,
  clear s,
  intros x s hx hj j hc,
  rw finset.sum_cons,
  simp only [finset.mem_cons] at hc,
  cases hc with j_eq_x j_in_s,
  simp [j_eq_x],
  apply (hj j_in_s).trans,
  simp,
end

lemma le_monomial_degree  {s : Type*} (t : s →₀ ℕ) (j : s) : t j ≤ monomial_degree t :=
begin
  by_cases c : j ∈ t.support,
  { apply nat.term_le_sum,
    exact c },
  simp only [not_not, finsupp.mem_support_iff] at c,
  simp [c],
end


lemma monomial_degree_sub  {σ : Type*} {m m' :  σ →₀ ℕ} (h : m' ≤ m) : 
  monomial_degree (m - m') = monomial_degree m - monomial_degree m' := 
begin
  simp [monomial_degree],
  rw finsupp.sum,
  simp,
  have t:= @finset.sum_sub_distrib ℕ σ (m-m').support m m',
  apply (int.coe_nat_eq_coe_nat_iff _ _).1,
  sorry
end

-- This depends on flt-regular. Use total_degree_monomial once its merged into mathlib
lemma total_degree_monomial_eq_monomial_degree  {σ R : Type*}[comm_semiring R] {m :  σ →₀ ℕ} {a : R} (h : a ≠ 0):
total_degree (monomial m a) = monomial_degree m := by  convert total_degree_monomial m h

-- Use monomial instead of single!
lemma monomial_degree_single {σ : Type*} {j : σ} {d : ℕ}:
monomial_degree (single j d) = d :=
begin
  rw monomial_degree,
  simp,
end

lemma monomial_degree_le_total_degree {σ R : Type*}[comm_semiring R] {m :  σ →₀ ℕ} {f  : mv_polynomial σ R} 
  (h : m ∈ f.support) : monomial_degree m ≤ total_degree f :=
begin
  rw total_degree,
  rw monomial_degree,
  apply finset.le_sup h,
end

lemma le_total_degree  {R σ : Type*} [comm_semiring R] {i: σ} {p : mv_polynomial σ R}
  {m: σ →₀ ℕ} (h_m : m ∈ p.support) : m i ≤ p.total_degree
:= (le_monomial_degree m i).trans $ monomial_degree_le_total_degree h_m

lemma coeff_zero_of_degree_greater_than_total_degree {F : Type u} [field F] 
(t : σ →₀ ℕ) (f : mv_polynomial σ F) :
monomial_degree t > total_degree f → coeff t f = 0 :=
begin
  intro h,
  by_cases c: t ∈ f.support,
  { exfalso,
    simpa using lt_of_le_of_lt (monomial_degree_le_total_degree c) h },
  simp only [not_not, mem_support_iff] at c,
  exact c,
end

def max_degree_monomial {F : Type u} [field F] 
(t : σ →₀ ℕ) (f : mv_polynomial σ F) : Prop := 
t ∈ f.support ∧ monomial_degree t = total_degree f

def dominant_monomial {F : Type u} [field F] 
(t : σ →₀ ℕ) (f : mv_polynomial σ F) : Prop := 
  max_degree_monomial t f 
  ∧  (∀ t' : σ →₀ ℕ, monomial_degree t' = monomial_degree t → coeff t' f ≠ 0 → t = t')

-- unused. perhaps useful as intermediate step?
lemma max_degree_monomial_iff_support_coff
{F : Type u} [field F] (t : σ →₀ ℕ) (f : mv_polynomial σ F) :
max_degree_monomial t f ↔ (coeff t f ≠ 0 ∧ ∀ t' ∈ f.support,  monomial_degree t' ≤ monomial_degree t) :=
begin
  sorry
end

-- unused. perhaps useful as intermediate step?
lemma max_degree_monomial_iff_nonzero_coef_and_le {F : Type u} [field F]
(t : σ →₀ ℕ) (f : mv_polynomial σ F) :
max_degree_monomial t f ↔ (coeff t f ≠ 0 ∧ total_degree f ≤ monomial_degree t) :=
begin
  sorry
end

lemma dominant_monomial_of_factor_is_factor_of_max_degree_monomial
  {F : Type u} [field F] (S : finset F) (t t' : σ →₀ ℕ ) 
  (f g : mv_polynomial σ F) (hfg : max_degree_monomial t (f*g))
  (hf : f ≠ 0) (hg : dominant_monomial t' g) : ∀ i : σ, t' i ≤ t i :=
begin
  sorry,
end

end mv_polynomial