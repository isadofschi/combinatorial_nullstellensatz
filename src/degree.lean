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
import from_flt_regular.homogenization

universes u v

variables {α : Type v}

open set function finsupp add_monoid_algebra


open_locale big_operators 


/-

  Total_degree, etc
  
-/

namespace mv_polynomial
variables {R : Type*} {σ : Type*} 
local attribute [instance] classical.prop_decidable

lemma X_ne_zero [comm_semiring R] [nontrivial R] (j : σ) : (X j : mv_polynomial σ R) ≠ 0 :=
begin
  rw ne_zero_iff,
  use single j 1,
  simp,
end

lemma total_degree_sum [comm_semiring R] (s : finset α) (p : α → mv_polynomial σ R) :
  total_degree (∑ i : α in s, p i) ≤ s.sup (λ i , total_degree(p i)) :=
begin
  apply finset.cons_induction_on s,
  simp,
  clear s,
  intros a s h_a_in_s h_ind,
  rw finset.sum_cons,
  rw finset.sup_cons,
  apply (total_degree_add _ _).trans,
  simp [h_ind],
end

lemma total_degree_mul_X_le [comm_semiring R] [nontrivial R] (f : mv_polynomial σ R) (j : σ) :
  total_degree (f * X j) ≤ total_degree f + 1 := 
begin
  apply (total_degree_mul f (X j)).trans,
  simp only [total_degree_X],
end

-- The following depends on https://github.com/leanprover-community/flt-regular

-- this appears in flt-regular as support_add_eq
lemma support_add_disjoint [comm_semiring R] {f g : mv_polynomial σ R} 
  (h : disjoint f.support g.support) : (f + g).support = f.support ∪ g.support := 
finsupp.support_add_eq h

lemma total_degree_add_eq_of_disjoint_support [comm_semiring R] {f g : mv_polynomial σ R} 
  (h : disjoint f.support g.support) : total_degree (f + g) = max f.total_degree g.total_degree :=
begin
  simp only [total_degree, support_add_disjoint h],
  apply finset.sup_union,
end

lemma total_degree_add_monomial [comm_semiring R] (f : mv_polynomial σ R) (a : σ →₀ ℕ) (b : R)
  (h : a ∉ f.support) (h_b: b ≠ 0) : total_degree (monomial a b + f)
    = linear_order.max (total_degree (monomial a b)) (total_degree f) :=
begin
  apply total_degree_add_eq_of_disjoint_support,
  simp [support_monomial, h_b, h],
end

open_locale pointwise

-- this uses code from flt-regular
lemma support_mul1 [comm_semiring R] [decidable_eq σ] (p q : mv_polynomial σ R) :
  (p * q).support ⊆ p.support + q.support := by convert support_mul' p q

lemma support_mul'' [comm_ring R] {f g : mv_polynomial σ R}{m : σ →₀ ℕ}( h : m ∈ (f * g).support) :
  ∃ mf mg, mf ∈ f.support ∧ mg ∈ g.support ∧ mf + mg = m :=  finset.mem_add.1 $ support_mul1 f g h

-- this uses code from flt-regular
lemma total_degree_mul' [comm_ring R] [is_domain R] {f g : mv_polynomial σ R} (hf : f ≠ 0)
  (hg : g ≠ 0) : total_degree (f * g) = total_degree f + total_degree g :=
total_degree_mul_eq hf hg

lemma total_degree_mul_X [comm_ring R] [is_domain R] {f : mv_polynomial σ R} (h : f ≠ 0)
  (j : σ) : total_degree (f * X j) = total_degree f + 1 :=
by simp [total_degree_mul' h (X_ne_zero j)]

end mv_polynomial
