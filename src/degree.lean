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
  cases finset.mem_union.1 (finset.mem_of_subset _ h')
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
  convert support_add,
end

/-
lemma mem_support_iff_nonzero_coeff [comm_semiring R] -- Do we already have this?  Yes, it is mem_support_iff
  (p : mv_polynomial σ R) (m : σ →₀ ℕ): m ∈ p.support ↔ coeff m p ≠ 0 := by simp
-/

end mv_polynomial

/-

  Degree: degree_of
  
-/
section PR10646
-- https://github.com/leanprover-community/mathlib/pull/10646

local attribute [instance] classical.prop_decidable

namespace multiset

lemma count_sup' {α : Type*} [decidable_eq α] (x : α) (s t : multiset α) :
count x (s ⊔ t) = max (count x s) (count x t) := by simp

end multiset

namespace mv_polynomial
variables {R : Type*} {σ : Type*} 

lemma support_sub [comm_ring R] (p q : mv_polynomial σ R) :
  (p - q).support ⊆ p.support ∪ q.support := 
begin
  rw [sub_eq_add_neg, ← @support_neg R σ _ q],
  convert support_add,
end

lemma degree_of_eq_sup {R : Type u} [comm_semiring R] (j : σ) (f : mv_polynomial σ R) :
  degree_of j f = f.support.sup (λ m , m j) :=
begin
  rw [ degree_of, degrees, multiset.count_sup ],
  congr,
  ext,
  simp,
end

lemma degree_of_lt_iff {R : Type u} [comm_semiring R]  {j : σ} {f : mv_polynomial σ R}
  {d : ℕ} (h : 0 < d):  degree_of j f < d ↔ ∀ m : σ →₀ ℕ, m ∈ f.support → m j < d := 
by rwa [degree_of_eq_sup j f, finset.sup_lt_iff]

lemma degree_of_C {σ : Type*} {R : Type*} [comm_semiring R] (a : R) (x : σ): 
  degree_of x (C a : mv_polynomial σ R) = 0 := by simp [degree_of, degrees_C]

lemma degree_of_add_le {σ : Type*} {R : Type*} [comm_semiring R] (x : σ)
  (f g : mv_polynomial σ R) : degree_of x (f + g) ≤ max (degree_of x f) (degree_of x g) :=
begin
  repeat {rw degree_of},
  apply (multiset.count_le_of_le x (degrees_add f g)).trans,
  rw multiset.count_sup',
end

lemma degree_of_sub_lt [comm_ring R] {x : σ} {f g : mv_polynomial σ R} {k : ℕ} (h : 0 < k)
  (hf : ∀ (m : σ →₀ ℕ), m ∈ f.support → (k ≤ m x) → coeff m f = coeff m g)
  (hg : ∀ (m : σ →₀ ℕ), m ∈ g.support → (k ≤ m x) → coeff m f = coeff m g) :
  degree_of x (f - g) < k := 
begin
  rw degree_of_lt_iff,
  intros m hm,
  by_contra hc,
  simp only [not_lt] at hc,
  have h := finset.mem_of_subset (support_sub f g) hm,
  cases (finset.mem_union).1 h with cf cg,
  have hf' := hf m cf hc,
  rw [← sub_eq_zero] at hf',
  simp only [mem_support_iff, ne.def, coeff_sub] at hm,
  contradiction,
  have hg' := hg m cg hc,
  rw [← sub_eq_zero] at hg',
  simp only [mem_support_iff, ne.def, coeff_sub] at hm,
  contradiction,
  exact h,
end

lemma monomial_le_degree_of [comm_ring R] (i : σ) {f : mv_polynomial σ R} {m : σ →₀ ℕ}
  (h_m : m ∈ f.support) : m i ≤ degree_of i f :=
begin
  rw degree_of_eq_sup i,
  apply finset.le_sup h_m,
end

-- TODO we could prove equality here with more hypotheses on R
lemma degree_of_mul_le [comm_ring R] (i : σ) (f g: mv_polynomial σ R) :
  degree_of i (f * g) ≤ degree_of i f + degree_of i g := 
begin
  repeat {rw degree_of},
  convert multiset.count_le_of_le i (degrees_mul f g),
  rw multiset.count_add,
end

lemma degree_of_X (i j : σ ) [comm_semiring R] [nontrivial R] :
  degree_of i (X j : mv_polynomial σ R) = if i = j then 1 else 0 :=
begin
  by_cases c : i = j,
  { simp only [c, if_true, eq_self_iff_true, degree_of, degrees_X, multiset.count_singleton] },
  simp [c, if_false, degree_of, degrees_X],
end

lemma degree_of_mul_X_ne  [comm_ring R] {i j : σ} (f : mv_polynomial σ R) (h : i ≠ j) :
  degree_of i (f * X j) = degree_of i f :=
begin
  repeat {rw degree_of_eq_sup i},
  rw support_mul_X,
  simp only [finset.sup_map],
  congr,
  ext,
  simp only [ single, nat.one_ne_zero, add_right_eq_self, add_right_embedding_apply, coe_mk,
              pi.add_apply, comp_app, ite_eq_right_iff, coe_add ],
  cc,
end

/- TODO in the following we have equality iff f ≠ 0 -/
lemma degree_of_mul_X_eq [comm_ring R] (j : σ) (f : mv_polynomial σ R) :
  degree_of j (f * X j)  ≤ degree_of j f + 1 := 
begin
  repeat {rw degree_of},
  apply (multiset.count_le_of_le j (degrees_mul f (X j))).trans,
  simp only [multiset.count_add, add_le_add_iff_left],
  convert multiset.count_le_of_le j (degrees_X' j),
  rw multiset.count_singleton_self,
end
end mv_polynomial

end PR10646

/-

  Total_degree, etc
  
-/
namespace mv_polynomial
variables {R : Type*} {σ : Type*} 
local attribute [instance] classical.prop_decidable

lemma X_ne_zero [comm_semiring R] [nontrivial R] (j : σ) : 
  (X j : mv_polynomial σ R) ≠ 0
:= begin
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

lemma total_degree_mul_X_le  [field R]
(f : mv_polynomial σ R)(j : σ) :
total_degree (f * X j) ≤ total_degree f + 1 := 
begin
  apply (total_degree_mul f (X j)).trans,
  simp,
end

lemma support_add_disjoint [comm_semiring R] {f g : mv_polynomial σ R} 
  (h : f.support ∩ g.support = ∅ ) : (f + g).support = f.support ∪ g.support :=
begin
  apply le_antisymm,
  convert support_add,
  unfold has_le.le,
  unfold preorder.le,
  unfold partial_order.le,
  apply finset.union_subset,
  unfold has_subset.subset,
  intros m hm,
  have hm' : m ∉ g.support,
  { by_contradiction c,
    have hm'' : m ∈ f.support ∩ g.support := by simp [hm, c],
    rw h at hm'',
    simpa using hm'' },
  simp only [mem_support_iff, coeff_add, ne.def],
  simp only [not_not, mem_support_iff] at hm',
  simpa [hm'] using hm,
  unfold has_subset.subset,
  intros m hm,
  have hm' : m ∉ f.support,
  { by_contradiction c,
    have hm'' : m ∈ f.support ∩ g.support := by simp [hm, c],
    rw h at hm'',
    simpa using hm'' },
  simp only [mem_support_iff, coeff_add, ne.def],
  simp only [not_not, mem_support_iff] at hm',
  simpa [hm'] using hm,
end

lemma total_degree_add_eq_of_disjoint_support [comm_semiring R] {f g : mv_polynomial σ R} 
  (h : f.support ∩ g.support = ∅ ) : total_degree (f + g) = max f.total_degree g.total_degree :=
begin
  repeat {rw total_degree},
  rw support_add_disjoint h,
  convert finset.sup_union,
end

lemma total_degree_add_monomial [comm_semiring R] (f : mv_polynomial σ R) 
  (a : σ →₀ ℕ) (b : R) (h : a ∉ f.support) (h_b: b ≠ 0) :
  total_degree (monomial a b + f) = linear_order.max (total_degree (monomial a b)) (total_degree f) :=
begin
  apply total_degree_add_eq_of_disjoint_support,
  simp [support_monomial, h_b, h],
end

-- The following depends on https://github.com/leanprover-community/flt-regular

open_locale pointwise

-- this uses code from flt-regular
lemma support_mul1 [comm_semiring R] [decidable_eq σ] (p q : mv_polynomial σ R) :
  (p * q).support ⊆ p.support + q.support := by convert support_mul' p q

lemma support_mul'' [comm_ring R] {f g : mv_polynomial σ R}{m : σ →₀ ℕ}( h : m ∈ (f * g).support) :
  ∃ mf mg, mf ∈ f.support ∧ mg ∈ g.support ∧ mf + mg = m :=  finset.mem_add.1 $ support_mul1 f g h

-- this uses code from flt-regular
lemma total_degree_mul' [comm_ring R] [is_domain R] {f g : mv_polynomial σ R} 
  (hf : f ≠ 0) (hg : g ≠ 0) : total_degree (f * g) = total_degree f + total_degree g := total_degree_mul_eq hf hg


lemma total_degree_mul_X [field R] {f : mv_polynomial σ R} (h : f ≠ 0)
  (j : σ) : total_degree (f * X j) = total_degree f + 1 :=
by simp [total_degree_mul' h (X_ne_zero j)]

end mv_polynomial
