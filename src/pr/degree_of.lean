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
import pr.support_sum
import from_flt_regular.homogenization

universes u v

variables {α : Type v}

open set function finsupp add_monoid_algebra


open_locale big_operators 


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
