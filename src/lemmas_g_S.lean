/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.variables
import data.mv_polynomial.supported
import algebra.algebra.basic
import data.mv_polynomial.comm_ring
import data.nat.basic

import degree
import degree_new

universes u

open set function finsupp add_monoid_algebra

open_locale big_operators 

namespace mv_polynomial

lemma C_mem_supported {R σ : Type*} [comm_semiring R] (s : set σ) (a : R) : C a ∈ supported R s :=
mem_supported.2 (by simp)

lemma support_monomial_of_mem_support_of_supported  {R σ : Type*} [comm_semiring R]
  {p : mv_polynomial σ R} {i : σ} { s : set σ} {m : σ →₀ ℕ} (hm : m ∈ p.support)
  (hp : p ∈ supported R s) : ∀ i ∈ m.support, i ∈ s :=
begin
  intros i h,
  simp only [finsupp.mem_support_iff, ne.def] at h,
  by_contradiction c,
  exact c (mem_of_mem_of_subset (by simpa using (mem_vars i).2 
    ⟨m, ⟨hm, by simp [h]⟩⟩) (mem_supported.1 hp)),
end

lemma support_monomial_of_mem_support_of_supported'  {R σ : Type*} [comm_semiring R]
  {p : mv_polynomial σ R} {i : σ} { s : set σ} {m : σ →₀ ℕ}
  (hm : m ∈ p.support) (hp : p ∈ supported R s) (hi : i ∉ s) : m i = 0 :=
begin
  by_contradiction c,
  exact hi (mem_of_mem_of_subset (by simpa using (mem_vars i).2 
    ⟨m, ⟨hm, by simp [c]⟩⟩) (mem_supported.1 hp)),
end

lemma eq_single_of_mem_support_of_supported_singleton  {R σ : Type*} [comm_semiring R] 
  {p : mv_polynomial σ R} {i : σ} {m : σ →₀ ℕ} (hm : m ∈ p.support)
  (hp : p ∈ supported R ({i} : set σ)) : m = single i (m i) :=
begin
  ext j,
  by_cases c : i = j,
  { simp [c] },
  { simp only [c, single_eq_of_ne, ne.def, not_false_iff],
    apply support_monomial_of_mem_support_of_supported' hm hp,
    simp only [mem_singleton_iff],
    by_contradiction c',
    exact c c'.symm },
end

lemma single_total_degree_mem_support_of_supported_singleton {R σ : Type*} [comm_semiring R]
  {p : mv_polynomial σ R} {i : σ} (h : p ≠ 0) (hp : p ∈ supported R ({i} : set σ)) :
  finsupp.single i p.total_degree ∈ p.support :=
begin
  cases exists_max_degree_monomial h with m hm,
  cases hm with h h',
  convert h,
  rw eq_single_of_mem_support_of_supported_singleton h hp,
  congr,
  rw [← h', eq_single_of_mem_support_of_supported_singleton h hp, monomial_degree_single],
  simp,
end

lemma dominant_monomial_single_of_supported_singleton {R σ : Type*} [comm_semiring R]
  {p : mv_polynomial σ R} {i : σ} (h : p ≠ 0) (hp : p ∈ supported R ({i} : set σ)) :
  dominant_monomial (finsupp.single i p.total_degree) p :=
begin
  rw dominant_monomial,
  split,
  { rw max_degree_monomial,
    split,
    { exact single_total_degree_mem_support_of_supported_singleton h hp },
    {rw monomial_degree_single} },
  { intros t' ht',
    rw max_degree_monomial at ht',
    have x := eq_single_of_mem_support_of_supported_singleton ht'.1 hp,
    rw x,
    congr,
    rw x at ht',
    rw monomial_degree_single at ht',
    exact ht'.2 },
end

lemma X_sub_C_ne_0 {R σ : Type*} [comm_ring R] [decidable_eq σ] [nontrivial R]
  (i : σ) (a : R) : X i - C a ≠ 0 :=
begin
  rw nonzero_iff_exists,
  use single i 1,
  have h' : ¬ 0 = single i 1, -- is this on mathlib?
  { suffices t : single i 1 i = 1,
    { by_contra h,
      simpa [←h] using t },
    simp },
  have c : coeff (single i 1) (X i - C a)  =  1 := by simp [h'],
  rw coeff at c,
  simp [c],
end

lemma total_degree_X_sub_C {R σ : Type*}[comm_ring R] [decidable_eq σ] [nontrivial R]
 (i : σ) (a : R) : total_degree (X i - C a) = 1 :=
begin
  -- this could be a separate lemma called `total_degree_sub_eq_left_of_total_degree_lt`
  rw [sub_eq_add_neg, total_degree_add_eq_left_of_total_degree_lt],
  { simp },
  { simp },
end

-- lemmas for g_S

lemma g_S_mem_supported {R σ : Type*} [comm_ring R] [nontrivial R]
  (S : finset R) (i : σ) : ∏ s in S, (X i - C s) ∈ supported R ({i}: set σ) :=
begin
  apply (supported R {i}).prod_mem,
  intros s hs,
  apply (supported R ({i}: set σ)).sub_mem,
  { apply X_mem_supported.2,
    { simp },
    { exact _inst_2 } },
  { apply C_mem_supported },
end

lemma eval_g_S_eq_zero {R σ : Type*} [comm_ring R] [is_domain R] (S : finset R) (hS : 0 < S.card) 
  (s : σ → R) (i : σ) (h_s : s i ∈ S) : eval s (∏ s in S, (X i - C s)) = 0 :=
by simp  [eval_prod, finset.prod_eq_zero h_s]

lemma g_S_ne_0 {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R)
 (i : σ) : ∏ s in S, (X i - C s) ≠ 0 :=
begin
  rw finset.prod_ne_zero_iff,
  intros a ha,
  apply X_sub_C_ne_0,
end

lemma total_degree_g_S {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R) (i : σ) :
  total_degree (∏ s in S, (X i - C s)) = S.card :=
begin
  apply finset.cons_induction_on S,
  { simp },
  { clear S,
    intros a S haS hind,
    rw [finset.prod_cons, finset.card_cons, total_degree_mul', hind, add_comm],
    congr,
    rw total_degree_X_sub_C,
    { apply X_sub_C_ne_0 },
    { apply g_S_ne_0 } },
end

lemma g_S_monic {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R) (i : σ) :
  coeff (single i S.card) ∏ s in S, (X i - C s) = 1 :=
begin
  apply finset.cons_induction_on S,
  { simp },
  { clear S,
    intros a S haS hind,
    simp only [finset.prod_cons, sub_mul, coeff_sub, finset.card_cons, coeff_X_mul', if_true,
              coeff_C_mul, single_eq_same, pi.add_apply, nat.succ_ne_zero, finsupp.mem_support_iff,
              ne.def, not_false_iff, add_tsub_cancel_right, coe_add, single_add, hind, sub_eq_self,
              mul_eq_zero],
    right,
    rw ← single_add,
    apply coeff_zero_of_degree_greater_than_total_degree,
    rw [total_degree_g_S, monomial_degree_single],
    simp },
end

lemma dominant_monomial_g_S {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R)
  (i : σ) :  dominant_monomial (finsupp.single i (S.card)) (∏ s in S, (X i - C s)) :=
begin
  rw ← total_degree_g_S S i,
  apply dominant_monomial_single_of_supported_singleton,
  { apply g_S_ne_0 },
  { apply g_S_mem_supported },
end

end mv_polynomial