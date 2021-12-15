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

--- lemmas for supported

lemma g_S_lem_6 {R σ : Type*} [comm_semiring R] {p : mv_polynomial σ R} {m: σ →₀ ℕ} {i j : σ} 
  (hp : p ∈ supported R ({i} : set σ)) (h_m : m ∈ p.support) (h : i ≠ j) : m j = 0 :=
begin
  have hp' := mem_supported.1 hp,
  by_contra c,
  have hj : j ∈ p.vars := (mem_vars j).2 ⟨m, h_m, (by simp [c])⟩,
  have t' := mem_singleton_iff.1 (mem_of_subset_of_mem hp' hj),
  rw t' at h,
  simpa using h,
end

lemma g_S_lem_6'{R σ : Type*} [comm_semiring R] {i j: σ}  {p : mv_polynomial σ R}
  {m: σ →₀ ℕ} (hp : p ∈ supported R ({i} : set σ)) (h' : m j ≠ 0) (h : j ≠ i)  :
    coeff m p = 0 :=
begin
  by_cases c : m ∈ p.support,
  { have t := g_S_lem_6 hp c h.symm,
    rw t at h',
    simpa using h', },
  simpa using c,
end

lemma C_mem_supported {R σ : Type*} [comm_semiring R] 
(s : set σ) (a : R) : C a ∈ supported R s := 
begin
  apply mem_supported.2,
  simp,
end

lemma add_mem_supported {R σ : Type*} [comm_semiring R] 
(s : set σ) (f g : mv_polynomial σ R)
(hf : f ∈ supported R s) (hg : g ∈ supported R s) : f + g ∈ supported R s :=
subalgebra.add_mem (supported R s) hf hg


lemma mul_mem_supported {R σ : Type*} [comm_semiring R] 
(s : set σ) (f g : mv_polynomial σ R)
(hf : f ∈ supported R s) (hg : g ∈ supported R s) : f * g ∈ supported R s := 
subalgebra.mul_mem (supported R s) hf hg

lemma sub_mem_supported {R σ : Type*} [comm_ring R] 
(s : set σ) (f g : mv_polynomial σ R)
(hf : f ∈ supported R s) (hg : g ∈ supported R s) : f - g ∈ supported R s := 
subalgebra.sub_mem (supported R s) hf hg

lemma prod_mem_supported {R σ α : Type*} [comm_semiring R] 
(s : set σ) (a : finset α) (f : α → mv_polynomial σ R)
(h : ∀ i ∈ a, f i ∈ supported R s) : ∏ i in a, f i ∈ supported R s := 
subalgebra.prod_mem (supported R s) h

lemma monomial_support_supported'  {R σ : Type*} [comm_semiring R] {p : mv_polynomial σ R} 
{i : σ} { s : set σ} {m : σ →₀ ℕ}
(hp : p ∈ supported R s)  (hm : m ∈ p.support) (hi : i ∉ s) : m i = 0 :=
begin
  by_contradiction c,
  have h' : i ∈ ((p.vars) : set σ) := by simpa using (mem_vars i).2 ⟨ m, ⟨hm, by simp [c]⟩⟩,
  rw mem_supported at hp,
  have t := mem_of_mem_of_subset h' hp,
  cc,
end

lemma monomial_support_supported  {R σ : Type*} [comm_semiring R] {p : mv_polynomial σ R} {i : σ} 
(hp : p ∈ supported R ({i} : set σ)) {m : σ →₀ ℕ} (hm : m ∈ p.support) : m = single i (m i)
:=
begin
  ext j,
  by_cases c : i = j,
  simp [c],
  simp only [c, single_eq_of_ne, ne.def, not_false_iff],
  apply monomial_support_supported' hp hm,
  simp only [mem_singleton_iff],
  cc,
end

lemma g_S_lem_1a {R σ : Type*} [comm_semiring R] {p : mv_polynomial σ R} {i : σ} 
(h : p ≠ 0) (hp : p ∈ supported R ({i} : set σ)) : finsupp.single i p.total_degree ∈ p.support :=
begin
  cases exists_max_degree_monomial h with m hm,
  cases hm with h h',
  have t := monomial_support_supported hp h,
  convert h,
  rw t,
  congr,
  rw ← h',
  rw t,
  rw monomial_degree_single,
  simp,
end

lemma g_S_lem_1 {R σ : Type*} [comm_semiring R] {p : mv_polynomial σ R} {i : σ} (h : p ≠ 0)
  (hp : p ∈ supported R ({i} : set σ)) : dominant_monomial (finsupp.single i p.total_degree) p :=
begin
  rw dominant_monomial,
  apply and.intro,
  rw max_degree_monomial,
  apply and.intro,
  exact g_S_lem_1a h hp,
  rw monomial_degree_single,
  intros t' ht',
  rw max_degree_monomial at ht',
  have x := monomial_support_supported hp ht'.1,
  rw x,
  congr,
  rw x at ht',
  rw monomial_degree_single at ht',
  exact ht'.2,
end


-- special case g_S

lemma g_S_lem_supported {R σ : Type*} [comm_ring R] [nontrivial R]
(S : finset R) (i : σ) : ∏ s in S, (X i - C s) ∈ supported R ({i}: set σ) :=
begin
  apply prod_mem_supported,
  intros s hs,
  apply sub_mem_supported,
  apply X_mem_supported.2,
  simp,
  exact _inst_2,
  apply C_mem_supported,
end


lemma eval_is_zero {R σ : Type*} [comm_ring R] [is_domain R] (S : finset R) (hS : 0 < S.card) 
  (s : σ → R) (i : σ) (h_s : s i ∈ S) : eval s (∏ s in S, (X i - C s)) = 0 :=
by simp  [eval_prod, finset.prod_eq_zero h_s]


lemma X_sub_C_ne_0 {R σ : Type*} [comm_ring R] [decidable_eq σ] [nontrivial R]
 (i : σ) (a : R) :  X i - C a ≠ 0 :=
begin
  rw nonzero_iff_exists,
  use single i 1,
  have h' : ¬ 0 = single i 1,
  { by_contra h,
    have t : single i 1 i = 1 := by simp,
    rw ←h at t,
    simpa using t },
  have c : coeff (single i 1) (X i - C a)  =  1 := by simp [h'],
  rw coeff at c,
  simp [c],
end

lemma total_degree_X_sub_C {R σ : Type*}[comm_ring R] [decidable_eq σ] [nontrivial R]
 (i : σ) (a : R) :  total_degree (X i - C a) = 1 :=
begin
  -- this could be a separate lemma called `total_degree_sub_eq_left_of_total_degree_lt`
  rw [sub_eq_add_neg, total_degree_add_eq_left_of_total_degree_lt],
  simp,
  simp,
end

lemma g_S_lem_5 {R  σ : Type* } [comm_semiring R] {i : σ} {m: σ →₀ ℕ} {p : mv_polynomial σ R}
  (h_m : m ∈ p.support) (h_m_i : m i = p.total_degree) : m = finsupp.single i p.total_degree :=
begin
  rw ←h_m_i,
  apply (monomial_degree_le_iff_eq_single m i).1,
  simpa [h_m_i] using monomial_degree_le_total_degree h_m,
end


lemma g_S_lem_0 {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R)
 (i : σ) : ∏ s in S, (X i - C s) ≠ 0 :=
begin
  rw finset.prod_ne_zero_iff,
  intros a ha,
  apply X_sub_C_ne_0,
end

lemma g_S_lem_4 {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R) (i : σ) :
  total_degree (∏ s in S, (X i - C s)) = S.card :=
begin
  apply finset.cons_induction_on S,
  simp,
  clear S,
  intros a S haS hind,
  rw [finset.prod_cons, finset.card_cons, total_degree_mul', hind, add_comm],
  congr,
  rw total_degree_X_sub_C,
  apply X_sub_C_ne_0,
  apply g_S_lem_0,
end

lemma g_S_lem_8 {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R) (i : σ) :
  coeff (single i S.card) ∏ s in S, (X i - C s) = 1 :=
begin
  apply finset.cons_induction_on S,
  simp,
  clear S,
  intros a S haS hind,
  simp only [finset.prod_cons, sub_mul, coeff_sub, finset.card_cons, coeff_X_mul', if_true,
            coeff_C_mul, single_eq_same, pi.add_apply, nat.succ_ne_zero, finsupp.mem_support_iff,
            ne.def, not_false_iff, add_tsub_cancel_right, coe_add, single_add, hind, sub_eq_self,
            mul_eq_zero],
  right,
  rw ← single_add,
  apply coeff_zero_of_degree_greater_than_total_degree,
  rw [g_S_lem_4, monomial_degree_single],
  simp,
end

lemma g_S_lem_1' {R σ : Type*} [comm_ring R] [is_domain R] [decidable_eq σ] (S : finset R)
  (i : σ) :  dominant_monomial (finsupp.single i (S.card)) (∏ s in S, (X i - C s)) :=
begin
  rw ← g_S_lem_4 S i,
  apply g_S_lem_1,
  apply g_S_lem_0,
  apply g_S_lem_supported,
end

end mv_polynomial