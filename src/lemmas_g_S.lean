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

-- unused (may be useful as intermediate step)
--lemma degree_of_eq_total_degree {R σ : Type*} [field R] {p : mv_polynomial σ R}
 --(i : σ) (h : p ∈ supported R ({i}: set σ)) : degree_of i p = total_degree p := sorry


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

lemma prod_mem_supported {R σ α : Type*}[decidable_eq α] [comm_semiring R] 
(s : set σ) (a : finset α) (f : α → mv_polynomial σ R)
(h : ∀ i ∈ a, f i ∈ supported R s) : ∏ i in a, f i ∈ supported R s := 
subalgebra.prod_mem (supported R s) h

lemma g_S_lem_1 {R σ : Type*} [field R] {p : mv_polynomial σ R} {i : σ} 
(hp : p ∈ supported R ({i} : set σ)) : dominant_monomial (finsupp.single i p.total_degree) p :=
begin
  sorry,
end

-- special case g_S

lemma g_S_lem_supported {R σ : Type*} [comm_ring R] [nontrivial R][decidable_eq R] 
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


lemma g_S_lem_0 { n : ℕ } {F : Type u} [field F] [decidable_eq F] [nontrivial F]
(S : finset F) (i : fin n) : (∏ s in S, (X i - C s)) ≠ 0 :=
begin
  rw finset.prod_ne_zero_iff,
  intros a ha,
  by_contra,
  have h' : ¬ 0 = single i 1,
  { by_contra,
    have t : single i 1 i = 1 := by simp,
    rw ←h at t,
    simpa using t },
  have c : coeff (single i 1) (X i - C a)  =  coeff (single i 1) 0 := by rw h,
  simp only [coeff_X, coeff_C, coeff_sub, coeff_zero, if_neg, h'] at c,
  simpa using c,
end

lemma g_S_lem_4 { n : ℕ } {F : Type u} [field F] {S : finset F} {i : fin n} :
  total_degree (∏ s in S, (X i - C s)) = S.card :=
begin
  sorry
end

lemma g_S_lem_8  { n : ℕ } {F : Type u} [field F] (S : finset F)(i : fin n)
  : coeff (single i S.card) ∏ s in S, (X i - C s) = 1 :=
begin
  apply finset.cons_induction_on S,
  simp,
  clear S,
  intros a S haS hind,
  rw finset.prod_cons,
  rw sub_mul,
  rw coeff_sub,
  rw finset.card_cons,
  rw coeff_X_mul',
  simp only [ if_true, coeff_C_mul, single_eq_same, pi.add_apply, nat.succ_ne_zero,
              finsupp.mem_support_iff, ne.def, not_false_iff, add_tsub_cancel_right, coe_add,
              single_add ],
  rw hind,
  simp only [sub_eq_self, mul_eq_zero],
  right,
  rw ← single_add,
  apply coeff_zero_of_degree_greater_than_total_degree,
  rw g_S_lem_4,
  rw monomial_degree_single,
  simp,
end

lemma g_S_lem_1' { n : ℕ } {R : Type* } [field R] [decidable_eq R] (S : finset R) (i : fin n) :
  dominant_monomial (finsupp.single i (S.card)) (∏ s in S, (X i - C s)) :=
begin
  rw ← g_S_lem_4,
  apply g_S_lem_1,
  apply g_S_lem_supported,
end

end mv_polynomial