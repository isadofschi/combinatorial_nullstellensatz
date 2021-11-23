/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.algebra.basic
import degree
import assorted_lemmas


/-
# Reduce degree

## Main results

- `reduce_degree`: corresponds to the following paragraph in the proof of Theorem 1.1 in Alon's
"Combinatorial Nullstellensatz" paper:
'Let \bar{f} be the polynomial obtained by writing f as a linear combination of monomials and replacing,
repeatedly, each occurrence of x ^ f_i (for 1 ≤ i ≤ n), where f_i > t_i, by a linear combination 
of smaller powers of x_i, using the relations g_i = ∏ s in (S i), (X i - C s) = 0. The resulting
polynomial \bar{f} is clearly of degree at most t_i in x_i, for each 1 ≤ i ≤ n, and is obtained from
f by subtracting from it products of the form h_i * g_i, where the degree of each polynomial 
h_i ∈ F[x_1 , ... , x_n] does not exceed deg(f) − deg(g_i)'.

-/

universe u

open set function finsupp add_monoid_algebra

open_locale big_operators

namespace mv_polynomial
open set function finsupp add_monoid_algebra

/-
  M' is a workaround for a "cannot sinthetize placeholder context error". How should I do this?
-/
private def M'  (n : ℕ ) (F : Type u) [field F] (S : fin n → finset F)
(hS : ∀ i : fin n, 0 < (S i).card)
: mv_polynomial (fin n) F → Prop :=
  λ f, ∃ h : fin n → mv_polynomial (fin n) F,
 (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ( ∀ m : fin n →₀ ℕ, m ∈ (f - (∑ i : fin n, h i * ∏ s in (S i), (X i - C s))).support → 
      ∀ j : fin n, m j < (S j).card)

private def M { n : ℕ } {F : Type u} [field F]{S : fin n → finset F}
  {hS : ∀ i : fin n, 0 < (S i).card} 
  : mv_polynomial (fin n) F → Prop := λ f, M' n F S hS f

local attribute [instance] classical.prop_decidable --esta permitido usar esto?

private lemma h_C { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) : ∀ (a : F), M' n F S hS (C a) :=
begin
  intro a,
  rw M',
  use λ i, 0,
  apply and.intro,
  intro i,
  left,
  refl,
  intros m hm j,
  have h: C a - ∑ (i : fin n), 0 * ∏ (s : F) in S i, (X i - C s) = C a,
  { have h1 : (λ i ,  0 * ∏ s in S i, (X i - C s)) = (λ i, 0),
    { ext,
      rw zero_mul },
    rw h1,
    simp, },
  rw h at hm,
  rw C_apply at hm,
  by_cases c : a = 0,
  { exfalso,
    rw c at hm,
    rw support_monomial at hm,
    simp only [finset.not_mem_empty, if_true, eq_self_iff_true] at hm,
    exact hm,
  },
  rw support_monomial at hm,
  rw if_neg at hm,
  have hm0 : m = 0 := finset.eq_of_mem_singleton hm,
  rw hm0,
  simp only [coe_zero, pi.zero_apply],
  exact hS j,
  exact c,
end

section aux_for_h_X

parameters {n : ℕ }{F : Type u} [field F] {S : fin n → finset F}
parameters {h: fin n → mv_polynomial (fin n) F} {hS: ∀ (i : fin n), 0 < (S i).card}
parameters {p: mv_polynomial (fin n) F}
parameters {j : fin n}
parameters {h_h: (∀ (i : fin n), h i = 0 ∨ (h i).total_degree + (S i).card ≤ p.total_degree) 
  ∧ ∀ (m : fin n →₀ ℕ), m ∈ (p - ∑ (i : fin n), h i * ∏ (s : F) in S i, (X i - C s)).support 
    → ∀ (j : fin n), m j < (S j).card}

parameter c_p_eq_0 : ¬p = 0


noncomputable def g : fin n → mv_polynomial (fin n) F := λ j : fin n, ∏ s in S j, (X j - C s)
noncomputable def f : mv_polynomial (fin n) F := (p - ∑ (i : fin n), h i * g i) * X j
noncomputable def ms : finset (fin n →₀ ℕ) := finset.filter (λ (m : fin n →₀ ℕ), m j = (S j).card) f.support
noncomputable def q : mv_polynomial (fin n) F := ∑ (m : fin n →₀ ℕ) in ms, (monomial (m - single j (S j).card)) (coeff m f)
noncomputable def h1 : fin n → mv_polynomial (fin n) F := λ (i : fin n), ite (i = j) (h j * X j - q) (h i * X j)

include c_p_eq_0 g f F ms q h1 S hS j p h_h h n 


lemma comp_1 : p * X j - ∑ (i : fin n), h1 i * g i = f - q * g j :=
begin
  sorry
end
include comp_1

lemma comp_2 : ∀ m, m ∈ ms → coeff m (f - q * g j) = 0 :=
begin
  sorry
end
include comp_2

lemma h_total_degree_f : total_degree f ≤ total_degree p + 1 :=
begin
  sorry -- use h_h
end
include h_total_degree_f

lemma h_total_degree_q : total_degree q + (S j).card ≤  total_degree p + 1 :=
begin
  -- use total_degree_sum, h_total_degree_f and the fact that
  -- each monomial m in the definition of q is in the support of f.
  sorry
end
include h_total_degree_q

lemma h_X_1 : (∀ (i : fin n), 
  h1 i = 0 ∨ (h1 i).total_degree + (S i).card ≤ (p * X j).total_degree) :=
begin
  intro i,
  by_cases c_h1_i_eq_0 : h1 i = 0,
  { left,
    exact c_h1_i_eq_0 },
  right,
  simp only [h1],
  rw total_degree_mul_X c_p_eq_0 j,
  have useful := (add_le_add_right (total_degree_mul_X_le (h i) j) (S i).card),
  by_cases c_i_eq_j : i = j,
  { rw if_pos c_i_eq_j,
    rw c_i_eq_j,
    have x := add_le_add_right (total_degree_add (h j * X j) (-q)) (S j).card,
    rw ← sub_eq_add_neg at x,
    have y : linear_order.max (h j * X j).total_degree (-q).total_degree +  (S j).card 
      ≤ p.total_degree + 1,
    { by_cases c_comp : (h j * X j).total_degree ≤ (-q).total_degree,
      { rw [max_eq_right c_comp, total_degree_neg],
        exact h_total_degree_q },
      simp only [not_le] at c_comp,
      rw max_eq_left c_comp.le,
      rw c_i_eq_j at useful,
      by_cases c_h_j_eq_0 : h j = 0,
      { rw [c_h_j_eq_0, zero_mul] at c_comp,
        simp only [nat.not_lt_zero, total_degree_zero] at c_comp,
        exfalso,
        exact c_comp },
      have y := add_le_add_right (what_is_the_name_for_this_one c_h_j_eq_0 (h_h.1 j)) 1,
      rw [add_assoc, add_comm (S j).card 1, ← add_assoc ] at y,
      exact useful.trans y },
    exact x.trans y },
  rw if_neg c_i_eq_j,
  have h_i_neq_0 : h i ≠ 0,
  { let x := c_h1_i_eq_0,
    simp only [h1] at x,
    by_contradiction,
    rw [if_neg c_i_eq_j, h, zero_mul] at x,
    cc },
  have y := add_le_add_right (what_is_the_name_for_this_one h_i_neq_0 (h_h.1 i)) 1,
  rw [add_assoc, add_comm (S i).card 1, ← add_assoc ] at y,
  exact useful.trans y,
end

lemma h_X_2 :
  ∀ (m : fin n →₀ ℕ), 
  m ∈ (p * X j - ∑ (i : fin n), h1 i * ∏ (s : F) in S i, (X i - C s)).support
  → ∀ (j : fin n), m j < (S j).card
:=
begin
  intros m hm i,
  by_contradiction h_m_i,
  rw comp_1 at hm,
  have m_mem_U := finset.mem_of_mem_of_subset hm (support_sub f (q * g j)),
  clear comp_1,
  by_cases c_m_in_sup_f : m ∈ f.support,
  { have x := support_mul_X j (p - ∑ (i : fin n), h i * g i),
    rw x at c_m_in_sup_f,
    clear x m_mem_U,
    simp only [exists_prop, add_right_embedding_apply, finset.mem_map] at c_m_in_sup_f,
     --mem_support_iff, ne.def, coeff_sub
    cases c_m_in_sup_f with m' h_m',
    have h_coeff_m' := h_m'.1,
    have h_m_m' := h_m'.2,
    clear h_m',
    have x := h_h.2 m' h_coeff_m' i,
    rw ← h_m_m' at h_m_i,
    simp only [pi.add_apply, not_lt, coe_add] at h_m_i,
    simp only [single] at h_m_i,
    simp only [coe_mk] at h_m_i,
    by_cases c_i_eq_j : i = j,
    { rw [if_pos c_i_eq_j.symm] at h_m_i,
      let x := sandwich x h_m_i,
      have h_m_in_ms : m ∈ ms,
      { sorry },
      have m_not_in_supp := comp_2 m h_m_in_ms,
      simp only [mem_support_iff, ne.def] at hm,
      tauto },
    have c_j_eq_i : ¬ j = i, cc,
    rw [ if_neg c_j_eq_i ] at h_m_i,
    linarith },
  have m_in_support_q_g_j := what_is_the_name_for_this_one c_m_in_sup_f (finset.mem_or_mem_of_mem_union m_mem_U),
  clear m_mem_U,
  sorry,
end
end aux_for_h_X

#check @comp_1


private lemma h_X { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
 (hS : ∀ i : fin n, 0 < (S i).card) :  ∀ (p : mv_polynomial (fin n) F) (j : fin n), 
    M' n F S hS p → M' n F S hS (p * X j) :=
begin
  intros p j h_Mp,
  cases h_Mp with h h_h,
  by_cases c_p_eq_0 : p = 0,
  { rw [ c_p_eq_0, zero_mul ], 
    rw c_p_eq_0 at h_h,
    rw M',
    use h,
    exact h_h },
  rw M',
  let g := λ j : fin n, ∏ s in S j, (X j - C s),
  let g_j := g j,
  let f := (p - ∑ (i : fin n), h i * g i) * X j ,
  let ms : finset (fin n →₀ ℕ) := f.support.filter (λ m , m j = (S j).card),
  let q : mv_polynomial (fin n) F := ∑ m in ms, monomial (m - (single j (S j).card)) (coeff m f),
  let h1 : fin n → mv_polynomial (fin n) F := λ i, if i = j then h j * X j - q else h i * X j,
  use h1,
  have comp_1 : p * X j - ∑ (i : fin n), h1 i * g i = f - q * g j,
  { sorry },
  have comp_2 : ∀ m, m ∈ ms → coeff m (f - q * g j) = 0,
  { sorry },
  have h_total_degree_f : total_degree f ≤ total_degree p + 1,
  { sorry }, -- use h_h
  have h_total_degree_q : total_degree q + (S j).card ≤  total_degree p + 1,
  { -- use total_degree_sum, h_total_degree_f and the fact that
    -- each monomial m in the definition of q is in the support of f.
    sorry },
  apply and.intro,
  intro i,
  by_cases c_h1_i_eq_0 : h1 i = 0,
  { left,
    exact c_h1_i_eq_0 },
  right,
  simp only [h1],
  rw total_degree_mul_X c_p_eq_0 j,
  have useful := (add_le_add_right (total_degree_mul_X_le (h i) j) (S i).card),
  by_cases c_i_eq_j : i = j,
  { rw if_pos c_i_eq_j,
    rw c_i_eq_j,
    have x := add_le_add_right (total_degree_add (h j * X j) (-q)) (S j).card,
    rw ← sub_eq_add_neg at x,
    have y : linear_order.max (h j * X j).total_degree (-q).total_degree +  (S j).card 
      ≤ p.total_degree + 1,
    { by_cases c_comp : (h j * X j).total_degree ≤ (-q).total_degree,
      { rw [max_eq_right c_comp, total_degree_neg],
        exact h_total_degree_q },
      simp only [not_le] at c_comp,
      rw max_eq_left c_comp.le,
      rw c_i_eq_j at useful,
      by_cases c_h_j_eq_0 : h j = 0,
      { rw [c_h_j_eq_0, zero_mul] at c_comp,
        simp only [nat.not_lt_zero, total_degree_zero] at c_comp,
        exfalso,
        exact c_comp },
      have y := add_le_add_right (what_is_the_name_for_this_one c_h_j_eq_0 (h_h.1 j)) 1,
      rw [add_assoc, add_comm (S j).card 1, ← add_assoc ] at y,
      exact useful.trans y },
    exact x.trans y },
  rw if_neg c_i_eq_j,
  have h_i_neq_0 : h i ≠ 0,
  { let x := c_h1_i_eq_0,
    simp only [h1] at x,
    by_contradiction,
    rw [if_neg c_i_eq_j, h, zero_mul] at x,
    cc },
  have y := add_le_add_right (what_is_the_name_for_this_one h_i_neq_0 (h_h.1 i)) 1,
  rw [add_assoc, add_comm (S i).card 1, ← add_assoc ] at y,
  exact useful.trans y,
  intros m hm i,
  by_contradiction h_m_i,
  rw comp_1 at hm,
  have m_mem_U := finset.mem_of_mem_of_subset hm (support_sub f (q * g j)),
  clear comp_1,
  by_cases c_m_in_sup_f : m ∈ f.support,
  { have x := support_mul_X j (p - ∑ (i : fin n), h i * g i),
    have c_m_in_sup_f' := c_m_in_sup_f,
    rw x at c_m_in_sup_f,
    clear x m_mem_U,
    simp only [exists_prop, add_right_embedding_apply, finset.mem_map] at c_m_in_sup_f,
     --mem_support_iff, ne.def, coeff_sub
    cases c_m_in_sup_f with m' h_m',
    have h_coeff_m' := h_m'.1,
    have h_m_m' := h_m'.2,
    clear h_m',
    have x := h_h.2 m' h_coeff_m' i,
    rw ← h_m_m' at h_m_i,
    simp only [pi.add_apply, not_lt, coe_add] at h_m_i,
    simp only [single] at h_m_i,
    simp only [coe_mk] at h_m_i,
    by_cases c_j_eq_i : j = i,
    { rw [if_pos c_j_eq_i] at h_m_i,
      let xeq := sandwich x h_m_i,
      have h_m_in_ms : m ∈ ms,
      { simp only [exists_prop, add_right_embedding_apply, finset.mem_map, finset.mem_filter ],
        apply and.intro,
        exact c_m_in_sup_f',
        rw ← h_m_m',
        simp only [single_eq_same, pi.add_apply, coe_add],
        rw c_j_eq_i,
        exact xeq.symm },
      have m_not_in_supp := comp_2 m h_m_in_ms,
      simp only [mem_support_iff, ne.def] at hm,
      tauto },
    rw [ if_neg c_j_eq_i ] at h_m_i,
    linarith },
  have m_in_support_q_g_j := what_is_the_name_for_this_one c_m_in_sup_f (finset.mem_or_mem_of_mem_union m_mem_U),
  clear m_mem_U,
  -- casos segun i = j
  -- el caso i ≠ j es facil
  sorry,
  /-
  have m_mem_U:= finset.mem_of_mem_of_subset hm (support_sub (p * X j) (∑ (i : fin n), h1 i * g i)),
  clear hm,
  by_cases c_m_in_ms : m ∈ ms,
  { -- arrive at a contradiction by showing the coefficient of m in f is 0
    sorry }, 
  by_cases c_m_in_pXj : m ∈ (p * (X j)).support,
  { -- show that m ∈ ms, contradiction!
    sorry },
  have m_in_supp_sum := what_is_the_name_for_this_one c_m_in_pXj (finset.mem_or_mem_of_mem_union m_mem_U),
  clear m_mem_U,
  have h_cases := support_sum (λ i : (fin n), h1 i * (g i)) m m_in_supp_sum,
  clear m_in_supp_sum,
  cases h_cases with k h_k,
  simp only [mem_support_iff, ite_mul, ne.def] at h_k,
  by_cases c_k_is_j : k = j,
  { rw if_pos c_k_is_j at h_k,
    -- show that m ∈ ms, contradiction!
    sorry },
  rw if_neg c_k_is_j at h_k,
  -- show that m ∈ ms, contradiction!
  -/
end

private lemma h_add_weak_aux_comp { n : ℕ } {F : Type u} [field F]
(S : fin n → finset F) (p q : mv_polynomial (fin n) F) 
(h1 h2 : fin n → mv_polynomial (fin n) F) : 
p + q - (∑ (i : fin n), (h1 + h2) i * (∏ (s : F) in S i, (X i - C s)))
= (p - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s))))
+ (q - (∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s)))) :=
calc p + q - (∑ (i : fin n), (h1 + h2) i * (∏ (s : F) in S i, (X i - C s)))
     = p + q - (∑ (i : fin n), (h1 i + h2 i) * (∏ (s : F) in S i, (X i - C s))) : by simp
...  = p + q - (∑ (i : fin n),(h1 i * (∏ (s : F) in S i, (X i - C s)) + h2 i * (∏ (s : F) in S i, (X i - C s)))) :
begin
  simp only [sub_right_inj],
  congr,
  ext,
  congr,
  rw add_mul,
end
...  = p + q - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s)) + ∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s))) :
by simp only [sub_right_inj,finset.sum_add_distrib]
...  = (p - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s))))
       + (q - (∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s)))) : 
by rw [← add_sub_assoc, ← sub_sub (p+q), sub_left_inj,sub_add_eq_add_sub]


private lemma h_add_weak { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) : 
∀ (a : fin n →₀ ℕ) (b : F) (f : mv_polynomial (fin n) F), 
    a ∉ f.support → b ≠ 0 → M' n F S hS f → M' n F S hS (single a b + f) :=
begin
  intros a b f h_a h_b h_Mf,
  cases h_Mf with h_f hh_f,
  have h_MCa := induction_on_monomial (h_C S hS) (h_X S hS) a b,
  cases h_MCa with h_Ca hhC_a,
  rw M',
  use h_Ca + h_f,
  apply and.intro,
  intro i,
  rw total_degree_add_monomial f a b h_a h_b,
  have re : ∀i,  (h_Ca + h_f) i = h_Ca i + h_f i,
  { intro i,
    simp,
  },
  rw re,
  by_cases h_Ca0 : h_Ca i = 0,
  { by_cases h_f0 : h_f i = 0,
    { left,
      rw [h_Ca0, h_f0],
      simp },
    right,
    rw h_Ca0,
    simp only [zero_add],
    have x : (h_f i).total_degree + (S i).card ≤ total_degree f,
    { have y := hh_f.1 i,
      cc },
    exact x.trans (le_max_right (total_degree (single a b)) (total_degree f)),
  },
  by_cases h_f0 : h_f i = 0,
  { right,
    rw h_f0,
    simp only [add_zero],
    have x : (h_Ca i).total_degree + (S i).card ≤ total_degree (single a b),
    { have y := hhC_a.1 i,
      have z : (h_Ca i).total_degree + (S i).card ≤ (monomial a b).total_degree := by cc,
      simpa using z },
    exact x.trans (le_max_left (total_degree (single a b)) (total_degree f)),
  },
  by_cases c : h_Ca i+ h_f i = 0,
  { left,
    exact c },
  right,
  have x := total_degree_add (h_Ca i) (h_f i),
  have y : (h_Ca i).total_degree + (S i).card ≤ total_degree (single a b) :=
    what_is_the_name_for_this_one h_Ca0 (hhC_a.1 i),
  have z : (h_f i).total_degree + (S i).card ≤ total_degree f :=
    what_is_the_name_for_this_one h_f0 (hh_f.1 i),
  have x' := add_le_add_right x (S i).card,
  rw max_add at x',
  exact x'.trans (max_le_le y z),
  intros m hm j,
  have hh_fm := hh_f.2 m,
  have hC_am := hhC_a.2 m,
  clear hh_f hhC_a,
  -- we now use support_add and our hypotheses
  have comp := h_add_weak_aux_comp S (monomial a b) f h_Ca h_f,
  simp at comp,
  have hm' : m ∈ ((monomial a b - (∑ (i : fin n), h_Ca i * (∏ (s : F) in S i, (X i - C s))))
    + (f - (∑ (i : fin n), h_f i * (∏ (s : F) in S i, (X i - C s))))).support,
  { rw ← comp,
    exact hm },
  have t := support_add hm',
  -- can we use rcases or something else here?
  by_cases c : m ∈  (monomial a b - (∑ (i : fin n),
   h_Ca i * (∏ (s : F) in S i, (X i - C s)))).support,
  { exact hC_am c j },
  have c' : m ∈ (f - (∑ (i : fin n), h_f i * (∏ (s : F) in S i, (X i - C s)))).support,
  { rw finset.mem_union at t,
    exact what_is_the_name_for_this_one c t,
  },
  exact hh_fm c' j,
end

lemma reduce_degree { n : ℕ } {F : Type u} [field F]
  (S : fin n → finset F) (hS : ∀ i : fin n, 0 < (S i).card)
  (f : mv_polynomial (fin n) F) :
  ∃ h : fin n → mv_polynomial (fin n) F,
  (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ( ∀ m : fin n →₀ ℕ, m ∈ (f - (∑ i : fin n, h i * ∏ s in S i, (X i - C s))).support → 
      ∀ j : fin n, m j < (S j).card) := 
begin
  have h : M f,
  { apply induction_on'' f,
    apply h_C S hS,
    apply h_add_weak S hS,
    apply h_X S hS },
  rw M at h, rw M' at h,
  exact h,
end

end mv_polynomial