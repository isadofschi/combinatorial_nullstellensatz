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
  ∧ ∀ j : fin n, degree_of j (f - (∑ i : fin n, h i * ∏ s in S i, (X i - C s))) < (S j).card

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
  intro j,
  have h: C a - ∑ (i : fin n), 0 * ∏ (s : F) in S i, (X i - C s) = C a,
  { have h1 : (λ i ,  0 * ∏ s in S i, (X i - C s)) = (λ i, 0),
    { ext,
      rw zero_mul },
    rw h1,
    simp, },
  rw h,
  rw degree_of_C,
  exact hS j,
end

namespace hX 
open set function finsupp add_monoid_algebra mv_polynomial

noncomputable theory

local attribute [instance] classical.prop_decidable

section h_X

variables {n : ℕ }
{F : Type u} [field F] {S : fin n → finset F}
{hS : ∀ i : fin n, 0 < (S i).card}

abbreviation g : fin n → mv_polynomial (fin n) F := λ (j : fin n), ∏ (s : F) in S j, (X j - C s)
#check @g n F _ S

variables {j :fin n}

variables {p : mv_polynomial (fin n) F}

variables {h : fin n → mv_polynomial (fin n) F}

variables {h_h : (∀ (i : fin n), h i = 0 
  ∨ (h i).total_degree + (S i).card ≤ p.total_degree) 
  ∧ ∀ (j : fin n),
 degree_of j (p - ∑ (i : fin n), h i * @g n F _ S i) < (S j).card }

variables {c_p_eq_0 : ¬p = 0}

abbreviation p1: mv_polynomial (fin n) F := 
  (p - ∑ (i : fin n), h i * @ g n F _ S i)
#check @p1 n F _ S j h

abbreviation f: mv_polynomial (fin n) F :=
 (p - ∑ (i : fin n), h i * @ g n F _ S i) * X j
#check @f n F _ S j p h

abbreviation ms: finset (fin n →₀ ℕ) :=
  finset.filter (λ (m : fin n →₀ ℕ), m j = (S j).card) (@f n F _ S j p h).support
#check @ms  n F _ S j p h

def q: mv_polynomial (fin n) F :=
  ∑ (m : fin n →₀ ℕ) in (@ms  n F _ S j p h), (monomial (m - single j (S j).card)) (coeff m (@f n F _ S j p h))
#check @q n F _ S j p h

def h1: fin n → mv_polynomial (fin n) F :=
   λ (i : fin n), ite (i = j) (h j * X j - (@q n F _ S j p h)) (h i * X j)
#check @h1 n F _ S j p h

lemma prop_ms (m : fin n →₀ ℕ):  m ∈ (@ms  n F _ S j p h) →  m j = (S j).card := sorry
#check @prop_ms n F _ S j p h

lemma exists_m1 {m : fin n →₀ ℕ} (h_m : m ∈ (@q n F _ S j p h).support):
  ∃ m1 : (fin n →₀ ℕ),
   m1 ∈ (@ms n F _ S j p h)  ∧ m = m1 - (single j (S j).card) := sorry
#check @exists_m1 n F _ S j p h

lemma comp_1:  p * X j - ∑ (i : fin n), (@h1 n F _ S j p h) i * (@g n F _ S) i = (@f n F _ S j p h
) - (@q n F _ S j p h) *  (@g n F _ S) j
:=
begin
  sorry
end
#check @comp_1 n F _ S j p h

lemma comp_2 : ∀ m, m ∈ (@ms  n F _ S j p h) → coeff m (@f n F _ S j p h) = coeff m ((@q n F _ S j p h) * (@g n F _ S) j)
:=begin
  sorry
end
#check @comp_2 n F _ S j p h

include h_h
lemma h_total_degree_f : total_degree (@f n F _ S j p h) ≤ total_degree p + 1 :=
begin
  sorry -- use h_h
end
#check @h_total_degree_f n F _ S j p h h_h
omit h_h

lemma h_total_degree_q : total_degree (@q n F _ S j p h) + (S j).card ≤  total_degree p + 1 :=
begin
  -- use total_degree_sum, h_total_degree_f and the fact that
  -- each monomial m in the definition of q is in the support of f.
  sorry
end
#check @h_total_degree_q n F _ S j p h

include h_h
lemma H_f : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ (@f n F _ S j p h).support → ((S i).card ≤ m i) → coeff m (@f n F _ S j p h) = coeff m ((@q n F _ S j p h) * (@g n F _ S) j)
:= begin
   intros i m h_m_in_supp_f h_S,
    let ms := @ms n F _ S j p h,
    have x : degree_of i p1 < (S i).card := h_h.2 i,
    have z := should_be_in_mathlib i h_m_in_supp_f,
    by_cases c_i_eq_j : i = j,
    { have h_m_in_ms : m ∈ ms,
      { have y := degree_of_mul_X_eq j p1,
        rw c_i_eq_j at x,
        rw c_i_eq_j at h_S,
        rw c_i_eq_j at z,
        have w := sandwich' h_S ( lt_of_le_of_lt (z.trans y) (add_lt_add_right x 1) ),
        simp only [exists_prop, add_right_embedding_apply, finset.mem_map, 
        finset.mem_filter, coeff_sub],
        exact ⟨h_m_in_supp_f , w.symm⟩ },
      exact comp_2 m h_m_in_ms },
    have y := degree_of_mul_X_ne  p1 c_i_eq_j,
    rw ← y at x, clear y,
    exfalso,
    linarith,
end
omit h_h
#check @H_f n F _ S j p h h_h

include h_h
lemma H_g : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ ((@q n F _ S j p h) * (@g n F _ S) j).support → ((S i).card ≤ m i) → coeff m (@f n F _ S j p h) = coeff m ((@q n F _ S j p h) * (@g n F _ S) j) := 
begin
  intros i m m_in_support_q_g_j h_S,
  let ms := @ms n F _ S j p h,
  have exists_m'_m'' := support_mul' m m_in_support_q_g_j,
  cases exists_m'_m'' with m' h_m',
  cases h_m' with m'' h_m_m'_m'',
  have h_m'_in_supp_q := h_m_m'_m''.1,
  have h_m''_in_supp_gj := h_m_m'_m''.2.1,
  have h_m_eq_m'_add_m'' := h_m_m'_m''.2.2,
  clear h_m_m'_m'',
  have h_mi_eq_mi'_add_mi'' : m i = m' i + m'' i,
  { rw h_m_eq_m'_add_m'',
    refl },
  have exists_m1 := (@exists_m1 n F _ S j p h m') h_m'_in_supp_q,
  cases exists_m1 with m1 h0m1,
  cases h0m1 with h_m1 h_m'_m1,
  by_cases c_i_eq_j : j = i,
  { have h_m_in_ms : m ∈ ms,
    { have x : m'' j ≤ (S j).card := mv_polynomial.lemita7 h_m''_in_supp_gj,
      rw ← c_i_eq_j at h_S,
      rw ← c_i_eq_j at h_mi_eq_mi'_add_mi'',
      have h_m'_m1_j : m' j = m1 j - (S j).card,
      { rw h_m'_m1,
        simp only [single_eq_same, coe_tsub, pi.sub_apply] },
      have h_S' := add_le_add_left h_S (m' j),
      have m1_j : m1 j = (S j).card := prop_ms m1 h_m1,
      have m'_j_eq_0 : m' j = 0,
      { rw h_m'_m1_j,
        exact nat.sub_eq_zero_of_le (le_of_eq m1_j) },
      have h : m j ≤ (S j).card,
      { rw h_mi_eq_mi'_add_mi'',
        rw m'_j_eq_0,
        rw zero_add,
        exact x },
      have h' : m j = (S j).card := eq_of_le_of_le h h_S,
      have x' : m'' j = (S j).card, {
        rw ←  h',
        rw h_m_eq_m'_add_m'',
        simpa using m'_j_eq_0 },
      have h'' : m'' = single j (S j).card := lemita5 h_m''_in_supp_gj x',
      have h_m_eq_m1 : m = m1,
      { rw [h_m_eq_m'_add_m'', h_m'_m1, h''],
        ext,
        by_cases c : j = a,
        { rw ← c,
          simp only [single_eq_same, pi.add_apply, coe_tsub, coe_add, pi.sub_apply],
          rw m1_j,
          simp },
        simp only [pi.add_apply, coe_tsub, coe_add, pi.sub_apply],
        rw single,
        rw coe_mk,
        rw if_neg c,
        simp },
      rw h_m_eq_m1,
      exact h_m1 },
    exact comp_2 m h_m_in_ms },
  -- case i ≠ j
  have h_m''_i : m'' i = 0 := lemita6 h_m''_in_supp_gj c_i_eq_j,
  have h' : m' i = m1 i,
  { rw [h_m'_m1, single],
    simp only [coe_mk, coe_tsub, pi.sub_apply, if_neg c_i_eq_j, tsub_zero] },
  have h'' : m1 i < (S i).card,
  { have c_i_eq_j' : ¬ i = j := ne_symm c_i_eq_j,
    have x := h_h.2 i,
    have x' := degree_of_mul_X_ne (p - ∑ (i : fin n), h i * g i) c_i_eq_j',
    rw ← x' at x, clear x',
    apply mv_polynomial.eee'.2 x m1,
    simp,
    simp [ms] at h_m1,
    exact h_m1.1 },
  exfalso,
  linarith,
  exact m,
end
omit h_h

include c_p_eq_0 h_h 
lemma h_X_1 :
  ∀ (i : fin n),
  (@h1 n F _ S j p h) i = 0 ∨ ((@h1 n F _ S j p h) i).total_degree + (S i).card
  ≤ (p * X j).total_degree
:= begin
  let h1 : fin n → mv_polynomial (fin n) F := @h1 n F _ S j p h,
  intro i,
  by_cases c_h1_i_eq_0 : h1 i = 0,
  { left,
    exact c_h1_i_eq_0 },
  right,
  simp only [hX.h1],
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
        exact (@h_total_degree_q n F _ S j p h) },
      simp only [not_le] at c_comp,
      rw max_eq_left c_comp.le,
      rw c_i_eq_j at useful,
      by_cases c_h_j_eq_0 : h j = 0,
      { rw [c_h_j_eq_0, zero_mul] at c_comp,
        simp only [nat.not_lt_zero, total_degree_zero] at c_comp,
        exfalso,
        exact c_comp },
      have y := add_le_add_right (right_of_not_of_or c_h_j_eq_0 (h_h.1 j)) 1,
      rw [add_assoc, add_comm (S j).card 1, ← add_assoc ] at y,
      exact useful.trans y },
    exact x.trans y },
  simp only [hX.h1, if_neg c_i_eq_j],
  have h_i_neq_0 : h i ≠ 0,
  { let x := c_h1_i_eq_0,
    simp only [h1] at x,
    by_contradiction,
    simp only [hX.h1, if_neg c_i_eq_j, h, zero_mul] at x,
    cc },
  have y := add_le_add_right (right_of_not_of_or h_i_neq_0 (h_h.1 i)) 1,
  rw [add_assoc, add_comm (S i).card 1, ← add_assoc ] at y,
  exact useful.trans y,
end
omit c_p_eq_0 h_h
#check @h_X_1 n F _ S j p h h_h c_p_eq_0

include h_h
lemma h_X_2 :
∀ (j_1 : fin n),
degree_of j_1 (p * X j - ∑ (i : fin n), (@h1 n F _ S j p h) i * ∏ (s : F) in S i, (X i - C s)) < (S j_1).card
:=
begin
  intro i,
  have H_f : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ f.support → ((S i).card ≤ m i) → coeff m f = coeff m (q * g j)
    := @H_f n F _ S j p h h_h,
  have H_g : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ (q * g j).support → ((S i).card ≤ m i) → coeff m f = coeff m (q * g j)
    := @H_g n F _ S j p h h_h,
  rw @comp_1 n F _ S j p h,
  exact degree_of_sub_aux i f (q * g j) (S i).card (H_f i) (H_g i),
end
omit h_h
#check @h_X_2 n F _ S j p h h_h

lemma h_X :
 ∀ (p : mv_polynomial (fin n) F) (j : fin n), M' n F S hS p → M' n F S hS (p * X j) :=
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
  use @h1 n F _ S j p h,
  apply and.intro,
  exact @h_X_1 n F _ S j p h h_h c_p_eq_0,
  exact @h_X_2 n F _ S j p h h_h,
end

end h_X

end hX

private lemma h_X { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
 (hS : ∀ i : fin n, 0 < (S i).card) :  ∀ (p : mv_polynomial (fin n) F) (j : fin n), 
    M' n F S hS p → M' n F S hS (p * X j) := hX.h_X


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
    right_of_not_of_or h_Ca0 (hhC_a.1 i),
  have z : (h_f i).total_degree + (S i).card ≤ total_degree f :=
    right_of_not_of_or h_f0 (hh_f.1 i),
  have x' := add_le_add_right x (S i).card,
  rw max_add at x',
  exact x'.trans (max_le_le y z),
  intro j,
  rw [ h_add_weak_aux_comp S (single a b) f h_Ca h_f],
  exact lt_of_le_of_lt (degree_of_add_le j _ _) (max_lt (hhC_a.2 j) (hh_f.2 j)),
end

lemma reduce_degree { n : ℕ } {F : Type u} [field F]
  (S : fin n → finset F) (hS : ∀ i : fin n, 0 < (S i).card)
  (f : mv_polynomial (fin n) F) :
  ∃ h : fin n → mv_polynomial (fin n) F,
  (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ∀ j : fin n, 
  degree_of j (f - (∑ i : fin n, h i * ∏ s in S i, (X i - C s))) < (S j).card := 
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