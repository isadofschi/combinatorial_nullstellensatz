/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.algebra.basic
import degree
import degree_new
import lemmas_g_S
import assorted_lemmas

/-
# Reduce degree

## Main results

- `reduce_degree`: Let F be a field and Sᵢ be finite nonempty subsets of $F$,
   defined for i ∈ {0, … , n - 1}. Let f ∈ F[x₀, … x_₁]. Let gᵢ = ∏ (xᵢ - s)
   where the product is taken over s ∈ Sᵢ.Then there are polynomials 
   hᵢ ∈ F[x₀, … x_₁] such that:
   (i) For each i, either hᵢ = 0 or deg hᵢ + |Sᵢ| ≤ deg f.
  (ii) For each j, the degⱼ (f - ∑ᵢ hᵢ gᵢ) < |Sⱼ|.

This corresponds to the following paragraph in the proof of Theorem 1.1 in Alon's
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
private def M' (R σ : Type*) [comm_ring R] [is_domain R] [fintype σ]
  (g : σ → mv_polynomial σ R)
  (hg : ∀ i : σ, g i ∈ supported R ({i} : set σ))
  (hS : ∀ i : σ, 0 < total_degree (g i))
  (hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1)
: mv_polynomial σ R → Prop :=
  λ f, ∃ h : σ → mv_polynomial σ R,
  (∀ i : σ, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
  ∧ ∀ i : σ,  degree_of i (f - (∑ j : σ, h j * g j)) < total_degree (g i)

private def M {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  {g : σ → mv_polynomial σ R}
  {hg : ∀ i : σ, g i ∈ supported R ({i} : set σ)}
  {hS : ∀ i : σ, 0 < total_degree (g i)}
  {hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1}
  : mv_polynomial σ R → Prop := λ f, M' R σ g hg hS hm f

local attribute [instance] classical.prop_decidable

private lemma h_C {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  (g : σ → mv_polynomial σ R)
  (hg : ∀ (i : σ), g i ∈ supported R {i})
  (hS : ∀ (i : σ), 0 < (g i).total_degree)
  (hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1)
 : ∀ (a : R), M' R σ g hg hS hm (C a) :=
begin
  intro a,
  rw M',
  use λ i, 0,
  simp only [true_and, zero_mul, implies_true_iff, true_or, eq_self_iff_true, sub_zero, 
             finset.sum_const_zero, degree_of_C],
  exact hS,
end

noncomputable theory

local attribute [instance] classical.prop_decidable

section h_X
/-
  This section contains the main steps in the proof of h_X
-/

variables {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
{g : σ → mv_polynomial σ R}
{hg : ∀ i : σ, g i ∈ supported R ({i} : set σ)}
{hS : ∀ i : σ, 0 < total_degree (g i)}
{hmonic : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1}
{j :σ} {p : mv_polynomial σ R} {h : σ → mv_polynomial σ R}
{h_h : (∀ (i : σ), h i = 0 
  ∨ (h i).total_degree + (g i).total_degree ≤ p.total_degree) 
  ∧ ∀ (j : σ),
 degree_of j (p - ∑ (i : σ), h i * g i) < (g j).total_degree }
{c_p_eq_0 : ¬p = 0}

private abbreviation p1: mv_polynomial σ R :=  (p - ∑ (i : σ), h i * g i)

private abbreviation f: mv_polynomial σ R := (p - ∑ (i : σ), h i * g i) * X j

private abbreviation ms: finset (σ →₀ ℕ) :=
  finset.filter (λ (m : σ →₀ ℕ), m j = (g j).total_degree) (@f R σ _ _ _ g j p h).support

private def q: mv_polynomial σ R :=
  ∑ (m : σ →₀ ℕ) in @ms R σ _ _ _ g j p h, (monomial (m - single j (g j).total_degree)) (coeff m (@f R σ _ _ _ g j p h))

private def h1: σ → mv_polynomial σ R := (λ i,  h i * (X j)) + single j  (@q R σ _ _ _ g j p h)

private lemma prop_ms (m : σ →₀ ℕ):  m ∈ (@ms R σ _ _ _ g j p h) →  m j = (g j).total_degree := 
begin
  intro h_m,
  simp only [exists_prop, add_right_embedding_apply, finset.mem_map, support_mul_X, 
             mem_support_iff, ne.def, finset.mem_filter, coeff_sub] at h_m,
  exact h_m.2,
end

private lemma prop_ms'' (m : σ →₀ ℕ):  m ∈ (@ms R σ _ _ _ g j p h) →  m ∈ (@f R σ _ _ _ g j p h).support :=
begin
  intro h,
  rw finset.mem_filter at h,
  exact h.1,
end

private lemma prop_ms' (m : σ →₀ ℕ):  m ∈ (@ms R σ _ _ _ g j p h) →  coeff m (@f R σ _ _ _ g j p h) ≠ 0 :=
begin
  intro h,
  rw ← mem_support_iff,
  apply prop_ms'',
  exact h,
end

private lemma q_eq_zero_of_ms_empty (h' : (@ms R σ _ _ _ g j p h) = ∅) : (@q R σ _ _ _ g j p h) = 0 :=
by simp [q, h']

private lemma exists_m1 {m : σ →₀ ℕ} (h_m : m ∈ (@q R σ _ _ _ g j p h).support):
  ∃ m1 : (σ →₀ ℕ),
   m1 ∈ (@ms R σ _ _ _ g j p h)  ∧ m = m1 - (single j (g j).total_degree) := 
begin
  rw q at h_m,
  have h_m' := support_sum h_m,
  rw [←finset.sup_eq_bUnion, finset.mem_sup] at h_m',
  cases h_m' with m1 h_m1',
  cases h_m1' with H h_m1,
  use m1,
  apply and.intro,
  { exact H },
  { simp only [exists_prop, mem_support_iff, coeff_monomial, ite_eq_right_iff, ne.def, not_forall] at h_m1,
  exact h_m1.1.symm },
end

include h_h
private lemma comp_1:
  p * X j - ∑ (i : σ), (@h1 R σ _ _ _ g j p h) i * g i 
  = (@f R σ _ _ _ g j p h) - (@q R σ _ _ _ g j p h) *  g j :=
begin
  rw h1,
  ext,
  simp only [coeff_sub, coeff_sum, coeff_mul_X'],
  let q := @q R σ _ _ _ g j p h,
  by_cases c_j_m : j ∈ m.support,
  { simp only [if_pos, c_j_m, pi.add_apply, coeff_sub, sub_sub],
    congr,
    suffices h : (λ x, coeff m ((h x * X j + single j q x) * g x ))
      = (λ x, coeff (m - single j 1) (h x * g x))
      + single j (coeff m (q * g j)),
    { rw h,
      simp, -- nonterminal simp
      rw finset.sum_add_distrib,
      congr,
      rw finsupp.sum_single' j },
    ext,
    rw [pi.add_apply, add_mul, coeff_add, mul_assoc, mul_comm (X j) (g x), ← mul_assoc, coeff_mul_X'],
    simp only [if_pos, c_j_m],
    congr,
    by_cases c_x : j = x,
    { rw [←c_x, finsupp.single_eq_same, finsupp.single_eq_same] },
    { simp [finsupp.single_eq_of_ne c_x] } },
  { simp only [if_neg, c_j_m, zero_sub, pi.add_apply, neg_inj, not_false_iff],
    suffices h : (λ x, coeff m ((h x * X j + single j q x) * g x )) = single j (coeff m (q * g j)),
    by rw [h, finsupp.sum_single' j],
    ext,
    simp only [add_mul, coeff_add, mul_assoc, mul_comm (X j) (g x)],
    simp only [← mul_assoc, coeff_mul_X', if_neg, c_j_m, zero_add, not_false_iff],
    by_cases c_x : j = x,
    { rw [←c_x, finsupp.single_eq_same, finsupp.single_eq_same] },
    { simp [finsupp.single_eq_of_ne c_x] } },
end
omit h_h

include hg
private lemma comp_2_aux :
  ∀ m m' ∈ (@ms R σ _ _ _ g j p h), m ≠ m' →  coeff m ((monomial (m' - single j (g j).total_degree)) (coeff m' (@f R σ _ _ _ g j p h)) * g j) = 0 :=
begin
 intros m m' hm h_m'_in_ms h_m_ne_m',
  by_cases c_m_m' : m' ≤ m,
  { rw [coeff_monomial_mul', mul_eq_zero_of_right],
    simp,
    have x' := (lt_of_le_of_ne c_m_m' h_m_ne_m'.symm).2,
    simp only [not_le, not_forall] at x',
    cases x' with x hx,
    have h : j ≠ x,
    { by_contradiction h,
      rw [←h, prop_ms m hm, prop_ms m' h_m'_in_ms] at hx,
      simpa using hx },
    have h' : (m - (m' - single j (g j).total_degree)) x ≠ 0,
    { simpa only [tsub_eq_zero_iff_le, not_le, ne.def, coe_tsub, pi.sub_apply,
                  single_eq_of_ne h] },
    rw g_S_lem_6' (hg j) h' h.symm },
  rw coeff_monomial_mul',
  apply if_neg,
  by_contradiction c,
  simp only [finsupp.le_def, not_le, not_forall] at c_m_m',
  cases c_m_m' with x hx,
  have h : j ≠ x,
  { by_contradiction h,
    rw [←h , prop_ms m hm, prop_ms m' h_m'_in_ms] at hx,
    simpa using hx,},
  rw finsupp.le_def at c,
  have cx := c x,
  simp only [tsub_le_iff_right, coe_tsub, pi.sub_apply, finsupp.single_eq_of_ne h,
             add_zero] at cx,
  simpa using lt_of_le_of_lt cx hx,
end
omit hg

include hmonic hg
private lemma comp_2 : ∀ m, m ∈ (@ms R σ _ _ _ g j p h) → coeff m (@f R σ _ _ _ g j p h) = coeff m ((@q R σ _ _ _ g j p h) * g j)
:=begin
  intros m hm,
  rw q,
  rw finset.sum_mul,
  rw coeff_sum ms,
  let f := @f R σ _ _ _ g j p h,
  let ms := @ms R σ _ _ _ g j p h,
  let f' :  (σ →₀ ℕ) → R := λ (x : σ →₀ ℕ), coeff m ((monomial (x - single j (g j).total_degree)) (coeff x f) * g j),
  let g' :  (σ →₀ ℕ) → R := (single  m  (coeff m f)),  
  have h''' : m - (m - single j (g j).total_degree) = single j (g j).total_degree,
  { ext,
    simp only [coe_tsub, pi.sub_apply],
    by_cases c : j = a,
    { simp [←c, prop_ms m hm] },
    { simp [single_eq_of_ne c] } },
  have h' : coeff m ((monomial (m - single j (g j).total_degree)) (coeff m f) * g j) = coeff m f,
  { simp only [coeff_monomial_mul', h''', tsub_le_self, if_true, hmonic j, mul_one] },
  have h: ∀ (x : σ →₀ ℕ), x ∈ ms → f' x = g' x,
  { intros m' hm',
    simp only [f',g'],
    by_cases c : m = m',
    { rw [c, finsupp.single_eq_same, ←c, h'] },
    { rw finsupp.single_eq_of_ne c,
      apply comp_2_aux m m' hm hm' c,
      exact hg } },
  simp only [@finset.sum_congr R (σ →₀ ℕ) ms ms f' g' _ (by refl) h, g', finsupp.sum_single'' hm],
end
omit hmonic hg

include h_h
private lemma h_total_degree_f : total_degree (@f R σ _ _ _ g j p h) ≤ total_degree p + 1 :=
begin
  apply (@total_degree_mul_X_le R _ _ _ p1 j).trans,
  apply add_le_add_right ∘ (total_degree_sub p (∑ (i : σ), h i * g i)).trans, 
  by_cases hc : p.total_degree ≤ (∑ (i : σ), h i * g i).total_degree,
  { rw max_eq_right hc,
    apply (total_degree_sum _ (λ i,  h i * g i)).trans ∘ finset.sup_le,
    intros i hi,
    by_cases c : h i = 0,
    { simp [c] },
    { exact (total_degree_mul (h i) (g i)).trans (or.resolve_left (h_h.1 i) c) } },
  { rw not_le at hc,
    rw max_eq_left hc.le },
end
omit h_h

include h_h
private lemma h_total_degree_q : (¬ (@ms R σ _ _ _ g j p h) = ∅ ) 
  →  total_degree (@q R σ _ _ _ g j p h) + (g j).total_degree ≤  total_degree p + 1 :=
begin
  intro h_ms,
  have c_ms_nonempty : ms.nonempty,
  { apply finset.nonempty_of_ne_empty,
    simpa using h_ms },
  rw q,
  apply (add_le_add_right (total_degree_sum ms (λ m, (monomial (m - single j (g j).total_degree)) (coeff m f) )) (g j).total_degree).trans,
  cases finset.exists_mem_eq_sup ms c_ms_nonempty 
    (λ (m : σ →₀ ℕ), ((monomial (m - single j (g j).total_degree)) (coeff m f)).total_degree) with m hm,
  cases hm with h_m_in_ms h_sup_f_eq_f_m,
  rw h_sup_f_eq_f_m,
  simp only,
  rw [total_degree_monomial_eq_monomial_degree (prop_ms' m h_m_in_ms), monomial_degree_sub, monomial_degree_single],
  { suffices x : monomial_degree m - (g j).total_degree + (g j).total_degree = monomial_degree m,
    by simpa [x] using
      le_trans (monomial_degree_le_total_degree (prop_ms'' m h_m_in_ms)) (@h_total_degree_f R σ _ _ _ g j p h h_h),
    rw nat.sub_add_cancel,
    rw ←prop_ms m h_m_in_ms,
    exact le_monomial_degree m j },
  { rw finsupp.le_def,
    intro i,
    by_cases c : i = j,
    { simp [c, prop_ms m h_m_in_ms] },
    { rw single_eq_of_ne,
      { exact zero_le (m i) },
      { symmetry,
        exact c } } },
  end
omit h_h

include h_h hg hmonic
private lemma H_f : ∀ i (m : σ →₀ ℕ),
    m ∈ (@f R σ _ _ _ g j p h).support → ((g i).total_degree ≤ m i) →
      coeff m (@f R σ _ _ _ g j p h) = coeff m ((@q R σ _ _ _ g j p h) * g j)
:= begin
   intros i m h_m_in_supp_f h_S,
    let ms := @ms R σ _ _ _ g j p h,
    have x : degree_of i p1 < (g i).total_degree := h_h.2 i,
    have z := monomial_le_degree_of i h_m_in_supp_f,
    by_cases c_i_eq_j : i = j,
    { suffices h_m_in_ms : m ∈ ms,
      { convert comp_2 m h_m_in_ms,
        { exact hg },
        { exact hmonic } },
      rw c_i_eq_j at x,
      rw c_i_eq_j at h_S,
      rw c_i_eq_j at z,
      have w := nat.eq_of_le_of_lt_succ h_S ( lt_of_le_of_lt (z.trans (@degree_of_mul_X_eq R _ _ j p1)) 
        (add_lt_add_right x 1) ),
      simp only [exists_prop, add_right_embedding_apply, finset.mem_map, 
      finset.mem_filter, coeff_sub],
      exact ⟨h_m_in_supp_f , w⟩ },
    { have y := degree_of_mul_X_ne p1 c_i_eq_j,
      rw ← y at x,
      exfalso,
      linarith },
end
omit h_h hg hmonic

include h_h hS hg hmonic
private lemma H_g : ∀ i (m : σ →₀ ℕ), m ∈ ((@q R σ _ _ _ g j p h) * g j).support 
  → ((g i).total_degree ≤ m i) 
  → coeff m (@f R σ _ _ _ g j p h) = coeff m ((@q R σ _ _ _ g j p h) * g j) := 
begin
  intros i m m_in_support_q_g_j h_S,
  let ms := @ms R σ _ _ _ g j p h,
  cases support_mul'' m_in_support_q_g_j with m' h_m',
  cases h_m' with m'' h_m_m'_m'',
  have h_m'_in_supp_q := h_m_m'_m''.1,
  have h_m''_in_supp_gj := h_m_m'_m''.2.1,
  have h_m_eq_m'_add_m'' := h_m_m'_m''.2.2.symm,
  clear h_m_m'_m'',
  have h_mi_eq_mi'_add_mi'' : m i = m' i + m'' i,
  { rw h_m_eq_m'_add_m'',
    refl },
  cases (@exists_m1 R σ _ _ _ g j p h m') h_m'_in_supp_q with m1 h0m1,
  cases h0m1 with h_m1 h_m'_m1,
  by_cases c_i_eq_j : j = i,
  { apply comp_2 m,
    { rw ← c_i_eq_j at h_S,
      rw ← c_i_eq_j at h_mi_eq_mi'_add_mi'',
      suffices h_m_eq_m1 : m = m1,
      { rwa h_m_eq_m1 },
      have h_m'_m1_j : m' j = m1 j - (g j).total_degree := 
        by simp only [h_m'_m1, single_eq_same, coe_tsub, pi.sub_apply],
      have m1_j : m1 j = (g j).total_degree := prop_ms m1 h_m1,
      have m'_j_eq_0 : m' j = 0 :=
        by simpa only [h_m'_m1_j] using nat.sub_eq_zero_of_le (le_of_eq m1_j),
      have h : m j ≤ (g j).total_degree,
      { rw [h_mi_eq_mi'_add_mi'', m'_j_eq_0, zero_add],
        exact mv_polynomial.le_total_degree h_m''_in_supp_gj },
      have x' : m'' j = (g j).total_degree,
      { by simpa [← nat.le_antisymm h h_S, h_m_eq_m'_add_m''] using m'_j_eq_0 },
      rw [h_m_eq_m'_add_m'', h_m'_m1, @g_S_lem_5 R σ _ j _ (g j) h_m''_in_supp_gj x'],
      ext,
      by_cases c : j = a,
      { simp [←c, m1_j] },
      { simp  [pi.add_apply, coe_tsub, coe_add, pi.sub_apply, single, coe_mk, if_neg c] } },
    { exact hg },
    { exact hmonic } },
  { have h_m''_i : m'' i = 0 := g_S_lem_6 (hg j) h_m''_in_supp_gj c_i_eq_j,
    have h' : m' i = m1 i := 
      by simp only [h_m'_m1, single, coe_mk, coe_tsub, pi.sub_apply, if_neg c_i_eq_j, tsub_zero],
    suffices h'' : m1 i < (g i).total_degree,
    { exfalso, linarith },
    { have x := h_h.2 i,
      apply (mv_polynomial.degree_of_lt_iff (hS i)).1 
        (by rwa degree_of_mul_X_ne (p - ∑ (i : σ), h i * g i) (not_eq_symm c_i_eq_j)) m1,
      simp only [exists_prop, add_right_embedding_apply, finset.mem_map, support_mul_X, 
                mem_support_iff, ne.def, finset.mem_filter, coeff_sub] at h_m1,
      simpa only [exists_prop, add_right_embedding_apply, finset.mem_map, support_mul_X, 
                mem_support_iff, ne.def, coeff_sub] using h_m1.1 } },
end
omit h_h hS hg hmonic

include c_p_eq_0 h_h 
private lemma h_X_1 :
  ∀ (i : σ),
  (@h1 R σ _ _ _ g j p h) i = 0 ∨ ((@h1 R σ _ _ _ g j p h) i).total_degree + (g i).total_degree
  ≤ (p * X j).total_degree
:= begin
  intro i,
  by_cases c_h1_i_eq_0 : h1 i = 0,
  { left,
    exact c_h1_i_eq_0 },
  { right,
    simp only [h1],
    rw total_degree_mul_X c_p_eq_0 j,
    have useful := (add_le_add_right (total_degree_mul_X_le (h i) j) (g i).total_degree),
    by_cases c_i_eq_j : i = j,
    { rw c_i_eq_j at useful,
      simp only [c_i_eq_j, single_eq_same, pi.add_apply],
      apply (add_le_add_right (total_degree_add (h j * X j) q) (g j).total_degree).trans,
      suffices y : linear_order.max (h j * X j).total_degree q.total_degree + (g i).total_degree 
        ≤ p.total_degree + 1,
      by rwa c_i_eq_j at y,
      by_cases h_ms : ms = ∅,
      { rw [@q_eq_zero_of_ms_empty R σ _ _ _ g j p h h_ms, total_degree_zero, c_i_eq_j],
        apply useful.trans,
        rw [add_comm, ←add_assoc],
        apply add_le_add_right _ 1,
        rw add_comm,
        simp only [h1, c_i_eq_j] at c_h1_i_eq_0,
        rw @q_eq_zero_of_ms_empty R σ _ _ _ g j p h h_ms at c_h1_i_eq_0,
        simp only [add_zero, coe_zero, single_zero] at c_h1_i_eq_0,
        suffices h_j_ne_zero : h j ≠ 0,
        by exact or.resolve_left (h_h.1 j) h_j_ne_zero,
        by_contra c,
        simpa [c] using c_h1_i_eq_0 },
      { by_cases c_comp : (h j * X j).total_degree ≤ q.total_degree,
        { rw [max_eq_right c_comp, c_i_eq_j],
          apply @h_total_degree_q R σ _ _ _ g j p h h_h h_ms},
        { simp only [not_le] at c_comp,
          rw max_eq_left c_comp.le,
          by_cases c_h_j_eq_0 : h j = 0,
          { simpa only [c_h_j_eq_0, zero_mul, nat.not_lt_zero, total_degree_zero] using c_comp },
          { rw c_i_eq_j,
            apply useful.trans,
            rw [add_assoc, ←add_comm (g j).total_degree 1, ←add_assoc],
            exact add_le_add_right (or.resolve_left (h_h.1 j) c_h_j_eq_0) 1, } } } },
    { simp only [pi.add_apply, h1, if_neg c_i_eq_j],
      suffices h_i_neq_0 : h i ≠ 0,
      { rw [single_eq_of_ne, add_zero],
        { apply useful.trans _,
          have y := add_le_add_right (or.resolve_left (h_h.1 i) h_i_neq_0) 1,
          rwa [add_assoc, add_comm (g i).total_degree 1, ← add_assoc ] at y },
        { symmetry,
          simpa only [ne.def] using c_i_eq_j } },
      by_contradiction,
      have x := c_h1_i_eq_0,
      simp only [h1, if_neg c_i_eq_j, h, zero_mul, pi.add_apply] at x,
      rw [zero_add, single_eq_of_ne] at x,
      { simpa only using x },
      { symmetry,
        simpa only [ne.def] using c_i_eq_j } } },
  end
omit c_p_eq_0 h_h

include h_h hS hg hmonic
private lemma h_X_2 :
∀ (j_1 : σ),
degree_of j_1 (p * X j - ∑ (i : σ), (@h1 R σ _ _ _ g j p h) i * g i) < (g j_1).total_degree
:=
begin
  intro i,
  rw @comp_1 R σ _ _ _ g j p h h_h,
  exact degree_of_sub_lt (hS i) (@H_f R σ _ _ _ g hg hmonic j p h h_h i)
    (@H_g R σ _ _ _ g hg hS hmonic j p h h_h i),
end
omit h_h hS hg hmonic

end h_X

private lemma h_X {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  (g : σ → mv_polynomial σ R)
  (hg : ∀ (i : σ), g i ∈ supported R ({i} : set σ ))
  (hS : ∀ (i : σ), 0 < (g i).total_degree) 
  (hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1)
  :  ∀ (p : mv_polynomial σ R) (j : σ), 
      M' R σ g hg hS hm p → M' R σ g hg hS hm (p * X j) :=
begin
  intros p j h_Mp,
  cases h_Mp with h h_h,
  by_cases c_p_eq_0 : p = 0,
  { rw [ c_p_eq_0, zero_mul, M'],
    exact ⟨h, by rwa c_p_eq_0 at h_h⟩ },
  { rw M',
    exact ⟨ @h1 R σ _ _ _ g j p h, ⟨@h_X_1 R σ _ _ _ g j p h h_h c_p_eq_0, @h_X_2 R σ _ _ _ g hg hS hm j p h h_h⟩⟩ },
end

private lemma h_add_weak_aux_comp  {R σ : Type*} [comm_ring R] [fintype σ]
  (g : σ → mv_polynomial σ R) (p q : mv_polynomial σ R) 
  (h1 h2 : σ → mv_polynomial σ R) : 
  p + q - (∑ (i : σ), (h1 + h2) i * g i)
  = (p - (∑ (i : σ), h1 i * g i))
  + (q - (∑ (i : σ), h2 i * g i)) :=
calc p + q - (∑ (i : σ), (h1 + h2) i * g i)
     = p + q - (∑ (i : σ), (h1 i + h2 i) * g i) : by simp
...  = p + q - (∑ (i : σ),(h1 i * g i + h2 i * g i)) :
  begin
    simp only [sub_right_inj],
    congr,
    ext,
    congr,
    rw add_mul,
  end
...  = p + q - (∑ (i : σ), h1 i * g i + ∑ (i : σ), h2 i * g i) :
  by simp only [sub_right_inj,finset.sum_add_distrib]
...  = (p - (∑ (i : σ), h1 i * g i))
       + (q - (∑ (i : σ), h2 i * g i)) : 
  by rw [← add_sub_assoc, ← sub_sub (p+q), sub_left_inj,sub_add_eq_add_sub]

private lemma h_add_weak {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  (g : σ → mv_polynomial σ R)
  (hg : ∀ (i : σ), g i ∈ supported R ({i} : set σ ))
  (hS : ∀ (i : σ), 0 < (g i).total_degree) 
  (hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1) : 
  ∀ (a : σ →₀ ℕ) (b : R) (f : mv_polynomial σ R), 
      a ∉ f.support → b ≠ 0 → M' R σ g hg hS hm f → M' R σ g hg hS hm (monomial a b) → M' R σ g hg hS hm (monomial a b + f) :=
begin
  intros a b f h_a h_b h_Mf h_Mmonomial,
  cases h_Mf with h_f hh_f,
  cases h_Mmonomial with h_Ca hhC_a,
  rw M',
  use h_Ca + h_f,
  apply and.intro,
  intro i,
  simp only [total_degree_add_monomial f a b h_a h_b, pi.add_apply],
  by_cases h_Ca0 : h_Ca i = 0,
  { by_cases h_f0 : h_f i = 0,
    { simp [h_Ca0, h_f0] },
    { right,
      rw h_Ca0,
      simp only [zero_add],
      exact (or.resolve_left (hh_f.1 i) h_f0).trans (le_max_right (total_degree (single a b)) (total_degree f)) } },
  { by_cases h_f0 : h_f i = 0,
    { right,
      rw h_f0,
      simp only [add_zero],
      exact (or.resolve_left (hhC_a.1 i) h_Ca0).trans (le_max_left (total_degree (single a b)) (total_degree f)), },
    { right,
      apply le_trans _ (max_le_max (or.resolve_left (hhC_a.1 i) h_Ca0) (or.resolve_left (hh_f.1 i) h_f0)),
      rw max_add_add_right,
      exact add_le_add_right (total_degree_add (h_Ca i) (h_f i)) (g i).total_degree, } },
  intro j,
  rw [ h_add_weak_aux_comp g (monomial a b) f h_Ca h_f],
  exact lt_of_le_of_lt (degree_of_add_le j _ _) (max_lt (hhC_a.2 j) (hh_f.2 j)),
end

lemma reduce_degree {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  (f : mv_polynomial σ R) (g : σ → mv_polynomial σ R)
  (hg : ∀ i : σ, g i ∈ supported R ({i} : set σ))
  (h0 : ∀ i : σ, 0 < total_degree (g i))
  (hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1) :
  ∃ h : σ → mv_polynomial σ R,
    (∀ i : σ, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
      ∧ ∀ i : σ,  degree_of i (f - (∑ j : σ, h j * g j)) < total_degree (g i) := 
begin
  apply induction_on'' f,
  { apply h_C g hg h0 hm }, 
  { apply h_add_weak g hg h0 hm },
  { apply h_X g hg h0 hm },
end

lemma reduce_degree_particular_case {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  (S : σ → finset R) (hS : ∀ i : σ, 0 < (S i).card)
  (f : mv_polynomial σ R) :
  ∃ h : σ → mv_polynomial σ R,
  (∀ i : σ, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ∀ j : σ, 
  degree_of j (f - (∑ i : σ, h i * ∏ s in S i, (X i - C s))) < (S j).card := 
begin
  let g : σ → mv_polynomial σ R := λ i, ∏ s in S i, (X i - C s),
  let hg : ∀ i : σ, g i ∈ supported R ({i} : set σ) := λ i,  g_S_lem_supported (S i) i,
  have h0 : ∀ i : σ, 0 < total_degree (g i),
  { intro i,
    rw g_S_lem_4,
    exact hS i,
  },
  have hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1,
  { intro i,
    simpa only [g, g_S_lem_4] using g_S_lem_8 (S i) i },
  cases reduce_degree f g hg h0 hm with h hh,
  use h,
  apply and.intro,
  intro i,
  rw ← g_S_lem_4,
  exact hh.1 i,
  intro j,
  rw ← g_S_lem_4,
  exact hh.2 j,
end

end mv_polynomial