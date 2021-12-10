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
private def M'  (n : ℕ ) (F : Type u) [field F]
  (g : fin n → mv_polynomial (fin n) F)
  (hg : ∀ i : fin n, g i ∈ supported F ({i} : set (fin n)))
  (hS : ∀ i : fin n, 0 < total_degree (g i))
  (hm : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1)
: mv_polynomial (fin n) F → Prop :=
  λ f, ∃ h : fin n → mv_polynomial (fin n) F,
  (∀ i : fin n, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
  ∧ ∀ i : fin n,  degree_of i (f - (∑ j : fin n, h j * g j)) < total_degree (g i)



private def M { n : ℕ } {F : Type u} [field F]
  {g : fin n → mv_polynomial (fin n) F}
  {hg : ∀ i : fin n, g i ∈ supported F ({i} : set (fin n))}
  {hS : ∀ i : fin n, 0 < total_degree (g i)}
  {hm : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1}

  : mv_polynomial (fin n) F → Prop := λ f, M' n F g hg hS hm f

local attribute [instance] classical.prop_decidable --esta permitido usar esto?

private lemma h_C { n : ℕ } {F : Type u} [field F] 
  (g : fin n → mv_polynomial (fin n) F)
  (hg : ∀ (i : fin n), g i ∈ supported F {i})
  (hS : ∀ (i : fin n), 0 < (g i).total_degree)
  (hm : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1)
 : ∀ (a : F), M' n F g hg hS hm (C a) :=
begin
  intro a,
  rw M',
  use λ i, 0,
  apply and.intro,
  intro i,
  left,
  refl,
  intro j,
  have h: C a - ∑ (i : fin n), 0 * g i = C a,
  { have h1 : (λ i ,  0 * g i) = (λ i, 0),
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
{F : Type u} [field F]
{g : fin n → mv_polynomial (fin n) F }
{hg : ∀ i : fin n, g i ∈ supported F ({i} : set (fin n))}
{hS : ∀ i : fin n, 0 < total_degree (g i)}
{hmonic : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1}


variables {j :fin n}

variables {p : mv_polynomial (fin n) F}

variables {h : fin n → mv_polynomial (fin n) F}

variables {h_h : (∀ (i : fin n), h i = 0 
  ∨ (h i).total_degree + (g i).total_degree ≤ p.total_degree) 
  ∧ ∀ (j : fin n),
 degree_of j (p - ∑ (i : fin n), h i * g i) < (g j).total_degree }

variables {c_p_eq_0 : ¬p = 0}

abbreviation p1: mv_polynomial (fin n) F :=  (p - ∑ (i : fin n), h i * g i)

abbreviation f: mv_polynomial (fin n) F := (p - ∑ (i : fin n), h i * g i) * X j

abbreviation ms: finset (fin n →₀ ℕ) :=
  finset.filter (λ (m : fin n →₀ ℕ), m j = (g j).total_degree) (@f n F _ g j p h).support

def q: mv_polynomial (fin n) F :=
  ∑ (m : fin n →₀ ℕ) in @ms  n F _ g j p h, (monomial (m - single j (g j).total_degree)) (coeff m (@f n F _ g j p h))

def h1: fin n → mv_polynomial (fin n) F := (λ i,  h i * (X j)) + single j  (@q n F _ g j p h)

lemma prop_ms (m : fin n →₀ ℕ):  m ∈ (@ms n F _ g j p h) →  m j = (g j).total_degree := 
begin
  intro h_m,
  simp at h_m,
  exact h_m.2,
end

lemma prop_ms'' (m : fin n →₀ ℕ):  m ∈ (@ms  n F _ g j p h) →  m ∈ (@f n F _ g j p h).support :=
begin
  intro h,
  rw finset.mem_filter at h,
  exact h.1,
end

lemma prop_ms' (m : fin n →₀ ℕ):  m ∈ (@ms  n F _ g j p h) →  coeff m (@f n F _ g j p h) ≠ 0 :=
begin
  intro h,
  rw ← mem_support_iff,
  apply prop_ms'',
  exact h,
end

lemma q_eq_zero_of_ms_empty (h' : (@ms n F _ g j p h) = ∅) : (@q n F _ g j p h) = 0 :=
begin
  simp only [q],
  rw h',
  simp,
end

lemma exists_m1 {m : fin n →₀ ℕ} (h_m : m ∈ (@q n F _ g j p h).support):
  ∃ m1 : (fin n →₀ ℕ),
   m1 ∈ (@ms n F _ g j p h)  ∧ m = m1 - (single j (g j).total_degree) := 
begin
  rw q at h_m,
  have h_m' := support_sum h_m,
  cases h_m' with m1 h_m1',
  clear h_m,
  cases h_m1' with H h_m1,
  use m1,
  apply and.intro,
  exact H,
  simp only [exists_prop, mem_support_iff, coeff_monomial, ite_eq_right_iff, ne.def, not_forall] at h_m1,
  exact h_m1.1.symm,
end

include h_h
lemma comp_1:  
  p * X j - ∑ (i : fin n), (@h1 n F _ g j p h) i * g i 
  = (@f n F _ g j p h) - (@q n F _ g j p h) *  g j
:=
begin
  rw h1,
  ext,
  rw coeff_sub,
  rw coeff_sub,
  rw coeff_sum,
  rw coeff_mul_X',
  rw coeff_mul_X',
  let q := @q n F _ g j p h,
  by_cases c_j_m : j ∈ m.support,
  { simp only [if_pos, c_j_m, pi.add_apply, coeff_sub],
    rw sub_sub,
    congr,
    rw coeff_sum,
    have h : (λ x, coeff m ((h x * X j + single j q x) * g x ))
      = (λ x, coeff (m - single j 1) (h x * g x))
      + single j (coeff m (q * g j)),
    { ext,
      simp only [pi.add_apply],
      rw add_mul,
      rw coeff_add,
      rw mul_assoc,
      rw mul_comm (X j) (g x),
      rw ← mul_assoc,
      rw coeff_mul_X',
      simp only [if_pos, c_j_m],
      congr,
      by_cases c_x : j = x,
      { rw [←c_x, finsupp.single_eq_same, finsupp.single_eq_same] },
      rw finsupp.single_eq_of_ne,
      rw finsupp.single_eq_of_ne,
      simp,
      simpa,
      simpa },
    rw h,
    simp, -- nonterminal simp
    rw finset.sum_add_distrib,
    clear h,
    congr,
    rw finsupp.sum_single' j},
  simp [if_neg, c_j_m],
  have h : (λ x, coeff m ((h x * X j + single j q x) * g x ))
  = single j (coeff m (q * g j)),
  { ext,
    rw add_mul,
    rw coeff_add,
    simp only,
    rw mul_assoc,
    rw mul_comm (X j) (g x),
    rw ← mul_assoc,
    rw coeff_mul_X',
    simp only [if_neg, c_j_m, zero_add, not_false_iff],
    by_cases c_x : j = x,
    { rw [←c_x, finsupp.single_eq_same, finsupp.single_eq_same] },
    rw finsupp.single_eq_of_ne,
    rw finsupp.single_eq_of_ne,
    simp,
    simpa,
    simpa, },
  rw h,
  rw finsupp.sum_single' j,
end
omit h_h

include hmonic hg
lemma comp_2 : ∀ m, m ∈ (@ms  n F _ g j p h) → coeff m (@f n F _ g j p h) = coeff m ((@q n F _ g j p h) * g j)
:=begin
  intros m hm,
  rw q,
  rw finset.sum_mul,
  rw coeff_sum ms,
  let f := @f n F _ g j p h,
  let ms := @ms n F _ g j p h,
  let f' :  (fin n →₀ ℕ) → F := λ (x : fin n →₀ ℕ), coeff m ((monomial (x - single j (g j).total_degree)) (coeff x f) * g j),
  let g' :  (fin n →₀ ℕ) → F := (single  m  (coeff m f)),  
  have h''' : m - (m - single j (g j).total_degree) = single j (g j).total_degree,
  { ext,
    simp only [coe_tsub, pi.sub_apply],
    by_cases c : j = a,
    { rw ←c,
      rw prop_ms m hm,
      simp, },
    rw single_eq_of_ne c,
    simp },
  have h' : coeff m ((monomial (m - single j (g j).total_degree)) (coeff m f) * g j) = coeff m f,
  { rw coeff_monomial_mul',
    rw h''',
    simp only [tsub_le_self, if_true],
    rw hmonic j,
    rw mul_one },
  have h'' :∀ m'∈ ms, m ≠ m'→  coeff m ((monomial (m' - single j (g j).total_degree)) (coeff m' f) * g j) = 0,
  { intros m' h_m'_in_ms h_m_ne_m',
    by_cases c_m_m' : m' ≤ m,
    { rw coeff_monomial_mul',
      rw mul_eq_zero_of_right,
      simp,
      have x : m' < m := finsupp.lt_of_le_and_ne c_m_m' h_m_ne_m'.symm,
      have x' := x.2,
      simp only [not_le, not_forall] at x',
      cases x' with x hx,
      have h : j ≠ x,
      { by_contradiction h,
        rw ←h at hx,
        rw [prop_ms m hm, prop_ms m' h_m'_in_ms] at hx,
        simpa using hx,
      },
      have h' : (m - (m' - single j (g j).total_degree)) x ≠ 0,
      { simp only [tsub_eq_zero_iff_le, not_le, ne.def, coe_tsub, pi.sub_apply],
        rw single_eq_of_ne h,
        simpa },
      rw g_S_lem_6' (hg j) h' h.symm },
    rw coeff_monomial_mul',
    apply if_neg,
    by_contradiction c,
    rw finsupp.le_def at c_m_m',
    simp only [not_le, not_forall] at c_m_m',
    cases c_m_m' with x hx,
    have h : j ≠ x,
    { by_contradiction h,
      rw ←h at hx,
      rw [prop_ms m hm, prop_ms m' h_m'_in_ms] at hx,
      simpa using hx,},
    rw finsupp.le_def at c,
    have cx := c x,
    simp only [tsub_le_iff_right, coe_tsub, pi.sub_apply] at cx,
    rw finsupp.single_eq_of_ne h at cx,
    rw add_zero at cx,
    have a := lt_of_le_of_lt cx hx,
    simpa using a},
  have h: ∀ (x : fin n →₀ ℕ), x ∈ ms → f' x = g' x,
  { intros m' hm',
    simp only [f',g'],
    by_cases c : m = m',
    { rw [c, finsupp.single_eq_same, ←c, h'] },
    rw finsupp.single_eq_of_ne c,
    apply h'' m' hm',
    simpa },
  have h0 : ms = ms,
  { refl },
  rw @finset.sum_congr F (fin n →₀ ℕ) ms ms f' g' _ h0 h,
  simp only [g'],
  rw finsupp.sum_single'' hm,
end
omit hmonic hg

include h_h
lemma h_total_degree_f : total_degree (@f n F _ g j p h) ≤ total_degree p + 1 :=
begin
  apply (total_degree_mul_X_le p1 j).trans,
  apply add_le_add_right,
  let r := ∑ (i : fin n), h i * g i,
  have t:= total_degree_sub p r,
  apply t.trans, clear t,
  by_cases h : p.total_degree ≤ r.total_degree,
  { rw max_eq_right h,
    clear h,
    have t := total_degree_sum (finset.fin_range n) (λ i,  h i * g i),
    simp only at t,
    have y : (finset.fin_range n).sup (λ (i : fin n), (h i * g i).total_degree) ≤ total_degree p,
    { apply finset.sup_le,
      intros i hi,
      by_cases c : h i = 0,
      { rw c,
        simp },
      have x : (h i).total_degree + (g i).total_degree ≤ p.total_degree,
      { have x' := h_h.1 i,
        cc },
      apply (total_degree_mul (h i) (g i)).trans,
      exact x},
    exact t.trans y,
  },
  rw not_le at h,
  rw max_eq_left h.le,
end
omit h_h

include h_h
lemma h_total_degree_q : (¬ (@ms  n F _ g j p h) = ∅ ) 
  →  total_degree (@q n F _ g j p h) + (g j).total_degree ≤  total_degree p + 1 :=
begin
  intro h_ms,
  have c_ms_nonempty : ms.nonempty,
  { apply finset.nonempty_of_ne_empty,
    simpa using h_ms },
  rw q,
  have t:= total_degree_sum ms (λm , (monomial (m - single j (g j).total_degree)) (coeff m f) ),
  have t' := add_le_add_right t (g j).total_degree,
  clear t,
  apply t'.trans ,
  clear t',
  simp only,
  let f := λ (m : fin n →₀ ℕ), ((monomial (m - single j (g j).total_degree)) (coeff m f)).total_degree,
  cases finset.exists_mem_eq_sup ms c_ms_nonempty f with m hm,
  cases hm with h_m_in_ms h_sup_f_eq_f_m,
  rw h_sup_f_eq_f_m,
  simp only [f],
  clear h_sup_f_eq_f_m f,
  rw total_degree_monomial_eq_monomial_degree (prop_ms' m h_m_in_ms),
  rw monomial_degree_sub,
  rw monomial_degree_single,
  have x : monomial_degree m - (g j).total_degree + (g j).total_degree = monomial_degree m,
  { rw nat.sub_add_cancel,
    rw ←prop_ms m h_m_in_ms,
    exact le_monomial_degree m j },
  rw x,
  have y : monomial_degree m ≤ total_degree f,
  { apply monomial_degree_le_total_degree,
    apply prop_ms'',
    exact h_m_in_ms },
  exact le_trans y (@h_total_degree_f n F _ g j p h h_h),
  rw finsupp.le_def,
  intro i,
  by_cases c : i = j,
  { rw c,
    rw prop_ms m h_m_in_ms,
    simp },
  rw single_eq_of_ne,
  simp,
  cc,
end
omit h_h

include h_h hg hmonic
lemma H_f : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ (@f n F _ g j p h).support → ((g i).total_degree ≤ m i) → coeff m (@f n F _ g j p h) = coeff m ((@q n F _ g j p h) * g j)
:= begin
   intros i m h_m_in_supp_f h_S,
    let ms := @ms n F _ g j p h,
    have x : degree_of i p1 < (g i).total_degree := h_h.2 i,
    have z := monomial_le_degree_of i h_m_in_supp_f,
    by_cases c_i_eq_j : i = j,
    { have h_m_in_ms : m ∈ ms,
      { have y := degree_of_mul_X_eq j p1,
        rw c_i_eq_j at x,
        rw c_i_eq_j at h_S,
        rw c_i_eq_j at z,
        have w := nat.eq_of_le_of_lt_succ h_S ( lt_of_le_of_lt (z.trans y) (add_lt_add_right x 1) ),
        simp only [exists_prop, add_right_embedding_apply, finset.mem_map, 
        finset.mem_filter, coeff_sub],
        exact ⟨h_m_in_supp_f , w⟩ },
        convert comp_2 m h_m_in_ms,
        exact hg,
        exact hmonic },
    have y := degree_of_mul_X_ne  p1 c_i_eq_j,
    rw ← y at x, clear y,
    exfalso,
    linarith,
end
omit h_h hg hmonic

include h_h hS hg hmonic
lemma H_g : ∀ i (m : (fin n) →₀ ℕ), m ∈ ((@q n F _ g j p h) * g j).support 
  → ((g i).total_degree ≤ m i) 
  → coeff m (@f n F _ g j p h) = coeff m ((@q n F _ g j p h) * g j) := 
begin
  intros i m m_in_support_q_g_j h_S,
  let ms := @ms n F _ g j p h,
  cases support_mul'' m_in_support_q_g_j with m' h_m',
  cases h_m' with m'' h_m_m'_m'',
  have h_m'_in_supp_q := h_m_m'_m''.1,
  have h_m''_in_supp_gj := h_m_m'_m''.2.1,
  have h_m_eq_m'_add_m'' := h_m_m'_m''.2.2.symm,
  clear h_m_m'_m'',
  have h_mi_eq_mi'_add_mi'' : m i = m' i + m'' i,
  { rw h_m_eq_m'_add_m'',
    refl },
  cases (@exists_m1 n F _ g j p h m') h_m'_in_supp_q with m1 h0m1,
  cases h0m1 with h_m1 h_m'_m1,
  by_cases c_i_eq_j : j = i,
  { apply comp_2 m,
    rw ← c_i_eq_j at h_S,
    rw ← c_i_eq_j at h_mi_eq_mi'_add_mi'',
    have h_m'_m1_j : m' j = m1 j - (g j).total_degree := 
      by simp only [h_m'_m1, single_eq_same, coe_tsub, pi.sub_apply],
    have m1_j : m1 j = (g j).total_degree := prop_ms m1 h_m1,
    have m'_j_eq_0 : m' j = 0 :=
      by simpa only [h_m'_m1_j] using nat.sub_eq_zero_of_le (le_of_eq m1_j),
    have h : m j ≤ (g j).total_degree,
    { rw [h_mi_eq_mi'_add_mi'', m'_j_eq_0, zero_add],
      exact mv_polynomial.le_total_degree h_m''_in_supp_gj },
    have x' : m'' j = (g j).total_degree :=
      by simpa [← nat.le_antisymm h h_S, h_m_eq_m'_add_m''] using m'_j_eq_0,
    have h_m_eq_m1 : m = m1,
    { rw [h_m_eq_m'_add_m'', h_m'_m1, @g_S_lem_5 F (fin n) _ j _ (g j) h_m''_in_supp_gj x'],
      ext,
      by_cases c : j = a,
      { simp [←c, m1_j], },
      simp  [pi.add_apply, coe_tsub, coe_add, pi.sub_apply, single, coe_mk, if_neg c] },
    rwa h_m_eq_m1,
    exact hg,
    exact hmonic },
  have h_m''_i : m'' i = 0 := g_S_lem_6 (hg j) h_m''_in_supp_gj c_i_eq_j,
  have h' : m' i = m1 i := 
    by simp only [h_m'_m1, single, coe_mk, coe_tsub, pi.sub_apply, if_neg c_i_eq_j, tsub_zero],
  have h'' : m1 i < (g i).total_degree,
  { have x := h_h.2 i,
    apply (mv_polynomial.degree_of_lt_iff (hS i)).1 
    (by rwa degree_of_mul_X_ne (p - ∑ (i : fin n), h i * g i) (not_eq_symm c_i_eq_j)) m1,
    simp only [exists_prop, add_right_embedding_apply, finset.mem_map, support_mul_X, 
               mem_support_iff, ne.def, finset.mem_filter, coeff_sub] at h_m1,
    simpa only [exists_prop, add_right_embedding_apply, finset.mem_map, support_mul_X, 
               mem_support_iff, ne.def, coeff_sub] using h_m1.1 },
  exfalso,
  linarith,
end
omit h_h hS hg hmonic

include c_p_eq_0 h_h 
lemma h_X_1 :
  ∀ (i : fin n),
  (@h1 n F _ g j p h) i = 0 ∨ ((@h1 n F _ g j p h) i).total_degree + (g i).total_degree
  ≤ (p * X j).total_degree
:= begin
  let h1 : fin n → mv_polynomial (fin n) F := @h1 n F _ g j p h,
  intro i,
  by_cases c_h1_i_eq_0 : h1 i = 0,
  { left,
    exact c_h1_i_eq_0 },
  right,
  simp only [hX.h1],
  rw total_degree_mul_X c_p_eq_0 j,
  have useful := (add_le_add_right (total_degree_mul_X_le (h i) j) (g i).total_degree),
  by_cases c_i_eq_j : i = j,
  { rw c_i_eq_j,
    simp only [single_eq_same, pi.add_apply],
    have x := add_le_add_right (total_degree_add (h j * X j) q) (g i).total_degree,
    have y : linear_order.max (h j * X j).total_degree q.total_degree + (g i).total_degree 
      ≤ p.total_degree + 1,
    { by_cases h_ms : ms = ∅,
      { rw @q_eq_zero_of_ms_empty n F _ g j p h h_ms,
        rw  total_degree_zero,
        rw c_i_eq_j at useful,
        rw c_i_eq_j,
        apply useful.trans,
        rw [add_comm, ←add_assoc],
        apply add_le_add_right _ 1,
        rw add_comm,
        --rw ←c_i_eq_j,
        simp only [h1, hX.h1, c_i_eq_j] at c_h1_i_eq_0,
        rw @q_eq_zero_of_ms_empty n F _ g j p h h_ms at c_h1_i_eq_0,
        simp only [add_zero, coe_zero, single_zero] at c_h1_i_eq_0,
        have h_j_ne_zero : h j ≠ 0,
        { by_contra c,
          rw c at c_h1_i_eq_0,
          simpa using c_h1_i_eq_0 },
        exact or.resolve_left (h_h.1 j) h_j_ne_zero },
      by_cases c_comp : (h j * X j).total_degree ≤ q.total_degree,
      { rw [max_eq_right c_comp],
        rw c_i_eq_j,
        apply @h_total_degree_q n F _ g j p h h_h h_ms},
      simp only [not_le] at c_comp,
      rw max_eq_left c_comp.le,
      rw c_i_eq_j at useful,
      by_cases c_h_j_eq_0 : h j = 0,
      { rw [c_h_j_eq_0, zero_mul] at c_comp,
        simp only [nat.not_lt_zero, total_degree_zero] at c_comp,
        exfalso,
        exact c_comp },
      have y := add_le_add_right (or.resolve_left (h_h.1 j) c_h_j_eq_0) 1,
      rw [add_assoc, add_comm (g j).total_degree 1, ← add_assoc ] at y,
      rw c_i_eq_j,
      exact useful.trans y },
      rw c_i_eq_j at x,
      rw c_i_eq_j at y,
    exact x.trans y },
  simp only [pi.add_apply, hX.h1, if_neg c_i_eq_j],
  have h_i_neq_0 : h i ≠ 0,
  { let x := c_h1_i_eq_0,
    simp only [h1] at x,
    by_contradiction,
    simp only [hX.h1, if_neg c_i_eq_j, h, zero_mul, pi.add_apply] at x,
    rw [zero_add, single_eq_of_ne] at x,
    simp only [eq_self_iff_true, not_true] at x,
    exact x,
    symmetry,
    simp only [ne.def],
    exact c_i_eq_j },
  have y := add_le_add_right (or.resolve_left (h_h.1 i) h_i_neq_0) 1,
  rw [add_assoc, add_comm (g i).total_degree 1, ← add_assoc ] at y,
  rw [single_eq_of_ne, add_zero],
  exact useful.trans y,
  symmetry,
  simp only [ne.def],
  exact c_i_eq_j,
end
omit c_p_eq_0 h_h

include h_h hS hg hmonic
lemma h_X_2 :
∀ (j_1 : fin n),
degree_of j_1 (p * X j - ∑ (i : fin n), (@h1 n F _ g j p h) i * g i) < (g j_1).total_degree
:=
begin
  intro i,
  have H_f : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ f.support → ((g i).total_degree ≤ m i) → coeff m f = coeff m (q * g j)
    := @H_f n F _ g hg hmonic j p h h_h,
  have H_g : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ (q * g j).support → ((g i).total_degree ≤ m i) → coeff m f = coeff m (q * g j)
    := @H_g n F _ g hg hS hmonic j p h h_h,
  rw @comp_1 n F _ g j p h h_h,
  exact degree_of_sub_lt (hS i) (H_f i) (H_g i),
end
omit h_h hS hg hmonic

include hg hmonic
lemma h_X :
 ∀ (p : mv_polynomial (fin n) F) (j : fin n), M' n F g hg hS hmonic p 
  → M' n F g hg hS hmonic (p * X j) :=
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
  use  @h1 n F _ g j p h,
  apply and.intro,
  exact @h_X_1 n F _ g j p h h_h c_p_eq_0,
  exact @h_X_2 n F _ g hg hS hmonic j p h h_h ,
end
omit hg hmonic

end h_X

end hX

private lemma h_X { n : ℕ } {F : Type u} [field F] 
(g : fin n → mv_polynomial (fin n) F)
(hg : ∀ (i : fin n), g i ∈ supported F ({i} : set (fin n) ))
(hS : ∀ (i : fin n), 0 < (g i).total_degree) 
(hm : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1)
 :  ∀ (p : mv_polynomial (fin n) F) (j : fin n), 
    M' n F g hg hS hm p → M' n F g hg hS hm (p * X j) := hX.h_X

private lemma h_add_weak_aux_comp { n : ℕ } {F : Type u} [field F]
(g : fin n → mv_polynomial (fin n) F) (p q : mv_polynomial (fin n) F) 
(h1 h2 : fin n → mv_polynomial (fin n) F) : 
p + q - (∑ (i : fin n), (h1 + h2) i * g i)
= (p - (∑ (i : fin n), h1 i * g i))
+ (q - (∑ (i : fin n), h2 i * g i)) :=
calc p + q - (∑ (i : fin n), (h1 + h2) i * g i)
     = p + q - (∑ (i : fin n), (h1 i + h2 i) * g i) : by simp
...  = p + q - (∑ (i : fin n),(h1 i * g i + h2 i * g i)) :
begin
  simp only [sub_right_inj],
  congr,
  ext,
  congr,
  rw add_mul,
end
...  = p + q - (∑ (i : fin n), h1 i * g i + ∑ (i : fin n), h2 i * g i) :
by simp only [sub_right_inj,finset.sum_add_distrib]
...  = (p - (∑ (i : fin n), h1 i * g i))
       + (q - (∑ (i : fin n), h2 i * g i)) : 
by rw [← add_sub_assoc, ← sub_sub (p+q), sub_left_inj,sub_add_eq_add_sub]

private lemma h_add_weak { n : ℕ } {F : Type u} [field F]
(g : fin n → mv_polynomial (fin n) F)
(hg : ∀ (i : fin n), g i ∈ supported F ({i} : set (fin n) ))
(hS : ∀ (i : fin n), 0 < (g i).total_degree) 
(hm : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1) : 
∀ (a : fin n →₀ ℕ) (b : F) (f : mv_polynomial (fin n) F), 
    a ∉ f.support → b ≠ 0 → M' n F g hg hS hm f → M' n F g hg hS hm (monomial a b) → M' n F g hg hS hm (monomial a b + f) :=
begin
  intros a b f h_a h_b h_Mf h_Mmonomial,
  cases h_Mf with h_f hh_f,
  cases h_Mmonomial with h_Ca hhC_a,
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
    have x : (h_f i).total_degree + (g i).total_degree ≤ total_degree f,
    { have y := hh_f.1 i,
      cc },
    exact x.trans (le_max_right (total_degree (single a b)) (total_degree f)),
  },
  by_cases h_f0 : h_f i = 0,
  { right,
    rw h_f0,
    simp only [add_zero],
    have x : (h_Ca i).total_degree + (g i).total_degree ≤ total_degree (single a b),
    { have y := hhC_a.1 i,
      have z : (h_Ca i).total_degree + (g i).total_degree ≤ (monomial a b).total_degree := by cc,
      simpa using z },
    exact x.trans (le_max_left (total_degree (single a b)) (total_degree f)),
  },
  by_cases c : h_Ca i+ h_f i = 0,
  { left,
    exact c },
  right,
  have x := total_degree_add (h_Ca i) (h_f i),
  have y : (h_Ca i).total_degree + (g i).total_degree ≤ total_degree (single a b) :=
    or.resolve_left (hhC_a.1 i) h_Ca0 ,
  have z : (h_f i).total_degree + (g i).total_degree ≤ total_degree f :=
    or.resolve_left (hh_f.1 i) h_f0,
  have x' := add_le_add_right x (g i).total_degree,
  rw max_add at x',
  exact x'.trans (max_le_max y z),
  intro j,
  rw [ h_add_weak_aux_comp g (monomial a b) f h_Ca h_f],
  exact lt_of_le_of_lt (degree_of_add_le j _ _) (max_lt (hhC_a.2 j) (hh_f.2 j)),
end

lemma reduce_degree { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin n) F) (g : fin n → mv_polynomial (fin n) F)
  (hg : ∀ i : fin n, g i ∈ supported F ({i} : set (fin n)))
  (h0 : ∀ i : fin n, 0 < total_degree (g i))
  (hm : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1) :
  ∃ h : fin n → mv_polynomial (fin n) F,
    (∀ i : fin n, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
      ∧ ∀ i : fin n,  degree_of i (f - (∑ j : fin n, h j * g j)) < total_degree (g i) := 
begin
  have h : M f,
  { apply induction_on'' f,
    apply h_C g hg h0 hm,
    apply h_add_weak g hg h0 hm,
    apply h_X g hg h0 hm },
  rw M at h, rw M' at h,
  exact h,
end

lemma reduce_degree_particular_case { n : ℕ } {F : Type u} [field F]
  (S : fin n → finset F) (hS : ∀ i : fin n, 0 < (S i).card)
  (f : mv_polynomial (fin n) F) :
  ∃ h : fin n → mv_polynomial (fin n) F,
  (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ∀ j : fin n, 
  degree_of j (f - (∑ i : fin n, h i * ∏ s in S i, (X i - C s))) < (S j).card := 
begin
  let g : fin n → mv_polynomial (fin n) F := λ i, ∏ s in S i, (X i - C s),
  let hg : ∀ i : fin n, g i ∈ supported F ({i} : set (fin n)) := λ i,  g_S_lem_supported (S i) i,
  let h0 : ∀ i : fin n, 0 < total_degree (g i),
  { intro i,
    rw g_S_lem_4,
    exact hS i,
  },
  let hm : ∀ i : fin n, coeff (single i (g i).total_degree) (g i) = 1,
  { intro i,
    simp only [g],
    rw g_S_lem_4,
    exact g_S_lem_8 (S i) i },
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