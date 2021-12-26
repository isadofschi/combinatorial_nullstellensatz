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

lemma induction_on_new {R σ : Type*} [comm_semiring R] {M : mv_polynomial σ R → Prop} (p : mv_polynomial σ R)
  (h_add_weak : ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R),
    a ∉ f.support → b ≠ 0 → M f → M (monomial a b) → M (monomial a b + f))
  (h_monomial : ∀ m : σ →₀ ℕ, ∀ b : R,
    (∀ p : mv_polynomial σ R, total_degree p < monomial_degree m → M p) → M (monomial m b)) 
  : M p := sorry


def is_reduced {R σ : Type*} [comm_ring R] (f : mv_polynomial σ R) (m : σ →₀ ℕ) : Prop
:= ∀ m' ∈ f.support, ¬ m ≤ m' -- would ∀ m', m≤ m' → m ∉ f.support be better?

lemma is_reduced_add {R σ : Type*} [comm_ring R] {f g: mv_polynomial σ R} {m : σ →₀ ℕ}
  (hf : is_reduced f m) (hg : is_reduced g m) : is_reduced (f + g) m :=
begin
  rw is_reduced,
  intros m' hm',
  have t:= (support_add hm'),
  simp only [finset.mem_union] at t,
  cases t,
  { exact hf m' t },
  { exact hg m' t }
end

private def M {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  {g : τ → mv_polynomial σ R} {m : τ → (σ →₀ ℕ)} {hm : ∀ i : τ, dominant_monomial (m i) (g i)}
  {h0 : ∀ i : τ, 0 < total_degree (g i)} {hmonic : ∀ i : τ, coeff (m i) (g i) = 1}
  : mv_polynomial σ R → Prop :=
  λ f, ∃ h : τ → mv_polynomial σ R, (∀ i : τ, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
    ∧ ∀ i : τ,  is_reduced (f - (∑ j : τ, h j * g j)) (m i)

private lemma h_add_weak_aux_comp  {R σ τ : Type*} [comm_ring R] [fintype τ]
  (g : τ → mv_polynomial σ R) (p q : mv_polynomial σ R) 
  (h1 h2 : τ → mv_polynomial σ R) : 
  p + q - (∑ (i : τ), (h1 + h2) i * g i)
  = (p - (∑ (i : τ), h1 i * g i))
  + (q - (∑ (i : τ), h2 i * g i)) :=
calc p + q - (∑ (i : τ), (h1 + h2) i * g i)
     = p + q - (∑ (i : τ), (h1 i + h2 i) * g i) : by simp
...  = p + q - (∑ (i : τ), (h1 i * g i + h2 i * g i)) :
  begin
    simp only [sub_right_inj],
    congr,
    ext,
    congr,
    rw add_mul,
  end
...  = p + q - (∑ (i : τ), h1 i * g i + ∑ (i : τ), h2 i * g i) :
  by simp only [sub_right_inj,finset.sum_add_distrib]
...  = (p - (∑ (i : τ), h1 i * g i))
       + (q - (∑ (i : τ), h2 i * g i)) : 
  by rw [← add_sub_assoc, ← sub_sub (p+q), sub_left_inj,sub_add_eq_add_sub]

private lemma reduce_degree_h_add_weak {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  {g : τ → mv_polynomial σ R} {m : τ → (σ →₀ ℕ)} (hm : ∀ i : τ, dominant_monomial (m i) (g i))
  (h0 : ∀ i : τ, 0 < total_degree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1)
  (a : σ →₀ ℕ) (b : R) (f : mv_polynomial σ R) (ha : a ∉ f.support) (hb : b ≠ 0)
  (Mf : @M R σ τ _ _ _ g m hm h0 hmonic f)
  (Mab : @M R σ τ _ _ _ g m hm h0 hmonic (monomial a b)) 
  : @M R σ τ _ _ _ g m hm h0 hmonic (monomial a b + f) := 
begin
  cases Mf with hf h_hf,
  cases Mab with hab h_hab,
  use hab + hf,
  split,
  { intro i,
    simp only [total_degree_add_monomial f a b ha hb, pi.add_apply],
    by_cases c : hab i = 0,
    { by_cases c' : hf i = 0,
      { simp [c, c'] },
      { right,
        simp only [c, zero_add, pi.add_apply],
        exact (or.resolve_left (h_hf.1 i) c').trans (le_max_right (total_degree (monomial a b)) (total_degree f)) } },
    { by_cases c' : hf i = 0,
      { right,
        rw c',
        simp only [add_zero],
        exact (or.resolve_left (h_hab.1 i) c).trans (le_max_left (total_degree (single a b)) (total_degree f)) },
      { right,
        apply le_trans _ (max_le_max (or.resolve_left (h_hab.1 i) c) (or.resolve_left (h_hf.1 i) c')),
        rw max_add_add_right,
        apply add_le_add_right,
        apply total_degree_add } } },
  { intro i,
    rw h_add_weak_aux_comp,
    exact is_reduced_add (h_hab.2 i) (h_hf.2 i) }
end

local attribute [instance] classical.prop_decidable

private lemma total_degree_p {R σ : Type*} [comm_ring R] [is_domain R]
  {g :  mv_polynomial σ R} {m a : (σ →₀ ℕ)} (hm : dominant_monomial m g) (h_monic : coeff m g = 1)
  {b : R} (hb : b ≠ 0) (h_m_le_a : m ≤ a )
  : total_degree (monomial a b - (monomial (a - m) b) * g) < monomial_degree a :=
begin
  sorry
end

private lemma reduce_degree_h_monomial {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  {g : τ → mv_polynomial σ R} {m : τ → (σ →₀ ℕ)} (hm : ∀ i : τ, dominant_monomial (m i) (g i))
  (h0 : ∀ i : τ, 0 < total_degree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1)
  (a : σ →₀ ℕ) (b : R) (hp : ∀ (p : mv_polynomial σ R), p.total_degree < monomial_degree a 
    → @M R σ τ _ _ _ g m hm h0 hmonic p) : @M R σ τ _ _ _ g m hm h0 hmonic (monomial a b) :=
begin
  rw M,
  by_cases c : ∀ i, is_reduced (monomial a b) (m i),
  { use λ i, 0,
    simp only [true_and, zero_mul, implies_true_iff, true_or, eq_self_iff_true, sub_zero, 
               finset.sum_const_zero, c] },
  { by_cases b_eq_zero : b = 0,
    { use λi, 0,
      simp only [is_reduced, b_eq_zero, finset.not_mem_empty, monomial_zero, forall_false_left,
                 zero_mul, implies_true_iff, true_or, eq_self_iff_true, sub_zero, support_zero,
                 and_self, finset.sum_const_zero] },
    { simp only [not_forall] at c,
      cases c with i hi,
      simp only [is_reduced, not_forall, exists_prop, not_not, support_monomial,
                 b_eq_zero, if_false, finset.mem_singleton] at hi,
      cases hi with a' ha',
      have ha := ha'.2,
      rw ha'.1 at ha,
      clear ha' a',
      let p := monomial a b - (monomial (a - m i) b) * (g i),
      have h_total_degree_p : p.total_degree < monomial_degree a,
      { exact total_degree_p (hm i) (hmonic i) b_eq_zero ha },
      cases hp p h_total_degree_p with h0 h_h0,
      let h := h0 + single i (monomial (a - m i) b),
      use h,
      split,
      { intro j,
        by_cases c : j = i,
        { right,
          rw c,
          simp only [h, total_degree_monomial_eq_monomial_degree b_eq_zero, single_eq_same, pi.add_apply],
          have t := hm i,
          simp only [dominant_monomial, max_degree_monomial] at t,
          rw ← t.1.2,
          clear c j h,
          cases h_h0.1 i with hl hr,
          { rw [hl, zero_add],
            apply le_of_eq,
            rw [total_degree_monomial_eq_monomial_degree, monomial_degree_sub ha, nat.sub_add_cancel],
            { exact monomial_degree_le_of_le ha },
            { exact b_eq_zero } },
          { apply (add_le_add_right (total_degree_add (h0 i) (monomial (a - m i) b)) (monomial_degree (m i))).trans,
            by_cases c : (h0 i).total_degree ≤ (monomial (a - m i) b).total_degree,
            { simp only [c, max_eq_right],
              rw [total_degree_monomial_eq_monomial_degree, monomial_degree_sub ha, nat.sub_add_cancel],
              { exact monomial_degree_le_of_le ha },
              { exact b_eq_zero} },
            { simp only [not_le] at c,
              simp only [c.le, max_eq_left],
              rw t.1.2,
              exact hr.trans h_total_degree_p.le } } },
        { simp only [h, pi.add_apply, c, forall_false_left, true_or, ite_eq_right_iff],
          rw single_eq_of_ne,
          cases h_h0.1 j,
          { left,
            simpa using h_1 },
          { right,
            rw add_zero,
            apply h_1.trans,
            rw total_degree_monomial_eq_monomial_degree,
            { exact le_of_lt h_total_degree_p },
            { exact b_eq_zero } },
          symmetry,
          simpa using c, } },
      { have comp : monomial a b - ∑ (j : τ), h j * g j = p - ∑ (j : τ), h0 j * g j,
        { simp only [p, h, pi.add_apply],
          rw sub_sub,
          congr,
          rw [← sum_single' i (monomial (a - m i) b * g i), ←finset.sum_add_distrib],
          congr,
          ext1 j,
          rw [add_mul, add_comm (h0 j * g j)],
          congr,
          by_cases c : i = j,
          { simp [c] },
          { simp [c] } },
        rw comp,
        exact h_h0.2 } } },
end

lemma reduce_degree_general {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  (f : mv_polynomial σ R) (g : τ → mv_polynomial σ R) {m : τ → (σ →₀ ℕ)} 
  (hm : ∀ i : τ, dominant_monomial (m i) (g i) ) (h0 : ∀ i : τ, 0 < total_degree (g i))
  (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) :
  ∃ h : τ → mv_polynomial σ R,
    (∀ i : τ, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
      ∧ ∀ i : τ,  is_reduced (f - (∑ j : τ, h j * g j)) (m i) := 
begin
  apply induction_on_new f,
  { apply reduce_degree_h_add_weak hm h0 hmonic },
  { apply reduce_degree_h_monomial hm h0 hmonic },
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
  sorry -- use reduce_degree_general
end

lemma reduce_degree_particular_case {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ] [decidable_eq σ]
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
  split,
  { intro i,
    rw ← g_S_lem_4 (S i),
    exact hh.1 i,
    exact _inst_4 },
  { intro i,
    rw ← g_S_lem_4 (S i),
    exact hh.2 i,
    exact _inst_4 },
end

end mv_polynomial