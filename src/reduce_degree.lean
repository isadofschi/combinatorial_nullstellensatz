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

- `is_reduced`: A mv_polynomial f is reduced with respect to m : σ →₀ ℕ if no monomial m' in the
  support of f satisfies m ≤ m'.

- `reduce_degree`: Let R be a integral domain and let f ∈ R[xₛ] be a multivariable polynomial.
   Suppose we are given a finite number of nonconstant polynomials gᵢ ∈ R[xₛ] each having a 
   dominant monomial mᵢ with coefficient 1. Then we can find polynomials hᵢ ∈ R[xₛ] such that:
  (i) For each i, either hᵢ = 0 or deg hᵢ + deg gᵢ ≤ deg f.
  (ii) For each i, f - ∑ j : τ, hⱼ gⱼ is reduced with respect to mᵢ.

- `reduce_degree_special_case`: Let R be a integral domain and Sᵢ be finite nonempty subsets of R,
   defined for i ∈ {0, … , n - 1}. Let f ∈ R[x₀, … xₙ]. Let gᵢ = ∏ (xᵢ - s)
   where the product is taken over s ∈ Sᵢ.Then there are polynomials 
   hᵢ ∈ F[x₀, … xₙ] such that:
   (i) For each i, either hᵢ = 0 or deg hᵢ + |Sᵢ| ≤ deg f.
  (ii) For each j, degⱼ (f - ∑ᵢ hᵢ gᵢ) < |Sⱼ|.

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

local attribute [instance] classical.prop_decidable

def is_reduced {R σ : Type*} [comm_ring R] (f : mv_polynomial σ R) (m : σ →₀ ℕ) : Prop
:= ∀ m' ∈ f.support, ¬ m ≤ m' -- would ∀ m', m ≤ m' → m ∉ f.support be better?

lemma is_reduced_add {R σ : Type*} [comm_ring R] {f g: mv_polynomial σ R} {m : σ →₀ ℕ}
  (hf : is_reduced f m) (hg : is_reduced g m) : is_reduced (f + g) m :=
begin
  rw is_reduced,
  intros m' hm',
  have t := support_add hm',
  simp only [finset.mem_union] at t,
  cases t,
  { exact hf m' t },
  { exact hg m' t }
end

private def M {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ] {g : τ → mv_polynomial σ R}
  {m : τ → (σ →₀ ℕ)} (hm : ∀ i : τ, dominant_monomial (m i) (g i))
  (h0 : ∀ i : τ, 0 < total_degree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) :
  mv_polynomial σ R → Prop := λ f, ∃ h : τ → mv_polynomial σ R,
    (∀ i : τ, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
     ∧ ∀ i : τ,  is_reduced (f - (∑ j : τ, h j * g j)) (m i)

private lemma h_add_weak_aux_comp  {R σ τ : Type*} [comm_ring R] [fintype τ]
  (g : τ → mv_polynomial σ R) (p q : mv_polynomial σ R)  (h1 h2 : τ → mv_polynomial σ R) :
  p + q - (∑ (i : τ), (h1 + h2) i * g i) = (p - (∑ (i : τ), h1 i * g i))
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
  (h0 : ∀ i : τ, 0 < total_degree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) (a : σ →₀ ℕ)
  (b : R) (f : mv_polynomial σ R) (ha : a ∉ f.support) (hb : b ≠ 0) (Mf : M hm h0 hmonic f)
  (Mab : M hm h0 hmonic (monomial a b))  : M hm h0 hmonic (monomial a b + f) := 
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

private lemma total_degree_p_aux { σ : Type*} { m m' a: σ →₀ ℕ} (h_m_le_a : m ≤ a) 
  (h : monomial_degree a ≤ monomial_degree m') (c : a - m ≤ m') 
  (t: monomial_degree (m' - (a - m)) ≤ monomial_degree m 
    ∧ (monomial_degree (m' - (a - m)) = monomial_degree m → m = m' - (a - m))) : a = m' :=
begin
  have h' : m' - (a - m) = m + m' - a,
  { rw add_comm,
    exact monomial_lemma_1 h_m_le_a c },
  rw h' at t,
  clear h',
  suffices h1 : monomial_degree (m + m' - a) = monomial_degree m,
  { ext i,
    zify,
    have t'' :  (m i : ℤ) = m i + m' i - a i,
    { conv
      begin
        to_lhs,
        rw t.2 h1,
      end,
      simp only [pi.add_apply, coe_tsub, coe_add, pi.sub_apply],
      rw int.coe_nat_sub,
      { rw int.coe_nat_add },
      { rw add_comm,
        exact monomial_lemma_2 c i } },
    rw [← add_sub, self_eq_add_right, sub_eq_zero] at t'',
    symmetry,
    exact t'' },
    apply le_antisymm,
    { exact t.1 },
    { suffices t' : monomial_degree m ≤ monomial_degree m + monomial_degree m' - monomial_degree a,
      { apply t'.trans,
        rw ← monomial_degree_add,
        exact monomial_degree_sub_le (m + m') a },
      rw nat.add_sub_assoc,
      { linarith },
      { exact h } },
end

private lemma total_degree_p {R σ : Type*} [comm_ring R] [is_domain R]
  {g :  mv_polynomial σ R} {m a : (σ →₀ ℕ)} (hm : dominant_monomial m g) (h_monic : coeff m g = 1)
  {b : R} (hb : b ≠ 0) (ha : a ≠ 0) (h_m_le_a : m ≤ a )
  : total_degree (monomial a b - (monomial (a - m) b) * g) < monomial_degree a :=
begin
  apply total_degree_sub_lt,
  { by_contradiction,
    simpa [monomial_degree_zero_iff.1 (le_zero_iff.1 (not_lt.1 h))] using ha },
  { intros m' hm' h',
    simp only [exists_prop, mem_support_iff, coeff_monomial, ite_eq_right_iff, ne.def, not_forall] at hm',
    simp only [← hm'.1, coeff_monomial, if_true, eq_self_iff_true],
    rw [coeff_monomial_mul', if_pos],
    { suffices h : coeff (a - (a - m)) g = 1,
      { simp [h] },
      suffices h : a - (a - m) = m,
      { simp [h, h_monic] },
      ext x,
      simp only [coe_tsub, pi.sub_apply, nat.sub_sub_self (h_m_le_a x)] },
    { simp } },
  { intros m' hm' h,
    simp only [mem_support_iff, ne.def, coeff_monomial_mul'] at hm',
    rw coeff_monomial_mul',
    by_cases c : a - m ≤ m',
    { suffices c_m_m' : a = m',
      { simp only [c, if_true, mul_eq_zero, c_m_m'.symm, eq_self_iff_true, coeff_monomial],
        suffices h : coeff (a - (a - m)) g = 1,
        { simp [h] },
        suffices h : a - (a - m) = m,
        { simp [h, h_monic] },
        ext x,
        simp only [coe_tsub, pi.sub_apply, nat.sub_sub_self (h_m_le_a x)] },
      simp only [c, if_true, mul_eq_zero, decidable.not_or_iff_and_not] at hm',
      have t1 := (dominant_monomial_iff hm) (m' - (a - m)) (mem_support_iff.2 hm'.2),
      apply total_degree_p_aux h_m_le_a h c,
      split,
      { exact t1.1 },
      { intro h,
        symmetry,
        exact t1.2 h } },
    { simp only [c, eq_self_iff_true, not_true, if_false] at hm',
      simpa using hm' } }
end

private lemma reduce_degree_h_monomial_a_eq_zero {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  {g : τ → mv_polynomial σ R} {m : τ → (σ →₀ ℕ)} (hm : ∀ i : τ, dominant_monomial (m i) (g i))
  (h0 : ∀ i : τ, 0 < total_degree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1)
  (b : R) : M hm h0 hmonic (monomial 0 b) :=
begin
  use λ i, 0,
  split,
  { intro i,
    left,
    refl },
  { intro i,
    conv in (0 * g _)
    begin
      rw zero_mul,
    end,
    simp only [monomial_zero', sub_zero, finset.sum_const_zero, is_reduced],
    intros m' hm',
    simp only [exists_prop, coeff_C, mem_support_iff, ite_eq_right_iff, ne.def, not_forall] at hm',
    simp only [← hm'.1, nonpos_iff_eq_zero],
    have hmi := (hm i).1,
    by_contra,
    simp only [max_degree_monomial, h] at hmi,
    simpa [←hmi.2, monomial_degree] using h0 i }
end

private lemma reduce_degree_h_monomial_comp {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  {g h0 : τ → mv_polynomial σ R} {m : σ →₀ ℕ} (a: σ →₀ ℕ) (b: R) (i : τ) :
  monomial a b - ∑ (j : τ), (h0 + single i (monomial (a - m) b)) j * g j
    = (monomial a) b - monomial (a - m) b * g i - ∑ (j : τ), h0 j * g j :=
begin
  simp only [pi.add_apply, sub_sub],
  congr,
  rw [← sum_single' i (monomial (a - m) b * g i), ←finset.sum_add_distrib],
  congr,
  ext1 j,
  rw [add_mul, add_comm (h0 j * g j)],
  congr,
  by_cases c : i = j,
  repeat { simp [c] }
end

private lemma reduce_degree_h_monomial {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  {g : τ → mv_polynomial σ R} {m : τ → (σ →₀ ℕ)} (hm : ∀ i : τ, dominant_monomial (m i) (g i))
  (h0 : ∀ i : τ, 0 < total_degree (g i)) (hmonic : ∀ i : τ, coeff (m i) (g i) = 1)
  (a : σ →₀ ℕ) (b : R) (hp : ∀ (p : mv_polynomial σ R), p.total_degree < monomial_degree a 
    → M hm h0 hmonic p) : M hm h0 hmonic (monomial a b) :=
begin
  by_cases c : ∀ i, is_reduced (monomial a b) (m i),
  { use λ i, 0,
    simp only [true_and, zero_mul, implies_true_iff, true_or, eq_self_iff_true, sub_zero, 
               finset.sum_const_zero, c] },
  { by_cases b_eq_zero : b = 0,
    { use λ i, 0,
      simp only [is_reduced, b_eq_zero, finset.not_mem_empty, monomial_zero, forall_false_left,
                 zero_mul, implies_true_iff, true_or, eq_self_iff_true, sub_zero, support_zero,
                 and_self, finset.sum_const_zero] },
    { by_cases a_eq_zero : a = 0,
      { rw a_eq_zero,
        apply reduce_degree_h_monomial_a_eq_zero },
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
        { exact total_degree_p (hm i) (hmonic i) b_eq_zero a_eq_zero ha },
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
              { simpa only [(not_le.1 c).le, max_eq_left, t.1.2] using hr.trans h_total_degree_p.le } } },
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
        { suffices comp : monomial a b - ∑ (j : τ), h j * g j = p - ∑ (j : τ), h0 j * g j,
          { rw comp,
            exact h_h0.2 },
          simp only [p, h],
          apply reduce_degree_h_monomial_comp } } } },
end

lemma reduce_degree {R σ τ : Type*} [comm_ring R] [is_domain R] [fintype τ]
  (f : mv_polynomial σ R) (g : τ → mv_polynomial σ R) {m : τ → (σ →₀ ℕ)} 
  (hm : ∀ i : τ, dominant_monomial (m i) (g i) ) (h0 : ∀ i : τ, 0 < total_degree (g i))
  (hmonic : ∀ i : τ, coeff (m i) (g i) = 1) : ∃ h : τ → mv_polynomial σ R,
    (∀ i : τ, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
      ∧ ∀ i : τ,  is_reduced (f - (∑ j : τ, h j * g j)) (m i) := 
begin
  apply induction_on_new f,
  { apply reduce_degree_h_add_weak hm h0 hmonic },
  { apply reduce_degree_h_monomial hm h0 hmonic },
end

lemma reduce_degree' {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  (f : mv_polynomial σ R) (g : σ → mv_polynomial σ R)
  (hg : ∀ i : σ, g i ∈ supported R ({i} : set σ)) (h0 : ∀ i : σ, 0 < total_degree (g i))
  (hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1) :
  ∃ h : σ → mv_polynomial σ R,
    (∀ i : σ, h i = 0 ∨ total_degree (h i) + total_degree (g i) ≤ total_degree f)
      ∧ ∀ i : σ,  degree_of i (f - (∑ j : σ, h j * g j)) < total_degree (g i) := 
begin
  have hm' : ∀ i : σ, dominant_monomial (single i (g i).total_degree) (g i),
  { intro i,
    apply dominant_monomial_single_of_supported_singleton _ (hg i),
    by_contradiction,
    simpa [h] using h0 i },
  cases reduce_degree f g hm' h0 hm with h h_h,
  use h,
  split,
  { exact h_h.1 },
  { intro i,
    rw [degree_of_eq_sup, finset.sup_lt_iff],
    { simpa only [is_reduced, single_le_iff, not_le, ne.def] using h_h.2 i },
    { exact h0 i } }
end

lemma reduce_degree_special_case {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
  [decidable_eq σ] (S : σ → finset R) (hS : ∀ i : σ, 0 < (S i).card) (f : mv_polynomial σ R) :
  ∃ h : σ → mv_polynomial σ R,
    (∀ i : σ, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
      ∧ ∀ j : σ, degree_of j (f - (∑ i : σ, h i * ∏ s in S i, (X i - C s))) < (S j).card :=
begin
  let g : σ → mv_polynomial σ R := λ i, ∏ s in S i, (X i - C s),
  let hg : ∀ i : σ, g i ∈ supported R ({i} : set σ) := λ i,  g_S_mem_supported (S i) i,
  have h0 : ∀ i : σ, 0 < total_degree (g i),
  { intro i,
    rw total_degree_g_S,
    exact hS i,
  },
  have hm : ∀ i : σ, coeff (single i (g i).total_degree) (g i) = 1,
  { intro i,
    simpa only [g, total_degree_g_S] using g_S_monic (S i) i },
  cases reduce_degree' f g hg h0 hm with h hh,
  use h,
  split,
  { intro i,
    rw ← total_degree_g_S (S i) i,
    exact hh.1 i, },
  { intro i,
    rw ← total_degree_g_S (S i) i,
    exact hh.2 i },
end

end mv_polynomial