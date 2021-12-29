/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
-- Note: This is https://github.com/leanprover-community/flt-regular/blob/master/src/ring_theory/polynomial/homogenization.lean

import data.mv_polynomial.comm_ring
import data.set.finite
import ring_theory.polynomial.homogeneous
import ring_theory.polynomial.basic
import order.symm_diff
import tactic.omega
-- import home_finder

/-!
# Homogenization

## Main definitions

* `mv_polynomial.homogenization`

## Main statements

* foo_bar_unique

## Notation



## Implementation details

* We homogenize polynomials over a given ground set of variables, rather than adjoining an extra
  variable to give the user more choice in the type of the polynomials involved.

## References

* [F. Bar, *Quuxes*][]

## Tags


-/

variables {R ι : Type*} [comm_semiring R]

open polynomial finset mv_polynomial

open_locale big_operators
noncomputable theory
namespace mv_polynomial

-- TODO PR
@[simp]
lemma total_degree_monomial (s : ι →₀ ℕ) {r : R} (hr : r ≠ 0) :
  total_degree (monomial s r) = s.sum (λ _ e, e) :=
begin
  classical,
  simp [total_degree, support_monomial, if_neg, hr],
end

section leading_terms
-- TODO is this the best def?
/-- The sum of the monomials of highest degree of a multivariate polynomial. -/
def leading_terms (p : mv_polynomial ι R) : mv_polynomial ι R :=
homogeneous_component p.total_degree p

lemma leading_terms_apply (p : mv_polynomial ι R) : p.leading_terms =
  ∑ d in p.support.filter (λ d, ∑ i in d.support, d i = p.total_degree), monomial d (coeff d p) :=
homogeneous_component_apply _ _
-- (p.support.filter (λ s : ι →₀ ℕ, s.sum (λ _ e, e) = p.total_degree)).sum $
--   λ s, monomial s (p.coeff s)

@[simp]
lemma leading_terms_zero : (0 : mv_polynomial ι R).leading_terms = 0 :=
by simp [leading_terms]

lemma finset.filter_eq_self_iff {α : Type*} (S : finset α) (h : α → Prop) [decidable_pred h] :
  S.filter h = S ↔ ∀ s ∈ S, h s :=
begin
  cases S,
  simp only [finset.filter, finset.mem_mk, multiset.filter_eq_self],
end

-- TODO for non-zero polys this is true that p.lead = p iff p.is_homogenous n for a fixed n
-- TODO generalize to p.homog comp = n
lemma leading_terms_eq_self_iff_is_homogeneous (p : mv_polynomial ι R) :
  p.leading_terms = p ↔ p.is_homogeneous p.total_degree :=
begin
  split; intro h,
  { rw is_homogeneous,
    contrapose! h,
    rcases h with ⟨h_w, h_h₁, h_h₂⟩,
    rw [leading_terms, ne.def, mv_polynomial.ext_iff],
    push_neg,
    use h_w,
    classical,
    change ¬ h_w.sum (λ (_x : ι) (e : ℕ), e) = p.total_degree at h_h₂,
    simp only [h_h₁.symm, coeff_homogeneous_component, exists_prop, and_true, ne.def, not_false_iff,
      not_forall, ite_eq_left_iff],
    convert h_h₂, },
  { rw [leading_terms_apply],
    rw (_ : p.support.filter (λ (s : ι →₀ ℕ), ∑ (i : ι) in s.support, s i = p.total_degree)
            = p.support),
    { rw support_sum_monomial_coeff p, },
    { rw finset.filter_eq_self_iff,
      intros s hs,
      rw [mem_support_iff] at hs,
      rw ← h hs, }, },
end

@[simp]
lemma leading_terms_C (r : R) : (C r : mv_polynomial ι R).leading_terms = C r :=
begin
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_C _ _,
  simp,
end

@[simp]
lemma leading_terms_monomial (s : ι →₀ ℕ) (r : R) : (monomial s r).leading_terms = monomial s r :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_monomial _ _ _ _,
  simpa [total_degree_monomial _ hr]
end

lemma is_homogeneous_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.is_homogeneous p.total_degree :=
homogeneous_component_is_homogeneous (total_degree p) p

lemma exists_coeff_ne_zero_total_degree {p : mv_polynomial ι R} (hp : p ≠ 0) :
  ∃ (v : ι →₀ ℕ), v.sum (λ _ e, e) = p.total_degree ∧ p.coeff v ≠ 0 :=
begin
  obtain ⟨b, hb₁, hb₂⟩ := p.support.exists_mem_eq_sup (finsupp.support_nonempty_iff.mpr hp)
    (λ (m : ι →₀ ℕ), m.to_multiset.card),
  use b,
  split,
  { rw ← total_degree_eq p at hb₂,
    rw hb₂,
    dsimp, -- TODO break this out as a lemma
    funext m,
    exact (finsupp.card_to_multiset _).symm, },
  { exact mem_support_iff.mp hb₁, },
end

-- TODO mathlib
@[simp] lemma support_eq_empty {f : mv_polynomial ι R} : f.support = ∅ ↔ f = 0 :=
finsupp.support_eq_empty

lemma support_add_eq [decidable_eq ι] {g₁ g₂ : mv_polynomial ι R}
  (h : disjoint g₁.support g₂.support) : (g₁ + g₂).support = g₁.support ∪ g₂.support :=
finsupp.support_add_eq h

@[simp] lemma monomial_eq_zero (a : ι →₀ ℕ) (b : R) : monomial a b = 0 ↔ b = 0 :=
finsupp.single_eq_zero

lemma support_sum_monomial_subset (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
  support (∑ v in S, monomial v (f v)) ⊆ S :=
begin
  classical,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  { rw finset.sum_insert hs,
    apply finset.subset.trans support_add,
    apply finset.union_subset,
    { apply finset.subset.trans support_monomial_subset (finset.subset_union_left _ S), },
    { apply finset.subset.trans hsi (finset.subset_insert _ _), }, },
end

lemma support_sum_monomial_eq [decidable_eq R] (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
  support (∑ v in S, monomial v (f v)) = S.filter (λ v, f v ≠ 0) :=
begin
  letI := classical.dec_eq ι,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  rw [finset.sum_insert hs, support_add_eq],
  { rw [hsi, filter_congr_decidable, filter_insert, support_monomial],
    split_ifs with h;
    { simp [h, insert_eq], }, },
  { apply disjoint_of_subset_left support_monomial_subset,
    apply disjoint_of_subset_right (support_sum_monomial_subset _ _),
    simp [support_sum_monomial_subset, hs], },
end

lemma sum_monomial_ne_zero_of_exists_mem_ne_zero (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R)
  (h : ∃ (s) (hs : s ∈ S), f s ≠ 0) : ∑ (s : ι →₀ ℕ) in S, monomial s (f s) ≠ 0 :=
begin
  classical,
  simp only [← support_eq_empty, support_sum_monomial_eq, filter_congr_decidable, ne.def],
  rcases h with ⟨s, h_S, h_s⟩,
  exact ne_empty_of_mem (mem_filter.mpr ⟨h_S, h_s⟩),
end

lemma leading_terms_ne_zero {p : mv_polynomial ι R} (hp : p ≠ 0) : p.leading_terms ≠ 0 :=
begin
  classical,
  rw leading_terms_apply,
  apply sum_monomial_ne_zero_of_exists_mem_ne_zero,
  simp only [exists_prop, mem_support_iff, finset.mem_filter],
  convert exists_coeff_ne_zero_total_degree hp,
  ext v,
  change v.sum (λ (_x : ι) (e : ℕ), e) with v.support.sum v,
  simp [and_comm],
end

@[simp]
lemma total_degree_homogenous_component_of_ne_zero {n : ℕ} {p : mv_polynomial ι R}
  (hp : homogeneous_component n p ≠ 0) :
  (homogeneous_component n p).total_degree = n :=
is_homogeneous.total_degree (homogeneous_component_is_homogeneous n p) hp

@[simp]
lemma total_degree_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.total_degree = p.total_degree :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  exact total_degree_homogenous_component_of_ne_zero (leading_terms_ne_zero hp),
end

-- TODO generalize this to homogeneous component idempotent?
lemma leading_terms_idempotent (p : mv_polynomial ι R) :
  p.leading_terms.leading_terms = p.leading_terms :=
begin
  rw [leading_terms_eq_self_iff_is_homogeneous, total_degree_leading_terms],
  exact is_homogeneous_leading_terms p,
end

lemma homogeneous_component_add (m  : ℕ) (p q : mv_polynomial ι R) :
  homogeneous_component m (p + q) = homogeneous_component m p + homogeneous_component m q :=
by rw [homogeneous_component, linear_map.comp_apply, linear_map.comp_apply, linear_map.comp_apply,
    linear_map.map_add, linear_map.map_add]

lemma coeff_leading_terms (p : mv_polynomial ι R) (d : ι →₀ ℕ) :
  coeff d p.leading_terms = if ∑ i in d.support, d i = p.total_degree then coeff d p else 0 :=
coeff_homogeneous_component _ _ _

lemma support_homogeneous_component (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support = p.support.filter (λ d, d.sum (λ _ m, m) = n) :=
begin
  rw homogeneous_component,
  simp only [finsupp.restrict_dom_apply, submodule.subtype_apply, function.comp_app,
    linear_map.coe_comp, set.mem_set_of_eq],
  erw ← finsupp.support_filter,
  refl,
end

lemma support_homogeneous_component_subset (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support ⊆ p.support :=
begin
  rw support_homogeneous_component,
  exact finset.filter_subset _ _,
end

lemma support_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.support = p.support.filter (λ d, d.sum (λ _ m, m) = p.total_degree) :=
support_homogeneous_component _ _

lemma support_leading_terms_subset (p : mv_polynomial ι R) : p.leading_terms.support ⊆ p.support :=
support_homogeneous_component_subset _ _

lemma eq_leading_terms_add (p : mv_polynomial ι R) (hp : p.total_degree ≠ 0) :
  ∃ p_rest : mv_polynomial ι R,
    p = p.leading_terms + p_rest ∧ p_rest.total_degree < p.total_degree :=
begin
  letI := classical.dec_eq ι,
  existsi (∑ (v : ι →₀ ℕ) in p.support \ p.leading_terms.support, (monomial v) (coeff v p)),
  split,
  { nth_rewrite 0 p.leading_terms.as_sum,
    have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.leading_terms.support), x.support.sum x = p.total_degree,
    { intros x hx,
      rw support_leading_terms at hx,
      simp at hx,
      exact hx.2, },
    simp_rw coeff_leading_terms,
    conv in (ite _ _ _)
    { rw [if_pos (this x H)], },
    have : p.leading_terms.support ⊆ p.support,
    from support_leading_terms_subset _,
    have : p.leading_terms.support ∩ p.support = p.leading_terms.support,
    { rw finset.inter_eq_left_iff_subset,
      exact this },
    nth_rewrite 0 ← this,
    rw [finset.inter_comm, finset.sum_inter_add_sum_diff],
    exact p.as_sum, },
  { rw [total_degree, finset.sup_lt_iff],
    intros b hb,
    rw support_leading_terms at hb,
    rw ← finset.filter_not at hb, -- TODO this was also hard to find maybe a negated version is good
    have := support_sum_monomial_subset _ _ hb,
    simp only [finset.mem_filter] at this,
    cases this,
    rw total_degree,
    exact lt_of_le_of_ne (finset.le_sup this_left) this_right,
    rw [bot_eq_zero],
    exact pos_iff_ne_zero.mpr hp, },
end

lemma finset.sup_eq_bot_iff {α β : Type*} [semilattice_sup β] [order_bot β] (f : α → β)
  (S : finset α) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ :=
begin
  classical,
  induction S using finset.induction with a S haS hi,
  { simp, },
  simp [hi],
end

lemma leading_terms_add_of_total_degree_lt (p q : mv_polynomial ι R)
  (h : q.total_degree < p.total_degree) : (p + q).leading_terms = p.leading_terms :=
by rw [leading_terms, leading_terms, total_degree_add_eq_left_of_total_degree_lt h,
  homogeneous_component_add, homogeneous_component_eq_zero _ q h, add_zero]

lemma homogeneous_component_C_mul (n : ℕ) (p : mv_polynomial ι R) (r : R) :
  homogeneous_component n (C r * p) = C r * homogeneous_component n p :=
begin
  rw homogeneous_component,
  simp only [finsupp.restrict_dom_apply, submodule.subtype_apply, function.comp_app,
    linear_map.coe_comp, set.mem_set_of_eq],
  rw C_mul', -- TODO this has a weird name
  rw finsupp.filter_smul,
  rw C_mul', -- TODO this has a weird name
end

lemma finsupp.support_smul_eq {α M R : Type*} [semiring R] [add_comm_monoid M] [module R M]
  [no_zero_smul_divisors R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} :
  (b • g).support = g.support :=
begin
  ext a,
  simp [finsupp.smul_apply, mem_support_iff, ne.def, hb],
end

@[simp]
lemma leading_terms_C_mul [no_zero_smul_divisors R R] (p : mv_polynomial ι R) (r : R) :
  (C r * p).leading_terms = C r * p.leading_terms :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  have : (C r * p).support = p.support,
  { rw C_mul',
    exact finsupp.support_smul_eq hr, },
  rw [leading_terms, leading_terms, total_degree, this, homogeneous_component_C_mul],
  refl,
end

lemma eq_C_of_total_degree_zero {p : mv_polynomial ι R} (hp : p.total_degree = 0) :
  ∃ r : R, p = C r :=
begin
  letI := classical.dec_eq ι,
  erw finset.sup_eq_bot_iff at hp,
  simp only [mem_support_iff] at hp,
  use coeff 0 p,
  ext,
  by_cases hm : m = 0,
  { simp [hm], },
  rw [coeff_C, if_neg (ne.symm hm)],
  classical,
  by_contradiction h,
  specialize hp m h,
  apply hm,
  rw finsupp.sum at hp, -- TODO this and line below could be a lemma, finsupp.sum_eq_zero_iff?
  simp only [not_imp_self, bot_eq_zero, finsupp.mem_support_iff, finset.sum_eq_zero_iff] at hp,
  ext,
  simp [hp],
end

-- TODO can things be generalized to no_zero_divisors (would require an instance for mv_poly)
-- sadly this adds some imports and requirements not needed in rest of file
@[simp]
lemma leading_terms_mul {S : Type*} [comm_ring S] [is_domain S] (p q : mv_polynomial ι S) :
  (p * q).leading_terms = p.leading_terms * q.leading_terms :=
begin
  by_cases hp : p.total_degree = 0,
  { rcases eq_C_of_total_degree_zero hp with ⟨rp, rfl⟩,
    rw [leading_terms_C_mul, leading_terms_C], },
  by_cases hq : q.total_degree = 0,
  { rcases eq_C_of_total_degree_zero hq with ⟨rq, rfl⟩,
    rw [mul_comm, leading_terms_C_mul, leading_terms_C, mul_comm], },
  have : (p.leading_terms * q.leading_terms).total_degree = p.total_degree + q.total_degree,
  { rw is_homogeneous.total_degree,
    apply is_homogeneous.mul (is_homogeneous_leading_terms p) (is_homogeneous_leading_terms q),
    apply mul_ne_zero,
    { apply leading_terms_ne_zero, -- TODO maybe this can be a lemma ne_zero_of_total_degree_ne_zero
      intro hh,
      subst hh,
      simpa, },
    { apply leading_terms_ne_zero, -- TODO maybe this can be a lemma ne_zero_of_total_degree_ne_zero
      intro hh,
      subst hh,
      simpa, }, },
  rcases eq_leading_terms_add p hp with ⟨wp, hp, tp⟩,
  rw hp,
  rcases eq_leading_terms_add q hq with ⟨wq, hq, tq⟩,
  rw hq,
  simp only [add_mul, mul_add],
  rw [add_assoc, leading_terms_add_of_total_degree_lt, leading_terms_add_of_total_degree_lt,
    leading_terms_add_of_total_degree_lt, leading_terms_idempotent, leading_terms_idempotent,
    leading_terms_eq_self_iff_is_homogeneous],
  { convert is_homogeneous.mul (is_homogeneous_leading_terms _) (is_homogeneous_leading_terms _), },
  { rwa total_degree_leading_terms, },
  { rwa total_degree_leading_terms, },
  { rw this,
    calc _ ≤ max (wp * q.leading_terms).total_degree (p.leading_terms * wq + wp * wq).total_degree :
              total_degree_add _ _
       ... ≤ max (wp * q.leading_terms).total_degree
              (max (p.leading_terms * wq).total_degree (wp * wq).total_degree) :
                max_le_max (le_refl _) (total_degree_add _ _)
       ... ≤ max (wp.total_degree + q.leading_terms.total_degree)
              (max (p.leading_terms * wq).total_degree (wp * wq).total_degree) :
                max_le_max (total_degree_mul _ _) (le_refl _)
       ... ≤ max (wp.total_degree + q.leading_terms.total_degree)
              (max (p.leading_terms.total_degree + wq.total_degree)
                (wp.total_degree + wq.total_degree)) :
                  max_le_max (le_refl _) (max_le_max (total_degree_mul _ _) (total_degree_mul _ _))
       ... < p.total_degree + q.total_degree : _,
    simp only [total_degree_leading_terms, max_lt_iff, add_lt_add_iff_right, add_lt_add_iff_left],
    exact ⟨tp, tq, add_lt_add tp tq⟩, },
end

lemma total_degree_mul_eq {S : Type*} [comm_ring S] [is_domain S] {p q : mv_polynomial ι S}
  (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).total_degree = p.total_degree + q.total_degree :=
begin
  rw [← total_degree_leading_terms, ← total_degree_leading_terms p, ← total_degree_leading_terms q,
    leading_terms_mul, is_homogeneous.total_degree],
  apply is_homogeneous.mul;
  simp [is_homogeneous_leading_terms],
  apply mul_ne_zero (leading_terms_ne_zero hp) (leading_terms_ne_zero hq),
end

end leading_terms

end mv_polynomial

namespace mv_polynomial
section

-- generalized version of the unprimed version
lemma support_sum_monomial_subset' [decidable_eq ι] {α : Type*} (S : finset α) (g : α → ι →₀ ℕ)
  (f : α → R) : support (∑ v in S, monomial (g v) (f v)) ⊆ S.image g :=
begin
  letI := classical.dec_eq α,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  { rw finset.sum_insert hs,
    apply finset.subset.trans support_add,
    apply finset.union_subset,
    { apply finset.subset.trans support_monomial_subset _,
      rw finset.image_insert,
      convert finset.subset_union_left _ (finset.image g S), },
    { apply finset.subset.trans hsi _,
      rw finset.image_insert,
      exact finset.subset_insert (g s) (finset.image g S), }, },
end
open_locale pointwise

lemma support_mul' [decidable_eq ι] (p q : mv_polynomial ι R) :
  (p * q).support ⊆ p.support + q.support :=
begin
  -- TODO this was really hard to find, maybe needs a docstring or alias?
  rw [p.as_sum, q.as_sum, finset.sum_mul_sum],
  simp_rw [monomial_mul],
  rw [support_sum_monomial_coeff, support_sum_monomial_coeff],
  exact finset.subset.trans (support_sum_monomial_subset' _ _ _) (finset.subset.refl _),
end

end

end mv_polynomial