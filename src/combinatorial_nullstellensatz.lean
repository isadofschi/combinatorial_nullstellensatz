/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import algebra.algebra.basic
import degree
import degree_new
import reduce_degree
import lemma_2_1
import data.mv_polynomial.comm_ring
import lemmas_g_S

/-!
# Combinatorial Nullstellensatz

In this file we prove the Combinatorial Nullstellensatz.
Our reference is
  N. Alon, Combinatorial Nullstellensatz, Combinatorics, Probability and Computing 8 (1999), 7-29.

## Main results

- `combinatorial_nullstellensatz`: Theorem 1.2 in Alon's paper.
- `combinatorial_nullstellensatz'`: Theorem 1.1 in Alon's paper.

-/

open_locale big_operators

namespace mv_polynomial

/- Theorem 1.1 in Alon's paper. -/
theorem combinatorial_nullstellensatz' {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
 [decidable_eq σ] (f : mv_polynomial σ R) (S : σ → finset R) (hS : ∀ i : σ, 0 < (S i).card)
  (hz : ∀ s : σ → R, (∀ i : σ, s i ∈ S i ) → eval s f = 0) : 
  ∃ h : σ → mv_polynomial σ R, (∀ i : σ, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
    ∧ f = ∑ i : σ, h i * ∏ s in (S i), (X i - C s) :=
begin
  cases (reduce_degree_special_case S hS f) with h h_h,
  use h,
  apply and.intro,
  exact h_h.1,
  rw ← sub_eq_zero,
  apply lemma_2_1 _ S (λ j, h_h.2 j) _,
  intros s h_s,
  simp only [ring_hom.map_sub, hz s h_s, eval_sum, zero_sub, neg_eq_zero, ring_hom.map_mul],
  apply finset.sum_eq_zero,
  intros i hi,
  simp [eval_g_S_eq_zero (S i) (hS i) s i (h_s i)],
end

theorem combinatorial_nullstellensatz'' {R σ : Type*} [comm_ring R] [is_domain R]
  [fintype σ] [decidable_eq σ] (f : mv_polynomial σ R) (t : σ →₀ ℕ)
  (h_max : max_degree_monomial t f) (S : σ → finset R) (h_card_S : ∀ i : σ, t i + 1 = (S i).card) :
  ∃ s : σ → R, (∀ i : σ, s i ∈ S i ) ∧ eval s f ≠ 0 :=
begin
  by_contra hc,
  cases combinatorial_nullstellensatz' f S (λ i , lt_of_le_of_lt (zero_le (t i)) (by simp [←h_card_S i]))
    (by simpa using hc) with h h1,
  clear hc,
  suffices h_zero : coeff t (∑ i : σ, h i * ∏ s in (S i), (X i - C s)) =  0,
  { simpa [h_zero, h1.2] using h_max.1 },
  simp only [coeff_sum],
  apply finset.sum_eq_zero,
  intros i hi,
  by_cases c1 : coeff t (h i * ∏ (s : R) in S i, (X i - C s)) = 0,
  { exact c1 },
  { by_cases c : monomial_degree t > total_degree (h i * ∏ (s : R) in S i, (X i - C s)),
    { exact coeff_zero_of_degree_greater_than_total_degree t _ c },
    { by_cases c'' : h i = 0,
      { simp [c''] },
      { simpa only [finsupp.single_eq_same, ←h_card_S, add_le_iff_nonpos_right, le_zero_iff] using
          dominant_monomial_of_factor_is_factor_of_max_degree_monomial (S i) t 
            (finsupp.single i (S i).card) (h i) (∏ (s : R) in S i, (X i - C s))
            ⟨mem_support_iff.mpr c1, le_antisymm (not_lt.mp c) _⟩  c'' (dominant_monomial_g_S (S i) i) i,
        by_cases c' : h i = 0,
        { simp [c', zero_mul] },
        { rw [total_degree_mul' c' (g_S_ne_0 (S i) i), total_degree_g_S, h_max.2],
          by_cases hi0 : h i = 0,
          { simpa [hi0] using c1 },
          { exact or.resolve_left (h1.1 i) hi0 } } } } },
end

private lemma choose_smaller_sets {R σ : Type*} (S : σ → finset R) (t : σ →₀ ℕ)
  (h_card_S : ∀ i : σ, t i < (S i).card) : ∃ S' : σ → finset R,
    (∀ i : σ, S' i ⊆ S i) ∧ (∀ i : σ, (S' i).card = t i + 1) :=
begin
  have t := λ i, finset.exists_smaller_set (S i) (t i +1) (h_card_S i),
  convert classical.skolem.1 t,
  ext S',
  rw forall_and_distrib,
end

/-
  Theorem 1.2 in Alon's paper.
-/
theorem combinatorial_nullstellensatz {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
 [decidable_eq σ] (f : mv_polynomial σ R) (t : σ →₀ ℕ) (h_max : max_degree_monomial t f)
  (S : σ → finset R) (h_card_S : ∀ i : σ, t i < (S i).card) : ∃ s : σ → R,
    (∀ i : σ, s i ∈ S i ) ∧ eval s f ≠ 0 :=
begin
  cases choose_smaller_sets S t h_card_S with S' hS',
  cases combinatorial_nullstellensatz'' f t h_max S' (λ i,  ((hS'.2) i).symm) with s h_s',
  exact ⟨ s, ⟨λ i, finset.mem_of_subset (hS'.1 i) (h_s'.1 i), h_s'.2 ⟩⟩,
end

end mv_polynomial
