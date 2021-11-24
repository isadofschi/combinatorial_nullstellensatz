/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import algebra.algebra.basic
import degree
import monomial_reduction
import assorted_lemmas
import add_one_variable
import data.mv_polynomial.comm_ring

/-!
# Combinatorial Nullstellensatz

In this file we prove the Combinatorial Nullstellensatz.
Our reference is
  N. Alon, Combinatorial Nullstellensatz, Combinatorics, Probability and Computing 8 (1999), 7-29.

## Main results

- `combinatorial_nullstellensatz`: Theorem 1.2 in Alon's paper.
- `combinatorial_nullstellensatz'`: Theorem 1.1 in Alon's paper.

-/

universes u v

variables {α : Type v}

open_locale big_operators

namespace mv_polynomial

/- Theorem 1.1 in Alon's paper. -/
theorem combinatorial_nullstellensatz' { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin n) F) 
  (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) 
  (hz : ∀ s : fin n → F, (∀ i : fin n, s i ∈ S i ) → eval s f = 0) :
  ∃ h : fin n → mv_polynomial (fin n) F,
  (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ f = ∑ i : fin n, h i * ∏ s in (S i), (X i - C s)
:=
begin
  let g : fin n → mv_polynomial (fin n) F := λ i, ∏ s in (S i), (X i - C s),
  let t_map : fin n → ℕ := λ i, (S i).card - 1,
  have hf : ∀ a, t_map a ≠ 0 → a ∈ (finset.fin_range n),
  { intro a,
    intro h,
    simp },
  let t : fin n →₀ ℕ := finsupp.on_finset (finset.fin_range n) t_map hf,
  have h_card_S' : ∀ i : fin n, t i + 1 = (S i).card,
  { intro i,
    simp only [finsupp.on_finset_apply],
    have t_mapi : t_map i = (S i).card -1 := by refl,
    rw t_mapi,
    apply nat.sub_add_cancel,
    have hSi := hS i,
    linarith },
  have exists_h := reduce_degree' S hS f,
  cases exists_h with h h_h,
  use h,
  apply and.intro,
  exact h_h.1,
  let P := f - (∑ i : fin n, h i * ∏ s in (S i), (X i - C s)),
  have tt : P = 0,
  { apply lemma_2_1 P t _ S _ _,
    intro j,
    have x := h_h.2 j,
    rw ← h_card_S' j at x,
    linarith,
    intro i,
    have h6 := h_card_S' i,
    linarith,
    intros s h_s,
    simp only [ring_hom.map_sub],
    rw hz s h_s,
    rw eval_sum,
    simp only [zero_sub, neg_eq_zero, ring_hom.map_mul],
    have hz' : ∑ (x : fin n), (eval s) (h x) * (eval s) (∏ (s : F) in S x, (X x - C s))
      = ∑ (x : fin n), (eval s) (h x) * (0:F),
    { congr,
      ext i,
      rw eval_is_zero (S i) (hS i) s i (h_s i) },
    rw hz',
    simp },
  rw ← sub_eq_zero,
  exact tt,
end

theorem combinatorial_nullstellensatz''
{ n : ℕ } {F : Type u} [field F]
(f : mv_polynomial (fin n) F) 
(t : fin n →₀ ℕ)
(h_max : max_degree_monomial t f)
(S : fin n → finset F)
(h_card_S : ∀ i : fin n, t i + 1 = (S i).card) :
∃ s : fin n → F, (∀ i : fin n, s i ∈ S i ) ∧ eval s f ≠ (0:F) :=
begin
  have h_coef_t := h_max.1, have h_deg := h_max.2,
  have h_card_S' : ∀ i : fin n, t i < (S i).card, 
  { intro i, 
    have t : t i < t i + 1 := by linarith,
    rw h_card_S i at t, 
    exact t },
  by_contra,
  have h' : ∀ s : fin n → F, (∀ i : fin n, s i ∈ S i) → eval s f = (0:F),
  { intro s,
    rw not_exists at h,
    have hs := h s,
    rw not_and at hs,
    intro hfi,
    have r := hs hfi, 
    simpa using r },
  clear h,
  have hS : ∀ i : fin n, 0 < (S i).card := λ i , lt_of_le_of_lt (by linarith) (h_card_S' i), 
  have h'' := combinatorial_nullstellensatz' f S hS h',
  clear hS, clear h',
  cases h'' with h h1,
  have h_deg_h := h1.1, have h_fgh := h1.2, clear h1,
  have h_nonzero : coeff t (∑ i : fin n, h i * ∏ s in (S i), (X i - C s)) ≠  0,
  { rw ← h_fgh,
    exact h_coef_t },
  clear h_fgh h_coef_t,
  suffices h_zero : coeff t (∑ i : fin n, h i * ∏ s in (S i), (X i - C s)) =  0, by cc,
    clear h_nonzero,
    have h_zero' : (λ i : fin n, coeff t (h i * ∏ s in (S i), (X i - C s))) = (λ i : fin n, (0:F)),
    { ext i,
      -- using `by_contradiction` here gave deterministic timeout:
      by_cases c1 : coeff t (h i * ∏ (s : F) in S i, (X i - C s)) = 0,
        exact c1,
      have h1 : total_degree (h i * ∏ s in (S i), (X i - C s)) ≤ monomial_degree t,
      { rw total_degree_mul',
        rw lemita4,
        have h2 : total_degree f = monomial_degree t :=
          ((max_degree_monomial_iff_nonzero_coeff_and_realizes_total_degree t f).1 h_max).2,
        rw ← h2,
        by_cases hi0 : h i = 0,
        { exfalso,
          have  hcoeff0 : coeff t (h i * ∏ (s : F) in S i, (X i - C s)) = 0,
          { rw hi0,
            rw zero_mul,
            simp,
          },
          cc },
        have r := h_deg_h i,
        cc,
        exact t },
      by_cases c : monomial_degree t > total_degree (h i * ∏ (s : F) in S i, (X i - C s)),
      { exact coeff_zero_of_degree_greater_than_total_degree t _ c },
      have c' : monomial_degree t = total_degree (h i * ∏ (s : F) in S i, (X i - C s)) :=
        by linarith,
      have ht: max_degree_monomial t (h i * ∏ (s : F) in S i, (X i - C s)),
      { rw max_degree_monomial_iff_nonzero_coeff_and_realizes_total_degree,
        apply and.intro,
        exact c1,
        symmetry,
        exact c' },
      have h_dom : dominant_monomial (finsupp.single i ((S i).card)) (∏ s in S i, (X i - C s)),
      { apply lemita1,
        exact t },
      by_cases c'' : h i ≠ 0,
      { have h_f := dominant_monomial_of_factor_is_factor_of_max_degree_monomial (S i) t 
          (finsupp.single i ((S i).card)) (h i) (∏ (s : F) in S i, (X i - C s)) ht c'' h_dom,
        have hfi := h_f i,
        simp only [finsupp.single_eq_same] at hfi,
        rw ← h_card_S i at hfi,
        exfalso,
        linarith },
      simp only [not_not] at c'',
      rw c'',
      rw zero_mul,
      simp },
    rw mv_polynomial.coeff_sum,
    rw h_zero',
    simp,
end

/-
Theorem 1.2 in Alon's paper.
-/
theorem combinatorial_nullstellensatz
{ n : ℕ } {F : Type u} [field F]
(f : mv_polynomial (fin n) F) 
(t : fin n →₀ ℕ)
(h_max : max_degree_monomial t f)
(S : fin n → finset F)
(h_card_S : ∀ i : fin n, t i < (S i).card) :
∃ s : fin n → F, (∀ i : fin n, s i ∈ S i ) ∧ eval s f ≠ 0 :=
begin
  have S' : fin n → finset F, sorry,
  have h_S_S' : ∀ i : fin n, S' i ⊆ S i, sorry,
  have h_card_S' : ∀ i : fin n, t i + 1 = (S' i).card, sorry,
  have exists_s := combinatorial_nullstellensatz'' f t h_max S' h_card_S',
  cases exists_s with s h_s',
  use s,
  apply and.intro,
  intro i,
  have h' := h_s'.1 i,
  have h'' := h_S_S' i,
  exact finset.mem_of_mem_of_subset h' h'',
  exact h_s'.2,
end

end mv_polynomial
