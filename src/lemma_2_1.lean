/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic
import pr.fin_succ_equiv
import pr.polynomial
import pr.rename

/-
# Add one variable

## Main results

- `lemma_2_1`: Let F be a field and f ∈ F[x₀,…,xₙ]. Suppose that for 0 ≤ i ≤ n,
  the degree of f in xᵢ is at most tᵢ. Let S₀,…,Sₙ ⊆ F be subsets such that tᵢ < |Sᵢ|.
  Suppose that f(s₀,…,sₙ) = 0 for each (s₀,…,sₙ) ∈ S₀ × … × Sₙ. Then f = 0.

  This is Lemma 2.1 in Alon's paper "Combinatorial Nullstellensatz".
-/

open_locale big_operators

local attribute [instance] classical.prop_decidable

namespace mv_polynomial

private lemma lemma_2_1_fin_n { n : ℕ } {R : Type*} [comm_ring R] [is_domain R]
  (f : mv_polynomial (fin n) R)
  (S : fin n → finset R)
  (hS : ∀ i : fin n, degree_of i f < (S i).card) 
  (hz : ∀ s : fin n → R, (∀ i : fin n, s i ∈ S i ) → eval s f = 0) :
  f = 0 :=
begin
  induction n with n hn,
  simp only [forall_const] at hz,
  apply (ring_equiv.map_eq_zero_iff (is_empty_ring_equiv R (fin 0))).1,
  simp only [is_empty_ring_equiv_apply],
  simpa using (hz fin.is_empty.elim),
  apply (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv R n)).1 ∘ polynomial.ext_iff.2,
  intro i,
  rw ← polynomial.coeff_zero i,
  apply hn (polynomial.coeff ((fin_succ_equiv R n) f) i),
  exact λ j, lt_of_le_of_lt (degree_of_coeff_fin_succ_equiv f j i) (hS j.succ),
  intros s hs,
  rw [ ← coeff_eval_eq_eval_coeff],
  suffices h : polynomial.map (eval s) (fin_succ_equiv R n f) = 0,
  { rw h,
    simp },
  by_contradiction c1,
  suffices h1 : (S 0).val ⊆ (polynomial.map (eval (λ (i : fin n), s i)) (fin_succ_equiv R n f)).roots, 
  { simpa using lt_of_le_of_lt ((polynomial.card_le_degree_of_finset_roots c1 h1).trans _) (hS 0),
    rw ← nat_degree_fin_succ_equiv f,
    -- exact polynomial.nat_degree_le_nat_degree (polynomial.degree_mono (support_eval s (fin_succ_equiv R n f))),
    exact nat_degree_eval_le_nat_degree s (fin_succ_equiv R n f) },
  suffices h0 : ∀ s' : fin n → R, (∀ i : fin n, s' i ∈ S i.succ) → ∀ y : R, y ∈ S 0 →  
    polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv R n) f)) = 0,
  { rw multiset.subset_iff,
    intros x hx,
    rw polynomial.mem_roots c1,
    simpa using h0 _ hs x hx },  
  intros s' hs' y hy,
  rw [← eval_eq_eval_mv_eval', hz],
  intro i,
  by_cases c : i ≠ 0,
  { rw [ ←fin.succ_pred i c, fin.cons_succ],
    exact hs' (fin.pred i c) },
  { rwa [not_not.1 c, fin.cons_zero] },
end

/- Lemma 2.1 in Alon's "Combinatorial Nullstellensatz" paper. -/
lemma lemma_2_1 {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ] (f : mv_polynomial σ R)
  (S : σ → finset R) (hS : ∀ i : σ, degree_of i f < (S i).card) 
  (hz : ∀ s : σ → R, (∀ i : σ, s i ∈ S i ) → eval s f = 0) : f = 0 :=
begin
  cases exists_fin_rename f with n hn,
  cases hn with ψ hψ,
  cases hψ with hψ hq,
  cases hq with g hg,
  rw hg,
  rw hg at hS,
  rw hg at hz,
  clear hg f,
  have h_S_nonempty : ∀ i, ∃ x, x ∈ S i,
  { intro i,
    apply multiset.card_pos_iff_exists_mem.1,
    convert lt_of_le_of_lt (zero_le _) (hS i), },
  have hs0 : ∃ s0 : σ → R, (∀ i : σ, s0 i ∈ S i ) := by apply classical.skolem.1 h_S_nonempty,
  by_cases c : nonempty (fin n),
  { have hS' : ∀ i : (fin n), degree_of i g < ((S ∘ ψ) i).card,
    { intro i,
      convert hS (ψ i),
      exact degree_of_rename_of_injective hψ i },
    suffices hz' : ∀ s : (fin n) → R, (∀ i : fin n, s i ∈ (S ∘ ψ) i ) → eval s g = 0,
      by simp [lemma_2_1_fin_n g (S ∘ ψ ) hS' hz'],
    intros s' h,
    cases hs0 with s0 hs0,
    let φ := @function.inv_fun (fin n) σ c ψ,
    have φ_left_inv := @function.left_inverse_inv_fun (fin n) σ c ψ hψ,
    let s : σ → R := λ i, if h : ∃ j : fin n, ψ j = i then (s' ∘ φ) i else s0 i,
    have hs' : s' = s ∘ ψ,
    { ext,
      have hx  : ∃ j, ψ j = ψ x := ⟨x, by refl⟩,
      simp only [function.comp_app, s, hx, dif_pos, φ, φ_left_inv x], },
    suffices hs : ∀ (i : σ), s i ∈ S i,
    { rw hs',
      convert hz s hs, 
      simp only [eval, eval₂_hom_rename] },
    intro i,
    by_cases ch : ∃ (j : fin n), ψ j = i,
    { simp only [s, dite_eq_ite, function.comp_app, if_pos, ch, φ ],
      cases ch with j hj,
      simpa [← hj, φ_left_inv j] using h j},
    { simpa only [s, dite_eq_ite, if_neg, ch, not_false_iff] using hs0 i } },
  { simp only [not_nonempty_iff] at c,
    cases @C_surjective R _ (fin n) c g with a ha,
    simp only [←ha, rename_C],
    simp only [←ha, rename_C] at hz,
    cases hs0 with s0 hs0,
    have t := hz s0 hs0,
    rw [eval_C] at t,
    simp [t] },
end

end mv_polynomial
