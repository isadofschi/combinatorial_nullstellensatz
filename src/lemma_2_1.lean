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
import fin_succ_equiv
import polynomial

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

namespace multiset
-- see #10726 https://github.com/leanprover-community/mathlib/pull/10726
theorem count_map_eq_count' {α β : Type* }[decidable_eq β] {f : α → β} (s : multiset α)
  (h : function.injective f) (x : α) : (s.map f).count (f x) = s.count x :=
begin
  suffices : (filter (λ (a : α), f x = f a) s).count x = card (filter (λ (a : α), f x = f a) s),
  { rw [count, countp_map, ← this],
    exact count_filter_of_pos rfl },
  { simp only [count_filter_of_pos],
    have h' : ((λ (a : α), f x = f a) : α → Prop)  = eq x,
    { ext y,
      apply iff.intro,
      exact λ h', h h',
      intro h',
      rw h', },
    simp only [h', count, countp_eq_card_filter],
    congr, }
end

end multiset

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
  apply (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv R n)).1,
  apply (polynomial.eq_zero_iff_every_coeff_zero ((fin_succ_equiv R n) f)).1,
  intro i,
  apply hn (polynomial.coeff ((fin_succ_equiv R n) f) i),
  exact λ j, lt_of_le_of_lt (degree_of_coeff_fin_suc_equiv f j i) (hS j.succ),
  intros s hs,
  rw [ ← coeff_eval_eq_eval_coeff, (polynomial.eq_zero_iff_every_coeff_zero (polynomial.map (eval s)
       ((fin_succ_equiv R n) f))).2 ],
  by_contradiction c1,
  have h0 : ∀ s' : fin n → R, (∀ i : fin n, s' i ∈ S i.succ) → ∀ y : R, y ∈ S 0 →  
    polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv R n) f)) = 0,
  { intros s' hs' y hy,
    rw [← eval_eq_eval_mv_eval', hz],
    intro i,
    by_cases c : i ≠ 0,
    { rwa [ ←fin.succ_pred i c, fin.cons_succ],
      exact hs' (fin.pred i c) },
    { simp only [not_not] at c,
      rwa [c, fin.cons_zero] } },
  simpa using lt_of_le_of_lt ((polynomial.number_zeroes_field c1 (h0 _ hs)).trans _) (hS 0),
  rw ← nat_degree_fin_suc_equiv f,
  exact nat_degree_eval_le_nat_degree s (fin_succ_equiv R n f),
end

private noncomputable def bundled_map_domain_injective {α β : Type*} {f : α → β} (h : function.injective f) :
 (α →₀ ℕ)  ↪ (β →₀ ℕ) := ⟨finsupp.map_domain f, finsupp.map_domain_injective h⟩

lemma support_rename_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
  {f : σ → τ} (h : function.injective f) : 
  ((rename f p).support : finset (τ →₀ ℕ)) = 
  finset.map (bundled_map_domain_injective h) p.support :=
begin
  rw finset.ext_iff,
  intro a,
  simp only [exists_prop, finset.mem_map, mem_support_iff, ne.def],
  apply iff.intro,
  intro h1,
  cases coeff_rename_ne_zero f p a h1 with d hd,
  use d,
  rw bundled_map_domain_injective,
  simp only [function.embedding.coe_fn_mk],
  exact hd.symm,
  intro h,
  cases h with b hb,
  simpa only [← hb.2, bundled_map_domain_injective, function.embedding.coe_fn_mk,
              coeff_rename_map_domain f h p b] using hb.1,
end

lemma multiset.sup_map {α β γ : Type* } {f : β → γ} (h : function.injective f) (g : α → multiset β) (s : finset α) : 
  multiset.map f (s.sup g) = s.sup (λ x,  multiset.map f (g x)) :=
begin
  apply finset.cons_induction_on s,
  simp,
  clear s,
  intros a s h_a_s h_ind,
  repeat {rw finset.sup_cons},
  rw ← h_ind,
  dsimp,
  rw multiset.map_union h,
end

lemma rename_degrees_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
  {f : σ → τ} (h : function.injective f) : degrees (rename f p) = (degrees p).map f :=
begin
  have h1 : (λ (x : σ →₀ ℕ), multiset.map f (finsupp.to_multiset x)) 
    = λ x, (x.map_domain f).to_multiset,
  { ext,
    rw finsupp.to_multiset_map, },
  simp only [degrees, multiset.sup_map h, h1, support_rename_injective h, finset.sup_map],
  congr,
end

lemma degree_of_rename_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
{f : σ → τ} (h : function.injective f) (i : σ) : degree_of i p = degree_of (f i) (rename f p) :=
by simp [degree_of, rename_degrees_injective h, multiset.count_map_eq_count' (p.degrees) h]

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
    have h : 0 < (S i).card,
    { have t:= hS i,
      linarith },
    convert h, },
  have hs0 : ∃ s0 : σ → R, (∀ i : σ, s0 i ∈ S i ) := by apply classical.skolem.1 h_S_nonempty,
  by_cases c : nonempty (fin n),
  { have hS' : ∀ i : (fin n), degree_of i g < ((S ∘ ψ) i).card,
    { intro i,
      have t := hS (ψ i),
      convert t,
      exact degree_of_rename_injective hψ i },
    have hz' : ∀ s : (fin n) → R, (∀ i : fin n, s i ∈ (S ∘ ψ) i ) → eval s g = 0,
    { intros s' h,
      cases hs0 with s0 hs0,
      let φ := @function.inv_fun (fin n) σ c ψ,
      have φ_left_inv := @function.left_inverse_inv_fun (fin n) σ c ψ hψ,
      let s : σ → R := λ i, if h : ∃ j : fin n, ψ j = i then (s' ∘ φ) i else s0 i,
      have hs' : s' = s ∘ ψ,
      { ext,
        have hx  : ∃ j, ψ j = ψ x := ⟨x, by refl⟩,
        simp only [function.comp_app, s, hx, dif_pos, φ, φ_left_inv x], },
      have hs : ∀ (i : σ), s i ∈ S i,
      { intro i,
        by_cases ch : ∃ (j : fin n), ψ j = i,
        { simp only [s, dite_eq_ite, function.comp_app, if_pos, ch, φ ],
          cases ch with j hj,
          simpa [← hj, φ_left_inv j] using h j},
        { simpa only [s, dite_eq_ite, if_neg, ch, not_false_iff] using hs0 i } },
      rw hs',
      convert hz s hs, 
      -- should this be a lemma called `eval_rename`?
      simp only [eval],
      rw eval₂_hom_rename },
    simp [lemma_2_1_fin_n g (S ∘ ψ ) hS' hz'] },
  { simp only [not_nonempty_iff] at c,
    cases @C_surjective R _ (fin n) c g with a ha,
    simp only [←ha, rename_C],
    simp only [←ha, rename_C] at hz,
    cases hs0 with s0 hs0,
    have t := hz s0 hs0,
    simp only [eval_C] at t,
    rw t,
    simp },
end

end mv_polynomial
