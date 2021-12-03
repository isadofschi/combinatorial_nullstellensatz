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

universes u v

variables {α : Type v}

open_locale big_operators

local attribute [instance] classical.prop_decidable

namespace mv_polynomial

/- Lemma 2.1 in Alon's "Combinatorial Nullstellensatz" paper. -/
lemma lemma_2_1 { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin n) F)
  (S : fin n → finset F)
  (hS : ∀ i : fin n, degree_of i f < (S i).card) 
  (hz : ∀ s : fin n → F, (∀ i : fin n, s i ∈ S i ) → eval s f = 0) :
  f = 0 :=
begin
  induction n with n hn,
  simp only [forall_const] at hz,
  apply (ring_equiv.map_eq_zero_iff (is_empty_ring_equiv F (fin 0))).1,
  simp only [is_empty_ring_equiv_apply],
  simpa using (hz fin.is_empty.elim),
  apply (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv F n)).1,
  apply (polynomial.eq_zero_iff_every_coeff_zero ((fin_succ_equiv F n) f)).1,
  intro i,
  apply hn (polynomial.coeff ((fin_succ_equiv F n) f) i),
  exact λ j, lt_of_le_of_lt (degree_of_coeff_fin_suc_equiv f j i) (hS j.succ),
  intros s hs,
  rw ← coeff_eval_eq_eval_coeff,
  rw (polynomial.eq_zero_iff_every_coeff_zero (polynomial.map (eval s) ((fin_succ_equiv F n) f))).2,
  by_contradiction c1,
  have h0 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i.succ) → ∀ y : F, y ∈ S 0 →  
    polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv F n) f)) = 0,
  { intros s' hs' y hy,
    rw [← eval_eq_eval_mv_eval', hz],
    intro i,
    by_cases c : i ≠ 0,
    { let i' := fin.pred i c,
      have r : i = i'.succ := by simp,
      rwa [ r, fin.cons_succ],
      exact hs' i' },
    simp only [not_not] at c,
    rwa [c, fin.cons_zero] },
  simpa using lt_of_le_of_lt ((polynomial.number_zeroes_field c1 (S 0) (h0 _ hs)).trans _) (hS 0),
  rw ← nat_degree_fin_suc_equiv f,
  exact nat_degree_eval_le_nat_degree s (fin_succ_equiv F n f),
end

end mv_polynomial
