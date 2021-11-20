/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.field
import degree

universe u

open set function finsupp add_monoid_algebra

open_locale big_operators

namespace mv_polynomial

lemma induction_on_monomial 
  {σ : Type} {R : Type*} [comm_semiring R]
  {M : mv_polynomial σ R → Prop}
  (h_C : ∀a, M (C a)) 
  (h_X : ∀p n, M p → M (p * X n)) :
  ∀s a, M (monomial s a) :=
begin
  assume s a,
  apply @finsupp.induction σ ℕ _ _ s,
  { show M (monomial 0 a), from h_C a, },
  { assume n e p hpn he ih,
    have : ∀e:ℕ, M (monomial p a * X n ^ e),
    { intro e,
      induction e,
      { simp [ih] },
      { simp [ih, pow_succ', (mul_assoc _ _ _).symm, h_X, e_ih] } },
    simp [add_comm, monomial_add_single, this] }
end

/- This is the flavor of induction we need here -/
lemma induction_on'' {σ : Type} {R : Type*} [comm_semiring R]
{M : mv_polynomial σ R → Prop} (p : mv_polynomial σ R)
  (h_C : ∀a, M (C a)) 
  (h_add_weak : ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R), 
    a ∉ f.support → b ≠ 0 → M f → M (single a b + f))
  (h_X : ∀p n, M p → M (p * X n)) :
  M p :=
have ∀s a, M (monomial s a),
begin
  assume s a,
  apply @finsupp.induction σ ℕ _ _ s,
  { show M (monomial 0 a), from h_C a, },
  { assume n e p hpn he ih,
    have : ∀e:ℕ, M (monomial p a * X n ^ e),
    { intro e,
      induction e,
      { simp [ih] },
      { simp [ih, pow_succ', (mul_assoc _ _ _).symm, h_X, e_ih] } },
    simp [add_comm, monomial_add_single, this] }
end,
finsupp.induction p
  (by have : M (C 0) := h_C 0; rwa [C_0] at this)
    h_add_weak

/-
  M' is a workaround for a "cannot sinthetize placeholder context error". How should I do this?
-/
private def M'  (n : ℕ ) (F : Type u) [field F] (S : fin n → finset F)
(hS : ∀ i : fin n, 0 < (S i).card)
: mv_polynomial (fin n) F → Prop :=
  λ f, ∃ h : fin n → mv_polynomial (fin n) F,
 (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ( ∀ m : fin n →₀ ℕ, m ∈ (f - (∑ i : fin n, h i * ∏ s in (S i), (X i - C s))).support → 
      ∀ j : fin n, m j < (S j).card)

private def M { n : ℕ } {F : Type u} [field F]{S : fin n → finset F}
  {hS : ∀ i : fin n, 0 < (S i).card} 
  : mv_polynomial (fin n) F → Prop := λ f, M' n F S hS f

private lemma h_C { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) : ∀ (a : F), M' n F S hS (C a) :=
begin
  intro a,
  rw M',
  use λ i, 0,
  apply and.intro,
  intro i,
  left,
  refl,
  intro m,
  intro j,
  have h: C a - ∑ (i : fin n), 0 * ∏ (s : F) in S i, (X i - C s) = C a,
  { have h1 : (λ i ,  0 * ∏ s in S i, (X i - C s)) = (λ i, 0),
    { ext,
      rw zero_mul },
    rw h1,
    simp, },
  sorry,
  /-
  rw h at m,
  rw C_apply at m,
  by_cases c : a = 0,
  {
    sorry, -- TODO use support_monomial
  },
  sorry -- TODO use support_monomial
  -/
end

private lemma h_X { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
 (hS : ∀ i : fin n, 0 < (S i).card) :  ∀ (p : mv_polynomial (fin n) F) (j : fin n), 
    M' n F S hS p → M' n F S hS (p * X j) :=
begin
  intros p j h_Mp,
  cases h_Mp with h_p hhp,
  rw M',
  -- TODO h_p * X j may or not work, depending on the degree of h_p in X j.
  -- Let g_j =  ∏ s in (S j), (X j - C s)
  -- If it does not work, we modify it by substracting 
  -- g_j times the coefficient in h_p (seen as a polynomial in X j) of (X j)^(S j).card-1
  sorry
end

private lemma h_add_weak { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) : 
∀ (a : fin n →₀ ℕ) (b : F) (f : (fin n →₀ ℕ) →₀ F), 
    a ∉ f.support → b ≠ 0 → M' n F S hS f → M' n F S hS (single a b + f) :=
begin
  intros a b f h_a h_b h_Mf,
  cases h_Mf with h_f hh_f,
  have h_MCa := induction_on_monomial (h_C S hS) (h_X S hS) a b,
  cases h_MCa with h_Ca hhC_a,
  rw M',
  use h_Ca + h_f,
  apply and.intro,
  intro i,
  by_cases c : (h_Ca + h_f) i = 0,
  { left,
    exact c },
  right,
  rw total_degree_add_monomial f a b h_a h_b,
  have re : ∀i,  (h_Ca + h_f) i = h_Ca i + h_f i,
  { intro i,
    simp,
  },
  rw re,
  -- split in cases h_Ca = 0, h_f = 0,
  -- use total_degree_add, total_degree_add_monomial
  sorry, --TODO
  intros m j,
  sorry -- TODO
end

lemma reduce_degree { n : ℕ } {F : Type u} [field F]
  (S : fin n → finset F) (hS : ∀ i : fin n, 0 < (S i).card)
  (f : mv_polynomial (fin n) F) :
  ∃ h : fin n → mv_polynomial (fin n) F,
  (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ( ∀ m : fin n →₀ ℕ, m ∈ (f - (∑ i : fin n, h i * ∏ s in (S i), (X i - C s))).support → 
      ∀ j : fin n, m j < (S j).card) := 
begin
  have h : M f,
  {
    apply induction_on'' f,
    apply h_C S hS,
    apply h_add_weak S hS,
    apply h_X S hS,
  },
  rw M at h, rw M' at h,
  exact h,
end

end mv_polynomial