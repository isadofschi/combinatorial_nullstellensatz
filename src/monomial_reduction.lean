/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.field
import degree
import topology.metric_space.algebra


/-
# Reduce degree

## Main results

- `reduce_degree`: corresponds to the following paragraph in the proof of Theorem 1.1 in Alon's
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

namespace finset
variable {α : Type*}
theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : finset α)) : x = y := sorry
end finset 

section open decidable tactic
variables {α : Type u} [linear_order α]

lemma max_le_le {a b c d: ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) : max a c ≤ max b d := sorry

lemma max_add {a b c: ℕ} : max a b + c = max (a+c) (b+c) := sorry

end

lemma what_is_the_name_for_this_one {p q : Prop}(h1 : ¬ p) (h2 : p ∨ q) : q :=
begin
  cc,
end


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

local attribute [instance] classical.prop_decidable --esta permitido usar esto?

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
  intros m hm j,
  have h: C a - ∑ (i : fin n), 0 * ∏ (s : F) in S i, (X i - C s) = C a,
  { have h1 : (λ i ,  0 * ∏ s in S i, (X i - C s)) = (λ i, 0),
    { ext,
      rw zero_mul },
    rw h1,
    simp, },
  rw h at hm,
  rw C_apply at hm,
  by_cases c : a = 0,
  { exfalso,
    rw c at hm,
    rw support_monomial at hm,
    simp only [finset.not_mem_empty, if_true, eq_self_iff_true] at hm,
    exact hm,
  },
  rw support_monomial at hm,
  rw if_neg at hm,
  have hm0 : m = 0 := finset.eq_of_mem_singleton hm,
  rw hm0,
  simp only [coe_zero, pi.zero_apply],
  exact hS j,
  exact c,
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

private lemma h_add_weak_aux_comp { n : ℕ } {F : Type u} [field F]
(S : fin n → finset F) (p q : mv_polynomial (fin n) F) 
(h1 h2 : fin n → mv_polynomial (fin n) F) : 
p + q - (∑ (i : fin n), (h1 + h2) i * (∏ (s : F) in S i, (X i - C s)))
= (p - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s))))
+ (q - (∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s)))) :=
calc p + q - (∑ (i : fin n), (h1 + h2) i * (∏ (s : F) in S i, (X i - C s)))
     = p + q - (∑ (i : fin n), (h1 i + h2 i) * (∏ (s : F) in S i, (X i - C s))) : by simp
...  = p + q - (∑ (i : fin n),(h1 i * (∏ (s : F) in S i, (X i - C s)) + h2 i * (∏ (s : F) in S i, (X i - C s)))) :
begin
  simp only [sub_right_inj],
  congr,
  ext,
  congr,
  rw add_mul,
end
...  = p + q - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s)) + ∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s))) :
by simp only [sub_right_inj,finset.sum_add_distrib]
...  = (p - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s))))
       + (q - (∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s)))) : 
by rw [← add_sub_assoc, ← sub_sub (p+q), sub_left_inj,sub_add_eq_add_sub]


private lemma h_add_weak { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) : 
∀ (a : fin n →₀ ℕ) (b : F) (f : mv_polynomial (fin n) F), 
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
    have x : (h_f i).total_degree + (S i).card ≤ total_degree f,
    { have y := hh_f.1 i,
      cc },
    exact x.trans (le_max_right (total_degree (single a b)) (total_degree f)),
  },
  by_cases h_f0 : h_f i = 0,
  { right,
    rw h_f0,
    simp only [add_zero],
    have x : (h_Ca i).total_degree + (S i).card ≤ total_degree (single a b),
    { have y := hhC_a.1 i,
      have z : (h_Ca i).total_degree + (S i).card ≤ (monomial a b).total_degree := by cc,
      simpa using z },
    exact x.trans (le_max_left (total_degree (single a b)) (total_degree f)),
  },
  by_cases c : h_Ca i+ h_f i = 0,
  { left,
    exact c },
  right,
  have x := total_degree_add (h_Ca i) (h_f i),
  have y : (h_Ca i).total_degree + (S i).card ≤ total_degree (single a b) :=
    what_is_the_name_for_this_one h_Ca0 (hhC_a.1 i),
  have z : (h_f i).total_degree + (S i).card ≤ total_degree f :=
    what_is_the_name_for_this_one h_f0 (hh_f.1 i),
  have x' := add_le_add_right x (S i).card,
  rw max_add at x',
  exact x'.trans (max_le_le y z),
  intros m hm j,
  have hh_fm := hh_f.2 m,
  have hC_am := hhC_a.2 m,
  clear hh_f hhC_a,
  -- we now use support_add and our hypotheses
  have comp := h_add_weak_aux_comp S (monomial a b) f h_Ca h_f,
  simp at comp,
  have hm' : m ∈ ((monomial a b - (∑ (i : fin n), h_Ca i * (∏ (s : F) in S i, (X i - C s))))
    + (f - (∑ (i : fin n), h_f i * (∏ (s : F) in S i, (X i - C s))))).support,
  { rw ← comp,
    exact hm },
  have t := support_add hm',
  -- can we use rcases or something else here?
  by_cases c : m ∈  (monomial a b - (∑ (i : fin n),
   h_Ca i * (∏ (s : F) in S i, (X i - C s)))).support,
  { exact hC_am c j },
  have c' : m ∈ (f - (∑ (i : fin n), h_f i * (∏ (s : F) in S i, (X i - C s)))).support,
  { rw finset.mem_union at t,
    exact what_is_the_name_for_this_one c t,
  },
  exact hh_fm c' j,
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
  { apply induction_on'' f,
    apply h_C S hS,
    apply h_add_weak S hS,
    apply h_X S hS },
  rw M at h, rw M' at h,
  exact h,
end

end mv_polynomial