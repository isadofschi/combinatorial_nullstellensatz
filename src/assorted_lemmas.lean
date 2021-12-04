import data.finset.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.algebra.basic

section ne_symm
universe u
variables {α : Type u} 
lemma ne_symm {a b : α } (h: ¬ (a = b)) : ¬ (b = a) := by cc
end ne_symm

/-

Lemmas for logic

-/

/- ¿ is this already in logic.basic or somewhere else in mathlib ? -/
lemma right_of_not_of_or {p q : Prop}(h1 : ¬ p) (h2 : p ∨ q) : q := 
(or_iff_not_imp_left.1 h2) h1

/-

Lemmas for max, linear_order, etc

-/

section open decidable tactic

universe u

variables {α : Type u} [linear_order α]

lemma max_add {a b c: ℕ} : max a b + c = max (a+c) (b+c) :=
begin
  by_cases h : a ≤ b,
  { rw max_eq_right h,
    have h' : a + c ≤ b + c := by linarith,
    rw max_eq_right h',
  },
  rw not_le at h,
  rw max_eq_left h.le,
  have h' : b + c ≤ a + c := by linarith,
  rw max_eq_left h',
end

end


namespace finsupp

open set function finsupp add_monoid_algebra
open_locale big_operators


lemma sum_single'' {M : Type*} [has_zero M] [add_comm_monoid M] {α : Type*} {s : finset α}
{j : α} (h : j ∈ s) (a : M) : 
  ∑ x in s , (single j a) x  = a := 
begin
  revert h,
  apply finset.cons_induction_on s,
  intro h,
  exfalso,
  simpa using h,
  clear s,
  intros j' s h' h h'',
  rw finset.sum_cons,
  rw finset.mem_cons at h'',
  cases h'' with j_eq_j' j_in_s,
  { rw j_eq_j',
    simp only [single_eq_same],
    rw add_comm,
    have h: s.sum ⇑(single j' a) = 0,
    { have h0 : ∀ x ∈ s, single j' a x = 0,
      { intros x hx,
        have j'_ne_x : j' ≠ x,
        { by_contra c,
          rw c at h',
          cc, },
        simp [j'_ne_x],
      },
      -- use h0
      sorry },
    rw h,
    sorry }, -- ?? 
  rw h j_in_s,
  have j_ne_j' : j ≠ j',
  { by_contra c,
    rw c at j_in_s,
    cc, },
  simp only [j_ne_j', single_eq_of_ne, ne.def, not_false_iff, zero_add],
  sorry, -- ??
end

-- what should we put here instead of ℕ?
lemma sum_single' {M : Type*} [has_zero M] [add_comm_monoid M] {n : ℕ}
(j : fin n) (a : M) : 
  ∑ ( x : fin n) , (single j a) x  = a := 
begin
  rw sum_single'',
  simp,
end

variables {σ : Type*} 

-- what should we put here instead of ℕ?
lemma lt_of_le_and_ne {m n: σ →₀ ℕ} (h1 : m ≤ n) : m ≠ n → m < n :=
begin
  intro h,
  -- rw using definition of lt
  -- use nat.lt_of_le_and_ne,
  sorry,
end

end finsupp

/-

Lemmas for mv_polynomial: support, coeff, induction

-/

namespace mv_polynomial
open set function finsupp add_monoid_algebra
open_locale big_operators

variables {R : Type*} {σ : Type*} 

universe u

lemma support_sum [comm_semiring R]{ α : Type}{s : finset α}
  {f : α → mv_polynomial σ R} {m : σ →₀ ℕ} (h : m ∈ (∑ x in s, f x).support) :
  ∃ x ∈ s, m ∈ (f x).support
:= sorry

lemma mem_support_iff_nonzero_coeff [comm_semiring R] -- do we really need this? Do we already have this?
(p : mv_polynomial σ R) (m : σ →₀ ℕ): 
m ∈ p.support ↔ coeff m p ≠ 0 := by simp

lemma support_sub {R : Type*}{n : ℕ}[comm_ring R]
(p q : mv_polynomial (fin n) R): 
(p - q).support ⊆ p.support ∪ q.support := sorry

-- Compare with https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L1129
lemma support_mul' {R : Type*}[comm_ring R]
 {f g : mv_polynomial σ R}{m : σ →₀ ℕ}(m ∈ (f * g).support):
 ∃ m' m'', m' ∈ f.support ∧ m'' ∈ g.support ∧ m = m' + m'' :=
begin
  sorry -- use support_mul
end 

-- compare the following with https://github.com/leanprover-community/mathlib/pull/10429/fileshttps://github.com/leanprover-community/mathlib/pull/10429/files
lemma coeff_monomial_mul [comm_semiring R] (m m' :  σ →₀ ℕ) (h : m' ≤ m) (f : mv_polynomial σ R) (a : R): 
  coeff m ((monomial m' a) * f) = a * coeff (m-m') f := 
begin
  sorry
end

lemma coeff_monomial_mul' [comm_semiring R] (m m' :  σ →₀ ℕ) (h : ¬ m' ≤ m) (f : mv_polynomial σ R) (a : R): 
  coeff m ((monomial m' a) * f) = 0 := 
begin
  sorry
end

-- PR to  data/mv_polynomial/basic.lean
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
have ∀s a, M (monomial s a) := induction_on_monomial h_C h_X,
finsupp.induction p
  (by have : M (C 0) := h_C 0; rwa [C_0] at this)
    h_add_weak

end mv_polynomial