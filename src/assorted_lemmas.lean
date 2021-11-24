import data.finset.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.algebra.basic


/-
Sandwich (this is probably on mathlib!)
-/
lemma sandwich {a b : ℕ} (h : a < b) (h' : b ≤ a + 1) : b = a + 1 :=
begin
  sorry
end

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

lemma max_le_le {a b c d: ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) : max a c ≤ max b d := begin
  by_cases h : a ≤ c,
  { rw max_eq_right h,
    exact h₂.trans (le_max_right b d),
  },
  rw not_le at h,
  rw max_eq_left h.le,
  exact h₁.trans (le_max_left b d),
end

lemma max_add {a b c: ℕ} : max a b + c = max (a+c) (b+c) :=
begin
  by_cases h : a ≤ b,
  { rw max_eq_right h,
    have h' : a + c ≤ b + c := by linarith,
    rw max_eq_right h',
  },
  rw not_le at h,
  rw max_eq_left h.le,
  have h' : b + c≤ a + c := by linarith,
  rw max_eq_left h',
end

end

/-

Lemmas for finset

-/

namespace finset

variables {α : Type*} 

lemma mem_of_mem_of_subset {x : α} {s t : finset α} 
(h : x ∈ s) (h' : s ⊆ t) : x ∈ t := sorry

-- how to use α instead of fin n →₀ ℕ here?
theorem mem_or_mem_of_mem_union {n : ℕ} {x : (fin n →₀ ℕ)} {a b : finset (fin n →₀ ℕ)}
 (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := sorry

end finset

/-

Lemmas for mv_polynomial

-/

namespace mv_polynomial
open set function finsupp add_monoid_algebra
open_locale big_operators

variable {R : Type*}
variables {σ : Type*} 

lemma support_sub {R : Type*}{n : ℕ}[comm_ring R]
(p q : mv_polynomial (fin n) R): 
(p - q).support ⊆ p.support ∪ q.support := sorry

lemma support_mul' {R : Type*}[comm_ring R]{n : ℕ}
 {f g : mv_polynomial σ R}{m : σ →₀ ℕ}(m ∈ (f * g).support):
 ∃ m' m'', m' ∈ f.support ∧ m'' ∈ g.support ∧ m = m' + m'' :=
begin
  sorry -- use support_mul
end 

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