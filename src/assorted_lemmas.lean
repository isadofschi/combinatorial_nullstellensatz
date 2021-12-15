import data.finset.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.algebra.basic

section ne_symm
universe u
variables {α : Type u} 
lemma not_eq_symm {a b : α } (h: ¬ (a = b)) : ¬ (b = a) := -- or "by cc",
begin
 rw ← ne,
 symmetry,
 rwa ne,
end
end ne_symm

/-

Lemmas for max, linear_order, etc

-/

section open decidable tactic

universe u

variables {α : Type u} [linear_order α]

-- what should we put here instead of ℕ?
lemma max_add {N : Type*} [linear_ordered_add_comm_monoid N] {a b c: N} : 
  max a b + c = max (a+c) (b+c) :=
begin
  by_cases h : a ≤ b,
  { rw [max_eq_right h, max_eq_right _],
    rw [add_comm, add_comm b],
    apply add_le_add_left h },
  { rw not_le at h,
    rw [max_eq_left h.le, max_eq_left _],
    rw [add_comm, add_comm a],
    apply add_le_add_left (le_of_lt  h) },
end

end

namespace finsupp

open set function finsupp add_monoid_algebra
open_locale big_operators

lemma sum_single'' {M : Type*} [semiring M] {α : Type*} {s : finset α} {j : α} (h : j ∈ s)
 (a : M) : ∑ x in s , (single j a) x  = a := 
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
  { have h: s.sum ⇑(single j' a) = 0,
    { let f1 : α → M := (λ x, single j' a x),
      let g1 : α → M := (λ x, 0),
      rw @finset.sum_congr _ _ s s f1 g1 _ (by refl) _,
      simp,
      intros x hx,
      simp only [f1, g1],
      have j'_ne_x : j' ≠ x,
      { by_contra c,
        rw c at h',
        cc, },
      simp [j'_ne_x] },
    simp [j_eq_j', h]},
 { have j_ne_j' : j ≠ j',
   { by_contra c,
     rw c at j_in_s,
     cc, },
  simp [h j_in_s, j_ne_j'] }
end

lemma sum_single' {M σ : Type*} [semiring M] [fintype σ] (j : σ) (a : M) :
  ∑ ( x : σ) , single j a x  = a := by simp [sum_single'']

variables {σ : Type*} 

-- analogue of nat.lt_of_le_and_ne
lemma lt_of_le_and_ne {N : Type*} [linear_order N] [has_zero N] {m n: σ →₀ N} (h : m ≤ n) :
  m ≠ n → m < n :=
begin
  intro h1,
  unfold has_lt.lt preorder.lt,
  apply and.intro,
  unfold has_le.le preorder.le at h,
  exact h,
  by_contra c,
  have h2 : m = n := le_antisymm h (by simpa using c),
  cc,
end

end finsupp
