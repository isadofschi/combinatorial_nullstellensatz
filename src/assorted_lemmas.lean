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
  { rw j_eq_j',
    simp only [single_eq_same],
    rw add_comm,
    have h: s.sum ⇑(single j' a) = 0,
    { let f1 : α → M := (λ x, single j' a x),
      let g1 : α → M := (λ x, 0),
      have h0 : ∀ x ∈ s, f1 x = g1 x,
      { intros x hx,
        simp only [f1, g1],
        have j'_ne_x : j' ≠ x,
        { by_contra c,
          rw c at h',
          cc, },
        simp [j'_ne_x] },
      have t0 := @finset.sum_congr _ _ s s f1 g1 _ (by refl) h0,
      rw t0,
      simp, },
    rw h,
    simp },
  rw h j_in_s,
  have j_ne_j' : j ≠ j',
  { by_contra c,
    rw c at j_in_s,
    cc, },
  simp only [j_ne_j', single_eq_of_ne, ne.def, not_false_iff, zero_add],
end

lemma sum_single' {M : Type*} [semiring M] {n : ℕ}
(j : fin n) (a : M) : 
  ∑ ( x : fin n) , (single j a) x  = a := 
begin
  rw sum_single'',
  simp,
end

variables {σ : Type*} 

-- what should we put here instead of ℕ?
lemma lt_of_le_and_ne {m n: σ →₀ ℕ} (h : m ≤ n) : m ≠ n → m < n :=
begin
  intro h1,
  unfold has_lt.lt preorder.lt,
  apply and.intro,
  unfold has_le.le preorder.le at h,
  exact h,
  by_contra c,
  let h2 : m = n := le_antisymm h (by simpa using c),
  cc,
end

end finsupp
