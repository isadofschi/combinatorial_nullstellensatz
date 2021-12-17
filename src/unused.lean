import algebra.algebra.basic

section open decidable tactic

universe u

variables {α : Type u} [linear_order α]

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

-- This is PR #10822 (closed)
/-
lemma eq_zero_iff_every_coeff_zero {R : Type*} [comm_semiring R] (p : polynomial R) :
  (∀ (i : ℕ), polynomial.coeff p i = 0) ↔ p = 0 := by simp only [ext_iff, coeff_zero]
-/