/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/

--  This is PR #10731

import data.mv_polynomial.basic
import data.mv_polynomial.variables
import algebra.algebra.basic
import data.mv_polynomial.comm_ring
import data.nat.basic

universes u v

variables {α : Type v}

open set function finsupp add_monoid_algebra


open_locale big_operators 



namespace mv_polynomial 

variables {R : Type*} {σ : Type*} 


local attribute [instance] classical.prop_decidable

lemma support_sum [comm_semiring R] { α : Type*} {s : finset α} {f : α → mv_polynomial σ R}
  {m : σ →₀ ℕ} (h : m ∈ (∑ x in s, f x).support) : ∃ x ∈ s, m ∈ (f x).support :=
begin
  revert h,
  apply finset.cons_induction_on s,
  intro h,
  exfalso,
  simpa using h,
  clear s,
  intros a s a_notin_s h h',
  rw finset.sum_cons at h',
  cases finset.mem_union.1 (finset.mem_of_subset _ h') with h1 h2,
  use a,
  apply and.intro,
  simp only [finset.mem_insert, finset.cons_eq_insert],
  left,
  refl,
  exact h1,
  cases h h2 with x hx,
  cases hx with hx1 hx2,
  use x,
  apply and.intro,
  simp only [finset.mem_insert, finset.cons_eq_insert],
  right,
  exact hx1,
  exact hx2,
  convert support_add,
end

end mv_polynomial