/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic
import data.finset.basic

namespace polynomial

lemma eq_zero_iff_every_coeff_zero {R : Type*} [comm_semiring R] (p : polynomial R) :
  (∀ (i : ℕ), polynomial.coeff p i = 0) ↔ p = 0 :=
begin
  apply iff.intro,
  intro h,
  ext i,
  simp only [h i, polynomial.coeff_zero],
  intros h i,
  simp [h],
end

theorem number_zeroes_field {R : Type*} [comm_ring R] [is_domain R] {p : polynomial R} (h : p ≠ 0)
  {Z : finset R } (hZ : ∀ z ∈ Z, polynomial.eval z p = 0) : Z.card ≤ p.nat_degree :=
begin
  apply trans _ (polynomial.card_roots' h),
  rw finset.card,
  apply multiset.card_le_of_le (finset.val_le_iff_val_subset.2 _),
  rw multiset.subset_iff,
  intros x hx,
  simpa [polynomial.mem_roots h] using hZ x hx,
end

end polynomial