/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic
import data.finset.basic


local attribute [instance] classical.prop_decidable

namespace polynomial

universes u v

variables {α : Type v}

lemma eq_zero_iff_every_coeff_zero {R : Type u} [comm_semiring R] (p : polynomial R) :
  (∀ (i : ℕ), polynomial.coeff p i = 0) ↔ p = 0 :=
begin
  apply iff.intro,
  intro h,
  ext,
  rw h n,
  simp only [polynomial.coeff_zero],
  intros h i,
  rw h,
  simp,
end

theorem number_zeroes_field {F : Type u} [field F]{p : polynomial F}(h : p ≠ 0)
{Z : finset F } (hZ : ∀ z ∈ Z, polynomial.eval z p = 0) : Z.card ≤ p.nat_degree :=
begin
  apply trans _ (polynomial.card_roots' h),
  rw finset.card,
  have h0 : Z.val ⊆ p.roots,
  { rw multiset.subset_iff,
    intros x hx,
    let z := hZ x hx,
    rwa polynomial.mem_roots h,},
  apply multiset.card_le_of_le (finset.val_le_iff_val_subset.2 h0),
end

end polynomial