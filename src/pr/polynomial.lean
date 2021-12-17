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

-- This is PR #10824
theorem card_le_degree_of_finset_roots {R : Type*} [comm_ring R] [is_domain R] {p : polynomial R} (h : p ≠ 0)
  {Z : finset R } (hZ : ∀ z ∈ Z, is_root p z) : Z.card ≤ p.nat_degree :=
begin
  apply trans _ (polynomial.card_roots' h),
  rw finset.card,
  apply multiset.card_le_of_le (finset.val_le_iff_val_subset.2 _),
  rw multiset.subset_iff,
  intros x hx,
  simpa [polynomial.mem_roots h] using hZ x hx,
end

end polynomial