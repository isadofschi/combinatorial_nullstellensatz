/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported

namespace mv_polynomial

-- This is #10768 https://github.com/leanprover-community/mathlib/pull/10768

-- this should be near the definition of degree_of. TODO PR this one separately!
lemma degree_of_zero {R : Type*} [comm_semiring R] {σ : Type*} (i : σ) :
  degree_of i (0 : mv_polynomial σ R) = 0 :=
by simp only [degree_of, degrees_zero, multiset.count_zero]

end mv_polynomial