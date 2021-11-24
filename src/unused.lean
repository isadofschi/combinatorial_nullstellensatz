import data.finset.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported
import algebra.algebra.basic
import data.polynomial.basic
import data.polynomial.ring_division

namespace mv_polynomial

open set function finsupp add_monoid_algebra
open_locale big_operators

universe u

variable {R : Type*}
variables {σ : Type*} 


lemma support_sum {n : ℕ} [comm_semiring R]
  (f : (fin n) → mv_polynomial σ R) (m : σ →₀ ℕ): 
  m ∈ (∑ x : (fin n), f x).support → ∃ x : (fin n), m ∈ (f x).support
:= sorry

/- esta def se usa -/
private def res {n: ℕ }{R : Type*} (s : fin (n+1) → R) : fin n → R := λ i , s i


/- Evaluating all the Xi at si is the same as evaluating X(n+1) at s(n+1) and 
  later evaluating X1 ... Xn at s1 ... sn -/
/- We are not using this one but it might be nice to have this in mathlib -/
lemma eval_eq_mv_eval_eval {n : ℕ} {R : Type u} [comm_ring R]
(s : fin (n+1) → R)
 : ∀ f : mv_polynomial (fin (n+1)) R, 
 eval s f = eval (res s) (polynomial.eval (C( s (n+1))) ((fin_succ_equiv R n) f)) :=
begin
  sorry
end

/- Evaluating all the Xi at si is the same as evaluating X1 ... Xn at s1 ... sn and
   later evaluating X(n+1) at s(n+1) -/
/- We are not using this one but it might be nice to have this in mathlib -/
lemma eval_eq_eval_mv_eval {n : ℕ} {R : Type u} [comm_ring R]
(s : fin (n+1) → R) : ∀ f : mv_polynomial (fin (n+1)) R, 
 eval s f = polynomial.eval (s (n+1)) (polynomial.map (eval (res s)) ((fin_succ_equiv R n) f)) :=
begin
  sorry,
end

end mv_polynomial