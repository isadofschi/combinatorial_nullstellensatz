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
private def extfin {n:ℕ}(s' : fin n →₀  ℕ) (y : ℕ) : fin (n+1) →₀ ℕ := sorry
--(fin.snoc s' y, sorry)


/- Evaluating all the Xi at si is the same as evaluating X(n+1) at s(n+1) and 
  later evaluating X1 ... Xn at s1 ... sn -/
/- We are not using this one but it might be nice to have this in mathlib -/
lemma eval_eq_mv_eval_eval {n : ℕ} {R : Type u} [comm_ring R]
(s : fin (n+1) → R)
 : ∀ f : mv_polynomial (fin (n+1)) R, 
 eval s f = eval (fin.init s) (polynomial.eval (C( s (n+1))) ((fin_succ_equiv R n) f)) :=
begin
  sorry
end


lemma support_f_i {n : ℕ} {R : Type u} [comm_ring R]
(f : mv_polynomial (fin (n+1)) R) (i : ℕ) 
{t' : fin n →₀ ℕ }
(h_t' : t' ∈ (polynomial.coeff ((fin_succ_equiv R n) f) i).support) :
(extfin t' i) ∈ f.support :=
begin
  sorry,
end

/- Evaluating all the Xi at si is the same as evaluating X1 ... Xn at s1 ... sn and
   later evaluating X(n+1) at s(n+1) -/
/- We are not using this one but it might be nice to have this in mathlib -/
lemma eval_eq_eval_mv_eval {n : ℕ} {R : Type u} [comm_ring R]
(s : fin (n+1) → R) : ∀ f : mv_polynomial (fin (n+1)) R, 
 eval s f = polynomial.eval (s (n+1)) (polynomial.map (eval (fin.init s)) ((fin_succ_equiv R n) f)) :=
begin
  sorry,
end


lemma eq_zero_iff_every_coeff_zero_strong {R : Type u} [comm_ring R](p : polynomial R)
: (∀ i:ℕ, i ≤ polynomial.nat_degree p → polynomial.coeff p i = 0) ↔ p = 0 :=
begin
  apply iff.intro,
  intro h,
  ext,
  rw h n,
  simp,
  sorry,
  intros h i h',
  rw h,
  simp,
end

lemma cannot_find_this {n m: ℕ } (h : n < m): n = ↑(fin.mk n h) :=
begin
  simp only [fin.mk_eq_subtype_mk, fin.coe_of_nat_eq_mod, fin.coe_mk],
end

lemma nat_degree_le_t { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin (n+1)) F)
  (d : ℕ)
  (h : ∀ t' : fin (n+1) →₀ ℕ, t' ∈ f.support → t' n ≤ d) : 
  (fin_succ_equiv F n f).nat_degree < d :=
begin
  sorry
end


end mv_polynomial