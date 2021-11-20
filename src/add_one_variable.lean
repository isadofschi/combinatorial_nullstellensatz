import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported
import data.polynomial.basic
import data.polynomial.ring_division

import algebra.field

universes u v

variables {α : Type v}

open_locale big_operators

namespace mv_polynomial


-- We surely already have this somewhere in mathlib!
private def resfin {n: ℕ } (s : fin (n+1) →₀ ℕ ) : fin n →₀ ℕ := sorry

private def extfin {n:ℕ}(s' : fin n →₀  ℕ) (y : ℕ) : fin (n+1) →₀ ℕ := sorry

lemma resfin_eq {n :ℕ} (s : fin (n+1) →₀ ℕ): ∀ (i : fin n), s i = resfin s i :=
begin
  intro i,
  sorry,
end

--private def refin_eq_le_n {n:ℕ}{R: Type*}{i : fin n}(s : fin (n+1) → R) : 
--resfin s i = s ↑i := sorry 

private def res {n: ℕ }{R : Type*} (s : fin (n+1) → R) : fin n → R := λ i , s i

lemma res_eq {n :ℕ} {R :Type*}(s : fin (n+1) → R): ∀ (i : fin n), s i = res s i :=
begin
  intro i,
  refl,
end

private def ext1 {n:ℕ}{R: Type*}(s' : fin n → R)(y : R) : fin (n+1) → R := 
λ i, if h : ↑i < n then s' (fin.mk i h) else y

private def ext1_eq_n {n:ℕ}{R: Type*}(s' : fin n → R)(y : R) : 
ext1 s' y n = y := sorry 

private def ext1_eq_le_n {n:ℕ}{R: Type*}{i : fin(n+1)}(s' : fin n → R)(y : R)(h : ↑i < n) : 
ext1 s' y i = s' (fin.mk i h) := sorry 

/- Evaluating all the Xi at si is the same as evaluating X(n+1) at s(n+1) and 
  later evaluating X1 ... Xn at s1 ... sn -/
lemma eval_eq_mv_eval_eval {n : ℕ} {R : Type u} [comm_ring R]
(s : fin (n+1) → R)
 : ∀ f : mv_polynomial (fin (n+1)) R, 
 eval s f = eval (res s) (polynomial.eval (C( s (n+1))) ((fin_succ_equiv R n) f)) :=
begin
  sorry
end

/- Evaluating all the Xi at si is the same as evaluating X1 ... Xn at s1 ... sn and
   later evaluating X(n+1) at s(n+1) -/
lemma eval_eq_eval_mv_eval {n : ℕ} {R : Type u} [comm_ring R]
(s : fin (n+1) → R) : ∀ f : mv_polynomial (fin (n+1)) R, 
 eval s f = polynomial.eval (s (n+1)) (polynomial.map (eval (res s)) ((fin_succ_equiv R n) f)) :=
begin
  sorry,
end

lemma eval_eq_eval_mv_eval' {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (y : R): ∀ f : mv_polynomial (fin (n+1)) R, 
 eval (ext1 s' y) f = polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv R n) f)) :=
begin
  sorry,
end

lemma coeff_eval_eq_eval_coeff {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ):
polynomial.coeff (polynomial.map (eval s') f) i =  eval s' (polynomial.coeff f i) 
:=
begin
  simp only [polynomial.coeff_map],
end


lemma support_f_i {n : ℕ} {R : Type u} [comm_ring R]
(f : mv_polynomial (fin (n+1)) R) (i : ℕ) (t' : (polynomial.coeff ((fin_succ_equiv R n) f) i).support) :
(extfin ↑t' i) ∈ f.support :=
begin
  sorry,
end

lemma nat_degree_eval_eq_nat_degree {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ):
polynomial.nat_degree (polynomial.map (eval s') f) =  polynomial.nat_degree f
:=
begin
  sorry,
end

lemma nat_degree_le_t { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin (n+1)) F)
  (d : ℕ)
  (h : ∀ t' : f.support,  t' n ≤ d) : 
  (fin_succ_equiv F n f).nat_degree < d :=
begin
  sorry
end

lemma eq_zero_iff_every_coeff_zero {R : Type u} [comm_ring R](p : polynomial R)
: (∀ i:ℕ, i ≤ polynomial.nat_degree p → polynomial.coeff p i = 0) ↔ p = 0 :=
begin
  sorry,
end

theorem number_zeroes_field {F : Type u} [field F]{p : polynomial F}(h : p ≠ 0)
(Z : finset F ) (hZ : ∀ z ∈ Z, polynomial.eval z p = 0) : Z.card ≤ p.nat_degree :=
begin
  let t := polynomial.card_roots' h,
  have h1 : Z.card ≤ p.roots.card,
  {
     sorry,
  },
  exact h1.trans t,
end

/- Lemma 2.1 in Alon's paper. -/
lemma lemma_2_1 { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin n) F)
  (t : fin n →₀ ℕ)
  (ht : ∀ i : fin n, ∀ t' : f.support,  t' i ≤ t i)
  (S : fin n → finset F)
  (hS : ∀ i : fin n, t i < (S i).card) 
  (hz : ∀ s : fin n → F, (∀ i : fin n, s i ∈ S i ) → eval s f = 0) :
  f = 0 :=
begin
  induction n with n hn,
  simp only [forall_const] at hz,
  apply (ring_equiv.map_eq_zero_iff (is_empty_ring_equiv F (fin 0))).1,
  simp only [is_empty_ring_equiv_apply],
  let t := hz fin.is_empty.elim,
  simpa using t,
  have h00 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
    ∀ y : F, y ∈ S n →  
    polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv F n) f)) = 0,
  {
    intros s' hs' y hy,
    rw ← eval_eq_eval_mv_eval',
    rw hz,
    intro i,
    sorry }, --should be easy: by_cases c : i < n, etc
  let d := polynomial.nat_degree ((fin_succ_equiv F n) f),
  have h_f_s'_eq_0 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) → 
    polynomial.map (eval s') ((fin_succ_equiv F n) f) = 0,
  { intros s' hs',
    by_cases c : polynomial.map (eval s') ((fin_succ_equiv F n) f) = 0,
    { exact c },
    exfalso,
    let t1 := number_zeroes_field c (S n) (h00 _ _),
    have uu : (polynomial.map (eval s') ((fin_succ_equiv F n) f)).nat_degree < t n,
    { have x := nat_degree_le_t f (t n) (ht n),
      rw ← nat_degree_eval_eq_nat_degree at x,
      exact x,
      exact n },
    let cc1 := (lt_of_le_of_lt t1 uu).trans (hS n),
    simpa using cc1,
    exact hs' },
  have h_f_s'_i_eq_0 :  ∀ i : ℕ, i ≤ d →  
    ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
     polynomial.coeff (polynomial.map (eval s') ((fin_succ_equiv F n) f)) i = 0,
  { intros i i_le_d s' hs',
      let p :=  h_f_s'_eq_0 s' hs',
      let t:= eq_zero_iff_every_coeff_zero (polynomial.map (eval s') ((fin_succ_equiv F n) f)),
      let tev := t.2 p i,
      rw tev,
      clear tev t p,
      rw nat_degree_eval_eq_nat_degree s' ((fin_succ_equiv F n) f),
      exact i_le_d,
      exact n },
  have h_f_s'_i_eq_0' :  ∀ i : ℕ, i ≤ d →  
    ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
     eval s' (polynomial.coeff ((fin_succ_equiv F n) f) i) = 0,
  { intros i i_le_d s' hs',
    rw ← coeff_eval_eq_eval_coeff,
    exact  h_f_s'_i_eq_0 i i_le_d s' hs' },
  
  have h11 : ∀ i : ℕ, i ≤ d → polynomial.coeff ((fin_succ_equiv F n) f) i = 0,
  { intros i i_le_d,
    --let f_i := polynomial.coeff ((fin_succ_equiv F n) f) i,
    have coso := h_f_s'_i_eq_0' i i_le_d,
    have hnf_i := hn (polynomial.coeff ((fin_succ_equiv F n) f) i) (resfin t) _ _ _ coso, 
    exact hnf_i,
    intros j t',
    rw ← resfin_eq t j,
    have ht' : t' j ≤ t ↑j, 
    { have x := support_f_i f i t',
      --exact ht j t1, 
      -- use ht somehow
     sorry },
    exact ht',
    intro j,
    rw ← resfin_eq t j,
    exact hS ↑j,
  },
  have casi : (fin_succ_equiv F n) f = 0,
  { apply (eq_zero_iff_every_coeff_zero ((fin_succ_equiv F n) f)).1,
    exact h11 },
  exact (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv F n)).1 casi,
end

end mv_polynomial