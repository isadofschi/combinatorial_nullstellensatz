import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic

import assorted_lemmas 
-- only le_of_val_subset, mod_succ_self_eq_self

universes u v

variables {α : Type v}

open_locale big_operators

namespace mv_polynomial


-- Restriction and extension between fin n and fin (n+1)

local attribute [instance] classical.prop_decidable --esta permitido usar esto?

private def res {n: ℕ }{R : Type*} (s : fin (n+1) → R) : fin n → R := λ i , s i

private lemma res_eq {n :ℕ} {R :Type*}(s : fin (n+1) → R): ∀ (i : fin n), s i = res s i :=
begin
  intro i,
  refl,
end

private noncomputable def ext1 {n:ℕ}{R: Type*}(s' : fin n → R)(y : R) : fin (n+1) → R := 
λ i, if h : ↑i < n then s' (fin.mk i h) else y

private def ext1_eq_n {n:ℕ}{R: Type*}(s' : fin n → R)(y : R) : 
ext1 s' y n = y := begin
  rw ext1,
  have h : ¬ (n % n.succ < n),
  { rw mod_succ_self_eq_self n,
    linarith },
  simp only [fin.coe_of_nat_eq_mod, fin.mk_eq_subtype_mk, h, fin.coe_of_nat_eq_mod, dif_neg, not_false_iff],
end

private def ext1_eq_le_n {n:ℕ}{R: Type*}{i : fin(n+1)}(s' : fin n → R)(y : R)(h : ↑i < n) : 
ext1 s' y i = s' (fin.mk i h) :=
begin
  rw ext1,
  simp only [h, dif_pos],
end

private def resfin {n: ℕ } (s : fin (n+1) →₀ ℕ ) : fin n →₀ ℕ 
:= sorry -- algo así? finsupp.mk (finset.fin_range n ) (res s)  (by sorry)

private def extfin {n:ℕ}(s' : fin n →₀  ℕ) (y : ℕ) : fin (n+1) →₀ ℕ := sorry

private lemma resfin_eq {n :ℕ} (s : fin (n+1) →₀ ℕ): ∀ (i : fin n), s i = resfin s i :=
begin
  intro i,
  sorry,
end

private def extfin_eq_le_n {n:ℕ}{i : fin n}
(s' : fin n →₀  ℕ)(y : ℕ)(h : ↑i < n) : 
extfin s' y i = s' (fin.mk i h) := sorry 

/-

Lemmas

-/

lemma eval_eq_eval_mv_eval' {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (y : R): ∀ f : mv_polynomial (fin (n+1)) R, 
 eval (ext1 s' y) f = polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv R n) f)) :=
begin
  sorry,
end

lemma coeff_eval_eq_eval_coeff {n : ℕ} {R : Type u} [comm_semiring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ):
polynomial.coeff (polynomial.map (eval s') f) i =  eval s' (polynomial.coeff f i) 
:=
begin
  simp only [polynomial.coeff_map],
end

lemma support_eval' {n : ℕ} {R : Type u} [comm_semiring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ):
i ∈ (polynomial.map (eval s') f).support → i ∈ f.support :=
begin
  intro hi,
  simp only [polynomial.mem_support_iff, polynomial.coeff_map, ne.def] at hi,
  by_contradiction,
  simp only [polynomial.mem_support_iff, not_not, ne.def] at h,
  rw h at hi,
  simpa using hi,
end


lemma support_eval {n : ℕ} {R : Type u} [comm_semiring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)):
(polynomial.map (eval s') f).support ⊆ f.support :=
begin
rw finset.subset_iff,
intros x hx,
exact support_eval' s' f x hx,
end

lemma degree_eval_le_degree {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) :
polynomial.degree (polynomial.map (eval s') f) ≤ polynomial.degree f
:=
begin
  rw polynomial.degree,
  rw polynomial.degree,
  rw finset.sup_le_iff,
  intro b,
  intro hb,
  apply finset.le_sup (support_eval' s' f b hb),
end


lemma nat_degree_eval_le_nat_degree {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) :
polynomial.nat_degree (polynomial.map (eval s') f) ≤ polynomial.nat_degree f
:=
begin
  rw polynomial.nat_degree,
  rw polynomial.nat_degree,
  sorry,
end

lemma nat_degree_fin_suc_equiv {n : ℕ} {F : Type u} [field F]
  (f : mv_polynomial (fin (n+1)) F) : 
  (fin_succ_equiv F n f).nat_degree = degree_of ↑n f :=
begin
  sorry
end

lemma degree_of_coeff_fin_suc_equiv {n : ℕ} {F : Type u} [field F]
  (f : mv_polynomial (fin (n+1)) F) (j:fin n)(i:ℕ) : 
  degree_of j (polynomial.coeff (fin_succ_equiv F n f) i) ≤ degree_of ↑j f :=
begin
  sorry
end

lemma eq_zero_iff_every_coeff_zero {R : Type u} [comm_ring R](p : polynomial R)
: (∀ i:ℕ, polynomial.coeff p i = 0) ↔ p = 0 :=
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
(Z : finset F ) (hZ : ∀ z ∈ Z, polynomial.eval z p = 0) : Z.card ≤ p.nat_degree :=
begin
  have h0 : Z.val ⊆ p.roots,
  { rw multiset.subset_iff,
    intros x hx,
    let z := hZ x hx,
    rwa polynomial.mem_roots h },
  have h1 : Z.card ≤ p.roots.card,
  { rw finset.card,
    exact multiset.card_le_of_le (le_of_val_subset h0),
  },
  exact h1.trans (polynomial.card_roots' h),
end

/- Lemma 2.1 in Alon's paper. -/
lemma lemma_2_1 { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin n) F)
  (t : fin n →₀ ℕ)
  (ht : ∀ i : fin n, degree_of i f ≤ t i)
  (S : fin n → finset F)
  (hS : ∀ i : fin n, t i < (S i).card) 
  (hz : ∀ s : fin n → F, (∀ i : fin n, s i ∈ S i ) → eval s f = 0) :
  f = 0 :=
begin
  induction n with n hn,
  simp only [forall_const] at hz,
  apply (ring_equiv.map_eq_zero_iff (is_empty_ring_equiv F (fin 0))).1,
  simp only [is_empty_ring_equiv_apply],
  --let t := ,
  simpa using (hz fin.is_empty.elim),
  apply (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv F n)).1,
  apply (eq_zero_iff_every_coeff_zero ((fin_succ_equiv F n) f)).1,
  intro i,
  apply hn (polynomial.coeff ((fin_succ_equiv F n) f) i) (resfin t),
  intro j,
  --let f_i := polynomial.coeff ((fin_succ_equiv F n) f) i,
  rw ← resfin_eq t j,
  exact (degree_of_coeff_fin_suc_equiv f j i).trans (ht j),
  intro j,
  rw ← resfin_eq t j,
  exact hS ↑j,
  intros s hs,
  rw ← coeff_eval_eq_eval_coeff,
  rw (eq_zero_iff_every_coeff_zero (polynomial.map (eval s) ((fin_succ_equiv F n) f))).2,
  -- I do not know how to prove h00 in a neat way:
  have h0 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
    ∀ y : F, y ∈ S n →  
    polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv F n) f)) = 0,
  {
    intros s' hs' y hy,
    rw ← eval_eq_eval_mv_eval',
    rw hz,
    intro i,
    by_cases c : ↑i < n,
    { rw (ext1_eq_le_n s' y c), 
      have x:= hs' (fin.mk i c),
      simp only [fin.coe_eq_cast_succ, fin.mk_eq_subtype_mk, fin.cast_succ_mk, fin.eta] at x,
      simp only [fin.mk_eq_subtype_mk],
      exact x,
    },
    have r : ↑n = i,
    { apply fin.eq_of_veq,
      simp,
      rw ← (sandwich' (le_of_not_lt c) i.property),
      rw mod_succ_self_eq_self },
    rwa [ ← r, ext1_eq_n s' y ] },
  by_contradiction c,
  let t1 := number_zeroes_field c (S n) (h0 _ _),
  have u : (polynomial.map (eval s) ((fin_succ_equiv F n) f)).nat_degree ≤ t n,
  { have x := nat_degree_eval_le_nat_degree s (fin_succ_equiv F n f),
    rw nat_degree_fin_suc_equiv f at x,
    have y := ht n,
    exact x.trans y },
  simpa using lt_of_le_of_lt (t1.trans u) (hS n),
  exact hs,
end

end mv_polynomial
