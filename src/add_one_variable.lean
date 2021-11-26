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
(f : mv_polynomial (fin (n+1)) R) (i : ℕ) 
{t' : fin n →₀ ℕ }
(h_t' : t' ∈ (polynomial.coeff ((fin_succ_equiv R n) f) i).support) :
(extfin t' i) ∈ f.support :=
begin
  sorry,
end

lemma nat_degree_eval_le_nat_degree {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) :
polynomial.nat_degree (polynomial.map (eval s') f) ≤ polynomial.nat_degree f
:=
begin
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

lemma nat_degree_le_t { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin (n+1)) F)
  (d : ℕ)
  (h : ∀ t' : fin (n+1) →₀ ℕ, t' ∈ f.support → t' n ≤ d) : 
  (fin_succ_equiv F n f).nat_degree < d :=
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
    rw polynomial.mem_roots h,
    exact z },
  have h1 : Z.card ≤ p.roots.card,
  { rw finset.card,
    apply multiset.card_le_of_le,
    exact le_of_val_subset h0,
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
  let t := hz fin.is_empty.elim,
  simpa using t,
  -- I do not know how to prove h00 in a neat way:
  have h00 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
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
    have hnn1 : n < n+1 := by linarith,
    have c' : ↑i = n,
    { have x : ↑i < n+1 := i.2,
      linarith,
    },
    have h : i = fin.mk n hnn1,
    { apply fin.eq_of_veq,
      exact c' },
    rw h,
    simp only [fin.mk_eq_subtype_mk],
    have x:= ext1_eq_n s' y,
    have x1 := coe_eq_mk hnn1,
    rw x1 at x,
    simp only [fin.mk_eq_subtype_mk] at x,
    rw x,
    simp only [fin.mk_eq_subtype_mk] at x1,
    rw ← x1,
    exact hy },
  let d := polynomial.nat_degree ((fin_succ_equiv F n) f),
  have h_f_s'_eq_0 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) → 
    polynomial.map (eval s') ((fin_succ_equiv F n) f) = 0,
  { intros s' hs',
    by_cases c : polynomial.map (eval s') ((fin_succ_equiv F n) f) = 0,
    { exact c },
    exfalso,
    let t1 := number_zeroes_field c (S n) (h00 _ _),
    have uu : (polynomial.map (eval s') ((fin_succ_equiv F n) f)).nat_degree ≤ t n,
    { have x := nat_degree_fin_suc_equiv f,
      have x' := nat_degree_eval_le_nat_degree s' (fin_succ_equiv F n f),
      rw x at x',
      have y := ht n,
      exact x'.trans y },
    let cc1 := lt_of_le_of_lt (t1.trans uu) (hS n),
    simpa using cc1,
    exact hs' },
  have h_f_s'_i_eq_0 :  ∀ i : ℕ,
    ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
     polynomial.coeff (polynomial.map (eval s') ((fin_succ_equiv F n) f)) i = 0,
  { intros i  s' hs',
      let p :=  h_f_s'_eq_0 s' hs',
      let t:= eq_zero_iff_every_coeff_zero (polynomial.map (eval s') ((fin_succ_equiv F n) f)),
      let tev := t.2 p i,
      rw tev },
  have h_f_s'_i_eq_0' :  ∀ i : ℕ, 
    ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
     eval s' (polynomial.coeff ((fin_succ_equiv F n) f) i) = 0,
  { intros i s' hs',
    rw ← coeff_eval_eq_eval_coeff,
    exact  h_f_s'_i_eq_0 i s' hs' },
  have h11 : ∀ i : ℕ, polynomial.coeff ((fin_succ_equiv F n) f) i = 0,
  { intros i,
    --let f_i := polynomial.coeff ((fin_succ_equiv F n) f) i,
    have coso := h_f_s'_i_eq_0' i,
    have x := hn (polynomial.coeff ((fin_succ_equiv F n) f) i) (resfin t) _ _ _ coso, 
    exact x,
    intro j,
    rw ← resfin_eq t j,
    exact (degree_of_coeff_fin_suc_equiv f j i).trans (ht j),
    intro j,
    rw ← resfin_eq t j,
    exact hS ↑j },
  have casi : (fin_succ_equiv F n) f = 0,
  { apply (eq_zero_iff_every_coeff_zero ((fin_succ_equiv F n) f)).1,
    exact h11 },
  exact (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv F n)).1 casi,
end

end mv_polynomial
