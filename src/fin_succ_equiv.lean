/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic


universes u v

variables {α : Type v}

open_locale big_operators

namespace mv_polynomial


/-

  cons and tail for maps fin n → R and fin n →₀ M

-/ 

local attribute [instance] classical.prop_decidable

private noncomputable def fin.support
{M : Type*} [has_zero M] {n : ℕ} (f : fin n → M) : finset (fin n) :=
(finset.fin_range n).filter (λ i, f i ≠ 0)

private lemma fin.mem_support_to_fun 
{M : Type*} [has_zero M] {n : ℕ} (f : fin n → M)
: ∀ a, a ∈ fin.support f ↔ f a ≠ 0 := begin
intro a,
rw fin.support,
simp,
end

private noncomputable def fin.to_finsupp
{M : Type*} [has_zero M] {n:ℕ } (f : fin n → M ) : fin n →₀ M :=
⟨ fin.support f , f, fin.mem_support_to_fun f ⟩

private noncomputable def fin.finsupp.tail {n: ℕ } (s : fin (n+1) →₀ ℕ ) : fin n →₀ ℕ 
:= fin.to_finsupp (fin.tail s.to_fun)

private noncomputable def fin.finsupp.cons {n:ℕ} (y : ℕ) (s : fin n →₀  ℕ) : fin (n+1) →₀ ℕ := 
fin.to_finsupp (fin.cons y s.to_fun)

private lemma fin.finsupp.tail_eq {n :ℕ} (s : fin (n+1) →₀ ℕ) : 
∀ (i : fin n), s i.succ = fin.finsupp.tail s i :=
begin
  intro i,
  rw [fin.finsupp.tail, fin.tail],
  congr,
end

private lemma fin.finsupp.cons_zero {n:ℕ}
(y : ℕ) (s : fin n →₀  ℕ) : 
fin.finsupp.cons y s 0 = y := 
begin 
  rw [fin.finsupp.cons, fin.cons, fin.to_finsupp],
  simp,
end

private lemma fin.finsupp.cons_succ {n:ℕ} (i : fin n)
(y : ℕ) (s : fin n →₀  ℕ) : 
fin.finsupp.cons y s i.succ = s i := 
begin 
  rw [fin.finsupp.cons, fin.cons, fin.to_finsupp],
  simp only [fin.cases_succ, finsupp.coe_mk],
  rw [coe_fn, finsupp.has_coe_to_fun],
end


private lemma fin.finsupp.tail_cons {n:ℕ} (y : ℕ) (s : fin n →₀  ℕ) :
  fin.finsupp.tail (fin.finsupp.cons y s) = s :=
begin
  simp only [fin.finsupp.cons, fin.cons, fin.finsupp.tail, fin.tail],
  ext,
  simp only [fin.to_finsupp, finsupp.coe_mk,fin.cases_succ],
  rw [coe_fn, finsupp.has_coe_to_fun],
end

private lemma fin.finsupp.cons_tail {n:ℕ} (y : ℕ) (s : fin (n+1) →₀  ℕ) :
  fin.finsupp.cons (s 0) (fin.finsupp.tail s) = s :=
begin
  ext,
  by_cases c_a : a = 0,
  { rw c_a,
    rw fin.finsupp.cons_zero },
  let a' := fin.pred a c_a,
  have h : a = a'.succ := by simp,
  rw h,
  rw fin.finsupp.cons_succ,
  rw fin.finsupp.tail_eq,
end

private lemma fin.finsupp.cons_zero_zero {n : ℕ}:
  fin.finsupp.cons 0 (0: fin n →₀  ℕ ) = 0 :=
begin
  ext,
  by_cases c : a ≠ 0,
  { let a' := fin.pred a c,
    have r : a = a'.succ := by simp,
    rw r,
    rw fin.finsupp.cons_succ,
    simp },
  simp only [not_not] at c,
  rw c,
  simp,
  rw fin.finsupp.cons_zero 0 0,
end

private lemma fin.finsupp.cons_nonzero_any  {n : ℕ}{y : ℕ} {m: fin n →₀  ℕ } (h : y ≠ 0):
  fin.finsupp.cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h1 : fin.finsupp.cons y m 0 = 0,
  { rw c,
    refl },
  rw fin.finsupp.cons_zero at h1,
  cc,
end

private lemma fin.finsupp.cons_any_nonzero {n : ℕ}{y : ℕ} {m: fin n →₀  ℕ } (h : m ≠ 0):
  fin.finsupp.cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h' : m = 0,
  { ext,
    rw [ ← fin.finsupp.cons_succ a y m, c],
    simp },
  cc,
end



-- this should be near the definition of degree_of
lemma degree_of_zero {R : Type*}[comm_semiring R]{σ : Type*}(i : σ) :
degree_of i (0 : mv_polynomial σ R) = 0 :=
begin
  rw degree_of,
  simp,
end


lemma fin_succ_equiv_add {n : ℕ} {R : Type u} [comm_semiring R] 
(f g : mv_polynomial (fin (n+1)) R) :
  fin_succ_equiv R n (f + g) = fin_succ_equiv R n f + fin_succ_equiv R n g :=
begin
  simp
end

lemma fin_succ_equiv_mul {n : ℕ} {R : Type u} [comm_semiring R] 
(f g : mv_polynomial (fin (n+1)) R) :
  fin_succ_equiv R n (f * g) = fin_succ_equiv R n f * fin_succ_equiv R n g :=
begin
  simp
end

lemma fin_succ_equiv_zero {n : ℕ} {R : Type u} [comm_semiring R] :
  fin_succ_equiv R n 0 = 0 :=
begin
  simp,
end


lemma fin_succ_equiv_eq_zero {n : ℕ} {R : Type u} [comm_semiring R] :
  fin_succ_equiv R n (X 0) = polynomial.X :=
begin
  simp,  
end

lemma fin_succ_equiv_ne_zero {n : ℕ} {R : Type u} [comm_semiring R] {j : fin n} :
  fin_succ_equiv R n (X j.succ) = polynomial.C (X j) :=
begin
  simp,
end

lemma fin_succ_equiv_coeff_coeff {n : ℕ} {R : Type u} [comm_semiring R]
  (m : fin n →₀  ℕ) (f : mv_polynomial (fin (n+1)) R ) (i : ℕ) :
  coeff m (polynomial.coeff (fin_succ_equiv R n f) i) = coeff (fin.finsupp.cons i m) f :=
begin
  revert i m,
  apply induction_on f,
  intros a i m,
  by_cases c_i : i = 0,
  { rw c_i,
    simp only [fin_succ_equiv_apply, polynomial.coeff_C_zero, coeff_C, ring_hom.coe_comp, eval₂_hom_C],
    by_cases c_m : 0 = m,
    { rw ← c_m,
      simp only [if_true, eq_self_iff_true],
      rw fin.finsupp.cons_zero_zero,
      simp },
    simp only [c_m, if_false],
    have x : ¬ fin.finsupp.cons 0 m = 0,
    { apply fin.finsupp.cons_any_nonzero,
      symmetry,
      simpa using c_m },
    have x' : ¬ 0 = fin.finsupp.cons 0 m := by cc,
    simp only [x', if_false ] },
  simp only [fin_succ_equiv_apply, coeff_C, function.comp_app, ring_hom.coe_comp, eval₂_hom_C],
  rw polynomial.coeff_C,
  simp only [c_i, if_false],
  rw coeff_zero,
  have x : ¬ fin.finsupp.cons i m = 0,
  { apply fin.finsupp.cons_nonzero_any,
    simpa using c_i },
  have x' :  ¬ 0 = fin.finsupp.cons i m := by cc,
  simp only [x', if_false ],
  intros p q hp hq i m,
  rw fin_succ_equiv_add,
  rw polynomial.coeff_add,
  repeat { rw coeff_add },
  rw [hp, hq],
  intros p j hp i m,
  rw coeff_mul_X' (fin.finsupp.cons i m) j p,
  rw [ fin_succ_equiv_mul ],
  by_cases c_j : j = 0,
  { rw c_j,
    by_cases c_i : i = 0,
    { rw c_i,
      simp only [fin_succ_equiv_apply, fin.cases_zero, polynomial.coeff_X_zero, coe_eval₂_hom, polynomial.mul_coeff_zero,
  finsupp.mem_support_iff, ne.def, eval₂_hom_X', mul_zero, coeff_zero],
      have t : ¬¬(fin.finsupp.cons 0 m) 0 = 0,
      { simp only [not_not],
        rw fin.finsupp.cons_zero },
      simp only [t, if_false] },
    rw fin_succ_equiv_eq_zero,
    let i' := nat.pred i,
    have r : i = i'.succ,
    { rw nat.succ_pred_eq_of_pos _,
      apply nat.pos_of_ne_zero,
      simpa },
    rw r,
    rw polynomial.coeff_mul_X,
    rw hp i',
    simp only [finsupp.mem_support_iff, ne.def],
    simp only [fin.finsupp.cons_zero],
    rw ← r,
    simp only [c_i, if_true, not_false_iff],
    congr,
    ext,
    by_cases c_a : a = 0,
    { rw c_a,
      simp only [finsupp.single_eq_same, finsupp.coe_tsub, pi.sub_apply],
      repeat { rw fin.finsupp.cons_zero },
      refl },
    simp only [finsupp.single_eq_same, finsupp.coe_tsub, pi.sub_apply],
    have c_a' : a ≠ 0,
    { simpa using c_a },
    let a' := fin.pred a c_a',
    have r : a = a'.succ := by simp,
    rw r,
    repeat {rw fin.finsupp.cons_succ},
    rw finsupp.single,
    have c_a' : ¬ 0 = a := by cc,
    simp [c_a', if_false] },
  let j' := fin.pred j c_j,
  have r : j = j'.succ := by simp,
  rw [r, fin_succ_equiv_ne_zero],
  rw polynomial.coeff_mul_C,
  rw coeff_mul_X',
  rw hp i,
  simp only [fin.succ_pred, finsupp.mem_support_iff, ne.def],
  by_cases c_mj' : m j' = 0,
  { simp only [ r, fin.finsupp.cons_succ, c_mj',if_false, eq_self_iff_true, not_true ] },
  simp only [ r, fin.finsupp.cons_succ, c_mj', if_true, not_false_iff ],
  congr,
  ext,
  by_cases c_a : a = 0,
  { rw c_a,
    simp [fin.finsupp.cons_zero, finsupp.single, c_j] },
  let a' := fin.pred a c_a,
  have r : a = a'.succ := by simp,
  simp only [finsupp.coe_tsub, pi.sub_apply],
  rw r,
  repeat {rw fin.finsupp.cons_succ},
  simp [finsupp.single, c_j],
end

lemma degree_of_eq {R : Type*}[comm_semiring R]{σ : Type*}
 (p : mv_polynomial σ R) (j : σ) :
  degree_of j p = p.support.sup (λm, m j) :=
begin
  rw [degree_of, degrees, multiset.count_sup],
  congr,
  ext,
  simp,
end

lemma eval_eq_eval_mv_eval' {n : ℕ} {R : Type u} [comm_semiring R]
  (s : fin n → R) (y : R) (f : mv_polynomial (fin (n+1)) R) : 
  eval (fin.cons y s : fin (n+1) → R) f
  = polynomial.eval y (polynomial.map (eval s) ((fin_succ_equiv R n) f)) :=
begin
  apply induction_on f,
  intro a,
  simp,
  intros p q hp hq,
  rw fin_succ_equiv_add,
  simp only [ring_hom.map_add, polynomial.map_add, polynomial.eval_add],
  congr,
  exact hp,
  exact hq,
  intros p j h,
  rw fin_succ_equiv_mul,
  simp only [eval_X, polynomial.map_mul, ring_hom.map_mul, polynomial.eval_mul],
  congr,
  exact h,
  clear h f,
  simp only [fin_succ_equiv_apply, eval₂_hom_X'],
  by_cases c : j = 0,
  { rw c,
    rw fin.cons_zero,
    simp },
  have c' : j ≠ 0 := by simpa only [ne.def],
  let i := fin.pred j c',
  have r : j = i.succ := by simp,
  rw [r, fin.cons_succ],
  simp,
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

lemma degree_eval_le_degree {n : ℕ} {R : Type u} [comm_semiring R]
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

lemma nat_degree_eval_le_nat_degree {n : ℕ} {R : Type u} [comm_semiring R]
(s : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) :
polynomial.nat_degree (polynomial.map (eval s) f) ≤ polynomial.nat_degree f
:= polynomial.nat_degree_le_nat_degree (degree_eval_le_degree s f)

lemma support_f_i {n : ℕ} {R : Type u} [comm_semiring R]
  {f : mv_polynomial (fin (n+1)) R} {i : ℕ} 
  {m : fin n →₀ ℕ }:
  m ∈ (polynomial.coeff ((fin_succ_equiv R n) f) i).support
  ↔ (fin.finsupp.cons i m) ∈ f.support :=
begin
  apply iff.intro,
  intro h,
  simp only [mem_support_iff, ne.def],
  rw ← fin_succ_equiv_coeff_coeff,
  simpa using h,
  intro h,
  rw mem_support_iff,
  rw fin_succ_equiv_coeff_coeff m f i,
  simpa using h,
end

lemma fin_succ_equiv_support {R : Type u}[comm_semiring R] {n i : ℕ} {f : mv_polynomial (fin (n+1)) R} :
i ∈ (fin_succ_equiv R n f).support ↔ ∃ m , (fin.finsupp.cons i m)  ∈ f.support :=
begin
  apply iff.intro,
  intro h,
  have h' := ne_zero_iff.1 (polynomial.mem_support_iff.1 h),
  cases h' with m' hm',
  use m',
  apply support_f_i.1,
  simpa using hm',
  intro hm,
  cases hm with m' hm',
  have h1 : (fin_succ_equiv R n f).coeff i ≠ 0,
  { apply ne_zero_iff.2,
    use m',
    simpa using support_f_i.2 hm' },
  simpa using h1,
end

-- where should this be?
lemma coe_with_bottom_sup {α : Type*} {s : finset α} (h : s.nonempty) (f : α → ℕ): 
 (↑(s.sup f) : (with_bot ℕ)) = s.sup (λ i, ↑(f i) ) := 
 begin
  rw ← finset.coe_sup' h,
  congr, 
  simp only [finset.sup'_eq_sup],
 end 

lemma degree_fin_suc_equiv {n : ℕ} {R : Type u} [comm_semiring R]
  {f : mv_polynomial (fin (n+1)) R} (h : f ≠ 0): 
  (fin_succ_equiv R n f).degree = degree_of 0 f :=
begin
  have t : (fin_succ_equiv R n f).support.nonempty,
  { by_contradiction c,
    simp only [finset.not_nonempty_iff_eq_empty, polynomial.support_eq_empty] at c,
    let t'' : (fin_succ_equiv R n f) ≠ 0,
    { let ii := (fin_succ_equiv R n).symm,
      have h' : f = 0 :=
        calc f =  ii (fin_succ_equiv R n f) :
        begin
          simp only [ii, ←alg_equiv.inv_fun_eq_symm],
          exact ((fin_succ_equiv R n).left_inv f).symm,
        end
        ...    =  ii 0 : by rw c
        ...    = 0 : by simp,
      cc },
    cc },
  rw polynomial.degree,
  have h : (fin_succ_equiv R n f).support.sup (λ x , x)  = degree_of 0 f,
  { apply nat.le_antisymm,
    apply finset.sup_le,
    intros i hi,
    rw degree_of_eq,
    cases fin_succ_equiv_support.1 hi with m hm,
    have t2 := @finset.le_sup ℕ _ _ _ (λ m, m 0 : (fin (n + 1) →₀ ℕ) → ℕ) _ hm,
    simp only at t2,
    rwa fin.finsupp.cons_zero at t2,
    rw degree_of_eq,
    apply @finset.sup_le _ _ _ (f.support) (λ (m : fin (n + 1) →₀ ℕ), m 0),
    intros m hm,
    simp only,
    let m' := fin.finsupp.tail m,
    have hm' : fin.finsupp.cons (m 0) m' = m,
    { rw fin.finsupp.cons_tail (m 0) },
    have h'' : m 0 ∈ (fin_succ_equiv R n f).support, {
      apply (@fin_succ_equiv_support R _ n (m 0) f).2,
      use m',
      rwa hm' },
    apply @finset.le_sup ℕ  _ _ _ (λ x, x) _ h'' },
  rw ← h,
  rw coe_with_bottom_sup t,
  congr,
end

lemma nat_degree_fin_suc_equiv {n : ℕ} {R : Type u} [comm_semiring R]
  (f : mv_polynomial (fin (n+1)) R) : 
  (fin_succ_equiv R n f).nat_degree = degree_of 0 f :=
begin
  by_cases c : f = 0,
  { rw [c, fin_succ_equiv_zero, polynomial.nat_degree_zero, degree_of_zero] },
  have c' : f ≠ 0 := by simpa only [ne.def],
  rw polynomial.nat_degree,
  rw degree_fin_suc_equiv c',
  simp,
end

lemma degree_of_coeff_fin_suc_equiv {n : ℕ} {R : Type u} [comm_semiring R]
  (p : mv_polynomial (fin (n+1)) R) (j : fin n) (i : ℕ) : 
  degree_of j (polynomial.coeff (fin_succ_equiv R n p) i) ≤ degree_of j.succ p :=
begin
  rw [degree_of_eq, degree_of_eq, finset.sup_le_iff],
  intros m hm,
  have t := support_f_i.1 hm,
  rw ← fin.finsupp.cons_succ j i m,
  have h : (fin.finsupp.cons i m) j.succ 
    = (λ (m1 : fin n.succ →₀ ℕ), m1 j.succ) (fin.finsupp.cons i m) := by simp,
  rw h,
  apply finset.le_sup t,
end

end mv_polynomial