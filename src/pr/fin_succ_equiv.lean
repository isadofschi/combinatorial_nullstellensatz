/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/

--This is now PR #10812

import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic

import pr.cons_tail

namespace polynomial

lemma degree_mono {R S: Type*} [comm_semiring R][comm_semiring S] 
{f : polynomial R}{g : polynomial S} (h : f.support ⊆ g.support) : f.degree ≤ g.degree :=
by simpa only [degree] using finset.sup_mono h
end polynomial

namespace mv_polynomial

universes u v

variables {α : Type v}

open_locale big_operators

lemma fin_succ_equiv_add {n : ℕ} {R : Type u} [comm_semiring R]
  (f g : mv_polynomial (fin (n + 1)) R) : fin_succ_equiv R n (f + g)
  = fin_succ_equiv R n f + fin_succ_equiv R n g := by simp

lemma fin_succ_equiv_mul {n : ℕ} {R : Type u} [comm_semiring R]
  (f g : mv_polynomial (fin (n + 1)) R) :
  fin_succ_equiv R n (f * g) = fin_succ_equiv R n f * fin_succ_equiv R n g := by simp

lemma fin_succ_equiv_zero {n : ℕ} {R : Type u} [comm_semiring R] :
  fin_succ_equiv R n 0 = 0 := by simp

lemma fin_succ_equiv_X_eq_zero {n : ℕ} {R : Type u} [comm_semiring R] :
  fin_succ_equiv R n (X 0) = polynomial.X := by simp

lemma fin_succ_equiv_X_ne_zero {n : ℕ} {R : Type u} [comm_semiring R] {j : fin n} :
  fin_succ_equiv R n (X j.succ) = polynomial.C (X j) := by simp

private lemma fin_succ_equiv_coeff_coeff_C {n : ℕ } {R : Type u} [comm_semiring R] 
  (a : R) (i : ℕ) (m : fin n →₀ ℕ) : 
  coeff m (((fin_succ_equiv R n) (C a)).coeff i) = coeff (finsupp.cons i m) (C a) :=
begin
  by_cases c_i : i = 0,
  { simp only [c_i, fin_succ_equiv_apply, polynomial.coeff_C_zero, coeff_C, ring_hom.coe_comp,
               eval₂_hom_C],
    by_cases c_m : 0 = m,
    { simp only [← c_m, if_true, eq_self_iff_true, finsupp.cons_zero_zero] },
    { have x : ¬ finsupp.cons 0 m = 0,
      { apply finsupp.cons_any_nonzero,
        symmetry,
        simpa using c_m },
      have x' : ¬ 0 = finsupp.cons 0 m := by cc,
      simp only [c_m, if_false, x', if_false] } },
  { have x : ¬ finsupp.cons i m = 0,
    { apply finsupp.cons_nonzero_any,
      simpa using c_i },
    have x' :  ¬ 0 = finsupp.cons i m := by cc,
    simp only [fin_succ_equiv_apply, coeff_C, function.comp_app, ring_hom.coe_comp, eval₂_hom_C,
               polynomial.coeff_C, c_i, if_false, coeff_zero, x', if_false] },
end

local attribute [instance] classical.prop_decidable


private lemma fin_succ_equiv_coeff_coeff_case_p_X  {n : ℕ } {R : Type u} [comm_semiring R] 
  (p : mv_polynomial (fin (n + 1)) R) (j : fin (n + 1)) (hp : ∀ (i : ℕ) (m : fin n →₀ ℕ),
  coeff m (((fin_succ_equiv R n) p).coeff i) = coeff (finsupp.cons i m) p) (i : ℕ) 
  (m : fin n →₀ ℕ) : coeff m (((fin_succ_equiv R n) (p * X j)).coeff i) 
  = coeff (finsupp.cons i m) (p * X j) :=
begin
  rw [coeff_mul_X' (finsupp.cons i m) j p, fin_succ_equiv_mul],
  by_cases c_j : j = 0,
  { rw c_j,
    by_cases c_i : i = 0,
    { rw c_i,
      simp only [fin_succ_equiv_apply, fin.cases_zero, polynomial.coeff_X_zero, coe_eval₂_hom,
                  polynomial.mul_coeff_zero, finsupp.mem_support_iff, ne.def, eval₂_hom_X', 
                  mul_zero, coeff_zero ],
      have t : ¬¬(finsupp.cons 0 m) 0 = 0 := by simp only [ not_not, finsupp.cons_zero],
      simp only [t, if_false] },
    { rw fin_succ_equiv_X_eq_zero,
      let i' := nat.pred i,
      have r : i = i'.succ,
      { rw nat.succ_pred_eq_of_pos _,
        exact nat.pos_of_ne_zero (by simpa) },
      rw [r, polynomial.coeff_mul_X, hp i'],
      simp only [finsupp.mem_support_iff, ne.def, finsupp.cons_zero],
      rw ← r,
      simp only [c_i, if_true, not_false_iff],
      congr,
      ext,
      by_cases c_a : a = 0,
      { rw c_a,
        simp only [finsupp.single_eq_same, finsupp.coe_tsub, pi.sub_apply],
        repeat { rw finsupp.cons_zero },
        refl },
      { simp only [finsupp.single_eq_same, finsupp.coe_tsub, pi.sub_apply],
        have c_a' : a ≠ 0 := by simpa using c_a,
        rw [←fin.succ_pred a c_a', finsupp.cons_succ, finsupp.cons_succ, finsupp.single],
        have c_a'' : ¬ 0 = a := by simpa using c_a'.symm,
        simp [c_a'', if_false] } } },
  { let j' := fin.pred j c_j,
    have r : j = j'.succ := by simp,
    rw [r, fin_succ_equiv_X_ne_zero, polynomial.coeff_mul_C, coeff_mul_X', hp i],
    simp only [fin.succ_pred, finsupp.mem_support_iff, ne.def],
    by_cases c_mj' : m j' = 0,
    { simp only [r, finsupp.cons_succ, c_mj', if_false, eq_self_iff_true, not_true] },
    { simp only [r, finsupp.cons_succ, c_mj', if_true, not_false_iff],
      congr,
      ext,
      by_cases c_a : a = 0,
      { simp [c_a, finsupp.cons_zero, finsupp.single, c_j] },
      { simp only [finsupp.coe_tsub, pi.sub_apply],
        rw ←fin.succ_pred a c_a,
        repeat {rw finsupp.cons_succ},
        simp [finsupp.single, c_j] } } },
end

/-- This gives the relation between the coefficients of the coefficients of `fin_succ_equiv R n f`
    and the coefficients of `f`. -/
lemma fin_succ_equiv_coeff_coeff {n : ℕ} {R : Type u} [comm_semiring R]
  (m : fin n →₀  ℕ) (f : mv_polynomial (fin (n + 1)) R ) (i : ℕ) :
  coeff m (polynomial.coeff (fin_succ_equiv R n f) i) = coeff (finsupp.cons i m) f :=
begin
  revert i m,
  apply induction_on f,
  apply fin_succ_equiv_coeff_coeff_C,
  intros p q hp hq i m,
  rw [ fin_succ_equiv_add, polynomial.coeff_add, coeff_add, coeff_add, hp, hq],
  apply fin_succ_equiv_coeff_coeff_case_p_X,
end

lemma eval_eq_eval_mv_eval' {n : ℕ} {R : Type u} [comm_semiring R] (s : fin n → R) (y : R)
  (f : mv_polynomial (fin (n + 1)) R) : eval (fin.cons y s : fin (n + 1) → R) f
  = polynomial.eval y (polynomial.map (eval s) ((fin_succ_equiv R n) f)) :=
begin
  apply induction_on f,
  intro a,
  simp,
  intros p q hp hq,
  simp only [fin_succ_equiv_add, ring_hom.map_add, polynomial.map_add, polynomial.eval_add],
  congr,
  exact hp,
  exact hq,
  intros p j h,
  simp only [fin_succ_equiv_mul, eval_X, polynomial.map_mul, ring_hom.map_mul, 
             polynomial.eval_mul],
  congr,
  exact h,
  clear h f,
  simp only [fin_succ_equiv_apply, eval₂_hom_X'],
  by_cases c : j = 0,
  { rw c,
    simp [fin.cons_zero] },
  have c' : j ≠ 0 := by simpa only [ne.def],
  rw [←fin.succ_pred j c', fin.cons_succ],
  simp,
end

lemma coeff_eval_eq_eval_coeff {n : ℕ} {R : Type u} [comm_semiring R] (s' : fin n → R)
  (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ) :
  polynomial.coeff (polynomial.map (eval s') f) i =  eval s' (polynomial.coeff f i) :=
by simp only [polynomial.coeff_map]

lemma support_eval' {n : ℕ} {R : Type u} [comm_semiring R] (s' : fin n → R)
  (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ) 
  (h : i ∈ (polynomial.map (eval s') f).support) : i ∈ f.support :=
begin
  simp only [polynomial.mem_support_iff, polynomial.coeff_map, ne.def] at h,
  by_contradiction c,
  simp only [polynomial.mem_support_iff, not_not, ne.def] at c,
  rw c at h,
  simpa using h,
end

lemma support_eval {n : ℕ} {R : Type u} [comm_semiring R] (s' : fin n → R) 
  (f : polynomial (mv_polynomial (fin n) R)): (polynomial.map (eval s') f).support ⊆ f.support :=
finset.subset_iff.1 (support_eval' s' f)

lemma degree_eval_le_degree {n : ℕ} {R : Type u} [comm_semiring R] (s' : fin n → R)
  (f : polynomial (mv_polynomial (fin n) R)) : 
  polynomial.degree (polynomial.map (eval s') f) ≤ polynomial.degree f :=
polynomial.degree_mono ( support_eval s' f)

lemma nat_degree_eval_le_nat_degree {n : ℕ} {R : Type u} [comm_semiring R] (s : fin n → R)
  (f : polynomial (mv_polynomial (fin n) R)) :
polynomial.nat_degree (polynomial.map (eval s) f) ≤ polynomial.nat_degree f
:= polynomial.nat_degree_le_nat_degree (degree_eval_le_degree s f)

lemma support_coeff_fin_succ_equiv {n : ℕ} {R : Type u} [comm_semiring R] {f : mv_polynomial (fin (n + 1)) R}
  {i : ℕ} {m : fin n →₀ ℕ } : m ∈ (polynomial.coeff ((fin_succ_equiv R n) f) i).support
  ↔ (finsupp.cons i m) ∈ f.support :=
begin
  apply iff.intro,
  intro h,
  simpa [←fin_succ_equiv_coeff_coeff] using h,
  intro h,
  simpa [mem_support_iff, ←fin_succ_equiv_coeff_coeff m f i] using h,
end

lemma fin_succ_equiv_support {R : Type u}[comm_semiring R] {n i : ℕ}
  {f : mv_polynomial (fin (n + 1)) R} : i ∈ (fin_succ_equiv R n f).support
  ↔ ∃ m, (finsupp.cons i m) ∈ f.support :=
begin
  apply iff.intro,
  intro h,
  cases ne_zero_iff.1 (polynomial.mem_support_iff.1 h) with m' hm',
  exact ⟨m', support_coeff_fin_succ_equiv.1 (mem_support_iff.2 hm')⟩,
  intro hm,
  cases hm with m' hm',
  simpa using ne_zero_iff.2 ⟨m', mem_support_iff.1 (support_coeff_fin_succ_equiv.mpr hm')⟩,
end

-- where should this be?
lemma coe_with_bottom_sup {α : Type*} {s : finset α} (h : s.nonempty) (f : α → ℕ) : 
  (↑(s.sup f) : (with_bot ℕ)) = s.sup (λ i, f i) := 
begin
  rw ← finset.coe_sup' h,
  congr, 
  simp only [finset.sup'_eq_sup],
end 

lemma support_fin_succ_equiv_nonempty  {n : ℕ} {R : Type u} [comm_semiring R]
  {f : mv_polynomial (fin (n + 1)) R} (h : f ≠ 0) : (fin_succ_equiv R n f).support.nonempty :=
begin
  by_contradiction c,
  simp only [finset.not_nonempty_iff_eq_empty, polynomial.support_eq_empty] at c,
  have t'' : (fin_succ_equiv R n f) ≠ 0,
  { let ii := (fin_succ_equiv R n).symm,
    have h' : f = 0 :=
      calc f =  ii (fin_succ_equiv R n f) : by  simpa only [ii, ←alg_equiv.inv_fun_eq_symm]
                                                using ((fin_succ_equiv R n).left_inv f).symm
      ...    =  ii 0 : by rw c
      ...    = 0 : by simp,
    cc },
  cc,
end

lemma degree_fin_succ_equiv {n : ℕ} {R : Type u} [comm_semiring R]
  {f : mv_polynomial (fin (n + 1)) R} (h : f ≠ 0) :
  (fin_succ_equiv R n f).degree = degree_of 0 f :=
begin
  rw polynomial.degree,
  have h' : (fin_succ_equiv R n f).support.sup (λ x , x)  = degree_of 0 f,
  { rw degree_of_eq_sup,
    apply nat.le_antisymm,
    apply finset.sup_le,
    intros i hi,
    cases fin_succ_equiv_support.1 hi with m hm,
    simpa only [finsupp.cons_zero] using
      @finset.le_sup ℕ _ _ _ _ (λ m, m 0 : (fin (n + 1) →₀ ℕ) → ℕ) _ hm,
    apply @finset.sup_le _ _ _ _ (f.support) (λ (m : fin (n + 1) →₀ ℕ), m 0),
    intros m hm,
    simp only,
    exact @finset.le_sup ℕ  _ _ _ _ (λ x, x) _ 
    ( (@fin_succ_equiv_support R _ n (m 0) f).2
      ⟨finsupp.tail m, (by rwa (finsupp.cons_tail m))⟩) },
  rw ← h',
  rw coe_with_bottom_sup (support_fin_succ_equiv_nonempty h),
  congr,
end

lemma nat_degree_fin_succ_equiv {n : ℕ} {R : Type u} [comm_semiring R]
  (f : mv_polynomial (fin (n + 1)) R) : (fin_succ_equiv R n f).nat_degree = degree_of 0 f :=
begin
  by_cases c : f = 0,
  { rw [c, (fin_succ_equiv R n).map_zero, polynomial.nat_degree_zero, degree_of_zero] },
  { rw [polynomial.nat_degree, degree_fin_succ_equiv (by simpa only [ne.def]) ],
    simp },
end

lemma degree_of_coeff_fin_succ_equiv {n : ℕ} {R : Type u} [comm_semiring R]
  (p : mv_polynomial (fin (n + 1)) R) (j : fin n) (i : ℕ) : 
  degree_of j (polynomial.coeff (fin_succ_equiv R n p) i) ≤ degree_of j.succ p :=
begin
  rw [degree_of_eq_sup, degree_of_eq_sup, finset.sup_le_iff],
  intros m hm,
  rw ← finsupp.cons_succ j i m,
  convert finset.le_sup (support_coeff_fin_succ_equiv.1 hm),
  refl,
end

end mv_polynomial