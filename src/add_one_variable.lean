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

/-
# Add one variable

## Main results

- `lemma_2_1`: Let F be a field and f ∈ F[x₀,…,xₙ]. Suppose that for 0 ≤ i ≤ n,
  the degree of f in xᵢ is at most tᵢ. Let S₀,…,Sₙ ⊆ F be subsets such that tᵢ < |Sᵢ|.
  Suppose that f(s₀,…,sₙ) = 0 for each (s₀,…,sₙ) ∈ S₀ × … × Sₙ. Then f = 0.

  This is Lemma 2.1 in Alon's paper "Combinatorial Nullstellensatz".
-/

universes u v

variables {α : Type v}

open_locale big_operators

namespace mv_polynomial

/-
Natural numbers and fin
-/

lemma mod_succ_self_eq_self (n : ℕ) : n % n.succ = n :=
begin
  apply nat.mod_eq_of_lt,
  apply nat.lt_succ_self,
end

lemma coe_eq_mk {n : ℕ }(h : n < n+1): ↑n = fin.mk n h :=
begin
  apply fin.eq_of_veq,
  simp,
  exact mod_succ_self_eq_self n
end

/-
Finsets and multisets
-/

/- these would be useful to have (assuming not already on mathlib!)-/
lemma one_le_count_of_mem 
{α : Type u} [decidable_eq α ]{x :α}
{a : multiset α} (h : x ∈ a) : 1 ≤ a.count x := 
begin
  have t := multiset.count_le_of_le x ( multiset.singleton_le.2 h),
  simp only [multiset.count_singleton, if_pos] at t,
  exact t,
end

lemma le_of_subset_of_nodup 
{α : Type u} [decidable_eq α ]
{a b : multiset α} (h : a ⊆ b) (h' : a.nodup) : a ≤ b 
:=
begin
  apply multiset.le_iff_count.2,
  intro x,
  by_cases c : x ∈ a,
  { rw multiset.count_eq_one_of_mem h' c,
    exact one_le_count_of_mem (multiset.mem_of_subset h c) },
  rw multiset.count_eq_zero_of_not_mem c,
  simp,
end

lemma le_of_val_subset
{α : Type u} [decidable_eq α]
{a : finset α} {b : multiset α} (h : a.val ⊆ b) : a.val ≤ b := 
begin 
  exact le_of_subset_of_nodup h a.2,
end

/-

  cons and tail for maps fin n → R and fin n →₀ M

-/ 

local attribute [instance] classical.prop_decidable

private def point.cons  {n:ℕ}{α: Type*}(y : α) (s' : fin n → α) : fin (n+1) → α := 
fin.cons y s'

private def point.cons_zero {n:ℕ}{α: Type*}(s' : fin n → α)(y : α) : 
point.cons y s' 0 = y :=
begin
  rw point.cons,
  simp,
end

private def point.cons_succ {n:ℕ}{α: Type*}{i : fin n}
(y : α) (s' : fin n → α) : 
point.cons y s' i.succ = s' i :=
begin
  rw point.cons,
  simp,
end

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
    rw ← fin.finsupp.cons_succ a y m,
    rw c,
    simp },
  cc,
end


/-

More lemmas

-/

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

lemma degree_of_zero {R : Type*}[comm_semiring R]{σ : Type*}(i : σ) :
degree_of i (0 : mv_polynomial σ R) = 0 :=
begin
  rw degree_of,
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

lemma well_known_but_cannot_find {n : ℕ} (h : ¬ n = 0) : 0 < n :=
begin
  by_contradiction h',
  simp only [not_lt, le_zero_iff] at h',
  cc,
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
      simp,
      have t : ¬¬(fin.finsupp.cons 0 m) 0 = 0,
      { simp only [not_not],
        rw fin.finsupp.cons_zero },
      simp only [t, if_false] },
    rw fin_succ_equiv_eq_zero,
    let i' := nat.pred i,
    have r : i = i'.succ,
    { rw nat.succ_pred_eq_of_pos _,
      exact well_known_but_cannot_find c_i },
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
  rw degree_of,
  rw degrees,
  simp,
  rw multiset.count_sup,
  congr,
  ext,
  simp,
end

lemma eval_eq_eval_mv_eval' {n : ℕ} {R : Type u} [comm_semiring R]
  (s : fin n → R) (y : R) (f : mv_polynomial (fin (n+1)) R) : 
  eval (point.cons y s) f
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
  simp,
  by_cases c : j = 0,
  { rw c,
    rw point.cons_zero,
    simp },
  have c' : j ≠ 0 := by simpa only [ne.def],
  let i := fin.pred j c',
  have r : j = i.succ := by simp,
  rw [r, point.cons_succ],
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

lemma eq_zero_iff_every_coeff_zero {R : Type u} [comm_semiring R] (p : polynomial R) :
  (∀ i:ℕ, polynomial.coeff p i = 0) ↔ p = 0 :=
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
  apply trans _ (polynomial.card_roots' h),
  rw finset.card,
  have h0 : Z.val ⊆ p.roots,
  { rw multiset.subset_iff,
    intros x hx,
    let z := hZ x hx,
    rwa polynomial.mem_roots h,},
  apply multiset.card_le_of_le (le_of_val_subset h0),
end

/- Lemma 2.1 in Alon's "Combinatorial Nullstellensatz" paper. -/
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
  simpa using (hz fin.is_empty.elim),
  apply (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv F n)).1,
  apply (eq_zero_iff_every_coeff_zero ((fin_succ_equiv F n) f)).1,
  intro i,
  apply hn (polynomial.coeff ((fin_succ_equiv F n) f) i) (fin.finsupp.tail t),
  intro j,
  rw ← fin.finsupp.tail_eq t j,
  exact (degree_of_coeff_fin_suc_equiv f j i).trans (ht j.succ),
  intro j,
  rw ← fin.finsupp.tail_eq t j,
  exact hS j.succ,
  intros s hs,
  rw ← coeff_eval_eq_eval_coeff,
  rw (eq_zero_iff_every_coeff_zero (polynomial.map (eval s) ((fin_succ_equiv F n) f))).2,
  by_contradiction c1,
  have h0 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i.succ) → ∀ y : F, y ∈ S 0 →  
    polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv F n) f)) = 0,
  { intros s' hs' y hy,
    rw [← eval_eq_eval_mv_eval', hz],
    intro i,
    by_cases c : i ≠ 0,
    { let i' := fin.pred i c,
      have r : i = i'.succ := by simp,
      rwa [ r, point.cons_succ y s'],
      exact hs' i' },
    simp only [not_not] at c,
    rwa [c, point.cons_zero] },
  simpa using lt_of_le_of_lt ((number_zeroes_field c1 (S 0) (h0 _ hs)).trans _) (hS 0),
  have x := nat_degree_eval_le_nat_degree s (fin_succ_equiv F n f),
  rw nat_degree_fin_suc_equiv f at x,
  exact x.trans (ht 0),
end

end mv_polynomial
