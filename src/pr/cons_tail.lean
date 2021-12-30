/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.fin.basic
import data.fin.tuple
import data.finset.basic
import data.finsupp.basic

local attribute [instance] classical.prop_decidable

-- This is now part of PR #10812

/-
namespace fintype

noncomputable def support {M σ : Type*} [has_zero M] [fintype σ] (f : σ → M) : finset σ :=
(fintype.elems σ).filter (λ i, f i ≠ 0)

lemma mem_support_to_fun {M σ : Type*} [has_zero M] [fintype σ] (f : σ → M) :
  ∀ a, a ∈ support f ↔ f a ≠ 0 :=
begin
  intro a,
  rw fintype.support,
  apply iff.intro,
  simp,
  intro h,
  simp only [ne.def, finset.mem_filter],
  apply and.intro,
  exact finset.mem_univ a,
  simpa using h,
end

noncomputable def to_finsupp {M  σ : Type*} [has_zero M] [fintype σ] (f : σ → M ) : σ →₀ M :=
   ⟨fintype.support f, f, fintype.mem_support_to_fun f⟩

end fintype

-/
namespace finsupp
/-

  cons and tail for maps fin n →₀ M

-/ 

noncomputable def tail {n: ℕ } (s : fin (n+1) →₀ ℕ ) : fin n →₀ ℕ 
:= finsupp.equiv_fun_on_fintype.inv_fun (fin.tail s.to_fun)

noncomputable def cons {n:ℕ} (y : ℕ) (s : fin n →₀  ℕ) : fin (n+1) →₀ ℕ := 
finsupp.equiv_fun_on_fintype.inv_fun (fin.cons y s.to_fun)

lemma tail_eq {n :ℕ} (s : fin (n+1) →₀ ℕ) : ∀ (i : fin n), s i.succ = finsupp.tail s i :=
begin
  intro i,
  rw [finsupp.tail, fin.tail],
  congr,
end

lemma cons_zero {n:ℕ} (y : ℕ) (s : fin n →₀  ℕ) : finsupp.cons y s 0 = y :=
by simp [finsupp.cons, finsupp.equiv_fun_on_fintype]

lemma cons_succ {n : ℕ} (i : fin n) (y : ℕ) (s : fin n →₀ ℕ) : finsupp.cons y s i.succ = s i :=
begin 
  simp only [finsupp.cons, fin.cons, finsupp.equiv_fun_on_fintype, fin.cases_succ, finsupp.coe_mk],
  rw [coe_fn, finsupp.has_coe_to_fun],
end

lemma tail_cons {n : ℕ} (y : ℕ) (s : fin n →₀ ℕ) : finsupp.tail (finsupp.cons y s) = s :=
begin
  simp only [finsupp.cons, fin.cons, finsupp.tail, fin.tail],
  ext,
  simp only [equiv_fun_on_fintype_symm_apply_to_fun, equiv.inv_fun_as_coe, 
  finsupp.coe_mk, fin.cases_succ, equiv_fun_on_fintype],
  rw [coe_fn, finsupp.has_coe_to_fun],
end

lemma cons_tail {n : ℕ} (s : fin (n + 1) →₀ ℕ) :
  finsupp.cons (s 0) (finsupp.tail s) = s :=
begin
  ext,
  by_cases c_a : a = 0,
  { rw [c_a, finsupp.cons_zero] },
  { rw [←fin.succ_pred a c_a, finsupp.cons_succ, finsupp.tail_eq] },
end

lemma cons_zero_zero {n : ℕ} : finsupp.cons 0 (0 : fin n →₀  ℕ ) = 0 :=
begin
  ext,
  by_cases c : a ≠ 0,
  { rw [←fin.succ_pred a c, finsupp.cons_succ],
    simp },
  { simp only [not_not] at c,
    rw [c, finsupp.cons_zero 0 0],
    simp },
end

lemma cons_nonzero_any  {n : ℕ} {y : ℕ} {m : fin n →₀ ℕ } (h : y ≠ 0) :
  finsupp.cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h1 : finsupp.cons y m 0 = 0 := by simp [c],
  rw finsupp.cons_zero at h1,
  cc,
end

lemma cons_any_nonzero {n : ℕ} {y : ℕ} {m: fin n →₀ ℕ} (h : m ≠ 0) : finsupp.cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h' : m = 0,
  { ext,
    simp [ ← finsupp.cons_succ a y m, c] },
  cc,
end

end finsupp
