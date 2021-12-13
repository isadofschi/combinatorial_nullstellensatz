/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.fin.basic
import data.fin.tuple
import data.finset.basic
import data.finsupp.basic

namespace fin.finsupp
/-

  cons and tail for maps fin n →₀ M

-/ 

local attribute [instance] classical.prop_decidable

noncomputable def fin.support {M : Type*} [has_zero M] {n : ℕ} (f : fin n → M) : finset (fin n) :=
(finset.fin_range n).filter (λ i, f i ≠ 0)

lemma fin.mem_support_to_fun {M : Type*} [has_zero M] {n : ℕ} (f : fin n → M) :
  ∀ a, a ∈ fin.support f ↔ f a ≠ 0 :=
begin
  intro a,
  rw fin.support,
  simp,
end

noncomputable def fin.to_finsupp {M : Type*} [has_zero M] {n : ℕ} (f : fin n → M ) : fin n →₀ M :=
   ⟨fin.support f, f, fin.mem_support_to_fun f⟩

noncomputable def tail {n: ℕ } (s : fin (n+1) →₀ ℕ ) : fin n →₀ ℕ 
:= fin.to_finsupp (fin.tail s.to_fun)

noncomputable def cons {n:ℕ} (y : ℕ) (s : fin n →₀  ℕ) : fin (n+1) →₀ ℕ := 
fin.to_finsupp (fin.cons y s.to_fun)

lemma tail_eq {n :ℕ} (s : fin (n+1) →₀ ℕ) : ∀ (i : fin n), s i.succ = fin.finsupp.tail s i :=
begin
  intro i,
  rw [fin.finsupp.tail, fin.tail],
  congr,
end

lemma cons_zero {n:ℕ} (y : ℕ) (s : fin n →₀  ℕ) : fin.finsupp.cons y s 0 = y :=
by simp [fin.finsupp.cons, fin.to_finsupp]

lemma cons_succ {n : ℕ} (i : fin n) (y : ℕ) (s : fin n →₀ ℕ) : fin.finsupp.cons y s i.succ = s i :=
begin 
  simp only [fin.finsupp.cons, fin.cons, fin.to_finsupp, fin.cases_succ, finsupp.coe_mk],
  rw [coe_fn, finsupp.has_coe_to_fun],
end


lemma tail_cons {n : ℕ} (y : ℕ) (s : fin n →₀ ℕ) : fin.finsupp.tail (fin.finsupp.cons y s) = s :=
begin
  simp only [fin.finsupp.cons, fin.cons, fin.finsupp.tail, fin.tail],
  ext,
  simp only [fin.to_finsupp, finsupp.coe_mk,fin.cases_succ],
  rw [coe_fn, finsupp.has_coe_to_fun],
end

lemma cons_tail {n : ℕ} (y : ℕ) (s : fin (n + 1) →₀ ℕ) :
  fin.finsupp.cons (s 0) (fin.finsupp.tail s) = s :=
begin
  ext,
  by_cases c_a : a = 0,
  { rw [c_a, fin.finsupp.cons_zero] },
  { rw [←fin.succ_pred a c_a, fin.finsupp.cons_succ, fin.finsupp.tail_eq] },
end

lemma cons_zero_zero {n : ℕ} : fin.finsupp.cons 0 (0 : fin n →₀  ℕ ) = 0 :=
begin
  ext,
  by_cases c : a ≠ 0,
  { rw [←fin.succ_pred a c, fin.finsupp.cons_succ],
    simp },
  { simp only [not_not] at c,
    rw [c, fin.finsupp.cons_zero 0 0],
    simp },
end

lemma cons_nonzero_any  {n : ℕ} {y : ℕ} {m : fin n →₀ ℕ } (h : y ≠ 0) :
  fin.finsupp.cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h1 : fin.finsupp.cons y m 0 = 0 := by simp [c],
  rw fin.finsupp.cons_zero at h1,
  cc,
end

lemma cons_any_nonzero {n : ℕ} {y : ℕ} {m: fin n →₀ ℕ} (h : m ≠ 0) : fin.finsupp.cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h' : m = 0,
  { ext,
    simp [ ← fin.finsupp.cons_succ a y m, c] },
  cc,
end

end fin.finsupp
