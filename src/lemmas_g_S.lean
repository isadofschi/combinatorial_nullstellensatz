/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.variables
import algebra.algebra.basic
import data.mv_polynomial.comm_ring
import data.nat.basic

import degree

universes u

open set function finsupp add_monoid_algebra


open_locale big_operators 

namespace mv_polynomial

lemma eval_is_zero { n : ℕ } {R σ : Type*} [comm_ring R] [is_domain R] (S : finset R) (hS : 0 < S.card) 
  (s : σ → R) (i : σ) (h_s : s i ∈ S) : eval s (∏ s in S, (X i - C s)) = 0 :=
by simp  [eval_prod, finset.prod_eq_zero h_s]

/-
  Do this with more generality.
-/

-- Rename these results

lemma g_S_lem_0 { n : ℕ } {F : Type u} [field F] (S : finset F) (i : fin n) :
(∏ s in S, (X i - C s)) ≠ 0 := sorry

lemma g_S_lem_6 { n : ℕ } {F : Type u} [field F] {S : finset F} {i j: fin n}
  {m: fin n →₀ ℕ} (h_m : m ∈ (∏ s in S, (X i - C s)).support) 
  (h : i ≠ j) : m j = 0 :=
begin
  -- use https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L1164
  sorry
end

lemma g_S_lem_6' { n : ℕ } {F : Type u} [field F] {S : finset F} {i j: fin n}
  {m: fin n →₀ ℕ} (h : j ≠ i) (h' : m j ≠ 0) :  coeff m  (∏ s in S, (X i - C s)) = 0 :=
begin
  sorry
end

lemma g_S_lem_7 { n : ℕ } {F : Type u} [field F] {S : finset F} {i: fin n}
  {m: fin n →₀ ℕ} (h_m : m ∈ (∏ s in S, (X i - C s)).support) : m i ≤ S.card
:= sorry

lemma g_S_lem_8  { n : ℕ } {F : Type u} [field F] {S : finset F} {i: fin n}
  : coeff (single i S.card) ∏ s in S, (X i - C s) = 1 :=
begin
  sorry,
end

lemma g_S_lem_4 { n : ℕ } {F : Type u} [field F] {S : finset F} {i : fin n} :
  total_degree (∏ s in S, (X i - C s)) = S.card :=
begin
  sorry
end

-- Maybe the following is useful here:
-- https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L1151

lemma g_S_lem_5 { n : ℕ } {F : Type u} [field F] {S : finset F} {i : fin n}
  {m: fin n →₀ ℕ} (h_m : m ∈ (∏ s in S, (X i - C s)).support)
  (h_m_i : m i = S.card) : m = single i S.card :=
begin
  sorry
end
 
lemma g_S_lem_1 { n : ℕ } {F : Type u} [field F] (S : finset F) (i : fin n) :
  dominant_monomial (finsupp.single i (S.card)) (∏ s in S, (X i - C s)) :=
begin
  sorry,
end



end mv_polynomial