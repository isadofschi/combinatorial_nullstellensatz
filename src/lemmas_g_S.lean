/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.variables
import data.mv_polynomial.supported
import algebra.algebra.basic
import data.mv_polynomial.comm_ring
import data.nat.basic

import degree
import degree_new

universes u

open set function finsupp add_monoid_algebra


open_locale big_operators 

namespace mv_polynomial

--- lemmas for supported

lemma degree_of_eq_total_degree {R σ : Type*} [field R] {p : mv_polynomial σ R}
 (i : σ) (h : p ∈ supported R ({i}: set σ)) : degree_of i p = total_degree p := sorry


lemma g_S_lem_6 {R σ : Type*} [comm_semiring R] {p : mv_polynomial σ R} {m: σ →₀ ℕ} {i j : σ} 
  (hp : p ∈ supported R ({i} : set σ)) (h_m : m ∈ p.support) (h : i ≠ j) : m j = 0 :=
begin
  -- use https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L1164
  sorry
end

lemma g_S_lem_6'{R σ : Type*} [comm_semiring R] {i j: σ}  {p : mv_polynomial σ R}
  {m: σ →₀ ℕ} (hp : p ∈ supported R ({i} : set σ)) (h' : m j ≠ 0) (h : j ≠ i)  :
    coeff m  p = 0 :=
begin
  sorry
end

-- this follows from a more general lemma!
lemma g_S_lem_7  {R σ : Type*} [comm_semiring R] {i: σ} {p : mv_polynomial σ R}
  {m: σ →₀ ℕ} (h_m : m ∈ p.support) : m i ≤ p.total_degree
:= sorry

-- Maybe the following is useful here:
-- https://github.com/leanprover-community/flt-regular/blob/c85f9a22a02515a27fe7bc93deaf8487ab22ca59/src/ring_theory/polynomial/homogenization.lean#L1151

lemma g_S_lem_5 {R  σ : Type* } [field R] {i : σ}
  {m: σ →₀ ℕ}  {p : mv_polynomial σ R}
  (h_m : m ∈ p.support) (hp : p ∈ supported R ({i} : set σ))
  (h_m_i : m i = p.total_degree) : m = finsupp.single i p.total_degree :=
begin
  sorry
end
 
lemma g_S_lem_1 {R σ : Type*} [field R] {p : mv_polynomial σ R} {i : σ} 
(hp : p ∈ supported R ({i} : set σ)) : dominant_monomial (finsupp.single i p.total_degree) p :=
begin
  sorry,
end

-- special case

lemma eval_is_zero {R σ : Type*} [comm_ring R] [is_domain R] (S : finset R) (hS : 0 < S.card) 
  (s : σ → R) (i : σ) (h_s : s i ∈ S) : eval s (∏ s in S, (X i - C s)) = 0 :=
by simp  [eval_prod, finset.prod_eq_zero h_s]


lemma g_S_lem_0 { n : ℕ } {F : Type u} [field F] (S : finset F) (i : fin n) :
(∏ s in S, (X i - C s)) ≠ 0 := sorry

lemma g_S_lem_4 { n : ℕ } {F : Type u} [field F] {S : finset F} {i : fin n} :
  total_degree (∏ s in S, (X i - C s)) = S.card :=
begin
  sorry
end

lemma g_S_lem_8  { n : ℕ } {F : Type u} [field F] (S : finset F)(i : fin n)
  : coeff (single i S.card) ∏ s in S, (X i - C s) = 1 :=
begin
  sorry,
end

lemma g_S_lem_supported {R σ : Type*} [field R] (S : finset R) (i : σ) :
∏ s in S, (X i - C s) ∈ supported R ({i}: set σ) := sorry

lemma g_S_lem_1' { n : ℕ } {F : Type u} [field F] (S : finset F) (i : fin n) :
  dominant_monomial (finsupp.single i (S.card)) (∏ s in S, (X i - C s)) :=
begin
  sorry,
end

end mv_polynomial