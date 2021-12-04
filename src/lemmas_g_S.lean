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

universes u v

variables {α : Type v}

open set function finsupp add_monoid_algebra


open_locale big_operators 

namespace mv_polynomial

/-
  Do this with more generality
-/

lemma lemita1 { n : ℕ } {F : Type u} [field F] (S : finset F) (i : fin n) :
  dominant_monomial (finsupp.single i (S.card)) (∏ s in S, (X i - C s)) :=
begin
  sorry,
end

lemma lemita4 { n : ℕ } {F : Type u} [field F] {S : finset F} {i : fin n} :
  total_degree (∏ s in S, (X i - C s)) = S.card :=
begin
  sorry
end

lemma lemita5 { n : ℕ } {F : Type u} [field F] {S : finset F} {i : fin n}
  {m: fin n →₀ ℕ} (h_m : m ∈ (∏ s in S, (X i - C s)).support)
  (h_m_i : m i = S.card) : m = single i S.card :=
begin
  sorry
end

lemma lemita6 { n : ℕ } {F : Type u} [field F] {S : finset F} {i j: fin n}
  {m: fin n →₀ ℕ} (h_m : m ∈ (∏ s in S, (X i - C s)).support) 
  (h : i ≠ j) : m j = 0 :=
begin
  sorry
end

lemma lemita6' { n : ℕ } {F : Type u} [field F] {S : finset F} {i j: fin n}
  {m: fin n →₀ ℕ} (h : j ≠ i) (h' : m j ≠ 0) :  coeff m  (∏ s in S, (X i - C s)) = 0 :=
begin
  sorry
end


lemma lemita7 { n : ℕ } {F : Type u} [field F] {S : finset F} {i: fin n}
  {m: fin n →₀ ℕ} (h_m : m ∈ (∏ s in S, (X i - C s)).support) : m i ≤ S.card
:= sorry

lemma lemita8  { n : ℕ } {F : Type u} [field F] {S : finset F} {i: fin n}
  : coeff (single i S.card) ∏ s in S, (X i - C s) = 1 :=
begin
  sorry,
end

lemma eval_is_zero { n : ℕ } {F : Type u} [field F]
  (S : finset F)
  (hS : 0 < S.card) 
  (s : fin n → F)
  (i : fin n)
  (h_s : s i ∈ S) :
  eval s (∏ s in S, (X i - C s)) = 0
:= begin
  sorry,
end

end mv_polynomial