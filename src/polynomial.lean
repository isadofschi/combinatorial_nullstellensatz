/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic


local attribute [instance] classical.prop_decidable

namespace PR10603 -- #10603 - https://github.com/leanprover-community/mathlib/pull/10603
universes u
variables {α : Type u}
open_locale big_operators
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
lemma val_le_of_val_subset
{α : Type u} [decidable_eq α]
{a : finset α} {b : multiset α} (h : a.val ⊆ b) : a.val ≤ b := 
begin 
  exact le_of_subset_of_nodup h a.2,
end
end PR10603


namespace polynomial

universes u v

variables {α : Type v}

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
  apply multiset.card_le_of_le (PR10603.val_le_of_val_subset h0),
end

end polynomial