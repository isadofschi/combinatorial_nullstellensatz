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


-- This is PR #10921

open_locale big_operators

local attribute [instance] classical.prop_decidable

namespace mv_polynomial

noncomputable def map_domain_embedding_of_injective {α β : Type*} {f : α → β} (h : function.injective f) :
 (α →₀ ℕ)  ↪ (β →₀ ℕ) := ⟨finsupp.map_domain f, finsupp.map_domain_injective h⟩

noncomputable def map_domain_embedding_of_embedding {α β : Type*} (f : α ↪ β) :
 (α →₀ ℕ)  ↪ (β →₀ ℕ) := ⟨finsupp.map_domain f.to_fun, finsupp.map_domain_injective f.inj'⟩


/-
-- variante con embedding
lemma support_rename_injective' {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
  {f : σ ↪ τ} : 
  (rename f p).support = finset.map (map_domain_embedding_of_embedding f) p.support 
  := sorry
-/

lemma support_rename_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
  {f : σ → τ} (h : function.injective f) : 
  (rename f p).support  = finset.map (map_domain_embedding_of_injective h) p.support :=
begin
  rw finset.ext_iff,
  intro a,
  simp only [exists_prop, finset.mem_map, mem_support_iff, ne.def],
  apply iff.intro,
  intro h1,
  cases coeff_rename_ne_zero f p a h1 with d hd,
  use d,
  simpa only [map_domain_embedding_of_injective, function.embedding.coe_fn_mk] using hd.symm,
  intro h,
  cases h with b hb,
  simpa only [← hb.2, map_domain_embedding_of_injective, function.embedding.coe_fn_mk,
              coeff_rename_map_domain f h p b] using hb.1,
end

lemma multiset.sup_map {α β γ : Type*}
 {f : β → γ} (h : function.injective f) (g : α → multiset β) (s : finset α) : 
  multiset.map f (s.sup g) = s.sup (λ x,  multiset.map f (g x)) :=
begin
  apply finset.cons_induction_on s,
  simp,
  intros a s' h_a_s h_ind,
  simp [finset.sup_cons, ← h_ind, multiset.map_union h],
end

/-
lemma sup_map_multiset {α β γ: Type*} [semilattice_sup α] [has_bot α] 
   (s : finset γ) (f : γ → multiset β) (g : β ↪ α) :
   multiset.map g (s.sup f) = s.sup (multiset.map g ∘ f) :=
begin
  apply finset.cons_induction_on s,
  simp,
  intros a s' h_a_s h_ind,
  simp only [finset.sup_cons, ←h_ind, multiset.sup_eq_union, function.comp_app],
  rw multiset.map_union,
  exact g.inj',
end

-/

lemma rename_degrees_of_injective {R σ τ : Type*} [decidable_eq σ] [decidable_eq τ][comm_semiring R] {p : mv_polynomial σ R}
  {f : σ → τ} (h : function.injective f) : degrees (rename f p) = (degrees p).map f :=
begin
  have h1 : (λ (x : σ →₀ ℕ), multiset.map f (finsupp.to_multiset x)) 
    = λ x, (x.map_domain f).to_multiset,
  { ext,
    rw finsupp.to_multiset_map, },
  have t := multiset.sup_map h finsupp.to_multiset p.support,
  simp only [degrees, h1, t, support_rename_injective h, finset.sup_map],
  congr,
end

lemma degree_of_rename_of_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
{f : σ → τ} (h : function.injective f) (i : σ) : degree_of i p = degree_of (f i) (rename f p) :=
by simp only [degree_of, rename_degrees_of_injective h, multiset.count_map_eq_count' f (p.degrees) h]

end mv_polynomial