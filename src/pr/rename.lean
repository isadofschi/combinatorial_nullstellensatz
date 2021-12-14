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


open_locale big_operators

local attribute [instance] classical.prop_decidable

namespace multiset
-- see #10726 https://github.com/leanprover-community/mathlib/pull/10726
theorem count_map_eq_count' {α β : Type* }[decidable_eq β] {f : α → β} (s : multiset α)
  (h : function.injective f) (x : α) : (s.map f).count (f x) = s.count x :=
begin
  suffices : (filter (λ (a : α), f x = f a) s).count x = card (filter (λ (a : α), f x = f a) s),
  { rw [count, countp_map, ← this],
    exact count_filter_of_pos rfl },
  { simp only [count_filter_of_pos],
    have h' : ((λ (a : α), f x = f a) : α → Prop)  = eq x,
    { ext y,
      apply iff.intro,
      exact λ h', h h',
      intro h',
      rw h', },
    simp only [h', count, countp_eq_card_filter],
    congr, }
end

end multiset

namespace mv_polynomial

noncomputable def bundled_map_domain_injective {α β : Type*} {f : α → β} (h : function.injective f) :
 (α →₀ ℕ)  ↪ (β →₀ ℕ) := ⟨finsupp.map_domain f, finsupp.map_domain_injective h⟩

lemma support_rename_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
  {f : σ → τ} (h : function.injective f) : 
  ((rename f p).support : finset (τ →₀ ℕ)) = 
  finset.map (bundled_map_domain_injective h) p.support :=
begin
  rw finset.ext_iff,
  intro a,
  simp only [exists_prop, finset.mem_map, mem_support_iff, ne.def],
  apply iff.intro,
  intro h1,
  cases coeff_rename_ne_zero f p a h1 with d hd,
  use d,
  simpa only [bundled_map_domain_injective, function.embedding.coe_fn_mk] using hd.symm,
  intro h,
  cases h with b hb,
  simpa only [← hb.2, bundled_map_domain_injective, function.embedding.coe_fn_mk,
              coeff_rename_map_domain f h p b] using hb.1,
end

lemma multiset.sup_map {α β γ : Type* } {f : β → γ} (h : function.injective f) (g : α → multiset β) (s : finset α) : 
  multiset.map f (s.sup g) = s.sup (λ x,  multiset.map f (g x)) :=
begin
  apply finset.cons_induction_on s,
  simp,
  intros a s' h_a_s h_ind,
  simp [finset.sup_cons, ← h_ind, multiset.map_union h],
end

lemma rename_degrees_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
  {f : σ → τ} (h : function.injective f) : degrees (rename f p) = (degrees p).map f :=
begin
  have h1 : (λ (x : σ →₀ ℕ), multiset.map f (finsupp.to_multiset x)) 
    = λ x, (x.map_domain f).to_multiset,
  { ext,
    rw finsupp.to_multiset_map, },
  simp only [degrees, multiset.sup_map h, h1, support_rename_injective h, finset.sup_map],
  congr,
end

lemma degree_of_rename_injective {R σ τ : Type*} [comm_semiring R] {p : mv_polynomial σ R}
{f : σ → τ} (h : function.injective f) (i : σ) : degree_of i p = degree_of (f i) (rename f p) :=
by simp [degree_of, rename_degrees_injective h, multiset.count_map_eq_count' (p.degrees) h]

end mv_polynomial