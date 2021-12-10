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

-- check https://github.com/leanprover-community/flt-regular/blob/master/src/ring_theory/polynomial/homogenization.lean
-- and https://github.com/leanprover-community/mathlib/pull/10429/files for useful lemmas

namespace mv_polynomial 

variables {R : Type*} {σ : Type*} 

/- 
  
  New definitions: monomial_degree, max_degree_monomial, dominant_monomial

-/

-- this def is also given in flt-regular
def monomial_degree {s : Type*} (t : s →₀ ℕ) : ℕ := t.sum (λ _ e, e) --∑ i in t.support, t i

lemma nat.term_le_sum {s : finset α } (f : α → ℕ){j : α} (hj : j ∈ s) : f j ≤ s.sum f :=
begin
  revert j,
  apply finset.cons_induction_on s,
  simp,
  clear s,
  intros x s hx hj j hc,
  rw finset.sum_cons,
  simp only [finset.mem_cons] at hc,
  cases hc with j_eq_x j_in_s,
  simp [j_eq_x],
  apply (hj j_in_s).trans,
  simp,
end

lemma le_monomial_degree  {s : Type*} (t : s →₀ ℕ) (j : s) : t j ≤ monomial_degree t :=
begin
  by_cases c : j ∈ t.support,
  { apply nat.term_le_sum,
    exact c },
  simp only [not_not, finsupp.mem_support_iff] at c,
  simp [c],
end

-- this holds for  [ordered_add_comm_monoid N] if 0 ≤ n forall n ∈ N 
lemma finsupp.support_subset_of_le {s : Type*}  {f g :  s →₀ ℕ} (h : f ≤ g) :
f.support ⊆ g.support := 
begin
  unfold has_subset.subset,
  intros a ha,
  simp only [finsupp.mem_support_iff, ne.def] at ha,
  have t := lt_of_lt_of_le (nat.pos_of_ne_zero ha) (h a),
  simp only [finsupp.mem_support_iff, ne.def],
  by_contra,
  rw h at t,
  simpa using t,
end

-- this holds for [ordered_add_comm_monoid N] (with a different proof)
lemma finsupp.sum_le_sum {s : Type*}  {f g :  s →₀ ℕ} (h : f ≤ g) :
f.sum (λ x y , y) ≤ g.sum (λ x y , y) :=
begin
  rw sum_of_support_subset f (finsupp.support_subset_of_le h) (λ x y, y) (by simp),
  rw finsupp.sum,
  apply finset.sum_le_sum,
  intros i hi,
  simp only [h i],
end

lemma monomial_degree_le_of_le  {σ : Type*} {m m' :  σ →₀ ℕ} (h : m' ≤ m) : 
  monomial_degree m' ≤ monomial_degree m :=
begin
  repeat {rw monomial_degree},
  exact finsupp.sum_le_sum h,
end

lemma monomial_degree_add {σ : Type*} (m m' :  σ →₀ ℕ) : 
  monomial_degree (m + m') = monomial_degree m + monomial_degree m' :=
begin
  repeat {rw monomial_degree},
  rw sum_add_index,
  simp,
  simp,
end

lemma monomial_degree_sub  {σ : Type*} {m m' :  σ →₀ ℕ} (h : m' ≤ m) : 
  monomial_degree (m - m') = monomial_degree m - monomial_degree m' := 
begin
  rw eq_tsub_iff_add_eq_of_le (monomial_degree_le_of_le h),
  rw ← monomial_degree_add,
  congr,
  ext,
  rw le_def at h,
  simp only [pi.add_apply, coe_tsub, coe_add, pi.sub_apply],
  rw nat.sub_add_cancel (h a),
end

-- This depends on flt-regular. Use total_degree_monomial once its merged into mathlib
lemma total_degree_monomial_eq_monomial_degree  {σ R : Type*}[comm_semiring R] {m :  σ →₀ ℕ} {a : R} (h : a ≠ 0):
total_degree (monomial m a) = monomial_degree m := by  convert total_degree_monomial m h

-- Use monomial instead of single!
lemma monomial_degree_single {σ : Type*} {j : σ} {d : ℕ}:
monomial_degree (single j d) = d :=
begin
  rw monomial_degree,
  simp,
end

lemma eq_single_of_monomial_degree_eq {σ : Type*}
(m :  σ →₀ ℕ) (i : σ) : monomial_degree m = m i  →  m = single i (m i) :=
begin
  intro h,
  rw monomial_degree at h,
  have h0 : single i (m i) ≤ m := by simp,
  have y : ∀ j ∈ m.support, m j ≤ single i (m i) j,
  { by_contra c,
    simp only [not_le, not_forall] at c,
    have x := @finset.sum_lt_sum σ ℕ _ (single i (m i)) m m.support (λ i h, h0 i) c,
    have y := sum_of_support_subset _ (finsupp.support_subset_of_le h0) (λ x y, y) (by simp),
    rw ←y at x,
    simp only [sum_single_index] at x,
    rw ←h at x,
    rw finsupp.sum at x,
    simpa using x,
  },
  have x := @finset.sum_lt_sum σ ℕ _ (single i (m i)) m m.support (λ i h, h0 i),
  ext,
  by_cases c : a ∈ m.support,
  { exact le_antisymm (y a c) (h0 a)},
  by_cases c' : i = a,
  { simp only [c', single_eq_same] },
  simp only [c', single_eq_of_ne, ne.def, not_false_iff],
  simpa using c,
end


lemma monomial_degree_le_iff_eq_single {σ : Type*}
(m :  σ →₀ ℕ) (i : σ) : monomial_degree m ≤ m i  ↔ m = single i (m i) :=
begin
  apply iff.intro,
  intro h,
  have t := le_monomial_degree m i,
  have x := le_antisymm t h,
  clear t h,
  apply eq_single_of_monomial_degree_eq m i,
  exact x.symm,
  intro h,
  rw h,
  rw monomial_degree_single,
  simp,
end

lemma monomial_degree_le_total_degree {σ R : Type*}[comm_semiring R] {m :  σ →₀ ℕ} {f  : mv_polynomial σ R} 
  (h : m ∈ f.support) : monomial_degree m ≤ total_degree f :=
begin
  rw total_degree,
  rw monomial_degree,
  apply finset.le_sup h,
end

lemma le_total_degree  {R σ : Type*} [comm_semiring R] {i: σ} {p : mv_polynomial σ R}
  {m: σ →₀ ℕ} (h_m : m ∈ p.support) : m i ≤ p.total_degree
:= (le_monomial_degree m i).trans $ monomial_degree_le_total_degree h_m

lemma coeff_zero_of_degree_greater_than_total_degree {R : Type*} [comm_semiring R] 
(t : σ →₀ ℕ) (f : mv_polynomial σ R) :
monomial_degree t > total_degree f → coeff t f = 0 :=
begin
  intro h,
  by_cases c: t ∈ f.support,
  { exfalso,
    simpa using lt_of_le_of_lt (monomial_degree_le_total_degree c) h },
  simp only [not_not, mem_support_iff] at c,
  exact c,
end

def max_degree_monomial {R : Type*} [comm_semiring R] 
(t : σ →₀ ℕ) (f : mv_polynomial σ R) : Prop := 
t ∈ f.support ∧ monomial_degree t = total_degree f


-- this uses a lemma from flt-regular
lemma support_nonempty_iff {R σ: Type*} [comm_semiring R] 
{f : mv_polynomial σ R} : f.support.nonempty ↔ f ≠ 0 :=
begin
  rw iff_not_comm,
  simp only [support_eq_empty, finset.not_nonempty_iff_eq_empty], 
end

lemma exists_max_degree_monomial {R : Type*} [comm_semiring R] 
{f : mv_polynomial σ R} (h : f ≠ 0) : ∃ t, max_degree_monomial t f :=
begin
  unfold max_degree_monomial,
  rw total_degree,
  unfold monomial_degree,
  have h : f.support.nonempty := support_nonempty_iff.2 h,
  have t:= finset.exists_mem_eq_sup (f.support) h (λ (s : σ →₀ ℕ), s.sum (λ (n : σ) (e : ℕ), e)),
  cases t with m hm,
  exact ⟨m, ⟨hm.1, hm.2.symm⟩⟩,
end

lemma eq_and_eq_of_le_add_le_eq {a1 a2 b1 b2 : ℕ}
(h1: a1 ≤ b1) (h2 : a2 ≤ b2) (h : a1 + a2 = b1 + b2) : a1 = b1 ∧ a2 = b2 :=
begin
  apply and.intro,
  by_cases c : a1 < b1,
  { have x := add_lt_add_of_lt_of_le c h2,
    rw h at x,
    simpa using x },
  rw not_lt at c,
  exact le_antisymm h1 c,
  by_cases c : a2 < b2,
  { have x := add_lt_add_of_le_of_lt h1 c,
    rw h at x,
    simpa using x },
  rw not_lt at c,
  exact le_antisymm h2 c,
end

lemma max_degree_monomial_mul {σ R : Type*}[comm_ring R][is_domain R] {f g : mv_polynomial σ R}{m : σ →₀ ℕ} 
(hf : f ≠ 0)(hg : g ≠ 0)
(h : max_degree_monomial m (f * g)) :
  ∃ mf mg, max_degree_monomial mf f ∧ max_degree_monomial mg g ∧ mf + mg = m := 
begin
  rw max_degree_monomial at h,
  cases support_mul'' h.1 with mf mgh,
  cases mgh with mg h',
  use mf, 
  use mg,
  have h_m_in_sup_fg := h.1,
  have h_deg_m := h.2,
  clear h,
  have h_mf_in_sup_f := h'.1,
  have h_mg_in_sup_g := h'.2.1,
  have h_mf_add_mg_eq_m := h'.2.2,
  clear h',
  have x := total_degree_mul' hf hg,
  rw ← h_deg_m at x,
  rw ← h_mf_add_mg_eq_m at x,
  rw monomial_degree_add at x,
  have xf := monomial_degree_le_total_degree h_mf_in_sup_f,
  have xg := monomial_degree_le_total_degree h_mg_in_sup_g,
  have x' := eq_and_eq_of_le_add_le_eq xf xg x,
  exact ⟨ ⟨ h_mf_in_sup_f, x'.1 ⟩ , ⟨ h_mg_in_sup_g, x'.2 ⟩, h_mf_add_mg_eq_m ⟩,
end

def dominant_monomial {R : Type*} [comm_semiring R] 
(t : σ →₀ ℕ) (f : mv_polynomial σ R) : Prop := 
  max_degree_monomial t f ∧ (∀ t' : σ →₀ ℕ, max_degree_monomial t' f → t' = t)

lemma dominant_monomial_of_factor_is_factor_of_max_degree_monomial
  {R : Type*} [comm_ring R] [is_domain R] (S : finset R) (t t' : σ →₀ ℕ ) 
  (f g : mv_polynomial σ R) (hfg : max_degree_monomial t (f*g))
  (hf : f ≠ 0) (hg : dominant_monomial t' g) : t' ≤ t :=
begin
  by_cases c : g = 0,
  rw c at hg,
  rw dominant_monomial at hg,
  rw max_degree_monomial at hg,
  simpa using hg.1.1,
  cases max_degree_monomial_mul hf c hfg with mf mgh,
  cases mgh with mg h,
  rw dominant_monomial at hg,
  rw ← hg.2 mg h.2.1,
  rw ← h.2.2,
  simp,
end

end mv_polynomial