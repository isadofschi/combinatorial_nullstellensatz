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

variables {R : Type*} {σ : Type*} 

/- 
  
  New definitions: monomial_degree, max_degree_monomial, dominant_monomial

-/

-- this def is also given in flt-regular
def monomial_degree {s : Type*} (t : s →₀ ℕ) : ℕ := t.sum (λ _ e, e)

lemma nat.term_le_sum {s : finset α } (f : α → ℕ){j : α} (hj : j ∈ s) : f j ≤ s.sum f :=
begin
  revert j,
  apply finset.cons_induction_on s,
  { simp },
  { clear s,
    intros x s hx hj j hc,
    rw finset.sum_cons,
    simp only [finset.mem_cons] at hc,
    cases hc with j_eq_x j_in_s,
    { simp [j_eq_x] },
    { simp [(hj j_in_s).trans] } },
end

lemma le_monomial_degree {s : Type*} (t : s →₀ ℕ) (j : s) : t j ≤ monomial_degree t :=
begin
  by_cases c : j ∈ t.support,
  { exact nat.term_le_sum _ c },
  { simp only [not_not, finsupp.mem_support_iff] at c,
    simp [c] },
end

-- this holds for [ordered_add_comm_monoid N] if 0 ≤ n forall n ∈ N 
lemma finsupp.support_subset_of_le {s : Type*} {f g : s →₀ ℕ} (h : f ≤ g) :
f.support ⊆ g.support := 
begin
  simp only [has_subset.subset, finsupp.mem_support_iff, ne.def],
  intros a ha,
  by_contra c,
  simpa [c] using lt_of_lt_of_le (nat.pos_of_ne_zero ha) (h a),
end

-- this holds for [ordered_add_comm_monoid N] (with a different proof)
lemma finsupp.sum_le_sum {s : Type*} {f g : s →₀ ℕ} (h : f ≤ g) :
f.sum (λ x y , y) ≤ g.sum (λ x y , y) :=
begin
  rw [sum_of_support_subset f (finsupp.support_subset_of_le h) (λ x y, y) (by simp), finsupp.sum],
  apply finset.sum_le_sum,
  intros i hi,
  simp only [h i],
end

lemma monomial_degree_le_of_le {σ : Type*} {m m' : σ →₀ ℕ} (h : m' ≤ m) : 
  monomial_degree m' ≤ monomial_degree m :=
by simpa [monomial_degree] using finsupp.sum_le_sum h

lemma monomial_degree_add {σ : Type*} (m m' : σ →₀ ℕ) : 
  monomial_degree (m + m') = monomial_degree m + monomial_degree m' :=
by simp [monomial_degree, sum_add_index]

lemma monomial_degree_sub {σ : Type*} {m m' : σ →₀ ℕ} (h : m' ≤ m) : 
  monomial_degree (m - m') = monomial_degree m - monomial_degree m' := 
begin
  rw [eq_tsub_iff_add_eq_of_le (monomial_degree_le_of_le h), ← monomial_degree_add],
  congr,
  ext a,
  rw le_def at h,
  simp only [pi.add_apply, coe_tsub, coe_add, pi.sub_apply, nat.sub_add_cancel (h a)],
end

-- is this on mathlib? name?
lemma sub_le_etc {a b c : ℕ } (h : a - b ≤ c) : a ≤ c + b :=
begin
  apply nat.le_of_sub_eq_zero,
  rw [add_comm, ←nat.sub_sub],
  exact nat.sub_eq_zero_of_le h,
end

lemma monomial_degree_sub_le {σ : Type*} (m m' : σ →₀ ℕ) : 
  monomial_degree m - monomial_degree m' ≤ monomial_degree (m - m') := 
begin
  have h : m ≤ (m - m') + m',
  { intro i,
    simp only [pi.add_apply, coe_tsub, coe_add, pi.sub_apply],
    apply sub_le_etc,
    refl },
  have h' := monomial_degree_le_of_le h,
  rw monomial_degree_add at h',
  simp only [tsub_le_iff_right],
  exact h',
end


lemma monomial_degree_zero_iff {σ : Type*} {m : σ →₀ ℕ} : monomial_degree m = 0 ↔ m = 0 :=
begin
  split,
  { intro h,
    ext i,
    apply nat.eq_zero_of_le_zero _,
    apply (le_monomial_degree m i).trans,
    rw h, },
  { intro h,
    simp [h, monomial_degree], },
end

-- This depends on flt-regular. Use total_degree_monomial once its merged into mathlib
lemma total_degree_monomial_eq_monomial_degree {σ R : Type*} [comm_semiring R] {m : σ →₀ ℕ} {a : R} 
  (h : a ≠ 0): total_degree (monomial m a) = monomial_degree m :=
by convert total_degree_monomial m h

-- Use monomial instead of single!
lemma monomial_degree_single {σ : Type*} {j : σ} {d : ℕ} : monomial_degree (single j d) = d :=
by simp [monomial_degree]

lemma eq_single_of_monomial_degree_eq {σ : Type*}
(m :  σ →₀ ℕ) (i : σ) : monomial_degree m = m i → m = single i (m i) :=
begin
  intro h,
  rw monomial_degree at h,
  have h0 : single i (m i) ≤ m := by simp,
  suffices y : ∀ j ∈ m.support, m j ≤ single i (m i) j,
  { ext,
    by_cases c : a ∈ m.support,
    { exact le_antisymm (y a c) (h0 a) },
    { by_cases c' : i = a,
      { simp only [c', single_eq_same] },
      { simpa [c', single_eq_of_ne, ne.def, not_false_iff] using c, } } },
  by_contra c,
  simp only [not_le, not_forall] at c,
  suffices x : m.sum (λ (_x : σ) (e : ℕ), e) < m.support.sum ⇑m,
  by simpa [finsupp.sum] using x,
  simpa only [h, ←sum_of_support_subset _ (finsupp.support_subset_of_le h0) (λ x y, y) (by simp),
              sum_single_index] 
    using @finset.sum_lt_sum σ ℕ _ (single i (m i)) m m.support (λ i h, h0 i) c,
end

lemma monomial_degree_le_iff_eq_single {σ : Type*}
  (m :  σ →₀ ℕ) (i : σ) : monomial_degree m ≤ m i ↔ m = single i (m i) :=
begin
  apply iff.intro,
  { intro h,
    exact eq_single_of_monomial_degree_eq m i (le_antisymm (le_monomial_degree m i) h).symm },
  { intro h,
    rw h,
    simp [monomial_degree_single] },
end

lemma monomial_degree_le_total_degree {σ R : Type*}[comm_semiring R] {m : σ →₀ ℕ} {f : mv_polynomial σ R} 
  (h : m ∈ f.support) : monomial_degree m ≤ total_degree f :=
by simp [total_degree, monomial_degree, finset.le_sup h]

lemma le_total_degree {R σ : Type*} [comm_semiring R] {i: σ} {p : mv_polynomial σ R}
  {m: σ →₀ ℕ} (h_m : m ∈ p.support) : m i ≤ p.total_degree
:= (le_monomial_degree m i).trans $ monomial_degree_le_total_degree h_m

lemma coeff_zero_of_degree_greater_than_total_degree {R : Type*} [comm_semiring R]  (t : σ →₀ ℕ) 
  (f : mv_polynomial σ R) : monomial_degree t > total_degree f → coeff t f = 0 :=
begin
  intro h,
  by_cases c: t ∈ f.support,
  { exfalso,
    simpa using lt_of_le_of_lt (monomial_degree_le_total_degree c) h },
  { simp only [not_not, mem_support_iff] at c,
    exact c },
end

def max_degree_monomial {R : Type*} [comm_semiring R] (t : σ →₀ ℕ) (f : mv_polynomial σ R) : Prop
:= t ∈ f.support ∧ monomial_degree t = total_degree f

-- this uses a lemma from flt-regular
lemma support_nonempty_iff {R σ: Type*} [comm_semiring R]  {f : mv_polynomial σ R} :
  f.support.nonempty ↔ f ≠ 0 :=
begin
  rw iff_not_comm,
  simp only [support_eq_empty, finset.not_nonempty_iff_eq_empty], 
end

lemma exists_max_degree_monomial {R : Type*} [comm_semiring R] 
  {f : mv_polynomial σ R} (h : f ≠ 0) : ∃ t, max_degree_monomial t f :=
begin
  simp only [max_degree_monomial, total_degree, monomial_degree],
  cases finset.exists_mem_eq_sup (f.support) (support_nonempty_iff.2 h)
    (λ (s : σ →₀ ℕ), s.sum (λ (n : σ) (e : ℕ), e)) with m hm,
  exact ⟨m, ⟨hm.1, hm.2.symm⟩⟩,
end

lemma eq_and_eq_of_le_add_le_eq {a1 a2 b1 b2 : ℕ} (h1: a1 ≤ b1) (h2 : a2 ≤ b2)
  (h : a1 + a2 = b1 + b2) : a1 = b1 ∧ a2 = b2 :=
begin
  apply and.intro,
  { by_cases c : a1 < b1,
    { simpa [h] using add_lt_add_of_lt_of_le c h2 },
    { exact le_antisymm h1 (not_lt.1 c) } },
  { by_cases c : a2 < b2,
    { simpa [h] using add_lt_add_of_le_of_lt h1 c },
    { exact le_antisymm h2 (not_lt.1 c) } },
end

lemma max_degree_monomial_mul {σ R : Type*}[comm_ring R][is_domain R] {f g : mv_polynomial σ R}
  {m : σ →₀ ℕ} (hf : f ≠ 0) (hg : g ≠ 0) (h : max_degree_monomial m (f * g)) :
  ∃ mf mg, max_degree_monomial mf f ∧ max_degree_monomial mg g ∧ mf + mg = m := 
begin
  rw max_degree_monomial at h,
  cases support_mul'' h.1 with mf mgh,
  cases mgh with mg h',
  use mf, 
  use mg,
  suffices x : monomial_degree mf = f.total_degree ∧ monomial_degree mg = g.total_degree,
  { exact ⟨ ⟨h'.1, x.1⟩ , ⟨h'.2.1, x.2⟩, h'.2.2 ⟩, },
  apply eq_and_eq_of_le_add_le_eq (monomial_degree_le_total_degree h'.1)
    (monomial_degree_le_total_degree h'.2.1),
  simpa [ h.2, h'.2.2, ←monomial_degree_add] using total_degree_mul' hf hg,
end

def dominant_monomial {R : Type*} [comm_semiring R]  (t : σ →₀ ℕ) (f : mv_polynomial σ R) : Prop :=
max_degree_monomial t f ∧ (∀ t' : σ →₀ ℕ, max_degree_monomial t' f → t' = t)

lemma dominant_monomial_of_factor_is_factor_of_max_degree_monomial
  {R : Type*} [comm_ring R] [is_domain R] (S : finset R) (t t' : σ →₀ ℕ ) 
  (f g : mv_polynomial σ R) (hfg : max_degree_monomial t (f*g))
  (hf : f ≠ 0) (hg : dominant_monomial t' g) : t' ≤ t :=
begin
  by_cases c : g = 0,
  { rw [c, dominant_monomial, max_degree_monomial] at hg,
    simpa using hg.1.1 },
  { cases max_degree_monomial_mul hf c hfg with mf mgh,
    cases mgh with mg h,
    rw dominant_monomial at hg,
    simp [←hg.2 mg h.2.1, ← h.2.2] },
end

end mv_polynomial