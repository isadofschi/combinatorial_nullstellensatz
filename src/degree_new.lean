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

-- near total_degree_eq
lemma total_degree_eq' {R σ : Type*} [comm_semiring R] (p : mv_polynomial σ R) :
  p.total_degree = p.support.sup (monomial_degree) :=
begin
  rw [total_degree],
  congr, funext m,
end

lemma total_degree_lt_iff {R σ : Type*} [comm_semiring R] {f : mv_polynomial σ R} {d : ℕ} (h : 0 < d) :
  total_degree f < d ↔ ∀ m : σ →₀ ℕ, m ∈ f.support → monomial_degree m < d :=
by rwa [total_degree_eq', finset.sup_lt_iff]

lemma total_degree_sub_lt {R σ : Type*} [comm_ring R] [is_domain R] 
{f g : mv_polynomial σ R} {k : ℕ} (h : 0 < k)
  (hf : ∀ (m : σ →₀ ℕ), m ∈ f.support → (k ≤ monomial_degree m) → coeff m f = coeff m g)
  (hg : ∀ (m : σ →₀ ℕ), m ∈ g.support → (k ≤ monomial_degree m) → coeff m f = coeff m g) :
  total_degree (f - g) < k :=
begin
  rw total_degree_lt_iff h,
  intros m hm,
  by_contra hc,
  simp only [not_lt] at hc,
  have h' := support_sub σ f g hm,
  simp only [mem_support_iff, ne.def, coeff_sub, sub_eq_zero] at hm,
  simp [mem_union] at h',
  cases h' with cf cg,
  { exact hm (hf m (by simpa using cf) hc) },
  { exact hm (hg m (by simpa using cg) hc) }
end

lemma max_degree_monomial_iff_of_eq_degree' {R σ : Type*} [comm_semiring R] (p : mv_polynomial σ R)
 {m m' : σ →₀ ℕ} (hm' : m' ∈ p.support) (h : monomial_degree m = monomial_degree m' ) : 
 max_degree_monomial m p → max_degree_monomial m' p :=
begin
  intro h',
  split,
  { exact hm' },
  { rw ← h,
    exact h'.2 }
 end

lemma max_degree_monomial_iff_of_eq_degree {R σ : Type*} [comm_semiring R] (p : mv_polynomial σ R)
 {m m' : σ →₀ ℕ} (hm : m ∈ p.support) (hm' : m' ∈ p.support) (h : monomial_degree m = monomial_degree m') : 
 max_degree_monomial m p ↔ max_degree_monomial m' p :=
begin
  split,
  { apply max_degree_monomial_iff_of_eq_degree',
    { exact hm' },
    { exact h } },
  { apply max_degree_monomial_iff_of_eq_degree',
    { exact hm },
    { exact h.symm } }
 end


lemma max_degree_monomial_iff {R σ : Type*} [comm_ring R]
{f : mv_polynomial σ R} { m : σ →₀ ℕ} :
max_degree_monomial m f ↔ m ∈ f.support ∧ ∀ m' ∈ f.support, 
  monomial_degree m' ≤ monomial_degree m :=
begin
  split,
  { intro h,
    split,
    { exact h.1 },
    { intros m' hm',
      have t := h.2,
      rw total_degree_eq' at t,
      rw t,
      apply finset.le_sup hm' } },
  { intro h,
    split,
    { exact h.1 },
    { rw total_degree_eq',
      rw ← finset.sup'_eq_sup,
      { apply le_antisymm,
        { apply finset.le_sup',
          exact h.1 },
        { apply finset.sup'_le,
          exact h.2 } } } },
end

lemma dominant_monomial_iff {R σ : Type*} [comm_ring R]  {f : mv_polynomial σ R} { m : σ →₀ ℕ} :
  dominant_monomial m f → ∀ m' ∈ f.support, monomial_degree m' ≤ monomial_degree m 
    ∧ (monomial_degree m' = monomial_degree m → m' = m) :=
begin
  intros h m' hm',
  split,
  { apply (max_degree_monomial_iff.1 h.1).2,
    exact hm' },
  { intro h1,
    apply h.2,
    rw max_degree_monomial_iff_of_eq_degree f hm' h.1.1 h1,
    exact h.1}
end

lemma induction_on_total_degree {R σ : Type*} [comm_semiring R] {M : mv_polynomial σ R → Prop}
 (p : mv_polynomial σ R) (h : ∀ (p' : mv_polynomial σ R),
   (∀ q,  total_degree q < total_degree p' → M q) → M p') : M p :=
begin
  let P : ℕ → Prop := λ n, ∀ p : mv_polynomial σ R, total_degree p ≤ n → M p,
  suffices l' : ∀ n, P n,
  { apply l' (total_degree p),
    refl },
  { intro n,
    induction n with d hd,
    { intros p hp,
      apply h p,
      intros q hq,
      simpa using lt_of_lt_of_le hq hp },
    { intros p hp,
      apply h p,
      intros q hq,
      exact hd q (nat.le_of_lt_succ (lt_of_lt_of_le hq hp)) } },
end

local attribute [instance] classical.prop_decidable

lemma induction_on_new {R σ : Type*} [comm_semiring R] {M : mv_polynomial σ R → Prop} (p : mv_polynomial σ R)
  (h_add_weak : ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R),
    a ∉ f.support → b ≠ 0 → M f → M (monomial a b) → M (monomial a b + f))
  (h_monomial : ∀ m : σ →₀ ℕ, ∀ b : R,
    (∀ p : mv_polynomial σ R, total_degree p < monomial_degree m → M p) → M (monomial m b)) 
  : M p :=
  begin
    apply induction_on_total_degree,
    { intros p,
      apply induction_on''' p,
      { intros a h,
        apply h_monomial,
        intros x h2,
        simpa [monomial_degree] using h2 },
      { intros a b f ha hb hMf h,
        apply h_add_weak a b f ha hb (hMf _),
        { apply h_monomial,
          intros p' hp',
          suffices h' : p'.total_degree < (monomial a b).total_degree,
          { apply (h p') ∘ (lt_of_lt_of_le h'),
            rw total_degree_add_eq_of_disjoint_support,
            { simp only [le_refl, true_or, le_max_iff] },
            { simpa only [ support_monomial, hb, not_not, mem_support_iff, if_false, 
                          finset.disjoint_singleton_left, not_not, finsupp.mem_support_iff]
                using ha} },
          rw total_degree_monomial_eq_monomial_degree,
          { exact hp' },
          { exact hb } },
        { intros q hq,
          apply (h q) ∘ (lt_of_lt_of_le hq),
          rw total_degree_add_eq_of_disjoint_support,
          { simp only [le_refl, or_true, le_max_iff] },
          { simpa only [support_monomial, hb, not_not, mem_support_iff, if_false, 
                        finset.disjoint_singleton_left, not_not, finsupp.mem_support_iff] 
             using ha} } } },
  end
  
def is_reduced {R σ : Type*} [comm_ring R] (f : mv_polynomial σ R) (m : σ →₀ ℕ) : Prop
:= ∀ m' ∈ f.support, ¬ m ≤ m' -- would ∀ m', m≤ m' → m ∉ f.support be better?

lemma is_reduced_add {R σ : Type*} [comm_ring R] {f g: mv_polynomial σ R} {m : σ →₀ ℕ}
  (hf : is_reduced f m) (hg : is_reduced g m) : is_reduced (f + g) m :=
begin
  rw is_reduced,
  intros m' hm',
  have t:= (support_add hm'),
  simp only [finset.mem_union] at t,
  cases t,
  { exact hf m' t },
  { exact hg m' t }
end

end mv_polynomial