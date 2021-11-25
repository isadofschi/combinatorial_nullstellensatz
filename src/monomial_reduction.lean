/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ivan Sadofschi Costa.
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import algebra.algebra.basic
import degree
import assorted_lemmas


/-
# Reduce degree

## Main results

- `reduce_degree`: corresponds to the following paragraph in the proof of Theorem 1.1 in Alon's
"Combinatorial Nullstellensatz" paper:
'Let \bar{f} be the polynomial obtained by writing f as a linear combination of monomials and replacing,
repeatedly, each occurrence of x ^ f_i (for 1 ≤ i ≤ n), where f_i > t_i, by a linear combination 
of smaller powers of x_i, using the relations g_i = ∏ s in (S i), (X i - C s) = 0. The resulting
polynomial \bar{f} is clearly of degree at most t_i in x_i, for each 1 ≤ i ≤ n, and is obtained from
f by subtracting from it products of the form h_i * g_i, where the degree of each polynomial 
h_i ∈ F[x_1 , ... , x_n] does not exceed deg(f) − deg(g_i)'.

-/

universe u

open set function finsupp add_monoid_algebra

open_locale big_operators

namespace mv_polynomial
open set function finsupp add_monoid_algebra





lemma eee { n : ℕ } {F : Type u} [field F] 
(j : fin n) (f : mv_polynomial (fin n) F) (d : ℕ):
f.support.sup (λ m , m j) = degree_of j f :=
begin
  sorry
end

/- casi como finset.sup_le_iff pero es con < en vez de ≤ -/
lemma aux { a : Type u } (s : finset a) (f : a → ℕ) (d : ℕ) :
(∀ x, x ∈ s → f x < d ) ↔ s.sup f < d :=
begin
  sorry
end

lemma eee' { n : ℕ } {F : Type u} [field F] 
(j : fin n) (f : mv_polynomial (fin n) F) (d : ℕ):
(∀ m : fin n →₀ ℕ, m ∈ f.support → m j < d)
↔ degree_of j f < d :=
begin
  rw ← eee j f d,
  rw aux,
end








/-
  M' is a workaround for a "cannot sinthetize placeholder context error". How should I do this?
-/
private def M'  (n : ℕ ) (F : Type u) [field F] (S : fin n → finset F)
(hS : ∀ i : fin n, 0 < (S i).card)
: mv_polynomial (fin n) F → Prop :=
  λ f, ∃ h : fin n → mv_polynomial (fin n) F,
 (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ∀ j : fin n, degree_of j (f - (∑ i : fin n, h i * ∏ s in S i, (X i - C s))) < (S j).card

private def M { n : ℕ } {F : Type u} [field F]{S : fin n → finset F}
  {hS : ∀ i : fin n, 0 < (S i).card} 
  : mv_polynomial (fin n) F → Prop := λ f, M' n F S hS f

local attribute [instance] classical.prop_decidable --esta permitido usar esto?

private lemma h_C { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) : ∀ (a : F), M' n F S hS (C a) :=
begin
  intro a,
  rw M',
  use λ i, 0,
  apply and.intro,
  intro i,
  left,
  refl,
  intro j,
  have h: C a - ∑ (i : fin n), 0 * ∏ (s : F) in S i, (X i - C s) = C a,
  { have h1 : (λ i ,  0 * ∏ s in S i, (X i - C s)) = (λ i, 0),
    { ext,
      rw zero_mul },
    rw h1,
    simp, },
  rw h,
  rw degree_of_C,
  exact hS j,
end

private lemma h_X { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
 (hS : ∀ i : fin n, 0 < (S i).card) :  ∀ (p : mv_polynomial (fin n) F) (j : fin n), 
    M' n F S hS p → M' n F S hS (p * X j) :=
begin
  intros p j h_Mp,
  cases h_Mp with h h_h,
  by_cases c_p_eq_0 : p = 0,
  { rw [ c_p_eq_0, zero_mul ], 
    rw c_p_eq_0 at h_h,
    rw M',
    use h,
    exact h_h },
  rw M',
  let g := λ j : fin n, ∏ s in S j, (X j - C s),
  let g_j := g j,
  let p1 := p - ∑ (i : fin n), h i * g i,
  let f :=  p1 * X j ,
  let ms : finset (fin n →₀ ℕ) := f.support.filter (λ m , m j = (S j).card),
  let q : mv_polynomial (fin n) F := ∑ m in ms, monomial (m - (single j (S j).card)) (coeff m f),
  let h1 : fin n → mv_polynomial (fin n) F := λ i, if i = j then h j * X j - q else h i * X j,
  use h1,
  have comp_1 : p * X j - ∑ (i : fin n), h1 i * g i = f - q * g j,
  { sorry },
  have comp_2 : ∀ m, m ∈ ms → coeff m f = coeff m (q * g j), --unused ahora
  { sorry },
  have h_total_degree_f : total_degree f ≤ total_degree p + 1,
  { sorry }, -- use h_h
  have h_total_degree_q : total_degree q + (S j).card ≤  total_degree p + 1,
  { -- use total_degree_sum, h_total_degree_f and the fact that
    -- each monomial m in the definition of q is in the support of f.
    sorry },
  have H_g : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ (q * g j).support → ((S i).card ≤ m i) → coeff m f = coeff m (q * g j), 
    { intros i m m_in_support_q_g_j h_S,
      have exists_m'_m'' := support_mul' m m_in_support_q_g_j,
      cases exists_m'_m'' with m' h_m',
      cases h_m' with m'' h_m_m'_m'',
      have h_m'_in_supp_q := h_m_m'_m''.1,
      have h_m''_in_supp_gj := h_m_m'_m''.2.1,
      have h_m_eq_m'_add_m'' := h_m_m'_m''.2.2,
      clear h_m_m'_m'',
      have h_mi_eq_mi'_add_mi'' : m i = m' i + m'' i,
      { rw h_m_eq_m'_add_m'',
        refl },
      -- since m' ∈ q.support we can obtain:
      have m1 : fin n →₀ ℕ, sorry,
      have h_m1 : m1 ∈ ms, sorry,
      have h_m'_m1 : m' = m1 - (single j (S j).card), sorry,
      by_cases c_i_eq_j : i = j,
      { have h_m_in_ms : m ∈ ms,
        { have x : m'' j ≤ (S j).card, sorry, -- by h_m''_in_supp_gj 
          rw c_i_eq_j at h_S,
          rw c_i_eq_j at h_mi_eq_mi'_add_mi'',
          have h_m'_m1_j : m' j = m1 j - (S j).card,
          { rw h_m'_m1,
            simp only [single_eq_same, coe_tsub, pi.sub_apply] },
          have h_S' := add_le_add_left h_S (m' j),
          have m1_j : m1 j = (S j).card, sorry, -- use h_m1
          have m'_j_eq_0 : m' j = 0,
          { rw h_m'_m1_j,
            exact nat.sub_eq_zero_of_le (le_of_eq m1_j) },
          have h : m j ≤ (S j).card,
          { rw h_mi_eq_mi'_add_mi'',
            rw m'_j_eq_0,
            rw zero_add,
            exact x },
          have h' : m j = (S j).card := sorry, -- immediate from h hS'
          have h'' : m'' = single j (S j).card, sorry, -- separate lemma
          have h_m_eq_m1 : m = m1,
          { rw [h_m_eq_m'_add_m'', h_m'_m1, h''],
            ext,
            by_cases c : j = a,
            { rw ← c,
              simp,
              rw m1_j,
              simp },
            simp,
            rw single,
            rw coe_mk,
            rw if_neg c,
            simp },
          rw h_m_eq_m1,
          exact h_m1 },
        exact comp_2 m h_m_in_ms },
      -- case i ≠ j
      have h_m''_i : m'' i = 0, sorry, -- X i does not appear in g j
      have h' : m' i = m1 i, sorry, -- use c_i_eq_j
      have h'' : m1 i < (S i).card,
      { --use m1 ∈ ms,  support_mul_X and i≠ j
        sorry },
      exfalso,
      linarith,
      exact m,
    },
sorry, -- speedup para que no corra lo que sigue
  have H_f : ∀ i (m : (fin n) →₀ ℕ),
    m ∈ f.support → ((S i).card ≤ m i) → coeff m f = coeff m (q * g j),
  { intros i m h_m_in_supp_f h_S,
    have x : degree_of i p1 < (S i).card := h_h.2 i,
    have z := should_be_in_mathlib i h_m_in_supp_f,
    by_cases c_i_eq_j : i = j,
    { have h_m_in_ms : m ∈ ms,
      { have y := degree_of_mul_X_eq j p1,
        rw c_i_eq_j at x,
        rw c_i_eq_j at h_S,
        rw c_i_eq_j at z,
        have w := sandwich' h_S ( lt_of_le_of_lt (z.trans y) (add_lt_add_right x 1) ),
        simp only [exists_prop, add_right_embedding_apply, finset.mem_map, 
        finset.mem_filter, coeff_sub],
        exact ⟨h_m_in_supp_f , w.symm⟩ },
      exact comp_2 m h_m_in_ms },
    have y := degree_of_mul_X_ne  p1 c_i_eq_j,
    rw ← y at x, clear y,
    exfalso,
    linarith },
  apply and.intro,
  intro i,
  by_cases c_h1_i_eq_0 : h1 i = 0,
  { left,
    exact c_h1_i_eq_0 },
  right,
  simp only [h1],
  rw total_degree_mul_X c_p_eq_0 j,
  have useful := (add_le_add_right (total_degree_mul_X_le (h i) j) (S i).card),
  by_cases c_i_eq_j : i = j,
  { rw if_pos c_i_eq_j,
    rw c_i_eq_j,
    have x := add_le_add_right (total_degree_add (h j * X j) (-q)) (S j).card,
    rw ← sub_eq_add_neg at x,
    have y : linear_order.max (h j * X j).total_degree (-q).total_degree +  (S j).card 
      ≤ p.total_degree + 1,
    { by_cases c_comp : (h j * X j).total_degree ≤ (-q).total_degree,
      { rw [max_eq_right c_comp, total_degree_neg],
        exact h_total_degree_q },
      simp only [not_le] at c_comp,
      rw max_eq_left c_comp.le,
      rw c_i_eq_j at useful,
      by_cases c_h_j_eq_0 : h j = 0,
      { rw [c_h_j_eq_0, zero_mul] at c_comp,
        simp only [nat.not_lt_zero, total_degree_zero] at c_comp,
        exfalso,
        exact c_comp },
      have y := add_le_add_right (right_of_not_of_or c_h_j_eq_0 (h_h.1 j)) 1,
      rw [add_assoc, add_comm (S j).card 1, ← add_assoc ] at y,
      exact useful.trans y },
    exact x.trans y },
  rw if_neg c_i_eq_j,
  have h_i_neq_0 : h i ≠ 0,
  { let x := c_h1_i_eq_0,
    simp only [h1] at x,
    by_contradiction,
    rw [if_neg c_i_eq_j, h, zero_mul] at x,
    cc },
  have y := add_le_add_right (right_of_not_of_or h_i_neq_0 (h_h.1 i)) 1,
  rw [add_assoc, add_comm (S i).card 1, ← add_assoc ] at y,
  exact useful.trans y,
  intro i,
  rw comp_1,
  exact degree_of_sub_aux i f (q * g j) (S i).card (H_f i) (H_g i),
end

/-
  -- old code
  rw ← eee', -- avoiding this may simplify the rest of the proof
  intros m hm,
  by_contradiction h_m_i,
  --rw comp_1 at hm,
  have m_mem_U := finset.mem_of_mem_of_subset hm (support_sub f (q * g j)),
  clear comp_1,
  by_cases c_m_in_sup_f : m ∈ f.support,
  { have x := support_mul_X j (p - ∑ (i : fin n), h i * g i),
    have c_m_in_sup_f' := c_m_in_sup_f,
    rw x at c_m_in_sup_f,
    clear x m_mem_U,
    simp only [exists_prop, add_right_embedding_apply, finset.mem_map] at c_m_in_sup_f,
     --mem_support_iff, ne.def, coeff_sub
    cases c_m_in_sup_f with m' h_m',
    have h_coeff_m' := h_m'.1,
    have h_m_m' := h_m'.2,
    clear h_m',
    have x0 := h_h.2 i,
    rw ← eee' at x0,
    have x := x0 m' h_coeff_m',
    rw ← h_m_m' at h_m_i,
    simp only [pi.add_apply, not_lt, coe_add] at h_m_i,
    simp only [single] at h_m_i,
    simp only [coe_mk] at h_m_i,
    by_cases c_j_eq_i : j = i,
    { rw [if_pos c_j_eq_i] at h_m_i,
      let xeq := sandwich x h_m_i,
      have h_m_in_ms : m ∈ ms,
      { simp only [exists_prop, add_right_embedding_apply, finset.mem_map, finset.mem_filter ],
        apply and.intro,
        exact c_m_in_sup_f',
        rw ← h_m_m',
        simp only [single_eq_same, pi.add_apply, coe_add],
        rw c_j_eq_i,
        exact xeq.symm },
      have m_not_in_supp := comp_2 m h_m_in_ms,
      simp only [mem_support_iff, ne.def] at hm,
      tauto },
    rw [ if_neg c_j_eq_i ] at h_m_i,
    linarith },
  have m_in_support_q_g_j := right_of_not_of_or c_m_in_sup_f (finset.mem_or_mem_of_mem_union m_mem_U),
  clear m_mem_U,
  have exists_m'_m'' := support_mul' m m_in_support_q_g_j,
  cases exists_m'_m'' with m' h_m',
  cases h_m' with m'' h_m_m'_m'',
  by_cases c_i_eq_j : i = j,
  { -- por h_m_i tengo (S j).card ≤ m j
    -- por h_m_m'_m'' m j = m' j + m'' j
    -- por ser m'' monomio de g j tengo m'' j ≤ (S j).card
    -- por ser m' monomio de q tengo m' = m1 - (single j (S j).card) para algun m1 en ms
    -- luego m' j = m1 j - (S j).card = 0
    -- entonces m j = m1 j - (S j).card + m'' j = 0 + m'' j ≤ (S j).card ≤ m j
    -- luego debe valer la igualdad en m'' j ≤ (S j).card
    -- entonces m'' = single j (S j).card
    -- entonces m = m1
    -- aplico comp_2 para conseguir una contradiccion
    sorry },
  -- por h_m_i tengo (S i).card ≤ m i
  -- por h_m_m'_m'' m i = m' i + m'' i
  -- por ser i≠ j tengo m'' i = 0
  -- por ser m' monomio de q tengo m' = m1 - (single j (S j).card) para algun m1 en ms
  -- luego (usando i ≠ j) m' i = m1 i
  -- por estar m1 en ms (por support_mul_X y ser i≠ j) vale m1 i < (S i).card
  -- de todo esto deducimos m i < m i, contradiccion!
  sorry,
  exact n,
  exact m,
end
-/

private lemma h_add_weak_aux_comp { n : ℕ } {F : Type u} [field F]
(S : fin n → finset F) (p q : mv_polynomial (fin n) F) 
(h1 h2 : fin n → mv_polynomial (fin n) F) : 
p + q - (∑ (i : fin n), (h1 + h2) i * (∏ (s : F) in S i, (X i - C s)))
= (p - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s))))
+ (q - (∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s)))) :=
calc p + q - (∑ (i : fin n), (h1 + h2) i * (∏ (s : F) in S i, (X i - C s)))
     = p + q - (∑ (i : fin n), (h1 i + h2 i) * (∏ (s : F) in S i, (X i - C s))) : by simp
...  = p + q - (∑ (i : fin n),(h1 i * (∏ (s : F) in S i, (X i - C s)) + h2 i * (∏ (s : F) in S i, (X i - C s)))) :
begin
  simp only [sub_right_inj],
  congr,
  ext,
  congr,
  rw add_mul,
end
...  = p + q - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s)) + ∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s))) :
by simp only [sub_right_inj,finset.sum_add_distrib]
...  = (p - (∑ (i : fin n), h1 i * (∏ (s : F) in S i, (X i - C s))))
       + (q - (∑ (i : fin n), h2 i * (∏ (s : F) in S i, (X i - C s)))) : 
by rw [← add_sub_assoc, ← sub_sub (p+q), sub_left_inj,sub_add_eq_add_sub]


private lemma h_add_weak { n : ℕ } {F : Type u} [field F] (S : fin n → finset F)
  (hS : ∀ i : fin n, 0 < (S i).card) : 
∀ (a : fin n →₀ ℕ) (b : F) (f : mv_polynomial (fin n) F), 
    a ∉ f.support → b ≠ 0 → M' n F S hS f → M' n F S hS (single a b + f) :=
begin
  intros a b f h_a h_b h_Mf,
  cases h_Mf with h_f hh_f,
  have h_MCa := induction_on_monomial (h_C S hS) (h_X S hS) a b,
  cases h_MCa with h_Ca hhC_a,
  rw M',
  use h_Ca + h_f,
  apply and.intro,
  intro i,
  rw total_degree_add_monomial f a b h_a h_b,
  have re : ∀i,  (h_Ca + h_f) i = h_Ca i + h_f i,
  { intro i,
    simp,
  },
  rw re,
  by_cases h_Ca0 : h_Ca i = 0,
  { by_cases h_f0 : h_f i = 0,
    { left,
      rw [h_Ca0, h_f0],
      simp },
    right,
    rw h_Ca0,
    simp only [zero_add],
    have x : (h_f i).total_degree + (S i).card ≤ total_degree f,
    { have y := hh_f.1 i,
      cc },
    exact x.trans (le_max_right (total_degree (single a b)) (total_degree f)),
  },
  by_cases h_f0 : h_f i = 0,
  { right,
    rw h_f0,
    simp only [add_zero],
    have x : (h_Ca i).total_degree + (S i).card ≤ total_degree (single a b),
    { have y := hhC_a.1 i,
      have z : (h_Ca i).total_degree + (S i).card ≤ (monomial a b).total_degree := by cc,
      simpa using z },
    exact x.trans (le_max_left (total_degree (single a b)) (total_degree f)),
  },
  by_cases c : h_Ca i+ h_f i = 0,
  { left,
    exact c },
  right,
  have x := total_degree_add (h_Ca i) (h_f i),
  have y : (h_Ca i).total_degree + (S i).card ≤ total_degree (single a b) :=
    right_of_not_of_or h_Ca0 (hhC_a.1 i),
  have z : (h_f i).total_degree + (S i).card ≤ total_degree f :=
    right_of_not_of_or h_f0 (hh_f.1 i),
  have x' := add_le_add_right x (S i).card,
  rw max_add at x',
  exact x'.trans (max_le_le y z),
  intro j,
  rw [ h_add_weak_aux_comp S (single a b) f h_Ca h_f],
  exact lt_of_le_of_lt (degree_of_add_le j _ _) (max_lt (hhC_a.2 j) (hh_f.2 j)),
end

lemma reduce_degree { n : ℕ } {F : Type u} [field F]
  (S : fin n → finset F) (hS : ∀ i : fin n, 0 < (S i).card)
  (f : mv_polynomial (fin n) F) :
  ∃ h : fin n → mv_polynomial (fin n) F,
  (∀ i : fin n, h i = 0 ∨ total_degree (h i) + (S i).card ≤ total_degree f)
  ∧ ∀ j : fin n, 
  degree_of j (f - (∑ i : fin n, h i * ∏ s in S i, (X i - C s))) < (S j).card := 
begin
  have h : M f,
  { apply induction_on'' f,
    apply h_C S hS,
    apply h_add_weak S hS,
    apply h_X S hS },
  rw M at h, rw M' at h,
  exact h,
end

end mv_polynomial