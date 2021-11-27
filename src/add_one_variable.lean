import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.equiv
import data.mv_polynomial.supported
import data.polynomial.basic
import data.polynomial.ring_division
import algebra.algebra.basic

universes u v

variables {α : Type v}

open_locale big_operators

namespace mv_polynomial

/-
Natural numbers and fin
-/

lemma mod_succ_self_eq_self (n : ℕ) : n % n.succ = n :=
begin
  apply nat.mod_eq_of_lt,
  apply nat.lt_succ_self,
end

lemma coe_eq_mk {n : ℕ }(h : n < n+1): ↑n = fin.mk n h :=
begin
  apply fin.eq_of_veq,
  simp,
  exact mod_succ_self_eq_self n
end

/-
Finsets and multisets
-/

/- these would be useful to have (assuming not already on mathlib!)-/
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

lemma le_of_val_subset
{α : Type u} [decidable_eq α]
{a : finset α} {b : multiset α} (h : a.val ⊆ b) : a.val ≤ b := 
begin 
  exact le_of_subset_of_nodup h a.2,
end

/-

  init and snoc for maps fin n → R and fin n →₀ M

-/ 

local attribute [instance] classical.prop_decidable --esta permitido usar esto?

private def point.snoc {n:ℕ}{α: Type*}(s' : fin n → α)(y : α) : fin (n+1) → α := 
fin.snoc s' y

private def ext1_eq_n {n:ℕ}{α: Type*}(s' : fin n → α)(y : α) : 
point.snoc s' y n = y :=
begin
  rw point.snoc,
  rw fin.snoc,
  have h : ¬ (n: fin (n+1)).val < n,
  { simp only [fin.val_eq_coe, not_lt, fin.coe_of_nat_eq_mod],
    rw mod_succ_self_eq_self },
  simp only [ fin.coe_of_nat_eq_mod, fin.mk_eq_subtype_mk, h, fin.coe_of_nat_eq_mod, dif_neg,
              not_false_iff, cast_eq],
end

def ext1_eq_le_n {n:ℕ}{α: Type*}{i : fin(n+1)}
(s' : fin n → α)(y : α)(h : ↑i < n) : 
point.snoc s' y i = s' (fin.mk i h) :=
begin
  rw point.snoc,
  rw fin.snoc,
  simp only [fin.mk_eq_subtype_mk, cast_eq, fin.val_eq_coe, h, dif_pos ],
  congr,
end

noncomputable def fin.support
{M : Type*} [has_zero M] {n : ℕ} (f : fin n → M) : finset (fin n) :=
(finset.fin_range n).filter (λ i, f i ≠ 0)

lemma fin.mem_support_to_fun 
{M : Type*} [has_zero M] {n : ℕ} (f : fin n → M)
: ∀ a, a ∈ fin.support f ↔ f a ≠ 0 := begin
intro a,
rw fin.support,
simp,
end

noncomputable def fin.to_finsupp
{M : Type*} [has_zero M] {n:ℕ } (f : fin n → M ) : fin n →₀ M :=
⟨ fin.support f , f, fin.mem_support_to_fun f ⟩


noncomputable def resfin {n: ℕ } (s : fin (n+1) →₀ ℕ ) : fin n →₀ ℕ 
:= fin.to_finsupp (fin.init s.to_fun)

noncomputable def extfin {n:ℕ}(s' : fin n →₀  ℕ) (y : ℕ) : fin (n+1) →₀ ℕ := 
fin.to_finsupp (fin.snoc s'.to_fun y)

lemma resfin_eq {n :ℕ} (s : fin (n+1) →₀ ℕ): ∀ (i : fin n), s i = resfin s i :=
begin
  intro i,
  rw resfin,
  congr,
  simp,
end

lemma extfin_eq_le_n {n:ℕ}(i : fin n) /- unused -/
(s' : fin n →₀  ℕ)(y : ℕ) : 
extfin s' y i = s' i := 
begin 
  rw extfin,
  rw fin.to_finsupp,
  simp only [fin.coe_eq_cast_succ, fin.mk_eq_subtype_mk, fin.eta, fin.snoc_cast_succ, finsupp.coe_mk],
  rw [coe_fn, finsupp.has_coe_to_fun],
end


/-

Lemmas

-/

lemma eval_eq_eval_mv_eval' {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (y : R) (f : mv_polynomial (fin (n+1)) R) : 
 eval (point.snoc s' y  : fin (n+1) → R) f = polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv R n) f)) :=
begin
  sorry,
end

lemma coeff_eval_eq_eval_coeff {n : ℕ} {R : Type u} [comm_semiring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ):
polynomial.coeff (polynomial.map (eval s') f) i =  eval s' (polynomial.coeff f i) 
:=
begin
  simp only [polynomial.coeff_map],
end

lemma support_eval' {n : ℕ} {R : Type u} [comm_semiring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) (i : ℕ):
i ∈ (polynomial.map (eval s') f).support → i ∈ f.support :=
begin
  intro hi,
  simp only [polynomial.mem_support_iff, polynomial.coeff_map, ne.def] at hi,
  by_contradiction,
  simp only [polynomial.mem_support_iff, not_not, ne.def] at h,
  rw h at hi,
  simpa using hi,
end


lemma support_eval {n : ℕ} {R : Type u} [comm_semiring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)):
(polynomial.map (eval s') f).support ⊆ f.support :=
begin
rw finset.subset_iff,
intros x hx,
exact support_eval' s' f x hx,
end

lemma degree_eval_le_degree {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) :
polynomial.degree (polynomial.map (eval s') f) ≤ polynomial.degree f
:=
begin
  rw polynomial.degree,
  rw polynomial.degree,
  rw finset.sup_le_iff,
  intro b,
  intro hb,
  apply finset.le_sup (support_eval' s' f b hb),
end


lemma nat_degree_eval_le_nat_degree {n : ℕ} {R : Type u} [comm_ring R]
(s' : fin n → R) (f : polynomial (mv_polynomial (fin n) R)) :
polynomial.nat_degree (polynomial.map (eval s') f) ≤ polynomial.nat_degree f
:=
begin
  rw polynomial.nat_degree,
  rw polynomial.nat_degree,
  sorry,
end

lemma nat_degree_fin_suc_equiv {n : ℕ} {F : Type u} [field F]
  (f : mv_polynomial (fin (n+1)) F) : 
  (fin_succ_equiv F n f).nat_degree = degree_of ↑n f :=
begin
  sorry
end

lemma degree_of_coeff_fin_suc_equiv {n : ℕ} {F : Type u} [field F]
  (f : mv_polynomial (fin (n+1)) F) (j:fin n)(i:ℕ) : 
  degree_of j (polynomial.coeff (fin_succ_equiv F n f) i) ≤ degree_of ↑j f :=
begin
  sorry
end

lemma eq_zero_iff_every_coeff_zero {R : Type u} [comm_semiring R](p : polynomial R) :
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
  have h0 : Z.val ⊆ p.roots,
  { rw multiset.subset_iff,
    intros x hx,
    let z := hZ x hx,
    rwa polynomial.mem_roots h },
  have h1 : Z.card ≤ p.roots.card,
  { rw finset.card,
    exact multiset.card_le_of_le (le_of_val_subset h0),
  },
  exact h1.trans (polynomial.card_roots' h),
end

/- Lemma 2.1 in Alon's paper. -/
lemma lemma_2_1 { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin n) F)
  (t : fin n →₀ ℕ)
  (ht : ∀ i : fin n, degree_of i f ≤ t i)
  (S : fin n → finset F)
  (hS : ∀ i : fin n, t i < (S i).card) 
  (hz : ∀ s : fin n → F, (∀ i : fin n, s i ∈ S i ) → eval s f = 0) :
  f = 0 :=
begin
  induction n with n hn,
  simp only [forall_const] at hz,
  apply (ring_equiv.map_eq_zero_iff (is_empty_ring_equiv F (fin 0))).1,
  simp only [is_empty_ring_equiv_apply],
  --let t := ,
  simpa using (hz fin.is_empty.elim),
  apply (ring_equiv.map_eq_zero_iff ↑(fin_succ_equiv F n)).1,
  apply (eq_zero_iff_every_coeff_zero ((fin_succ_equiv F n) f)).1,
  intro i,
  apply hn (polynomial.coeff ((fin_succ_equiv F n) f) i) (resfin t),
  intro j,
  --let f_i := polynomial.coeff ((fin_succ_equiv F n) f) i,
  rw ← resfin_eq t j,
  exact (degree_of_coeff_fin_suc_equiv f j i).trans (ht j),
  intro j,
  rw ← resfin_eq t j,
  exact hS ↑j,
  intros s hs,
  rw ← coeff_eval_eq_eval_coeff,
  rw (eq_zero_iff_every_coeff_zero (polynomial.map (eval s) ((fin_succ_equiv F n) f))).2,
  -- I do not know how to prove h00 in a neat way:
  have h0 : ∀ s' : fin n → F, (∀ i : fin n, s' i ∈ S i) →
    ∀ y : F, y ∈ S n →  
    polynomial.eval y (polynomial.map (eval s') ((fin_succ_equiv F n) f)) = 0,
  {
    intros s' hs' y hy,
    rw ← eval_eq_eval_mv_eval',
    rw hz,
    intro i,
    by_cases c : ↑i < n,
    { rw (ext1_eq_le_n s' y c), 
      have x:= hs' (fin.mk i c),
      simp only [fin.coe_eq_cast_succ, fin.mk_eq_subtype_mk, fin.cast_succ_mk, fin.eta] at x,
      simp only [fin.mk_eq_subtype_mk],
      exact x,
    },
    have r : ↑n = i,
    { apply fin.eq_of_veq,
      simp,
      rw nat.eq_of_le_of_lt_succ (le_of_not_lt c) i.property,
      rw mod_succ_self_eq_self },
    rwa [ ← r, ext1_eq_n s' y ] },
  by_contradiction c,
  let t1 := number_zeroes_field c (S n) (h0 _ _),
  have u : (polynomial.map (eval s) ((fin_succ_equiv F n) f)).nat_degree ≤ t n,
  { have x := nat_degree_eval_le_nat_degree s (fin_succ_equiv F n f),
    rw nat_degree_fin_suc_equiv f at x,
    have y := ht n,
    exact x.trans y },
  simpa using lt_of_le_of_lt (t1.trans u) (hS n),
  exact hs,
end

end mv_polynomial
