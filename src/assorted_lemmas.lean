import data.finset.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring

section ne_symm
universe u
variables {α : Type u} 
lemma not_eq_symm {a b : α } (h: ¬ (a = b)) : ¬ (b = a) := -- or "by cc",
begin
 rw ← ne,
 symmetry,
 rwa ne,
end
end ne_symm

namespace finsupp

open set function finsupp add_monoid_algebra
open_locale big_operators

lemma sum_single'' {M : Type*} [semiring M] {α : Type*} {s : finset α} {j : α} (h : j ∈ s)
 (a : M) : ∑ x in s , (single j a) x  = a := 
begin
  revert h,
  apply finset.cons_induction_on s,
  simp,
  clear s,
  intros j' s h' h h'',
  rw finset.sum_cons,
  rw finset.mem_cons at h'',
  cases h'' with j_eq_j' j_in_s,
  { have h: s.sum ⇑(single j' a) = 0,
    { rw @finset.sum_congr _ _ s s (λ x, single j' a x) (λ x, 0) _ (by refl) _,
      simp,
      intros x hx,
      have j'_ne_x : j' ≠ x,
      { by_contra c,
        rw c at h',
        cc, },
      simp [j'_ne_x] },
    simp [j_eq_j', h] },
 { have j_ne_j' : j ≠ j',
   { by_contra c,
     rw c at j_in_s,
     cc, },
  simp [h j_in_s, j_ne_j'] }
end

lemma sum_single' {M σ : Type*} [semiring M] [fintype σ] (j : σ) (a : M) :
  ∑ ( x : σ) , single j a x  = a := by simp only [sum_single'', finset.mem_univ]


end finsupp
