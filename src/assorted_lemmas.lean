import data.finset.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring

namespace finsupp

open set function finsupp add_monoid_algebra
open_locale big_operators

lemma sum_single'' {M : Type*} [semiring M] {α : Type*} {s : finset α} {j : α} (h : j ∈ s)
 (a : M) : ∑ x in s , (single j a) x  = a := 
begin
  revert h,
  apply finset.cons_induction_on s,
  { simp },
  { clear s,
    intros j' s h' h h'',
    rw finset.sum_cons,
    rw finset.mem_cons at h'',
    cases h'' with j_eq_j' j_in_s,
    { suffices h: s.sum ⇑(single j' a) = 0,
      by simp [j_eq_j', h],
      suffices z : ∀ (x : α), x ∈ s → (λ x, (single j' a) x) x = (λ x, 0) x,
      { rw finset.sum_congr (by refl) z,
        simp },
      intros x hx,
      suffices j'_ne_x : j' ≠ x,
      by simp [j'_ne_x],
      by_contra c,
      rw c at h',
      exact h' hx },
    { suffices j_ne_j' : j ≠ j',
      by simp [h j_in_s, j_ne_j'],
      by_contra c,
      rw c at j_in_s,
      exact h' j_in_s } },
end

lemma sum_single' {M σ : Type*} [semiring M] [fintype σ] (j : σ) (a : M) :
  ∑ ( x : σ) , single j a x  = a := by simp only [sum_single'', finset.mem_univ]

end finsupp
