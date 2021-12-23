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
  { simp },
  { clear s,
    intros j' s h' h h'',
    rw finset.sum_cons,
    rw finset.mem_cons at h'',
    cases h'' with j_eq_j' j_in_s,
    { suffices h: s.sum ⇑(single j' a) = 0,
      by simp [j_eq_j', h],
      rw @finset.sum_congr _ _ s s (λ x, single j' a x) (λ x, 0) _ (by refl) _,
      simp,
      intros x hx,
      suffices j'_ne_x : j' ≠ x,
      by simp [j'_ne_x],
      by_contra c,
      rw c at h',
      exact (and_not_self_iff _).1 ⟨hx, h'⟩ },
  { suffices j_ne_j' : j ≠ j',
    by simp [h j_in_s, j_ne_j'],
    by_contra c,
    rw c at j_in_s,
    exact (and_not_self_iff _).1 ⟨j_in_s, h'⟩ } },
end

lemma sum_single' {M σ : Type*} [semiring M] [fintype σ] (j : σ) (a : M) :
  ∑ ( x : σ) , single j a x  = a := by simp only [sum_single'', finset.mem_univ]


end finsupp
