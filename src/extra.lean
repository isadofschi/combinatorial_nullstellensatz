import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

/-
  What is the right way to do this?

  maybe all of this is done in `comm_ring.lean`!


def sub [comm_ring R] : mv_polynomial σ R → mv_polynomial σ R→ mv_polynomial σ R :=
  λ f g, f + C(-1:R) * g

instance [comm_ring R] : has_sub (mv_polynomial σ R) :=  ⟨sub⟩

lemma sub_def [comm_ring R] (f g : mv_polynomial σ R) : f - g =  f + C(-1:R) * g :=
begin
    refl,
end

@[simp] lemma sub_eq_iff_eq_add [comm_ring R] (p q r : mv_polynomial σ R) :
  p - q = r ↔ p = r + q :=
begin
  apply iff.intro,
  intro h,
  rw sub_def at h,
  sorry,
  intro h,
  rw sub_def,
  sorry,
end
-/
/-
@[simp] lemma sub_eq_zero_iff_eq [comm_ring R] (p q : mv_polynomial σ R) : p - q = 0 ↔ p = q :=
begin
  exact sub_eq_zero,
end
-/
/-
variables {f : σ → R}

lemma eval_sub [comm_ring R] : 
∀ p q : (mv_polynomial σ R), eval f (p - q) = (eval f p) - (eval f q) :=
begin
  intros p q,
  rw sub_def,
  simp [sub_eq_add_neg],
end
-/
end mv_polynomial