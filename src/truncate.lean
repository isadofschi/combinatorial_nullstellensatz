import algebra.algebra.basic

universes u v

variables {α : Type v}

open_locale big_operators

namespace finset

def truncate {s : finset α} {n : ℕ } (h : n ≤ s.card ) : finset α :=  sorry

lemma card_truncate {s : finset α} {n : ℕ } (h : n ≤ s.card ) : (truncate h).card = n :=
begin
  sorry,
end

lemma truncate_sub {s : finset α} {n : ℕ } (h : n ≤ s.card) : (truncate h) ⊆ s :=
begin
  sorry
end
  
end finset