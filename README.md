# Lean formalization of the Combinatorial Nullstellensatz

```
theorem combinatorial_nullstellensatz { n : ℕ } {F : Type u} [field F]
  (f : mv_polynomial (fin n) F) (t : fin n →₀ ℕ) (h_max : max_degree_monomial t f)
  (S : fin n → finset F) (h_card_S : ∀ i : fin n, t i < (S i).card) :
  ∃ s : fin n → F, (∀ i : fin n, s i ∈ S i ) ∧ eval s f ≠ 0 :=
```

We follow Alon's original paper which is available at http://www.math.tau.ac.il/~nogaa/PDFS/null2.pdf
