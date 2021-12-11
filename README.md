# A Lean formal proof of the Combinatorial Nullstellensatz

```
theorem combinatorial_nullstellensatz {R σ : Type*} [comm_ring R] [is_domain R] [fintype σ]
 [decidable_eq σ] (f : mv_polynomial σ R) (t : σ →₀ ℕ) (h_max : max_degree_monomial t f)
  (S : σ → finset R) (h_card_S : ∀ i : σ, t i < (S i).card) : ∃ s : σ → R,
    (∀ i : σ, s i ∈ S i ) ∧ eval s f ≠ 0 
```

We follow Alon's original paper which is available at http://www.math.tau.ac.il/~nogaa/PDFS/null2.pdf
