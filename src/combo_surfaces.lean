import data.finset.powerset

def fin_abstr_simpl_complex {A : Type*} (K : finset (finset A)) :=
  ∀ σ ∈ K, ∀ τ ⊆ σ, τ ∈ K

example (K : finset (finset ℕ)) (hK : K = { ∅, {1}, {2}, {1, 2}, {3}}) : fin_abstr_simpl_complex K :=
by { rw [hK, fin_abstr_simpl_complex], dec_trivial }

example (K : finset (finset ℕ)) (hK : K = { ∅, {1}, {2}, {3}, {4}, {5}, {1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {1,2,3}, {1,2,4}, {4,5}}) : fin_abstr_simpl_complex K :=
by { rw [hK, fin_abstr_simpl_complex], dec_trivial }

def fin_abstr_simplex {A : Type*} (k : ℕ) (σ : finset A) (K : finset (finset A)) {hK : fin_abstr_simpl_complex K} :=
  σ ∈ K ∧ (finset.card σ = k)