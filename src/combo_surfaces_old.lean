import tactic.suggest
import tactic.linarith

import data.set
--import data.nat.basic

open set
--open nat

--variable {U : Type}
--variables A B C : set U
--variable x : U

variable A : Type*

--universes u
--variables {α : Type u} {A B C : set α}

--inductive asc (K : set (finset A)) : Type


def abstr_simpl_complex_old {A : Type*} (K : set (finset A)) := 
  ∀ σ ∈ K, ∀ τ ⊆ σ, τ ∈ K

example (K : set (finset ℕ)) (hK : K = { ∅, {1}, {2}, {1, 2}, {3}}) : abstr_simpl_complex K :=
begin
  intros σ hσ τ hτ,
  rw hK at hσ,
  simp at hσ,
  rw hK,
  simp,
  obtain rfl|rfl|rfl|rfl|rfl := hσ,
  { rw finset.subset_empty at hτ,
    exact or.inl hτ, },
  { rw finset.subset_singleton_iff at hτ,
    cases hτ,
    { exact or.inl hτ, },
    right,
    exact or.inl hτ, },
  { rw finset.subset_singleton_iff at hτ,
    cases hτ,
    { exact or.inl hτ, },
    right,
    right,
    exact or.inl hτ, },
  { rw ← finset.mem_powerset at hτ,
    have h : {1,2}.powerset = {∅, {1}, {2}, {1,2}},
    { library_search },
    --rw finset.subset_doubleton_iff at hτ, 
    },
  rw finset.subset_singleton_iff at hτ,
  cases hτ,
  { exact or.inl hτ, },
  repeat {right},
  exact hτ,
  --rw mem_singleton_iff at hσ,
end

example (B : set A) (C : set A) : B ⊆ C ↔ B ∈ 𝒫 C :=
begin
  exact (mem_powerset_iff B C).symm,
end

def abstr_simplex_old {A : Type*} (k : ℕ) (σ : finset A) (K : set (finset A)) {hK : abstr_simpl_complex K} :=
  σ ∈ K ∧ (finset.card σ = k)


--def abstr_simpl_complex {A : Type*} (K : set (set A)) := 
--  ∀ (σ : set A), (σ ∈ K) → (finite σ) ∧ (∀ (τ : set A), (τ ⊆ σ) → τ ∈ K)

--def ASC : set(finset A) → Prop := abstr_simpl_complex