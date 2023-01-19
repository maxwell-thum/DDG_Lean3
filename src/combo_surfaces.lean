/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. (this might not be done yet)
Author: Maxwell Thum.
-/
import data.finset.powerset

/-!
A *(finite) abstract simplicial complex* is a pair `(V, K)`, where 
`V` is a finite set, 
`K ⊆ 𝒫(V)` is a set of subsets of `V`, 
every `σ ∈ K` is finite, 
and for all `σ ∈ K`, 
`σ' ⊆ σ` implies `σ' ∈ K`. 
`V` is called the set of *vertices* and elements of `K` are called *simplices*.
-/

variables {A : Type*} (K : Type*) 

namespace abstract_simplicial_complex

def fin_abstr_simpl_complex {A : Type*} (K : finset (finset A)) :=
  ∀ σ ∈ K, ∀ τ ⊆ σ, τ ∈ K

/-- Based off of `analysis.convex.simplicial_complex.basic`. -/
class abstract_simplicial_complex {A : Type*} (K : Type*) :=
(vertices : set A)
(simplices : set (finset vertices))
(not_empty_mem : ∅ ∉ simplices)
(down_closed : ∀ σ ∈ simplices, ∀ τ ⊆ σ, τ ≠ ∅ → τ ∈ simplices)

example (K : finset (finset ℕ)) (hK : K = { ∅, {1}, {2}, {1, 2}, {3}}) : fin_abstr_simpl_complex K :=
by { rw [hK, fin_abstr_simpl_complex], dec_trivial }

example (K : finset (finset ℕ)) (hK : K = { ∅, {1}, {2}, {3}, {4}, {5}, {1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {1,2,3}, {1,2,4}, {4,5}}) : fin_abstr_simpl_complex K :=
by { rw [hK, fin_abstr_simpl_complex], dec_trivial }

def fin_abstr_simplex {A : Type*} (k : ℕ) (σ : finset A) (K : finset (finset A)) {hK : fin_abstr_simpl_complex K} :=
  σ ∈ K ∧ (finset.card σ = k)

end abstract_simplicial_complex