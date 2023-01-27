/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. (this might not be done yet)
Author: Maxwell Thum.
-/
import data.finset.powerset
--import data.set.finite
--import data.set.default

/-!
A *(finite) abstract simplicial complex* `K` is a pair `(V, S)`, where 
`V` is a finite set, 
`S ⊆ 𝒫(V)` is a set of subsets of `V`, 
every `σ ∈ S` is finite, 
and for all `σ ∈ S`, 
`σ' ⊆ σ` implies `σ' ∈ S`. 
`V` is called the set of *vertices* and elements of `S` are called *simplices*.
-/

universes u v

variables (A : Type*)

/-- Based off of `analysis.convex.simplicial_complex.basic` and 
`https://ncatlab.org/nlab/show/simplicial+complex`. -/
--@[ext]
class abstract_simplicial_complex := -- making this a class again?
--(vertices : set A) -- maybe we don't start with the vertices, we start with the simplices and let vertices be 0-simplices
(simplices : set (finset A))
--(simpl_subset_𝒫vert : ∀ σ ∈ simplices, ↑σ ⊆ vertices)
(not_empty_mem : ∅ ∉ simplices)
(down_closed : ∀ σ ∈ simplices, ∀ τ ⊆ σ, τ ≠ ∅ → τ ∈ simplices)
--(vert_subset_simpl : ∀ v ∈ vertices, { v } ∈ simplices)

namespace abstract_simplicial_complex

instance example_1 : abstract_simplicial_complex ℕ :=
{ simplices := { {1}, {2}, {1, 2}, {3}},
  not_empty_mem := dec_trivial,
  down_closed := by simp ; dec_trivial,
}

/- Getting some error about class instance depth
instance example_2 : abstract_simplicial_complex ℕ :=
{ simplices := {{1}, {2}, {3}, {4}, {5}, {1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {1,2,3}, {1,2,4}, {4,5}},
  not_empty_mem := dec_trivial,
  down_closed := by simp ; dec_trivial,
}
-/

def p_simplices {A : Type*} (K : abstract_simplicial_complex A) (p : ℕ) := 
  { σ ∈ K.simplices | finset.card σ = p+1 }

def vertices (K : abstract_simplicial_complex A) := p_simplices K 0

end abstract_simplicial_complex