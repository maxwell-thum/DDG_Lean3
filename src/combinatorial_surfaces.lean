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

variable {A : Type*}

/-- Based off of `analysis.convex.simplicial_complex.basic` and 
`https://ncatlab.org/nlab/show/simplicial+complex`. -/
--@[ext]
class abstract_simplicial_complex (A : Type*) := -- making this a class again?
--(vertices : set A) -- maybe we don't start with the vertices, we start with the simplices and let vertices be 0-simplices
(simplices : set (finset A))
--(simpl_subset_𝒫vert : ∀ σ ∈ simplices, ↑σ ⊆ vertices)
(not_empty_mem : ∅ ∉ simplices)
(down_closed : ∀ σ ∈ simplices, ∀ τ ⊆ σ, τ ≠ ∅ → τ ∈ simplices)
--(vert_subset_simpl : ∀ v ∈ vertices, { v } ∈ simplices)

namespace abstract_simplicial_complex

/- The set of `k`-simplices, the simplices with `k+1` elements. -/
def k_simplices (K : abstract_simplicial_complex A) (k : ℕ) := 
  { σ ∈ K.simplices | finset.card σ = k+1 }

/- The set of vertices, which is just another name for 0-simplices. -/
def vertices (K : abstract_simplicial_complex A) := k_simplices K 0

/- A pure (abstract) `k`-simplicial complex is such that every simplex is contained in some `k`-simplex. -/
class pure_abstract_k_simplicial_complex (A : Type*) (k : ℕ) extends abstract_simplicial_complex A :=
(pure : ∀ σ ∈ simplices, ∃ σ' ∈ k_simplices to_abstract_simplicial_complex k, σ ⊆ σ')

/- Any subset of an abstract simplicial complex, not necessarily itself an asc -/
class asc_subset (K : abstract_simplicial_complex A) :=
(simplices : set (finset A))
(subset : simplices ⊆ K.simplices)

instance asc_is_asc_subset_self (K : abstract_simplicial_complex A) : asc_subset K :=
{ simplices := K.simplices,
  subset := rfl.subset, }

-- **TODO**: Do we just want this proposition or do we want a yes/no?
/- -/
def is_subcomplex {A : Type*} {K: abstract_simplicial_complex A} (S : asc_subset K) : Prop :=
  S.simplices ⊆ K.simplices

/-- Construct an abstract simplicial complex as a subset of a given abstract simplicial complex. -/
@[simps]
def of_subcomplex {A : Type*} (K : abstract_simplicial_complex A)
  (S : asc_subset K)
  (down_closed : ∀ σ ∈ S.simplices, ∀ τ ⊆ σ, τ ∈ S.simplices) :
  abstract_simplicial_complex A :=
{ simplices := S.simplices,
  not_empty_mem := λ h, K.not_empty_mem (S.subset h),
  down_closed := λ σ hσ τ hτσ _, down_closed σ hσ τ hτσ, }

def star {A : Type*} {K : abstract_simplicial_complex A} (S : asc_subset K) : asc_subset K :=
{ simplices := { σ ∈ K.simplices | ∃ σ' ∈ S.simplices, σ' ⊆ σ },
  subset := by refine simplices.sep_subset (λ (x : finset A), ∃ (σ' : finset A) (H : σ' ∈ asc_subset.simplices K), σ' ⊆ x)}

def closure {A : Type*} {K : abstract_simplicial_complex A} (S : asc_subset K) : asc_subset K := sorry

/- The link of a subset of an asc is -/
def link {A : Type*} {K : abstract_simplicial_complex A} (S : asc_subset K) : asc_subset K := sorry


end abstract_simplicial_complex