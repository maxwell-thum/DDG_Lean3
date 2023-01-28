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

/-- Based off of `analysis.convex.simplicial_complex.basic`,
`https://ncatlab.org/nlab/show/simplicial+complex`, and Keenan Crane's DDG textbook. -/
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
def is_pure_k_asc (K : abstract_simplicial_complex A) (k : ℕ) : Prop :=
  ∀ σ ∈ K.simplices, ∃ σ' ∈ K.k_simplices k, σ ⊆ σ'

/- An asc `K'` is a subcomplex of the asc `K` if all of `K'`'s simplices belong to `K`. -/
def subcomplex (K' K : abstract_simplicial_complex A) : Prop :=
  K'.simplices ⊆ K.simplices

/- Every asc is a subcomplex of itself. -/
@[simp]
lemma asc_subcomplex_self (K : abstract_simplicial_complex A) : K.subcomplex K := rfl.subset

/-- Any subset of an asc (not necessarily itself an asc) -/
class asc_subset (K : abstract_simplicial_complex A) :=
(simplices : set (finset A))
(subset : simplices ⊆ K.simplices)

namespace asc_subset

/-- Instance taking a subcomplex of an asc to a subset of that asc. -/
instance subcomplex_to_asc_subset (K' K : abstract_simplicial_complex A) (K'_subc_K : K'.subcomplex K) : 
    asc_subset K :=
{ simplices := K'.simplices,
  subset := K'_subc_K, }

/-- In particular, we can take an asc to a subset of itself. -/ -- (is this instance unnecessary?)
instance asc_to_asc_subset_self (K : abstract_simplicial_complex A) : asc_subset K :=
  asc_subset.subcomplex_to_asc_subset K K (asc_subcomplex_self K)

/-- The proposition that an `asc_subset` is closed downward
--, which is equivalent to it forming an asc / 
--subset by the previous lemma `of_subcomplex_is_subcomplex`. 
--Note: I understand that logically this feels a bit... circular. I don't have a good way  -/
def is_down_closed {K : abstract_simplicial_complex A} (S : asc_subset K) : Prop := 
  ∀ σ ∈ S.simplices, ∀ τ ⊆ σ, τ ≠ ∅ → τ ∈ S.simplices

lemma subcomplex_to_asc_subset_is_down_closed (K' K : abstract_simplicial_complex A) 
    (K'_subc_K : K'.subcomplex K) :
    (asc_subset.subcomplex_to_asc_subset K' K K'_subc_K).is_down_closed := K'.down_closed

/-- Construct an asc from a downward-closed subset of a given asc. -/
@[simps]
instance to_complex (K : abstract_simplicial_complex A)
  (S : asc_subset K)
  (down_closed : S.is_down_closed) :
  abstract_simplicial_complex A :=
{ simplices := S.simplices,
  not_empty_mem := λ h, K.not_empty_mem (S.subset h),
  down_closed := down_closed, }

/- --`to_complex` only actually gives an asc; this shows that that asc is indeed a subcomplex. 
As a consequence, if an `asc_subset` is closed downward, then it forms a subcomplex. -/
@[simp]
lemma to_complex_is_subcomplex (K : abstract_simplicial_complex A) (S : asc_subset K)
    (down_closed : is_down_closed S) : 
    (asc_subset.to_complex K S down_closed).subcomplex K := 
  S.subset

/-- The star of an `asc_subset` `S` is the set of simplices in its asc which contain a simplex in `S`. -/
def star {K : abstract_simplicial_complex A} (S : asc_subset K) : asc_subset K :=
{ simplices := { σ ∈ K.simplices | ∃ σ' ∈ S.simplices, σ' ⊆ σ },
  subset := abstract_simplicial_complex.simplices.sep_subset (λ (x : finset A), ∃ σ' ∈ simplices K, σ' ⊆ x)}

/-- Book definition: "The closure Cl(S) is the smallest (i.e., fewest elements) subcomplex of K 
that contains S." This is a rough definition in an arbitrary type `A` / possibly infinite set `K.simplices`
as it is not necessarily clear that there even *exists* such a minimal set. Perhaps we need to restrict  -/
def closure {K : abstract_simplicial_complex A} (S : asc_subset K) : asc_subset K := 
{ simplices := sorry
  subset := sorry }

@[simp]
lemma closure_is_down_closed {K : abstract_simplicial_complex A} (S : asc_subset K) :
    S.closure.is_down_closed := sorry

/- The link of a subset of an asc is -/
def link {K : abstract_simplicial_complex A} (S : asc_subset K) : asc_subset K := 
{ simplices := S.star.closure.simplices \ S.closure.star.simplices,
  subset := sorry }

end asc_subset

def boundary {K : abstract_simplicial_complex A} (K' : abstract_simplicial_complex A) [K'.subcomplex K] 
    {k : ℕ} [is_pure_k_asc K' k] : 
    abstract_simplicial_complex A := by sorry
--{ refine (closure _)}  

end abstract_simplicial_complex