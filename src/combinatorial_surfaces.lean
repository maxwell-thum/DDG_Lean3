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

/-- Based off of `analysis.convex.simplicial_complex.basic`,
`https://ncatlab.org/nlab/show/simplicial+complex`, and Keenan Crane's DDG textbook. -/
--@[ext]
class abstract_simplicial_complex (A : Type*) := -- making this a class again?
(simplices : set (finset A))
(not_empty_mem : ∅ ∉ simplices)
(down_closed : ∀ σ ∈ simplices, ∀ τ ⊆ σ, τ ≠ ∅ → τ ∈ simplices)

namespace abstract_simplicial_complex
variables {A : Type*} {K : abstract_simplicial_complex A}

/-- The degree of a simplex is its cardinality minus one. -/
def degree (σ : finset A) (hσ : σ ∈ K.simplices) : ℕ := σ.card - 1

/-- The set of `k`-simplices in `K`, the simplices in `K` with `k+1` elements. -/
def k_simplices (K : abstract_simplicial_complex A) (k : ℕ) : set (finset A) := 
  { σ ∈ K.simplices | σ.card = k+1 }

/-- The degree of a `k`-simplex is actually `k`, justifying the name. -/
@[simp]
lemma degree_k_simplex_eq_k (σ : finset A) {hσ : σ ∈ K.simplices} {k : ℕ}
    (hσk : σ ∈ k_simplices K k) : degree σ hσ = k := 
  tsub_eq_of_eq_add hσk.2

/-- The set of vertices, which is just another name for 0-simplices. -/
def vertices (K : abstract_simplicial_complex A) := k_simplices K 0

/-- A pure (abstract) `k`-simplicial complex is such that every simplex is contained in 
some `k`-simplex. -/
def is_pure_k_asc (K : abstract_simplicial_complex A) (k : ℕ) : Prop :=
  ∀ σ ∈ K.simplices, ∃ σ' ∈ K.k_simplices k, σ ⊆ σ'

/-- An asc `K'` is a subcomplex of the asc `K` if all of `K'`'s simplices belong to `K`. -/
def subcomplex (K' K : abstract_simplicial_complex A) : Prop := K'.simplices ⊆ K.simplices

/-- Every asc is a subcomplex of itself. -/
@[simp]
lemma asc_subcomplex_self (K : abstract_simplicial_complex A) : K.subcomplex K := rfl.subset

/-- Proposition that a set (not necessarily itself an asc) is a subset of an asc. -/
def subset_asc (S : set (finset A)) (K : abstract_simplicial_complex A) := S ⊆ K.simplices

/-- The set of simplices of a subcomplex of an asc `K` form a subset of `K`. -/
@[simp]
lemma subcomplex_simplices_is_subset_asc (K' K : abstract_simplicial_complex A) 
    (K'_subc_K : K'.subcomplex K) : subset_asc K'.simplices K := K'_subc_K

-- (is this lemma unnecessary?)
/-- In particular, the simplices of an asc are a subset of themselves. -/
@[simp]
lemma asc_simplices_is_subset_asc (K : abstract_simplicial_complex A) : 
    subset_asc K.simplices K := rfl.subset

/-- The proposition that a subset of an asc is closed downward
--, which is equivalent to it forming an asc / 
--subset by the previous lemma `of_subcomplex_is_subcomplex`. 
--Note: I understand that logically this feels a bit... circular. I don't have a good way ...
Note 2: Both here and in `degree`, it seems weird that the definition doesn't (explicitly) 
depend on the asc stuff, but it's still important that we only want to talk about degree or
down-closedness in the context of an asc. Right? -/
def is_down_closed (S : set (finset A)) (hS : subset_asc S K) : Prop := 
  ∀ σ ∈ S, ∀ τ ⊆ σ, τ ≠ ∅ → τ ∈ S

/-- Construct an asc from a downward-closed subset of a given asc. -/
@[simps]
instance to_asc (K : abstract_simplicial_complex A)
  (S : set (finset A))
  (hS : subset_asc S K)
  (down_closed : is_down_closed S hS) :
  abstract_simplicial_complex A :=
{ simplices := S,
  not_empty_mem := λ h, K.not_empty_mem (hS h),
  down_closed := down_closed, }

/- The asc constructed from a downward-closed subset of an asc `K` is a subcomplex of `K`. -/
@[simp]
lemma to_asc_is_subcomplex (K : abstract_simplicial_complex A) (S : set (finset A))
    (hS : subset_asc S K) (down_closed : is_down_closed S hS) : 
    (abstract_simplicial_complex.to_asc K S hS down_closed).subcomplex K := 
  hS

/-- The star of a subset `S` of an asc `K` is the set of simplices in `K` which contain a 
simplex in `S`. -/
def star (S : set (finset A)) (hS : subset_asc S K) : set (finset A) :=
  { σ ∈ K.simplices | ∃ σ' ∈ S, σ' ⊆ σ }

/-- The star of a subset `S` of an asc `K` indeed forms a subset of `K`. -/
@[simp]
lemma star_is_subset_asc (S : set (finset A)) 
    (hS : subset_asc S K) : subset_asc (star S hS) K := by
{ simp only [subset_asc, star, set.sep_subset], }  

/-- (Downward?) closure of a single simplex. -/
def simplex_closure (σ : finset A) 
    (hσ : σ ∈ K.simplices) : set (finset A) :=
  { σ' ∈ K.simplices | σ' ⊆ σ }

/- **TODO**: Define union and intersection of complexes. Make these instances of `has_union`
and `has_int` or whatever they're called. This may be a good reason to let ∅ be a simplex.
On a related note, do we want `subcomplex` to be an instance of `has_sub`? -/
/-- The closure of a subset `S` of an asc `K` is the union of the closures of its simplices.
--Book definition: "The closure Cl(S) is the smallest (i.e., fewest elements) subcomplex of 
--K  that contains S." This is a rough definition in an arbitrary type `A` / possibly infinite 
--set `K.simplices` as it is not necessarily clear that there even *exists* such a minimal set. 
--Perhaps we need a nicer definition.  -/
def closure (S : set (finset A)) (hS : subset_asc S K) : 
    set (finset A) := 
  ⋃ (σ ∈ S), simplex_closure σ (hS H)

@[simp]
lemma closure_is_subset_asc (S : set (finset A))
    (hS : subset_asc S K) : subset_asc (closure S hS) K := by
{ unfold subset_asc closure,
  simp at *,
  sorry
  }

@[simp]
lemma closure_is_down_closed (S : set (finset A)) 
    (hS : subset_asc S K) : is_down_closed (closure S hS):= sorry
  

/- The link of a subset of an asc is -/
def link (S : asc_subset K) : asc_subset K := 
{ simplices := S.star.closure.simplices \ S.closure.star.simplices,
  subset := sorry }

/--  -/
def boundary (K' : abstract_simplicial_complex A) [K'.subcomplex K] 
    {k : ℕ} [is_pure_k_asc K' k] : 
    abstract_simplicial_complex A := by sorry
--{ refine (closure _)}  

end abstract_simplicial_complex