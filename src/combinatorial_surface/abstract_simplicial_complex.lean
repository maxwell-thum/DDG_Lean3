/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. **TODO**: get this license
Author: Maxwell Thum.
-/
import data.finset.powerset
--import data.set.finite
--import data.set.default

/-!
# IMPORTANT
I am getting hung up on little details here and there and I don't think I can make some of these decisions
until I have a bigger picture of what all these definitions are supposed to serve. For now I will just try
to build the blueprint and move on with lots of `sorry`s.

# Abstract simplicial complexes (should this file be renamed? split up?)
A *(finite) abstract simplicial complex* `K` is a pair `(V, S)`, where 
`V` is a finite set, 
`S ⊆ 𝒫(V)` is a set of subsets of `V`,
every `σ ∈ S` is finite, 
and for all `σ ∈ S`, 
`σ' ⊆ σ` implies `σ' ∈ S`. 
`V` is called the set of *vertices* and elements of `S` are called *simplices*.


## Notation

`σ ∈ K` means that `σ` is a simplex of `K`.

`K' ⊆ K` means that the simplices of `K'` are simplices of `K`.

-/

universes u v

/-- Based off of `analysis.convex.simplicial_complex.basic`,
`https://ncatlab.org/nlab/show/simplicial+complex`, and Keenan Crane's DDG textbook.
I am allowing the empty set to be a simplex. -/
--@[ext]
class abstract_simplicial_complex (A : Type*) := -- making this a class again?
(simplices : set (finset A))
(down_closed : ∀ σ ∈ simplices, ∀ τ ⊆ σ, τ ∈ simplices)

namespace abstract_simplicial_complex
variables {A : Type*} [K : abstract_simplicial_complex A]

/-- A `finset` belongs to an `abstract_simplicial_complex` if it's a simplex of it. -/
instance : has_mem (finset A) (abstract_simplicial_complex A) := ⟨λ σ K, σ ∈ K.simplices⟩

/-- The degree (or dimension) of a simplex is its cardinality minus one. -/ --
def degree (σ : finset A) : ℤ := σ.card - 1

/-- The set of `k`-simplices in `K`, the simplices in `K` with degree `k`. -/
def k_simplices (K : abstract_simplicial_complex A) (k : ℤ) : set (finset A) := 
  { σ ∈ K.simplices | degree σ = k }

-- **TODO**: make this more in line with `analysis.convex.simplicial_complex.basic`
/-- The set of vertices of an ASC, corresponding to its 0-simplices. -/
def vertices (K : abstract_simplicial_complex A) : set A := ⋃ σ ∈ K.simplices, (σ : set A)

/-- A pure (abstract) `k`-simplicial complex is such that every simplex is contained in 
some `k`-simplex. -/
def is_pure_k_asc (K : abstract_simplicial_complex A) (k : ℕ) : Prop :=
  ∀ σ ∈ K.simplices, ∃ σ' ∈ K.k_simplices k, σ ⊆ σ'

/-- An ASC `K'` is a subcomplex of the ASC `K` if all of `K'`'s simplices belong to `K`. -/
--instance subcomplex : has_subset (abstract_simplicial_complex A) := ⟨λ K' K, K'.simplices ⊆ K.simplices⟩
def subcomplex (K' K : abstract_simplicial_complex A) : Prop := K'.simplices ⊆ K.simplices

-- -- ~~Is this unnecessary now that we have an instance of `has_subset`?~~
/-- Every ASC is a subcomplex of itself. -/
@[simp]
lemma asc_subcomplex_self (K : abstract_simplicial_complex A) : K.subcomplex K := rfl.subset

/-
/- I think I might prefer to just use `S ⊆ K.simplices`. Being able to just write `S ⊆ K` might be nice,
but `⊆` seems to be reserved for terms of the same type. -/
/-- Proposition that a set (not necessarily itself an ASC) is a subset of an ASC. -/
def subset_asc (S : set (finset A)) (K : abstract_simplicial_complex A) := S ⊆ K.simplices

/-- The set of simplices of a subcomplex of an ASC `K` form a subset of `K`. -/
@[simp]
lemma subcomplex_simplices_is_subset_asc (K' K : abstract_simplicial_complex A) 
    (K'_subc_K : K'.subcomplex K) : subset_asc K'.simplices K := K'_subc_K

-- (is this lemma unnecessary?)
/-- In particular, the simplices of an ASC are a subset of themselves. -/
@[simp]
lemma asc_simplices_is_subset_asc (K : abstract_simplicial_complex A) : 
    subset_asc K.simplices K := rfl.subset
-/

/-- The proposition that a subset of an ASC is closed downward
--, which is equivalent to it forming an ASC / 
--subset by the previous lemma `of_subcomplex_is_subcomplex`. 
--Note: I understand that logically this feels a bit... circular. I don't have a good way ...
Note 2: Both here and in `degree`, it seems weird that the definition doesn't (explicitly) 
depend on the ASC stuff, but it's still important that we only want to talk about degree or
down-closedness in the context of an ASC. Right? -/
def is_down_closed (S : set (finset A)) (hS : S ⊆ K.simplices) : Prop := 
  ∀ σ ∈ S, ∀ τ ⊆ σ, τ ∈ S

/-
/-- Construct an ASC from a downward-closed subset of a given ASC. -/
--@[simps]
instance to_asc (K : abstract_simplicial_complex A)
  (S : set (finset A))
  (hS : S ⊆ K.simplices)
  (down_closed : is_down_closed S hS) :
  abstract_simplicial_complex A :=
{ simplices := S,
  down_closed := down_closed, }

/- The ASC constructed from a downward-closed subset of an ASC `K` is a subcomplex of `K`. -/
@[simp]
lemma to_asc_is_subcomplex (K : abstract_simplicial_complex A) (S : set (finset A))
    (hS : S ⊆ K.simplices) (down_closed : is_down_closed S hS) : 
    (abstract_simplicial_complex.to_asc K S hS down_closed).subcomplex K := 
  hS
-/

/-- The star of a subset `S` of an ASC `K` is the set of simplices in `K` which contain a 
simplex in `S`. -/
def star (S : set (finset A)) {hS : S ⊆ K.simplices} : set (finset A) :=
  { σ ∈ K.simplices | ∃ σ' ∈ S, σ' ⊆ σ }

/- trying to get blueprint working
/-- The star of a subset `S` of an ASC `K` indeed forms a subset of `K`. -/
@[simp]
lemma star_is_subset_asc (S : set (finset A)) 
    {hS : S ⊆ K.simplices} : (@star A K S hS) ⊆ K.simplices := 
  by sorry --simp only [subset_asc, star, set.sep_subset]
-/

/-- (Downward?) closure of a single simplex. -/
def simplex_closure (σ : finset A) 
    (hσ : σ ∈ K.simplices) : set (finset A) :=
  { σ' ∈ K.simplices | σ' ⊆ σ }

/- **TODO**: Define union and intersection of complexes. Make these instances of `has_union`
and `has_int` or whatever they're called. This may be a good reason to let ∅ be a simplex.
On a related note, do we want `subcomplex` to be an instance of `has_sub`? -/
/-- The closure of a subset `S` of an ASC `K` is the union of the closures of its simplices.
--Book definition: "The closure Cl(S) is the smallest (i.e., fewest elements) subcomplex of 
--K  that contains S." This is a rough definition in an arbitrary type `A` / possibly infinite 
--set `K.simplices` as it is not necessarily clear that there even *exists* such a minimal set. 
--Perhaps we need a nicer definition.  -/
def closure (S : set (finset A)) [hS : S ⊆ K.simplices] : 
    set (finset A) := 
  ⋃ (σ ∈ S), simplex_closure σ (hS H)

/- for now 
/-- The closure of a subset `S` of an ASC `K` indeed forms a subset of `K`. -/
@[simp]
lemma closure_is_subset_asc (S : set (finset A))
    (hS : S ⊆ K.simplices) : (closure S hS) ⊆ K.simplices := by
{ unfold subset_asc closure,
  simp at *,
  sorry
  }

@[simp]
lemma closure_is_down_closed (S : set (finset A)) 
    (hS : subset_asc S K) : is_down_closed (closure S hS) (closure_is_subset_asc S hS) := 
  sorry

/- The link of a subset of an ASC is -/
def link (S : set (finset A)) (hS : subset_asc S K) : set (finset A) := 
  S.star.closure.simplices \ S.closure.star.simplices


/--  -/
def boundary (K' : abstract_simplicial_complex A) [K'.subcomplex K] 
    {k : ℕ} [is_pure_k_asc K' k] : 
    abstract_simplicial_complex A := by sorry
--{ refine (closure _)}  

-/
end abstract_simplicial_complex