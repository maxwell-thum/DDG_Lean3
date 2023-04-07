/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import combinatorial_surface.abstract_simplicial_complex.basic

/-!
# Oriented abstract simplicial complexes

~~Based on this definition from (a StackExchange question quoting) Rotman's
Algebraic Topology:
"An oriented simplicial complex K
 is a simplicial complex and a partial order on Vert(K)
 whose restriction to the vertices of any simplex in K
 is a linear order."~~

Now based on my definition which is easier: an orientation on an ASC is a set of 
functions from its simplices/simplices to ℕ with compatible orders. 

## Main declarations

* 

## Notation

-/

open finset set abstract_simplicial_complex
variables (E : Type*) [decidable_eq E] {s t : finset E} {x : E}

/-- An *oriented* abstract simplicial complex is an abstract simplicial complex with orders assigned to
each of its simplices such that the order of a subset of a simplex has the same order as that subset has within
the larger simplex's order. -/
@[ext] structure oriented_asc extends abstract_simplicial_complex E :=
(orientation : simplices → list E)
(orientation_nodup : Π s : simplices, (orientation s).nodup)
(olists_eq_simplices : Π s : simplices, (⟨orientation s, orientation_nodup s⟩ : finset E) = s.1) -- name is wip
(orientation_consistent : Π s : simplices, Π t : simplices, t.1 ⊆ s.1 → (orientation t).sublist (orientation s))
-- (orientation_is_vertices : Π s : simplices, (orientation s).to_finset = s.1) -- name is wip

namespace oriented_asc
variables {E} {K : oriented_asc E} {k : ℕ}

/-- The set of oriented simplices in `K`. -/
def oriented_simplices (K : oriented_asc E) : set (list E) := range K.orientation


/-- The set of oriented `k`-simplices in `K`, the oriented simplices of length `k+1`. -/
def oriented_k_simplices (K : oriented_asc E) (k : ℕ) : set K.oriented_simplices := 
  { s | s.1.length = k + 1 }

@[simp] lemma orientation_length_eq_card {t : K.simplices} : 
    (K.orientation t).length = t.1.card := by
  rw [← K.olists_eq_simplices t, card_mk, multiset.coe_card]

/-- `oriented_k_simplices` equals the set of images of `k`-simplices under `K.orientation`. -/
lemma oriented_k_simplices_eq_orientation_of_k_simplices :
  K.oriented_k_simplices k = { s | ∃ t ∈ K.k_simplices k, K.orientation t = s.1 } := by
{ unfold oriented_k_simplices,
  simp only [set_of],
  ext s,
  split,
  { intro hs,
    cases s.2 with t ht,
    use t,
    split,
    { unfold k_simplices,
      rw [mem_set_of_eq, ← orientation_length_eq_card, ht],
      exact hs, },
    { exact ht, },
  },
  { intro hs,
    cases hs with t ht,
    cases ht with htk hts,
    rw ← hts,
    rw orientation_length_eq_card,
    unfold k_simplices at htk,
    rw mem_set_of_eq at htk,
    exact htk,
  },
}

/-
/-- The set of oriented `k`-simplices in `K`, the 'image' of `K.simplices` under `K.orientation`. -/
def oriented_k_simplices (K : oriented_asc E) (k : ℕ) : set K.oriented_simplices := 
  { s | ∃ t ∈ K.k_simplices k, K.orientation t = s.1 }
  --{ s : K.oriented_simplices | s.1.length = k + 1 }

/-- The images of `k`-simplices under `K.orientation` are indeed `k+1` long. -/
lemma oriented_k_simplex_length_eq_k : 
  ∀ s : K.oriented_simplices, ∀ k : ℕ, s ∈ oriented_k_simplices K k ↔ s.1.length = k + 1 := by
{ intros s k,
  split,
  { intro hs,
    cases hs with t ht,
    cases ht with htk hts,
    rw ← hts,
    have card_eq_length : (K.orientation t).length = (⟨K.orientation t, K.orientation_nodup t⟩ : finset E).card,
      simp only [card_mk, multiset.coe_card],
    rw card_eq_length,
    rw K.olists_eq_simplices t,
    unfold k_simplices at htk,
    rw mem_set_of_eq at htk,
    exact htk, },
  { intro hs,
    unfold oriented_k_simplices,
    rw mem_set_of_eq,
    use s.1.to_finset,

    }
}
-/

lemma oriented_k_plus_1_simplex_remove_nth_is_oriented_k_simplex : 
  ∀ s : K.oriented_simplices, s ∈ K.oriented_k_simplices (k+1) → ∀ 

end oriented_asc