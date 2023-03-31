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
functions from its simplices/faces to ℕ with compatible orders. 

## Main declarations

* 

## Notation

-/

open finset set abstract_simplicial_complex
variables (E : Type*) [decidable_eq E] {s t : finset E} {x : E}

/-- An *oriented* abstract simplicial complex is an abstract simplicial complex with orders assigned to
each of its faces such that the order of a subset of a face has the same order as that subset has within
the larger face's order. -/
@[ext] structure oriented_asc extends abstract_simplicial_complex E :=
(orientation : faces → list E)
(orientation_nodup : Π s : faces, (orientation s).nodup)
(olists_eq_faces : Π s : faces, (⟨orientation s, orientation_nodup s⟩ : finset E) = s.1) -- name is wip
(orientation_consistent : Π s : faces, Π t : faces, t.1 ⊆ s.1 → (orientation t).sublist (orientation s))
-- (orientation_is_vertices : Π s : faces, (orientation s).to_finset = s.1) -- name is wip

namespace oriented_asc
variables {E} {K : oriented_asc E}

/-- The set of oriented faces in `K`. -/
def oriented_faces (K : oriented_asc E) : set (list E) := range K.orientation

/-- The set of oriented `k`-faces in `K`, the 'image' of `K.faces` under `K.orientation`. -/
def oriented_k_faces (K : oriented_asc E) (k : ℕ) : set K.oriented_faces := 
  { s | ∃ t ∈ K.k_faces k, K.orientation t = s.1 }
  --{ s : K.oriented_faces | s.1.length = k + 1 }

/-- The images of `k`-faces under `K.orientation` are indeed `k+1` long. -/
lemma oriented_k_face_length_eq_k {k : ℕ} : 
  ∀ s : K.oriented_faces, s ∈ oriented_k_faces K k → s.1.length = k + 1 := by
{ intros s hs,
  cases hs with t ht,
  cases ht with htk hts,
  rw ← hts,
  have card_eq_length : (K.orientation t).length = (⟨K.orientation t, K.orientation_nodup t⟩ : finset E).card,
    simp only [card_mk, multiset.coe_card],
  rw card_eq_length,
  rw K.olists_eq_faces t,
  unfold k_faces at htk,
  rw mem_set_of_eq at htk,
  exact htk, 
}

end oriented_asc