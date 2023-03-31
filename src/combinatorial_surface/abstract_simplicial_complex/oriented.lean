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
variables (E : Type*) [decidable_eq E] {K : abstract_simplicial_complex E} {s t : finset E} {x : E}

--instance : has_inv (fin s.card ≃ s) := 

@[ext] structure oriented_asc extends abstract_simplicial_complex E :=
(orientation : faces → list E)
(orientation_nodup : Π s : faces, (orientation s).nodup)
(orientation_is_vertices : Π s : faces, (orientation s).to_finset = s.1) -- name is wip
(orientation_consistent : Π s : faces, Π t : faces, t.1 ⊆ s.1 → (orientation t).sublist (orientation s))
--(orientation_is_vertices : Π s : faces, (⟨orientation s, orientation_nodup s⟩ : finset E) = s.1) -- name is wip
/-(orientation_consistent : Π s : faces, ∀ k : fin (s.1.card), 
  (orientation s).remove_nth k = orientation ⟨s.1.erase ((orientation s).nth_le k (by {

  })), by {
    have : s.val.erase ((orientation s).nth_le ↑k _) ⊆ s,
    { }
  }⟩)-/
--(consistent : ∀ s ∈ faces, ∀ t ∈ faces, t ⊆ s → )
/-
/- I understand that `compatible` is absurd but this definition was the only way I 
could get Lean to understand me. It just wasn't synthesizing the placeholders 
otherwise. 
Possibly related: Why are multiple `E`s showing up everywhere?? -/
(compatible : ∀ s : finset E, ∀ hs : s ∈ faces, ∀ t : finset E, ∀ ht : t ∈ faces, 
  ∀ v : E, ∀ hv : v ∈ s ∩ t, ∀ w : E, ∀ hw : w ∈ s ∩ t, 
  ((orientation s hs)⁻¹ ⟨v, (mem_of_mem_inter_left hv)⟩) 
  ≤ (orientation s hs ⟨w, (mem_of_mem_inter_left hw)⟩) 
  ↔ (orientation t ht ⟨v, (mem_of_mem_inter_right hv)⟩) 
  ≤ (orientation t ht ⟨w, (mem_of_mem_inter_right hw)⟩)) -/
--(complex_orientation : partial_order {x // {x} ∈ faces})
--(simplex_orientation : Π s : finset {x // {x} ∈ faces}, s ∈ faces → linear_order s)
--(complex_orient_eq_simplex_orient : ∀ s ∈ faces, ∀ v w ∈ s, complex_orientation.le v w ↔ (simplex_orientation s _).le v w)

--(oriented_faces : Π k : ℕ, set (fin (k+1) → E))


/-- The set of `k`-faces in `K`, the faces in `K` with degree `k`. -/
def oriented_k_faces (K : oriented_asc E) (k : ℕ) : set (list E) := 
  { s ∈ K.faces | s.card = k + 1 }