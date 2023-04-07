/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import set_theory.zfc.basic
--import combinatorial_surface.abstract_simplicial_complex

/-!
# Halfedge meshes

## Main declarations

* 

## Notation


-/

/-- A halfedge mesh is a set (usually) of "halfedges" equipped with two
permutations: `twin` and `next`, usually denoted "η" and "ρ" respectively.
`next` can be any permutation, but `twin` must be an involution with no fixed 
points. -/
structure halfedge_mesh :=
  (halfedges : Type*)
  (twin : halfedges → halfedges)
  --(twin_is_perm : function.bijective twin) -- pretty sure `twin_twin_eq_id` implies this
  (twin_twin_eq_id : twin ∘ twin = id)
  (twin_no_fixed : ∀ h : halfedges, twin h ≠ h)
  (next : halfedges → halfedges)
  (next_is_perm : function.bijective next)

namespace halfedge_mesh
variables {H : halfedge_mesh}

/-- The edge corresponding to a halfedge is its orbit under `twin`, which is
luckily simply itself and its twin. -/
def edge (h : H.halfedges) : set H.halfedges := { h, H.twin h }

/-- The set of all edges of `H` -/
def edges (H : halfedge_mesh) : set (set H.halfedges) :=
  ⋃ h : H.halfedges, { edge h }

/-- The face corresponding to a halfedge is its orbit under `next`. (I take this
to include its preimages as well; don't want to worry about inverses with types) -/
def face (h : H.halfedges) : set H.halfedges :=
  (⋃ n : ℕ, { nat.iterate H.next n h }) 
    ∪ (⋃ n : ℕ, nat.iterate (set.preimage H.next) n {h})

/-- The set of all faces of `H` -/
def faces (H : halfedge_mesh) : set (set H.halfedges) :=
  ⋃ h : H.halfedges, { face h }

/-- The vertex corresponding to a halfedge is its orbit under `next ∘ twin`. -/
def vertex (h : H.halfedges) : set H.halfedges := 
  (⋃ n : ℕ, { nat.iterate (H.next ∘ H.twin) n h }) 
    ∪ (⋃ n : ℕ, nat.iterate (set.preimage (H.next ∘ H.twin)) n {h})

/-- The set of all vertices of `H` -/
def vertices (H : halfedge_mesh) : set (set H.halfedges) :=
  ⋃ h : H.halfedges, { vertex h }


--open abstract_simplicial_complex
--variables {E : Type*} {K : abstract_simplicial_complex E} {s t : finset E} {x : E}


end halfedge_mesh
