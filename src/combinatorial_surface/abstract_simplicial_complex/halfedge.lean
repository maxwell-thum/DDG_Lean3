/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import combinatorial_surface.abstract_simplicial_complex.basic
import combinatorial_surface.halfedge_mesh

/-!
# Halfedge representations of pure 2-ASCs

In this file, we define 

## Main declarations

## Notation

-/

open abstract_simplicial_complex halfedge_mesh
variables {E : Type*} [decidable_eq E] {K : abstract_simplicial_complex E} {s t : finset E} {x : E}

/-- Construct a halfedge representation of a (manifold?) pure abstract simplicial 2-complex. -/
@[simps] def to_halfedge_mesh (K : abstract_simplicial_complex E) : halfedge_mesh :=
{ halfedges := { ij : E × E // ij.1 ∈ K.vertices ∧ ij.2 ∈ K.vertices ∧ {ij.1, ij.2} ∈ K.k_faces 1 },
  twin := λ ij, ⟨(ij.1.2, ij.1.1), ⟨ij.2.2.1, ij.2.1, by {rw [finset.pair_comm] ; exact ij.2.2.2}⟩⟩,
  twin_twin_eq_id := by
  { ext,
      simp only [subtype.val_eq_coe, subtype.coe_mk, id.def],
      simp only [subtype.val_eq_coe, subtype.coe_mk, id.def], },
  twin_is_perm := by 
  { split,
    { intros ij₁ ij₂ h,
      simp only [subtype.val_eq_coe, prod.mk.inj_iff] at h,
      rw [subtype.ext_iff, prod.eq_iff_fst_eq_snd_eq],
      exact and.comm.mp h, },
    { intros ij,
      existsi (twin ij),
       }, },
  twin_no_fixed := sorry,
  next := sorry,
  next_is_perm := sorry }