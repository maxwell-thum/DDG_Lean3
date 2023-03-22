/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import group_theory.free_abelian_group_finsupp
import combinatorial_surface.abstract_simplicial_complex

/-!
# Simplicial homology

In this file, we define simplicial homology of abstract simplicial complexes.

This file takes some inspiration from the simplicial homology in simplicial sets in
the Liquid Tensor Experiment.

## Main declarations

* 

## Notation


-/

--open finset set

open abstract_simplicial_complex
variables {E : Type*} {K : abstract_simplicial_complex E} {s t : finset E} {x : E}

/-- The group of `k`-chains on `K` is the free abelian group on the set of 
`k`-faces of `K`.-/
def k_chains (K : abstract_simplicial_complex E) (k : ℕ) := K.k_faces k →₀ ℤ

