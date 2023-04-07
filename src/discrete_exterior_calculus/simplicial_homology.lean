/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import group_theory.free_abelian_group_finsupp
import algebra.module.linear_map
import linear_algebra.dual
import algebra.big_operators.basic
import combinatorial_surface.abstract_simplicial_complex.oriented

/-!
# Simplicial (co)homology

In this file, we define simplicial homology and cohomology of abstract simplicial complexes.

This file takes some inspiration from the simplicial homology in simplicial sets in
the Liquid Tensor Experiment.

## Main declarations

* 

## Notation


-/

open finset set abstract_simplicial_complex finsupp
variables {E : Type*} [decidable_eq E] {K : oriented_asc E} {k : ℕ} {s t : finset E} {x : E}

/- # (Abstract) simplicial homology (sort of) -/

/-- The group of `k`-chains on `K` is the free abelian group on the set of 
(oriented) `k`-simplices of `K`. 
(this definition doesn't quite seem the same as what's written here)-/
def k_chains (K : oriented_asc E) (k : ℕ) := K.oriented_k_simplices k →₀ ℤ

/-- The additive commutative monoid structure on `k_chains K k`. -/
noncomputable instance k_chains.add_comm_monoid : add_comm_monoid (k_chains K k) 
  := finsupp.add_comm_monoid

/-- The `ℤ`-module structure on `k_chains K k`. -/
noncomputable instance k_chains.int_module : module ℤ (k_chains K k)
  := finsupp.module (K.oriented_k_simplices k) ℤ

noncomputable def boundary : k_chains K (k+1) →ₗ[ℤ] k_chains K k
  := ⟨(λ σ, 
        (finset.sum σ.support (λ s, 
          finset.sum (finset.range (k + 1)) (λ i, 
            (-1:ℤ)^i • (list.remove_nth s.1.1 i)) ))), --∑ i : fin (k+1), (-1:ℤ)^(i:ℕ) • (s.delete i) 
    sorry, 
    sorry⟩

/- # (Abstract) simplicial cohomology (sort of) -/

/-- The group of `k`-cochains on `K` is the dual of the group of `k`-chains.
(I kinda want to move away from the group language if it makes sense to)-/
def k_cochains (K : oriented_asc E) (k : ℕ) := module.dual ℤ (k_chains K k)

/-- The coboundary is simply the tranpose of the boundary. -/
noncomputable def coboundary : k_cochains K k → k_cochains K (k+1)
  := module.dual.transpose boundary
