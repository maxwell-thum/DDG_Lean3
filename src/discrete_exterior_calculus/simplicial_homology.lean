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

namespace oriented_asc

open finset set finsupp oriented_asc.oriented_simplices.oriented_n_simplices
variables {E : Type*} [decidable_eq E] {K : oriented_asc E} {n : ℕ} {x : E}

/- # (Abstract) simplicial homology (sort of) -/

/-- The group of `n`-chains on `K` is the free abelian group on the set of 
(oriented) `n`-simplices of `K`. 
(this definition doesn't quite seem the same as what's written here)-/
def n_chains (K : oriented_asc E) (n : ℕ) := K.oriented_n_simplices n →₀ ℤ

namespace oriented_n_simplices

end oriented_n_simplices

namespace n_chains

/-- The additive commutative monoid structure on `K.n_chains n`. -/
noncomputable instance n_chains.add_comm_monoid : add_comm_monoid (K.n_chains n) 
  := finsupp.add_comm_monoid

/-- The `ℤ`-module structure on `K.n_chains n`. -/
noncomputable instance n_chains.int_module : module ℤ (K.n_chains n)
  := finsupp.module (K.oriented_n_simplices n) ℤ

/-- The `n`-chain boundary of a single `(n+1)`-simplex. -/
noncomputable def simplex_boundary (s : K.oriented_n_simplices (n+1)) : K.n_chains n
  := finset.sum (finset.range (n + 2)) (λ i, single (remove_kth_vertex s i) ((-1:ℤ)^i))

/-- Helper function which multiplies the boundary of a simplex by an integer. -/
noncomputable def simplex_boundary' : K.oriented_n_simplices (n+1) → ℤ → K.n_chains n
  := λ s, λ z, z • simplex_boundary s

/-- Helper lemma for `simplex_boundary'_add`. -/
lemma simplex_boundary'_zero_eq_zero {s : ↥(K.oriented_n_simplices n)} 
    {σ τ : K.n_chains (n + 1)} (t : ↥(K.oriented_n_simplices (n+1))) : 
    t ∈ σ.support ∪ τ.support → simplex_boundary' t 0 = 0 := by
{ intro ht,
  unfold simplex_boundary',
  simp only [zero_smul], }

lemma simplex_boundary'_add {σ τ : K.n_chains (n + 1)} : 
    sum (σ + τ) simplex_boundary' = 
    sum σ simplex_boundary' + sum τ simplex_boundary' := by
{ rw [sum_of_support_subset (σ + τ) finsupp.support_add _ simplex_boundary'_zero_eq_zero],
  rw [sum_of_support_subset σ (subset_union_left σ.support τ.support) _ simplex_boundary'_zero_eq_zero],
  rw [sum_of_support_subset τ (subset_union_right σ.support τ.support) _ simplex_boundary'_zero_eq_zero],
  simp only [finsupp.add_apply],
  rw ← finset.sum_add_distrib,
  apply congr_arg,
  ext s t,
  unfold simplex_boundary',
  simp only [finsupp.coe_smul, zsmul_eq_mul, int.cast_add, pi.mul_apply, finsupp.coe_add, pi.add_apply, ← int.distrib_right],
  refl,
  sorry
  --unfold simplex_boundary,
   }

lemma simplex_boundary'_smul (z : ℤ) (σ : K.n_chains (n + 1)) : 
    sum (z • σ) simplex_boundary' = 
    z • sum σ simplex_boundary' := by
{ sorry }

/-- The boundary of an `(n+1)`-chain. -/
noncomputable def boundary : K.n_chains (n+1) →ₗ[ℤ] K.n_chains n := 
⟨ (λ σ, sum σ simplex_boundary'),
  simplex_boundary'_add, 
  simplex_boundary'_smul
  ⟩

/- # (Abstract) simplicial cohomology (sort of) -/

/-- The group of `k`-cochains on `K` is the dual of the group of `k`-chains.
(I kinda want to move away from the group language if it makes sense to)-/
def n_cochains (K : oriented_asc E) (n : ℕ) := module.dual ℤ (K.n_chains n)

/-- The coboundary is simply the tranpose of the boundary. -/
noncomputable def coboundary : n_cochains K n → n_cochains K (n+1)
  := module.dual.transpose boundary

end n_chains

end oriented_asc
