/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import group_theory.free_abelian_group_finsupp
import algebra.module.linear_map
import linear_algebra.dual
import algebra.big_operators.basic
import data.nat.parity
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
variables {E : Type*} [decidable_eq E] {K : oriented_asc E} {n : ℕ} {R : Type*} [comm_ring R] [nontrivial R]

/- # (Abstract) simplicial homology (sort of) -/

/-- The group of `n`-chains on `K` is the free abelian group on the set of 
(oriented) `n`-simplices of `K`. 
(this definition doesn't quite seem the same as what's written here)
This generalizes this to coefficients in an arbitrary comm ring `R`. -/
def n_chains (K : oriented_asc E) (R : Type*) [comm_ring R] [nontrivial R] (n : ℕ) 
  := K.oriented_n_simplices n →₀ R

namespace n_chains

/-- The additive commutative monoid structure on `K.n_chains n`. -/
noncomputable instance add_comm_monoid : add_comm_monoid (K.n_chains R n) 
  := finsupp.add_comm_monoid

/-- The `R`-module structure on `K.n_chains n`. -/
noncomputable instance module : module R (K.n_chains R n)
  := finsupp.module (K.oriented_n_simplices n) R

/-- The `n`-chain boundary of a single `(n+1)`-simplex. -/
noncomputable def simplex_boundary (s : K.oriented_n_simplices (n+1)) : K.n_chains R n
  := finset.sum (finset.range (n + 2)) (λ i, single (remove_kth_vertex s i) ((-1:R)^i))

/-- Helper function which multiplies the boundary of a simplex by a ring element. -/
noncomputable def simplex_boundary' : K.oriented_n_simplices (n+1) → R → K.n_chains R n
  := λ s, λ z, z • simplex_boundary s

/-- Helper lemma for `simplex_boundary'_add` and `simplex_boundary'_smul`. -/
lemma simplex_boundary'_zero_eq_zero (t : ↥(K.oriented_n_simplices (n+1))) : 
    simplex_boundary' t (0 : R) = 0 := by
{ unfold simplex_boundary',
  simp only [zero_smul], }

/-- `simplex_boundary'` respects chain addition. -/
lemma simplex_boundary'_add (σ τ : K.n_chains R (n + 1)) : 
    sum (σ + τ) simplex_boundary' = 
    sum σ simplex_boundary' + sum τ simplex_boundary' := by
{ rw [sum_of_support_subset (σ + τ) finsupp.support_add _ (λ t _, simplex_boundary'_zero_eq_zero t)],
  rw [sum_of_support_subset σ (subset_union_left σ.support τ.support) _ (λ t _, simplex_boundary'_zero_eq_zero t)],
  rw [sum_of_support_subset τ (subset_union_right σ.support τ.support) _ (λ t _, simplex_boundary'_zero_eq_zero t)],
  simp only [finsupp.add_apply],
  rw ← finset.sum_add_distrib,
  apply congr_arg,
  ext s t,
  unfold simplex_boundary',
  simp only [finsupp.coe_smul, finsupp.coe_add, pi.add_apply, pi.smul_apply, smul_eq_mul, ←add_mul], }

/-- `simplex_boundary'` respects scalar multiplication. -/
lemma simplex_boundary'_smul (z : R) (σ : K.n_chains R (n + 1)) : 
    sum (z • σ) simplex_boundary' = z • sum σ simplex_boundary' := by
{ rw [@finsupp.sum_smul_index' _ R _ _ _ _ _ _ _ _ simplex_boundary'_zero_eq_zero], -- eye roll
  rw [finsupp.smul_sum],
  apply congr_arg,
  ext t z s,
  unfold simplex_boundary',
  simp [mul_assoc], }

/-- The boundary of an `(n+1)`-chain. -/
noncomputable def boundary (n : ℕ) : K.n_chains R (n+1) →ₗ[R] K.n_chains R n := 
⟨ (λ σ, sum σ simplex_boundary'),
  simplex_boundary'_add, 
  simplex_boundary'_smul⟩

lemma neg_one_pow_neq_zero {n : ℕ} : (-1:R) ^ n ≠ 0 := by 
{ cases neg_one_pow_eq_or R n,
  exact ne_zero_of_eq_one h,
  rw h,
  simp, }

/-- The boundary of a boundary is zero. -/
theorem boundary_sq_eq_zero : (boundary n) ∘ₗ (boundary (n+1)) 
    = (0 : K.n_chains R (n+2) →ₗ[R] K.n_chains R n) := by
{ ext s t,
  unfold boundary,
  simp,
  unfold single,
  unfold simplex_boundary',
  unfold simplex_boundary,
  unfold finsupp.sum,
  simp [finsupp.coe_finset_sum, finset.sum_apply],
  simp [single],q
  
  sorry
  --simp [neg_one_pow_neq_zero],
  --simp only [linear_map.coe_comp, function.comp_app, lsingle_apply, linear_map.zero_apply, finsupp.coe_zero, pi.zero_apply],
  --unfold boundary,
  --simp only [linear_map.coe_mk, linear_map.map_finsupp_sum, finsupp.sum_apply, finsupp.sum],
  --unfold single,
  --simp,
  }

end n_chains

/- # (Abstract) simplicial cohomology (sort of) -/

/-- The group of `k`-cochains on `K` is the dual of the group of `k`-chains.
(I kinda want to move away from the group language if it makes sense to)-/
def n_cochains (K : oriented_asc E) (R : Type*) [comm_ring R] [nontrivial R] (n : ℕ) 
  := module.dual R (K.n_chains R n)

namespace n_cochains

/-- The additive commutative monoid structure on `K.n_cochains R n`. -/
noncomputable instance add_comm_monoid : add_comm_monoid (K.n_cochains R n) 
  := module.dual.add_comm_monoid R (K.n_chains R n)

/-- The `R`-module structure on `K.n_cochains R n`. -/
noncomputable instance module : module R (K.n_cochains R n)
  := module.dual.module R (K.n_chains R n)

/-- The coboundary is simply the tranpose of the boundary. -/
noncomputable def coboundary (n : ℕ) : K.n_cochains R n →ₗ[R] K.n_cochains R (n+1)
  := @module.dual.transpose R _ _ _ _ _ _ _ (n_chains.boundary n) -- eye roll #2

/-- The coboundary of a coboundary is zero. -/
theorem coboundary_sq_eq_zero : (coboundary (n+1)) ∘ₗ (coboundary n) 
    = (0 : K.n_cochains R n →ₗ[R] K.n_cochains R (n+2)) := by
{ unfold coboundary,
  rw ← module.dual.transpose_comp,
  rw n_chains.boundary_sq_eq_zero,
  simp, }

end n_cochains

end oriented_asc
