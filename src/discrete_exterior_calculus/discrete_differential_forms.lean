/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import data.real.basic
import discrete_exterior_calculus.simplicial_homology

/-!
# Discrete differential forms

In this file, we define discrete differential forms in abstract simplicial complexes.

## Main declarations

* 

## Notation


-/

namespace oriented_asc

open finset set finsupp oriented_asc.oriented_simplices.oriented_n_simplices 
variables {E : Type*} [decidable_eq E] {K : oriented_asc E} {n : ℕ} {x : E}

/- # Discrete differential forms -/

/-- A discrete differential `n`-form on an oriented ASC `K` is a real-valued 
function on the set of `K`'s oriented `n`-simplices. -/
def discrete_differential_n_forms (K : oriented_asc E) (n : ℕ) 
  := K.oriented_n_simplices n → ℝ

def real_n_cochains (K : oriented_asc E) (n : ℕ)
  := K.n_chains n →ₗ[ℤ] ℝ

--def real_coboundary : real_n_cochains K n →ₗ[ℤ] real_n_cochains K (n+1):= (linear_map.llcomp R M M' R).flip

/-- The discrete exterior derivative -/
def discrete_exterior_derivative (α : K.discrete_differential_n_forms n) :
    K.discrete_differential_n_forms (n+1)
  := 

end oriented_asc
