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
variables {E : Type*} [decidable_eq E] {K : oriented_asc E} {n m : ℕ} {x : E}

/- # Discrete differential forms -/

/-- A discrete differential `m`-form on an oriented ASC `K` is a real-valued 
function on the set of `K`'s oriented `m`-simplices. -/
def discrete_differential_m_forms (K : oriented_asc E) (m : ℕ) 
  := K.oriented_n_simplices m → ℝ

namespace d_d_forms

open n_cochains

/-- The additive commutative monoid structure on `K.discrete_differential_m_forms m`. -/
instance add_comm_monoid : add_comm_monoid (K.discrete_differential_m_forms m) 
  := pi.add_comm_monoid

/-- The `ℝ`-module structure on `K.discrete_differential_m_forms m`. -/
instance module : module ℝ (K.discrete_differential_m_forms m)
  :=  function.module (K.oriented_n_simplices m) ℝ ℝ

def d_d_m_forms_to_m_cochains (m : ℕ) :
    K.discrete_differential_m_forms m ≃ₗ[ℝ] K.n_cochains ℝ m := 
{ to_fun := λ p, 
  { to_fun := λ σ, finsupp.sum σ (λ s a, a * (p s)),
    map_add' := by 
    { intros x y,
      unfold finsupp.sum,
      sorry }, 
    map_smul' := sorry, },
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  map_add' := sorry,
  map_smul' := sorry,
   }

/-- The discrete exterior derivative -/
noncomputable def discrete_exterior_derivative : K.discrete_differential_m_forms m →ₗ[ℝ]
    K.discrete_differential_m_forms (m+1)
  := (d_d_m_forms_to_m_cochains (m+1)).symm.to_linear_map ∘ₗ (coboundary m) ∘ₗ (d_d_m_forms_to_m_cochains m).to_linear_map

end d_d_forms

end oriented_asc
