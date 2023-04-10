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
functions from its simplices/simplices to ℕ with compatible orders. 

## Main declarations

* 

## Notation

-/

open finset set abstract_simplicial_complex
variables (E : Type*) [decidable_eq E] {x : E}

/-- An *oriented* abstract simplicial complex is an abstract simplicial complex with orders assigned to
each of its simplices such that the order of a subset of a simplex has the same order as that subset has within
the larger simplex's order. -/
@[ext] structure oriented_asc extends abstract_simplicial_complex E :=
(orientation : simplices → list E)
(orientation_nodup : Π s : simplices, (orientation s).nodup)
(olists_eq_simplices : Π s : simplices, (orientation s).to_finset = s.1)
--(olists_eq_simplices : Π s : simplices, (⟨orientation s, orientation_nodup s⟩ : finset E) = s.1) -- name is wip
(orientation_consistent : Π s : simplices, Π t : simplices, t.1 ⊆ s.1 → (orientation t).sublist (orientation s))
-- (orientation_is_vertices : Π s : simplices, (orientation s).to_finset = s.1) -- name is wip

namespace oriented_asc
variables {E} {K : oriented_asc E} {n : ℕ} --{k : fin (n+1)}

/-- The set of oriented simplices in `K`. -/
def oriented_simplices (K : oriented_asc E) : set (list E) := range K.orientation

/-- Coercion from `simplices` to `oriented_simplices`. -/
instance : has_coe K.simplices K.oriented_simplices := ⟨λ s, ⟨K.orientation s, mem_range_self s⟩⟩

/-- Convenient name-/
def deorient (s : oriented_simplices K) : finset E := s.1.to_finset
/-
⟨s.1, by 
{ cases s.2 with t ht,
  rw ← ht,
  exact K.orientation_nodup t, } ⟩ 
-/

--lemma deorient_comp_orientation_eq_id (s : K.simplices) : deorient (K.orientation s) = s.1 := by { }

lemma deorient_is_simplex (s : oriented_simplices K) : deorient s ∈ K.simplices := by
{ cases s.2 with t ht,
  rw deorient,
  rw ← ht,
  rw K.olists_eq_simplices t,
  exact t.2, }

/-- Coercion from `oriented_simplices` back to `simplices`. -/
instance : has_coe K.oriented_simplices K.simplices := ⟨λ s, ⟨deorient s, deorient_is_simplex s⟩⟩

/-- The set of oriented `n`-simplices in `K`, the oriented simplices of length `n+1`. -/
def oriented_n_simplices (K : oriented_asc E) (n : ℕ) : set (list E) := 
  { s | s ∈ K.oriented_simplices ∧ s.length = n + 1 }

@[simp] lemma orientation_length_eq_card {t : K.simplices} : 
    (K.orientation t).length = t.1.card := by
  rw [← K.olists_eq_simplices t, card_mk, multiset.coe_card]

/-- `oriented_n_simplices` equals the set of images of `n`-simplices under `K.orientation`. -/
lemma oriented_n_simplices_eq_orientation_of_k_simplices :
  K.oriented_n_simplices n = { s | ∃ t ∈ K.n_simplices n, K.orientation t = s } := by
{ unfold oriented_n_simplices,
  simp only [set_of],
  ext s,
  split,
  { intro hs,
    cases hs.1 with t ht,
    use t,
    split,
    { unfold n_simplices,
      rw [mem_set_of_eq, ← orientation_length_eq_card, ht],
      exact hs.2, },
    { exact ht, },
  },
  { intro hs,
    cases hs with t ht,
    cases ht with htk hts,
    rw ← hts,
    rw orientation_length_eq_card,
    unfold n_simplices at htk,
    rw mem_set_of_eq at htk,
    split,
    { unfold oriented_simplices,
      exact mem_range_self _, },
    exact htk,
  },
}


lemma oriented_n_plus_1_simplex_remove_kth_is_oriented_n_simplex 
    {s : list E} {hs : s ∈ K.oriented_n_simplices (n+1)} {k : fin (n+2)} : 
  list.remove_nth s k ∈ K.oriented_n_simplices n := by
{ unfold oriented_n_simplices,
  simp only [mem_set_of_eq],
  split,
  { unfold oriented_simplices,
    simp only [set.mem_range, set_coe.exists],
     },
  { rw list.length_remove_nth _ _ ((eq.symm hs.2).trans_gt (fin.is_lt k)),
    simp [hs.2], }
}

end oriented_asc