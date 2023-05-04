/-
Copyright (c) 2023 Maxwell Thum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxwell Thum
-/
import combinatorial_surface.abstract_simplicial_complex.basic

/-!
# Oriented abstract simplicial complexes

A definition from (a StackExchange question quoting) Rotman's
Algebraic Topology:
"An oriented simplicial complex K
 is a simplicial complex and a partial order on Vert(K)
 whose restriction to the vertices of any simplex in K
 is a linear order."

My modified definition: An orientation on an ASC assigns each simplex a list 
containing each of its vertices exactly once.

## Main declarations

* 

## Notation

-/

open finset set abstract_simplicial_complex abstract_simplicial_complex.simplices.n_simplices
variables (E : Type*) [decidable_eq E] {x : E}

/-- An *oriented* abstract simplicial complex is an abstract simplicial complex with orders assigned to
each of its simplices such that the order of a subset of a simplex has the same order as that subset has within
the larger simplex's order. -/
@[ext] structure oriented_asc extends abstract_simplicial_complex E :=
(orientation : simplices → list E)
(orientation_nodup : ∀ s : simplices, (orientation s).nodup)
(olists_eq_simplices : ∀ s : simplices, (orientation s).to_finset = s.1)
(orientation_consistent : ∀ n : ℕ, ∀ s : to_abstract_simplicial_complex.n_simplices (n+1), 
  ∀ v : E, ∀ hv : v ∈ s.1, orientation (remove_vertex s v hv) = (orientation s).erase v)
--(orientation_consistent : ∀ s : simplices, ∀ t : simplices, t.1 ⊆ s.1 → (orientation t).sublist (orientation s))

namespace oriented_asc
variables {E} {K : oriented_asc E} {n : ℕ}

/-- The set of oriented simplices in `K`. -/
def oriented_simplices (K : oriented_asc E) : set (list E) := range K.orientation

namespace simplices

/-- Coercion from `simplices` to `oriented_simplices`. -/
instance : has_coe K.simplices K.oriented_simplices := ⟨λ s, ⟨K.orientation s, mem_range_self s⟩⟩

end simplices

open abstract_simplicial_complex.simplices.n_simplices

namespace oriented_simplices

/-- Deoriented simplices are actually simplices, so we can convert `oriented_simplices` back to 
`simplices`. -/
lemma deorient_is_simplex {s : oriented_simplices K} : s.1.to_finset ∈ K.simplices := 
begin
  cases s.2 with t ht,
  rw ← ht,
  rw K.olists_eq_simplices t,
  exact t.2,
end

/-- Coercion from `oriented_simplices` back to `simplices`. -/
instance : has_coe K.oriented_simplices K.simplices := ⟨λ s, ⟨s.1.to_finset, deorient_is_simplex⟩⟩

/-- The other direction of `olists_eq_simplices`: deorienting then orienting 
gives you your original oriented simplex. -/
lemma orient_comp_deorient_eq_val (s : K.oriented_simplices) : K.orientation (s : K.simplices) = s.1 := 
begin
  unfold coe lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe,
  rcases s.2 with ⟨t, ht⟩,
  simp only [←ht],
  simp only [K.olists_eq_simplices t, subtype.val_eq_coe, subtype.coe_eta],
end

end oriented_simplices

/-- The set of oriented `n`-simplices in `K`, the oriented simplices of length `n+1`. -/
def oriented_n_simplices (K : oriented_asc E) (n : ℕ) : set (list E) := 
  { s | s ∈ K.oriented_simplices ∧ s.length = n + 1 }

namespace oriented_simplices

namespace oriented_n_simplices

instance : decidable_eq $ K.oriented_n_simplices n := 
  by apply subtype.decidable_eq

/-- Coercion from `oriented_n_simplices` to `oriented_simplices`. -/
instance {n : ℕ} : has_coe (K.oriented_n_simplices n) K.oriented_simplices := ⟨λ s, ⟨s.1, s.2.1⟩⟩

@[simp] lemma orientation_length_eq_card {s : K.simplices} : 
    (K.orientation s).length = s.1.card := 
  by rw [← K.olists_eq_simplices s, ← list.to_finset_eq (K.orientation_nodup s), 
    card_mk, multiset.coe_card]

/-- Deoriented `n`-simplices are actually `n`-simplices, so we can coerce `oriented_n_simplices` back 
to `n_simplices`. -/
lemma deorient_n_is_n_simplex {s : oriented_n_simplices K n} : s.1.to_finset ∈ K.n_simplices n := 
begin
  cases s.2 with _ hs,
  cases left with t ht,
  rw ← ht,
  rw K.olists_eq_simplices t,
  split,
  exact t.2,
  rw [← orientation_length_eq_card, ht],
  exact hs,
end

/-- Coercion from `oriented_n_simplices` to `n_simplices`. -/
instance : has_coe (K.oriented_n_simplices n) (K.n_simplices n) := 
  ⟨λ s, ⟨s.1.to_finset, deorient_n_is_n_simplex⟩⟩

/-- Coercing an oriented `n`-simplex to a simplex yields the same simplex 
whether you coerce to `n_simplices` or `oriented_simplices` first. 
(I feel like I shouldn't have to use this since its proof is `rfl`) -/
lemma oriented_n_coes_commute (s : K.oriented_n_simplices n) :
  ((s : K.oriented_simplices) : K.simplices) = ((s : K.n_simplices n) : K.simplices) := rfl

/-- `oriented_n_simplices` equals the set of images of `n`-simplices under `K.orientation`. -/
lemma oriented_n_simplices_eq_orientation_of_n_simplices :
    K.oriented_n_simplices n = 
    { s | ∃ t : K.simplices, t.1 ∈ K.n_simplices n ∧ K.orientation t = s } := 
begin
  unfold oriented_n_simplices,
  simp only [set_of],
  ext s,
  split,
  { intro hs,
    cases hs.1 with t ht,
    use t,
    split,
    { unfold n_simplices,
      rw [mem_set_of_eq, ← orientation_length_eq_card, ht],
      split,
        exact t.2,
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
    exact htk.2,
  },
end

end oriented_n_simplices

end oriented_simplices

/-- Coercion from `n_simplices` to `oriented_n_simplices`. -/
instance : has_coe (K.n_simplices n) (K.oriented_n_simplices n) := 
  ⟨λ s, ⟨K.orientation (s : K.simplices), by {
    split,
    { unfold oriented_simplices,
      simp only [mem_range_self], },
    { rw oriented_simplices.oriented_n_simplices.orientation_length_eq_card,
      rw ← s.2.2,
      refl, }, }⟩⟩

namespace oriented_simplices

namespace oriented_n_simplices

variables {s : K.oriented_n_simplices (n+1)} {k : fin (n + 2)}

lemma k_lt_s_length : ↑k < s.1.length := 
begin
  cases s.2 with hs1 hs,
  exact ((eq.symm hs).trans_gt (fin.is_lt k)),
end

/-- The length of an oriented `(n+1)`-simplex's list with an element removed is `n+1`. -/
lemma oriented_np1_simplex_remove_kth_length (k : ℕ) (hk : k < n+2) : 
    (s.val.remove_nth k).length = n+1 := 
begin
  cases s.2 with hs1 hs,
  cases hs1 with t ht,
  rw list.length_remove_nth _ _ ((eq.symm hs).trans_gt hk),
  rw hs,
  refl,
end

/-- Removing the `k`th element from an oriented `(n+1)`-simplex yields a subset (once coerced)-/
lemma oriented_np1_simplex_remove_kth_is_subset :
    (s.1.remove_nth ↑k).to_finset ⊆ s.1.to_finset := 
begin
  intros v hv,
  simp only [list.mem_to_finset],
  simp only [list.mem_to_finset] at hv,
  --rw list.remove_nth_eq_nth_tail at hv,
  sorry
end

lemma oriented_np1_simplex_remove_kth_nodup : (s.1.remove_nth ↑k).nodup := 
begin
  unfold list.nodup,
  sorry
end

lemma oriented_np1_simplex_remove_kth_to_finset_card_eq_np1 : 
    (s.1.remove_nth ↑k).to_finset.card = n + 1 := 
begin
  sorry
end

/-- If you remove the kth element from an oriented (n+1)-simplex, you still have a simplex. -/
lemma oriented_np1_simplex_remove_kth_is_n_simplex : 
    (s.1.remove_nth ↑k).to_finset ∈ K.n_simplices n := 
begin
  split,
  { apply (K.down_closed s.1.to_finset deorient_n_is_n_simplex.1 
      (s.1.remove_nth ↑k).to_finset oriented_np1_simplex_remove_kth_is_subset),
    apply (not_iff_not_of_iff finset.card_eq_zero).1,
    rw oriented_np1_simplex_remove_kth_to_finset_card_eq_np1,
    exact nat.succ_ne_zero n, },
  exact oriented_np1_simplex_remove_kth_to_finset_card_eq_np1,
end

/-- `k`th element of `s` -/
def kth_vertex (s : K.oriented_n_simplices (n+1)) (k : fin (n+2)) : E := 
  list.nth_le s.1 ↑k k_lt_s_length

/-- The `k`th vertex of an oriented simplex is a member of the corresponding simplex. -/
lemma kth_vertex_in_simplex : kth_vertex s k ∈ (s : K.simplices).1 := 
begin
  have : (s : K.simplices).1 = s.1.to_finset,
    refl,
  rw this,
  simp only [list.mem_to_finset],
  exact s.val.nth_le_mem ↑k k_lt_s_length,
end

/-- If you remove the `k`th element from an oriented `(n+1)`-simplex, you still have an oriented simplex. -/
theorem oriented_np1_simplex_remove_kth_is_oriented_n_simplex : 
    list.remove_nth s.1 k ∈ K.oriented_n_simplices n := 
begin
  simp only [oriented_n_simplices_eq_orientation_of_n_simplices, 
    exists_and_distrib_left, mem_set_of_eq],
  let t := remove_vertex (s : K.n_simplices (n+1)) (kth_vertex s k) kth_vertex_in_simplex,
  use (t : K.simplices),
  split,
    exact t.2,
  rw K.orientation_consistent n s (kth_vertex s k) kth_vertex_in_simplex,
  rw ← oriented_n_coes_commute s,
  --rw (rfl : ((s : K.n_simplices (n+1)) : K.simplices) = ((s : K.oriented_simplices) : K.simplices)),
  rw [orient_comp_deorient_eq_val ↑s],
  sorry
end

/-- Removing the `k`th vertex from an oriented `(n+1)`-simplex to obtain an oriented `n`-simplex. -/
def remove_kth_vertex (s : K.oriented_n_simplices (n+1)) (k : fin (n+2)) : 
    K.oriented_n_simplices n := 
  ⟨s.1.remove_nth ↑k, oriented_np1_simplex_remove_kth_is_oriented_n_simplex⟩

end oriented_n_simplices

end oriented_simplices

end oriented_asc
