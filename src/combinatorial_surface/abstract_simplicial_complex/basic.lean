/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Maxwell Thum
-/
import data.finset.basic
import data.set.finite

/-!
# DISCLAIMER
**THIS IS MY COPY OF MATHLIB'S `analysis.convex.simplicial_complex.basic`!!!**
These edits have nothing to do with the original authors. 
I'm not sure whether this will ultimately go in mathlib, so I'm changing a lot willy-nilly.
Much of the code here is not necessarily relevant to DDG, but I have 
modified it and left it here in case this gets added to mathlib.

# Abstract simplicial complexes

In this file, we define abstract simplicial complexes. An abstract simplicial complex is...

## Main declarations

* `abstract_simplicial_complex E`: An abstract simplicial complex in the type `E`.
* `abstract_simplicial_complex.vertices`: The zero dimensional simplices of an abstract simplicial complex.
* `abstract_simplicial_complex.facets`: The maximal simplices of an abstract simplicial complex.

## Notation

`s ∈ K` means that `s` is a simplex of `K`.

`K ≤ L` means that the simplices of `K` are simplices of `L`.

## TODO

Simplicial complexes can be generalized to affine spaces once `convex_hull` has been ported.
-/

open finset set

variables (E : Type*) [decidable_eq E]

/-- An abstract simplicial complex in a type `E` is a downward closed set of nonempty
finite sets. -/
-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
@[ext] structure abstract_simplicial_complex :=
(simplices : set (finset E))
(not_empty_mem : ∅ ∉ simplices)
(down_closed : ∀ s ∈ simplices, ∀ t ⊆ s, t ≠ ∅ → t ∈ simplices)

namespace abstract_simplicial_complex
variables {E} {K : abstract_simplicial_complex E} {s t : finset E} {x : E}

/-- A `finset` belongs to an `abstract_simplicial_complex` if it's a simplex of it. -/
instance : has_mem (finset E) (abstract_simplicial_complex E) := ⟨λ s K, s ∈ K.simplices⟩

/-- -/
lemma disjoint_or_exists_inter_eq_simplex (hs : s ∈ K.simplices) (ht : t ∈ K.simplices) :
  (s : set E) ∩ t = ∅ ∨ ∃ u ∈ K.simplices, (s : set E) ∩ t = u :=
begin
  classical,
  by_contra' h,
  refine h.2 (s ∩ t) (K.down_closed s hs _ (inter_subset_left _ _) $ λ hst, h.1 _) _,
  { rw [← coe_inter],
    exact coe_eq_empty.mpr hst, },
  { rw [coe_inter], }
end


/-- Construct an abstract simplicial complex by removing the empty simplex for you. -/
@[simps] def of_erase
  (simplices : set (finset E))
  (down_closed : ∀ s ∈ simplices, ∀ t ⊆ s, t ∈ simplices) :
  abstract_simplicial_complex E :=
{ simplices := simplices \ {∅},
  not_empty_mem := λ h, h.2 (mem_singleton _),
  down_closed := λ s hs t hts ht, ⟨down_closed s hs.1 t hts, ht⟩,
  }

/-- Construct an abstract simplicial complex as a subset of a given abstract simplicial 
complex. -/
@[simps] def of_subcomplex (K : abstract_simplicial_complex E)
  (simplices : set (finset E))
  (subset : simplices ⊆ K.simplices)
  (down_closed : ∀ s ∈ simplices, ∀ t ⊆ s, t ∈ simplices) :
  abstract_simplicial_complex E :=
{ simplices := simplices,
  not_empty_mem := λ h, K.not_empty_mem (subset h),
  down_closed := λ s hs t hts _, down_closed s hs t hts,
}

/-! ### Degrees and Vertices -/

/-- The set of `n`-simplices in `K`, the simplices in `K` with degree `n`. -/
def n_simplices (K : abstract_simplicial_complex E) (n : ℕ) : set (finset E) := 
  { s : finset E | s ∈ K.simplices ∧ s.card = n + 1 }

/-- The vertices of an abstract simplicial complex are the elements of its (zero-dimensional) simplices. -/
def vertices (K : abstract_simplicial_complex E) : set E := {x | {x} ∈ K.simplices}

lemma mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.simplices := iff.rfl

lemma vertices_eq : K.vertices = ⋃ k ∈ K.simplices, (k : set E) :=
begin
  ext x,
  refine ⟨λ h, mem_bUnion h $ mem_coe.2 $ mem_singleton_self x, λ h, _⟩,
  obtain ⟨s, hs, hx⟩ := mem_Union₂.1 h,
  exact K.down_closed _ hs _ (finset.singleton_subset_iff.2 $ mem_coe.1 hx) (singleton_ne_empty _),
end

namespace simplices

namespace n_simplices

/-- Coercion from `n_simplices` to `simplices`. -/
instance {n : ℕ} : has_coe (K.n_simplices n) K.simplices := ⟨λ s, ⟨s.1, s.2.1⟩⟩

/-! #### Removing single vertices 
This is mostly for `oriented.lean`. -/

lemma np1_simplex_remove_vertex_is_n_simplex 
  {n : ℕ} (s : K.n_simplices (n+1)) (v : E) (hv : v ∈ s.1) : (erase s.1 v) ∈ K.n_simplices n :=
begin
  apply and.symm,
  have : (erase s.1 v).card = n + 1,
    rw [finset.card_erase_of_mem hv, s.2.2, add_tsub_cancel_right],
  split,
    exact this,
  { apply K.down_closed s.1 s.2.1 (erase s.1 v) (finset.erase_subset v s.1),
    apply (not_iff_not_of_iff finset.card_eq_zero).1,
    rw this,
    simp, },
end

/-- Removing a vertex from an `(n+1)`-simplex to obtain an `n`-simplex. -/
def remove_vertex {n : ℕ} (s : K.n_simplices (n+1)) (v : E) (hv : v ∈ s.1) : K.n_simplices n := 
  ⟨erase s.1 v, np1_simplex_remove_vertex_is_n_simplex s v hv⟩

end n_simplices

end simplices

/-! ### Facets -/

/-- A facet of an abstract simplicial complex is a maximal simplex. -/
def facets (K : abstract_simplicial_complex E) : set (finset E) :=
{s ∈ K.simplices | ∀ ⦃t⦄, t ∈ K.simplices → s ⊆ t → s = t}

lemma mem_facets : s ∈ K.facets ↔ s ∈ K.simplices ∧ ∀ t ∈ K.simplices, s ⊆ t → s = t := mem_sep_iff

lemma facets_subset : K.facets ⊆ K.simplices := λ s hs, hs.1

lemma not_facet_iff_subsimplex (hs : s ∈ K.simplices) : (s ∉ K.facets ↔ ∃ t, t ∈ K.simplices ∧ s ⊂ t) :=
begin
  refine ⟨λ (hs' : ¬ (_ ∧ _)), _, _⟩,
  { push_neg at hs',
    obtain ⟨t, ht⟩ := hs' hs,
    exact ⟨t, ht.1, ⟨ht.2.1, (λ hts, ht.2.2 (subset.antisymm ht.2.1 hts))⟩⟩ },
  { rintro ⟨t, ht⟩ ⟨hs, hs'⟩,
    have := hs' ht.1 ht.2.1,
    rw this at ht,
    exact ht.2.2 (subset.refl t) } -- `has_ssubset.ssubset.ne` would be handy here
end

/-!
### The semilattice of abstract simplicial complexes

`K ≤ L` means that `K.simplices ⊆ L.simplices`.
-/

variables (E)

/-- The complex consisting of only the simplices present in both of its arguments. -/
instance : has_inf (abstract_simplicial_complex E) :=
⟨λ K L, { simplices := K.simplices ∩ L.simplices,
  not_empty_mem := λ h, K.not_empty_mem (set.inter_subset_left _ _ h),
  down_closed := λ s hs t hst ht, ⟨K.down_closed _ hs.1 _ hst ht, L.down_closed _ hs.2 _ hst ht⟩,
  }⟩

instance : semilattice_inf (abstract_simplicial_complex E) :=
{ inf := (⊓),
  inf_le_left := λ K L s hs, hs.1,
  inf_le_right := λ K L s hs, hs.2,
  le_inf := λ K L M hKL hKM s hs, ⟨hKL hs, hKM hs⟩,
  .. (partial_order.lift simplices $ λ x y, ext _ _) }

instance : has_bot (abstract_simplicial_complex E) :=
⟨{ simplices := ∅,
  not_empty_mem := set.not_mem_empty ∅,
  down_closed := λ s hs _, (set.not_mem_empty _ hs).elim,
  }⟩

instance : order_bot (abstract_simplicial_complex E) :=
{ bot_le := λ K, set.empty_subset _, .. abstract_simplicial_complex.has_bot E }

instance : inhabited (abstract_simplicial_complex E) := ⟨⊥⟩

variables {E}

lemma simplices_bot : (⊥ : abstract_simplicial_complex E).simplices = ∅ := rfl

lemma facets_bot : (⊥ : abstract_simplicial_complex E).facets = ∅ := eq_empty_of_subset_empty facets_subset

end abstract_simplicial_complex
