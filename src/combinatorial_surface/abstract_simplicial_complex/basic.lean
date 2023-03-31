/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Maxwell Thum
-/
--import analysis.convex.hull
--import linear_algebra.affine_space.independent
import data.finset.basic
import data.set.finite

/-!
# DISCLAIMER
**THIS IS MY COPY OF MATHLIB'S `analysis.convex.simplicial_complex.basic`!!!**
These edits have nothing to do with the original authors. 
I'm not sure whether this will ultimately go in mathlib, so I'm changing a lot willy-nilly.

# Abstract simplicial complexes

In this file, we define abstract simplicial complexes. An abstract simplicial complex is...

## Main declarations

* `abstract_simplicial_complex E`: An abstract simplicial complex in the type `E`.
* `abstract_simplicial_complex.vertices`: The zero dimensional faces of an abstract simplicial complex.
* `abstract_simplicial_complex.facets`: The maximal faces of an abstract simplicial complex.

## Notation

`s ∈ K` means that `s` is a face of `K`.

`K ≤ L` means that the faces of `K` are faces of `L`.

## TODO

Simplicial complexes can be generalized to affine spaces once `convex_hull` has been ported.
-/

open finset set

variables (E : Type*) [decidable_eq E]

/-- An abstract simplicial complex in a type `E` is a downward closed set of nonempty
finite sets. -/
-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
@[ext] structure abstract_simplicial_complex :=
(faces : set (finset E))
(not_empty_mem : ∅ ∉ faces)
--(indep : ∀ {s}, s ∈ faces → affine_independent 𝕜 (coe : (s : set E) → E))
(down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ≠ ∅ → t ∈ faces)
/-(inter_subset_convex_hull : ∀ {s t}, s ∈ faces → t ∈ faces →
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E))-/

namespace abstract_simplicial_complex
variables {E} {K : abstract_simplicial_complex E} {s t : finset E} {x : E}

/-- A `finset` belongs to an `abstract_simplicial_complex` if it's a face of it. -/
instance : has_mem (finset E) (abstract_simplicial_complex E) := ⟨λ s K, s ∈ K.faces⟩

/-
/-- The underlying space of a simplicial complex is the union of its faces. -/
def space (K : simplicial_complex 𝕜 E) : set E := ⋃ s ∈ K.faces, convex_hull 𝕜 (s : set E)

lemma mem_space_iff : x ∈ K.space ↔ ∃ s ∈ K.faces, x ∈ convex_hull 𝕜 (s : set E) := mem_Union₂

lemma convex_hull_subset_space (hs : s ∈ K.faces) : convex_hull 𝕜 ↑s ⊆ K.space :=
subset_bUnion_of_mem hs

protected lemma subset_space (hs : s ∈ K.faces) : (s : set E) ⊆ K.space :=
(subset_convex_hull 𝕜 _).trans $ convex_hull_subset_space hs

lemma convex_hull_inter_convex_hull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
  convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t = convex_hull 𝕜 (s ∩ t : set E) :=
(K.inter_subset_convex_hull hs ht).antisymm $ subset_inter
  (convex_hull_mono $ set.inter_subset_left _ _) $ convex_hull_mono $ set.inter_subset_right _ _
-/

/-- -/
lemma disjoint_or_exists_inter_eq_face (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
  (s : set E) ∩ t = ∅ ∨ ∃ u ∈ K.faces, (s : set E) ∩ t = u :=
begin
  classical,
  by_contra' h,
  refine h.2 (s ∩ t) (K.down_closed s hs _ (inter_subset_left _ _) $ λ hst, h.1 _) _,
  { rw [← coe_inter],
    exact coe_eq_empty.mpr hst, },
  { rw [coe_inter], }
end


/-- Construct an abstract simplicial complex by removing the empty face for you. -/
@[simps] def of_erase
  (faces : set (finset E))
  --(indep : ∀ s ∈ faces, affine_independent 𝕜 (coe : (s : set E) → E))
  (down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces)
  /-(inter_subset_convex_hull : ∀ s t ∈ faces,
    convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E))-/ :
  abstract_simplicial_complex E :=
{ faces := faces \ {∅},
  not_empty_mem := λ h, h.2 (mem_singleton _),
  --indep := λ s hs, indep _ hs.1,
  down_closed := λ s hs t hts ht, ⟨down_closed s hs.1 t hts, ht⟩,
  --inter_subset_convex_hull := λ s t hs ht, inter_subset_convex_hull _ hs.1 _ ht.1 
  }

/-- Construct an abstract simplicial complex as a subset of a given abstract simplicial 
complex. -/
@[simps] def of_subcomplex (K : abstract_simplicial_complex E)
  (faces : set (finset E))
  (subset : faces ⊆ K.faces)
  (down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces) :
  abstract_simplicial_complex E :=
{ faces := faces,
  not_empty_mem := λ h, K.not_empty_mem (subset h),
  --indep := λ s hs, K.indep (subset hs),
  down_closed := λ s hs t hts _, down_closed s hs t hts,
  --inter_subset_convex_hull := λ s t hs ht, K.inter_subset_convex_hull (subset hs) (subset ht) 
}

/-! ### Degrees and Vertices -/

/-
/-- The degree (or dimension) of a simplex is its cardinality minus one. -/
def degree (s : finset E) : ℕ := s.card - 1
-/

/-- The set of `k`-faces in `K`, the faces in `K` with degree `k`. -/
def k_faces (K : abstract_simplicial_complex E) (k : ℕ) : set (finset E) := 
  { s ∈ K.faces | s.card = k + 1 }

/-- The vertices of an abstract simplicial complex are its zero dimensional faces. -/
def vertices (K : abstract_simplicial_complex E) : set E := {x | {x} ∈ K.faces}

lemma mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := iff.rfl

lemma vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : set E) :=
begin
  ext x,
  refine ⟨λ h, mem_bUnion h $ mem_coe.2 $ mem_singleton_self x, λ h, _⟩,
  obtain ⟨s, hs, hx⟩ := mem_Union₂.1 h,
  exact K.down_closed _ hs _ (finset.singleton_subset_iff.2 $ mem_coe.1 hx) (singleton_ne_empty _),
end

/-
lemma vertices_subset_space : K.vertices ⊆ K.space :=
vertices_eq.subset.trans $ Union₂_mono $ λ x hx, subset_convex_hull 𝕜 x

lemma vertex_mem_convex_hull_iff (hx : x ∈ K.vertices) (hs : s ∈ K.faces) :
  x ∈ convex_hull 𝕜 (s : set E) ↔ x ∈ s :=
begin
  refine ⟨λ h, _, λ h, subset_convex_hull _ _ h⟩,
  classical,
  have h := K.inter_subset_convex_hull hx hs ⟨by simp, h⟩,
  by_contra H,
  rwa [←coe_inter, finset.disjoint_iff_inter_eq_empty.1
    (finset.disjoint_singleton_right.2 H).symm, coe_empty, convex_hull_empty] at h,
end

/-- A face is a subset of another one iff its vertices are.  -/
lemma face_subset_face_iff (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
  convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t ↔ s ⊆ t :=
⟨λ h x hxs, (vertex_mem_convex_hull_iff (K.down_closed hs (finset.singleton_subset_iff.2 hxs) $
  singleton_ne_empty _) ht).1 (h (subset_convex_hull 𝕜 ↑s hxs)), convex_hull_mono⟩
-/

/-! ### Facets -/

/-- A facet of an abstract simplicial complex is a maximal face. -/
def facets (K : abstract_simplicial_complex E) : set (finset E) :=
{s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t}

lemma mem_facets : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t := mem_sep_iff

lemma facets_subset : K.facets ⊆ K.faces := λ s hs, hs.1

lemma not_facet_iff_subface (hs : s ∈ K.faces) : (s ∉ K.facets ↔ ∃ t, t ∈ K.faces ∧ s ⊂ t) :=
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

`K ≤ L` means that `K.faces ⊆ L.faces`.
-/

variables (E)

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : has_inf (abstract_simplicial_complex E) :=
⟨λ K L, { faces := K.faces ∩ L.faces,
  not_empty_mem := λ h, K.not_empty_mem (set.inter_subset_left _ _ h),
  --indep := λ s hs, K.indep hs.1,
  down_closed := λ s hs t hst ht, ⟨K.down_closed _ hs.1 _ hst ht, L.down_closed _ hs.2 _ hst ht⟩,
  --inter_subset_convex_hull := λ s t hs ht, K.inter_subset_convex_hull hs.1 ht.1 
  }⟩

instance : semilattice_inf (abstract_simplicial_complex E) :=
{ inf := (⊓),
  inf_le_left := λ K L s hs, hs.1,
  inf_le_right := λ K L s hs, hs.2,
  le_inf := λ K L M hKL hKM s hs, ⟨hKL hs, hKM hs⟩,
  .. (partial_order.lift faces $ λ x y, ext _ _) }

instance : has_bot (abstract_simplicial_complex E) :=
⟨{ faces := ∅,
  not_empty_mem := set.not_mem_empty ∅,
  --indep := λ s hs, (set.not_mem_empty _ hs).elim,
  down_closed := λ s hs _, (set.not_mem_empty _ hs).elim,
  --inter_subset_convex_hull := λ s _ hs, (set.not_mem_empty _ hs).elim 
  }⟩

instance : order_bot (abstract_simplicial_complex E) :=
{ bot_le := λ K, set.empty_subset _, .. abstract_simplicial_complex.has_bot E }

instance : inhabited (abstract_simplicial_complex E) := ⟨⊥⟩

variables {E}

lemma faces_bot : (⊥ : abstract_simplicial_complex E).faces = ∅ := rfl

--lemma space_bot : (⊥ : simplicial_complex 𝕜 E).space = ∅ := set.bUnion_empty _

lemma facets_bot : (⊥ : abstract_simplicial_complex E).facets = ∅ := eq_empty_of_subset_empty facets_subset

end abstract_simplicial_complex
