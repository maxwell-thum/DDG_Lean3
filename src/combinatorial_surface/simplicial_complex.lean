/-
Copyright (c) 2021 YaÃ«l Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YaÃ«l Dillies, Bhavik Mehta, Maxwell Thum
-/
import analysis.convex.hull
import linear_algebra.affine_space.independent
import combinatorial_surface.finite_abstract_simplicial_complex
import data.real.basic

/-!
# DISCLAIMER
**THIS IS MY COPY OF MATHLIB'S `analysis.convex.simplicial_complex.basic`!!!**
These edits have nothing to do with the original authors. 
I'm not sure whether this will ultimately go in mathlib, so I'm changing a lot willy-nilly.

# Simplicial complexes

In this file, we define simplicial complexes in `ð`-modules. A simplicial complex is a collection
of simplices closed by inclusion (of vertices) and intersection (of underlying sets).

We model them by a downward-closed set of affine independent finite sets whose convex hulls "glue
nicely", each finite set and its convex hull corresponding respectively to the vertices and the
underlying set of a simplex.

## Main declarations

* `simplicial_complex ð E`: A simplicial complex in the `ð`-module `E`.
* `simplicial_complex.vertices`: The zero dimensional faces of a simplicial complex.
* `simplicial_complex.facets`: The maximal faces of a simplicial complex.

## Notation

`s â K` means that `s` is a face of `K`.

`K â¤ L` means that the faces of `K` are faces of `L`.

## Implementation notes

"glue nicely" usually means that the intersection of two faces (as sets in the ambient space) is a
face. Given that we store the vertices, not the faces, this would be a bit awkward to spell.
Instead, `simplicial_complex.inter_subset_convex_hull` is an equivalent condition which works on the
vertices.

## TODO

Simplicial complexes can be generalized to affine spaces once `convex_hull` has been ported.
-/

open finset set

variables (ð E : Type*) {Î¹ : Type*} [ordered_ring ð] [add_comm_group E] [module ð E]

namespace geometry

/-- A simplicial complex in a `ð`-module is a collection of simplices which glue nicely together.
Note that the textbook meaning of "glue nicely" is given in
`geometry.simplicial_complex.disjoint_or_exists_inter_eq_convex_hull`. It is mostly useless, as
`geometry.simplicial_complex.convex_hull_inter_convex_hull` is enough for all purposes. -/
-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
@[ext] structure simplicial_complex extends abstract_simplicial_complex E :=
--(faces : set (finset E))
--(not_empty_mem : â â faces)
(indep : â {s}, s â faces â affine_independent ð (coe : (s : set E) â E))
--(down_closed : â {s t}, s â faces â t â s â t â  â â t â faces)
(inter_subset_convex_hull : â {s t}, s â faces â t â faces â
  convex_hull ð âs â© convex_hull ð ât â convex_hull ð (s â© t : set E))

namespace simplicial_complex
variables {ð E} {K : simplicial_complex ð E} {s t : finset E} {x : E}

/-
/-- A `finset` belongs to a `simplicial_complex` if it's a face of it. -/
instance : has_mem (finset E) (simplicial_complex ð E) := â¨Î» s K, s â K.facesâ©
-/

/-- The underlying space of a simplicial complex is the union of its faces. -/
def space (K : simplicial_complex ð E) : set E := â s â K.faces, convex_hull ð (s : set E)

lemma mem_space_iff : x â K.space â â s â K.faces, x â convex_hull ð (s : set E) := mem_Unionâ

lemma convex_hull_subset_space (hs : s â K.faces) : convex_hull ð âs â K.space :=
subset_bUnion_of_mem hs

protected lemma subset_space (hs : s â K.faces) : (s : set E) â K.space :=
(subset_convex_hull ð _).trans $ convex_hull_subset_space hs

lemma convex_hull_inter_convex_hull (hs : s â K.faces) (ht : t â K.faces) :
  convex_hull ð âs â© convex_hull ð ât = convex_hull ð (s â© t : set E) :=
(K.inter_subset_convex_hull hs ht).antisymm $ subset_inter
  (convex_hull_mono $ set.inter_subset_left _ _) $ convex_hull_mono $ set.inter_subset_right _ _

/-- The conclusion is the usual meaning of "glue nicely" in textbooks. It turns out to be quite
unusable, as it's about faces as sets in space rather than simplices. Further,  additional structure
on `ð` means the only choice of `u` is `s â© t` (but it's hard to prove). -/
lemma disjoint_or_exists_inter_eq_convex_hull (hs : s â K.faces) (ht : t â K.faces) :
  disjoint (convex_hull ð (s : set E)) (convex_hull ð ât) â¨
  â u â K.faces, convex_hull ð (s : set E) â© convex_hull ð ât = convex_hull ð âu :=
begin
  classical,
  by_contra' h,
  refine h.2 (s â© t) (K.down_closed hs (inter_subset_left _ _) $ Î» hst, h.1 $
    disjoint_iff_inf_le.mpr $ (K.inter_subset_convex_hull hs ht).trans _) _,
  { rw [âcoe_inter, hst, coe_empty, convex_hull_empty],
    refl },
  { rw [coe_inter, convex_hull_inter_convex_hull hs ht] }
end

/-- Construct a simplicial complex by removing the empty face for you. -/
@[simps] def of_erase
  (faces : set (finset E))
  (indep : â s â faces, affine_independent ð (coe : (s : set E) â E))
  (down_closed : â s â faces, â t â s, t â faces)
  (inter_subset_convex_hull : â s t â faces,
    convex_hull ð âs â© convex_hull ð ât â convex_hull ð (s â© t : set E)) :
  simplicial_complex ð E :=
{ faces := faces \ {â},
  not_empty_mem := Î» h, h.2 (mem_singleton _),
  indep := Î» s hs, indep _ hs.1,
  down_closed := Î» s t hs hts ht, â¨down_closed _ hs.1 _ hts, htâ©,
  inter_subset_convex_hull := Î» s t hs ht, inter_subset_convex_hull _ hs.1 _ ht.1 }

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps] def of_subcomplex (K : simplicial_complex ð E)
  (faces : set (finset E))
  (subset : faces â K.faces)
  (down_closed : â {s t}, s â faces â t â s â t â faces) :
  simplicial_complex ð E :=
{ faces := faces,
  not_empty_mem := Î» h, K.not_empty_mem (subset h),
  indep := Î» s hs, K.indep (subset hs),
  down_closed := Î» s t hs hts _, down_closed hs hts,
  inter_subset_convex_hull := Î» s t hs ht, K.inter_subset_convex_hull (subset hs) (subset ht) }

/-- Construct a simplicial complex from an abstract simplicial complex. This is usually 
called *geometric realization*. This particular realization is from 
`https://ncatlab.org/nlab/show/simplicial+complex#canonical_construction`. -/
def of_finasc {A : Type*} (K : finite_abstract_simplicial_complex A) : simplicial_complex â (K.vertices â â) := 
{ faces := { x : finset (K.vertices â â) | â a â K.faces, âx = f '' a}, -- idk put an order on the set first
  not_empty_mem := sorry, --K.not_empty_mem,
  indep := sorry,
  down_closed := sorry, --K.down_closed,
  inter_subset_convex_hull := sorry }

/-! ### Vertices -/

/-
/-- The vertices of a simplicial complex are its zero dimensional faces. -/
def vertices (K : simplicial_complex ð E) : set E := {x | {x} â K.faces}


lemma mem_vertices : x â K.vertices â {x} â K.faces := abstract_simplicial_complex.mem_vertices

lemma vertices_eq : K.vertices = â k â K.faces, (k : set E) := abstract_simplicial_complex.vertices_eq
-/

lemma vertices_subset_space : K.vertices â K.space :=
abstract_simplicial_complex.vertices_eq.subset.trans $ Unionâ_mono $ Î» x hx, subset_convex_hull ð x

lemma vertex_mem_convex_hull_iff (hx : x â K.vertices) (hs : s â K.faces) :
  x â convex_hull ð (s : set E) â x â s :=
begin
  refine â¨Î» h, _, Î» h, subset_convex_hull _ _ hâ©,
  classical,
  have h := K.inter_subset_convex_hull hx hs â¨by simp, hâ©,
  by_contra H,
  rwa [âcoe_inter, finset.disjoint_iff_inter_eq_empty.1
    (finset.disjoint_singleton_right.2 H).symm, coe_empty, convex_hull_empty] at h,
end

/-- A face is a subset of another one iff its vertices are.  -/
lemma face_subset_face_iff (hs : s â K.faces) (ht : t â K.faces) :
  convex_hull ð (s : set E) â convex_hull ð ât â s â t :=
â¨Î» h x hxs, (vertex_mem_convex_hull_iff (K.down_closed hs (finset.singleton_subset_iff.2 hxs) $
  singleton_ne_empty _) ht).1 (h (subset_convex_hull ð âs hxs)), convex_hull_monoâ©

/-! ### Facets -/

/-
/-- A facet of a simplicial complex is a maximal face. -/
def facets (K : simplicial_complex ð E) : set (finset E) :=
{s â K.faces | â â¦tâ¦, t â K.faces â s â t â s = t}


lemma mem_facets : s â K.facets â s â K.faces â§ â t â K.faces, s â t â s = t := mem_sep_iff

lemma facets_subset : K.facets â K.faces := Î» s hs, hs.1

lemma not_facet_iff_subface (hs : s â K.faces) : (s â K.facets â â t, t â K.faces â§ s â t) :=
begin
  refine â¨Î» (hs' : Â¬ (_ â§ _)), _, _â©,
  { push_neg at hs',
    obtain â¨t, htâ© := hs' hs,
    exact â¨t, ht.1, â¨ht.2.1, (Î» hts, ht.2.2 (subset.antisymm ht.2.1 hts))â©â© },
  { rintro â¨t, htâ© â¨hs, hs'â©,
    have := hs' ht.1 ht.2.1,
    rw this at ht,
    exact ht.2.2 (subset.refl t) } -- `has_ssubset.ssubset.ne` would be handy here
end
-/

/-!
### The semilattice of simplicial complexes

`K â¤ L` means that `K.faces â L.faces`.
-/

variables (ð E)

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : has_inf (simplicial_complex ð E) :=
â¨Î» K L, { faces := K.faces â© L.faces,
  not_empty_mem := Î» h, K.not_empty_mem (set.inter_subset_left _ _ h),
  indep := Î» s hs, K.indep hs.1,
  down_closed := Î» s t hs hst ht, â¨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst htâ©,
  inter_subset_convex_hull := Î» s t hs ht, K.inter_subset_convex_hull hs.1 ht.1 }â©

/- I don't think I care about this much for DDG so I'm just commenting it out for now
instance : semilattice_inf (K : simplicial_complex ð E) :=
{ inf := (â),
  inf_le_left := Î» K L s hs, hs.1,
  inf_le_right := Î» K L s hs, hs.2,
  le_inf := Î» K L M hKL hKM s hs, â¨hKL hs, hKM hsâ©,
  .. (partial_order.lift (abstract_simplicial_complex.faces â to_abstract_simplicial_complex) $ Î» x y, ext _ _) }
-/

instance : has_bot (simplicial_complex ð E) :=
â¨{ faces := â,
  not_empty_mem := set.not_mem_empty â,
  indep := Î» s hs, (set.not_mem_empty _ hs).elim,
  down_closed := Î» s _ hs, (set.not_mem_empty _ hs).elim,
  inter_subset_convex_hull := Î» s _ hs, (set.not_mem_empty _ hs).elim }â©

/- Ditto
instance : order_bot (simplicial_complex ð E) :=
{ bot_le := Î» K, set.empty_subset _, .. simplicial_complex.has_bot ð E }
-/

instance : inhabited (simplicial_complex ð E) := â¨â¥â©

variables {ð E}

lemma faces_bot : (â¥ : simplicial_complex ð E).faces = â := rfl

lemma space_bot : (â¥ : simplicial_complex ð E).space = â := set.bUnion_empty _

lemma facets_bot : (â¥ : simplicial_complex ð E).facets = â := eq_empty_of_subset_empty abstract_simplicial_complex.facets_subset

end simplicial_complex
end geometry
