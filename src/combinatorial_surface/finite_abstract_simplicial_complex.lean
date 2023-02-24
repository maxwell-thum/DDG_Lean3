/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Maxwell Thum
-/
import combinatorial_surface.abstract_simplicial_complex

/-!
# Finite abstract simplicial complexes

In this file, we define finite abstract simplicial complexes, which are ASCs with 
finitely many faces, or, equivalently, finitely many vertices.

## Main declarations

* `finite_abstract_simplicial_complex E`: A finite abstract simplicial complex in the type `E`.
-/

open finset set

variables (E : Type*)

/-- A finite abstract simplicial complex has finitely many faces. -/
@[ext] structure finite_abstract_simplicial_complex extends abstract_simplicial_complex E :=
(is_finite : finite faces)
namespace finite_abstract_simplicial_complex

variables {E} {K : finite_abstract_simplicial_complex E} {s t : finset E} {x : E}

lemma finite_asc_vertices_finite : finite K.vertices := sorry

end finite_abstract_simplicial_complex