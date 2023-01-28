import combinatorial_surfaces

namespace abstract_simplicial_complex

instance example_1 : abstract_simplicial_complex ℕ :=
{ simplices := { {1}, {2}, {1, 2}, {3}},
  not_empty_mem := dec_trivial,
  down_closed := by simp ; dec_trivial, }

/- --Getting some error about class instance depth
instance example_2 : abstract_simplicial_complex ℕ :=
{ simplices := {{1}, {2}, {3}, {4}, {5}, {1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {1,2,3}, {1,2,4}, {4,5}},
  not_empty_mem := dec_trivial,
  down_closed := by simp ; dec_trivial,
}
-/

end abstract_simplicial_complex