import combinatorial_surfaces

open abstract_simplicial_complex

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
#eval @degree ℕ example_1 {1} (by dec_trivial) -- 0
#eval @degree ℕ example_1 {2} (by dec_trivial) -- 0
#eval @degree ℕ example_1 {1,2} (by dec_trivial) -- 1
#eval @degree ℕ example_1 {3} (by dec_trivial) -- 0
