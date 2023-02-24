import combinatorial_surface.abstract_simplicial_complex

open abstract_simplicial_complex

set_option class.instance_max_depth 150000

def example_1 : abstract_simplicial_complex ℕ :=
{ faces := { {1}, {2}, {1, 2}, {3}},
  not_empty_mem := dec_trivial,
  down_closed := by simp ; dec_trivial, }

-- Was getting some error about class instance depth
def example_2 : abstract_simplicial_complex ℕ :=
{ faces := {{1}, {2}, {3}, {4}, {5}, {1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {1,2,3}, {1,2,4}, {4,5}},
  not_empty_mem := dec_trivial,
  down_closed := by simp ; dec_trivial, }

/-- An infinite example: A single 0-face for every natural number -/
def example_3 : abstract_simplicial_complex ℕ :=
{ faces := ⋃ n : ℕ, {{n}},
  not_empty_mem := by simp only [set.Union_singleton_eq_range, set.mem_range, finset.singleton_ne_empty, exists_false, not_false_iff],
  down_closed := by 
  { simp only [set.Union_singleton_eq_range, set.mem_range, ne.def, forall_exists_index, forall_apply_eq_imp_iff',
      finset.subset_singleton_iff],
    intros a t ht₁ ht₂,
    have hta : t = {a} := (or_iff_right ht₂).mp ht₁,
    exact Exists.intro a (eq.symm hta), } }

/-- An infinite example: The power set of the natural numbers -/
def example_4 : abstract_simplicial_complex ℕ :=
{ faces := (⋃ s : finset ℕ, {s}) \ {∅},
  not_empty_mem := by simp only [set.mem_diff, set.mem_singleton, not_true, and_false, not_false_iff],
  down_closed := by simp only [set.Union_singleton_eq_range, set.range_id', set.mem_diff, set.mem_univ, set.mem_singleton_iff, true_and, imp_self,
    implies_true_iff], }

/-
#eval @degree ℕ example_1 {1} (by dec_trivial) -- 0
#eval @degree ℕ example_1 {2} (by dec_trivial) -- 0
#eval @degree ℕ example_1 {1,2} (by dec_trivial) -- 1
#eval @degree ℕ example_1 {3} (by dec_trivial) -- 0
-/
