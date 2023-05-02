-- import definition of ℝ
import data.real.basic

-- proposition that a function `f : ℝ → ℝ` is non-decreasing
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- *EXAMPLE PROOF*
example (f g : ℝ → ℝ) (hf : non_decreasing f) 
  (hg : non_decreasing g) : non_decreasing (g ∘ f) :=
begin
  rw non_decreasing at *,
  simp only [function.comp_app],
  intros x₁ x₂ h,
  have step₁ : f x₁ ≤ f x₂, by
    exact hf x₁ x₂ h,
  exact hg (f x₁) (f x₂) step₁,
end

/-
  rw non_decreasing at *,
  simp only [function.comp_app],
  intros x₁ x₂ h, -- library_search
  have step₁ : f x₁ ≤ f x₂, by
    exact hf x₁ x₂ h,
  exact hg (f x₁) (f x₂) step₁,
-/

-- exact λ x₁ x₂ h, hg _ _ (hf _ _ h),
