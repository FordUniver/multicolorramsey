import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Almost everywhere inequality from pointwise inequality
-/

open MeasureTheory

variable {α : Type*}

/-- Convert a pointwise inequality on a set to an almost-everywhere inequality. -/
theorem ae_le_of_forall_on_le {f g : α → ℝ} {s : Set α} [MeasurableSpace α] {μ : Measure α}
    (ms : MeasurableSet s) (h₁ : ∀ x ∈ s, g x ≤ f x) :
    g ≤ᶠ[ae (μ.restrict s)] f := by
  filter_upwards [ae_restrict_mem ms] with x hx using h₁ x hx
