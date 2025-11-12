import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability on finite types
-/

open MeasureTheory

variable {X : Type*}

/-- Any function on a finite type with a finite measure is integrable. -/
lemma integrable_of_fintype [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} :
    Integrable f μ := ⟨AEStronglyMeasurable.of_discrete, HasFiniteIntegral.of_finite⟩
