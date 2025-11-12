import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Indicator function multiplication identity
-/

open Set

variable {X Y : Type*}

/-- Multiplication by indicator of 1 equals indicator of the function. -/
lemma indicator_one_mul [MulZeroOneClass Y] [MeasurableSpace X] (f : X → Y) (s : Set X) (x : X) :
    f x * s.indicator 1 x = s.indicator f x := by
  by_cases hx : x ∈ s <;> simp [hx]
