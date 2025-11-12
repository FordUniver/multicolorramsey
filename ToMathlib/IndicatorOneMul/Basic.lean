import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Indicator function multiplication identity
-/

open Set

variable {X Y : Type*}

/-- Multiplication by indicator of 1 equals indicator of the function. -/
lemma indicator_one_mul [MulZeroOneClass Y] [MeasurableSpace X] (f : X → Y) (E : Set X) (x : X) :
    f x * E.indicator 1 x = E.indicator f x := by
  by_cases hx : x ∈ E <;> simp [hx]
