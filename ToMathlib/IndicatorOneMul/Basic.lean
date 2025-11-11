import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Indicator function multiplication identity

This file proves a simple but useful identity for indicator functions.
-/

open Set

variable {X Y : Type*}

/-- Multiplication by an indicator function of 1 equals the indicator of the original function. -/
lemma indicator_one_mul [MulZeroOneClass Y] [MeasurableSpace X] (f : X → Y) (E : Set X) (x : X) :
    f x * E.indicator 1 x = E.indicator f x := by
  by_cases hx : x ∈ E <;> simp [hx]
