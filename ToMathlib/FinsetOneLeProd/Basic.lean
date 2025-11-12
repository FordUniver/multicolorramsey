import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Product inequalities for CommMonoidWithZero
-/

namespace Finset

/-- If all elements are at least 1, then the product is at least 1. -/
theorem one_le_prod''' {R ι : Type*}
    [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  apply le_trans (le_of_eq prod_const_one.symm)
  gcongr with i hh
  exact fun _ _ ↦ zero_le_one' R
  exact h i hh

end Finset
