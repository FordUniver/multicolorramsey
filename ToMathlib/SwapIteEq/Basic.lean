import Mathlib.Data.Fintype.Card

/-!
# Equiv.swap composition with if-then-else
-/

/-- Composing `Equiv.swap c d` with an if-then-else function swaps the test condition. -/
theorem swap_ite_eq {α β : Type} [DecidableEq α] (c d : α) (t k : β) :
  (fun x ↦ if x = d then t else k) ∘ (Equiv.swap c d) = (fun x ↦ if x = c then t else k) := by
  ext x
  wlog hcd : (c = d)
  · push_neg at hcd
    simp only [Function.comp_apply]
    by_cases h1 : x = c
    · simp [h1, Equiv.swap_apply_left]
    · by_cases h2 : x = d
      · simp only [h2, Equiv.swap_apply_right, hcd.symm, ↓reduceIte, ite_eq_right_iff]
        intro; contradiction
      · simp only [Equiv.swap_apply_of_ne_of_ne h1 h2, h2, ↓reduceIte, right_eq_ite_iff]
        intro; contradiction
  · simp [hcd]
