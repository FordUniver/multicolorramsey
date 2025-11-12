import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.ENNReal.Basic

/-!
# Sum and expectation bound lemmas

Lemmas about finding elements that bound sums and expectations.
-/

open Finset

variable {X Y : Type*}

namespace Fintype

/-- There exists an element such that the sum is bounded by the cardinality times that element. -/
lemma exists_mul_of_sum_bound [Nonempty X] [Fintype X] [AddCommMonoid Y] [LinearOrder Y]
    [IsOrderedAddMonoid Y] (g : X → Y) :
    ∃ j, ∑ i, g i ≤ (Fintype.card X) • g j := by
  obtain ⟨j, p⟩ : ∃ j, ∀ i, g i ≤ g j := Finite.exists_max g
  use j
  calc ∑ i : X, g i ≤ ∑ i : X, g j           := by exact sum_le_sum fun i a ↦ p i
                  _ = (Fintype.card X) • g j := by simp only [sum_const, card_univ]

end Fintype

namespace Finset

/-- There exists an element in the finset such that the sum is bounded by the cardinality times that element. -/
lemma exists_mul_of_sum_bound [Nonempty X] [Fintype X] [AddCommMonoid Y] [LinearOrder Y]
    [IsOrderedAddMonoid Y] (s : Finset X) (g : X → Y) (ns : s.Nonempty) :
    ∃ j ∈ s, ∑ i ∈ s, g i ≤ (#s) • g j := by
  obtain ⟨j, ⟨js, p⟩⟩ := exists_max_image s g ns
  use j
  use js
  exact sum_le_card_nsmul s g (g j) (fun x a ↦ p x a)

/-- There exists an element whose value is at least the expectation. -/
lemma exists_le_expect {ι : Type*} {α : Type*} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α] {s : Finset ι} {f : ι → α}
    (hs : s.Nonempty) :
    ∃ x ∈ s, s.expect f ≤ f x := by
  by_contra h
  push_neg at h
  obtain ⟨m, ⟨ms, mmin⟩⟩ := exists_max_image s f hs
  obtain ⟨z, ⟨zs, mltz⟩⟩ := exists_lt_of_lt_expect hs (h m ms)
  exact not_lt_of_ge (mmin z zs) mltz

end Finset

namespace Fin

open scoped ENNReal

/-- There exists an index such that the sum is bounded by `r` times that element. -/
lemma exists_mul_of_sum_bound {r : ℕ} [Nonempty (Fin r)] (g : Fin r → ℝ≥0∞) :
    ∃ j, ∑ i, g i ≤ r * g j := by
  have := Fintype.exists_mul_of_sum_bound g
  simp only [Fintype.card_fin, nsmul_eq_mul] at this
  assumption

end Fin
