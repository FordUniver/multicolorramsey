import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Equivalence between even naturals and naturals

Equivalence {n : ℕ // Even n} ≃ ℕ and related infinite sum transformations.
-/

variable {T : Type*}

/-- The bijection {n : ℕ // Even n} ≃ ℕ given by n ↦ n/2. -/
def evenEquivNat : {n : ℕ // Even n} ≃ ℕ where
  toFun := fun ⟨n, _⟩ => n / 2
  invFun n := ⟨2 * n, even_two_mul n⟩
  left_inv := fun ⟨_, en⟩ => by simp [Nat.mul_div_cancel' en.two_dvd]
  right_inv n := by simp

/-- Infinite sum over doubled indices equals the sum over even natural numbers. -/
theorem tsum_double_eq_tsum_even [AddCommMonoid T] [TopologicalSpace T] (f : ℕ → T) :
    ∑' x : ℕ, f (2 * x) = ∑' x : {n : ℕ | Even n}, f x :=
  evenEquivNat.symm.tsum_eq <| f ∘ (↑)
