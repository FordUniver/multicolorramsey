import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Equivalence between even naturals and naturals

This file provides an equivalence between even natural numbers and all natural numbers,
and uses it to transform infinite sums.

## Main declarations

- `evenEquivNat`: The equivalence {n : ℕ // Even n} ≃ ℕ given by n ↦ n/2
- `tsum_double_eq_tsum_even`: Transforms ∑' x, f (2*x) into ∑' x : {n | Even n}, f x
-/

variable {T : Type*}

/-- The natural bijection between even natural numbers and all natural numbers,
given by division by 2. -/
def evenEquivNat : {n : ℕ // Even n} ≃ ℕ where
  toFun := fun ⟨n, _⟩ => n / 2
  invFun n := ⟨2 * n, even_two_mul n⟩
  left_inv := fun ⟨_, en⟩ => by simp [Nat.mul_div_cancel' en.two_dvd]
  right_inv n := by simp

/-- An infinite sum over doubled indices equals the sum over even natural numbers. -/
theorem tsum_double_eq_tsum_even [AddCommMonoid T] [TopologicalSpace T] (f : ℕ → T) :
    ∑' x : ℕ, f (2 * x) = ∑' x : {n : ℕ | Even n}, f x :=
  evenEquivNat.symm.tsum_eq <| f ∘ (↑)
