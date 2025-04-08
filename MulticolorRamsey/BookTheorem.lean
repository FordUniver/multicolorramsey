import MulticolorRamsey.Basic


open Finset Real

-- Some options:
--  * Move this to mathlib
--  * Move this to Basic.lean
--  * Always use ⊤ : SimpleGraph V instead of completeGraph V
--  * Change the definition of completeGraph to ⊤ in Basic.lean
--  * Change the definition of completeGraph to ⊤ in mathlib
instance [DecidableEq V] : DecidableRel (completeGraph V).Adj := fun x y => inferInstanceAs (Decidable (x ≠ y))

theorem book
    {n r : ℕ} (_ : 0 < r)
    {V : Type} [DecidableEq V] [Nonempty V] [Fintype V] (_ : Fintype.card V = n)
    (χ : (completeGraph V).EdgeColoring (Fin r))
    (X : Finset V) -- non-empty and not everything?
    (Y : Fin r → (Finset V)) -- non-empty and not everything?
    (p μ : ℝ) (_ : 0 < p) (_ : 2^10 * r^3 < μ)
    (t m : ℕ) (_ : μ^5 / p < t)
    (_ : ∀ x i, p * # (Y i) ≤ # (χ.N i x ∩ Y i))
    (_ : (μ^2 / p)^(μ * r * t) ≤ # X)
    (_ : ∀ i, ((exp (2^13 * r^3 / μ^2)) / p)^t * m ≤ # (Y i))
    : True := by
  sorry
