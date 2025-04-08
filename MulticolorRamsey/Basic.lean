import Mathlib.Combinatorics.SimpleGraph.Basic

import Mathlib.Probability.Distributions.Uniform

import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.Data.ENNReal.Basic

import Mathlib.Algebra.Order.GroupWithZero.Unbundled

import Mathlib.MeasureTheory.MeasurableSpace.Basic

import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open MeasureTheory ProbabilityTheory Finset Real

----------------------------------------------------------------------------------------------------
--  edge colorings

namespace SimpleGraph

variable {V : Type α} {G : SimpleGraph V}

/-- An edge coloring maps each member of the graph's edge set to a colour in `C` --/
abbrev EdgeColoring (C : Type) := G.edgeSet → C

/-- `EC.coloredNeighborSet c v` is the set of vertices that have an edge to `v` in `G` which is
colored with `c` under the edge coloring `EC`. -/
def EdgeColoring.coloredNeighborSet {EC : G.EdgeColoring C} (c : C) (v : V) : Set V :=
  {w | ∃ p : G.Adj v w, EC ⟨s(v,w), p⟩ = c}

instance EdgeColoring.coloredNeighborSetFintype [Fintype V] [DecidableRel G.Adj] [DecidableEq C]
    {EC : G.EdgeColoring C} : Fintype (EC.coloredNeighborSet c v) := by
  simp [EdgeColoring.coloredNeighborSet]
  exact Subtype.fintype _

/-- `EC.coloredNeighborFinset c v` is the Finset of vertices that have `c`-colored edge to `v` in
`G` under the edge coloring `EC`, in case the `c`-colored subgraph of `G` is locally finite at `v`.
-/
def EdgeColoring.coloredNeighborFinset {EC : G.EdgeColoring C} (c : C) (v : V)
    [Fintype (EC.coloredNeighborSet c v)] : Finset V :=
  (EC.coloredNeighborSet c v).toFinset

-- "Given an edge colouring, we write $N_i(u)$ to denote the neighbourhood of vertex $u$ in colour $i$."
abbrev EdgeColoring.N {C} {V} {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableEq C] [Fintype V] (χ : G.EdgeColoring C) (i : C) x :=
  χ.coloredNeighborFinset i x

/-- The book graph with vertex set $A \cup B$ has edge set $\{uv : u ≠ v \text{ and } \{u,v\} \not\subset B\}$ --/
def BookGraph (A B : Type) : SimpleGraph (A ⊕ B) := {
  Adj := by
    rintro x y
    rcases x with a | b <;> rcases y with a' | b'
    · exact a ≠ a'
    · exact True
    · exact True
    · exact False
  symm := by aesop_graph
  loopless := by
    intro x
    rcases x with a | b
    all_goals push_neg; simp
}

end SimpleGraph

----------------------------------------------------------------------------------------------------
--  stuuf we may need

-- namespace Finset

-- variable {α M : Type*}

-- def indicator {s : Finset α} [One M] {f : α → M} (x : α) [DecidableEq α] : M := if x ∈ s then f x else 1

-- def indicator1 {s : Finset α} [DecidableEq α] (x : α) : ℝ := if x ∈ s then 0 else 1

-- end Finset

-- variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} -- [IsProbabilityMeasure P]
--  {n r : ℕ}

-- def foldvecn : (r : ℕ) → (σ : Fin r → (Fin n → α)) → (Fin (∑ _ : Fin r, n) → α)
-- | 0 => fun _ => Matrix.vecEmpty
-- | r + 1 => fun σ => Matrix.vecAppend (by simp [add_mul, add_comm]) (σ 0) (foldvecn r (fun i => σ (i + 1)))

-- -- a computable tensor product
-- def foldvecc : (r : ℕ) → (σ : Fin r → (X → (Fin n → ℝ))) → (X → (Fin (∑ _ : Fin r, n) → ℝ)) :=
--   fun r σ x => foldvecn r (fun r' n' => σ r' x n')

-- -- open scoped TensorProduct

-- -- def tp (v w : (Fin r → ℝ)) : TensorProduct ℝ (Fin r → ℝ) (Fin r → ℝ) := by exact v ⊗ₜ w

-- lemma dotAppend : (r : ℕ) → (v v' w w' : Fin r → ℝ) → dotProduct (Fin.append v v') (Fin.append w w') = (dotProduct v w) * (dotProduct v' w')
-- | 0 => by simp
-- | r + 1 => _

-- lemma dotAppendV : (r : ℕ) → (v v' w w' : Vector ℝ r) → dotProduct (Fin.append v v') (Fin.append w w') = 0
-- | 0 => by simp
-- | r + 1 => _


-- lemma image_nenf {s : Finset A} (f : A → B) [DecidableEq B] [nx : Nonempty  { x // x ∈ s }] :
--     (image f s).Nonempty := image_nonempty.mpr (nonempty_coe_sort.mp nx)

-- lemma image_nen {s : Finset A} {f : A → B} [DecidableEq B] [nx : Nonempty  { x // x ∈ s }] :
--     (image f s).Nonempty := image_nenf f


-- lemma min_le [LinearOrder B] (f g : A → B) (exteq : ∀ a, f a ≤ g a) (X : Finset A) [Nonempty X]:
--     Finset.min (image f X) ≤ Finset.min (image g X) := by
--   simp [Finset.le_min_iff, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
--   intros a as
--   have := Finset.min_le (mem_image_of_mem f as)
--   exact le_trans this (by simp only [WithTop.coe_le_coe, ge_iff_le]; exact (exteq a))


-- lemma min'_le [LinearOrder A] [LinearOrder B] (f g : A → B) (exteq : ∀ a, f a ≤ g a) (X : Finset A) [nx : Nonempty X]:
--     Finset.min' (image f X) (image_nen) ≤
--     Finset.min' (image g X) (image_nen) := by
--   simp [Finset.le_min_iff, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
--   intros a as
--   have : (image f X).min' _ ≤ ↑(f a) := Finset.min'_le (image f X) _ (mem_image_of_mem f as)
--   exact Preorder.le_trans ((image f X).min' image_nen) (f a) (g a) this (exteq a)


-- lemma min'_leX [LinearOrder A] [LinearOrder B] (f g : A → B) (X : Finset A) [nx : Nonempty X] (exteq : ∀ a, (a ∈ X) → f a ≤ g a):
--     Finset.min' (image f X) (image_nen) ≤
--     Finset.min' (image g X) (image_nen) := by
--   simp [Finset.le_min_iff, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
--   intros a as
--   have : (image f X).min' _ ≤ ↑(f a) := Finset.min'_le (image f X) _ (mem_image_of_mem f as)
--   exact Preorder.le_trans ((image f X).min' image_nen) (f a) (g a) this (exteq a as)

-- lemma image_const [LinearOrder B] (f : A → B) (c : B) (X : Finset A) [nen: Nonempty X] (cnst : ∀ x ∈ X , f x = c) :
--     Finset.min' (image f X) (image_nen) = c := by sorry

----------------------------------------------------------------------------------------------------
--  moments lemma

lemma moments (X : Type) [Fintype X] [Nonempty X] [MeasurableSpace X] [Fintype V]
    (σ : Fin r → (X → (V → ℝ))) (l : Fin r → ℕ)
    (U : Measure X) :
    (0 : ℝ) ≤ (U.prod U)[ fun xx => ∏ i, (dotProduct (σ i xx.1) (σ i xx.2)) ^ (l i) ] := by
  have (v : X → ℝ) : 0 ≤ dotProduct v v := by
    simp[dotProduct, ←pow_two]
    exact Finset.sum_nonneg (fun x _ => pow_two_nonneg (v x))

  let L := ∑ i, l i
  let a : Fin L → Fin r := sorry
  sorry


----------------------------------------------------------------------------------------------------
-- special function lemma

noncomputable def coshsqrt (x : ℝ) :=  ∑' n : ℕ , (x ^ n / (2 * n).factorial)

lemma le_coshsqrt : ∀ x, x ≤ 2 + coshsqrt x := by -- i'd like to "observe" that ffs
  have sqrtpow (x : ℝ) (xpos : 0 ≤ x) (n : ℕ)  : x ^ n = (Real.sqrt x)^(2 * n) := by
    simp [sqrt_eq_rpow, pow_mul]
    sorry
  intro x
  simp_rw [coshsqrt]
  by_cases h : 0 ≤ x
  · simp_rw [sqrtpow x h, ← (cosh_eq_tsum √x)]
    sorry
  · sorry

noncomputable def f (x : Fin r → ℝ) : ℝ :=
  ∑ j : Fin r, x j * (1 / (2 + coshsqrt (x j))) * (∏ i : Fin r, (2 + coshsqrt (x i)))

lemma f_ge (x : Fin r → ℝ) : (∏ i : Fin r, (x i)) ≤ f x := by
  have :  ∏ i : Fin r, x i ≤ ∏ i : Fin r, (2 + coshsqrt (x i)) := sorry
  sorry

lemma specialFunctionE (x : Fin r → ℝ) (_ :  ∀ i, -3 * r ≤ x i) :
    f x ≤ 3^r * r * Real.exp (∑ i, Real.sqrt (x i + 3 * r)) := sorry

lemma specialFunctionEc (x : Fin r → ℝ) (_ :  ∃ i, x i < -3 * r) :
    f x ≤ -1 := sorry

----------------------------------------------------------------------------------------------------
-- probabilistic method

open scoped ENNReal

lemma probabilistic_method {X : Type} [Fintype X] [MeasurableSpace X] (U : Measure X) (p : X → X → Prop) [∀ i j, Decidable (p j i)] :
    (0 : ℝ≥0∞) < (U.prod U) { x : X × X | p x.1 x.2 } → ∃ x : X, ∃ x' : X , p x x' := by
      intro a
      by_contra c
      simp_all only [not_exists, not_and, coe_mem, ite_false, integral_zero, Set.setOf_false, measure_empty, lt_self_iff_false]

----------------------------------------------------------------------------------------------------
-- TODO i just put here everything that annoyed me
lemma omg {a b : ℝ} (_ : 0 < b) : a = a / b * b := by sorry
lemma omg2 {a b c : ℝ} (_ : 0 < b) : a ≤ c ↔ a / b ≤ c / b := by sorry
lemma omg3 {a b : ℝ} (_ : 0 < b) : a = a * b / b := by sorry
lemma omg4 {a b c : ℝ} : a ≤ c ↔ a * b ≤ c * b := by sorry
lemma omg5 {a b c : ℝ≥0∞} : b ≤ c ↔ a * b ≤ a * c := by sorry
lemma omg6 {a b : ℝ} : - a ≤ a * b ↔ -1 ≤ b := by sorry
lemma omg7 (a b : ℝ) : a * b / a = b := sorry

lemma exists_mul_of_sum_bound [Nonempty (Fin r)] (g : Fin r → ℝ≥0∞) : ∃ j, ∑ i, g i ≤ r * g j := by
  obtain ⟨j, p⟩ : ∃ j, ∀ i, g i ≤ g j := Finite.exists_max g
  use j
  calc ∑ i : Fin r, g i ≤ ∑ i : Fin r, g j := by exact sum_le_sum fun i a ↦ p i
                      _ = r * g j := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
