import Mathlib.Combinatorics.SimpleGraph.Basic

import Mathlib.Probability.Distributions.Uniform

import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.Data.ENNReal.Basic

import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs

import Mathlib.MeasureTheory.MeasurableSpace.Basic

import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

import Mathlib.MeasureTheory.Integral.Average

import Mathlib.Probability.ProbabilityMassFunction.Integrals

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

end SimpleGraph

----------------------------------------------------------------------------------------------------
--  stuuf we may need

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
    (U : Measure (X × X)) :
    (0 : ℝ) ≤ U[ fun xx => ∏ i, (dotProduct (σ i xx.1) (σ i xx.2)) ^ (l i) ] := by
  have (v : X → ℝ) : 0 ≤ dotProduct v v := by
    simp[dotProduct, ←pow_two]
    exact Finset.sum_nonneg (fun x _ => pow_two_nonneg (v x))

  let L := ∑ i, l i
  let a : Fin L → Fin r := sorry
  sorry


----------------------------------------------------------------------------------------------------
-- special function lemma

noncomputable def coshsqrt (x : ℝ) :=  ∑' n : ℕ , (x ^ n / (2 * n).factorial)

lemma ffs (b : ℕ) : b ≤ 2 * b :=
  match b with
  | 0 => Nat.le_mul_self 0
  | b + 1 => by rw [mul_add_one]; simp; exact Nat.le_add_right_of_le (ffs b)

lemma mew {x} (xpos: (0 : ℝ) ≤ ↑x) : Summable (fun n ↦ (x ^ n / (2 * n).factorial)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (Real.summable_pow_div_factorial x)
    all_goals intro b
    positivity
    refine div_le_div₀ ?_ ?_ ?_ ?_
    exact pow_nonneg xpos b
    exact Preorder.le_refl (x ^ b)
    positivity
    exact Nat.cast_le.mpr (Nat.factorial_le (ffs b))


lemma le_coshsqrt (x : ℝ) (xnn : 0 ≤ x) : x ≤ 2 + coshsqrt x := by -- i'd like to "observe" that ffs
  have : coshsqrt x = 1 + x / 2 + x ^ 2 / ↑(4).factorial + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial := by
    simp [coshsqrt, ← Summable.sum_add_tsum_nat_add 3 (mew xnn), Finset.sum, add_comm]
  simp [this]
  have spos : 0 ≤ ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial := tsum_nonneg (by intro; positivity)
  have : 2 + (1 + x / 2 + x ^ 2 / ↑(Nat.factorial 4) + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial) = (3 + x / 2 + x ^ 2 / ↑(Nat.factorial 4)) + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial := by ring
  simp [this]
  suffices x ≤ (3 + x / 2 + x ^ 2 / ↑(Nat.factorial 4)) from le_add_of_le_of_nonneg this spos
  sorry
  -- have sqrtpow (x : ℝ) (xpos : 0 ≤ x) (n : ℕ)  : x ^ n = (Real.sqrt x)^(2 * n) := by
  --   simp [sqrt_eq_rpow, pow_mul]
  --   sorry
  -- intro x
  -- simp_rw [coshsqrt]
  -- by_cases h : 0 ≤ x
  -- · simp_rw [sqrtpow x h, ← (cosh_eq_tsum √x)]
  --   sorry
  -- · sorry

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
-- TODO maybe mathlib wants some of this

lemma Fintype.exists_mul_of_sum_bound [Nonempty X] [Fintype X] [AddCommMonoid Y] [LinearOrder Y] [IsOrderedAddMonoid Y] (g : X → Y) :
    ∃ j, ∑ i, g i ≤ (Fintype.card X) • g j := by
  obtain ⟨j, p⟩ : ∃ j, ∀ i, g i ≤ g j := Finite.exists_max g
  use j
  calc ∑ i : X, g i ≤ ∑ i : X, g j           := by exact sum_le_sum fun i a ↦ p i
                  _ = (Fintype.card X) • g j := by simp only [sum_const, card_univ, nsmul_eq_mul]

lemma Finset.exists_mul_of_sum_bound [Nonempty X] [Fintype X] [AddCommMonoid Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (s : Finset X) (g : X → Y) (ns : s.Nonempty) :
    ∃ j ∈ s, ∑ i ∈ s, g i ≤ (#s) • g j := by
  obtain ⟨j, ⟨js, p⟩⟩ := Finset.exists_max_image s g ns
  use j
  use js
  exact Finset.sum_le_card_nsmul s g (g j) (fun x a ↦ p x a)


lemma Finset.exists_le_expect.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  [PosSMulMono ℚ≥0 α] {s : Finset ι} {f : ι → α} (hs : s.Nonempty) :
    ∃ x ∈ s, s.expect f ≤ f x := by
  by_contra h
  push_neg at h
  obtain ⟨m, ⟨ms, mmin⟩⟩ := Finset.exists_max_image s f hs
  obtain ⟨z, ⟨zs, mltz⟩⟩ := Finset.exists_lt_of_lt_expect hs (h m ms)
  exact not_lt_of_le (mmin z zs) mltz

open scoped ENNReal

lemma Fin.exists_mul_of_sum_bound [Nonempty (Fin r)] (g : Fin r → ℝ≥0∞) : ∃ j, ∑ i, g i ≤ r * g j := by
  have := Fintype.exists_mul_of_sum_bound g
  simp only [Fintype.card_fin, nsmul_eq_mul] at this
  assumption

----------------------------------------------------------------------------------------------------
-- probabilistic method


lemma probabilistic_method {X : Type} [Fintype X] [MeasurableSpace X] (U : Measure X) (p : X → X → Prop) [∀ i j, Decidable (p j i)] :
    (0 : ℝ≥0∞) < (U.prod U) { x : X × X | p x.1 x.2 } → ∃ x : X, ∃ x' : X , p x x' := by
      intro a
      by_contra c
      simp_all only [not_exists, not_and, coe_mem, ite_false, integral_zero, Set.setOf_false, measure_empty, lt_self_iff_false]


lemma pidgeon_sum {X Y : Type} [nenx: Nonempty X] [fin: Fintype X] [nen: Nonempty Y] [fin: Fintype Y]
    (p : X → Y → Prop) [∀ i j, Decidable (p i j)] {β : Real} :
    β ≤ ((Fintype.card ↑{x : X × Y | p x.1 x.2}) : ℝ) / ((Fintype.card (X × Y)) : ℝ) →
    ∃ x : X, ∃ Y' : Finset Y, β * (Fintype.card Y) ≤ ((Y'.card) : ℝ) ∧ ∀ y ∈ Y', p x y := by

  intros bound
  let f := fun x ↦ (# { y : Y | p x y} : ℝ)

  have card_sum : ∑ i : X, f i = Fintype.card {x : X × Y // p x.1 x.2} := by
    have := Fintype.sum_prod_type' (fun i j ↦ if p i j then 1 else 0)
    rw [Fintype.card_subtype, Finset.card_filter, this]
    simp only [sum_boole, Nat.cast_id, Nat.cast_sum, f]

  have : β * ↑(Fintype.card Y) ≤ univ.expect f := by
    rw [expect_eq_sum_div_card, card_univ, card_sum, ← le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos),
      ← div_mul_eq_div_div, ← Nat.cast_mul, ← Fintype.card_prod]
    exact bound

  obtain ⟨x, ⟨_, bx⟩⟩ : ∃ x ∈ univ, univ.expect f ≤ f x :=
    Finset.exists_le_expect (univ_nonempty_iff.mpr nenx)

  use x
  use ({y : Y | p x y} : Finset Y)

  constructor
  · exact le_trans this bx
  · simp only [mem_filter, mem_univ, true_and, imp_self, implies_true]


lemma pidgeon_thing {X Y : Type} [Nonempty X] [Fintype X] [Nonempty Y] [Fintype Y]
    [MeasurableSpace (X × Y)] [MeasurableSingletonClass (X × Y)]
    (p : X × Y → Prop) [∀ i, Decidable (p i)] {β : Real} :
    let U := (PMF.uniformOfFintype (X × Y)).toMeasure
    ENNReal.ofReal β ≤ (U { x : X × Y | p x }) →
    ∃ x : X, ∃ Y' : Finset Y, β * (Fintype.card Y) ≤ (Y'.card) ∧ ∀ y ∈ Y', p ⟨x, y⟩ := by
  intro U bound

  simp [U, PMF.toMeasure_uniformOfFintype_apply { x : X × Y | p x } (Set.Finite.measurableSet (Set.toFinite {x | p x}))] at bound
  rw [ENNReal.ofReal_le_iff_le_toReal, ← Nat.cast_mul, ← Fintype.card_prod] at bound

  · simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at bound
    exact pidgeon_sum (fun x y ↦ p ⟨x, y⟩) (by convert bound) -- TODO convert needed because of a mathlib issue: PR https://github.com/leanprover-community/mathlib4/pull/24074

  · have nz : (Fintype.card X : ENNReal) * (Fintype.card Y) ≠ 0 := by simp
    convert ne_of_lt (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) nz) -- same


----------------------------------------------------------------------------------------------------

-- TODO i just put here everything that annoyed me
lemma omg {a b : ℝ} (p : b ≠ 0) : a = a / b * b := by
  have := invertibleOfNonzero p
  exact (div_mul_cancel_of_invertible a b).symm
lemma omg2 {a b c : ℝ} (p : b ≠ 0) : a ≤ c ↔ a / b ≤ c / b := by sorry
lemma omg3 {a b : ℝ} (p : b ≠ 0) : a = a * b / b := (mul_div_cancel_right₀ a p).symm
lemma omg4 {a b c : ℝ} (bnn : 0 ≤ b) : a ≤ c ↔ a * b ≤ c * b := by sorry
lemma omg5 {a b c : ℝ≥0∞} : b ≤ c ↔ a * b ≤ a * c := by sorry
lemma omg6 {a b : ℝ} : - a ≤ a * b ↔ -1 ≤ b := by
  sorry
