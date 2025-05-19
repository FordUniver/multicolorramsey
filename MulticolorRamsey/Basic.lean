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

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Group.Indicator
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay


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
section
open MeasureTheory ProbabilityTheory Finset Real

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

end

----------------------------------------------------------------------------------------------------
-- special function lemma

noncomputable def coshsqrt (x : ℝ) :=  ∑' n : ℕ , (x ^ n / (2 * n).factorial)

lemma mew {x} (xpos: (0 : ℝ) ≤ ↑x) : Summable (fun n ↦ (x ^ n / (2 * n).factorial)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (Real.summable_pow_div_factorial x)
    all_goals intro b
    positivity
    refine div_le_div₀ (pow_nonneg xpos b) (Preorder.le_refl (x ^ b)) (by positivity) ?_
    exact Nat.cast_le.mpr (Nat.factorial_le (by linarith))

lemma le_coshsqrt (x : ℝ) (xnn : 0 ≤ x) : x ≤ 2 + coshsqrt x := by
  have : coshsqrt x = 1 + x / 2 + x ^ 2 / ↑(4).factorial + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial := by
    simp [coshsqrt, ← Summable.sum_add_tsum_nat_add 3 (mew xnn), Finset.sum, add_comm]
  simp [this]
  have spos : 0 ≤ ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial := tsum_nonneg (by intro; positivity)
  have : 2 + (1 + x / 2 + x ^ 2 / ↑(Nat.factorial 4) + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial) = (3 + x / 2 + x ^ 2 / ↑(Nat.factorial 4)) + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial := by ring
  simp [this]
  suffices x ≤ 3 + x / 2 + x ^ 2 / 24 from le_add_of_le_of_nonneg this spos
  nlinarith

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

section
open MeasureTheory ProbabilityTheory Finset Real

lemma Fintype.exists_mul_of_sum_bound [Nonempty X] [Fintype X] [AddCommMonoid Y] [LinearOrder Y] [IsOrderedAddMonoid Y] (g : X → Y) :
    ∃ j, ∑ i, g i ≤ (Fintype.card X) • g j := by
  obtain ⟨j, p⟩ : ∃ j, ∀ i, g i ≤ g j := Finite.exists_max g
  use j
  calc ∑ i : X, g i ≤ ∑ i : X, g j           := by exact sum_le_sum fun i a ↦ p i
                  _ = (Fintype.card X) • g j := by simp only [sum_const, card_univ, nsmul_eq_mul]

lemma Finset.exists_mul_of_sum_bound [Nonempty X] [Fintype X] [AddCommMonoid Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
    (s : Finset X) (g : X → Y) (ns : s.Nonempty) :
    ∃ j ∈ s, ∑ i ∈ s, g i ≤ (#s) • g j := by
  obtain ⟨j, ⟨js, p⟩⟩ := exists_max_image s g ns
  use j
  use js
  exact sum_le_card_nsmul s g (g j) (fun x a ↦ p x a)


lemma Finset.exists_le_expect.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  [PosSMulMono ℚ≥0 α] {s : Finset ι} {f : ι → α} (hs : s.Nonempty) :
    ∃ x ∈ s, s.expect f ≤ f x := by
  by_contra h
  push_neg at h
  obtain ⟨m, ⟨ms, mmin⟩⟩ := exists_max_image s f hs
  obtain ⟨z, ⟨zs, mltz⟩⟩ := exists_lt_of_lt_expect hs (h m ms)
  exact not_lt_of_le (mmin z zs) mltz

open scoped ENNReal

lemma Fin.exists_mul_of_sum_bound [Nonempty (Fin r)] (g : Fin r → ℝ≥0∞) : ∃ j, ∑ i, g i ≤ r * g j := by
  have := Fintype.exists_mul_of_sum_bound g
  simp only [Fintype.card_fin, nsmul_eq_mul] at this
  assumption

end
----------------------------------------------------------------------------------------------------
-- probabilistic method

section
open MeasureTheory ProbabilityTheory Finset Real ENNReal

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

end


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
    exact pidgeon_sum (fun x y ↦ p ⟨x, y⟩) bound

  · have nz : (Fintype.card X : ENNReal) * (Fintype.card Y) ≠ 0 := by simp
    exact ne_of_lt (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) nz)

----------------------------------------------------------------------------------------------------
-- integral of rexp (-√x) * (1 / (2 * √x))

section

open MeasureTheory ProbabilityTheory Real ENNReal Set

lemma integrableOn_one_div_two_mul_sqrt {m : ℝ} : IntegrableOn (fun x ↦ 1 / (2 * √x)) (Icc 0 m) := by
  have : (∀ x ∈ Ioo 0 m, HasDerivAt (fun x ↦ √x) ((fun x ↦ 1 / (2 * √ x)) x) x) := by
    intros x xi
    refine (hasDerivAt_id' x).sqrt ?_
    by_contra h
    rw [h] at xi
    exact left_mem_Ioo.mp xi
  apply integrableOn_Icc_iff_integrableOn_Ioc.mpr

  exact intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_id' _).sqrt this (by intros; positivity)


lemma integrableOn_exp_neg_sqrt : IntegrableOn (fun x ↦ rexp (-√x) * (1 / (2 * √x))) (Ioi 0) ℙ := by

  have i0 : IntegrableOn (fun x ↦ rexp (-√x) * (1 / (2 * √x))) (Ioc 0 1) ℙ := by
    apply integrableOn_Icc_iff_integrableOn_Ioc.mp
    exact IntegrableOn.continuousOn_mul (continuousOn_id' _).sqrt.neg.rexp integrableOn_one_div_two_mul_sqrt isCompact_Icc

  have i1 : IntegrableOn (fun x ↦ rexp (-√x) * (1 / (2 * √x))) (Ioi 1) ℙ := by
    have {m : ℝ} (mp : 0 < m) : IntegrableOn (fun (x : ℝ) ↦ x ^ (-(1.5 : ℝ))) (Ioi m) ℙ :=
      integrableOn_Ioi_rpow_of_lt (show -(1.5 : ℝ) < -1 by linarith) mp

    refine integrable_of_le_of_le ?_ ?_ ?_ (integrable_zero _ _ _) (this (by positivity))
    · have := (measurable_exp.comp continuous_sqrt.measurable.neg).mul ((continuous_sqrt.measurable.const_mul 2).const_div 1)
      exact this.stronglyMeasurable.aestronglyMeasurable
    all_goals {
      have s1 : {a | 1 < a ∧ rexp (-√a) * (1 / (2 * √a)) ≤ 0} = ∅ := by ext x; simp; intro; positivity
      have s2 : {a | 1 < a ∧ a ^ (-(1.5 : ℝ)) ≤ rexp (-√a) * (1 / (2 * √a))} = ∅ := by
        ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]; intro
        have : √x ^ 2 / 2 < rexp √x := lt_of_lt_of_le (by linarith [sqrt_pos.mpr (by positivity)]) (quadratic_le_exp_of_nonneg (by positivity))
        simp only [sq_sqrt] at this
        have := (inv_lt_inv₀ (by positivity) (by positivity)).mpr this
        have xpos : 0 < x := by positivity
        have pow_recip_sqrt_cubed : ((√x)⁻¹) ^ 3 = x ^ (-(1.5 : ℝ)) := by
          rw [sqrt_eq_rpow, ← Real.rpow_neg_one, ← rpow_mul (le_of_lt xpos), ← Real.rpow_natCast, ← rpow_mul (le_of_lt xpos)]
          norm_num
        rw [← pow_recip_sqrt_cubed, exp_neg, show (√x)⁻¹ ^ 3 = (√x ^ 2 / 2)⁻¹ * (1 / (2 * √x)) by ring]
        exact (mul_lt_mul_iff_of_pos_right (show 0 < (1 / (2 * sqrt x)) by positivity)).mpr this

      refine ae_le_of_ae_lt (ae_iff.mpr ?_)
      simp only [not_lt, measurableSet_Ioi, Measure.restrict_apply', setOf_inter_eq_sep, mem_Ioi]
      simp only [s1, s2, OuterMeasureClass.measure_empty]
    }

  convert i0.union i1
  symm
  exact Ioc_union_Ioi_eq_Ioi (by positivity)


lemma integral_exp_neg_sqrt : ∫ (x : ℝ) in Ioi 0, rexp (-√x) * (1 / (2 * √x)) = 1 := by

  nth_rewrite 2 [integral_exp_neg_Ioi_zero.symm]
  have := @MeasureTheory.integral_comp_mul_deriv_Ioi (fun x ↦ √x) (fun x ↦ 1 / (2 * √ x)) (fun x ↦ rexp (-x)) 0
  simp only [mem_Ioi, Function.comp_apply,sqrt_zero] at this
  refine this ?_ ?_ ?_ ?_ ?_ ?_
  exact continuous_sqrt.continuousOn
  · refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b; use b^2; intro a ab
    exact le_sqrt_of_sq_le ab
  · intro x xpos
    apply HasDerivWithinAt.sqrt
    exact (hasDerivWithinAt_id x _)
    exact Ne.symm (ne_of_lt xpos)
  · exact (continuous_id.neg).rexp.continuousOn
  · have : (fun x ↦ √x) '' Ici 0 = Ici 0 := by
      ext b
      constructor
      · simp only [mem_image, mem_Ici, forall_exists_index, and_imp]; intro x xpos xe; simp [← xe]
      · simp; intro bpos; use b^2; simp [bpos]
    rw [this]
    have := integrableOn_Ici_iff_integrableOn_Ioi.mpr (exp_neg_integrableOn_Ioi 0 zero_lt_one)
    simpa only [neg_mul, one_mul]
  exact integrableOn_Ici_iff_integrableOn_Ioi.mpr integrableOn_exp_neg_sqrt

end

----------------------------------------------------------------------------------------------------

section

open Set Finset

lemma Fintype.argmax' {X Y : Type} [Fintype X] [Nonempty X] (f : X → Y) [LinearOrder Y] :
    ∃ x : X, ∀ y : X, f y ≤ f x := by
  let ⟨x, ⟨_, p⟩⟩ := mem_image.mp (max'_mem (image f univ) (image_nonempty.mpr univ_nonempty))
  use x
  intro y
  convert le_max' (image f univ) (f y) (mem_image.mpr ⟨y, ⟨mem_univ y, rfl⟩⟩)

lemma maxUnion {X Y : Type} [Fintype X] [Nonempty X] [LinearOrder X] (τ : Y → X → ℝ) (nen: ∀ x, (Finset.image (τ x) univ).Nonempty)  :
    {x | Λ ≤ max' (univ.image (τ x)) (nen x)} = ⋃ i, { x | Λ ≤ τ x i} := by
  ext x
  constructor
  · simp only [mem_setOf_eq, mem_iUnion]
    intro mx
    obtain ⟨i, j⟩ := Fintype.argmax' (τ x)
    use i
    trans (Finset.image (τ x) univ).max' (nen x)
    exact mx
    simp [j]
  · simp only [mem_iUnion, mem_setOf_eq, forall_exists_index]
    intros i mi
    refine le_trans mi (le_max' _ _ ?_)
    simp

end

----------------------------------------------------------------------------------------------------

-- TODO i just put here everything that annoyed me
lemma omg {a b : ℝ} (p : b ≠ 0) : a = a / b * b := by
  have := invertibleOfNonzero p
  exact (div_mul_cancel_of_invertible a b).symm
lemma omg2 {a b c : ℝ} (p : b ≠ 0) : a ≤ c ↔ a / b ≤ c / b := by sorry
lemma omg3 {a b : ℝ} (p : b ≠ 0) : a = a * b / b := (mul_div_cancel_right₀ a p).symm
lemma omg4 {a b c : ℝ} (bnn : 0 ≤ b) : a ≤ c ↔ a * b ≤ c * b := by sorry
lemma omg5 {a b c : ENNReal} : b ≤ c ↔ a * b ≤ a * c := by sorry
lemma omg6 {a b : ℝ} : - a ≤ a * b ↔ -1 ≤ b := by
  sorry
