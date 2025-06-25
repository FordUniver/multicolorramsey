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

noncomputable def coshsqrt (x : ℝ) :=  ∑' n : ℕ , (x ^ n / ((2 * n).factorial : ℝ))

lemma monotone_coshsqrt : MonotoneOn coshsqrt (Set.Ici 0) := sorry

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
  have : 2 + (1 + x / 2 + x ^ 2 / ↑(Nat.factorial 4) + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial) =
      (3 + x / 2 + x ^ 2 / ↑(Nat.factorial 4)) + ∑' (i : ℕ), x ^ (i + 3) / ↑(2 * (i + 3)).factorial := by ring
  simp [this]
  suffices x ≤ 3 + x / 2 + x ^ 2 / 24 from le_add_of_le_of_nonneg this (tsum_nonneg (by intro; positivity))
  nlinarith

section

open Real

----------------------------------------------------------------------------------------------------
--idk mathlib?

theorem tsum_even_nat [TopologicalSpace T] [AddCommMonoid T] (f : Nat → T) :
    ∑' (x : {n : ℕ | Even n}), f x = ∑' (x : ℕ), f (2 * x) := by
  rw [← Equiv.tsum_eq (Equiv.ofBijective (fun n : {n : ℕ | Even n} => (n : ℕ) / 2) ?_)]
  · congr; ext x; congr; simp; exact (Nat.two_mul_div_two_of_even (x.prop)).symm
  · constructor
    · rintro ⟨_, hn⟩ ⟨_, hm⟩ h
      simp_all [Nat.even_iff, Nat.div_eq_of_lt]
      exact (Nat.div_left_inj (even_iff_two_dvd.mp hn) (even_iff_two_dvd.mp hm)).mp h
    · intro n
      exact ⟨⟨2 * n, (by simp)⟩, by simp⟩

----------------------------------------------------------------------------------------------------

lemma ge_coshsqrt (x : ℝ) (xnn : 0 ≤ x) : 2 + coshsqrt x ≤ 3 * Real.exp √x := by
  have : coshsqrt x ≤ rexp √x := by
    simp [coshsqrt, Real.exp_eq_exp_ℝ, NormedSpace.exp, NormedSpace.expSeries_sum_eq_div]
    have : ∑' (a : ℕ), ENNReal.ofReal (x ^ a / ↑(2 * a).factorial) ≤ ∑' (a : ℕ), ENNReal.ofReal (√x ^ a / ↑a.factorial) := by
      nth_rw 2 [← Summable.tsum_add_tsum_compl (s := { n : ℕ | Even n}) (by simp) (by simp)]
      rw [tsum_even_nat (fun n ↦ ENNReal.ofReal (√x ^ n / (n : ℕ).factorial))]
      simp_rw [pow_mul, Real.sq_sqrt xnn]
      exact le_self_add
    rw [← ENNReal.ofReal_tsum_of_nonneg] at this
    rw [← ENNReal.ofReal_tsum_of_nonneg] at this
    rw [← ENNReal.ofReal_le_ofReal_iff]
    exact this
    · positivity
    · intro; positivity
    · exact Real.summable_pow_div_factorial √x
    · intro; positivity
    · exact mew xnn

  have : 2 ≤ 2 * rexp √x := by linarith [one_le_exp (sqrt_nonneg x)]
  linarith

lemma icc_coshsqrt (x : ℝ) (xnn : x < 0) : coshsqrt x ∈ Set.Icc (-1) 1 := by sorry

lemma coshsqrt_pos {x : ℝ} : 0 ≤ 2 + coshsqrt x := by
  by_cases xnn : 0 ≤ x
  · exact le_trans xnn (le_coshsqrt x xnn)
  · have := Set.mem_Icc.mp (icc_coshsqrt x (lt_of_not_le xnn))
    linarith

lemma coshsqrt_m1 (x : ℝ) : 0 ≤ 2 + coshsqrt x := sorry


noncomputable def f (x : Fin r → ℝ) : ℝ :=
  ∑ j : Fin r, x j * (1 / (2 + coshsqrt (x j))) * (∏ i : Fin r, (2 + coshsqrt (x i)))

lemma f_ge (x : Fin r → ℝ) : (∏ i : Fin r, (x i)) ≤ f x := by
  have :  ∏ i : Fin r, x i ≤ ∏ i : Fin r, (2 + coshsqrt (x i)) := sorry
  sorry

lemma specialFunctionE (x : Fin r → ℝ) (_ :  ∀ i, -3 * r ≤ x i) :
    f x ≤ 3^r * r * Real.exp (∑ i, Real.sqrt (x i + 3 * r)) := by
  simp only [f]
  rw [← Finset.sum_mul]

  trans  (∑ i : Fin r, 1) * ∏ i, (2 + coshsqrt (x i))
  gcongr
  have : ∀ i, 0 ≤ (2 + coshsqrt (x i)) := sorry
  exact Finset.prod_nonneg fun i a ↦ this i

  expose_names
  by_cases hh : 0 < x i
  · trans x i * (x i)⁻¹
    gcongr
    ring_nf
    have : x i ≤ (2 + coshsqrt (x i)) := le_coshsqrt _ (le_of_lt hh)
    exact (inv_le_inv₀ (lt_of_lt_of_le hh this) hh).mpr this
    exact mul_inv_le_one
  · by_cases hhh : x i = 0
    · rw [hhh]
      simp
    · trans x i * (1 / (2 + (-1)))
      sorry
      ring_nf
      exact le_trans (le_of_not_lt hh) zero_le_one

  trans  (∑ i : Fin r, 1) * ∏ i, (2 + coshsqrt (x i + 3 * r))
  gcongr
  intros
  exact coshsqrt_pos
  expose_names
  have : 0 ≤ x i + 3 * ↑r := by trans -3 * r + 3 * r; field_simp; exact add_le_add_right (h i) (3 * ↑r)
  by_cases 0 ≤ x i
  · sorry
  · sorry

  trans  (∑ i : Fin r, 1) * ∏ i, 3 * Real.exp √(x i + 3 * r)
  gcongr
  · intros; exact coshsqrt_pos
  · refine ge_coshsqrt ?_ ?_
    sorry

  simp
  rw [Real.exp_sum, Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc]
  ring_nf; gcongr
  exact Nat.one_le_ofNat
  exact card_finset_fin_le Finset.univ

lemma specialFunctionEc (x : Fin r → ℝ) (_ :  ∃ i, x i < -3 * r) :
    f x ≤ -1 := sorry

end
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

section
--TODO maybe mathlib

open Set Finset

lemma prod_set_eq_union {X Y : Type} (f : X × Y → Prop) : {a | f a} = ⋃ x, {x} ×ˢ {y : Y | f (x, y)} := by
  ext ⟨x, y⟩
  simp only [mem_setOf_eq, mem_iUnion, mem_prod, mem_singleton_iff, exists_eq_left']

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

section

open Real

lemma sum_sqrt_le {r : ℕ} {X : Type*} [Fintype X] [nenr: Nonempty (Fin r)] {τ : X → Fin r → ℝ} {x : X} :
    let M := fun x ↦ (Finset.image (τ x) (Finset.univ : Finset (Fin r))).max' (Finset.Nonempty.image Finset.univ_nonempty (τ x))
    ∑ i, √(3 * ↑r * τ x i + 3 * ↑r) ≤ ↑r * (√3 * √↑r) * √((M x) + 1) := by
  intro M
  have (i : Fin r) : √(3 * ↑r * τ x i + 3 * ↑r) ≤ √(3 * ↑r * (M x) + 3 * ↑r) := by
    apply Real.sqrt_le_sqrt
    have : τ x i ≤ M x := by
      apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    nlinarith
  convert Finset.sum_le_sum fun i _ => this i
  simp [mul_assoc, ← mul_add]
  repeat rw [← sqrt_mul (Nat.cast_nonneg' r)]
  left; ring_nf

end


-- lemma three_ineq_ENN {r : ℕ} (rpos: 0 < r) : r * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * 3 ^ r * 3 +
--       r ^ 2 * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * ENNReal.ofReal (r * √3 * √r) * 3 ^ r * 3 ≤
--     1 := by
--   suffices r * (3 ^ (-((r : ℝ) * 4))) * 3 ^ r * 3 + r ^ 2 * (3 ^ (-((r : ℝ) * 4))) * (r * √3 * √r) * 3 ^ r * 3 ≤ 1 from sorry

--   have : 3 ^ (-((r : ℝ) * 4)) * (3 : ℝ) ^ (r : ℝ) = 3 ^ (- (r : ℝ) * 3) := by rw [← rpow_add zero_lt_three]; ring_nf
--   have ee : (3 ^ (-((r : ℝ) * 4))) * (3 : ℝ) ^ r * 3 = 3 ^ (- (r : ℝ) * 3) * 3 := by congr; convert this; norm_cast
--   have : (3 : ℝ) ^ (- (r : ℝ) * 3) * 3 = 3 ^ (- (r : ℝ) * 3 + 1) := by rw [← rpow_add_one]; exact (NeZero.ne' 3).symm
--   rw [this] at ee
--   simp_rw [ee]

--   have : r * r * √3 * √r + 1 ≤ r * r * √r * 3 := by
--     suffices 1 ≤ (3 - √3) * (r * (r * √r)) from by linarith
--     have o : 1 ≤ (3 - √3) := by nlinarith [sq_sqrt (zero_le_three)]
--     have t : 1 ≤ r * (r * √r) := by
--       nlinarith [sq_sqrt (le_trans zero_le_one (show 1 ≤ (r : ℝ) by sorry)),
--         show 0 < r * (r * √r) by positivity,
--         sq_nonneg (r - 1), sq_nonneg (√r - 1)]
--     exact one_le_mul_of_one_le_of_one_le o t


--   suffices h : (3 * 3 ^ (- r * 3) * r) * (r * r * √r * 3) ≤ 1 from le_trans (mul_le_mul_of_nonneg_left this (by positivity)) h

--   have : 3 * 3 ^ (- r * 3) * r * (r * r * √r * 3) ≤ 3 ^ (- r * 5) * 3 := by
--     have : 3 * 3 ^ (- r * 3) * r * (r * r * √r * 3) = (r * √3 ^ (-r)) ^ (7/2) * 3 ^ (- r * 5) * 3 := by sorry
--     rw [this]
--     have : (r / √3 ^ r) ^ (7/2) ≤ 1 := sorry
--     have : (r / √3 ^ r) ^ (7 / 2) * 3 ^ (-r * 5) ≤ 3 ^ (-r * 5) := mul_le_of_le_one_left (by positivity) this
--     sorry

--   trans 3 ^ (-(5 : ℝ)) * 3
--   trans 3 ^ (-r * 5) * 3
--   exact this
--   simp [rpos]
--   ring_nf; linarith


lemma three_ineq_ENN {r : ℕ} (rpos: 0 < r) : r * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * 3 ^ r * 3 +       r ^ 2 * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * ENNReal.ofReal (r * √3 * √r) * 3 ^ r * 3 ≤     1 := by sorry

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

lemma omg7 (a b c : ENNReal) (ab : a < b) (ac : a < c) (bc : b < c) : c - b < c - a := by sorry
