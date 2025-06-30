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


import Canonical

section

open MeasureTheory ProbabilityTheory Real ENNReal Set


theorem ae_le_of_forallOn_le {f : α → ℝ} {s : Set α}  [MeasurableSpace α] {μ : Measure α} (ms : MeasurableSet s) (h₁ : ∀ x ∈ s, g x ≤ f x) :
    g ≤ᶠ[ae (μ.restrict s)] f := by
      filter_upwards [ae_restrict_mem ms] with x hx using h₁ x hx

-- maybe mathlib
lemma indicator_one_mul {x : X} [MulZeroOneClass Y] (f : X → Y) [MeasurableSpace X] (E : Set X) :
    f x * E.indicator 1 x = E.indicator f x := by
  by_cases hx : x ∈ E <;> simp [hx]

lemma IntegrableFin {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] {ℙᵤ : Measure X} [IsFiniteMeasure ℙᵤ] {f : X → ℝ} :
  Integrable f ℙᵤ := ⟨ AEStronglyMeasurable.of_discrete , HasFiniteIntegral.of_finite ⟩


----------------------------------------------------------------------------------------------------
-- integral of rexp (-√x) * (1 / (2 * √x))

lemma bounded_thingy_on_s {f g h : ℝ → ℝ} (ms : MeasurableSet s) (Ih : IntegrableOn h s) (Ig : IntegrableOn g s)
    (dh : ∀ x ∈ s, h x ≤ f x) (dg : ∀ x ∈ s, f x ≤ g x) (mf : Measurable f) : IntegrableOn f s :=
  integrable_of_le_of_le (mf.aestronglyMeasurable) (ae_le_of_forallOn_le ms dh) (ae_le_of_forallOn_le ms dg) Ih Ig

lemma integrableOn_one_div_two_mul_sqrt_plus (m : ℝ) (c : ℝ) : IntegrableOn (fun x ↦ 1 / (2 * √(x + c))) (Icc (-c) m) := by
  have : (∀ x ∈ Ioo (-c) m, HasDerivAt (fun x ↦ √(x + c)) ((fun x ↦ 1 / (2 * √(x + c))) x) x) := by
    intros x xi
    have := ((hasDerivAt_id' x).add (hasDerivAt_const x c)).sqrt (by linarith [mem_Ioo.mp xi])
    simpa only [one_div, mul_inv_rev, add_zero]
  apply integrableOn_Icc_iff_integrableOn_Ioc.mpr

  exact intervalIntegral.integrableOn_deriv_of_nonneg ((continuousOn_id' _).add continuousOn_const).sqrt this (by intros; positivity)

lemma continuousOn_add_const : ContinuousOn (fun (x : ℝ) ↦ (x + c)) s := ((continuousOn_id' _).add continuousOn_const)

lemma intOn1 {m : ℝ} : IntegrableOn (fun x ↦ 1 / (2 * √(x + 1))) (Ioc (-1) m) := by
  apply integrableOn_Icc_iff_integrableOn_Ioc.mp
  exact integrableOn_one_div_two_mul_sqrt_plus m 1

lemma improper_integral_shift (c : ℝ) (f : ℝ → ℝ) (cf : ContinuousOn f (Ioi 0))
    (If : IntegrableOn f (Ici 0) ℙ) (Iif : IntegrableOn (fun x ↦ f (x + c)) (Ici (-c)) ℙ) :
    ∫ (x : ℝ) in Ioi (-c), f (x + c) = ∫ (x : ℝ) in Ioi 0, f x := by
  have deriv (x : ℝ) (_ : x ∈ Ioi (-c)) : HasDerivWithinAt (fun x ↦ x + c) ((fun x ↦ 1) x) (Ioi x) x := by
    simp; exact hasDerivWithinAt_id x (Ici x)
  have := integral_comp_mul_deriv_Ioi continuousOn_add_const (Filter.tendsto_atTop_add_const_right _ _ fun ⦃U⦄ a ↦ a)
      deriv
      (by simpa)
      (by simpa)
      (by simpa)
  simpa [this]

-- https://github.com/leanprover-community/mathlib4/pull/25045
lemma integrableOn_pow {m a c : ℝ} (mp : 0 < m) (ha : a < -1) (cp : 0 ≤ c) : IntegrableOn (fun (x : ℝ) ↦ (x + c) ^ a) (Ioi m) ℙ := by
  have hd : ∀ x ∈ Ici m, HasDerivAt (fun t => (t + c) ^ (a + 1) / (a + 1)) ((x + c) ^ a) x := by
    intro x hx
    convert (((hasDerivAt_id _).add_const c).rpow_const _).div_const (a + 1) using 1
    field_simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
    simp_all; left; have := (lt_of_lt_of_le mp hx); exact ne_of_gt (by linarith)

  have ht : Filter.Tendsto (fun t => ((t + c) ^ (a + 1)) / (a + 1)) Filter.atTop (nhds (0 / (a + 1))) := by
    refine Filter.Tendsto.div_const ?_ (a + 1)
    have := tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
    simp [neg_neg] at this

    have :
      Filter.Tendsto (fun t : ℝ => (t + c : ℝ) ^ (a + 1)) Filter.atTop (nhds 0) =
      Filter.Tendsto ((fun x : ℝ => x ^ (a + 1)) ∘ fun t : ℝ => (t + c : ℝ)) Filter.atTop (nhds 0) := by simp [add_assoc]; rfl
    rw [this]
    apply Filter.Tendsto.comp
    assumption
    exact Filter.tendsto_atTop_add_const_right _ c (fun ⦃U⦄ a ↦ a)

  exact integrableOn_Ioi_deriv_of_nonneg' hd (fun t ht => rpow_nonneg (by linarith [gt_trans ht mp]) a) ht

lemma measEsqc : Measurable fun x ↦ rexp (d * √(x + 1)) * (c * (1 / (2 * √(x + 1)))) := by
  have : Measurable fun x ↦  √(id x + 1) := (continuous_id.add continuous_const).sqrt.measurable
  exact (measurable_exp.comp (this.const_mul d)).mul (((this.const_mul 2).const_div 1).const_mul c)

lemma integrableOn_exp_neg_sqrt_plus {c : ℝ} (cn : 0 ≤ c) : IntegrableOn (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) (Ioi (-c)) ℙ := by

  have i0 : IntegrableOn (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) (Ioc (-c) 1) ℙ := by
    apply integrableOn_Icc_iff_integrableOn_Ioc.mp
    refine IntegrableOn.continuousOn_mul ?_ ?_ isCompact_Icc
    exact continuousOn_add_const.sqrt.neg.rexp
    exact integrableOn_one_div_two_mul_sqrt_plus _ c

  have i1 : IntegrableOn (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) (Ioi 1) ℙ := by
    have mf : Measurable (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) :=
        have := (continuous_id.add continuous_const).sqrt.measurable
        (measurable_exp.comp this.neg).mul ((this.const_mul 2).const_div 1)
    have Ig : IntegrableOn (fun x ↦ (x + c) ^ (-(1.5 : ℝ))) (Ioi 1) := (integrableOn_pow zero_lt_one (by linarith : -(1.5 : ℝ) < -1) cn)
    refine bounded_thingy_on_s measurableSet_Ioi (integrable_zero _ _ _) Ig ?_ ?_ mf

    all_goals intros x ax
    positivity

    simp only [mem_Ioi] at ax
    have xcn : 0 < x + c := by positivity
    have xpos : 0 < x := by positivity
    have pow_recip_sqrt_cubed (x : ℝ) (xpos : 0 < x) : ((√x)⁻¹) ^ 3 = x ^ (-(1.5 : ℝ)) := by
      rw [sqrt_eq_rpow, ← Real.rpow_neg_one, ← rpow_mul (le_of_lt xpos), ← Real.rpow_natCast, ← rpow_mul (le_of_lt xpos)]
      norm_num
    have moo : (√(x + c))⁻¹ ^ 3 = (√(x + c) ^ 2 / 2)⁻¹ * (1 / (2 * √(x + c))) := by
      have (x : ℝ) (xp : 0 < x) : (√x)⁻¹ ^ 3 = (√x ^ 2 / 2)⁻¹ * (1 / (2 * √x)) := by ring
      exact this (x + c) xcn
    rw [← pow_recip_sqrt_cubed (x + c) xcn, exp_neg, moo]

    have : √(x + c) ^ 2 / 2 < rexp √(x + c) := lt_of_lt_of_le (by linarith [sqrt_pos.mpr xcn]) (quadratic_le_exp_of_nonneg (by positivity))
    simp only [sq_sqrt] at this
    have := (inv_lt_inv₀ (by positivity) (by positivity)).mpr this
    exact le_of_lt ((mul_lt_mul_iff_of_pos_right (show 0 < (1 / (2 * sqrt (x + c))) by positivity)).mpr this)

  convert i0.union i1
  symm
  exact Ioc_union_Ioi_eq_Ioi (le_trans (Right.neg_nonpos_iff.mpr cn) zero_le_one)

lemma intEsqc (c : ℝ) : IntegrableOn (fun x ↦ rexp (- √(x + 1)) * (c * (1 / (2 * √(x + 1))))) (Ioi (-1)) := by
    have := (integrableOn_exp_neg_sqrt_plus (zero_le_one)).mul_const c
    simpa [mul_comm c, mul_assoc]


lemma integrableOn_exp_neg_sqrt : IntegrableOn (fun x ↦ rexp (-√x) * (1 / (2 * √x))) (Ioi 0) ℙ := by
  have := integrableOn_exp_neg_sqrt_plus (Preorder.le_refl 0)
  simpa

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
  have : IntegrableOn (fun x ↦ rexp (-√x) * (1 / (2 * √x))) (Ioi 0) ℙ := by
    have := integrableOn_exp_neg_sqrt_plus (Preorder.le_refl 0)
    simpa
  exact integrableOn_Ici_iff_integrableOn_Ioi.mpr this

lemma terriblel (c : ℝ) : ∫ a in Ioi (-1), (rexp (- √(a + 1)) *  (c * (1 / (2 * √(a + 1))))) = c := by
  have := improper_integral_shift 1 (fun a ↦ rexp (-√a) * (c * (1 / (2 * √a)))) ?_ ?_ ?_
  simp only [this]
  have := congrArg (HMul.hMul c) integral_exp_neg_sqrt
  simp only [← integral_const_mul c, mul_one] at this
  nth_rw 2 [← this]
  congr; ext; linarith

  have : ContinuousOn (fun x ↦ 1 / 2 • √x) (Ioi 0) :=
    continuousOn_const.div ((continuousOn_id' _).sqrt.const_smul 2) (by simp [sqrt_ne_zero'])
  have := (continuousOn_id' _).sqrt.neg.rexp.mul (this.const_smul c)
  simpa only [nsmul_eq_mul, smul_eq_mul]
  -- TODO what how to all_goals and then stop again
  all_goals have (a : ℝ) : rexp (-√a) * (c * (1 / (2 * √a))) = (rexp (-√a) * (1 / (2 * √a))) * c := by ring
  all_goals simp_rw [this]
  all_goals apply integrableOn_Ici_iff_integrableOn_Ioi.mpr
  · exact (integrableOn_exp_neg_sqrt).smul_const c
  · exact ((integrableOn_exp_neg_sqrt_plus zero_le_one).smul_const c)

-- TODO can probably have this nicer with direct lebesge
lemma terrible (c : ENNReal) (cnt : c ≠ ⊤) :
    ∫⁻ a in Ioi (-1), ENNReal.ofReal (rexp (- √(a + 1)) * (c.toReal * (1 / (2 * √(a + 1))))) = c := by
  apply (toReal_eq_toReal _ cnt).mp

  rw [← integral_eq_lintegral_of_nonneg_ae, terriblel]
  · filter_upwards; intro; positivity
  · apply Measurable.aestronglyMeasurable
    have : Measurable fun x ↦  √(id x + 1) := (continuous_id.add continuous_const).sqrt.measurable
    exact (measurable_exp.comp this.neg).mul (((this.const_mul 2).const_div 1).const_mul c.toReal)

  apply ne_of_lt
  apply IntegrableOn.setLIntegral_lt_top
  exact intEsqc c.toReal

lemma lintegral_Ioc_eq_Ioi (l : ℝ) (f : ℝ → ENNReal) (x : X) (b : X → ℝ) :
    ∫⁻ (a : ℝ) in Ioc l (b x), f a = ∫⁻ (a : ℝ) in Ioi l, f a * {y | a ≤ (b y)}.indicator 1 x := by
  repeat rw [← lintegral_indicator]
  simp only [indicator, mem_setOf_eq, Pi.one_apply, mul_ite, mul_one, mul_zero, ← ite_and]
  congr; ext; congr
  exact measurableSet_Ioi
  exact measurableSet_Ioc

end
