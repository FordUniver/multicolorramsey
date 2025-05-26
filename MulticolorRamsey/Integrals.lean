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



-- maybe mathlib
lemma indicator_one_mul {x : X} (f : X → ℝ) [MeasurableSpace X] (E : Set X) :
    f x * E.indicator 1 x = E.indicator f x := by
  by_cases hx : x ∈ E <;> simp [hx]


----------------------------------------------------------------------------------------------------
-- integral of rexp (-√x) * (1 / (2 * √x))


lemma bounded_thingy {f g h : ℝ → ℝ} (Ig : IntegrableOn g s) (Ih : IntegrableOn h s)
    (dg : f ≤ g) (dh : h ≤ f) (mf : Measurable f) : IntegrableOn f s :=
  integrable_of_le_of_le (mf.aestronglyMeasurable) (Filter.Eventually.of_forall dh) (Filter.Eventually.of_forall dg) Ih Ig

lemma bounded_thingy_on_s {f g h : ℝ → ℝ} (ms : MeasurableSet s) (Ih : IntegrableOn h s) (Ig : IntegrableOn g s)
    (dh : ∀ x ∈ s, h x ≤ f x) (dg : ∀ x ∈ s, f x ≤ g x) (mf : Measurable f) : IntegrableOn f s :=
  integrable_of_le_of_le (mf.aestronglyMeasurable)
    (by filter_upwards [ae_restrict_mem ms] with x hx using dh x hx)
    (by filter_upwards [ae_restrict_mem ms] with x hx using dg x hx)
    Ih Ig

lemma integrableOn_one_div_two_mul_sqrt_plus (m : ℝ) (c : ℝ) : IntegrableOn (fun x ↦ 1 / (2 * √(x + c))) (Icc (-c) m) := by
  have : (∀ x ∈ Ioo (-c) m, HasDerivAt (fun x ↦ √(x + c)) ((fun x ↦ 1 / (2 * √(x + c))) x) x) := by
    intros x xi
    have := ((hasDerivAt_id' x).add (hasDerivAt_const x c)).sqrt (by linarith [mem_Ioo.mp xi])
    simpa only [one_div, mul_inv_rev, add_zero]
  apply integrableOn_Icc_iff_integrableOn_Ioc.mpr

  exact intervalIntegral.integrableOn_deriv_of_nonneg ((continuousOn_id' _).add continuousOn_const).sqrt this (by intros; positivity)

lemma integrableOn_one_div_two_mul_sqrt {m : ℝ} : IntegrableOn (fun x ↦ 1 / (2 * √x)) (Icc 0 m) := by
  have := integrableOn_one_div_two_mul_sqrt_plus m 0
  simpa

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

lemma measEsqc : Measurable fun x ↦ rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1)))) := by
  have : Measurable fun x ↦  √(id x + 1) := (continuous_id.add continuous_const).sqrt.measurable
  exact (measurable_exp.comp (this.const_mul c)).mul (((this.const_mul 2).const_div 1).const_mul c)



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



-- lemma integrableOn_exp_neg_sqrt_plus_mul {c d e : ℝ} (cn : 0 ≤ c) (epos : 0 ≤ e) (dnz : d ≠ 0) : IntegrableOn (fun x ↦ rexp (d * √(x + c)) * (e * (1 / (2 * √(x + c))))) (Ioi (-c)) ℙ := by

--   simp_rw [mul_comm d, ← smul_eq_mul _ d]
--   -- simp_rw [mul_comm e, ← smul_eq_mul _ e]


--   have i0 : IntegrableOn (fun x ↦ rexp (√(x + c) • d) * (e * (1 / (2 * √(x + c))))) (Ioc (-c) 1) ℙ := by
--     apply integrableOn_Icc_iff_integrableOn_Ioc.mp
--     refine IntegrableOn.continuousOn_mul ?_ ?_ isCompact_Icc
--     exact hrrrm
--     exact (integrableOn_one_div_two_mul_sqrt_plus _ cn).const_mul e

--   have i1 : IntegrableOn (fun x ↦ rexp (√(x + c) • d) * (e * (1 / (2 * √(x + c))))) (Ioi 1) ℙ := by
--     have mf : Measurable (fun x ↦ rexp (√(x + c) • d) * (e * (1 / (2 * √(x + c))))) :=
--         have := (continuous_id.add continuous_const).sqrt.measurable
--         (measurable_exp.comp (this.smul_const d)).mul (((this.const_mul 2).const_div 1).const_mul e)
--     have Ig : IntegrableOn (fun x ↦ e * ((x + c) ^ (-(1.5 : ℝ)))) (Ioi 1) := (integrableOn_pow zero_lt_one (by linarith : -(1.5 : ℝ) < -1) cn).const_mul e
--     refine bounded_thingy_on_s measurableSet_Ioi (integrable_zero _ _ _) Ig ?_ ?_ mf

--     all_goals intros x ax
--     positivity

--     simp only [mem_Ioi] at ax
--     have xcn : 0 < x + c := by positivity
--     have xpos : 0 < x := by positivity
--     have pow_recip_sqrt_cubed (x : ℝ) (xpos : 0 < x) : ((√x)⁻¹) ^ 3 = x ^ (-(1.5 : ℝ)) := by
--       rw [sqrt_eq_rpow, ← Real.rpow_neg_one, ← rpow_mul (le_of_lt xpos), ← Real.rpow_natCast, ← rpow_mul (le_of_lt xpos)]
--       norm_num
--     have moo : e * (√(x + c))⁻¹ ^ 3 = (√((x + c) • d) ^ 2 / 2)⁻¹ * (e * (1 / (2 * √(x + c)))) := by
--       have (x : ℝ) : (√x)⁻¹ ^ 3 = (√x ^ 2 / 2)⁻¹ * (1 / (2 * √x)) := by ring
--       have := this ((x + c) • d)
--       sorry
--     rw [← pow_recip_sqrt_cubed (x + c) xcn, smul_eq_mul, exp_mul, moo]

--     have : √((x + c) • d) ^ 2 / 2 < rexp √((x + c) • d) := lt_of_lt_of_le (by linarith [sqrt_pos.mpr xcn]) (quadratic_le_exp_of_nonneg (by positivity))
--     simp only [sq_sqrt] at this
--     have := (inv_lt_inv₀ (by positivity) (by linarith [xcn, dnz])).mpr this
--     `exact le_of_lt ((mul_lt_mul_iff_of_pos_right (show 0 < e * (1 / (2 * sqrt (x + c))) by positivity)).mpr this)

--   convert i0.union i1
--   symm
--   exact Ioc_union_Ioi_eq_Ioi (le_trans (Right.neg_nonpos_iff.mpr cn) zero_le_one)


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


lemma integrable_p {X : Finset V} [Nonempty X] (M : { x // x ∈ X } × { x // x ∈ X } → ℝ) [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X] {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] (E : Set ({ x // x ∈ X } × { x // x ∈ X })) :
    let f := (fun (p : ({ x // x ∈ X } × { x // x ∈ X }) × ℝ) ↦ rexp (c * √(p.2 + 1)) * (c * (1 / (2 * √(p.2 + 1)))) * (E ∩ {x | p.2 ≤ M x}).indicator (fun x ↦ 1) p.1)
    Integrable f (ℙᵤ.prod (Measure.restrict ℙ (Ioi (-1)))) := by
  intro f
  have meas : AEStronglyMeasurable f (ℙᵤ.prod (Measure.restrict ℙ (Ioi (-1)))) := sorry
  refine (integrable_prod_iff meas).mpr ⟨?_, Integrable.of_finite⟩
  refine Filter.Eventually.of_forall ?_
  intro x
  simp only [f]

  let ff := (fun y ↦ rexp (c * √(y + 1)) * (c * (1 / (2 * √(y + 1)))) * (E ∩ {x | y ≤ M x}).indicator (fun x ↦ 1) x)

  obtain ⟨ε, ⟨εl, pe⟩⟩ :
      ∃ ε ∈ Ioi (-1), ∀ p2 ∈ (Ioo (-1) ε),  {x | ε ≤ M x} = {x | p2 ≤ M x} := by sorry
  have i0 : IntegrableOn ff (Ioo (-1) ε) ℙ := by
    simp only [ff]
    have hst :
        EqOn (fun y ↦ rexp (c * √(y + 1)) * (c * (1 / (2 * √(y + 1)))) * (E ∩ {x | ε ≤ M x}).indicator (fun x ↦ 1) x) ff (Ioo (-1) ε) := by
      simp only [EqOn, ff]
      intros y yoo
      congr
      exact pe y yoo
    refine IntegrableOn.congr_fun ?_ hst measurableSet_Ioo
    refine Integrable.mul_const ?_ ((E ∩ {x | ε ≤ M x}).indicator (fun x ↦ 1) x)
    apply integrableOn_Icc_iff_integrableOn_Ioo.mp
    refine IntegrableOn.continuousOn_mul ?_ ?_ isCompact_Icc
    convert (continuousOn_add_const.sqrt.const_smul c).rexp
    have : (fun y ↦ c * (1 / (2 * √(y + 1)))) = fun y ↦ ((fun _ ↦ c) y) * ((fun y ↦ (1 / (2 * √(y + 1)))) y) := by simp
    rw [this]
    exact IntegrableOn.continuousOn_mul continuousOn_const (integrableOn_one_div_two_mul_sqrt_plus ε 1) isCompact_Icc

  have i1 : IntegrableOn ff (Ici ε) ℙ := by
    sorry

  have := i0.union i1
  rw [Ioo_union_Ici_eq_Ioi] at this
  simp [IntegrableOn] at this
  convert this
  exact εl

end
