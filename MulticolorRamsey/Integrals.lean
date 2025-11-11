import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ToMathlib.IndicatorOneMul.Basic


section

open MeasureTheory ProbabilityTheory Real ENNReal Set


theorem ae_le_of_forallOn_le {f : α → ℝ} {s : Set α}  [MeasurableSpace α] {μ : Measure α} (ms : MeasurableSet s) (h₁ : ∀ x ∈ s, g x ≤ f x) :
    g ≤ᶠ[ae (μ.restrict s)] f := by
      filter_upwards [ae_restrict_mem ms] with x hx using h₁ x hx

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
    have := ((hasDerivAt_id' x).add (hasDerivAt_const x c)).sqrt (by simp; linarith [mem_Ioo.mp xi])
    simpa only [one_div, mul_inv_rev, add_zero]

  apply (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).mpr

  exact intervalIntegral.integrableOn_deriv_of_nonneg ((continuousOn_id' _).add continuousOn_const).sqrt this (by intros; positivity)

lemma continuousOn_add_const : ContinuousOn (fun (x : ℝ) ↦ (x + c)) s := ((continuousOn_id' _).add continuousOn_const)

lemma intOn1 {m : ℝ} : IntegrableOn (fun x ↦ 1 / (2 * √(x + 1))) (Ioc (-1) m) := by
  apply (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).mp
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

-- -- https://github.com/leanprover-community/mathlib4/pull/25045
-- lemma integrableOn_pow {m a c : ℝ} (mp : 0 < m) (ha : a < -1) (cp : 0 ≤ c) : IntegrableOn (fun (x : ℝ) ↦ (x + c) ^ a) (Ioi m) ℙ := by
--   have hd : ∀ x ∈ Ici m, HasDerivAt (fun t => (t + c) ^ (a + 1) / (a + 1)) ((x + c) ^ a) x := by
--     intro x hx
--     convert (((hasDerivAt_id _).add_const c).rpow_const _).div_const (a + 1) using 1
--     field_simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
--     simp_all; left; have := (lt_of_lt_of_le mp hx); exact ne_of_gt (by linarith)

--   have ht : Filter.Tendsto (fun t => ((t + c) ^ (a + 1)) / (a + 1)) Filter.atTop (nhds (0 / (a + 1))) := by
--     refine Filter.Tendsto.div_const ?_ (a + 1)
--     have := tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
--     simp [neg_neg] at this

--     have :
--       Filter.Tendsto (fun t : ℝ => (t + c : ℝ) ^ (a + 1)) Filter.atTop (nhds 0) =
--       Filter.Tendsto ((fun x : ℝ => x ^ (a + 1)) ∘ fun t : ℝ => (t + c : ℝ)) Filter.atTop (nhds 0) := by simp; rfl
--     rw [this]
--     apply Filter.Tendsto.comp
--     assumption
--     exact Filter.tendsto_atTop_add_const_right _ c (fun ⦃U⦄ a ↦ a)

--   exact integrableOn_Ioi_deriv_of_nonneg' hd (fun t ht => rpow_nonneg (by linarith [gt_trans ht mp]) a) ht

lemma measEsqc : Measurable fun x ↦ rexp (d * √(x + 1)) * (c * (1 / (2 * √(x + 1)))) := by
  have : Measurable fun x ↦  √(id x + 1) := (continuous_id.add continuous_const).sqrt.measurable
  exact (measurable_exp.comp (this.const_mul d)).mul (((this.const_mul 2).const_div 1).const_mul c)

lemma integrableOn_exp_neg_sqrt_plus {c : ℝ} (cn : 0 ≤ c) : IntegrableOn (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) (Ioi (-c)) ℙ := by

  have i0 : IntegrableOn (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) (Ioc (-c) 1) ℙ := by
    apply (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).mp
    refine IntegrableOn.continuousOn_mul ?_ ?_ isCompact_Icc
    exact continuousOn_add_const.sqrt.neg.rexp
    exact integrableOn_one_div_two_mul_sqrt_plus _ c

  have i1 : IntegrableOn (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) (Ioi 1) ℙ := by
    have mf : Measurable (fun x ↦ rexp (-√(x + c)) * (1 / (2 * √(x + c)))) :=
        have := (continuous_id.add continuous_const).sqrt.measurable
        (measurable_exp.comp this.neg).mul ((this.const_mul 2).const_div 1)
    have Ig : IntegrableOn (fun x ↦ (x + c) ^ (-(1.5 : ℝ))) (Ioi 1) :=
      integrableOn_add_rpow_Ioi_of_lt (by linarith) (by linarith)
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
    have := (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).mpr (exp_neg_integrableOn_Ioi 0 zero_lt_one)
    simpa only [neg_mul, one_mul]
  have : IntegrableOn (fun x ↦ rexp (-√x) * (1 / (2 * √x))) (Ioi 0) ℙ := by
    have := integrableOn_exp_neg_sqrt_plus (Preorder.le_refl 0)
    simpa
  exact (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).mpr this

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
  all_goals apply (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).mpr
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

section

open MeasureTheory ProbabilityTheory Real ENNReal Set Fin


noncomputable abbrev ecsq (c : ℝ) := fun y ↦ rexp (c * √(y + 1))
noncomputable abbrev ecsq' (c : ℝ) := fun x ↦ (rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1)))))
abbrev oℝ := ENNReal.ofReal


lemma fundamental (c m : ℝ) (mp : -1 ≤ m) :
    ∫ (y : ℝ) in (Ioc (-1) m), ecsq' c y = ecsq c m - ecsq c (-1) := by

  have hderiv (x : ℝ) (xi : x ∈ Ioo (-1) m) := by
    have : x + 1 ≠ 0 := by linarith [mem_Ioo.mp xi]
    exact ((((hasDerivAt_id' x).add_const (1 : ℝ)).sqrt this).const_mul c).exp

  have hcont : ContinuousOn (ecsq c) (Icc (-1) m) := (continuousOn_add_const.sqrt.const_smul c).rexp

  have hcont' : ContinuousOn (ecsq' c) (Ioc (-1) m) := by
    have (x : ℝ) (xi : x ∈ Ioc (-1) m) : 2 * √(x + 1) ≠ 0 := by
      have : 0 < x + 1 := by linarith [xi.1]
      have : 0 < 2 * √(x + 1) := by positivity
      linarith
    let ccon {c  : ℝ} {s : Set ℝ} : ContinuousOn (fun x ↦ c) s := continuousOn_const
    exact (hcont.mono Ioc_subset_Icc_self).mul (ccon.mul (ccon.div (ccon.mul continuousOn_add_const.sqrt) this))

  have hint : IntervalIntegrable (ecsq' c) volume (-1) m := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le mp).mpr ?_
    have : IntegrableOn (fun x ↦ c * (1 / (2 * √(x + 1)))) (Icc (-1) m) ℙ :=
      ((integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).mpr intOn1).continuousOn_mul continuousOn_const isCompact_Icc
    exact (this.continuousOn_mul hcont isCompact_Icc).mono_set Ioc_subset_Icc_self

  -- fundamental thm of calculus
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le mp hcont hderiv hint
  convert this
  exact (intervalIntegral.integral_of_le mp).symm


theorem integral_ecsq' (c m : ℝ) (mp : -1 ≤ m) (cpos : 0 < c):
    oℝ (ecsq c m) = ∫⁻ (y : ℝ), oℝ (ecsq' c y) ∂(volume.restrict (Ioc (-1) m)) + oℝ (ecsq c (-1)) := by
  have fnd := fundamental c m mp
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← ofReal_add (by positivity)]
    symm; congr; apply add_eq_of_eq_sub
    convert fnd
    positivity
  · by_cases hm : m = -1
    · simp [hm]
    · apply MeasureTheory.Integrable.of_integral_ne_zero
      rw [fnd]
      simp [ecsq]
      have : -1 < m := lt_of_le_of_ne mp (hm ∘ Eq.symm)
      have : 0 < √(m + 1) := by linarith [sqrt_pos_of_pos (neg_lt_iff_pos_add.mp this)]
      have : 1 < rexp (c * √(m + 1)) := by exact one_lt_exp_iff.mpr (by positivity)
      nlinarith
  · refine ae_le_of_forallOn_le measurableSet_Ioc ?_
    intros; positivity


lemma exp_indicator (m : X × X → ℝ) (E : Set (X × X)) (mp : ∀ x, m x < -1 → x ∉ E) (x : X × X)
    (c : ENNReal) (cpos : 0 < c) (cnt : c ≠ ⊤):
    oℝ (ecsq c.toReal (m x)) * E.indicator 1 x =
      (∫⁻ a in (Ioi (-1)), oℝ (ecsq' c.toReal a) * ((E ∩ { x | a ≤ m x}).indicator (fun _ ↦ 1) x)) + E.indicator (fun _ ↦ 1) x := by

  by_cases cm : -1 ≤ m x
  · have := integral_ecsq' c.toReal (m x) cm (toReal_pos (ne_of_lt cpos).symm cnt)
    simp at this
    by_cases hx : x ∈ E
    · simp [hx, ecsq, ecsq', this, lintegral_Ioc_eq_Ioi]
      congr; ext y
      have (a : ℝ) : (E ∩ {x | a ≤ m x}).indicator (1 : (X × X) → ENNReal) x = {x | a ≤ m x}.indicator 1 x := by
        simp [inter_indicator_one, hx]
      rw [show ((1 : (X × X) → ENNReal) = (fun x ↦ (1 : ENNReal))) by exact rfl] at this -- TODO whet
      simp [this y]
      congr
    · simp [hx]
  · push_neg at cm
    have := mp x cm
    simp [this]

variable {V : Type} {X : Finset V} [MeasurableSpace X] {ℙᵤ : Measure (X × X)} [dm: DiscreteMeasurableSpace (X × X)]

lemma integral_bound {r : ℕ} {M : (X × X) → ℝ} {E : Set (X × X)} (mp : ∀ x, M x < -1 → x ∉ E)
    (measInter : Measurable fun (a : (X × X) × ℝ) ↦ (E ∩ {x | a.2 ≤ M x}).indicator (fun _ ↦ (1 : ENNReal)) a.1)
    {c C : ENNReal} (cpos : 0 < c) (cnt : c ≠ ⊤) (cleC : c.toReal ≤ C.toReal - 1) :

    let β := oℝ ( 3 ^ (-(4 : ℝ) * r))

    ℙᵤ E < β →

    (∀ y, -1 ≤ y → ℙᵤ (E ∩ {x | y ≤ M x}) < oℝ (rexp (-C.toReal * √(y + 1))) * β * r) →

    ∫⁻ x in E, oℝ (ecsq c.toReal (M x)) ∂ℙᵤ ≤ β * (r * c + 1)
    := by
  intros β h ch

  let measE := DiscreteMeasurableSpace.forall_measurableSet E

  set cℝ := c.toReal

  -- integral over E is integral over indicator
  simp only [← lintegral_indicator measE]
  have (x : X × X) := indicator_one_mul (x := x) (fun x ↦ oℝ (ecsq cℝ (M x))) E
  simp_rw [← this]

  -- "For any constant c ≤ C-1, we have ..."
  have exp_bound23:
      (fun x ↦ (oℝ (ecsq cℝ (M x)) * E.indicator 1 x)) =
      (fun x ↦ ∫⁻ a in (Ioi (-1)), oℝ (ecsq' cℝ a) * ((E ∩ { x | a ≤ M x}).indicator (fun _ ↦ 1) x)) + E.indicator (fun _ ↦ 1) := by
    ext x
    convert exp_indicator M E mp x c cpos cnt

  -- first step
  have := congrArg (fun (f : (X × X → ENNReal)) ↦ (∫⁻ x, f x ∂ℙᵤ)) exp_bound23
  simp only [Pi.add_apply] at this
  rw [lintegral_add_right _ ((measurable_indicator_const_iff 1).mpr measE)] at this
  simp only [lintegral_indicator_const measE 1] at this
  simp only [this, ge_iff_le]

--TODO mathlib lintegral_indicator_const integral_indicator_const parameter order
-- ENNReal.toReal_eq_toReal_iff' same as ENNReal.toReal_eq_toReal?

  -- tonelli
  rw [lintegral_lintegral_swap ((measEsqc.ennreal_ofReal.comp measurable_snd).aemeasurable.mul measInter.aemeasurable)]
  simp only [lintegral_const_mul _ Measurable.of_discrete, lintegral_indicator_const MeasurableSet.of_discrete 1, one_mul]
  apply le_trans (add_le_add_left (le_of_lt h) _) ?_

  -- second step
  have step2 (y : ℝ) (yge : y ∈ Ioi (-1)) :
      oℝ (ecsq' cℝ y) * ℙᵤ (E ∩ {x | y ≤ M x}) ≤ oℝ (ecsq' cℝ y) * oℝ (rexp (-C.toReal * √(y + 1))) * β * r := by
    have := mul_le_mul_of_nonneg_left (le_of_lt (ch y (le_of_lt yge))) (zero_le (oℝ (ecsq' cℝ y)))
    simpa only [mul_assoc]

  -- third step
  have step3 (y : ℝ) (yge : y ∈ Ioi (-1)) := by
    have step3' : ecsq' cℝ y * (rexp (-C.toReal * √(y + 1))) ≤ rexp (- √(y + 1)) * (cℝ * (1 / (2 * √(y + 1)))) := by
      simp only [mul_comm, mul_assoc, ← exp_add, ecsq']
      gcongr
      nlinarith [sqrt_pos_of_pos (neg_lt_iff_pos_add.mp yge)]
    have := ofReal_le_ofReal step3'
    rw [ofReal_mul' (exp_nonneg _)] at this
    have βpos : 0 ≤ β := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this βpos) (Nat.cast_nonneg' r)

  -- linearity of integral
  have measf : Measurable fun x ↦ oℝ (rexp (-√(x + 1)) * (cℝ * (1 / (2 * √(x + 1))))) := by
    have := (measEsqc (d := -1) (c := cℝ)).ennreal_ofReal
    simp only [neg_mul, one_mul] at this
    exact this

  have (y : ℝ) (yge : y ∈ Ioi (-1)) := le_trans (step2 y yge) (step3 y yge)
  apply le_trans (add_le_add_right (setLIntegral_mono ((measf.mul_const β).mul_const r) this) _) ?_

  rw [lintegral_mul_const r (measf.mul_const β), lintegral_mul_const β measf, terrible c cnt]
  ring_nf
  exact Preorder.le_refl _


end
