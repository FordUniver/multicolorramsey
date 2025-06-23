import MulticolorRamsey.Basic
import MulticolorRamsey.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
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

import Init.Tactics

import Mathlib.Tactic.Linarith


open MeasureTheory ProbabilityTheory Real ENNReal Set Fin

variable {r : ℕ}


-- lemma three_ineq {r : ℕ} (rpos : 0 < r) : ↑r * 3 ^ (-((r : ℝ) * 4)) * 3 ^ r + ↑r ^ 3 * 3 ^ (-((r : ℝ) * 4)) * √3 * √↑r * 3 ^ r ≤ 1 / 3 := by sorry
  -- suffices hh :  3 ^ r * (3 ^ (-((4 : ℝ) * ↑r)) * ↑r * (↑r * (↑r * (√3 * √↑r)) + 1)) ≤ 1/3 from by ring_nf at hh;
  -- cancel_denoms
  -- have : (3 : ℝ) ^ (r : ℝ) * 3 ^ (-(4 * (r : ℝ))) = 3 ^ (- (r : ℝ) * 3) := by rw [← rpow_add zero_lt_three]; ring_nf
  -- have : 3 * (3 : ℝ) ^ r * 3 ^ (-(4 * (r : ℝ))) = 3 * 3 ^ (- (r : ℝ) * 3) := by linarith
  -- simp_rw [this]

  -- have : r * r * √3 * √r + 1 ≤ r * r * √r * 3 := by
  --   suffices 1 ≤ (3 - √3) * (r * (r * √r)) from by linarith
  --   have o : 1 ≤ (3 - √3) := by nlinarith [sq_sqrt (zero_le_three)]
  --   have t : 1 ≤ r * (r * √r) := by
  --     nlinarith [sq_sqrt (le_trans zero_le_one (show 1 ≤ (r : ℝ) by sorry)),
  --       show 0 < r * (r * √r) by positivity,
  --       sq_nonneg (r - 1), sq_nonneg (√r - 1)]
  --   exact one_le_mul_of_one_le_of_one_le o t


  -- suffices h : (3 * 3 ^ (- r * 3) * r) * (r * r * √r * 3) ≤ 1 from le_trans (mul_le_mul_of_nonneg_left this (by positivity)) h

  -- have : 3 * 3 ^ (- r * 3) * r * (r * r * √r * 3) ≤ 3 ^ (- r * 5) * 3 := by
  --   have : 3 * 3 ^ (- r * 3) * r * (r * r * √r * 3) = (r * √3 ^ (-r)) ^ (7/2) * 3 ^ (- r * 5) * 3 := by sorry
  --   rw [this]
  --   have : (r / √3 ^ r) ^ (7/2) ≤ 1 := sorry
  --   have : (r / √3 ^ r) ^ (7 / 2) * 3 ^ (-r * 5) ≤ 3 ^ (-r * 5) := mul_le_of_le_one_left (by positivity) this
  --   sorry

  -- trans 3 ^ (-(5 : ℝ)) * 3
  -- trans 3 ^ (-r * 5) * 3
  -- exact this
  -- simp [rpos]
  -- ring_nf; linarith

-- theeorem one_le_r_mul_r_mul_sqrt_r (r : ℝ) (h : 2 ≤ r) : 1 ≤ r * (r * √r) := by
--   have h₃ : 0 ≤ r * √r := by positivity
--   nlinarith [sq_sqrt (show 0 ≤ r by linarith), sq_nonneg (r - 1), sq_nonneg (√r - 1)]

-- lemma C_ineq (r : ℕ) (rpos : 0 < r) :
--     ↑r * √(3 * ↑r) ≤ 4 * (↑r : ℝ) * √↑r - 1 := by
--   simp only [Nat.ofNat_nonneg, sqrt_mul]
--   have one_le : 1 ≤ (r : ℝ) := by exact Nat.one_le_cast.mpr rpos
--   have dd :  0 < 4 * ↑r * √↑r - 1 := by
--     have : 4 ≤ 4 * r * √r := by nlinarith [sqrt_nonneg r, sq_sqrt (Nat.cast_nonneg' r)]
--     linarith
--   apply (one_le_div (by positivity)).mp
--   rw [sub_div]
--   have : 4 * ↑r * √↑r / (↑r * (√3 * √↑r)) = 4 / √3 := by field_simp; linarith
--   have : 4 / 2 ≤ 4 / √3 := div_le_div_of_nonneg_left zero_le_four (sqrt_pos.mpr zero_lt_three) (sqrt_le_iff.mpr (by simp only [Nat.ofNat_nonneg, true_and]; linarith))
--   have : 1 / (↑r * (√3 * √↑r)) ≤ 1 := by
--     rw [one_div]; refine inv_le_one_of_one_le₀ ?_;
--     nlinarith [show 1 ≤ √3 by exact one_le_sqrt.mpr Nat.one_le_ofNat, one_le_sqrt.mpr one_le]
--   linarith


lemma fundamental (c m : ℝ) (mp : -1 ≤ m) :
    let ecsq (c : ℝ) := fun y ↦ rexp (c * √(y + 1))
    let ecsq' (c : ℝ) := fun x ↦ (rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1)))))
    ∫ (y : ℝ) in (Ioc (-1) m), ecsq' c y = ecsq c m - ecsq c (-1) := by
  intros ecsq ecsq'

  have hderiv (c x : ℝ) (xi : x ∈ Ioo (-1) m) := by
    have : x + 1 ≠ 0 := by linarith [mem_Ioo.mp xi]
    exact ((((hasDerivAt_id' x).add_const (1 : ℝ)).sqrt this).const_mul c).exp

  have hcont (c m : ℝ) : ContinuousOn (ecsq c) (Icc (-1) m) := (continuousOn_add_const.sqrt.const_smul c).rexp

  have hcont' (c m : ℝ) : ContinuousOn (ecsq' c) (Ioc (-1) m) := by
    have (x : ℝ) (xi : x ∈ Ioc (-1) m) : 2 * √(x + 1) ≠ 0 := by
      have : 0 < x + 1 := by linarith [xi.1]
      have : 0 < 2 * √(x + 1) := by positivity
      linarith
    let Ccon {c  : ℝ} {s : Set ℝ} : ContinuousOn (fun x ↦ c) s := continuousOn_const
    exact ((hcont c m).mono Ioc_subset_Icc_self).mul (Ccon.mul (Ccon.div (Ccon.mul continuousOn_add_const.sqrt) this))

  have hint (c m : ℝ) (mp : -1 ≤ m) : IntervalIntegrable (ecsq' c) volume (-1) m := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le mp).mpr ?_
    have : IntegrableOn (fun x ↦ c * (1 / (2 * √(x + 1)))) (Icc (-1) m) ℙ :=
      (integrableOn_Icc_iff_integrableOn_Ioc.mpr intOn1).continuousOn_mul continuousOn_const isCompact_Icc
    exact (this.continuousOn_mul (hcont c m) isCompact_Icc).mono_set Ioc_subset_Icc_self

  -- fundamental thm of calculus
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le mp (hcont c m) (hderiv c) (hint c m mp)
  convert this
  exact (intervalIntegral.integral_of_le mp).symm


theorem integral_ecsq' (c m : ℝ) (mp : -1 ≤ m) (cpos : 0 < c):
    let ecsq := fun y ↦ rexp (c * √(y + 1))
    let ecsq' := fun x ↦ (rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1)))))
    ENNReal.ofReal (ecsq m) = ∫⁻ (y : ℝ), ENNReal.ofReal (ecsq' y) ∂(Measure.restrict volume (Ioc (-1) m)) + ENNReal.ofReal (ecsq (-1)) := by
  simp only [ofReal_one]
  have fnd := fundamental c m mp
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← ofReal_add (by positivity)]
    symm; congr; apply add_eq_of_eq_sub
    convert fnd
    simp [exp_nonneg]
  · by_cases hm : m = -1
    · simp [hm]
    · apply MeasureTheory.Integrable.of_integral_ne_zero
      rw [fnd]
      simp
      have : -1 < m := lt_of_le_of_ne mp (hm ∘ Eq.symm)
      have : 0 < √(m + 1) := by linarith [sqrt_pos_of_pos (neg_lt_iff_pos_add.mp this)]
      have : 1 < rexp (c * √(m + 1)) := by exact one_lt_exp_iff.mpr (by positivity)
      nlinarith
  · refine ae_le_of_forallOn_le measurableSet_Ioc ?_
    intros; positivity


lemma exp_indicator (m : X × X → ℝ) (E : Set (X × X)) (mp : ∀ x, m x < -1 → x ∉ E) (x : X × X) (c : ENNReal) (cpos : 0 < c) (cnt : c ≠ ⊤):
    let ecsq := fun y ↦ rexp (c.toReal * √(y + 1))
    let ecsq' := fun x ↦ rexp (c.toReal * √(x + 1)) * (c.toReal * (1 / (2 * √(x + 1))))
    ENNReal.ofReal (ecsq (m x)) * E.indicator 1 x =
      (∫⁻ a in (Ioi (-1)), ENNReal.ofReal (ecsq' a) * ((E ∩ { x | a ≤ m x}).indicator (fun _ ↦ 1) x)) + E.indicator (fun _ ↦ 1) x := by

  intros ecsq ecsq'

  by_cases cm : -1 ≤ m x
  · have := integral_ecsq' c.toReal (m x) cm (toReal_pos (ne_of_lt cpos).symm cnt)
    simp at this
    by_cases hx : x ∈ E
    · simp [hx, ecsq, ecsq', this, add_mul, ← integral_mul_const, lintegral_Ioc_eq_Ioi, mul_assoc, one_mul]
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


lemma exp_ineq {r : ℕ} {V : Type} [Fintype V] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] (Z : Fin r → X × X → ℝ) (exPos : 0 ≤ ℙᵤ[ fun xx => f (fun i => Z i xx) ]) :

    let E : Set (X × X) := { xx |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }

    let exp := fun xx => 3 ^ r * r * exp (∑ i, √(Z i xx + 3 * r))
    let 𝔼exp := ∫ x in E, exp x ∂ℙᵤ -- we don't use lebesue integral for this because we want negative

    1 - (ℙᵤ E).toReal ≤ 𝔼exp := by
  intros E exp 𝔼exp

  let measE := DiscreteMeasurableSpace.forall_measurableSet E
  have mEc : MeasurableSet Eᶜ := MeasurableSet.compl_iff.mpr measE

  have Ecb : ∫ x in Eᶜ, f fun i ↦ Z i x ∂ℙᵤ ≤ ∫ x in Eᶜ, -1 ∂ℙᵤ := by
    have : ∀ x ∈ Eᶜ, (f fun i ↦ Z i x) ≤ -1 := by
      intros x xinEc
      simp only [E, mem_compl_iff, mem_setOf_eq, not_forall, not_le] at xinEc
      exact specialFunctionEc (fun i ↦ Z i x) xinEc
    exact setIntegral_mono_on IntegrableFin.integrableOn (by simp) mEc this

  have Eb : ∫ x in E, f fun i ↦ Z i x ∂ℙᵤ ≤ 𝔼exp :=
    setIntegral_mono_on
      IntegrableFin.integrableOn IntegrableFin measE
      (fun x xinE => specialFunctionE (fun i ↦ Z i x) xinE)

  have : ∫ x in Eᶜ, -1 ∂ℙᵤ = - 1 + (ℙᵤ E).toReal := by
    simp [integral_const_mul, Measure.real, prob_compl_eq_one_sub measE]
    rw [toReal_sub_of_le prob_le_one one_ne_top, toReal_one, neg_sub]
    exact sub_eq_neg_add (ℙᵤ E).toReal 1

  rw [this] at Ecb

  rw [← integral_add_compl measE IntegrableFin] at exPos

  have : 0 ≤ 𝔼exp + (- 1 + (ℙᵤ E).toReal) :=
    le_trans (le_trans exPos (add_le_add_right Eb _)) (add_le_add_left Ecb _)
  simp [add_assoc, add_comm] at this
  simpa [zero_le, add_comm]


lemma exp_ineq_ENN {r : ℕ} {V : Type} [Fintype V] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] (Z : Fin r → X × X → ℝ) (exPos : 0 ≤ ℙᵤ[ fun xx => f (fun i => Z i xx) ]) :

    let E : Set (X × X) := { xx |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }

    let exp := fun x => 3^r * r * exp (∑ i, √(Z i x + 3 * r))

    (1 : ENNReal) - ℙᵤ E ≤ ∫⁻ x in E, ENNReal.ofReal (exp x) ∂ℙᵤ := by
  intros E exp

  have : ENNReal.ofReal (∫ x in E, exp x ∂ℙᵤ) = ∫⁻ x in E, ENNReal.ofReal (exp x) ∂ℙᵤ := by
    apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    simp; filter_upwards; intro; positivity
  simp_rw [← this]
  apply (toReal_le_toReal (by simp) (by simp)).mp
  rw [toReal_ofReal, toReal_sub_of_le prob_le_one one_ne_top, toReal_one]
  exact exp_ineq Z exPos
  positivity


----------------------------------------------------------------------------------------------------


lemma integral_bound {r : ℕ} {V : Type} [Fintype V] {X : Finset V} [MeasurableSpace X] [dm: DiscreteMeasurableSpace (X × X)]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ]
    {M : (X × X) → ℝ} {E : Set (X × X)} (mp : ∀ x, M x < -1 → x ∉ E)
    (measInter : Measurable fun (a : (X × X) × ℝ) ↦ (E ∩ {x | a.2 ≤ M x}).indicator (fun _ ↦ (1 : ENNReal)) a.1)
    {c C : ENNReal} (cpos : 0 < c) (cnt : c ≠ ⊤) (cleC : c.toReal ≤ C.toReal - 1) :

    let β := ENNReal.ofReal ( 3 ^ (-(4 : ℝ) * r))
    let ecsq (y : ℝ) := rexp (c.toReal * √(y + 1))

    ℙᵤ E < β →

    (∀ y, -1 ≤ y → ℙᵤ (E ∩ {x | y ≤ M x}) < ENNReal.ofReal (rexp (-C.toReal * √(y + 1))) * β * r) →

    ∫⁻ x in E, ENNReal.ofReal (ecsq (M x)) ∂ℙᵤ ≤ β * (r * c + 1)
    := by
  intros β ecsq h ch

  let ecsq' (x : ℝ) := (ecsq x) * (c.toReal * (1 / (2 * √(x + 1))))
  let measE := DiscreteMeasurableSpace.forall_measurableSet E

  -- integral over E is integral over indicator
  simp only [← lintegral_indicator measE]
  have (x : X × X) := indicator_one_mul (x := x) (fun x ↦ ENNReal.ofReal (ecsq (M x))) E
  simp_rw [← this]

  -- "For any constant c ≤ C-1, we have ..."
  have exp_bound23:
      (fun x ↦ (ENNReal.ofReal (ecsq (M x)) * E.indicator 1 x)) =
      (fun x ↦ ∫⁻ a in (Ioi (-1)), ENNReal.ofReal (ecsq' a) * ((E ∩ { x | a ≤ M x}).indicator (fun _ ↦ 1) x)) + E.indicator (fun _ ↦ 1) := by
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
      ENNReal.ofReal (ecsq' y) * ℙᵤ (E ∩ {x | y ≤ M x}) ≤ ENNReal.ofReal (ecsq' y) * ENNReal.ofReal (rexp (-C.toReal * √(y + 1))) * β * r := by
    have := mul_le_mul_of_nonneg_left (le_of_lt (ch y (le_of_lt yge))) (zero_le (ENNReal.ofReal (ecsq' y)))
    simpa only [mul_assoc]

  -- third step
  have step3 (y : ℝ) (yge : y ∈ Ioi (-1)) := by
    have step3' : ecsq' y * (rexp (-C.toReal * √(y + 1))) ≤ rexp (- √(y + 1)) * (c.toReal * (1 / (2 * √(y + 1)))) := by
      simp only [mul_comm, mul_assoc, ← exp_add, ecsq', ecsq]
      gcongr
      nlinarith [sqrt_pos_of_pos (neg_lt_iff_pos_add.mp yge)]
    have := ofReal_le_ofReal step3'
    rw [ofReal_mul' (exp_nonneg _)] at this
    have βpos : 0 ≤ β := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this βpos) (Nat.cast_nonneg' r)

  -- linearity of integral
  have measf : Measurable fun x ↦ ENNReal.ofReal (rexp (-√(x + 1)) * (c.toReal * (1 / (2 * √(x + 1))))) := by
    have := (measEsqc (d := -1) (c := c.toReal)).ennreal_ofReal
    simp only [neg_mul, one_mul] at this
    exact this

  have (y : ℝ) (yge : y ∈ Ioi (-1)) := le_trans (step2 y yge) (step3 y yge)
  apply le_trans (add_le_add_right (setLIntegral_mono ((measf.mul_const β).mul_const r) this) _) ?_

  rw [lintegral_mul_const r (measf.mul_const β), lintegral_mul_const β measf, terrible c cnt]
  ring_nf
  exact Preorder.le_refl _


lemma lintegral_sum_bound {r : ℕ} {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] {σ : Fin r → (X → (V → ℝ))} :

    let β := ENNReal.ofReal (3 ^ (-(4 : ℝ) * (r : ℝ)))
    let C := 4 * (r : ENNReal) * ENNReal.ofReal (√r)
    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i
    let E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }

    have nenI (x : X × X) := Finset.Nonempty.image Finset.univ_nonempty (τ x)

    let M (x : X × X) : ℝ := Finset.max' (Finset.univ.image (τ x)) (nenI x)
    let c := ENNReal.ofReal (r * √(3 * r))

    ℙᵤ E < β →
    (∀ y, -1 ≤ y → ℙᵤ (E ∩ {x | y ≤ M x}) < ENNReal.ofReal (rexp (-C.toReal * √(y + 1))) * β * r) →

    ∫⁻ x in E, ENNReal.ofReal (rexp (∑ i, √(Z i x + 3 * r))) ∂ℙᵤ ≤ β * (r * c + 1) := by
  intros β C _ Z E nenI M c βge ch

  have rpos : 0 < r := Fin.pos'

  let exp := fun xx => 3^r * r * exp (∑ i, √(Z i xx + 3 * r))
  let 𝔼exp := ∫⁻ (x : X × X ) in E, ENNReal.ofReal (exp x) ∂ℙᵤ
  let ecsq := fun y ↦ rexp (c.toReal * √(y + 1))

  have cc :
      ∀ x ∈ E, ENNReal.ofReal (rexp (∑ i, √(Z i x + 3 * r))) ≤ ENNReal.ofReal (ecsq (M x)) := by
    intro x xE
    apply ofReal_le_ofReal
    simp [ecsq, Nat.ofNat_nonneg, sqrt_mul, exp_le_exp, Z, ecsq, c]
    rw [toReal_ofReal (by positivity)]
    exact sum_sqrt_le

  have dd :
      ∫⁻ x in E, ENNReal.ofReal (ecsq (M x)) ∂ℙᵤ ≤ β * (r * c + 1) := by
    have mp (x : X × X) (aM : M x < -1) : x ∉ E := by
      simp only [neg_mul, mem_setOf_eq, not_forall, not_le, E]
      use nenr.some
      rw [← lt_div_iff₀' (by positivity)]
      ring_nf
      rw [Field.mul_inv_cancel]
      simp only [Finset.max'_lt_iff, Finset.mem_image, Finset.mem_univ, true_and,
        forall_exists_index, forall_apply_eq_imp_iff, M] at aM
      exact aM nenr.some
      positivity

    have ee : c.toReal ≤ C.toReal - 1 := by
      simp [c, C]
      rw [toReal_ofReal (by positivity)]
      have : 1 ≤ (r : ℝ) := Nat.one_le_cast.mpr rpos
      have : 1 ≤ (r * √r) := by nlinarith [one_le_sqrt.mpr this]
      have : √3 ≤ 3 := Real.sqrt_le_iff.mpr ⟨zero_le_three, by linarith⟩
      trans 4 * (r * √r) - 1 * (r * √r)

      rw [← sub_mul]
      nlinarith
      rw [mul_assoc]
      exact tsub_le_tsub_left (by linarith) _

    have ff :
        Measurable fun (a : (X × X) × ℝ) ↦ (E ∩ {x | a.2 ≤ M x}).indicator (fun x ↦ (1 : ENNReal)) a.1 := by
      refine Measurable.ite ?_ measurable_const measurable_const
      simp [preimage]
      refine Measurable.and ?_ ?_
      · simp only [neg_mul, E]
        refine Measurable.forall ?_
        intro i
        have : Measurable (fun x ↦ -(3 * r) ≤ Z i x) := Measurable.of_discrete
        exact this.comp measurable_fst
      · simp_rw [← not_lt, M]
        apply Measurable.not
        simp [Finset.max'_lt_iff]
        refine Measurable.forall ?_
        intro i
        simp_rw [← measurableSet_setOf, prod_set_eq_union]
        exact MeasurableSet.iUnion (fun _ ↦ (measurableSet_singleton _).prod measurableSet_Ioi)

    exact integral_bound mp ff (by positivity) ofReal_ne_top ee βge ch

  refine le_trans (le_trans (setLIntegral_mono Measurable.of_discrete cc) dd) ?_
  simp [β, c, ENNReal.ofReal_mul, le_refl]

----------------------------------------------------------------------------------------------------
-- sorries

lemma expPos {r : ℕ} {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] {σ : Fin r → (X → (V → ℝ))} :

    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i

    (0 ≤ ℙᵤ[ fun xx => f (fun i => (Z i xx)) ]) := by sorry -- big sorry. issue #8


lemma three_ineq_ENN {r : ℕ} (rpos: 0 < r) : r * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * 3 ^ r * 3 +
      r ^ 2 * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * ENNReal.ofReal (r * √3 * √r) * 3 ^ r * 3 ≤
    1 := sorry -- likely extremely ugly

--------------------------------------------------------------------------------------------------

lemma juicy {r : ℕ} {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] {σ : Fin r → (X → (V → ℝ))} :

    let β := (3 ^ (-(4 : ℝ) * (r : ℝ)) : ℝ)
    let C := 4 * (r : ℝ) * √r
    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i
    let E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }
    ℙᵤ.real E < β →
    ∃ Λ : ℝ, -1 ≤ Λ ∧ ∃ i : Fin r,
      ENNReal.ofReal (β * exp (-C * √(Λ + 1))) ≤
      ℙᵤ { x : X × X | (Λ ≤ τ x i ∧ ∀ j ≠ i, -1 ≤ τ x j) }
    := by
  intros β C τ Z E h

  have nenI (x : X × X) := Finset.Nonempty.image Finset.univ_nonempty (τ x)
  let M (x : X × X) : ℝ := Finset.max' (Finset.univ.image (τ x)) (nenI x)

  obtain ⟨Λ , ⟨minus1leΛ, le_pr⟩⟩ : ∃ (y : ℝ), (-1 ≤ y) ∧ rexp (-C * √(y + 1)) * β * r ≤ (ℙᵤ.real (E ∩ {x | y ≤ M x})) := by
    have rpos : 0 < r := Fin.pos'

    let c := ENNReal.ofReal (r * √(3 * r))

    let exp := fun xx => 3^r * r * exp (∑ i, √(Z i xx + 3 * r))
    let 𝔼exp := ∫⁻ (x : X × X ) in E, ENNReal.ofReal (exp x) ∂ℙᵤ

    obtain ⟨Λ, ⟨Λle, ee⟩⟩ :
        ∃ (y : ℝ), (-1 ≤ y) ∧
        ENNReal.ofReal (rexp (-(((4 * r * ENNReal.ofReal (√r)) ).toReal) * √(y + 1))) * (ENNReal.ofReal β) * r ≤ ℙᵤ (E ∩ {x | y ≤ M x}) := by

      -- we assume this in eq (2) in the blueprint
      by_contra ch
      push_neg at ch

      have := (lt_ofReal_iff_toReal_lt (measure_ne_top ℙᵤ E)).mpr h
      have := lintegral_sum_bound this ch

      have ca := calc 1 - (ENNReal.ofReal β)
        _ ≤ 1 - (ℙᵤ E) := by gcongr
        _ ≤ 𝔼exp := exp_ineq_ENN Z expPos
        _ = (3 ^ r * r ) * ∫⁻ x in E, ENNReal.ofReal (rexp (∑ i, √(Z i x + 3 * r))) ∂ℙᵤ
            := by simp [𝔼exp, exp];
                  simp_rw [ENNReal.ofReal_mul' (exp_nonneg _)];
                  rw [lintegral_const_mul]; congr; norm_cast
                  exact Measurable.of_discrete
        _ ≤ (3 ^ r * r ) * ( (ENNReal.ofReal β) * (r * c + 1))
            := by gcongr -- uses lintegral_sum_bound
        _ ≤ 1/3 := by simp [β, c]; ring_nf; exact three_ineq_ENN rpos

      have : 1 / 3 < 1 - (ENNReal.ofReal β) := by
        simp [β]
        rw [← ofReal_one, ← ofReal_sub _ (by positivity)]
        apply (lt_ofReal_iff_toReal_lt (three_ne_zero ∘ inv_eq_top.mp)).mpr
        simp only [toReal_inv, toReal_ofNat]
        have : (3 : ℝ) ^ (-(4 * (r : ℝ))) ≤ 1 / (3 ^ (4 : ℝ)) := by
          rw [Real.rpow_neg (by positivity)]
          field_simp
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          gcongr
          · exact Nat.one_le_ofNat
          · simp only [Nat.ofNat_pos, le_mul_iff_one_le_right, Nat.one_le_cast.mpr rpos]
        linarith

      exact (lt_self_iff_false _).mp (lt_of_le_of_lt ca this)

    use Λ
    simp only [Λle, true_and]

    apply (ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp

    convert ee
    rw [ofReal_mul' (show (0 : ℝ) ≤ r by positivity), ofReal_mul' (show 0 ≤ β by positivity), ofReal_natCast r]

    congr
    simp [C]

  use Λ, minus1leΛ

  rw [(maxUnion τ nenI), inter_iUnion] at le_pr

  obtain ⟨i, pip⟩ := Fin.exists_mul_of_sum_bound (fun i ↦ ℙᵤ (E ∩ {x | Λ ≤ τ x i}))
  use i

  have Eiff : {x | Λ ≤ τ x i ∧ (∀ (j : Fin r), j ≠ i → -1 ≤ τ x j)} = E ∩ {x | Λ ≤ τ x i} := by
    ext x
    simp only [and_comm, neg_mul, mem_inter_iff, mem_setOf_eq, and_congr_right_iff, E, τ]
    intro l
    refine ⟨?_ , fun xM j _ ↦ omg6.mp (xM j)⟩
    · intro nj j
      refine omg6.mpr ?_
      by_cases jeqi : j = i
      · subst jeqi
        exact le_trans minus1leΛ l
      · exact nj j jeqi

  simp only [Eiff]
  refine omg5.mpr (le_trans ?_ pip)

  have union_bound := measure_iUnion_fintype_le ℙᵤ fun i ↦ (E ∩ {x | Λ ≤ τ x i})
  have union :=
    ofReal_le_of_le_toReal (le_trans
      le_pr
      ((toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr union_bound))

  convert union
  simp only [mul_comm, ofReal_mul (Nat.cast_nonneg' r), ofReal_natCast, β]

----------------------------------------------------------------------------------------------------

lemma geometric {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] (X : Finset V) [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    (ℙᵤ : Measure (X × X)) [IsProbabilityMeasure ℙᵤ] (σ : Fin r → (X → (V → ℝ))) :

    let β := (3 ^ (-(4 : ℝ) * (r : ℝ)) : ℝ)
    let C := 4 * (r : ℝ) * √r
    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    ∃ Λ : ℝ, -1 ≤ Λ ∧ ∃ i : Fin r,
      ENNReal.ofReal (β * exp (-C * √(Λ + 1))) ≤
      ℙᵤ { x : X × X | (Λ ≤ τ x i ∧ ∀ j ≠ i, -1 ≤ τ x j) }

    := by
  intros β C τ

  let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i

  set E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx } with eE

  by_cases h : β ≤ (ℙᵤ E).toReal
  · exists -1
    have (i : Fin r) (x : X × X) := @and_forall_ne (Fin r) (fun i => -1 ≤ τ x i) i

    simp only [le_refl, neg_add_cancel, sqrt_zero, mul_zero, exp_zero, mul_one, ne_eq, true_and, this]

    have (x : X × X) : (∀ (b : Fin r), -1 ≤ τ x b) ↔ (∀  (i : Fin r), -3 * r ≤ (Z i x)) := by
      have : ∀ i, (-3 * r ≤ 3 * r * τ x i ↔ -1 ≤ τ x i) := by simp [omg6]
      simp_rw [Z, this]
    simp_rw [this, ← eE, ofReal_le_of_le_toReal h]

    exists ⟨0, Fin.pos'⟩
  · push_neg at h
    exact juicy h
