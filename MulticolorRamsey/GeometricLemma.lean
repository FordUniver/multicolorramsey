import MulticolorRamsey.Basic
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



import Mathlib.Tactic.Linarith


open MeasureTheory ProbabilityTheory Real ENNReal

variable {r : ℕ}


lemma intOnTerrible : IntegrableOn (fun x ↦ rexp (-√x) * (1 / (2 * √x))) (Set.Ici 0) ℙ := by sorry
  -- apply integrableOn_Ici_iff_integrableOn_Ioi.mpr
  -- apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg
  -- · have :  ContinuousWithinAt (fun x ↦ rexp (-√x)) (Set.Ici 0) 0 := sorry
  --   exact this
  -- · sorry
  -- · sorry


lemma integral_exp_neg_sqrt : ∫ (x : ℝ) in Set.Ioi 0, rexp (-√x) * (1 / (2 * √x)) = 1 := by
  nth_rewrite 2 [integral_exp_neg_Ioi_zero.symm]
  have := @MeasureTheory.integral_comp_mul_deriv_Ioi (fun x ↦ √x) (fun x ↦ 1 / (2 * √ x)) (fun x ↦ rexp (-x)) 0
  simp only [Set.mem_Ioi, Function.comp_apply,sqrt_zero] at this
  refine this ?_ ?_ ?_ ?_ ?_ ?_
  exact Real.continuous_sqrt.continuousOn
  · refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b; use b^2; intro a ab
    exact le_sqrt_of_sq_le ab
  · intro x xpos
    apply HasDerivWithinAt.sqrt
    exact (hasDerivWithinAt_id x _)
    exact Ne.symm (ne_of_lt xpos)
  · exact (continuous_id.neg).rexp.continuousOn
  · exact sorry -- MeasureTheory.Integral.ExpDecay.exp_neg_integrableOn_Ioi
  · exact intOnTerrible

lemma three_ineq {r : ℕ} : 3 ^ r * ↑r * (3 ^ (-((4 : ℝ) * ↑r)) * (↑r * (↑r * (√3 * √↑r)) + 1)) ≤ 3⁻¹ := sorry

lemma C_ineq (rpos : 0 < r) :
    let C := 4 * (↑r : ℝ) ^ ((3 : ℝ) / 2)
    ↑r * √(3 * ↑r) ≤ C - 1 := by
  intro C
  simp [C]
  sorry



-- maybe mathlib
lemma indicator_one_mul {x : X} {f : X → ℝ} [MeasurableSpace X] {E : Set X}:
    f x * E.indicator 1 x = E.indicator f x := by
  by_cases hx : x ∈ E <;> simp [hx]

theorem sum_sqrt_le {r : ℕ} {X : Type*} [Fintype X] [nenr: Nonempty (Fin r)] {τ : X → Fin r → ℝ} {x : X} :
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
  repeat rw [← Real.sqrt_mul (Nat.cast_nonneg' r)]
  left; ring_nf

lemma hrm : ContinuousOn (fun (x : ℝ) ↦ (x + c)) s := ((continuousOn_id' _).add continuousOn_const)

lemma improper_integral_shift (c : ℝ) (f : ℝ → ℝ) (cf : ContinuousOn f (Set.Ioi 0))
    (If : IntegrableOn f (Set.Ici 0) ℙ) (Iif : IntegrableOn (fun x ↦ f (x + c)) (Set.Ici (-c)) ℙ) :
    ∫ (x : ℝ) in Set.Ioi (-c), f (x + c) = ∫ (x : ℝ) in Set.Ioi 0, f x := by
  have (x : ℝ) (_ : x ∈ Set.Ioi (-c)) : HasDerivWithinAt (fun x ↦ x + c) ((fun x ↦ 1) x) (Set.Ioi x) x := by
    simp; exact hasDerivWithinAt_id x (Set.Ici x)
  have := @MeasureTheory.integral_comp_mul_deriv_Ioi (fun x ↦ x + c) (fun _ ↦ 1) f (-c)
      hrm (Filter.tendsto_atTop_add_const_right _ _ fun ⦃U⦄ a ↦ a) this ?_ ?_ ?_
  all_goals simpa [this]

lemma terrible (c : ℝ) : ∫ a in Set.Ioi (-1), rexp (- √(a + 1)) *  (c * (1 / (2 * √(a + 1)))) = c := by
  have := improper_integral_shift 1 (fun a ↦ rexp (-√a) * (c * (1 / (2 * √a)))) ?_ ?_ ?_
  simp only [this]
  have := congrArg (HMul.hMul c) integral_exp_neg_sqrt
  simp only [← integral_mul_left c, mul_one] at this
  nth_rw 2 [← this]
  congr; ext; linarith

  have : ContinuousOn (fun x ↦ 1 / 2 • √x) (Set.Ioi 0) :=
    continuousOn_const.div ((continuousOn_id' _).sqrt.const_smul 2) (by simp [sqrt_ne_zero'])
  have := (continuousOn_id' _).sqrt.neg.rexp.mul (this.const_smul c)
  simpa only [nsmul_eq_mul, smul_eq_mul]
  · sorry
  · simp only
    sorry


lemma einzwei (l : ℝ) (f : ℝ → ℝ) (x : X) (b : X → ℝ) :
    ∫ (a : ℝ) in Set.Ioc l (b x), f a = ∫ (a : ℝ) in Set.Ioi l, f a * {y | a ≤ (b y)}.indicator 1 x := by
  repeat rw [← integral_indicator]
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, mul_ite, mul_one, mul_zero, ← ite_and]
  congr; ext; congr
  exact measurableSet_Ioi
  exact measurableSet_Ioc


lemma intOn1 {m : ℝ} : IntegrableOn (fun x ↦ 1 / (2 * √(x + 1))) (Set.Ioc (-1) m) := by
  apply intervalIntegral.integrableOn_deriv_of_nonneg hrm.sqrt
  · intros x xi
    apply HasDerivAt.sqrt
    simp only [hasDerivAt_add_const_iff]
    exact (hasDerivAt_id' x)
    by_contra h
    rw [neg_eq_of_add_eq_zero_left h] at xi
    exact Set.left_mem_Ioo.mp xi
  · intros ; positivity


lemma IntegrableFin {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] {ℙᵤ : Measure X} [IsFiniteMeasure ℙᵤ] {f : X → ℝ} :
  Integrable f ℙᵤ := ⟨ AEStronglyMeasurable.of_discrete , HasFiniteIntegral.of_finite ⟩

-- lemma intOn :
--     let ecsq (c : ℝ) := fun y ↦ rexp (c * √(y + 1))
--     let ecsq' (c : ℝ) := fun x ↦ (rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1)))))
--     IntegrableOn (fun a ↦ ecsq' c a * ecsq (-C) a) (Set.Ioi (-1)) ℙ := by
--   intros ecsq ecsq'
--   sorry

-- lemma intOn3 :
--     IntegrableOn (fun x ↦ (rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1))))) * rexp (-C * √(x + 1)) * β * ↑r) (Set.Ioi (-1)) ℙ := (intOn.mul_const β).mul_const (r : ℝ)

lemma fundamental (c m : ℝ) (mp : -1 ≤ m) :
    let ecsq (c : ℝ) := fun y ↦ rexp (c * √(y + 1))
    let ecsq' (c : ℝ) := fun x ↦ (rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1)))))
    ∫ (y : ℝ) in (Set.Ioc (-1) m), ecsq' c y = ecsq c m - ecsq c (-1) := by
  intros ecsq ecsq'

  have hderiv (c x : ℝ) (xi : x ∈ Set.Ioo (-1) m) := by
    have : x + 1 ≠ 0 := by linarith [Set.mem_Ioo.mp xi]
    exact ((((hasDerivAt_id' x).add_const (1 : ℝ)).sqrt this).const_mul c).exp

  have hcont (c m : ℝ) : ContinuousOn (ecsq c) (Set.Icc (-1) m) := (hrm.sqrt.const_smul c).rexp

  have hcont' (c m : ℝ) : ContinuousOn (ecsq' c) (Set.Ioc (-1) m) := by
    have (x : ℝ) (xi : x ∈ Set.Ioc (-1) m) : 2 * √(x + 1) ≠ 0 := by
      have : 0 < x + 1 := by linarith [xi.1]
      have : 0 < 2 * √(x + 1) := by positivity
      linarith
    let Ccon {c  : ℝ} {s : Set ℝ} : ContinuousOn (fun x ↦ c) s := continuousOn_const
    exact ((hcont c m).mono Set.Ioc_subset_Icc_self).mul (Ccon.mul (Ccon.div (Ccon.mul hrm.sqrt) this))

  have hint (c m : ℝ) (mp : -1 ≤ m) : IntervalIntegrable (ecsq' c) volume (-1) m := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le mp).mpr ?_
    have : IntegrableOn (fun x ↦ c * (1 / (2 * √(x + 1)))) (Set.Icc (-1) m) ℙ :=
      (integrableOn_Icc_iff_integrableOn_Ioc.mpr intOn1).continuousOn_mul continuousOn_const isCompact_Icc
    exact (this.continuousOn_mul (hcont c m) isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

  -- fundamental thm of calculus
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le mp (hcont c m) (hderiv c) (hint c m mp)
  convert this
  exact (intervalIntegral.integral_of_le mp).symm


lemma exp_bound2 (c : ℝ) (m : X×X → ℝ) (E : Set (X × X)) (mp : ∀ x, m x < -1 → x ∉ E):
    let ecsq (c : ℝ) := fun y ↦ rexp (c * √(y + 1))
    let ecsq' (c : ℝ) := fun x ↦ (rexp (c * √(x + 1)) * (c * (1 / (2 * √(x + 1)))))
    (fun x ↦ (ecsq c (m x) * (E.indicator 1 x))) =
    (fun x ↦ ∫ a in (Set.Ioi (-1)), (ecsq' c a) * ((E ∩ { x | a ≤ m x}).indicator (fun _ ↦ 1) x)) + E.indicator (fun _ ↦ 1) := by

  intros ecsq ecsq'; ext x

  by_cases cm : -1 ≤ m x
  · have : ecsq c (m x) = (∫ y in (Set.Ioc (-1) (m x)), ecsq' c y) + ecsq c (-1) :=
      (add_eq_of_eq_sub (fundamental c (m x) cm)).symm
    have e1 : ecsq c (-1) = 1 := by simp [ecsq]
    simp only [this, add_mul, ← integral_mul_right, einzwei, mul_assoc, one_mul, e1]
    congr; ext a
    simp only [mul_comm, mul_eq_mul_left_iff]
    left
    have : E.indicator (1 : X × X → ℝ) x * {y | a ≤ m y}.indicator 1 x = (E ∩ {y | a ≤ m y}).indicator 1 x := by
      rw [Set.inter_indicator_one]; congr
    rw [this]
    exact rfl
  · push_neg at cm
    have := mp x cm
    simp [this]


lemma Fintype.argmax' {X Y : Type} [Fintype X] [Nonempty X] (f : X → Y) [LinearOrder Y] : ∃ x : X, ∀ y : X, f y ≤ f x := by
  let ⟨x, ⟨_, p⟩⟩ := Finset.mem_image.mp (Finset.max'_mem (Finset.image f Finset.univ) (Finset.image_nonempty.mpr Finset.univ_nonempty))
  use x
  intro y
  convert Finset.le_max' (Finset.image f Finset.univ) (f y) (Finset.mem_image.mpr ⟨y, ⟨Finset.mem_univ y, rfl⟩⟩)

lemma maxUnion {X Y : Type} [Fintype X] [Nonempty X] [LinearOrder X] (τ : Y → X → ℝ) (nen: ∀ x, (Finset.image (τ x) Finset.univ).Nonempty)  :
    {x | Λ ≤ Finset.max' (Finset.univ.image (τ x)) (nen x)} = ⋃ i, { x | Λ ≤ τ x i} := by
  ext x
  constructor
  · simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    intro mx
    obtain ⟨i, j⟩ := Fintype.argmax' (τ x)
    use i
    have : (Finset.image (τ x) Finset.univ).max' (nen x) ≤ τ x i := by simp [j]
    exact le_trans mx this
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq, forall_exists_index]
    intros i mi
    refine le_trans mi (Finset.le_max' _ _ ?_)
    simp

----------------------------------------------------------------------------------------------------


lemma expPos {r : ℕ} {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] {σ : Fin r → (X → (V → ℝ))} :

    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i

    (0 ≤ ℙᵤ[ fun xx => f (fun i => (Z i xx)) ]) := by sorry -- big sorry. issue #8

--------------------------------------------------------------------------------------------------

lemma exp_ineq {r : ℕ} {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] {σ : Fin r → (X → (V → ℝ))} :

    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i
    let E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }

    let exp := fun xx => 3^r * r * Real.exp (∑ i, √(Z i xx + 3 * r))
    let 𝔼exp := ∫ (x : X × X ) in E, exp x ∂ℙᵤ

    1 - (ℙᵤ E).toReal ≤ 𝔼exp := by
  intros τ Z E exp 𝔼exp

  let measE := (DiscreteMeasurableSpace.forall_measurableSet E)
  have mEc : MeasurableSet Eᶜ := MeasurableSet.compl_iff.mpr measE

  have Ecb : ∫ x in Eᶜ, f fun i ↦ Z i x ∂ℙᵤ ≤ ∫ x in Eᶜ, -1 ∂ℙᵤ := by
    have : ∀ x ∈ Eᶜ, (f fun i ↦ Z i x) ≤ -1 := by
      intros x xinEc
      simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at xinEc
      exact specialFunctionEc (fun i ↦ Z i x) xinEc
    exact setIntegral_mono_on (Integrable.integrableOn IntegrableFin) (by simp) mEc this

  have Eb : ∫ x in E, f fun i ↦ Z i x ∂ℙᵤ ≤ 𝔼exp :=
    setIntegral_mono_on
      (Integrable.integrableOn IntegrableFin)
      IntegrableFin
      measE
      (fun x xinE => specialFunctionE (fun i ↦ Z i x) xinE)

  have : ∫ x in Eᶜ, -1 ∂ℙᵤ = - 1 + (ℙᵤ E).toReal := by
    simp [integral_mul_left, Measure.real, prob_compl_eq_one_sub measE]
    rw [toReal_sub_of_le, toReal_one, neg_sub]
    exact sub_eq_neg_add (ℙᵤ E).toReal 1
    exact prob_le_one
    exact one_ne_top

  rw [this] at Ecb

  have exPos : (0 ≤ ℙᵤ[ fun xx => f (fun i => (Z i xx)) ]) := expPos
  rw [← integral_add_compl measE IntegrableFin] at exPos

  have : 0 ≤ 𝔼exp + (- 1 + (ℙᵤ E).toReal) :=
    le_trans (le_trans exPos (add_le_add_right Eb _)) (add_le_add_left Ecb _)
  simp [add_assoc, add_comm] at this
  simpa [zero_le, add_comm]

----------------------------------------------------------------------------------------------------


lemma juicy {r : ℕ} {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] {X : Finset V} [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    {ℙᵤ : Measure (X × X)} [IsProbabilityMeasure ℙᵤ] {σ : Fin r → (X → (V → ℝ))} :

    let β := (3 ^ (-(4 : ℝ) * (r : ℝ)) : ℝ)
    let C := 4 * (↑r : ℝ) ^ ((3 : ℝ) / 2)
    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i
    let E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }
    (ℙᵤ E).toReal < β →
    ∃ Λ : ℝ, -1 ≤ Λ ∧ ∃ i : Fin r,
      ENNReal.ofReal (β * Real.exp (-C * √(Λ + 1))) ≤
      ℙᵤ { x : X × X | (Λ ≤ τ x i ∧ ∀ j ≠ i, -1 ≤ τ x j) }

    := by
  intros β C τ Z E h

  let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i

  let measE := (DiscreteMeasurableSpace.forall_measurableSet E)

  ----------------------------
  -- expected value inequality (eq. (3))

  let exp := fun xx => 3^r * r * Real.exp (∑ i, √(Z i xx + 3 * r))
  let 𝔼exp := ∫ (x : X × X ) in E, exp x ∂ℙᵤ

  ----------
  -- juicy bit

  have nenI (x : X × X) := Finset.Nonempty.image Finset.univ_nonempty (τ x)

  let M (x : X × X) : ℝ := Finset.max' (Finset.univ.image (τ x)) (nenI x)

  obtain ⟨Λ , ⟨minus1leΛ, le_pr⟩⟩ : ∃ (y : ℝ), (-1 ≤ y) ∧ rexp (-C * √(y + 1)) * β * r ≤ (ℙᵤ.real (E ∩ {x | y ≤ M x})) := by

    -- we assume this in eq (2) in the blueprint
    by_contra ch
    push_neg at ch


    let ecsq (c : ℝ) := fun y ↦ rexp (c * √(y + 1))
    let ecsq' (c : ℝ) := fun x ↦ (ecsq c x) * (c * (1 / (2 * √(x + 1))))


    have int_le (c : ℝ) (cpos : 0 < c) (cleC : c ≤ C - 1) :
        ∫ x in E, ecsq c (M x) ∂ℙᵤ ≤ β * (r * c + 1) := by
      simp only [Nat.ofNat_nonneg, sqrt_mul, ← MeasureTheory.integral_indicator measE]
      have (x : X×X) := @indicator_one_mul (X×X) x (fun x ↦ ecsq c (M x)) _ E
      simp_rw [← this]

      have mp (x : X × X) (aM : M x < -1) : x ∉ E := by
        simp only [neg_mul, Set.mem_setOf_eq, not_forall, not_le, E]
        use nenr.some
        have : 0 < (3 * (r : ℝ)) := by simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]; exact Fin.pos'
        rw [← (lt_div_iff₀' this)]
        ring_nf
        simp [M] at aM
        convert aM nenr.some
        exact Field.mul_inv_cancel (↑r : ℝ) (ne_of_gt (Nat.cast_pos'.mpr Fin.pos'))


      -- "For any constant c ≤ C-1, we have ..."
      have exp_bound23:
          (fun x ↦ (ecsq c (M x) * (E.indicator 1 x))) =
          (fun x ↦ ∫ a in (Set.Ioi (-1)), (ecsq' c a) * ((E ∩ { x | a ≤ M x}).indicator (fun _ ↦ 1) x)) + E.indicator (fun _ ↦ 1) :=
        exp_bound2 c M E mp

      -- first step
      have := congrArg (fun (f : (X × X → ℝ)) ↦ (∫ x, f x ∂ℙᵤ)) (exp_bound23)
      simp [integral_add, integral_indicator_const (1 : ℝ) measE] at this
      simp [this]
      rw [integral_integral_swap]
      have nn (y : ℝ) : ∫ a , (E ∩ {x | y ≤ M x}).indicator (fun x ↦ 1) a ∂ℙᵤ = ℙᵤ.real (E ∩ {x | y ≤ M x}) := by
        convert integral_indicator_const (1 : ℝ) MeasurableSet.of_discrete
        simp only [smul_eq_mul, mul_one]
        exact dm
      simp [integral_mul_left, nn]

      -- second step
      have step2 (y : ℝ) (yge : y ∈ Set.Ioi (-1)) : ecsq' c y * ℙᵤ.real (E ∩ {x | y ≤ M x}) ≤ ecsq' c y * rexp (-C * √(y + 1)) * β * r := by
        have : 0 ≤ ecsq' c y := by positivity
        have := mul_le_mul_of_nonneg_left (le_of_lt (ch y (le_of_lt yge))) this
        simpa [mul_assoc]

      -- third step
      have step3 (y : ℝ) (yge : y ∈ Set.Ioi (-1)) : ecsq' c y * (ecsq (-C) y) ≤ rexp (- √(y + 1)) * (c * (1 / (2 * √(y + 1)))) := by
        have yspos : 0 < √(y + 1) := sqrt_pos_of_pos (neg_lt_iff_pos_add.mp yge)
        simp [ecsq', ecsq, mul_comm, mul_assoc, cpos, this, ← exp_add, ← one_add_mul, cleC, yspos]
        exact le_sub_iff_add_le'.mp cleC

      have βpos : 0 ≤ β := by positivity
      have urrg (y : ℝ) (yge : y ∈ Set.Ioi (-1)) : ecsq' c y * ℙᵤ.real (E ∩ {x | y ≤ M x}) ≤ rexp (- √(y + 1)) * (c * (1 / (2 * √(y + 1))))  * β * r :=
        le_trans (step2 y yge) ( mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (step3 y yge) βpos) (Nat.cast_nonneg' r))
      apply le_trans (add_le_add_left (le_of_lt h) _) ?_
      apply le_trans (add_le_add_right (setIntegral_mono_on ?_ ?_ measurableSet_Ioi urrg) β) ?_
      · sorry
      · sorry
      · simp only [integral_mul_right]
        rw [terrible c]
        ring_nf
        exact Preorder.le_refl _

      · sorry -- whet?


    have int_le2 (c : ℝ) (cpos : 0 < c) (cleC : c ≤ C - 1) :
        ∫ x, ecsq c (M x) * E.indicator 1 x ∂ℙᵤ ≤ β * (r * c + 1) := sorry

    have int_le3 (c : ℝ) (cpos : 0 < c) (cleC : c ≤ C - 1) :
        ∫ x in E, ecsq c (M x) ∂ℙᵤ ≤ β * (r * c + 1) := by
      simp only [Nat.ofNat_nonneg, sqrt_mul, ← MeasureTheory.integral_indicator measE]
      have (x : X×X) := @indicator_one_mul (X×X) x (fun x ↦ ecsq c (M x)) _ E
      simp_rw [← this]
      exact int_le2 c cpos cleC

    have int_le4 (c : ℝ) (cpos : 0 < c) (cleC : c ≤ C - 1) :
        ∫ x in E, rexp (∑ i, √(Z i x + 3 * ↑r)) ∂ℙᵤ ≤ β * (r * (r * √(3 *r)) + 1) := by
      sorry

    -- set c := r * √(3 *r)
    have rpos : 0 < r := Fin.pos'

    have aa: (fun x ↦ rexp (∑ i, √(Z i x + 3 * ↑r))) ≤ (fun x ↦ ecsq (↑ r * √(3 * r)) (M x)) := by
      intro x
      simp only [Nat.ofNat_nonneg, sqrt_mul, exp_le_exp, Z, ecsq, M, C]
      exact sum_sqrt_le

    have bb: ∫ x in E, rexp (∑ i, √(Z i x + 3 * ↑r)) ∂ℙᵤ ≤ ∫ x in E, ecsq (↑ r * √(3 * r)) (M x) ∂ℙᵤ :=
      MeasureTheory.setIntegral_mono sorry sorry aa

    have : ∫ x in E, rexp (∑ i, √(Z i x + 3 * ↑r)) ∂ℙᵤ ≤ β * (↑r * (↑r * √(3 * r)) + 1) :=
      le_trans bb (int_le _ (by positivity) (C_ineq rpos))

    have := calc 1 - (ℙᵤ E).toReal
      _ ≤ 𝔼exp := exp_ineq
      _ = (3 ^ r * ↑r ) * ∫ x in E, rexp (∑ i, √(Z i x + 3 * ↑r)) ∂ℙᵤ
          := by simp only [integral_mul_left, 𝔼exp, Z, C, ecsq, M, exp]
      _ ≤ (3 ^ r * ↑r ) * (β * (↑r * (↑r * √(3 * r)) + 1))
          := by simp_all only [Nat.cast_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_right, pow_pos, _root_.mul_le_mul_left]
      _ ≤ 1/3 := by simp [β, three_ineq]

    have : 2/3 ≤ (ℙᵤ E).toReal := by linarith
    have βle : β < 2/3 := by
      simp[β]
      have : (3 : ℝ) ^ (-(4 * (r: ℝ))) ≤ (3 : ℝ) ^ (-(4 : ℝ)) := by simpa
      exact lt_of_le_of_lt this (by linarith)

    exact (lt_self_iff_false _).mp (lt_trans βle (lt_of_le_of_lt this h))

  use Λ, minus1leΛ

  rw [(maxUnion τ nenI), Set.inter_iUnion] at le_pr

  obtain ⟨i, pip⟩ := Fin.exists_mul_of_sum_bound (fun i ↦ ℙᵤ (E ∩ {x | Λ ≤ τ x i}))
  use i

  have Eiff : (E ∩ {x | Λ ≤ τ x i}) =
      {x | Λ ≤ τ x i ∧ (∀ (j : Fin r), j ≠ i → -1 ≤ τ x j) } := by
    ext x
    simp [and_comm, neg_mul, Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff, E, τ]
    intro l
    constructor
    · intro xM j jni
      exact omg6.mp (xM j)
    · intro nj j
      by_cases jeqi : j = i
      · subst jeqi
        exact omg6.mpr (le_trans minus1leΛ l)
      · exact omg6.mpr (nj j jeqi)

  simp only [τ, ← Eiff]
  refine omg5.mpr (le_trans ?_ pip)

  have union_bound := measure_iUnion_fintype_le ℙᵤ fun i ↦ (E ∩ {x | Λ ≤ τ x i})
  have union :=
    ofReal_le_of_le_toReal (le_trans
      (le_pr)
      ((toReal_le_toReal (measure_ne_top ℙᵤ (⋃ i, E ∩ {x | Λ ≤ τ x i})) (by simp)).mpr union_bound))

  convert union
  simp [mul_comm, mul_assoc, ofReal_mul (Nat.cast_nonneg' r)]

----------------------------------------------------------------------------------------------------

lemma geometric {V : Type} [Fintype V] [nenr: Nonempty (Fin r)] (X : Finset V) [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass (X × X)] [dm: DiscreteMeasurableSpace (X × X)] [DecidableEq X]
    (ℙᵤ : Measure (X × X)) [IsProbabilityMeasure ℙᵤ] (σ : Fin r → (X → (V → ℝ))) :

    let β := (3 ^ (-(4 : ℝ) * (r : ℝ)) : ℝ)
    let C := 4 * (↑r : ℝ) ^ ((3 : ℝ) / 2)
    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)


    ∃ Λ : ℝ, -1 ≤ Λ ∧ ∃ i : Fin r,
      ENNReal.ofReal (β * Real.exp (-C * √(Λ + 1))) ≤
      ℙᵤ { x : X × X | (Λ ≤ τ x i ∧ ∀ j ≠ i, -1 ≤ τ x j) }

    := by
  intros β C τ

  let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i

  set E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx } with eE
  let measE := (DiscreteMeasurableSpace.forall_measurableSet E)

  by_cases h : β ≤ (ℙᵤ E).toReal
  · exists -1
    have (i : Fin r) (x : X × X) := @and_forall_ne (Fin r) (fun i => -1 ≤ τ x i) i

    simp only [le_refl, neg_add_cancel, Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one, ne_eq, true_and, this]

    have (x : X × X) : (∀ (b : Fin r), -1 ≤ τ x b) ↔ (∀  (i : Fin r), -3 * r ≤ (Z i x)) := by
      have : ∀ i, (-3 * ↑r ≤ 3 * ↑r * τ x i ↔ -1 ≤ τ x i) := by simp [omg6]
      simp_rw [Z, this]
    simp_rw [this, ← eE, ofReal_le_of_le_toReal h]

    exists ⟨0, Fin.pos'⟩
  · push_neg at h
    exact juicy h
