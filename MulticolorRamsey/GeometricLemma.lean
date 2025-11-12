import MulticolorRamsey.Basic
import MulticolorRamsey.Integrals

open MeasureTheory ProbabilityTheory Real ENNReal Set Fin

variable {V : Type} {X : Finset V} [MeasurableSpace X] {ℙᵤ : Measure (X × X)} [dm: DiscreteMeasurableSpace (X × X)]
 [MeasurableSingletonClass (X × X)] [IsProbabilityMeasure ℙᵤ]

lemma exp_ineq_ENN (rpos : 0 < r) (Z : Fin r → X × X → ℝ) (exPos : 0 ≤ ℙᵤ[ fun xx => f (fun i => Z i xx) ]) :
    let E : Set (X × X) := { xx |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }
    let exp := fun x => 3^r * r * exp (∑ i, √(Z i x + 3 * r))

    (1 : ENNReal) - ℙᵤ E ≤ ∫⁻ x in E, oℝ (exp x) ∂ℙᵤ := by
  intros E exp

  -- convert to bocher (non-lebesque) integral because we want to talk about negative
  let 𝔼exp := ∫ x in E, exp x ∂ℙᵤ
  have : oℝ 𝔼exp = ∫⁻ x in E, oℝ (exp x) ∂ℙᵤ := by
    apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    simp; filter_upwards; intro; positivity
  simp_rw [← this]

  apply (toReal_le_toReal (by simp) (by simp)).mp
  rw [toReal_ofReal (by positivity), toReal_sub_of_le prob_le_one one_ne_top, toReal_one]

  let measE := DiscreteMeasurableSpace.forall_measurableSet E

  have Ecb : ∫ x in Eᶜ, f fun i ↦ Z i x ∂ℙᵤ ≤ ∫ x in Eᶜ, -1 ∂ℙᵤ := by
    have : ∀ x ∈ Eᶜ, (f fun i ↦ Z i x) ≤ -1 := by
      intros x xinEc
      simp only [E, mem_compl_iff, mem_setOf_eq, not_forall, not_le] at xinEc
      exact specialFunctionEc rpos (fun i ↦ Z i x) xinEc
    exact setIntegral_mono_on integrable_of_fintype.integrableOn (by simp) (MeasurableSet.compl_iff.mpr measE) this

  have Eb : ∫ x in E, f fun i ↦ Z i x ∂ℙᵤ ≤ 𝔼exp :=
    setIntegral_mono_on
      integrable_of_fintype.integrableOn integrable_of_fintype measE
      (fun x _ => specialFunctionE (fun i ↦ Z i x))

  have : ∫ x in Eᶜ, -1 ∂ℙᵤ = - 1 + (ℙᵤ E).toReal := by
    simp [Measure.real, prob_compl_eq_one_sub measE]
    rw [toReal_sub_of_le prob_le_one one_ne_top, toReal_one, neg_sub]
    exact sub_eq_neg_add (ℙᵤ E).toReal 1

  rw [this] at Ecb

  rw [← integral_add_compl measE integrable_of_fintype] at exPos

  have : 0 ≤ 𝔼exp + (- 1 + (ℙᵤ E).toReal) :=
    le_trans (le_trans exPos (add_le_add_right Eb _)) (add_le_add_left Ecb _)
  simp [add_assoc, add_comm] at this
  simpa [add_comm]

----------------------------------------------------------------------------------------------------

variable [Fintype V] [nenr: Nonempty (Fin r)] (σ : Fin r → (X → (V → ℝ)))

omit [IsProbabilityMeasure ℙᵤ] in
lemma lintegral_sum_bound :

    let β := oℝ (3 ^ (-(4 : ℝ) * (r : ℝ)))
    let C := 4 * (r : ENNReal) * oℝ (√r)
    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i
    let E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx }

    have nenI (x : X × X) := Finset.Nonempty.image Finset.univ_nonempty (τ x)

    let M (x : X × X) : ℝ := Finset.max' (Finset.univ.image (τ x)) (nenI x)
    let c := oℝ (r * √(3 * r))

    ℙᵤ E < β →
    (∀ y, -1 ≤ y → ℙᵤ (E ∩ {x | y ≤ M x}) < oℝ (rexp (-C.toReal * √(y + 1))) * β * r) →

    ∫⁻ x in E, oℝ (rexp (∑ i, √(Z i x + 3 * r))) ∂ℙᵤ ≤ β * (r * c + 1) := by
  intros β C _ Z E nenI M c βge ch

  have rpos : 0 < r := Fin.pos'

  let exp := fun xx => 3^r * r * exp (∑ i, √(Z i xx + 3 * r))
  let 𝔼exp := ∫⁻ (x : X × X ) in E, oℝ (exp x) ∂ℙᵤ
  let cℝ := c.toReal

  have cc :
      ∀ x ∈ E, oℝ (rexp (∑ i, √(Z i x + 3 * r))) ≤ oℝ (rexp (cℝ * √((M x) + 1))) := by
    intro x xE
    apply ofReal_le_ofReal
    simp [Nat.ofNat_nonneg, sqrt_mul, exp_le_exp, Z, cℝ, c]
    exact sum_sqrt_le

  have dd :
      ∫⁻ x in E, oℝ (rexp (cℝ * √((M x) + 1))) ∂ℙᵤ ≤ β * (r * c + 1) := by
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
      simp
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

lemma expPos :

    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * τ x i

    (0 ≤ ℙᵤ[ fun xx => f (fun i => (Z i xx)) ]) := by sorry -- big sorry. issue #8

--------------------------------------------------------------------------------------------------

lemma geometric :

    let β := (3 ^ (-(4 : ℝ) * (r : ℝ)) : ℝ)
    let C := 4 * (r : ℝ) * √r
    let τ (x : X × X) (i : Fin r) := (σ i x.1) ⬝ᵥ (σ i x.2)

    ∃ Λ : ℝ, -1 ≤ Λ ∧ ∃ i : Fin r,
      oℝ (β * exp (-C * √(Λ + 1))) ≤ ℙᵤ { x : X × X | (Λ ≤ τ x i ∧ ∀ j ≠ i, -1 ≤ τ x j) }

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

    have nenI (x : X × X) := Finset.Nonempty.image Finset.univ_nonempty (τ x)
    let M (x : X × X) : ℝ := Finset.max' (Finset.univ.image (τ x)) (nenI x)

    obtain ⟨Λ , ⟨minus1leΛ, le_pr⟩⟩ :
        ∃ (y : ℝ), (-1 ≤ y) ∧ rexp (-C * √(y + 1)) * β * r ≤ (ℙᵤ.real (E ∩ {x | y ≤ M x})) := by
      have rpos : 0 < r := Fin.pos'

      let c := oℝ (r * √(3 * r))

      let exp := fun xx => 3^r * r * exp (∑ i, √(Z i xx + 3 * r))
      let 𝔼exp := ∫⁻ (x : X × X ) in E, oℝ (exp x) ∂ℙᵤ

      obtain ⟨Λ, ⟨Λle, ee⟩⟩ :
          ∃ (y : ℝ), (-1 ≤ y) ∧
          oℝ (rexp (-(((4 * r * oℝ (√r))).toReal) * √(y + 1))) * (oℝ β) * r ≤ ℙᵤ (E ∩ {x | y ≤ M x}) := by

        -- we assume this in eq (2) in the blueprint
        by_contra ch
        push_neg at ch

        have := (lt_ofReal_iff_toReal_lt (measure_ne_top ℙᵤ E)).mpr h
        have := lintegral_sum_bound σ this ch

        have ca := calc 1 - oℝ β
          _ ≤ 1 - (ℙᵤ E) := by gcongr
          _ ≤ 𝔼exp := exp_ineq_ENN rpos Z (expPos σ)
          _ = (3 ^ r * r ) * ∫⁻ x in E, oℝ (rexp (∑ i, √(Z i x + 3 * r))) ∂ℙᵤ
              := by simp [𝔼exp, exp];
                    simp_rw [ENNReal.ofReal_mul' (exp_nonneg _)];
                    rw [lintegral_const_mul]; congr; norm_cast
                    exact Measurable.of_discrete
          _ ≤ (3 ^ r * r ) * ( (oℝ β) * (r * c + 1))
              := by gcongr -- uses lintegral_sum_bound
          _ ≤ 1/3 := by simp [β, c]; ring_nf; exact three_ineq_ENN rpos

        have : 1 / 3 < 1 - oℝ β := by
          simp [β]
          rw [← ofReal_one, ← ofReal_sub _ (by positivity)]
          apply (lt_ofReal_iff_toReal_lt (three_ne_zero ∘ inv_eq_top.mp)).mpr
          simp only [toReal_inv, toReal_ofNat]
          have : (3 : ℝ) ^ (-(4 * (r : ℝ))) ≤ 1 / (3 ^ (4 : ℝ)) := by
            rw [Real.rpow_neg (by positivity)]
            field_simp
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            gcongr
            simp
            norm_cast
            linarith
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
      refine ⟨?_ , fun xM j _ ↦ (omg6 (by positivity)).mp (xM j)⟩
      · intro nj j
        refine (omg6 (by positivity)).mpr ?_
        by_cases jeqi : j = i
        · subst jeqi
          exact le_trans minus1leΛ l
        · exact nj j jeqi

    simp only [Eiff]
    refine omg5.mp (le_trans ?_ pip)

    have union_bound := measure_iUnion_fintype_le ℙᵤ fun i ↦ (E ∩ {x | Λ ≤ τ x i})
    have union :=
      ofReal_le_of_le_toReal (le_trans
        le_pr
        ((toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr union_bound))

    convert union
    simp only [mul_comm, ofReal_mul (Nat.cast_nonneg' r), ofReal_natCast, β]
