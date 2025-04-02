import MulticolorRamsey.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Tactic.Linarith


open MeasureTheory ProbabilityTheory Real

variable (r : ℕ)


lemma geometric {V : Type} [Fintype V] [Nonempty (Fin r)] (X : Finset V) [Nonempty X] [MeasurableSpace X] [DecidableEq X]
    (U : Measure X) [IsProbabilityMeasure U] (σ : Fin r → (X → (V → ℝ))) :
    let β := 1 / (3 ^ ((4 : ℝ) * r) : ℝ)
    let C := 4 * (↑r : ℝ) ^ (3 / 2)
    let ℙᵤ := (U.prod U)
    ∃ Λ : ℝ, -1 ≤ Λ ∧ ∃ i : Fin r,
      ENNReal.ofReal (β * Real.exp (-C * Real.sqrt (Λ + 1))) ≤
      ℙᵤ { x : X × X | (Λ ≤ (σ i x.1) ⬝ᵥ (σ i x.2) ∧ ∀ j ≠ i, -1 ≤ (σ j x.1) ⬝ᵥ (σ j x.2)) }
    := by
  intros β C ℙᵤ

  let Z (i : Fin r) : (X × X) → ℝ := fun x => (3 : ℝ) * (r : ℝ) * (σ i x.1) ⬝ᵥ (σ i x.2)

  set E : Set (X × X) := { xx : X × X |  ∀ i, -(3 : ℝ) * r ≤ Z i xx } with eE
  have mE : MeasurableSet E := by sorry


  by_cases h : ENNReal.ofReal β ≤ ℙᵤ E
  · exists -1
    have (i : Fin r) (x : X × X) := @and_forall_ne (Fin r) (fun i => -1 ≤ σ i x.1 ⬝ᵥ σ i x.2) i

    simp only [le_refl, neg_add_cancel, Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one, ne_eq, true_and, this]

    have (x : X × X) : (∀ (b : Fin r), -1 ≤ σ b x.1 ⬝ᵥ σ b x.2) ↔ (∀  (i : Fin r), -3 * r ≤ (Z i x)) := by
      have : ∀ i, (-3 * ↑r ≤ 3 * ↑r * σ i x.1 ⬝ᵥ σ i x.2 ↔ -1 ≤ σ i x.1 ⬝ᵥ σ i x.2) := by simp [omg6]
      simp_rw [Z, this]
    simp_rw [this, ← eE, h]

    exists ⟨0, Fin.pos'⟩
  ·

    ----------------------------
    -- expected value positivity
    have exPos : 0 ≤ ℙᵤ[ fun xx => f (fun i => (Z i xx)) ] := by
      have moment := moments X σ (fun _ => 1) U

      simp_rw [f]
      rw [MeasureTheory.integral_finset_sum]
      refine Fintype.sum_nonneg ?_
      simp [Pi.le_def]
      intro i

      -- refine integral_nonneg ?_
      -- simp [Pi.le_def]
      -- intro x xX y yX
      -- set a : { x // x ∈ X } × { x // x ∈ X } := (⟨x, xX⟩, ⟨y, yX⟩)
      let f1 := fun x ↦ Z i x * (2 + coshsqrt (Z i x))⁻¹ * ∏ j : Fin r, (2 + coshsqrt (Z j x))
      have i1 : Integrable f1 ℙᵤ := sorry
      let f2 := fun x ↦ ∏ j : Fin r, Z j x
      have i2 : Integrable f2 ℙᵤ := sorry

      have : f2 ≤ f1 := by
          intro a
          sorry
        -- simp_rw [coshsqrtge]

      have : ∫ (x : X × X), f2 x ∂ℙᵤ ≤ ∫ (x : X × X), f1 x ∂ℙᵤ := integral_mono i2 i1 this


      refine le_trans moment ?_
      simp_rw [f1, f2, Z] at this
      sorry
      sorry

    ----------------------------
    -- expected value inequality

    let exp := fun xx => 3^r * r * Real.exp (∑ i, Real.sqrt (Z i xx + 3 * r))
    let ℙE := ENNReal.ofReal (∫ (x : X × X ) in E, exp x ∂ℙᵤ)

    have mEc := MeasurableSet.compl_iff.mpr mE

    have IZ : Integrable (fun xx ↦ f fun i ↦ Z i xx) ℙᵤ := by
      sorry

    have cp : (ℙᵤ Eᶜ) = 1 - (ℙᵤ E) := MeasureTheory.prob_compl_eq_one_sub mE

    have : 0 ≤ ℙE - (ℙᵤ Eᶜ) := by positivity

      -- wow i thought i had to do all of this terrible things thank you yves <3
      -- rw [← MeasureTheory.integral_add_compl mE IZ] at exPos

      -- have Ecb : ∫ (x : X × X ) in Eᶜ, f fun i ↦ Z i x ∂ℙᵤ ≤
      --     ∫ (x : X × X ) in Eᶜ, -1 ∂ℙᵤ := by
      --   have : ∀ x ∈ Eᶜ, (f fun i ↦ Z i x) ≤ -1 := by
      --     intros x xinEc
      --     simp only [eE, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at xinEc
      --     exact specialFunctionEc (fun i ↦ Z i x) xinEc
      --   exact MeasureTheory.setIntegral_mono_on (MeasureTheory.Integrable.integrableOn IZ) (by simp) mEc this

      -- have Eb : ∫ (x : X × X ) in E, f fun i ↦ Z i x ∂ℙᵤ ≤
      --     ∫ (x : X × X ) in E, exp x ∂ℙᵤ :=
      --   MeasureTheory.setIntegral_mono_on (MeasureTheory.Integrable.integrableOn IZ) (sorry) mE (fun x xinE => specialFunctionE (fun i ↦ Z i x) xinE)

      -- simp only [zero_le]


    ------------
    -- juicy bit

    let M (Λ : ℝ) (i : Fin r) := { x : X × X | Λ ≤ (σ i x.1) ⬝ᵥ (σ i x.2) }
    let bound Λ := ENNReal.ofReal (β *  Real.exp (-C*Real.sqrt (Λ + 1)))

    obtain ⟨Λ , ⟨minus1leΛ, le_pr⟩⟩ : ∃ Λ , -1 ≤ Λ ∧ (r * bound Λ) ≤ ℙᵤ (⋃ i, M Λ i ∩ E) := by
      by_contra h
      push_neg at h
      -- let m (x : X × X) : ENNReal := ENNReal.ofReal (Finset.max { (σ i x.1 ⬝ᵥ σ i x.2) | i : Fin r})
      -- have : ∀ c, c ≤ C - 1 →
      --     ℙᵤ[ fun x ↦ Real.exp (c * Real.sqrt ((m x) + 1)) * (𝕀s E x)] ≤ ENNReal.ofReal (β * (c * ↑r + 1 : ℝ) ):= sorry
      sorry -- juicy bit

    use Λ, minus1leΛ

    have union : r * bound Λ ≤ ∑ i, ℙᵤ (M Λ i ∩ E) :=
      le_trans (le_pr) (measure_iUnion_fintype_le ℙᵤ fun i ↦ M Λ i ∩ E) -- "union bound"

    obtain ⟨i, pip⟩ := exists_mul_of_sum_bound (fun i ↦ ℙᵤ (M Λ i ∩ E))

    use i

    have Eiff : M Λ i ∩ E =
        {x | Λ ≤ σ i x.1 ⬝ᵥ σ i x.2 ∧ ∀ (j : Fin r), j ≠ i → -1 ≤ σ j x.1 ⬝ᵥ σ j x.2} := by
      ext x
      simp only [neg_mul, Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff, M, f, E, Z]
      intro l
      constructor
      · intro xM j jni
        exact omg6.mp (xM j)
      · intro nj j
        by_cases jeqi : j = i
        · subst jeqi
          exact omg6.mpr (le_trans minus1leΛ l)
        · exact omg6.mpr (nj j jeqi)

    simp only [← Eiff]
    exact omg5.mpr (le_trans union pip)
