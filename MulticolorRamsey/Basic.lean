import Mathlib.Combinatorics.SimpleGraph.Basic

import Mathlib.Probability.Distributions.Uniform

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

import Mathlib.Combinatorics.SimpleGraph.Subgraph

import ExponentialRamsey.Prereq.Ramsey

import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Insert

import ToMathlib.EvenEquivNat.Basic

----------------------------------------------------------------------------------------------------
--  edge colorings

open Finset
open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {K K' : Type*} {c : K} {EC : G.EdgeLabelling K}

namespace EdgeLabelling

/-- `EC.coloredNeighborSet c v` is the set of vertices that have an edge to `v` in `G` which is
colored with `c` under the edge coloring `EC`. -/
def coloredNeighborSet {EC : G.EdgeLabelling K} (c : K) (v : V) : Set V :=
  -- {w | ∃ p : G.Adj v w, EC ⟨s(v,w), p⟩ = c}
  {w | w ∈ G.neighborSet v ∧ ∃ p, EC ⟨s(v, w), p⟩ = c}

lemma coloredNeighborSet_not_mem (c : K) (v : V) :
    v ∉ EC.coloredNeighborSet c v := by
  simp [EdgeLabelling.coloredNeighborSet]

instance coloredNeighborSetFintype [Fintype V] [DecidableRel G.Adj] [DecidableEq K] :
    Fintype (EC.coloredNeighborSet c v) := by
  simp [coloredNeighborSet]
  exact Subtype.fintype _

lemma coloredNeighborSet.symm (c : K) (v w : V) :
    w ∈ EC.coloredNeighborSet c v ↔ v ∈ EC.coloredNeighborSet c w := by
  simp [EdgeLabelling.coloredNeighborSet]
  sorry

end EdgeLabelling

namespace TopEdgeLabelling

open EdgeLabelling

variable {m : Finset V} {c : K} {EC : TopEdgeLabelling V K}

lemma monochromaticBetween_neighbors {c : K} {y : V} {T : Finset V}
    (h : ∀ x ∈ T, y ∈ EC.coloredNeighborSet c x) : EC.MonochromaticBetween T {y} c := by
  simp only [MonochromaticBetween, mem_coe, Set.mem_singleton_iff, top_adj, ne_eq, forall_eq]
  intros v vT vny
  exact (h v vT).2.choose_spec

/-- `EC.monochromatic c T Y` if `T` and `Y` are disjoint, all edges within `T` and all edges between
 `T` and `Y`are given color `c` by `EC`. -/
def MonochromaticBook (c : K) (T Y : Finset V) :=
  Disjoint T Y ∧ EC.MonochromaticOf T c ∧ EC.MonochromaticBetween T Y c

lemma monochromaticBook_subset {A B D : Finset V}
    (b : EC.MonochromaticBook i A B) (s : D ⊆ B) : EC.MonochromaticBook i A D :=
  ⟨(Finset.disjoint_of_subset_right s b.1), b.2.1, b.2.2.subset_right s ⟩

lemma monochromaticBook_pullback {V : Type u_1} {V' : Type u_2} {K : Type u_3}
  {EC : TopEdgeLabelling V K} (f : V' ↪ V) (c : K) (T Y : Finset V') (B : (EC.pullback f).MonochromaticBook c T Y)
   : EC.MonochromaticBook c (T.map f) (Y.map f) := by
  simp [MonochromaticBook] at B ⊢
  exact ⟨B.1, ⟨B.2.1, MonochromaticBetween.image B.2.2⟩⟩

lemma monochromaticBook_empty {A : Finset V}
 : EC.MonochromaticBook i ∅ A := by constructor <;> simp



end TopEdgeLabelling


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
-- coshsqrt0

section

open Real

noncomputable def coshsqrt (x : ℝ) :=  ∑' n : ℕ , (x ^ n / ((2 * n).factorial : ℝ))

lemma mew {x} (xpos: (0 : ℝ) ≤ x) : Summable (fun n ↦ (x ^ n / (2 * n).factorial)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (Real.summable_pow_div_factorial x)
    all_goals intro b
    positivity
    refine div_le_div₀ (pow_nonneg xpos b) (Preorder.le_refl (x ^ b)) (by positivity) ?_
    exact Nat.cast_le.mpr (Nat.factorial_le (by linarith))

lemma lt_coshsqrt (x : ℝ) (xnn : 0 ≤ x) : x < 2 + coshsqrt x := by
  have : coshsqrt x = 1 + x / 2 + x ^ 2 / ↑(4).factorial + ∑' (i : ℕ), x ^ (i + 3) / (2 * (i + 3)).factorial := by
    simp [coshsqrt, ← Summable.sum_add_tsum_nat_add 3 (mew xnn), Finset.sum, add_comm]
  simp [this]
  have : 2 + (1 + x / 2 + x ^ 2 / (Nat.factorial 4) + ∑' (i : ℕ), x ^ (i + 3) / (2 * (i + 3)).factorial) =
      (3 + x / 2 + x ^ 2 / (Nat.factorial 4)) + ∑' (i : ℕ), x ^ (i + 3) / (2 * (i + 3)).factorial := by ring
  simp [this]
  suffices x < 3 + x / 2 + x ^ 2 / 24 from lt_add_of_lt_of_nonneg this <| tsum_nonneg (by intro; positivity)
  nlinarith

lemma ge_coshsqrt (x : ℝ) (xnn : 0 ≤ x) : 2 + coshsqrt x ≤ 3 * Real.exp √x := by
  have : coshsqrt x ≤ rexp √x := by
    simp [coshsqrt, Real.exp_eq_exp_ℝ, NormedSpace.exp, NormedSpace.expSeries_sum_eq_div]
    -- "compare coefficients"
    have : ∑' (a : ℕ), ENNReal.ofReal (x ^ a / (2 * a).factorial) ≤ ∑' (a : ℕ), ENNReal.ofReal (√x ^ a / a.factorial) := by
      nth_rw 2 [← Summable.tsum_add_tsum_compl (s := { n : ℕ | Even n}) (by simp) (by simp)]
      rw [← tsum_double_eq_tsum_even (fun n ↦ ENNReal.ofReal (√x ^ n / (n : ℕ).factorial))]
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

lemma icc_coshsqrt_neg (x : ℝ) (xnn : x ≤ 0) : coshsqrt x ∈ Set.Icc (-1) 1 := by
  have : coshsqrt x = Real.cos √(-x) := by
    rw [Real.cos_eq_tsum, coshsqrt]
    congr; ext n; congr
    rw [pow_mul, sq_sqrt]
    by_cases h : Even n
    · simp [h.neg_pow]
    · rw [Nat.not_even_iff_odd] at h
      rw [h.neg_one_pow, h.neg_pow]
      simp
    exact Left.nonneg_neg_iff.mpr xnn
  rw [this]
  exact cos_mem_Icc √(-x)

lemma coshsqrt_pos {x : ℝ} (xn : x ≤ 0) : 0 < 2 + coshsqrt x := by
  have := Set.mem_Icc.mp (icc_coshsqrt_neg x xn)
  linarith

lemma coshsqrt_nonneg {x : ℝ} : 0 ≤ 2 + coshsqrt x := by
  by_cases xnn : 0 ≤ x
  · exact le_trans xnn (le_of_lt (lt_coshsqrt x xnn))
  · exact le_of_lt (coshsqrt_pos (le_of_lt (lt_of_not_ge xnn)))


lemma coshsqrt_mono {x y : ℝ} (xnn : 0 ≤ x) (xly : x ≤ y) : coshsqrt x ≤ coshsqrt y := by
  simp [coshsqrt]
  have ynn : 0 ≤ y := by trans x; exact xnn; exact xly
  have : ∑' (a : ℕ), ENNReal.ofReal (x ^ a / (2 * a).factorial) ≤ ∑' (a : ℕ), ENNReal.ofReal (y ^ a / (2 * a).factorial) := by
    gcongr
  rw [← ENNReal.ofReal_tsum_of_nonneg (by intros; positivity) (mew xnn)] at this
  rw [← ENNReal.ofReal_tsum_of_nonneg (by intros; positivity) (mew ynn)] at this
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
  exact this

lemma one_le_coshsqrt (x : ℝ) : 1 ≤ 2 + coshsqrt x := by
  by_cases h : 0 < x
  · have : 1 ≤ coshsqrt x := by
      trans 1 + ∑' (i : ℕ), x ^ (i + 1) / ↑(2 * (i + 1)).factorial
      simp; positivity
      simp [coshsqrt, ← Summable.sum_add_tsum_nat_add 1 (mew (le_of_lt h)), Finset.sum]
    linarith
  · have := (Set.mem_Icc.mp (icc_coshsqrt_neg x (le_of_not_gt h))).left
    linarith

-- TODO hmmm. mathlib? there is a version with [IsOrderedMonoid R] but not requiring zero
-- but the reals are not
theorem Finset.one_le_prod''' {R ι : Type*}
    [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  apply le_trans (le_of_eq prod_const_one.symm)
  gcongr with i hh
  exact fun _ _ ↦ zero_le_one' R
  exact h i hh

----------------------------------------------------------------------------------------------------
-- special function lemma

noncomputable def f (x : Fin r → ℝ) : ℝ :=
  ∑ j : Fin r, x j * (1 / (2 + coshsqrt (x j))) * (∏ i : Fin r, (2 + coshsqrt (x i)))

lemma specialFunctionE (x : Fin r → ℝ) : f x ≤ 3^r * r * Real.exp (∑ i, Real.sqrt (x i + 3 * r)) := by
  simp only [f, ← Finset.sum_mul]

  trans r * ∏ i, (2 + coshsqrt (x i))

  · gcongr
    · exact Finset.prod_nonneg fun _ _ ↦ coshsqrt_nonneg
    · trans (∑ i : Fin r, 1)
      · gcongr; expose_names
        by_cases h : 0 < x i
        · rw [← div_eq_mul_one_div]
          have := lt_coshsqrt (x i) (le_of_lt h)
          refine le_of_lt ((div_lt_one ?_).mpr this)
          linarith
        · push_neg at h
          have : 1 / (2 + coshsqrt (x i)) * x i ≤ 0 := by
            refine mul_nonpos_of_nonneg_of_nonpos ?_ h
            have := (Set.mem_Icc.mp (icc_coshsqrt_neg (x i) h)).right
            have := coshsqrt_pos h
            have : 0 ≤ 1 / (2 + coshsqrt (x i)) := by positivity
            linarith
          linarith
      · simp

  · rw [mul_comm (3 ^ r), mul_assoc]
    gcongr
    · simp_rw [Real.exp_sum, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      gcongr <;> expose_names
      · intros; exact coshsqrt_nonneg
      · by_cases h : 0 < x i
        · trans 3 * rexp √(x i)
          exact ge_coshsqrt _ (le_of_lt h)
          gcongr; simp
        · push_neg at h
          have := (Set.mem_Icc.mp (icc_coshsqrt_neg (x i) h)).right
          have : 3 ≤ 3 * rexp √(x i + 3 * ↑r) := by simp
          linarith


lemma specialFunctionEc (rpos : 0 < r) (x : Fin r → ℝ) (h : ∃ i, x i < -3 * r) :
    f x ≤ -1 := by
  obtain ⟨i, xil⟩ := h

  have t1 (x : ℝ) : x * (1 / (2 + coshsqrt x)) ≤ 1 := by
    by_cases hh : 0 < x
    · trans x * (1 / x)
      gcongr
      exact le_of_lt (lt_coshsqrt x (le_of_lt hh))
      simp [mul_inv_le_one]
    · push_neg at hh
      have := coshsqrt_pos hh
      have : 0 ≤ 1 / (2 + coshsqrt x) := by positivity
      trans 0; exact mul_nonpos_of_nonpos_of_nonneg hh this; exact zero_le_one' ℝ

  have t2 : (x i) * (1 / (2 + coshsqrt (x i))) ≤ (x i) / 3 := by
    rw [div_eq_mul_one_div _ 3]
    have : x i < 0 := lt_of_lt_of_le xil (by nlinarith)
    apply (mul_le_mul_left_of_neg _).mpr
    · gcongr; exact coshsqrt_pos (le_of_lt this)
      have := (Set.mem_Icc.mp (icc_coshsqrt_neg (x i) (le_of_lt this))).right
      linarith
    · exact this

  have t3 : ∑ j, x j * (1 / (2 + coshsqrt (x j))) ≤ -1 := by
    trans (x i) / 3 + (r - 1)
    · rw [Fintype.sum_eq_add_sum_compl i]
      gcongr
      trans ∑ i ∈ {i}ᶜ, 1
      gcongr; expose_names; exact t1 (x i_1)
      simp only [Finset.sum_const, Finset.card_compl, Fintype.card_fin, Finset.card_singleton,
        nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub]
      simp; exact rpos
    · linarith

  have t4 : 1 ≤ ∏ i, (2 + coshsqrt (x i)) := by
    refine Finset.one_le_prod''' ?_
    intros i _; expose_names; exact one_le_coshsqrt (x i)

  simp only [f, mul_comm _  (∏ i, (2 + coshsqrt (x i))), ← Finset.mul_sum]
  trans (∏ i, (2 + coshsqrt (x i))) * (-1)
  gcongr
  linarith

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
                  _ = (Fintype.card X) • g j := by simp only [sum_const, card_univ]

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
  exact not_lt_of_ge (mmin z zs) mltz

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
      simp_all only [not_exists, Set.setOf_false, measure_empty, lt_self_iff_false]


lemma pidgeon_sum {X Y : Type} [nenx: Nonempty X] [fin: Fintype X] [nen: Nonempty Y] [fin: Fintype Y]
    (p : X → Y → Prop) [∀ i j, Decidable (p i j)] {β : Real} :
    β ≤ ((Fintype.card {x : X × Y | p x.1 x.2}) : ℝ) / ((Fintype.card (X × Y)) : ℝ) →
    ∃ x : X, ∃ Y' : Finset Y, β * (Fintype.card Y) ≤ ((Y'.card) : ℝ) ∧ ∀ y ∈ Y', p x y := by

  intros bound
  let f := fun x ↦ (# { y : Y | p x y} : ℝ)

  have card_sum : ∑ i : X, f i = Fintype.card {x : X × Y // p x.1 x.2} := by
    have := Fintype.sum_prod_type' (fun i j ↦ if p i j then 1 else 0)
    rw [Fintype.card_subtype, Finset.card_filter, this]
    simp only [sum_boole, Nat.cast_id, Nat.cast_sum, f]

  have : β * (Fintype.card Y) ≤ univ.expect f := by
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
  ext; simp

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
    ∑ i, √(3 * r * τ x i + 3 * r) ≤ r * (√3 * √r) * √((M x) + 1) := by
  intro M
  have (i : Fin r) : √(3 * r * τ x i + 3 * r) ≤ √(3 * r * (M x) + 3 * r) := by
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


lemma three_ineq_ENN {r : ℕ} (rpos: 0 < r) :
    r * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * 3 ^ r * 3 + r ^ 3 * ENNReal.ofReal (3 ^ (-((r : ℝ) * 4))) * ENNReal.ofReal (√3) * ENNReal.ofReal (√r) * 3 ^ r * 3 ≤ 1 := by
  sorry

-- TODO i just put here everything that annoyed me
lemma omg5 {a b c : ENNReal} : a * b ≤ a * c ↔ b ≤ c := by
  constructor
  · sorry
  · exact fun a_1 ↦ mul_le_mul_left' a_1 a

lemma omg6 {a b : ℝ} (ap : 0 ≤ a) : - a ≤ a * b ↔ -1 ≤ b := by
  constructor
  · intro h
    sorry
  · intro h
    have : -a = a * (-1) := by ring
    rw [this]
    gcongr
