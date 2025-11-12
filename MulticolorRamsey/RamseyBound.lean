import MulticolorRamsey.Book

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Card
import ToMathlib.SwapIteEq.Basic

variable {V : Type} {r : ℕ} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty (Fin r)]

open Finset SimpleGraph


----------------------------------------------------------------------------------------------------
-- the "Erdős-Szekeres bound"
theorem ramseyNumber_le_pow[Fintype K] [DecidableEq K] (n : K → ℕ) (hr : 2 ≤ Fintype.card K) :
    ramseyNumber n ≤ (Fintype.card K) ^ ∑ k, n k := by
  by_cases h : ∀ k, 1 < n k
  · let sub_one (l : K) := Function.update n l (n l - 1)
    have sum_le_single : 1 ≤ ∑ k, n k := by
      trans ∑ k : K, 2
      · simp only [sum_const, card_univ, smul_eq_mul]; linarith [hr]
      · exact sum_le_sum (by simp only [mem_univ, forall_const]; exact h)
    have sub_one_sum (l : K) : ∑ k, sub_one l k = ∑ k, n k - 1 := by
      simp only [mem_univ, sum_update_of_mem, sdiff_singleton_eq_erase, add_comm, sub_one]
      rw [← Nat.add_sub_assoc (le_of_lt (h l)), Finset.sum_erase_add]
      exact mem_univ l
    apply le_trans (ramseyNumber_multicolour_bound h)
    trans ∑ l, (Fintype.card K) ^ ∑ k, sub_one l k
    · trans ∑ l, ramseyNumber (sub_one l)
      · simp [sub_one, hr]
      · gcongr; exact ramseyNumber_le_pow (sub_one _) hr
    · simp_rw [sub_one_sum, ← Nat.pow_sub_mul_pow (Fintype.card K) (sum_le_single)]
      simp [mul_comm]
  · push_neg at h
    apply le_trans (ramseyNumber_le_one h)
    exact Nat.one_le_pow (∑ k, n k) (Fintype.card K) (Nat.zero_lt_of_lt hr)
termination_by ∑ k, n k
decreasing_by
  rw [sub_one_sum]
  simp only [tsub_lt_self_iff, zero_lt_one, and_true, gt_iff_lt]
  exact sum_le_single


----------------------------------------------------------------------------------------------------
-- connection between monochromatic books and monochromatic cliques

-- this is kinda central, its how we get mono cliques from books in the first place
-- could generealize to fintypes
lemma monochromaticOf_of_monochromaticBook
    (χ : TopEdgeLabelling (Fin n) (Fin r)) (S : Fin r → Finset (Fin n))
    (TMbook : ∀ i, χ.MonochromaticBook i (S i) W) :
    ramseyNumber (λ (i : Fin r) ↦ k - #(S i)) ≤ #W →
    ∃ S, ∃ c, χ.MonochromaticOf (S.toSet) c ∧ k ≤ #S := by
  intros mle
  -- get the induced coloring on graph with #W vertices
  let χ' : TopEdgeLabelling (Fin #W) _ := χ.pullback (W.orderEmbOfFin rfl).1

  -- it has a c-monochromatic clique U of size ≥ k because W is larger than the ramsey number
  obtain ⟨U, ⟨c, rc⟩⟩ := ramseyNumber_spec (V := Fin #W) (K := Fin r) (by convert mle; simp) χ'

  -- embedding S back into the original graph yields a subset of W
  have : U.image (W.orderEmbOfFin rfl) ⊆ W := by
    intro x hx
    simp [Finset.mem_image] at hx
    obtain ⟨i, hi_mem, hi_eq⟩ := hx
    rw [← hi_eq]
    exact Finset.orderEmbOfFin_mem W rfl i

  use (S c) ∪ U.map (W.orderEmbOfFin rfl).1
  use c
  constructor
  simp only [coe_union, coe_map, RelEmbedding.coe_toEmbedding, ← coe_image]
  · apply χ.monochromaticOf_union.mpr
    simp only [coe_image]
    refine ⟨(TMbook c).2.1, ⟨rc.1.image, (TMbook c).2.2.subset_right ?_⟩⟩
    norm_cast
  · simp at rc
    apply le_trans rc.2
    rw [Finset.card_union_of_disjoint]
    simp only [add_comm, card_map]
    exact le_refl _
    convert Finset.disjoint_of_subset_right this (TMbook c).1
    ext; simp

-- special case for one smaller color
lemma blo (χ : TopEdgeLabelling (Fin n) (Fin r)) (c : Fin r)
    (TMbook : χ.MonochromaticBook c T M) (Tcard : #T = t) :
    ramseyNumber (λ (i : Fin r) ↦ if i = c then k - t else k) ≤ #M →
    ∃ S, ∃ c', χ.MonochromaticOf (S.toSet) c' ∧ k ≤ #S := by
  have := monochromaticOf_of_monochromaticBook (W := M) (k := k) χ (λ i ↦ if i = c then T else ∅) (λ i ↦ ?_)
  simp [apply_ite, Tcard] at this
  convert this
  simp
  by_cases h : i = c
  simp [h]; exact TMbook
  simp [h]; exact TopEdgeLabelling.monochromaticBook_empty


----------------------------------------------------------------------------------------------------
-- preliminary lemmata
theorem lemma52 (n r : ℕ) (ε : ℝ) (εge : 0 < ε) (χ : TopEdgeLabelling (Fin n) (Fin r)) :
    ∃ (W : Finset (Fin n)),
    ∃ (S : Fin r → (Finset (Fin n))),
    n * ((1 + ε) / (r : ℝ)) ^ (∑ i, #(S i)) ≤ #W ∧
    (∀ i w, ((1/ (r : ℝ)) - ε) * #W - 1 ≤ #((N χ i w) ∩ W)) ∧
    ∀ i, χ.MonochromaticBook i (S i) W := by
  sorry


theorem lemma53r {r k : ℕ} (kge : 2 ≤ k) (rge : 2 ≤ r) {ε : ℝ} (εin : ε ∈ Set.Ioo 0 1) (s : Fin r → ℕ)
    (sk : ∀ i, s i ≤ k) :
    let S := ∑ i, s i
    let b := (Real.exp (- (ε^2) * (k : ℝ) / 2) * r ^ (r * k) * ((1 + ε) / (r : ℝ)) ^ S)
    ε^2 * k ≤ S →
    ramseyNumber (λ i ↦ k - s i) ≤ b := by
  intro S b sbound

  have εge0 : 0 ≤ ε := le_of_lt (Set.mem_Ioo.mp εin).1

  have apparently : ramseyNumber (fun i ↦ k - (s i)) ≤ (r ^ (r * k - (S : ℝ)) : ℝ) := by
    have : (ramseyNumber fun i ↦ k - s i) ≤ r ^ (r * k - ∑ x, s x) := by
      convert ramseyNumber_le_pow (fun (i : Fin r) ↦ k - (s i)) (by simp [rge])
      exact (Fintype.card_fin r).symm
      simp [Finset.sum_tsub_distrib univ (f := λ _ ↦ k) (g := s) (λ i _ ↦ sk i)]
    rw [← Nat.cast_le (α := ℝ)] at this
    convert this
    simp [← Real.rpow_natCast]; congr
    rw [Nat.cast_sub, Nat.cast_mul]
    trans ∑ x : Fin r, k
    exact Finset.sum_le_sum (λ i _ ↦ sk i)
    simp

  have apparently2 : Real.exp (ε ^ 2 * (k : ℝ) / 2) ≤ (1 + ε) ^ (ε ^ 2 * k) := sorry

  trans r ^ (-S : ℝ) * r ^ ((r : ℝ) * (k : ℝ))
  · rw [← Real.rpow_add (by positivity), add_comm]
    ring_nf
    exact apparently
  · norm_cast; simp [b]
    rw [mul_right_comm]
    gcongr
    have (a b : ℝ) (c : ℕ) : (a / b) ^ c = a ^ c * b ^ (- c : ℤ) := by ring_nf; simp
    rw [this]
    trans 1 * ↑r ^ (- S : ℤ); simp
    rw [← mul_assoc]; gcongr
    trans Real.exp (-(ε ^ 2 * ↑k) / 2) * (1 + ε) ^ (ε ^ 2 * k)
    · trans (1 + ε) ^ (- (ε ^ 2 * ↑k)) * (1 + ε) ^ (ε ^ 2 * ↑k)
      · rw [← Real.rpow_add]
        apply Real.one_le_rpow; simp [εge0]; simp; positivity
      · rw [neg_div, Real.exp_neg, Real.rpow_neg]
        gcongr; positivity
    · gcongr
      rw [← Real.rpow_natCast _ S]
      apply Real.rpow_le_rpow_of_exponent_le _ sbound
      simp; exact le_of_lt (Set.mem_Ioo.mp εin).1



----------------------------------------------------------------------------------------------------
-- main result yay

theorem thm51r (r k : ℕ) (kp : 0 < k) (nr : 2 ≤ r) (kb : 2 ^ 160 * r ^ 16 ≤ k) :
    let δ := (2 ^ (- 160 : ℝ) : ℝ) * r ^ (- 12 : ℝ)
    let b := Real.exp (- δ * k) * r ^ (r * k)
    ramseyNumber (λ _ : Fin r ↦ k) ≤ b := by
  intro δ b
  let ε := (2 ^ (- 50 : ℝ) : ℝ) * r ^ (- 4 : ℝ)


  apply (Nat.le_floor_iff' (ne_of_gt (ramseyNumber_pos.mpr (λ _ ↦ ne_of_gt kp)))).mp
  apply ramseyNumber_le_iff_fin.mpr

  intro χ -- arbitrary r-coloring of K_(Fin ⌊b⌋)

  have rpos : 0 < r := by positivity
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp rpos
  have : Nonempty (Fin (Nat.floor b)) := sorry

  obtain ⟨W, ⟨S, ⟨Wb, pp⟩⟩⟩ := lemma52 _ r ε (by positivity) χ

  by_cases c : ε ^ 2 * k ≤ ∑ i, #(S i)
  · have : ramseyNumber (fun i ↦ k - #(S i)) ≤ #W := by
      rw [← Nat.cast_le (α := ℝ)]
      have εioo : ε ∈ Set.Ioo 0 1 := by
        simp; constructor; positivity;
        apply mul_lt_one_of_nonneg_of_lt_one_left
        positivity
        exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by simp)
        apply Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr rpos) (by simp)
      have kge2 : 2 ≤ k := by
        calc 2 ≤ 2 ^ 160 := by simp
          _ ≤ 2 ^ 160 * 1 := by simp
          _ ≤ 2 ^ 160 * r ^ 16 := by gcongr; rw [← one_pow 16]; exact Nat.pow_le_pow_left rpos _
          _ ≤ k := kb
      have (i : Fin r) : #(S i) ≤ k := by
        apply le_trans (card_finset_fin_le _) _
        sorry -- yamaan gave proof


      apply le_trans (lemma53r kge2 nr εioo (λ i ↦ #(S i)) this c) (le_trans _ Wb)
      gcongr; unfold b; unfold δ; unfold ε
      have := Nat.lt_floor_add_one (Real.exp (-(2 ^ (-160:ℝ) * ↑r ^ (-12:ℝ)) * ↑k) * ↑r ^ (r * k))
      rw [← sub_lt_iff_lt_add] at this
      apply le_trans _ (le_of_lt this)
      sorry
      -- gcongr
      -- rw [← Real.rpow_natCast, Real.mul_rpow (by positivity), ← Real.rpow_mul (by positivity),
      --   ← Real.rpow_mul (by positivity),
      --   show ∀ (k : ℝ), k / 2 = (1 / 2) * k by ring_nf; exact λ _ ↦ trivial, ← mul_assoc]
      -- gcongr; ring_nf; simp_rw [neg_div, mul_neg]
      -- apply neg_le_neg
      -- gcongr
      -- exact Nat.one_le_cast.mpr rpos
      -- linarith
      -- linarith
      -- positivity


    exact monochromaticOf_of_monochromaticBook χ S pp.2 this
  · -- ceil really?
    let t := Nat.ceil ((2 : ℝ) ^ (- 40 : ℤ) * r ^ (-3 : ℤ) * k)
    have tltk : t < k := sorry
    let p := 1 / r - 2 * ε
    let μ := 2^30 * r^3

    have μger : (2 : ℝ) ^ 10 * r ^ 3 ≤ μ := by simp [μ]; gcongr; linarith

    -- pick any color (we pick color 1) and make it smaller
    let odk (i : Fin r) := if i = ⟨1, nr⟩ then k - t else k
    let m := ramseyNumber odk
    have (c : Fin r) : odk c ≠ 0 := by
      simp [odk]; split
      exact Nat.sub_ne_zero_iff_lt.mpr tltk
      exact Nat.ne_zero_of_lt kp
    have mpos : 0 < m := ramseyNumber_pos.mpr this

    -- apply theorem 2.1 to the coloring restricted to W
    let χ' := χ.pullback (W.orderEmbOfFin rfl).1
    have : Nonempty (Fin #W) := sorry
    obtain ⟨c, ⟨T, ⟨M, ⟨Tcard, ⟨Mcard, TMbook⟩⟩⟩⟩⟩ :=
      book t m χ' sorry mpos univ (λ _ ↦ univ) p sorry μ μger sorry sorry sorry sorry

    -- re-embed
    let TTbook := TopEdgeLabelling.monochromaticBook_pullback (W.orderEmbOfFin rfl).1 c T M TMbook
    rw [← Finset.card_map] at Tcard Mcard
    simp [m] at Mcard
    have := ramseyNumber_equiv (n := odk) (Equiv.swap c ⟨1, nr⟩)
    simp_rw [← this] at Mcard
    simp [odk] at Mcard
    simp_rw [swap_ite_eq c ⟨1, nr⟩ (k - t) k] at Mcard

    -- get monochromatic clique from book
    obtain ⟨S, ⟨c', _⟩⟩ := blo (k := k) (t := t) χ c TTbook Tcard Mcard

    use S; use c'
