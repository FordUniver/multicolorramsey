import MulticolorRamsey.GeometricLemma
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open SimpleGraph Finset

variable {V W : Type} [LinearOrder W] {G : SimpleGraph V} {r : ℕ}

----------------------------------------------------------------------------------------------------
-- N

-- "Given an edge colouring, we write $N_i(u)$ to denote the neighbourhood of vertex $u$ in colour $i$."
abbrev N {C} [DecidableRel G.Adj] [DecidableEq C] [Fintype V] (χ : G.EdgeLabelling C) (i : C) x :=
  (χ.coloredNeighborSet i x).toFinset

-- lemma N_not_mem  [DecidableRel G.Adj] [DecidableEq C] [Fintype V] (χ : G.EdgeLabelling C) (i : C) x :
--     x ∉ N χ i x := by
--   simp [N, EdgeLabelling.coloredNeighborSet]

----------------------------------------------------------------------------------------------------
-- p
-- TODO maybe mathlib wants some of this.


def mymin (f : V → W) (X : Finset V) [nen: Nonempty X] : W :=
  (image f X).min' (image_nonempty.mpr (nonempty_coe_sort.mp nen))

lemma min_const {f : V → W} {X : Finset V} (cn : ∀ x ∈ X, f x = c) [nen: Nonempty X] :
    c = mymin f X := by
  obtain ⟨xg, ⟨xgm, xgn⟩⟩ := mem_image.mp (min'_mem (image f X) _)
  rw [cn xg xgm] at xgn
  assumption

lemma min_le_ℕ {f : V → ℝ} {g : V → ℕ} {X : Finset V} [nen: Nonempty X] (le : ∀ x ∈ X, f x ≤ g x) :
    mymin f X ≤ mymin g X := by
  obtain ⟨xg, ⟨xgm, xgn⟩⟩ := mem_image.mp (min'_mem (image g X) _)
  convert le_trans (min'_le _ (f xg) (mem_image_of_mem f xgm)) (le xg xgm)
  exact xgn.symm

-- lemma min_le_mem_ℕ {f : V → ℕ} {X : Finset V} {v : X} [Nonempty X] : mymin f X ≤ f v :=
--   min'_le _ _ (mem_image_of_mem f (coe_mem v))

lemma min_le_mem {f : V → W} {X : Finset V} [Nonempty X] (v : X) : mymin f X ≤ f v :=
  min'_le _ _ (mem_image_of_mem f (coe_mem v))

-- lemma min_ge {f : V → W} {X : Finset V} [Nonempty X] (v : X) (c : W) (le : ∀ v, c ≤ f v) :
--     c ≤ mymin f X :=
-- sorry

-- -- this is pᵢ|Yᵢ| in the text
-- def p'Y {V : Type} [Fintype V] [DecidableEq V] (X Y : Finset V) [nenX: Nonempty X] (χ : TopEdgeLabelling V (Fin r))
--     (i : Fin r) : ℕ :=
--   mymin (fun x => ((N χ i x) ∩ Y).card) X

-- -- this is pᵢ in the text
-- noncomputable def p {V : Type} [Fintype V] [DecidableEq V] (X Y : Finset V) [nenX : Nonempty X] (EC : TopEdgeLabelling V (Fin r))
--     (i : Fin r) : ℝ := (p'Y X Y EC i) / (Y.card : ℝ)

-- lemma p_subset {V : Type} [Fintype V] [DecidableEq V] {χ : TopEdgeLabelling V (Fin r)} {X X' Y : Finset V} [nenX : Nonempty X] [Nonempty X'] : X' ⊆ X → (p X Y χ i) ≤ (p X' Y χ i) := sorry

-- lemma p_nonneg {V : Type} [Fintype V] [DecidableEq V] (χ : TopEdgeLabelling V (Fin r)) (X Y : Finset V) [nenX : Nonempty X] :
--     0 ≤ (p X Y χ i) := by unfold p; positivity

-- lemma pY_pos {V : Type} [Fintype V] [DecidableEq V] (χ : TopEdgeLabelling V (Fin r)) (X Y : Finset V) [nenX : Nonempty X] (nen : ∀ x, (N χ i x) ∩ Y ≠ ∅):
--     0 < (p'Y X Y χ i) := by
--   unfold p'Y mymin; refine (lt_min'_iff (image (fun x ↦ (N χ i x ∩ Y).card) X) _).mpr ?_
--   intros c cc
--   have : ∀ x, 0 < (N χ i x ∩ Y).card := by intro xx; simp only [card_pos]; exact nonempty_iff_ne_empty.mpr (nen xx)
--   obtain ⟨z, ⟨zl, zc⟩⟩ := mem_image.mp cc
--   rw [← zc]
--   exact this z

-- lemma p_pos {V : Type} [Fintype V] [DecidableEq V] (χ : TopEdgeLabelling V (Fin r)) (X Y : Finset V) [nenX : Nonempty X] (_ : ∀ x, (N χ i x) ∩ Y ≠ ∅):
--     0 < (p X Y χ i) := by unfold p; sorry

-- lemma p_le_one {V : Type} [Fintype V] [DecidableEq V] (χ : TopEdgeLabelling V (Fin r)) (X Y : Finset V) [nenX : Nonempty X] :
--     (p X Y χ i) ≤ 1 := by
--   sorry


----------------------------------------------------------------------------------------------------
-- lifting finset elements

def lift {X : Finset V} (X' : Finset { x // x ∈ X }) : Finset V := map (Function.Embedding.subtype fun x => x ∈ X) X'

instance lift.Nonempty {X : Finset V} (X' : Finset { x // x ∈ X }) [nen : Nonempty X'] : Nonempty (lift X') := by
 obtain ⟨x', x'X'⟩ := nen
 refine ⟨(Function.Embedding.subtype fun x => x ∈ X) x', ?_⟩
 simp [lift, x'X']

lemma lift_nonempty {X : Finset V} (X' : Finset { x // x ∈ X }) (nen : X'.Nonempty) :  (lift X').Nonempty := by
  sorry

lemma lift_subset {X : Finset V} (X' : Finset { x // x ∈ X }) : (lift X') ⊆ X := by
  simp [lift]
  intro _ xl
  simp at xl
  exact xl.1

lemma lift_card {X : Finset V} (X' : Finset { x // x ∈ X }) : X'.card = (lift X').card := by
  simp [lift]

lemma tr {X : Finset V} {X' : Finset { x // x ∈ X }} {p : V → Prop} (e : ∀ a ∈ X', p a) :
    ∀ x ∈ lift X', p x  := by
  intro x xlX
  simp [lift] at xlX
  obtain ⟨xi, h⟩ := xlX
  exact e ⟨x, xi⟩ h

----------------------------------------------------------------------------------------------------
-- key lemma

open MeasureTheory ProbabilityTheory Finset Real SimpleGraph

open scoped ENNReal

variable [DecidableEq V] [Fintype V] {χ : TopEdgeLabelling V (Fin r)}

def ppY (χ : TopEdgeLabelling V (Fin r)) (X : Finset V) (Y : Fin r → Finset V) (i : Fin r) : ℕ :=
  if h : X.Nonempty
  then
    min' (image (fun x => ((N χ i x) ∩ (Y i)).card) X)
         (image_nonempty.mpr h)
  else 0

noncomputable def p'p (χ : TopEdgeLabelling V (Fin r)) (X : Finset V) (Y : Fin r → Finset V) (i : Fin r) : ℝ :=
    (ppY χ X Y i) / ((Y i).card : ℝ)

structure Saga (χ : TopEdgeLabelling V (Fin r)) where
  X : Finset V
  Y : Fin r → Finset V

abbrev Saga.pY (ki : Saga χ) (i : Fin r) : ℕ := ppY χ ki.X ki.Y i

noncomputable abbrev Saga.p (ki : Saga χ) (i : Fin r) : ℝ := p'p χ ki.X ki.Y i

lemma pk_le_one (ki : Saga χ) (i : Fin r) :
    (ki.p i) ≤ 1 := by
  sorry

lemma p_monoX (χ : TopEdgeLabelling V (Fin r)) {X X' : Finset V}
    (xsub : X' ⊆ X) (h : X'.Nonempty) (Y : Fin r → Finset V) (i : Fin r) :
    p'p χ X Y i ≤ p'p χ X' Y i := by
  simp [p'p, ppY]
  gcongr
  simp [h, h.mono xsub]
  intro a ax
  trans (image (fun x ↦ #(N χ i x ∩ Y i)) X').min' (image_nonempty.mpr h)
  exact min'_subset _ (image_subset_image xsub)
  apply min'_le
  simp only [mem_image]
  use a, ax


lemma p_monoY (χ : TopEdgeLabelling V (Fin r)) {X : Finset V} (Y Y' : Fin r → Finset V) (h : ∀ i, Y' i ⊆ Y i) (i : Fin r) :
    p'p χ X Y i ≤ p'p χ X Y' i := by
  simp [p'p, ppY]
  gcongr
  by_cases h : X.Nonempty
  sorry
  -- · simp [h, h.mono xsub]
  --   intro a ax
  --   trans (image (fun x ↦ #(N χ i x ∩ Y i)) X').min' (image_nonempty.mpr h)
  --   exact min'_subset _ (image_subset_image xsub)
  --   apply min'_le
  --   simp only [mem_image]
  --   use a, ax
  · simp [h]
    sorry
  sorry
  sorry

lemma pk_le_mem {ki : Saga χ} (i : Fin r) (xin : x ∈ ki.X) :
    (ki.pY i) ≤ #(N χ i x ∩ ki.Y i) := by
  simp [Saga.pY, ppY]
  split
  apply min'_le
  simp; use x
  simp


lemma nonempty_of_ppos {ki : Saga χ} (ppos : ∀ i, 0 < ki.pY i) : Nonempty ki.X := sorry


lemma keyk [Nonempty (Fin r)] -- {cardV : Fintype.card V = n}
  (χ : TopEdgeLabelling V (Fin r))
  (ki : Saga χ)
  (ppos : ∀ (i : Fin r), 0 < ki.pY i)
  (α : Fin r → ℝ) (αpos : ∀ i, 0 < α i) :

  let β := (3 ^ (-(4 : ℝ) * r) : ℝ)
  let C := 4 * (↑r : ℝ) * √r

  ∃ l : Fin r, ∃ Λ, (-1 ≤ Λ) ∧
  ∃ x ∈ ki.X, ∃ ki' : Saga χ, -- TODO paper says strict subset but idk if that's true
    (ki'.X.Nonempty) ∧
    (ki'.X ⊆ ki.X) ∧
    (∀ i, ↑(ki'.Y i) ⊆ (N χ i x) ∩ (ki.Y i)) ∧ -- same

    β * Real.exp (-C * Real.sqrt (Λ + 1)) * ki.X.card ≤ ki'.X.card ∧
    (∀ i, (ki'.Y i).card = (ki.p i) * (ki.Y i).card) ∧

    ki.p l + Λ * (α l) ≤ ki'.p l ∧

    ∀ i ≠ l, ki.p i - (α i) ≤ ki'.p i := by
  intros β C

  let p' (i : Fin r) (x : ki.X) : (ki.pY i) ≤ #(N χ i x ∩ ki.Y i) := pk_le_mem _ (coe_mem x)

  -- "for each 𝑥 ∈ 𝑋, choose a set N′i (x) ⊂ 𝑁i(x) ∩ Yi of size exactly 𝑝𝑖(𝑋, 𝑌𝑖)|Yi|"
  let N' (i : Fin r) (x : ki.X) : (Finset V) := Classical.choose (exists_subset_card_eq (p' i x))

  have N'sub {x : ki.X} (i : Fin r) : (N' i x) ⊆ N χ i x ∩ ki.Y i := by
    simp [N', Classical.choose_spec (exists_subset_card_eq (p' i x))]

  have N'subN {i : Fin r} {x : ki.X} : (N' i x) ⊆ N χ i x :=
  (subset_inter_iff.mp (N'sub i)).1

  have N'card {i : Fin r} {x : ki.X} : #(N' i x) = (ki.pY i) := by
    simp [N', Classical.choose_spec (exists_subset_card_eq (p' i x))]

  -- "... and set ..."
  let σ (i : Fin r) (x : ki.X) : (V → ℝ) :=
    (↑1 / Real.sqrt ((α i) * (ki.pY i))) •
      ((Set.indicator ↑(N' i x) (fun _ ↦ 1)) - (ki.p i) • (Set.indicator ↑(ki.Y i) (fun _ ↦ 1)))

  -- "... Note that, for any x,y ∈ X,..."
  -- TODO issue #14
  have Λiff (Λ : ℝ) (i : Fin r) {x y : ki.X} (lam_ge : Λ ≤ ((σ i x) ⬝ᵥ (σ i y))) : -- we only need mp direction, paper says iff
      ((ki.p i) + Λ * (α i)) * ((ki.pY i) : ℝ) ≤ ((N' i x) ∩ (N' i y)).card := sorry


  -- "Now by Lemma 7, there exists Λ ≥ -1 and colour l ∈ [r] such that..."
  let Fintype.instMeasurableSpace : MeasurableSpace ki.X := ⊤ -- we use the power set Σ-algebra so that the measure theory stuff stays sane
  have :  Nonempty { x // x ∈ ki.X } := nonempty_of_ppos ppos
  let U := (PMF.uniformOfFintype (ki.X × ki.X)).toMeasure
  obtain ⟨Λ, ⟨Λgen1, ⟨l, probge⟩⟩⟩ := geometric (ℙᵤ := U) σ
  exists l
  exists Λ; simp only [Λgen1, true_and]

  -- "Hence there exists a vertex x ∈ X and a set X' ⊂ X such that, ..."
  obtain ⟨x, ⟨X', ⟨X'card, X'props⟩⟩⟩ :=
    pidgeon_thing
      (fun (x : ki.X × ki.X) ↦ Λ ≤ σ l x.1 ⬝ᵥ σ l x.2 ∧ ∀ i, i ≠ l → -1 ≤ σ i x.1 ⬝ᵥ σ i x.2)
      probge

  exists x; simp only [coe_mem, neg_mul, true_and]

  -- "Setting $Y'_i = N'_i(x)$ for each $i \in [r]$,..."
  let Y' (i : Fin r) : Finset V := N' i x

  have Y'card {i : Fin r} : #(Y' i) = (ki.p i) * #(ki.Y i) := by
    simp_rw [Y', N'card, Saga.p]
    by_cases h : (ki.Y i).card = 0
    · simp [card_eq_zero.mp h, ppY]
      exact fun _ => (min_const (fun _ _ ↦ rfl)).symm
    · have : Invertible (#(ki.Y i) : ℝ) := invertibleOfNonzero (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_of_ne_zero h)))
      exact (div_mul_cancel_of_invertible _ _).symm

  let ki' : Saga χ := ⟨lift X', fun i => Y' i⟩
  exists ki'

  have nen' : X'.Nonempty := by
    -- apply Finset.Nonempty.ne_empty
    apply Finset.card_pos.mp
    -- rw [← lift_card]
    have : 0 < 3 ^ (-(4 : ℝ) * r) * rexp (-(4 * r * √r) * √(Λ + 1)) * (Fintype.card ki.X) :=
      by positivity
    convert lt_of_lt_of_le this X'card
    exact Iff.symm Nat.cast_pos'
  have : Nonempty { x // x ∈ X' } := nen'.to_subtype

  -- "...it follows that..."
  have Y'lee :
      ki.p l + Λ * (α l) ≤ ki'.p l ∧
      ∀ (i : Fin r), (i ≠ l) → ki.p i - (α i) ≤ ki'.p i := by

    let factor (i : Fin r) : ℝ := if i = l then Λ else -1

    let f (i : Fin r) (x' : V) : ℝ := (ki.p i + (factor i) * α i) * (ki.pY i)
    let g (i : Fin r) (x' : V) : ℕ := #(N χ i x' ∩ N' i x)

    have ext (i : Fin r) : (∀ a ∈ X', f i a ≤ g i a) := by
      intro x' xX'
      have : ∀ i, factor i ≤ σ i x' ⬝ᵥ σ i x := by
        intro i
        let xp := X'props x' xX'
        by_cases h : i = l
        all_goals simp only [h, ↓reduceIte, dotProduct_comm, factor]
        · exact xp.1
        · exact (xp.2 i h)

      have le : #(N' i ↑x' ∩ N' i ↑x) ≤ #(N χ i ↑x' ∩ N' i ↑x) := card_le_card (inter_subset_inter_right N'subN)
      have := le_trans ((Λiff (factor i) i) (this i)) (Nat.cast_le.mpr le)
      assumption


    have mins (i : Fin r) : f i ↑x ≤ ↑(mymin (g i) (lift X')) := calc f i x
     _ = (mymin (f i) (lift X'))        := min_const (fun _ _ ↦ rfl)
     _ ≤ (mymin (g i) (lift X'))        := min_le_ℕ (tr (ext i))

    have pos (i : Fin r) : (0 : ℝ) < ↑(#(N' i x)) := by simp only [N'card, Nat.cast_pos]; exact ppos i

    have hm (i : Fin r) :=
      calc ki.p i + (factor i) * α i
     _ = (f i) x / (ki.pY i) := (mul_div_cancel_right₀ _ <| by rw [← @N'card i x]; exact ne_of_gt (pos i)).symm
     _ = (f i) x / #(N' i x)  := by simp [N'card]
     _ ≤ (mymin (g i) (lift X')) / #(N' i x) := (div_le_div_iff_of_pos_right <| pos i).mpr (mins i)

    constructor
    · convert (hm l)
      exact Eq.symm (if_pos rfl)
      simp [mymin, Saga.p, p'p, ppY, ki', lift_nonempty, nen']
      gcongr
    · intros i inl
      have := hm i
      simp only [inl, ↓reduceIte, neg_mul, one_mul, factor] at this
      apply le_trans this
      simp [mymin, Saga.p, p'p, ppY, ki', lift_nonempty, nen']
      gcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ki']; exact lift_nonempty _ nen'
  · exact lift_subset X'
  · simp only [ki', N'sub, implies_true, Y']
  · simp only [neg_mul, Fintype.card_coe] at X'card
    simp only [ki', neg_mul, ← lift_card, X'card, β, C]
  · simp only [ki', Y'card, implies_true]
  · exact Y'lee.1
  · exact fun i inl ↦ Y'lee.2 i inl
