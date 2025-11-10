import MulticolorRamsey.GeometricLemma
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

----------------------------------------------------------------------------------------------------
-- N

-- "Given an edge colouring, we write $N_i(u)$ to denote the neighbourhood of vertex $u$ in colour $i$."
abbrev N {C} {V} {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableEq C] [Fintype V] (χ : G.EdgeColoring C) (i : C) x :=
  χ.coloredNeighborFinset i x

----------------------------------------------------------------------------------------------------
-- p
-- TODO maybe mathlib wants some of this.

def mymin {V W : Type} [LinearOrder W] (f : V → W) (X : Finset V) [nen: Nonempty X] : W :=
  Finset.min' (Finset.image f X) (Finset.image_nonempty.mpr (Finset.nonempty_coe_sort.mp nen))

lemma min_const {f : V → ℝ} {X : Finset V} (cn : ∀ x ∈ X, f x = c) [nen: Nonempty X] :
    c = mymin f X := by
  obtain ⟨xg, ⟨xgm, xgn⟩⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.image f X) _)
  rw [cn xg xgm] at xgn
  assumption

lemma min_le_ℕ {f : V → ℝ} {g : V → ℕ} {X : Finset V} [nen: Nonempty X] (le : ∀ x ∈ X, f x ≤ g x) :
    mymin f X ≤ mymin g X := by
  obtain ⟨xg, ⟨xgm, xgn⟩⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.image g X) _)
  convert le_trans (Finset.min'_le _ (f xg) (Finset.mem_image_of_mem f xgm)) (le xg xgm)
  exact xgn.symm

lemma min_le_mem_ℕ {f : V → ℕ} {X : Finset V} {v : X} [Nonempty X] : mymin f X ≤ f v :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem f (Finset.coe_mem v))


-- this is pᵢ|Yᵢ| in the text
def pY {V : Type} [Fintype V] [DecidableEq V] (X Y : Finset V) [nen: Nonempty X] (χ : (⊤ : SimpleGraph V).EdgeColoring (Fin r))
    (i : Fin r) : ℕ :=
  mymin (fun x => ((N χ i x) ∩ Y).card) X

-- this is pᵢ in the text
noncomputable def p {V : Type} [Fintype V] [DecidableEq V] (X Y : Finset V) [Nonempty X] (EC : (⊤ : SimpleGraph V).EdgeColoring (Fin r))
    (i : Fin r) : ℝ := (pY X Y EC i) / (Y.card : ℝ)


----------------------------------------------------------------------------------------------------
-- lifting finset elements

def lift {X : Finset V} (X' : Finset { x // x ∈ X }) : Finset V := Finset.map (Function.Embedding.subtype fun x => x ∈ X) X'

instance lift.Nonempty {X : Finset V} (X' : Finset { x // x ∈ X }) [nen : Nonempty X'] : Nonempty (lift X') := by
 obtain ⟨x', x'X'⟩ := nen
 refine ⟨(Function.Embedding.subtype fun x => x ∈ X) x', ?_⟩
 simp [lift, x'X']

lemma tr {X : Finset V} {X' : Finset { x // x ∈ X }} {p : V → Prop} (e : ∀ a ∈ X', p a) :
    ∀ x ∈ lift X', p x  := by
  intro x xlX
  simp [lift] at xlX
  obtain ⟨xi, h⟩ := xlX
  exact e ⟨x, xi⟩ h

----------------------------------------------------------------------------------------------------
-- Helper lemmas for dotProduct bilinearity (missing from Mathlib)
-- TODO: These should be upstreamed to Mathlib (see README for PR tracking)

section DotProductBilinearity

variable {V : Type*} [Fintype V] {R : Type*} [CommRing R]

lemma dotProduct_sub_left (a b c : V → R) :
    dotProduct (a - b) c = dotProduct a c - dotProduct b c := by
  simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma dotProduct_sub_right (a b c : V → R) :
    dotProduct a (b - c) = dotProduct a b - dotProduct a c := by
  simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma dotProduct_smul_left (r : R) (a b : V → R) :
    dotProduct (r • a) b = r * dotProduct a b := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma dotProduct_smul_right (r : R) (a b : V → R) :
    dotProduct a (r • b) = r * dotProduct a b := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  conv_lhs => arg 2; ext; rw [mul_comm, mul_assoc, mul_comm (b _)]
  rw [Finset.mul_sum]

end DotProductBilinearity

----------------------------------------------------------------------------------------------------
-- Helper lemmas for indicator dot products

section IndicatorHelpers

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Dot product of two indicator functions equals intersection size
lemma indicator_dotProduct_indicator (s t : Finset V) :
    dotProduct (Set.indicator (↑s : Set V) (1 : V → ℝ)) (Set.indicator (↑t : Set V) 1)
      = (s ∩ t).card := by
  simp only [dotProduct, Set.indicator, Pi.one_apply]
  have h : ∀ v : V, (if v ∈ (↑s : Set V) then (1 : ℝ) else 0) * (if v ∈ (↑t : Set V) then 1 else 0)
                    = if v ∈ s ∩ t then 1 else 0 := by
    intro v
    by_cases hs : v ∈ s <;> by_cases ht : v ∈ t <;> simp [hs, ht, Finset.mem_inter]
  simp_rw [h]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.sum_const_zero, add_zero]
  rw [Finset.inter_comm, Finset.inter_univ]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]

-- Dot product of indicator with itself
lemma indicator_dotProduct_self (s : Finset V) :
    dotProduct (Set.indicator (↑s : Set V) (1 : V → ℝ)) (Set.indicator (↑s : Set V) 1)
      = s.card := by
  rw [indicator_dotProduct_indicator, Finset.inter_self]

-- When s ⊆ t, dot product of indicators
lemma indicator_dotProduct_subset (s t : Finset V) (h : s ⊆ t) :
    dotProduct (Set.indicator (↑s : Set V) (1 : V → ℝ)) (Set.indicator (↑t : Set V) 1)
      = s.card := by
  rw [indicator_dotProduct_indicator]
  rw [Finset.inter_eq_left.mpr h]

end IndicatorHelpers

----------------------------------------------------------------------------------------------------
-- key lemma

open MeasureTheory ProbabilityTheory Finset Real

open scoped ENNReal

lemma key {n : ℕ} [Nonempty (Fin r)] (V : Type) [DecidableEq V] [Nonempty V] [Fintype V] {cardV : Fintype.card V = n}
  (χ : (⊤ : SimpleGraph V).EdgeColoring (Fin r))
  (X : Finset V) [nenX : Nonempty X]-- TODO strict subset!
  (Y : Fin r → (Finset V)) (Ypos : ∀ i, 0 < #(Y i)) -- TODO here too
  (α : Fin r → ℝ) (αpos : ∀ i, 0 < α i)
  (ppos : ∀ i, 0 < pY X (Y i) χ i) :


  let β := (3 ^ (-(4 : ℝ) * r) : ℝ)
  let C := 4 * (↑r : ℝ) * √r

  ∃ l : Fin r, ∃ Λ, (-1 ≤ Λ) ∧
  ∃ x ∈ X, ∃ X' : Finset X, ∃ nx : Nonempty X', ∃ Y' : Fin r → (Finset V), -- TODO paper says strict subset but idk if that's true
    (∀ i, ↑(Y' i) ⊆ (N χ i x) ∩ (Y i)) ∧ -- same

    β * Real.exp (-C * Real.sqrt (Λ + 1)) * ↑X.card ≤ ↑X'.card ∧
    (∀ i ≠ l, ((Y' i).card = (p X (Y i) χ i) * (Y i).card)) ∧

    p X (Y l) χ l + Λ * (α l) ≤ p (lift X') (Y' l) χ l ∧

    ∀ i ≠ l, p X (Y i) χ i - (α i) ≤ p (lift X') (Y' i) χ i := by

  intros β C

  let p' (i : Fin r) (x : X) : (pY X (Y i) χ i) ≤ #(N χ i x ∩ Y i) := min_le_mem_ℕ

  -- "for each 𝑥 ∈ 𝑋, choose a set N′i (x) ⊂ 𝑁i(x) ∩ Yi of size exactly 𝑝𝑖(𝑋, 𝑌𝑖)|Yi|"
  let N' (i : Fin r) (x : X) : (Finset V) := Classical.choose (Finset.exists_subset_card_eq (p' i x))

  have N'sub {x : X} (i : Fin r) : (N' i x) ⊆ N χ i x ∩ Y i := by
    simp [N', Classical.choose_spec (Finset.exists_subset_card_eq (p' i x))]

  have N'subN {i : Fin r} {x : X} : (N' i x) ⊆ N χ i x :=
  (Finset.subset_inter_iff.mp (N'sub i)).1

  have N'card {i : Fin r} {x : X} : #(N' i x) = (pY X (Y i) χ i) := by
    simp [N', Classical.choose_spec (Finset.exists_subset_card_eq (p' i x))]

  -- "... and set ..."
  let σ (i : Fin r) (x : X) : (V → ℝ) :=
    (↑1 / Real.sqrt ((α i) * (pY X (Y i) χ i))) •
      ((Set.indicator ↑(N' i x) (fun _ ↦ 1)) - (p X (Y i) χ i) • (Set.indicator ↑(Y i) (fun _ ↦ 1)))

  -- "... Note that, for any x,y ∈ X,..."
  -- TODO issue #14
  have Λiff (Λ : ℝ) (i : Fin r) {x y : X} (lam_ge : Λ ≤ ((σ i x) ⬝ᵥ (σ i y))) : -- we only need mp direction, paper says iff
      ((p X (Y i) χ i) + Λ * (α i)) * ((pY X (Y i) χ i) : ℝ) ≤ ((N' i x) ∩ (N' i y)).card := by
    -- Abbreviations for readability
    let α' := α i
    let p' := p X (Y i) χ i
    let pY' := pY X (Y i) χ i
    let Y' := Y i
    let Nx := N' i x
    let Ny := N' i y

    -- Key facts about N'
    have Nx_card : (Nx.card : ℝ) = pY' := by
      show ((N' i x).card : ℝ) = (pY X (Y i) χ i : ℝ)
      exact congrArg Nat.cast N'card
    have Ny_card : (Ny.card : ℝ) = pY' := by
      show ((N' i y).card : ℝ) = (pY X (Y i) χ i : ℝ)
      exact congrArg Nat.cast N'card
    have Nx_sub : Nx ⊆ Y' := (Finset.subset_inter_iff.mp (N'sub i)).2
    have Ny_sub : Ny ⊆ Y' := (Finset.subset_inter_iff.mp (N'sub i)).2
    have p'_eq : p' = pY' / (Y'.card : ℝ) := rfl
    have pY'_pos : (0 : ℝ) < pY' := Nat.cast_pos.mpr (ppos i)
    have α'_pos : (0 : ℝ) < α' := αpos i
    have Y'_pos : (0 : ℝ) < Y'.card := Nat.cast_pos.mpr (Ypos i)

    -- Following the blueprint calculation (lines 36-56)
    -- We need to show: (p + Λα)·pY ≤ |Nx ∩ Ny|

    -- Step 1: From Λ ≤ ⟨σ(x), σ(y)⟩, multiply by α·pY > 0
    have key_ineq : Λ * α' * pY' ≤ α' * pY' * (σ i x ⬝ᵥ σ i y) := by
      have h : (0 : ℝ) < α' * pY' := mul_pos α'_pos pY'_pos
      calc Λ * α' * pY'
          _ = Λ * (α' * pY') := by ring
          _ ≤ (σ i x ⬝ᵥ σ i y) * (α' * pY') := (mul_le_mul_right h).mpr lam_ge
          _ = α' * pY' * (σ i x ⬝ᵥ σ i y) := by ring

    -- Step 2: Expand the inner product using indicator functions
    -- σ(x) = (1/√(α·pY)) • (indNx - p·indY)
    let indNx := Set.indicator (↑Nx : Set V) (1 : V → ℝ)
    let indNy := Set.indicator (↑Ny : Set V) (1 : V → ℝ)
    let indY := Set.indicator (↑Y' : Set V) (1 : V → ℝ)

    -- The RHS equals: ⟨indNx - p·indY, indNy - p·indY⟩
    -- Key: σ(x) = (1/√(α·pY)) • (indNx - p·indY), so ⟨σ(x),σ(y)⟩ = (1/√(α·pY))^2 · ⟨...,  ...⟩
    -- Then α·pY · ⟨σ(x),σ(y)⟩ = α·pY · (1/(α·pY)) · ⟨..., ...⟩ = ⟨..., ...⟩
    have inner_expanded : α' * pY' * (σ i x ⬝ᵥ σ i y) =
        dotProduct (indNx - p' • indY) (indNy - p' • indY) := by
      -- TODO: After unfolding σ and bilinearity, need to show (α·pY)*(1/√(α·pY))² = 1
      -- Blocker: Pattern matching issues with mixed scalar/vector multiplication
      -- The cancellation lemma works, but combining s*s into s^2 when mixed with
      -- the inner product requires careful tactic work beyond current approach
      sorry

    -- Step 3: Expand the dot product using bilinearity
    have dot_expanded : dotProduct (indNx - p' • indY) (indNy - p' • indY) =
        ((Nx ∩ Ny).card : ℝ) - p' * p' * (Y'.card : ℝ) := by
      rw [dotProduct_sub_right, dotProduct_sub_left, dotProduct_sub_left]
      rw [dotProduct_smul_right, dotProduct_smul_right, dotProduct_smul_left, dotProduct_smul_left]
      simp only [indNx, indNy, indY]
      rw [indicator_dotProduct_indicator Nx Ny]
      rw [indicator_dotProduct_subset Nx Y' Nx_sub]
      rw [dotProduct_comm, indicator_dotProduct_subset Ny Y' Ny_sub]
      rw [indicator_dotProduct_self Y']
      rw [Nx_card, Ny_card]
      -- Goal: ↑(#(Nx ∩ Ny)) - p' * ↑pY' * 2 + p'^2 * ↑(#Y') = ↑(#(Nx ∩ Ny)) - p'^2 * ↑(#Y')
      -- Need: p' * pY' * 2 = p'^2 * |Y'| * 2, i.e., p' * pY' = p'^2 * |Y'|
      -- Since p' = pY'/|Y'|, we have: (pY'/|Y'|) * pY' = (pY'/|Y'|)^2 * |Y'|
      have h : p' * (pY' : ℝ) = p' ^ 2 * (Y'.card : ℝ) := by
        rw [p'_eq, sq]
        rw [mul_assoc]
        rw [div_mul_cancel₀ _ (ne_of_gt Y'_pos)]
      linarith

    -- Step 4: Combine all inequalities to reach the final goal
    show (p' + Λ * α') * pY' ≤ ((Nx ∩ Ny).card : ℝ)
    calc (p' + Λ * α') * pY'
        _ = p' * pY' + Λ * α' * pY' := by ring
        _ ≤ p' * pY' + α' * pY' * (σ i x ⬝ᵥ σ i y) := by linarith [key_ineq]
        _ = p' * pY' + dotProduct (indNx - p' • indY) (indNy - p' • indY) := by rw [inner_expanded]
        _ = p' * pY' + (((Nx ∩ Ny).card : ℝ) - p' * p' * (Y'.card : ℝ)) := by rw [dot_expanded]
        _ = p' * pY' + ((Nx ∩ Ny).card : ℝ) - p' * p' * (Y'.card : ℝ) := by ring
        _ = p' ^ 2 * (Y'.card : ℝ) + ((Nx ∩ Ny).card : ℝ) - p' * p' * (Y'.card : ℝ) := by
            have h : p' * (pY' : ℝ) = p' ^ 2 * (Y'.card : ℝ) := by
              rw [p'_eq, sq, mul_assoc, div_mul_cancel₀ _ (ne_of_gt Y'_pos)]
            rw [h]
        _ = ((Nx ∩ Ny).card : ℝ) := by ring
        _ ≤ ((Nx ∩ Ny).card : ℝ) := by linarith


  -- "Now by Lemma 7, there exists Λ ≥ -1 and colour l ∈ [r] such that..."
  let Fintype.instMeasurableSpace : MeasurableSpace X := ⊤ -- we use the power set Σ-algebra so that the measure theory stuff stays sane
  let U := (PMF.uniformOfFintype (X × X)).toMeasure
  obtain ⟨Λ, ⟨Λgen1, ⟨l, probge⟩⟩⟩ := geometric X U σ
  exists l
  exists Λ; simp only [Λgen1, true_and]

  -- "Hence there exists a vertex x ∈ X and a set X' ⊂ X such that, ..."
  obtain ⟨x, ⟨X', ⟨X'card, X'props⟩⟩⟩ :=
    pidgeon_thing
      (fun (x : X × X) ↦ Λ ≤ σ l x.1 ⬝ᵥ σ l x.2 ∧ ∀ i, i ≠ l → -1 ≤ σ i x.1 ⬝ᵥ σ i x.2)
      probge

  exists x; simp only [coe_mem, neg_mul, true_and]
  exists X'

  have : Nonempty { x // x ∈ X' } := by
    rw [← Fintype.card_pos_iff]
    have : 0 < (3 ^ (-(4 : ℝ) * ↑r)) * rexp (-((4 : ℝ) * r * √r) * √(Λ + 1)) * ↑(Fintype.card { x // x ∈ X }) := by positivity
    convert lt_of_lt_of_le this X'card using 1
    simp only [Fintype.card_coe, Nat.cast_pos]

  exists this

  -- "Setting $Y'_i = N'_i(x)$ for each $i \in [r]$,..."
  let Y' (i : Fin r) : Finset V := N' i x
  exists fun i => Y' i

  have Y'card {i : Fin r} : #(Y' i) = (p X (Y i) χ i) * #(Y i) := by
    simp_rw [Y', N'card, p]
    exact omg (ne_of_gt (Nat.cast_pos.mpr (Ypos i)))

  let lX' := lift X'

  -- "...it follows that..."
  have Y'lee :
      p X (Y l) χ l + Λ * (α l) ≤ p (lift X') (Y' l) χ l ∧
      ∀ (i : Fin r), (i ≠ l) → p X (Y i) χ i - (α i) ≤ p lX' (Y' i) χ i := by

    let factor (i : Fin r) : ℝ := if i = l then Λ else -1

    let f (i : Fin r) (x' : V) : ℝ := (p X (Y i) χ i + (factor i) * α i) * (pY X (Y i) χ i)
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


    have mins (i : Fin r) := calc f i x
     _ = (mymin (f i) lX')        := min_const (fun _ _ ↦ rfl)
     _ ≤ (mymin (g i) lX')        := min_le_ℕ (tr (ext i))

    have pos (i : Fin r) : (0 : ℝ) < ↑(#(N' i x)) := by simp only [N'card, Nat.cast_pos]; exact ppos i

    have hm (i : Fin r) :=
      calc p X (Y i) χ i + (factor i) * α i
     _ = (f i) x / ↑(pY X (Y i) χ i) := omg3 (by rw [← @N'card i x]; exact ne_of_gt (pos i))
     _ = (f i) x / #(N' i x)  := by simp [N'card]
     _ ≤ (mymin (g i) lX') / #(N' i x) := (omg2 (ne_of_gt (pos i))).mp (mins i)

    constructor
    · convert (hm l)
      exact Eq.symm (if_pos rfl)
    · intros i inl
      have := hm i
      simpa only [inl, reduceIte, neg_mul, one_mul, factor]

  repeat any_goals constructor
  · simp only [N'sub, implies_true, Y']
  · simp only [neg_mul, Fintype.card_coe] at X'card
    simp only [neg_mul, X'card, β, C]
  · simp only [Y'card, implies_true]
  · exact Y'lee.1
  · exact fun i inl ↦ Y'lee.2 i inl
