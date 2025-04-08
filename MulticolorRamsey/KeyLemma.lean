import MulticolorRamsey.GeometricLemma

open MeasureTheory ProbabilityTheory Finset Real

open scoped ENNReal

----------------------------------------------------------------------------------------------------
-- p
-- TODO use the proper minimum or whatever! i was to annoyed to figure out how it works at the time

def mymin (f : V → W) (X : Finset V) : W := sorry

lemma min_const (f : V → ℝ) (X : Finset V) (_ : ∀ x ∈ X, f x = c) : c = mymin f X := sorry

lemma min_le (f g : V → ℝ) (X : Finset V) (_ : ∀ x ∈ X, f x ≤ g x) : mymin f X ≤ mymin g X := sorry

lemma min_le_ℕ (f : V → ℝ) (g : V → ℕ) (X : Finset V) (_ : ∀ x ∈ X, f x ≤ g x) : mymin f X ≤ mymin g X := sorry

lemma min_le_mem (f : V → ℝ) (v : V) (X : Finset V) : mymin f X ≤ f v := sorry

lemma min_le_mem_ℕ (f : V → ℕ) (v : V) (X : Finset V) : mymin f X ≤ f v := sorry


-- this is pᵢ|Yᵢ| in the text
def pY {V : Type} [Fintype V] [DecidableEq V] (X Y : Finset V) (χ : (⊤ : SimpleGraph V).EdgeColoring (Fin r))
    (i : Fin r) : ℕ :=
  mymin (fun x => #((χ.N i x) ∩ Y)) X

-- this is pᵢ in the text
noncomputable def p {V : Type} [Fintype V] [DecidableEq V] (X Y : Finset V) (EC : (⊤ : SimpleGraph V).EdgeColoring (Fin r))
    (i : Fin r) : ℝ := (pY X Y EC i) / (#Y : ℝ)

----------------------------------------------------------------------------------------------------
-- key lemma

lemma sposnn {Λ : ℝ} :
    (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 3 ^ ((4 : ℝ) * r) * rexp (-(4 * ↑r ^ (3 / 2)) * √(Λ + 1))) := by
  positivity

lemma key {n : ℕ} [Nonempty (Fin r)] (V : Type) [DecidableEq V] [Nonempty V] [Fintype V] {cardV : Fintype.card V = n} [MeasurableSpace V]
  (χ : (⊤ : SimpleGraph V).EdgeColoring (Fin r))
  (X : Finset V) [nenX : Nonempty X]-- TODO strict subset!
  (Y : Fin r → (Finset V)) (Ypos : ∀ i, 0 < #(Y i)) -- TODO here too
  (α : Fin r → ℝ) (αpos : ∀ i, 0 < α i) :

  let β := ↑1 / (3 ^ (4 * r) : ℝ)
  let C := 4 * (↑r : ℝ) ^ ((3 : ℝ) / ↑2)

  ∃ l : Fin r, ∃ Λ, (-1 ≤ Λ) ∧
  ∃ x ∈ X, ∃ X' : Finset V, ∃ nx : Nonempty X', ∃ Y' : Fin r → (Finset V),
    X' ⊆ X ∧ -- TODO paper says strict subset but idk if that's true
    (∀ i, (Y' i) ⊆ (χ.N i x) ∩ (Y i)) ∧-- same

    β * Real.exp (-C * Real.sqrt (Λ + 1)) * X.card ≤ X'.card ∧

    p X (Y l) χ l + Λ * (α l) ≤ p X' (Y' l) χ l ∧

    (∀ i ≠ l, ((Y' i).card = (p X (Y i) χ i) * (Y i).card)) ∧
    ∀ i ≠ l, p X (Y i) χ i - (α i) ≤ p X' (Y' i) χ i := by

  intros β C

  let p' (i : Fin r) (x : V) : (pY X (Y i) χ i) ≤ #(χ.N i x ∩ Y i) :=
    min_le_mem_ℕ (fun x => #((χ.N i x) ∩ Y i)) x X

  -- "for each 𝑥 ∈ 𝑋, choose a set N′i (x) ⊂ 𝑁i(x) ∩ Yi of size exactly 𝑝𝑖(𝑋, 𝑌𝑖)|Yi|"
  let N' (i : Fin r) (x : V) : (Finset V) := Classical.choose (Finset.exists_subset_card_eq (p' i x))

  have N'sub {x : V} (i : Fin r) : (N' i x) ⊆ χ.N i x ∩ Y i := by
    simp [N', Classical.choose_spec (Finset.exists_subset_card_eq (p' i x))]

  have N'subN {i : Fin r} {x : V} : (N' i x) ⊆ χ.N i x :=
  (Finset.subset_inter_iff.mp (N'sub i)).1

  have N'card {i : Fin r} {x : V} : #(N' i x) = (pY X (Y i) χ i) := by
    simp [N', Classical.choose_spec (Finset.exists_subset_card_eq (p' i x))]

  -- "... and set ..."
  let σ (i : Fin r) (x : X) : (V → ℝ) :=
    (↑1 / Real.sqrt ((α i) * (pY X (Y i) χ i))) •
      ((Set.indicator ↑(N' i x) (fun _ ↦ 1)) - (p X (Y i) χ i) • (Set.indicator ↑(Y i) (fun _ ↦ 1)))

  -- "... Note that, for any x,y ∈ X,..."
  have Λiff (Λ : ℝ) (i : Fin r) {x y : X} (lam_ge : Λ ≤ ((σ i x) ⬝ᵥ (σ i y))) : -- we only need mp direction, paper says iff
      ((p X (Y i) χ i) + Λ * (α i)) * ((pY X (Y i) χ i) : ℝ) ≤ ((N' i x) ∩ (N' i y)).card := sorry

  -- "Now by Lemma 7, there exists Λ ≥ -1 and colour l ∈ [r] such that..."
  let U := (PMF.uniformOfFintype X).toMeasure
  obtain ⟨Λ, ⟨Λgen1, ⟨l, probge⟩⟩⟩ := geometric r X U σ
  exists l
  exists Λ; simp only [Λgen1, true_and]

  -- "Hence there exists a vertex x ∈ X and a set X' ⊂ X such that, ..."
  obtain ⟨x, ⟨x', ⟨hl, hi⟩⟩⟩ :=
    probabilistic_method U
      (fun (x x' : X) ↦ Λ ≤ σ l x ⬝ᵥ σ l x' ∧ ∀ i, i ≠ l → -1 ≤ σ i x ⬝ᵥ σ i x')
      (lt_of_lt_of_le sposnn probge)
  set X' : Finset V := { ↑x' } with X'd -- TODO we choose the singleton. is this a problem?


  exists x; simp only [coe_mem, neg_mul, true_and]
  exists X'; simp only [singleton_subset_iff, coe_mem, mem_singleton, nonempty_subtype, exists_eq, exists_const, X']

  -- "Setting $Y'_i = N'_i(x)$ for each $i \in [r]$,..."
  let Y' (i : Fin r) : Finset V := N' i x

  have Y'card {i : Fin r} : #(Y' i) = (p X (Y i) χ i) * #(Y i) := by
    simp_rw [Y', N'card, p]
    exact omg (Nat.cast_pos.mpr (Ypos i))

  -- "...it follows that..."
  -- TODO need to handle empty N'. at the moment we just "sorry" that case where we call Y'lee
  have Y'lee (pos : ∀ (i : Fin r), 0 < ↑(#(N' i x) : ℝ)) :
      p X (Y l) χ l + Λ * (α l) ≤ p X' (Y' l) χ l ∧
      ∀ (i : Fin r), (i ≠ l) → p X (Y i) χ i - (α i) ≤ p X' (Y' i) χ i := by

    -- the cases for l and i look so similar i'm sure there is some golf opportunity

    let fl (x' : V) : ℝ := (p X (Y l) χ l  + Λ * α l) * (pY X (Y l) χ l)
    let f (i : Fin r) (x' : V) : ℝ := (p X (Y i) χ i - α i) * (pY X (Y i) χ i)
    let g i (x' : V) : ℕ := #(N' i x' ∩ N' i x)

    have ext2 : (∀ a ∈ X', fl a ≤ g l a)  := by
      simp only [X'd, mem_singleton, forall_eq]
      have := calc Λ
        _ ≤ σ l x ⬝ᵥ σ l x' := by simp [hl]
        _ = σ l x' ⬝ᵥ σ l x := dotProduct_comm (σ l x) (σ l x')
      exact (Λiff Λ l) this

    have ext (i : Fin r) (inl : i ≠ l): (∀ a ∈ X', f i a ≤ g i a)  := by
      simp [X'd]
      have := calc -1
        _ ≤ σ i x ⬝ᵥ σ i x' := hi i inl
        _ = σ i x' ⬝ᵥ σ i x := dotProduct_comm (σ i x) (σ i x')
      have := (Λiff (-1 : ℝ) i) this
      simp only [neg_mul, one_mul] at this
      assumption


    have minsl := calc fl x
     _ = (mymin fl X')           := min_const fl X' (fun _ _ ↦ rfl)
     _ ≤ (mymin (g l) X')        := min_le_ℕ fl (g l) X' ext2

    have mins (i : Fin r) (inl : i ≠ l) := calc f i x
     _ = (mymin (f i) X')           := min_const (f i) X' (fun _ _ ↦ by simp_rw [f])
     _ ≤ (mymin (g i) X')           := min_le_ℕ (f i) (g i) X' (ext i inl)

    constructor

    · calc p X (Y l) χ l + Λ * α l
     _ = fl x / ↑(pY X (Y l) χ l) := omg3 (by rw [← @N'card l x]; exact pos l)
     _ = fl x / #(N' l x)  := by simp [N'card]
     _ ≤ (mymin (g l) X') /  #(N' l x) := (omg2 (pos l)).mp minsl

    · intros i inl
      calc p X (Y i) χ i - α i
     _ = f i x / ↑(pY X (Y i) χ i) := omg3 (by rw [← @N'card i x]; exact pos i)
     _ = f i x / #(N' i x)  := by simp [N'card]
     _ ≤ (mymin (g i) X') / #(N' i x) := (omg2 (pos i)).mp (mins i inl)


  exists fun i => Y' i

  repeat any_goals constructor
  · simp [Y', N'sub]
  · sorry
  · have := (Y'lee (fun i => Nat.cast_pos.mpr sorry)).1
    simp [X', this]
  · simp [Y'card]
  · simp [←X'd]
    intros i inl
    have := (Y'lee sorry).2 i inl
    exact (OrderedSub.tsub_le_iff_right  (p X (Y i) χ i) (α i) (p X' (Y' i) χ i)).mp this
