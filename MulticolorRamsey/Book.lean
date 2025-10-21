import MulticolorRamsey.KeyLemma
import ExponentialRamsey.Prereq.Ramsey


import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

open Finset SimpleGraph

variable {V : Type} {r : ℕ} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty (Fin r)]


----------------------------------------------------------------------------------------------------
-- maybe mathlib. check if they are still actually used tho

-- TODO is this weird? maybe we should do minimum over a different thing
-- instance nenfs  : Nonempty { x // x ∈ univ (α := V)} := sorry

lemma Real.pow_le_rpow_of_exponent_ge {x : ℝ} {y z : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := sorry

-- lemma Real.mul_le_mul_left {a b c : ℝ} (bpos : 0 ≤ b) (hinf : 0 ≤ a) : b ≤ c → b * a ≤ c * a := sorry

lemma Finset.card_le_card_insert {α : Type u_1} [DecidableEq α] (a : α) (s : Finset α) : s.card ≤ (insert a s).card := by
  by_cases h : a ∉ s
  · simp [card_insert_of_notMem h]
  · push_neg at h; simp [card_insert_of_mem h]


lemma erm {R : Type u_1} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]
    {L : Type u_3} {f : L→ R} {r : R} {t : List L} (hf0 : ∀ x ∈ t, 0 ≤ f x) (hf : ∀ x ∈ t, r ≤ f x) :
    r ^ t.length ≤ (List.map f t).prod := by
  sorry



lemma reh (Y : Finset V) : Membership.mem Y.val = Y.toSet := by
  ext; simp only [mem_val]; exact Eq.to_iff rfl


lemma pk_subset {X' : Finset V} (nen : X'.Nonempty) (ki : Saga χ) (sub : X' ⊆ ki.X) (i : Fin r) :
    (ki.p i) ≤ (p'p χ X' ki.Y i) := by
  unfold Saga.p
  simp [p'p, ppY]; gcongr; simp [nen]
  split
  intros a ax
  apply Finset.min'_le -- _ #(N χ i x ∩ ki.Y i) ?_
  simp
  use a, sub ax
  simp

----------------------------------------------------------------------------------------------------


----------------------------------------------------------------------------------------------------
section
-- parameters that don't change during book "algo"

structure BookParams (V : Type) (r : ℕ) [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty (Fin r)] where
    (t : ℕ) (tpos : 0 < t)
    (Λ₀ : ℝ) (Λ₀ge : -1 ≤ Λ₀)
    (δ : ℝ) (δpos : 0 < δ)
    χ : TopEdgeLabelling V (Fin r)
    (s : Saga χ)
    (nen : s.X.Nonempty)
    pYpos : ∀ (i : Fin r), 0 < s.pY i
    (lle : Λ₀ ≤ t) (δle : δ ≤ 1/4)
    (tge : 2 ≤ t)
    -- we have pnn because of the eq below (15) on p12
    (pnn : 0 ≤ ((image s.p univ).min' (image_nonempty.mpr univ_nonempty)) - 3 * δ / 4)

variable {V : Type} {r : ℕ} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty (Fin r)] {param : BookParams V r}

-- instance : Nonempty param.s.X := param.s.nenX

noncomputable def BookParams.p₀ (param : BookParams V r) :=
    (image param.s.p univ).min' (image_nonempty.mpr univ_nonempty)

noncomputable def BookParams.δp (param : BookParams V r) := param.p₀ - 3 * param.δ / 4

lemma tpos : 0 ≤ (1 - 1 / (param.t : ℝ)) := by
      have : 1 ≤ (param.t : ℝ) := by norm_cast; exact param.tpos
      have : 1 / (param.t : ℝ) ≤ 1 := by simp; exact Nat.cast_inv_le_one param.t
      linarith

lemma p₀pos : 0 ≤ param.p₀ := by unfold BookParams.p₀; sorry
lemma p₀le : param.p₀ ≤ param.s.p i := sorry
lemma δppos : 0 ≤ param.δp := by unfold BookParams.δp; sorry

end

----------------------------------------------------------------------------------------------------
section
-- input structure for key lemma

structure KeyIn (param : BookParams V r) extends Saga param.χ where
  pYpos : ∀ (i : Fin r), 0 < toSaga.pY i
  mono : param.s.p i ≤ toSaga.p i

variable {param : BookParams V r}

-- instance (kin : KeyIn param) : Nonempty kin.X := kin.nenX

-- noncomputable def KeyIn.p (kin : KeyIn param) (i : Fin r) : ℝ :=
--   kin.p i -- i should do this everywhere

-- lemma p'_nonneg (kin : KeyIn param) (i : Fin r) : 0 ≤ kin.p i :=
--   p_nonneg _ _ _

lemma p'_le_one (kin : KeyIn param) (i : Fin r) : kin.p i ≤ 1 :=
  pk_le_one kin.toSaga i

noncomputable def KeyIn.α (kin : KeyIn param) (i : Fin r) :=
  (1 / param.t) * ((kin.p i) - param.p₀ + param.δ)

lemma αpos (kin : KeyIn param) (i : Fin r) : 0 < kin.α i := by
  refine mul_pos (by norm_num; exact param.tpos) ?_
  refine add_pos_of_nonneg_of_pos (sub_nonneg.mpr ?_) param.δpos
  unfold BookParams.p₀ Saga.p
  trans param.s.p i
  exact p₀le
  exact kin.mono

end

----------------------------------------------------------------------------------------------------
variable {param : BookParams V r}


noncomputable def β (r : Nat) : ℝ := (3 ^ (-(4 : ℝ) * r) : ℝ)
noncomputable def C (r : Nat) : ℝ := 4 * (r : ℝ) * √r

lemma βpos : 0 < β r := by unfold β; positivity
lemma βposr : 0 < β r / r := by refine div_pos βpos ?_; norm_cast; exact Fin.pos'

-- output structure for key lemma
structure KeyOut (bin : KeyIn param) extends Saga param.χ where
  l : Fin r
  Λ : ℝ
  Λge : -1 ≤ Λ
  (x : V)
  (xX : x ∈ bin.X)
  (X'sub : toSaga.X ⊆ bin.X)
  (Y'sub : ∀ i, (toSaga.Y i) ⊆ (N param.χ i x) ∩ (bin.Y i))
  (βcard : β r * Real.exp (-C r * Real.sqrt (Λ + 1)) * bin.X.card ≤ toSaga.X.card)
  (Y'card : ∀ i, ((toSaga.Y i).card = (bin.p i) * (bin.Y i).card))
  (f : bin.p l + Λ * (bin.α l) ≤ toSaga.p l)
  (g : ∀ i ≠ l, bin.p i - (bin.α i) ≤ toSaga.p i)
  (nen : toSaga.X.Nonempty)


-- instance  {kin : KeyIn param} (kout : KeyOut kin) : Nonempty kout.X := by exact? --kout.nen

-- call key lemma with an input KeyIn
noncomputable def keybi (bin : KeyIn param)
: KeyOut bin := by
  have := keyk param.χ bin.toSaga bin.pYpos bin.α (αpos bin)
  choose l Λ Λge x xX s nen Xs Xprop d e f g using this
  exact ⟨s, l, Λ, Λge, x, xX, Xs, Xprop, d, e, f, g, nen⟩

----------------------------------------------------------------------------------------------------
-- input/state structure for book "algorithm"

noncomputable def ε (param : BookParams V r) (r : Nat) : ℝ :=
  (β r / (r : ℝ)) * Real.exp (-C r * √(param.Λ₀ + 1))
noncomputable def Xb (param : BookParams V r) (Λs : Fin r → List ℝ) (T : Fin r → Finset V) (i : Fin r) :=
  (ε param r) ^ (r * #(T i) + (Λs i).length) * Real.exp (- 4 * r * √r * ((Λs i).map (λ Λ ↦ √(1 + Λ))).sum) * #(param.s.X) - r * #(T i)

lemma εpos {t : Nat} : 0 ≤ ε param t := by unfold ε; apply mul_nonneg; exact sorry; positivity
lemma εle1 {t : Nat} : ε param t ≤ 1 := sorry
lemma εleβ {t : Nat} : ε param r ≤ β r := by
    unfold ε; trans β r / 1 * 1; gcongr; simp
    · exact le_of_lt βpos
    · exact le_of_lt βpos
    · sorry
    · exact Real.exp_le_one_iff.mpr sorry
    · simp

-- input structure for the book "algorithm".
-- keeps track of the input for the key lemma in the next call (the KeyIn param)
-- as well as collecting book candidate sets and lambdas
-- and proofs of lemmata for previous calls so we can induce
-- most importantly a proof that all book candidate sets are actually monochromatic books
structure BookIn (param : BookParams V r) extends KeyIn param where
  -- these came out
  T : Fin r → Finset V
  (Tle (i : Fin r) : #(T i) ≤ param.t)
  (Tdisj (i : Fin r) : Disjoint toKeyIn.X (T i))
  (Λs : Fin r → List ℝ) -- all lambdas of previous boost calls including this one
  (Λsge : ∀ i, ∀ Λ ∈ Λs i, param.Λ₀ < Λ)
  (l41 (i : Fin r) :
    param.δ * ((1 - 1/(param.t : ℝ)) ^ (#(T i)) * ((Λs i).map (λ Λ ↦ 1 + (Λ / (param.t : ℝ)))).prod) ≤ toKeyIn.p i - param.p₀ + param.δ)
  (l44 (i : Fin r) : param.δp ^ (#(T i) + (Λs i).length) * #(param.s.Y i) ≤ #(toKeyIn.Y i))
  (l45 (i : Fin r) : Xb param Λs T i ≤ #toKeyIn.X)
  (rainbow : ∀ i, ∀ y ∈ T i, ∀ x ∈ toKeyIn.X, x ∈ N param.χ i y) -- a nice invariant
  (mbook (i : Fin r) : param.χ.MonochromaticBook i (T i) (toKeyIn.Y i)) -- the relevant bit

-- get input from params (for first call)
noncomputable def BookParams.bin (param : BookParams V r) : BookIn param := by
  exact ⟨⟨⟨param.s.X, param.s.Y⟩, param.pYpos, fun {i} ↦ pk_subset param.nen param.s (fun _ a ↦ a) i⟩,
   λ _ ↦ ∅, by simp, by simp,
   λ _ ↦ [], by simp, by simp [Saga.p]; sorry,
   by simp,
   by simp [Xb],
   by simp, by simp [TopEdgeLabelling.MonochromaticBook, EdgeLabelling.MonochromaticOf, EdgeLabelling.MonochromaticBetween]⟩

def BookIn.maxB (bin : BookIn param) : ℕ := univ.sum λ i ↦ (bin.Λs i).length

noncomputable def BookIn.maxT (bin : BookIn param) : ℕ := ∑ i, #(bin.T i)

-- number of boost steps in color i we took so far
def BookIn.B (re : BookIn param) : Fin r → ℕ := λ i ↦ (re.Λs i).length

-- number of color steps in color i we took so far
def BookIn.C (re : BookIn param) : Fin r → ℕ := λ i ↦ (re.T i).card

noncomputable def BookIn.Xbound (bin : BookIn param) (T : Fin r → Finset V) (i : Fin r) :=
  Xb param bin.Λs T i

-- this somehow follows from the choice of Λ₀ and μ says yamaan
lemma Xbound_pos (bin : BookIn param) (T : Fin r → Finset V) (i : Fin r) :
    0 < bin.Xbound T i := sorry

----------------------------------------------------------------------------------------------------
-- output structure for book "algo"
-- i need the size of the biggest T as type parameter here, so i can argue that it gets bigger eventually
-- even after some boost steps in termination proof of stepper
structure BookOut (param : BookParams V r) (maxT : ℕ) where
  -- prev : BookIn param -- inputs for this call
  bin : BookIn param -- new inputs for next call
  -- (ky : KeyOut prev)
  -- (j : Fin r) -- which color did we pick
  step_inc : maxT < bin.maxT
  -- (step_lt : ∃ (i : Fin r), (T i).card < (bin.T i).card)
  -- (Tdisj (i : Fin r) : ∀ v ∈ T i, v ∉ bin.X ∧ ∀ j, v ∉ bin.Y j)

----------------------------------------------------------------------------------------------------
-- all the lemmata we need during each step

variable {bin : BookIn param} {kout : KeyOut bin.toKeyIn}

def newYb (kout : KeyOut bin.toKeyIn) (i : Fin r) := if i = kout.l then kout.Y i else bin.Y i
def newY (kout : KeyOut bin.toKeyIn) (i j : Fin r) := if i = j then kout.Y i else bin.Y i
def newT (i j : Fin r) (x : V) := if i = j then insert x (bin.T i) else bin.T i


-- p is bounded below
lemma l42p (bin : BookIn param) (i : Fin r) : param.δp ≤ bin.p i := by
    suffices param.δp - param.p₀ + param.δ ≤ bin.p i - param.p₀ + param.δ by linarith
    trans  param.δ * ((1 - 1 / param.t) ^ (bin.T i).card * (List.map (fun Λ ↦ 1 + Λ / (param.t : ℝ)) (bin.Λs i)).prod)
    · ring_nf
      trans 1/4 * (1/4)
      sorry
      sorry -- no idea
    exact bin.l41 i

lemma pl1 (bin : BookIn param) (i : Fin r) : param.δp ≤ 1 :=
  le_trans (l42p bin i) (p'_le_one _ _)

-- α is bounded below
lemma l42α (bin : BookIn param) (i : Fin r) : param.δ / (4 * param.t) ≤ bin.α i := by
    unfold KeyIn.α
    trans 1 / param.t * (param.δ * ((1 - 1 / param.t) ^ (bin.T i).card * (List.map (fun Λ ↦ 1 + Λ / (param.t : ℝ)) (bin.Λs i)).prod))
    · ring_nf; simp_rw [mul_assoc]; gcongr
      exact le_of_lt param.δpos
      sorry -- no idea
    · gcongr
      exact bin.l41 i

-- the upper bound on the number of boost steps
noncomputable def BookParams.B : ℕ :=
  ⌈param.t * (4 * Real.log (1 / param.δ)) / param.Λ₀⌉₊

-- "number of boost steps is bounded by a constant"
lemma l43 (bin : BookIn param) (i : Fin r):
    bin.B i ≤ param.B := by
  have posl (Λ : ℝ) (l : -1 ≤ Λ): 0 < (1 + Λ / param.t) := sorry
  have pos : 0 < (1 + param.Λ₀ / param.t) := posl param.Λ₀ param.Λ₀ge
  let c := (bin.T i).card
  have : 1/4 * param.δ * (1 + param.Λ₀/param.t) ^ (bin.B i) ≤ 1 + param.δ := by
    trans param.δ * (1 - 1 / (param.t : ℝ)) ^ c * (1 + param.Λ₀ / param.t) ^ bin.B i
    · rw [mul_comm _ param.δ]
      gcongr
      exact le_of_lt param.δpos
      sorry -- no idea
    · trans bin.p i - param.p₀ + param.δ
      · trans param.δ * (1 - 1 / param.t) ^ c * (List.map (fun Λ ↦ 1 + Λ / (param.t : ℝ)) (bin.Λs i)).prod
        gcongr param.δ * (1 - 1 / param.t) ^ c * ?_
        apply mul_nonneg (le_of_lt param.δpos) (pow_nonneg tpos _)
        · apply erm
          · intros _ a; refine le_of_lt (posl _ ?_); exact le_of_lt (lt_of_le_of_lt param.Λ₀ge (bin.Λsge i _ a))
          · intros _ Λi; gcongr; exact le_of_lt (bin.Λsge i _ Λi)
        · rw [mul_assoc]; exact bin.l41 i
      · have : bin.p i ≤ 1 := by unfold Saga.p; apply pk_le_one
        have : bin.p i - param.p₀ ≤ 1 := by trans bin.p i; exact sub_le_self (bin.p i) p₀pos; exact this
        gcongr
  have : (1 + param.Λ₀/param.t) ^ (bin.B i : ℝ) ≤ (1 + param.δ) * (1/4 * param.δ)⁻¹ := sorry
  have := Real.le_log_of_rpow_le pos this
  simp at this
  sorry

-- card of Y after color step is bounded below by something terrible
lemma l44color
  (kout : KeyOut bin.toKeyIn) (j : Fin r) (ghrm : x ∉ bin.T j)
  :
      let newY (i : Fin r) := if i = j then kout.Y i else bin.Y i
      let newT (i : Fin r) := if i = j then insert x (bin.T i) else bin.T i
  ∀ (i : Fin r), param.δp ^ ((newT i).card + bin.B i) * (param.s.Y i).card ≤ (newY i).card := by
    intro newY newT i
    unfold newY
    split -- did we color Y or no
    · expose_names
      rw [h]
      trans param.δp ^ (((bin.T j).card) + 1 + bin.B j) * (param.s.Y j).card
      · gcongr ?_ * (param.s.Y j).card
        refine Real.pow_le_rpow_of_exponent_ge param.pnn (pl1 bin i) ?_
        gcongr; simp [newT, ghrm]
      rw [kout.Y'card j]
      trans param.δp * param.δp ^ (bin.C j + bin.B j) * (param.s.Y j).card
      · gcongr ?_ * (param.s.Y j).card
        rw [show (bin.T j).card = bin.C j by rfl]
        exact le_of_eq (by ring)
      · trans param.δp * (bin.Y j).card
        · rw [mul_assoc]
          gcongr param.δp * ?_; exact param.pnn; exact bin.l44 j
        · gcongr; exact l42p bin j
    · expose_names
      trans param.δp ^ ((bin.T i).card + bin.B i) * (param.s.Y i).card
      · unfold newT; simp [h]
      trans param.δp ^ ((bin.T i).card + (bin.Λs i).length) * (param.s.Y i).card
      · gcongr ?_ * (param.s.Y i).card
        refine Real.pow_le_rpow_of_exponent_ge param.pnn (pl1 bin i) (by rfl)
      · exact bin.l44 i

-- card of Y after boost step is bounded below by something terrible
lemma l44boost  :
      let newΛs (i : Fin r) := if i = kout.l then kout.Λ :: (bin.Λs i) else bin.Λs i
  ∀ (i : Fin r), param.δp ^ ((bin.T i).card + (newΛs i).length) * (param.s.Y i).card ≤ (newYb kout i).card := by
    intro newΛs i
    unfold newYb newΛs
    split
    · rw [List.length]
      have (k : ℝ) (m n : ℕ) : k ^ (n + (m + 1)) = (k ^ (n + m) * k) := rfl
      rw [this]
      have (k s : ℝ) (m : ℕ) : s ^ m * s * k = s * (s ^ m * k) := by linarith
      rw [this]
      trans param.δp * #(bin.Y i)
      gcongr; exact param.pnn; exact bin.l44 i
      rw [kout.Y'card i]
      gcongr
      exact l42p bin i
    · exact bin.l44 i

----------------------------------------------------------------------------------------------------
-- lemma 4.5

-- card of X after boost step is bounded below
lemma l45boost  :
    let newΛs (i : Fin r) := if i = kout.l then kout.Λ :: (bin.Λs i) else bin.Λs i

    ∀ (i : Fin r), Xb param newΛs bin.T i ≤ (kout.X).card := by
  intro newΛs i
  have kc := kout.βcard
  have := bin.l45 i
  trans (β r * Real.exp (-C r * √(kout.Λ + 1))) / r * bin.X.card
  · trans ((#bin.X) : ℝ)
    sorry

    trans 1 * (#bin.X); simp; gcongr
    sorry

  trans 1 / (r : ℝ) * (kout.X.card : ℝ)
  · suffices 1 / (r : ℝ) * (β r * Real.exp (-C r * √(kout.Λ + 1)) * bin.X.card) ≤ 1 / (r : ℝ) * kout.X.card by sorry
    gcongr 1 / (r : ℝ) * ?_
  · simp
    trans 1 * (kout.X).card
    gcongr; exact Nat.cast_inv_le_one r
    simp

-- card of X after color step is bounded below
lemma l45color
    (kout : KeyOut bin.toKeyIn) (j : Fin r) (jn : j ≠ kout.l) :
    let X' := N param.χ j kout.x ∩ (kout.X)
    let newT (i : Fin r) := if i = j then insert kout.x (bin.T i) else bin.T i
    ∀ (i : Fin r), bin.Xbound newT i ≤ X'.card := by
  intro X' newT i
  unfold X'
  trans (β r * Real.exp (-C r * √(kout.Λ + 1))) / r * bin.X.card
  · sorry
  trans 1 / (r : ℝ) * (kout.X.card : ℝ)
  · suffices 1 / (r : ℝ) * (β r * Real.exp (-C r * √(kout.Λ + 1)) * bin.X.card) ≤ 1 / (r : ℝ) * kout.X.card by sorry
    gcongr 1 / (r : ℝ) * ?_
    exact kout.βcard
  · simp
    trans 1 * (kout.X).card
    gcongr; exact Nat.cast_inv_le_one r
    simp
    sorry

----------------------------------------------------------------------------------------------------
-- lemma 4.1

lemma l41nothing
    (X' : Finset V) (X'sub : X' ⊆ bin.X) (i : Fin r) (nen : X'.Nonempty) :
    param.δ * ((1 - 1 / param.t) ^ (bin.T i).card * (List.map (fun Λ ↦ 1 + Λ / (param.t : ℝ)) (bin.Λs i)).prod) ≤
    p'p param.χ X' bin.Y i - param.p₀ + param.δ := by
  trans bin.p i - param.p₀ + param.δ
  · exact bin.l41 i
  · gcongr
    refine pk_subset (V := V) nen bin.toSaga X'sub i

lemma l41color
  {kout : KeyOut bin.toKeyIn} (j : Fin r) (Tne : kout.x ∉ bin.T j) (jnn : j ≠ kout.l)
    (nen : (N param.χ j kout.x ∩ (kout.X)).Nonempty) :
    let X' := N param.χ j kout.x ∩ (kout.X)
    let newY (i : Fin r) := if i = j then kout.Y i else bin.Y i
    let newT (i : Fin r) := if i = j then insert kout.x (bin.T i) else bin.T i
∀ (i : Fin r), param.δ * ((1 - 1 / param.t) ^ (newT i).card * (List.map (fun Λ ↦ 1 + Λ / (param.t : ℝ)) (bin.Λs i)).prod) ≤
    p'p param.χ X' newY i - param.p₀ + param.δ := by
  intro X' newY newT i

  have pos : 0 ≤ 1 - 1 / (param.t : ℝ) := tpos

  unfold newT newY
  · by_cases h : i = j -- cases i = j vs i ≠ j
    · -- case i = j: this is the color we chose
      simp only [h]
      unfold X'
      simp only [↓reduceIte, ge_iff_le]
      trans bin.p j - bin.α j - param.p₀ + param.δ
      · trans (1 - 1 / (param.t : ℝ)) * (bin.p j - param.p₀ + param.δ)
        have thi (k : ℝ) (m : ℕ) : k ^ (m + 1) = (k ^ m * k) := rfl
        have tha (k s t : ℝ) (m : ℕ) : t * (s ^ m * s * k) = s * (t * (s ^ m * k)) := by ring
        rw [card_insert_of_notMem Tne, thi, tha]
        gcongr
        · exact bin.l41 j
        · unfold KeyIn.α; refine le_of_eq (by ring)
      · gcongr
        trans kout.p j
        exact kout.g j jnn
        simp only [p'p, ppY, ↓reduceIte]; gcongr; simp only [nen, ↓reduceDIte, le_min'_iff,
          mem_image, mem_inter, Set.mem_toFinset, forall_exists_index, and_imp]
        split
        intros i a ax axx nj
        apply Finset.min'_le
        simp only [mem_image]; use a; simp only [zero_le, implies_true]
    · simp only [h, ↓reduceIte, ge_iff_le]
      apply le_trans <| l41nothing X' (Subset.trans inter_subset_right kout.X'sub) i nen
      simp only [p'p, ppY, h, ↓reduceIte, le_refl]

lemma l41boost :
    let newΛs (i : Fin r) := if i = kout.l then kout.Λ :: (bin.Λs i) else bin.Λs i
    ∀ (i : Fin r), param.δ * ((1 - 1 / param.t) ^ (bin.T i).card * (List.map (fun Λ ↦ 1 + Λ / (param.t : ℝ)) (newΛs i)).prod) ≤
    p'p param.χ (kout.X) (newYb kout) i - param.p₀ + param.δ := by
  intro newΛs i

  have grm : 0 ≤ 1 + kout.Λ / param.t := by
    suffices h : -1 ≤ kout.Λ / param.t by linarith
    trans -1 / param.t
    rw [neg_div, neg_le_neg_iff, div_le_one]
    norm_cast; exact le_trans NeZero.one_le param.tge
    norm_cast; exact param.tpos
    apply div_le_div_of_nonneg_right
    exact kout.Λge
    norm_cast; exact le_of_lt param.tpos

  unfold newΛs newYb
  · by_cases h : i = kout.l
    · -- case i = kout.l: this is the color we chose
      simp only [h, ↓reduceIte, ge_iff_le]
      trans bin.p kout.l + kout.Λ * bin.α kout.l - param.p₀ + param.δ
      · trans (1 + kout.Λ / (param.t : ℝ)) * (bin.p kout.l - param.p₀ + param.δ)
        have (k s t u : ℝ) : k * (t * (s * u)) = s * (k * (t * u)) := by linarith
        rw [List.map_cons, List.prod_cons, this]
        gcongr
        · exact bin.l41 kout.l
        · unfold KeyIn.α
          ring_nf
          exact le_of_eq rfl
      · gcongr; apply le_trans kout.f
        simp [p'p, ppY]
    · simp only [h, ↓reduceIte, ge_iff_le]
      apply le_trans <| l41nothing kout.X kout.X'sub i kout.nen
      simp only [p'p, ppY, h, ↓reduceIte, le_refl]

lemma l46 :
    ((bin.Λs i).map (λ Λ ↦ √(1 + Λ))).sum ≤ param.t * 7 * r * Real.log (1 / param.δ) / √param.Λ₀ := sorry

----------------------------------------------------------------------------------------------------
-- correctness: the output T and Y always form a monochromatic book

lemma mau  {bin : BookIn param} {kout : KeyOut bin.toKeyIn} (i : Fin r) :
    Disjoint (bin.T i) (kout.Y i) := by
  refine disjoint_coe.mp (Set.disjoint_of_subset_right (trans (kout.Y'sub i) inter_subset_right) ?_)
  exact disjoint_coe.mpr (bin.mbook i).1


lemma mono_boost {bin : BookIn param} {kout : KeyOut bin.toKeyIn} (i : Fin r) :
    param.χ.MonochromaticBook i (bin.T i) (newYb kout i) := by
  apply param.χ.monochromaticBook_subset (bin.mbook i)
  simp [newYb]; split_ifs; exact (Subset.trans (kout.Y'sub i) inter_subset_right); simp

open EdgeLabelling in
lemma mono (i : Fin r) :
    let newY (i : Fin r) := if i = j then kout.Y i else bin.Y i
    let newT (i : Fin r) := if i = j then insert kout.x (bin.T i) else bin.T i
    param.χ.MonochromaticBook i (newT i) (newY i) := by
  intros newY newT
  unfold newT newY
  split
  · repeat any_goals constructor
    · -- disjoint
      simp only [disjoint_insert_left]
      constructor
      · apply Set.notMem_subset ?_ (coloredNeighborSet_not_mem (EC := param.χ) i kout.x)
        convert (Subset.trans (kout.Y'sub i) inter_subset_left)
        have (Y : Finset V) : Membership.mem Y.val = Y.toSet := by
          ext; simp only [mem_val]; exact Eq.to_iff rfl
        simp only [this, Set.subset_toFinset]
      · exact mau i
    · --newT monochromatic
      push_cast
      apply (monochromaticOf_insert).mpr
      constructor
      · exact (bin.mbook i).2.1
      · refine param.χ.monochromaticBetween_neighbors ?_
        convert λ y yy ↦ bin.rainbow i y yy kout.x kout.xX
        ext; simp
    · -- mono between newT and newY
      rw [insert_eq]
      push_cast
      apply monochromaticBetween_union_left.mpr ⟨?_, ?_⟩
      · refine (param.χ.monochromaticBetween_neighbors ?_).symm
        intros y yY
        rw [coloredNeighborSet.symm]
        convert mem_of_subset (Subset.trans (kout.Y'sub i) inter_subset_left) yY
        ext; simp
      · refine (bin.mbook i).2.2.subset_right ?_
        exact subset_trans (kout.Y'sub i) inter_subset_right


  exact bin.mbook i

----------------------------------------------------------------------------------------------------
-- big holes in the "algo"

-- TODO yamaan says this is ok issue #15
lemma pyposcolor :
    let X' := N param.χ j kout.x ∩ (kout.X)
    let newY (i : Fin r) := if i = j then kout.Y i else bin.Y i
    ∀ (i : Fin r), 0 < (Saga.mk (χ := param.χ) X' newY).pY i := by
  sorry

-- TODO yamaan says this is ok issue #15
lemma pypos :
    let X' := kout.X
    let newY (i : Fin r) := if i = kout.l then kout.Y i else bin.Y i
    ∀ (i : Fin r), 0 < (Saga.mk X' newY).pY (χ := χ) i := by
  sorry

-- TODO issue #25
lemma choice_j {bin : BookIn param} (kout : KeyOut bin.toKeyIn) :
    ∃ j, j ≠ kout.l ∧ (N param.χ j kout.x ∩ (kout.X)).card ≤ (kout.X.card - 1) / r := sorry -- issue #25

----------------------------------------------------------------------------------------------------
-- here comes the action

-- one good (color) step of the "algorithm". we recurse upon encountering a boost situation, and
-- return only after we did one color step. termination is guaranteed by lemma 4.3 (l43) which
-- bounds the number of boost steps.
noncomputable def step (bin : BookIn param) (Tlt : ∀ i, (bin.T i).card < param.t)
    : BookOut param (∑ i, (bin.T i).card) := by

  -- call the key lemma
  let kout := keybi bin.toKeyIn

  by_cases h : kout.Λ ≤ param.Λ₀
  · -- color step!
    choose j jn jp using choice_j kout

    -- update the vertices we consider
    let X' := N param.χ j kout.x ∩ (kout.X)

    -- update the book fringe
    let newY (i : Fin r) := if i = j then kout.Y i else bin.Y i

    -- TODO the sorry is vital, we need to thread another thing yay
    let new_in : KeyIn param := ⟨⟨X', newY⟩, λ i ↦ pyposcolor _, fun {i} => le_trans bin.mono sorry⟩

    -- update T: add x to book of color j
    have Tsub {i : Fin r} : kout.x ∉ bin.T i :=
      (bin.Tdisj i).notMem_of_mem_left_finset kout.xX

    let newT (i : Fin r) := if i = j then insert kout.x (bin.T i) else bin.T i

    have newTle (i : Fin r) : #(newT i) ≤ param.t := by
      unfold newT; split
      · rw [card_insert_of_notMem Tsub]; exact Tlt i
      · exact bin.Tle i

    have Xsub (i : Fin r) : Disjoint X' (newT i) := by
      have : Disjoint (kout.X) (bin.T i) := disjoint_of_subset_left kout.X'sub (bin.Tdisj i)
      have : Disjoint (N param.χ j kout.x ∩ kout.X) _ := disjoint_of_subset_left inter_subset_right this
      unfold X' newT
      split
      · simp [disjoint_insert_right, this, EdgeLabelling.coloredNeighborSet_not_mem]
      · exact this

    have rainbow : ∀ i, ∀ x ∈ newT i, ∀ y ∈ X', y ∈ N param.χ i x := by
      intros i x xT y yX
      have (h : x ∈ bin.T i) := bin.rainbow _ _ h _ (kout.X'sub (mem_inter.mp yX).2)
      unfold newT at xT
      split at xT
      · cases mem_insert.mp xT
        · expose_names; rw [h_1, h_2]
          exact mem_of_mem_filter y yX
        · expose_names; exact this h_2
      · exact this xT

    have nenX' : X'.Nonempty:= by
      refine card_pos.mp ((Nat.cast_pos (α := ℝ)).mp ?_)
      exact lt_of_lt_of_le (Xbound_pos _ _ _) (l45color kout j jn j)

    -- keep track of input for next iteration, state and inductive lemmata
    let newbi : BookIn param := ⟨new_in,
      newT, newTle, Xsub, bin.Λs, bin.Λsge,
      l41color j Tsub jn nenX', l44color kout j Tsub, l45color kout j jn, rainbow, mono⟩

    -- to ensure termination we also give a proof that T grew
    have Tcard : ∑ i, (bin.T i).card < ∑ i, (newbi.T i).card := by
      simp [newbi, newT, ← sum_erase_add (a := j), Tsub, sum_apply_ite_of_false]

    exact ⟨newbi, Tcard⟩

  · -- boost step!
    -- update our key sets
    -- TODO the sorry is vital, we need to thread another thing yay
    let new_in : KeyIn param := ⟨⟨kout.X, newYb kout⟩,  λ i ↦ pypos _, fun {i} => le_trans bin.mono sorry⟩

    -- keep track of the Λs used for boost steps
    let newΛs (i : Fin r) := if i = kout.l then kout.Λ :: (bin.Λs i) else bin.Λs i
    have newΛslt (i : Fin r) : ∀ Λ ∈ newΛs i, param.Λ₀ < Λ := by
      unfold newΛs; split
      · exact List.forall_mem_cons.mpr ⟨lt_of_not_ge h, bin.Λsge i⟩
      · exact bin.Λsge i

    have disjn (i : Fin r) := disjoint_of_subset_left kout.X'sub (bin.Tdisj i)

    have rainbow (i : Fin r) : ∀ y ∈ bin.T i, ∀ x ∈ kout.X, x ∈ N param.χ i y := by
      intros y yT x xX
      refine (bin.rainbow i y yT x) (Finset.mem_of_subset kout.X'sub xX)

    let newbi : BookIn param := ⟨new_in,
      bin.T, bin.Tle, disjn,
      newΛs, newΛslt,
      l41boost, l44boost, l45boost, rainbow, mono_boost⟩

    exact step newbi Tlt

termination_by r * param.B + 1 - bin.maxB
decreasing_by -- this uses boundedness of number of boost steps (l43)
  refine Nat.sub_lt_sub_left ?_ ?_
  · simp only [BookIn.maxB]
    -- here goes
    apply lt_of_lt_of_le (Order.lt_add_one_iff.mpr (sum_le_sum (λ i _ ↦ l43 bin i)))
    simp
  · simp [BookIn.maxB]
    apply sum_lt_sum
    intros i _; split <;> simp
    have (l : Fin r) (Λ : ℝ) (L : Fin r → List ℝ) : -- weird
        ∃ i ∈ univ, (L i).length < (if i = l then Λ :: L i else L i).length := by use l; simp
    apply this

-- recurse and do another step unless one of the Ts has appropriate size. termination is guaranteed
-- since the output type of each step includes a proof that some T has grown in size.
noncomputable def stepper  (bin : BookIn param) :
    ∃ sn : BookIn param, ∃ j, param.t = #(sn.T j) ∧ param.δp ^ (param.t + param.B) * #(param.s.Y j) ≤ #(sn.Y j) := by
  by_cases h : ∀ i, #(bin.T i) < param.t
  · exact stepper (step bin h).bin -- book not big enough yet. take another step
  · push_neg at h
    obtain ⟨j, jp⟩ := h
    have teqT := jp.antisymm (bin.Tle j)
    refine ⟨bin, j, ⟨teqT, ?_⟩⟩
    trans param.δp ^ (#(bin.T j) + (bin.Λs j).length) * #(param.s.Y j)
    · rw [← teqT]
      gcongr ?_ * #(param.s.Y j)
      exact Real.pow_le_rpow_of_exponent_ge param.pnn (pl1 bin j) (by gcongr; exact l43 bin j)
    · exact bin.l44 j

termination_by (r * param.t) - bin.maxT
decreasing_by
  unfold BookIn.maxT
  apply Nat.sub_lt_sub_left
  refine Nat.lt_of_lt_of_le (m :=  ∑ _ : Fin r, param.t) ?_ ?_
  gcongr with i
  · expose_names; exact univ_nonempty_iff.mpr inst_3
  · exact h i
  simp
  convert (step bin h).step_inc


-- thm 2.1
lemma book (t m : ℕ) (χ : TopEdgeLabelling V (Fin r))
  (tpos : 0 < t) (mpos : 0 < m)
  (X : Finset V) [nenX : Nonempty X]
  (Y : Fin r → (Finset V))
  (p : ℝ) (ppos : 0 < p)
  (μ : ℝ) (μge : 2^10 * r^3 ≤ μ)
  (tge : μ^5 / p ≤ t)
  (Y'card : ∀ i x, (p * ((Y i).card : ℝ) ≤ #((N χ i x) ∩ (Y i))))
  (Xge : (μ^2 / p)^(μ * r * t) ≤ #X)
  (Yge : ∀ i, (Real.exp (2^13 * r^3 / μ^2)) ^ t * m ≤ #(Y i))
  :
  ∃ c : Fin r, ∃ T M : Finset V, #T = t ∧ m ≤ #M ∧ χ.MonochromaticBook c T M := by
  let δ := p / μ^2
  have : 0 < r := Fin.pos'
  have : 0 < μ := lt_of_lt_of_le (by positivity) μge
  have δpos : 0 < δ := by simp [δ, ppos, sq_pos_of_pos this]
  let inp : BookParams V r :=
    ⟨t, tpos,
     (μ * Real.log (1 / δ) / 8 * (C r))^2, le_trans (by simp) (sq_nonneg _),
     δ, δpos,
     χ, ⟨X, Y⟩, sorry,
     sorry, -- issue #15
     sorry, sorry, sorry, sorry⟩

  -- run the "algorithm" and use its book
  obtain ⟨sn, ⟨j, ⟨a, b⟩⟩⟩ := stepper inp.bin

  use j
  use sn.T j
  use sn.Y j
  refine ⟨a.symm, ⟨?_, sn.mbook j⟩⟩

  -- now we need to bound size of Y to prove our book has the required size
  have : 0 ≤ inp.δp := δppos
  apply (Nat.cast_le (α := ℝ)).mp
  trans Real.exp (-2 * δ * t / p) * Real.exp (2 ^ 12 * r ^ 3 / μ ^ 2) ^ (t : ℝ) * m
  · apply le_mul_of_one_le_left (Nat.cast_nonneg' m)
    simp_rw [← Real.exp_mul, ← Real.exp_add]
    simp only [neg_mul, Real.one_le_exp_iff]
    sorry -- apparently follows from δ/p = 1/μ^2, as claimed on p12
  · trans Real.exp (-2 * δ * t / p) * (p ^ inp.B * Real.exp (2 ^ 13 * r ^ 3 / μ ^ 2) ^ (t : ℝ)) * m
    · gcongr Real.exp (-2 * δ * t / p) * ?_ * m
      trans Real.exp (-2 ^ 12 * r ^ 3 / μ ^ 2) * Real.exp (2 ^ 13 * r ^ 3 / μ ^ 2) ^ (t : ℝ)
      · sorry -- no idea but paper says so
      · gcongr
        sorry -- eq (16) somehow
    · trans inp.δp ^ (inp.t + inp.B) * (#(inp.s.Y j))
      · trans inp.δp ^ (inp.t + inp.B) * ((Real.exp (2^13 * r^3 / μ^2)) ^ t * m)
        · rw [show ∀ a b c d, a * (b * c) * d = (a * b) * (c * d) by sorry]
          gcongr
          sorry -- idk!
          norm_num
        · gcongr; exact Yge j
      · exact b
