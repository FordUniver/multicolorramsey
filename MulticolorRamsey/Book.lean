import MulticolorRamsey.KeyLemma

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

open Finset

----------------------------------------------------------------------------------------------------
-- maybe mathlib. check if they are still actually used tho

-- TODO is this weird? maybe we should do minimum over a different thing
instance nenfs  [Fintype V] [Nonempty V] : Nonempty { x // x ∈ univ (α := V)} := sorry

lemma Real.pow_le_rpow_of_exponent_ge {x : ℝ} {y z : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := sorry

lemma Real.mul_le_mul_left {a b c : ℝ} (bpos : 0 ≤ b) (hinf : 0 ≤ a) : b ≤ c → b * a ≤ c * a := sorry

lemma Finset.card_le_card_insert {α : Type u_1} [DecidableEq α] (a : α) (s : Finset α) : s.card ≤ (insert a s).card := by
  by_cases h : a ∉ s
  · simp [card_insert_of_notMem h]
  · push_neg at h; simp [card_insert_of_mem h]


lemma erm {R : Type u_1} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R] {L : Type u_3} {f : L→ R} {r : R} {t : List L} (hf0 : ∀ x ∈ t, 0 ≤ f x) (hf : ∀ x ∈ t, r ≤ f x) : r ^ t.length ≤ (List.map f t).prod := by
  sorry

----------------------------------------------------------------------------------------------------

variable {V : Type} {r : ℕ} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty (Fin r)]

----------------------------------------------------------------------------------------------------
-- parameters that don't change during book "algo"
structure book_params where
    (t : ℕ) (tpos : 0 < t)
    (Λ₀ : ℝ) (Λ₀ge : -1 ≤ Λ₀)
    (δ : ℝ) (δpos : 0 < δ)
    χ : (⊤ : SimpleGraph V).EdgeColoring (Fin r)
    X₀ : Finset V
    [nenX : Nonempty X₀]
    Y₀ : Fin r → Finset V
    pYpos : ∀ (i : Fin r), 0 < pY X₀ (Y₀ i) χ i
    (lle : Λ₀ ≤ t) (δle : δ ≤ 1/4)
    (tge : 2 ≤ t)
    -- we have pnn because of the eq below (15) on p12
    (pnn : 0 ≤ (mymin (fun i ↦ p X₀ (Y₀ i) χ i) (@univ (Fin r) (Fin.fintype r))) - 3 * δ / 4)

instance (pp : book_params (V := V) (r := r)) : Nonempty pp.X₀ := pp.nenX

def book_params.bound_pos (pp : book_params (V := V) (r := r)) : 0 < r * pp.t * (4 * Real.log (1 / pp.δ)) / pp.Λ₀ := sorry

noncomputable def book_params.p₀ (pp : book_params (V := V) (r := r)) := mymin (fun i ↦ p pp.X₀ (pp.Y₀ i) pp.χ i) (@univ (Fin r) (Fin.fintype r))

noncomputable def book_params.δp (pp : book_params (V := V) (r := r)) := pp.p₀ - 3 * pp.δ / 4

lemma p₀pos (pp : book_params (V := V) (r := r)) : 0 ≤ pp.p₀ := by unfold book_params.p₀; sorry
lemma p₀le (pp : book_params (V := V) (r := r)) : pp.p₀ ≤ p pp.X₀ (pp.Y₀ i) pp.χ i := sorry

lemma tpos (pp : book_params (V := V) (r := r)) : 0 ≤ (1 - 1 / (pp.t : ℝ)) := by
      have : 1 ≤ (pp.t : ℝ) := by norm_cast; exact pp.tpos
      have : 1 / (pp.t : ℝ) ≤ 1 := by simp; exact Nat.cast_inv_le_one pp.t
      linarith

lemma ggrmns {a d : ℝ} {b c e : ℕ} (DP : 0 ≤ d) (ar : 0 ≤ a) (al : a ≤ 1) (eb : e ≤ c) :
    a ^ (b + c) * d ≤ a ^ (b + e) * d := by
  gcongr ?_ * d
  refine Real.pow_le_rpow_of_exponent_ge ar al ?_
  gcongr b + ?_

lemma ggrmnsr {a d : ℝ} {b c e : ℕ} (DP : 0 ≤ d) (ar : 0 ≤ a) (al : a ≤ 1) (eb : e ≤ c) :
    a ^ (c + b) * d ≤ a ^ (e + b) * d := by
  gcongr ?_ * d
  refine Real.pow_le_rpow_of_exponent_ge ar al ?_
  gcongr ?_ + b

lemma gconcon {a b : ℝ} : 0 ≤ b → a ≤ a + b := by
  intros ng
  simp [ng]

----------------------------------------------------------------------------------------------------
-- input structure for key lemma

structure key_in (pp : book_params (V := V) (r := r)) where
  X : Finset V
  [nenX : Nonempty X]
  Y : Fin r → Finset V
  pYpos : ∀ (i : Fin r), 0 < pY X (Y i) pp.χ i

instance {pp : book_params (V := V) (r := r)} (ki : key_in pp) : Nonempty ki.X := ki.nenX

noncomputable def key_in.p' {pp : book_params (V := V) (r := r)} (nip : key_in pp) (i : Fin r) : ℝ :=
  p nip.X (nip.Y i) pp.χ i -- i should do this everywhere

lemma p'_nonneg {pp : book_params (V := V) (r := r)} (nip : key_in pp) (i : Fin r) : 0 ≤ nip.p' i :=
  p_nonneg _ _ _

lemma p'_le_one {pp : book_params (V := V) (r := r)} (nip : key_in pp) (i : Fin r) : nip.p' i ≤ 1 :=
  p_le_one pp.χ nip.X (nip.Y i)

noncomputable def key_in.α {pp : book_params (V := V) (r := r)} (nip : key_in pp) (i : Fin r) :=
  (1 / pp.t) * ((nip.p' i) - pp.p₀ + pp.δ)

lemma αpos {pp : book_params (V := V) (r := r)} (nip : key_in pp) (i : Fin r) : 0 < nip.α i :=
mul_pos
      (by norm_num; exact pp.tpos)
      (add_pos_of_nonneg_of_pos (sub_nonneg.mpr sorry) pp.δpos)

----------------------------------------------------------------------------------------------------

noncomputable def β (r : Nat) : ℝ := (3 ^ (-(4 : ℝ) * r) : ℝ)
noncomputable def C (r : Nat) : ℝ := 4 * (r : ℝ) * √r

lemma βpos : 0 < β r := by unfold β; positivity
lemma βposr : 0 < β r / r := by refine div_pos βpos ?_; norm_cast; exact Fin.pos'

-- output structure for key lemma
structure key_out {pp : book_params (V := V) (r := r)} (nip : key_in pp) where
  l : Fin r
  Λ : ℝ
  Λge : -1 ≤ Λ
  (x : V)
  (xX : x ∈ nip.X)
  (X' : Finset nip.X)
  [nenX' : Nonempty X']
  Y' : Fin r → Finset V
  (Y'sub : ∀ i, ↑(Y' i) ⊆ (N pp.χ i x) ∩ (nip.Y i))
  (βcard : β r * Real.exp (-C r * Real.sqrt (Λ + 1)) * nip.X.card ≤ X'.card)
  (Y'card : ∀ i, ((Y' i).card = (nip.p' i) * (nip.Y i).card))
  (f : nip.p' l + Λ * (nip.α l) ≤ p (lift X') (Y' l) pp.χ l)
  (g : ∀ i ≠ l, nip.p' i - (nip.α i) ≤ p (lift X') (Y' i) pp.χ i)


instance  {pp : book_params (V := V) (r := r)} {ki : key_in pp} (ko : key_out ki) : Nonempty ko.X' := ko.nenX'

-- call key lemma with an input key_in
noncomputable def keynip {pp : book_params (V := V) (r := r)} (nip : key_in pp (V := V) (r := r))
: key_out nip := by
  have := key V pp.χ nip.X nip.Y nip.α (αpos nip) nip.pYpos
  choose l Λ Λge x xX X' nenX' Y' Xprop d e f g using this
  exact ⟨l, Λ, Λge, x, xX, X', Y', Xprop, d, e, f, g⟩

----------------------------------------------------------------------------------------------------
-- input/state structure for book "algorithm"

noncomputable def ε (pp : book_params (V := V) (r := r)) (r : Nat) : ℝ :=
  (β r / (r : ℝ)) * Real.exp (-C r * √(pp.Λ₀ + 1))
noncomputable def Xb (pp : book_params (V := V) (r := r)) (Λs : Fin r → List ℝ) (T : Fin r → Finset V) (i : Fin r) :=
  (ε pp r) ^ (r * #(T i) + (Λs i).length) * Real.exp (- 4 * r * √r * ((Λs i).map (λ Λ ↦ √(1 + Λ))).sum) * #(pp.X₀) - r * #(T i)

lemma εpos (pp : book_params (V := V) (r := r)) (t : Nat) : 0 ≤ ε pp t := by unfold ε; apply mul_nonneg; exact sorry; positivity
lemma εle1 (pp : book_params (V := V) (r := r)) (t : Nat) : ε pp t ≤ 1 := sorry


structure book_nip (pp : book_params (V := V) (r := r)) where
  inp : key_in pp -- these ought to go into next step key lemma
  -- these came out
  T : Fin r → Finset V
  (Tle (i : Fin r) : #(T i) ≤ pp.t)
  (Tdisj (i : Fin r) : Disjoint inp.X (T i))
  (Λs : Fin r → List ℝ) -- all lambdas of previous boost calls including this one
  (Λsge : ∀ i, ∀ Λ ∈ Λs i, pp.Λ₀ < Λ)
  (l41 (i : Fin r) :
    pp.δ * ((1 - 1/(pp.t : ℝ)) ^ (#(T i)) * ((Λs i).map (λ Λ ↦ 1 + (Λ / (pp.t : ℝ)))).prod) ≤ inp.p' i - pp.p₀ + pp.δ)
  (l44 (i : Fin r) : pp.δp ^ (#(T i) + (Λs i).length) * #(pp.Y₀ i) ≤ #(inp.Y i))
  (l45 (i : Fin r) : Xb pp Λs T i ≤ #inp.X)
  (inv : ∀ i, ∀ y ∈ T i, ∀ x ∈ inp.X, x ∈ N pp.χ i y)
  (mbook (i : Fin r) : pp.χ.monochromaticBook i (T i) (inp.Y i))

-- get input from params (for first call)
noncomputable def book_params.nip (pp : book_params (V := V) (r := r)) : book_nip pp := by
  exact ⟨⟨pp.X₀, pp.Y₀, pp.pYpos⟩,
   λ _ ↦ ∅, by simp, by simp,
   λ _ ↦ [], by simp, by simp [key_in.p', p₀le],
   by simp, by simp [Xb],
   by simp, by simp [SimpleGraph.EdgeColoring.monochromaticBook, SimpleGraph.EdgeColoring.monochromatic]⟩

def book_nip.maxB {pp : book_params (V := V) (r := r)} (nip : book_nip pp) : ℕ := univ.sum λ i ↦ (nip.Λs i).length

noncomputable def book_nip.maxT {pp : book_params (V := V) (r := r)} (nip : book_nip pp) : ℕ := ∑ i, #(nip.T i)

-- number of boost steps in color i we took so far
def book_nip.B {pp} (re : book_nip pp (V := V) (r := r)) : Fin r → ℕ := λ i ↦ (re.Λs i).length

-- number of color steps in color i we took so far
def book_nip.C {pp} (re : book_nip pp (V := V) (r := r)) : Fin r → ℕ := λ i ↦ (re.T i).card

noncomputable def book_nip.Xbound (nip : book_nip pp (V := V) (r := r)) (T : Fin r → Finset V) (i : Fin r) :=
  Xb pp nip.Λs T i

-- this somehow follows from the choice of Λ₀ and μ says yamaan
lemma Xbound_pos (nip : book_nip pp (V := V) (r := r)) (T : Fin r → Finset V) (i : Fin r) :
    0 < nip.Xbound T i := sorry




----------------------------------------------------------------------------------------------------
-- output structure for book "algo"
-- i need the size of the biggest T as type parameter here, so i can argue that it gets bigger eventually
-- even after some boost steps in termination proof of stepper
structure book_out (pp : book_params (V := V) (r := r)) (maxT : ℕ) where
  -- prev : book_nip pp -- inputs for this call
  nip : book_nip pp -- new inputs for next call
  -- (ky : key_out prev)
  -- (j : Fin r) -- which color did we pick
  step_inc : maxT < nip.maxT
  -- (step_lt : ∃ (i : Fin r), (T i).card < (nip.T i).card)
  -- (Tdisj (i : Fin r) : ∀ v ∈ T i, v ∉ nip.X ∧ ∀ j, v ∉ nip.Y j)

----------------------------------------------------------------------------------------------------
-- all the lemmata we need during each step

-- p is bounded below
lemma l42p (nip : book_nip pp (V := V) (r := r)) (i : Fin r) : pp.δp ≤ nip.inp.p' i := by
    suffices pp.δp - pp.p₀ + pp.δ ≤ nip.inp.p' i - pp.p₀ + pp.δ by linarith
    trans  pp.δ * ((1 - 1 / ↑pp.t) ^ (nip.T i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (nip.Λs i)).prod)
    · ring_nf
      trans 1/4 * (1/4)
      sorry
      sorry -- no idea
    exact nip.l41 i

lemma pl1 (nip : book_nip pp (V := V) (r := r)) (i : Fin r) : pp.δp ≤ 1 :=
  le_trans (l42p nip i) (p'_le_one _ _)

lemma l42α (nip : book_nip pp (V := V) (r := r)) (i : Fin r) : pp.δ / (4 * pp.t) ≤ nip.inp.α i := by
    unfold key_in.α
    trans 1 / ↑pp.t * (pp.δ * ((1 - 1 / ↑pp.t) ^ (nip.T i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (nip.Λs i)).prod))
    · ring_nf; simp_rw [mul_assoc]; gcongr
      exact le_of_lt pp.δpos
      sorry -- no idea
    · gcongr
      exact nip.l41 i

-- "number of boost steps is bounded by a constant"
lemma l43 (nip : book_nip pp (V := V) (r := r)) (i : Fin r):
    nip.B i ≤ Nat.ceil (pp.t * (4 * Real.log (1 / pp.δ)) / pp.Λ₀) := by
  have posl (Λ : ℝ) (l : -1 ≤ Λ): 0 < (1 + Λ / pp.t) := sorry
  have pos : 0 < (1 + pp.Λ₀ / pp.t) := posl pp.Λ₀ pp.Λ₀ge
  let c := (nip.T i).card
  have : 1/4 * pp.δ * (1 + pp.Λ₀/pp.t) ^ (nip.B i) ≤ 1 + pp.δ := by
    trans pp.δ * (1 - 1 / (pp.t : ℝ)) ^ c * (1 + pp.Λ₀ / pp.t) ^ nip.B i
    · rw [mul_comm _ pp.δ]
      gcongr
      exact le_of_lt pp.δpos
      sorry -- no idea
    · trans nip.inp.p' i - pp.p₀ + pp.δ
      · trans pp.δ * (1 - 1 / ↑pp.t) ^ c * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (nip.Λs i)).prod
        gcongr pp.δ * (1 - 1 / ↑pp.t) ^ c * ?_
        apply mul_nonneg (le_of_lt pp.δpos) (pow_nonneg (tpos pp) _)
        · apply erm
          · intros _ a; refine le_of_lt (posl _ ?_); exact le_of_lt (lt_of_le_of_lt pp.Λ₀ge (nip.Λsge i _ a))
          · intros _ Λi; gcongr; exact le_of_lt (nip.Λsge i _ Λi)
        · rw [mul_assoc]; exact nip.l41 i
      · have : nip.inp.p' i ≤ 1 := by unfold key_in.p'; apply p_le_one
        have : nip.inp.p' i - pp.p₀ ≤ 1 := by trans nip.inp.p' i; exact sub_le_self (nip.inp.p' i) (p₀pos pp); exact this
        gcongr
  have : (1 + pp.Λ₀/pp.t) ^ (nip.B i : ℝ) ≤ (1 + pp.δ) * (1/4 * pp.δ)⁻¹ := sorry
  have := Real.le_log_of_rpow_le pos this
  simp at this
  sorry

-- card of Y is bounded below by something terrible
lemma l44color {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
  (ky : key_out nip.inp) (j : Fin r) (ghrm : x ∉ nip.T j)
  :
      let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i
      let newT (i : Fin r) := if i = j then insert x (nip.T i) else nip.T i
  ∀ (i : Fin r), pp.δp ^ ((newT i).card + nip.B i) * (pp.Y₀ i).card ≤ (newY i).card := by
    intro newY newT i
    unfold newY
    split -- did we color Y or no
    · expose_names
      rw [h]
      trans pp.δp ^ (((nip.T j).card) + 1 + nip.B j) * ↑(pp.Y₀ j).card
      · gcongr ?_ * ↑(pp.Y₀ j).card
        refine Real.pow_le_rpow_of_exponent_ge pp.pnn (pl1 nip i) ?_
        gcongr; simp [newT, h, card_union, ghrm]
      rw [ky.Y'card j]
      trans pp.δp * pp.δp ^ (nip.C j + nip.B j) * (pp.Y₀ j).card
      · gcongr ?_ * (pp.Y₀ j).card
        rw [show (nip.T j).card = nip.C j by rfl]
        exact le_of_eq (by ring)
      · trans pp.δp * (nip.inp.Y j).card
        · rw [mul_assoc]
          gcongr pp.δp * ?_; exact pp.pnn; exact nip.l44 j
        · gcongr; exact l42p nip j
    · expose_names
      trans pp.δp ^ ((nip.T i).card + nip.B i) * ↑(pp.Y₀ i).card
      · unfold newT; simp [h]
      trans pp.δp ^ ((nip.T i).card + (nip.Λs i).length) * ↑(pp.Y₀ i).card
      · gcongr ?_ * (pp.Y₀ i).card
        refine Real.pow_le_rpow_of_exponent_ge pp.pnn (pl1 nip i) (by rfl)
      · exact nip.l44 i

-- card of Y is bounded below by something terrible
lemma l44boost {pp : book_params} {nip : book_nip pp (V := V) (r := r)} {ky : key_out nip.inp} :
      let newY (i : Fin r) := if i = ky.l then ky.Y' i else nip.inp.Y i
      let newΛs (i : Fin r) := if i = ky.l then ky.Λ :: (nip.Λs i) else nip.Λs i
  ∀ (i : Fin r), pp.δp ^ ((nip.T i).card + (newΛs i).length) * (pp.Y₀ i).card ≤ (newY i).card := by
    intro newY newΛs i
    unfold newY newΛs
    split
    · rw [List.length]
      have (k : ℝ) (m n : ℕ) : k ^ (n + (m + 1)) = (k ^ (n + m) * k) := rfl
      rw [this]
      have (k s : ℝ) (m : ℕ) : s ^ m * s * k = s * (s ^ m * k) := by linarith
      rw [this]
      trans pp.δp * #(nip.inp.Y i)
      gcongr; exact pp.pnn; exact nip.l44 i
      rw [ky.Y'card i]
      gcongr
      exact l42p nip i
    · exact nip.l44 i

-- card of X is bounded below
lemma l45boost {pp : book_params} {nip : book_nip pp (V := V) (r := r)} {ky : key_out nip.inp} :
    let newΛs (i : Fin r) := if i = ky.l then ky.Λ :: (nip.Λs i) else nip.Λs i

    ∀ (i : Fin r), Xb pp newΛs nip.T i ≤ (lift ky.X').card := by
  intro newΛs i
  have εleβ : ε pp r ≤ β r := sorry
  have kc := ky.βcard
  have := nip.l45 i
  trans (β r * Real.exp (-C r * √(ky.Λ + 1))) / r * ↑nip.inp.X.card
  · trans ((#nip.inp.X) : ℝ)
    sorry

    sorry
  trans 1 / (r : ℝ) * (ky.X'.card : ℝ)
  · suffices 1 / (r : ℝ) * (β r * Real.exp (-C r * √(ky.Λ + 1)) * ↑nip.inp.X.card) ≤ 1 / (r : ℝ) * ↑ky.X'.card by sorry
    gcongr 1 / (r : ℝ) * ?_
  · simp [lift_card]
    trans 1 * (lift ky.X').card
    gcongr; exact Nat.cast_inv_le_one r
    simp

lemma l45color {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
    (ky : key_out nip.inp) (j : Fin r) (jn : j ≠ ky.l) :
    let X'' := N pp.χ j ky.x ∩ (lift ky.X')
    let newT (i : Fin r) := if i = j then insert ky.x (nip.T i) else nip.T i
    ∀ (i : Fin r), nip.Xbound newT i ≤ X''.card := by
  intro X'' newT i
  unfold X''
  have εleβ : ε pp r ≤ β r := sorry
  have := ky.βcard
  trans (β r * Real.exp (-C r * √(ky.Λ + 1))) / r * ↑nip.inp.X.card
  · sorry
  trans 1 / (r : ℝ) * (ky.X'.card : ℝ)
  · suffices 1 / (r : ℝ) * (β r * Real.exp (-C r * √(ky.Λ + 1)) * ↑nip.inp.X.card) ≤ 1 / (r : ℝ) * ↑ky.X'.card by sorry
    gcongr 1 / (r : ℝ) * ?_

  · simp [lift_card]
    trans 1 * (lift ky.X').card
    gcongr; exact Nat.cast_inv_le_one r
    simp
    sorry

lemma l41 {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
  (ky : key_out nip.inp) (j : Fin r) (Tne : ky.x ∉ nip.T j)
  :
    let X'' := if j = ky.l then lift ky.X' else N pp.χ j ky.x ∩ (lift ky.X')
    let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i
    let newT (i : Fin r) := if j = ky.l then nip.T i else (if i = j then insert ky.x (nip.T i) else nip.T i)
    let newΛs (i : Fin r) := if j = ky.l then (if i = j then ky.Λ :: (nip.Λs i) else nip.Λs i) else nip.Λs i
∀ (i : Fin r), pp.δ * ((1 - 1 / ↑pp.t) ^ (newT i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (newΛs i)).prod) ≤
    p (nenX := sorry) X'' (newY i) pp.χ i - pp.p₀ + pp.δ := by
  intro X'' newY newT newΛs i

  have X'sub : X'' ⊆ nip.inp.X := by
    unfold X''
    split
    exact (lift_subset ky.X')
    exact Subset.trans inter_subset_right (lift_subset ky.X')

  have nenX'' : Nonempty { x // x ∈ X'' } := sorry

  have pos : 0 ≤ 1 - 1 / (pp.t : ℝ) := tpos pp

  have grm : 0 ≤ 1 + ky.Λ / pp.t := sorry

  have grm2 (j : Fin r) (L : List ℝ) : 0 ≤ (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) L).prod := by
    apply List.prod_nonneg; intros a am;
    obtain ⟨b, ⟨bp, bpp⟩⟩ := List.mem_map.mp am
    trans 1 + b / (pp.t : ℝ)
    sorry -- is ok
    exact le_of_eq bpp

  unfold newT
  · by_cases h : i = j -- cases i = j vs i ≠ j
    · -- case i = j: this is the color we chose
      simp only [h]
      unfold X'' newY newΛs
      by_cases jn : j ≠ ky.l -- color or boost
      · -- color step
        simp only [jn, ↓reduceIte, ge_iff_le]
        trans nip.inp.p' j - nip.inp.α j - pp.p₀ + pp.δ
        · trans (1 - 1 / (pp.t : ℝ)) * (nip.inp.p' j - pp.p₀ + pp.δ)
          have thi (k : ℝ) (m : ℕ) : k ^ (m + 1) = (k ^ m * k) := rfl
          have tha (k s t : ℝ) (m : ℕ) : t * (s ^ m * s * k) = s * (t * (s ^ m * k)) := by ring
          rw [card_insert_of_notMem Tne, thi, tha]
          gcongr
          · exact nip.l41 j
          · unfold key_in.α; refine le_of_eq (by ring)
        · gcongr
          trans p (lift ky.X') (ky.Y' j) pp.χ j
          exact ky.g j jn
          have : Nonempty { x // x ∈ N pp.χ j ky.x ∩ lift ky.X' } := sorry
          exact p_subset inter_subset_right

      · -- boost step
        push_neg at jn
        simp only [jn, ↓reduceIte, ge_iff_le]
        trans nip.inp.p' ky.l + ky.Λ * nip.inp.α ky.l - pp.p₀ + pp.δ
        · trans (1 + ky.Λ / (pp.t : ℝ)) * (nip.inp.p' ky.l - pp.p₀ + pp.δ) -- color step
          have (k s t u : ℝ) : k * (t * (s * u)) = s * (k * (t * u)) := by linarith
          rw [List.map_cons, List.prod_cons, this]
          gcongr
          · exact nip.l41 ky.l
          · unfold key_in.α
            ring_nf
            exact le_of_eq rfl
        · gcongr; exact ky.f

    · -- case i ≠ j: nothing happened with this color
      have : nip.inp.Y i = newY i := by expose_names; simp [newY, h]
      trans nip.inp.p' i - pp.p₀ + pp.δ
      · unfold key_in.p'
        trans pp.δ * ((1 - 1 / (pp.t : ℝ)) ^ (nip.T i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (nip.Λs i)).prod)
        · gcongr pp.δ * ?_
          exact le_of_lt pp.δpos
          simp only [newΛs, ↓reduceIte, h]; split
          · exact le_of_eq rfl
          · exact le_of_eq rfl
        · convert nip.l41
          sorry
      · gcongr
        simp_rw [key_in.p', this]
        have : Nonempty { x // x ∈ nip.inp.X } := nip.inp.nenX
        exact p_subset X'sub

lemma l41color {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
  {ky : key_out nip.inp} (j : Fin r) (Tne : ky.x ∉ nip.T j) (jnn : j ≠ ky.l)
  :
    let X'' := N pp.χ j ky.x ∩ (lift ky.X')
    let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i
    let newT (i : Fin r) := if i = j then insert ky.x (nip.T i) else nip.T i
    let newΛs (i : Fin r) := nip.Λs i
∀ (i : Fin r), pp.δ * ((1 - 1 / ↑pp.t) ^ (newT i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (newΛs i)).prod) ≤
    p (nenX := sorry) X'' (newY i) pp.χ i - pp.p₀ + pp.δ := by
    have := l41 ky j Tne
    simp only [↓reduceIte, jnn] at this
    exact this

lemma l41boost {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
  {ky : key_out nip.inp} (Tne : ky.x ∉ nip.T ky.l)
  :
    let X'' := (lift ky.X')
    let newY (i : Fin r) := if i = ky.l then ky.Y' i else nip.inp.Y i
    let newΛs (i : Fin r) := if i = ky.l then ky.Λ :: (nip.Λs i) else nip.Λs i
∀ (i : Fin r), pp.δ * ((1 - 1 / ↑pp.t) ^ (nip.T i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (newΛs i)).prod) ≤
    p (nenX := sorry) X'' (newY i) pp.χ i - pp.p₀ + pp.δ := by
    have := l41 ky ky.l sorry
    simp only [↓reduceIte] at this
    exact this

lemma l46 {pp : book_params} {nip : book_nip pp (V := V) (r := r)} :
    ((nip.Λs i).map (λ Λ ↦ √(1 + Λ))).sum ≤ pp.t * 7 * r * Real.log (1 / pp.δ) / √pp.Λ₀ := sorry

-- TODO yamaan says this is ok issue #15
lemma pyposcolor  {pp : book_params} {nip : book_nip pp (V := V) (r := r)} {ky : key_out nip.inp} :
    let X'' := N pp.χ j ky.x ∩ (lift ky.X')
    let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i
    ∀ (i : Fin r), 0 < pY (nenX := sorry) X'' (newY i) pp.χ i := by
  sorry

-- TODO yamaan says this is ok issue #15
lemma pypos  {pp : book_params} {nip : book_nip pp (V := V) (r := r)} {ky : key_out nip.inp} :
    let X'' := lift ky.X'
    let newY (i : Fin r) := if i = ky.l then ky.Y' i else nip.inp.Y i
    ∀ (i : Fin r), 0 < pY (nenX := sorry) X'' (newY i) pp.χ i := by
  sorry

-- TODO issue #25
lemma choice_j {pp : book_params} {nip : book_nip pp (V := V) (r := r)} (ky : key_out nip.inp) :
    ∃ j, j ≠ ky.l ∧ (N pp.χ j ky.x ∩ (lift ky.X')).card ≤ (ky.X'.card - 1) / r := sorry -- issue #25


----------------------------------------------------------------------------------------------------
-- here comes the action

noncomputable def step {pp : book_params (V := V) (r := r)}
    (nip : book_nip pp (V := V) (r := r))
    (Tlt : ∀ i, (nip.T i).card < pp.t)
    : book_out pp (∑ i, (nip.T i).card) := by

  -- call the key lemma
  let ky := keynip nip.inp

  by_cases h : ky.Λ ≤ pp.Λ₀
  · -- color step!
    choose j jn jp using choice_j ky

    -- update the vertices we consider
    let X'' := N pp.χ j ky.x ∩ (lift ky.X')

    -- update the book fringe
    let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i

    have nenX'' : Nonempty { x // x ∈ X'' } := by
      refine (card_pos.mp ((Nat.cast_pos (α := ℝ)).mp ?_)).to_subtype
      exact lt_of_lt_of_le (Xbound_pos _ _ _) (l45color ky j jn j)

    let new_in : key_in pp := ⟨X'', newY, λ i ↦ pyposcolor _⟩

    -- update T: add x to book of color j
    have Tsub {i : Fin r} : ky.x ∉ nip.T i :=
      (nip.Tdisj i).notMem_of_mem_left_finset ky.xX

    let newT (i : Fin r) := if i = j then insert ky.x (nip.T i) else nip.T i

    have newTle (i : Fin r) : #(newT i) ≤ pp.t := by
      unfold newT; split
      · rw [card_insert_of_notMem Tsub]; exact Tlt i
      · exact nip.Tle i

    have Xsub (i : Fin r) : Disjoint X'' (newT i) := by
      have := disjoint_of_subset_left (lift_subset ky.X') (nip.Tdisj i)
      have : Disjoint (N pp.χ j ky.x ∩ lift ky.X') _ := disjoint_of_subset_left inter_subset_right this
      unfold X'' newT
      split
      · simp [disjoint_insert_right, N_not_mem, this]
      · exact this

    have inv : ∀ i, ∀ x ∈ newT i, ∀ y ∈ X'', y ∈ N pp.χ i x := by
      intros i x xT y yX
      have (h : x ∈ nip.T i) := nip.inv _ _ h _ (lift_subset ky.X' (mem_inter.mp yX).2)
      unfold newT at xT
      split at xT
      · cases mem_insert.mp xT
        · expose_names; rw [h_1, h_2]
          exact mem_of_mem_filter y yX
        · expose_names; exact this h_2
      · exact this xT


    have mono (i : Fin r) :  pp.χ.monochromaticBook i (newT i) (newY i) := by sorry
      -- have := nip.mbook i
      -- unfold SimpleGraph.EdgeColoring.monochromaticBook SimpleGraph.EdgeColoring.monochromatic newT newY
      -- unfold SimpleGraph.EdgeColoring.monochromaticBook SimpleGraph.EdgeColoring.monochromatic at this
      -- -- split
      -- · constructor
      --   · -- T and Y disjoint
      --     have : newY i ⊆ nip.inp.Y i := sorry
      --     sorry
      --   · constructor
      --     · -- T j-monochromatic
      --       intros x xT y yT xny
      --       -- simp at xny
      --       wlog h : x = ky.x generalizing
      --       · sorry -- exact this _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      --       · expose_names
      --         have : x ∈ X'' := by simp [h]; sorry
      --         have : x ∈ N pp.χ i y := inv i y yT x this
      --         unfold N at this
      --         have : y ∈ N pp.χ i x := (SimpleGraph.EdgeColoring.coloredNeighborFinset.symm i x y).mpr this
      --         unfold N at this
      --         have := ((pp.χ).color_coloredNeighborSet i x y).mp this
      --     · -- only j-mono edges between Y and T
      --       intros v vT w wT vnw
      --       wlog h : v = ky.x ∧ w ∈ (nip.T i) generalizing
      --       · sorry
      --       · --refine nip.xXmono i v ?_ w h.2 _
      --         sorry

      -- · exact nip.mbook i

    -- keep track of input for next iteration, state and inductive lemmata
    let newnip : book_nip pp := ⟨new_in,
      newT, newTle, Xsub, nip.Λs, nip.Λsge,
      l41color j Tsub jn, l44color ky j Tsub, l45color ky j jn, inv, mono⟩

    -- to ensure termination we also give a proof that T grew
    have Tcard : ∑ i, (nip.T i).card < ∑ i, (newnip.T i).card := by
      simp [newnip, newT, ← sum_erase_add (a := j), Tsub, sum_apply_ite_of_false]

    exact ⟨newnip, Tcard⟩

  · -- boost step!
    -- update our key sets
    let X'' := lift ky.X'
    let newY (i : Fin r) := if i = ky.l then ky.Y' i else nip.inp.Y i
    let new_in : key_in pp := ⟨X'', newY,  λ i ↦ pypos _⟩

    -- keep track of the Λs used for boost steps
    let newΛs (i : Fin r) := if i = ky.l then ky.Λ :: (nip.Λs i) else nip.Λs i
    have newΛslt (i : Fin r) : ∀ Λ ∈ newΛs i, pp.Λ₀ < Λ := by
      unfold newΛs; split
      · exact List.forall_mem_cons.mpr ⟨lt_of_not_ge h, nip.Λsge i⟩
      · exact nip.Λsge i

    have disjn := (λ i ↦ disjoint_of_subset_left (lift_subset ky.X') (nip.Tdisj i))

    let newnip : book_nip pp := ⟨new_in,
      nip.T, nip.Tle, disjn,
      newΛs, newΛslt,
      l41boost ((nip.Tdisj _).notMem_of_mem_left_finset ky.xX), l44boost, l45boost, sorry, sorry⟩

    exact step newnip Tlt

termination_by r * Nat.ceil (pp.t * (4 * Real.log (1 / pp.δ)) / pp.Λ₀) + 1 - nip.maxB
decreasing_by -- this uses boundedness of number of boost steps (l43)
  refine Nat.sub_lt_sub_left ?_ ?_
  · simp only [book_nip.maxB]
    -- here goes
    apply lt_of_lt_of_le (Order.lt_add_one_iff.mpr (sum_le_sum (λ i _ ↦ l43 nip i)))
    simp
  · simp [book_nip.maxB]
    apply sum_lt_sum
    intros i _; split <;> simp
    have (l : Fin r) (Λ : ℝ) (L : Fin r → List ℝ) : -- weird
        ∃ i ∈ univ, (L i).length < (if i = l then Λ :: L i else L i).length := by use l; simp
    apply this


noncomputable def book_params.m (pp : book_params (V := V) (r := r)) (j : Fin r) :=
  pp.δp ^ (pp.t + ⌈↑pp.t * (4 * Real.log (1 / pp.δ)) / pp.Λ₀⌉₊) * #(pp.Y₀ j)

noncomputable def stepper {pp : book_params (V := V) (r := r)} (nip : book_nip pp) :
    ∃ sn : book_nip pp, ∃ j, pp.t = #(sn.T j) ∧ pp.m j ≤ #(sn.inp.Y j) := by
  by_cases h : ∀ i, #(nip.T i) < pp.t
  · exact stepper (step nip h).nip
  · push_neg at h
    obtain ⟨j, jp⟩ := h
    have teqT := jp.antisymm (nip.Tle j)
    refine ⟨nip, j, ⟨teqT, ?_⟩⟩
    trans pp.δp ^ (#(nip.T j) + (nip.Λs j).length) * #(pp.Y₀ j)
    · rw [← teqT]
      unfold book_params.m
      gcongr ?_ * #(pp.Y₀ j)
      exact Real.pow_le_rpow_of_exponent_ge pp.pnn (pl1 nip j) (by gcongr; exact l43 nip j)
    · exact nip.l44 j

termination_by (r * pp.t) - nip.maxT
decreasing_by
  unfold book_nip.maxT
  apply Nat.sub_lt_sub_left
  refine Nat.lt_of_lt_of_le (m :=  ∑ _ : Fin r, pp.t) ?_ ?_
  gcongr with i
  · (expose_names; exact univ_nonempty_iff.mpr inst_3)
  · exact h i
  simp
  convert (step nip h).step_inc



theorem erdos_szekeres (m : ℕ) (μ p : ℝ) (μge : 2 ^ 10 * r ^ 3 ≤ μ):
  ∃ χ : (⊤ : SimpleGraph V).EdgeColoring (Fin r),
  ∃ (X : Finset V),
  ∃ (Y : Fin r → (Finset V)),
  ((μ ^ 2 / p) ^ (μ * r * t) < X.card) ∧
  ∀ i, (m * (Real.exp (2 ^ 13 * r ^ 3 / μ ^ 2)) ^ t < (Y i).card) ∧
  (∀ i, ∀ x ∈ X, (Y i) ⊆ (N χ i x) ∩ (Y i)) := sorry
