import MulticolorRamsey.KeyLemma
import ExponentialRamsey.Prereq.Ramsey


import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

open Finset SimpleGraph

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



lemma reh (Y : Finset V) : Membership.mem Y.val = Y.toSet := by ext; simp only [mem_val]; exact Eq.to_iff rfl



----------------------------------------------------------------------------------------------------

variable {V : Type} {r : ℕ} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty (Fin r)]

----------------------------------------------------------------------------------------------------
-- parameters that don't change during book "algo"
structure book_params where
    (t : ℕ) (tpos : 0 < t)
    (Λ₀ : ℝ) (Λ₀ge : -1 ≤ Λ₀)
    (δ : ℝ) (δpos : 0 < δ)
    χ : TopEdgeLabelling V (Fin r)
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

lemma δppos (pp : book_params (V := V) (r := r)) : 0 ≤ pp.δp := by unfold book_params.δp; sorry


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
lemma εleβ (pp : book_params (V := V) (r := r)) (t : Nat) : ε pp r ≤ β r := by
    unfold ε; trans β r / 1 * 1; gcongr; simp
    · exact le_of_lt βpos
    · exact le_of_lt βpos
    · sorry
    · exact Real.exp_le_one_iff.mpr sorry
    · simp


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
  (rainbow : ∀ i, ∀ y ∈ T i, ∀ x ∈ inp.X, x ∈ N pp.χ i y) -- a nice invariant
  (mbook (i : Fin r) : pp.χ.MonochromaticBook i (T i) (inp.Y i)) -- the relevant bit

-- get input from params (for first call)
noncomputable def book_params.nip (pp : book_params (V := V) (r := r)) : book_nip pp := by
  exact ⟨⟨pp.X₀, pp.Y₀, pp.pYpos⟩,
   λ _ ↦ ∅, by simp, by simp,
   λ _ ↦ [], by simp, by simp [key_in.p', p₀le],
   by simp, by simp [Xb],
   by simp, by simp [TopEdgeLabelling.MonochromaticBook, TopEdgeLabelling.MonochromaticOf, TopEdgeLabelling.MonochromaticBetween]⟩

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

-- α is bounded below
lemma l42α (nip : book_nip pp (V := V) (r := r)) (i : Fin r) : pp.δ / (4 * pp.t) ≤ nip.inp.α i := by
    unfold key_in.α
    trans 1 / ↑pp.t * (pp.δ * ((1 - 1 / ↑pp.t) ^ (nip.T i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (nip.Λs i)).prod))
    · ring_nf; simp_rw [mul_assoc]; gcongr
      exact le_of_lt pp.δpos
      sorry -- no idea
    · gcongr
      exact nip.l41 i

-- the upper bound on the number of boost steps
noncomputable def book_params.B {pp : book_params (V := V) (r := r)} : ℕ :=
  ⌈↑pp.t * (4 * Real.log (1 / pp.δ)) / pp.Λ₀⌉₊

-- "number of boost steps is bounded by a constant"
lemma l43 (nip : book_nip pp (V := V) (r := r)) (i : Fin r):
    nip.B i ≤ pp.B := by
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

-- card of Y after color step is bounded below by something terrible
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

-- card of Y after boost step is bounded below by something terrible
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

-- card of X after boost step is bounded below
lemma l45boost {pp : book_params} {nip : book_nip pp (V := V) (r := r)} {ky : key_out nip.inp} :
    let newΛs (i : Fin r) := if i = ky.l then ky.Λ :: (nip.Λs i) else nip.Λs i

    ∀ (i : Fin r), Xb pp newΛs nip.T i ≤ (lift ky.X').card := by
  intro newΛs i
  have kc := ky.βcard
  have := nip.l45 i
  trans (β r * Real.exp (-C r * √(ky.Λ + 1))) / r * ↑nip.inp.X.card
  · trans ((#nip.inp.X) : ℝ)
    sorry

    trans 1 * (#nip.inp.X); simp; gcongr
    sorry

  trans 1 / (r : ℝ) * (ky.X'.card : ℝ)
  · suffices 1 / (r : ℝ) * (β r * Real.exp (-C r * √(ky.Λ + 1)) * ↑nip.inp.X.card) ≤ 1 / (r : ℝ) * ↑ky.X'.card by sorry
    gcongr 1 / (r : ℝ) * ?_
  · simp [lift_card]
    trans 1 * (lift ky.X').card
    gcongr; exact Nat.cast_inv_le_one r
    simp

-- card of X after color step is bounded below
lemma l45color {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
    (ky : key_out nip.inp) (j : Fin r) (jn : j ≠ ky.l) :
    let X'' := N pp.χ j ky.x ∩ (lift ky.X')
    let newT (i : Fin r) := if i = j then insert ky.x (nip.T i) else nip.T i
    ∀ (i : Fin r), nip.Xbound newT i ≤ X''.card := by
  intro X'' newT i
  unfold X''
  trans (β r * Real.exp (-C r * √(ky.Λ + 1))) / r * ↑nip.inp.X.card
  · sorry
  trans 1 / (r : ℝ) * (ky.X'.card : ℝ)
  · suffices 1 / (r : ℝ) * (β r * Real.exp (-C r * √(ky.Λ + 1)) * ↑nip.inp.X.card) ≤ 1 / (r : ℝ) * ↑ky.X'.card by sorry
    gcongr 1 / (r : ℝ) * ?_
    exact ky.βcard
  · simp [lift_card]
    trans 1 * (lift ky.X').card
    gcongr; exact Nat.cast_inv_le_one r
    simp
    sorry

lemma l41nothing {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
    (X'' : Finset V) [nenX'' : Nonempty { x // x ∈ X'' }] (X'sub : X'' ⊆ nip.inp.X) (i : Fin r) :
    pp.δ * ((1 - 1 / ↑pp.t) ^ (nip.T i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (nip.Λs i)).prod) ≤
    p X'' (nip.inp.Y i) pp.χ i - pp.p₀ + pp.δ := by
  trans nip.inp.p' i - pp.p₀ + pp.δ
  · exact nip.l41 i
  · gcongr
    exact p_subset X'sub

lemma l41color {pp : book_params} {nip : book_nip pp (V := V) (r := r)}
  {ky : key_out nip.inp} (j : Fin r) (Tne : ky.x ∉ nip.T j) (jnn : j ≠ ky.l) [Nonempty {x // x ∈ N pp.χ j ky.x ∩ (lift ky.X')}]:
    let X'' := N pp.χ j ky.x ∩ (lift ky.X')
    let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i
    let newT (i : Fin r) := if i = j then insert ky.x (nip.T i) else nip.T i
∀ (i : Fin r), pp.δ * ((1 - 1 / ↑pp.t) ^ (newT i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (nip.Λs i)).prod) ≤
    p X'' (newY i) pp.χ i - pp.p₀ + pp.δ := by
  intro X'' newY newT i

  have pos : 0 ≤ 1 - 1 / (pp.t : ℝ) := tpos pp

  unfold newT newY
  · by_cases h : i = j -- cases i = j vs i ≠ j
    · -- case i = j: this is the color we chose
      simp only [h]
      unfold X''
      simp only [↓reduceIte, ge_iff_le]
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
        exact ky.g j jnn
        exact p_subset inter_subset_right

    · simp only [h, ↓reduceIte, ite_self]
      exact l41nothing X'' (Subset.trans inter_subset_right (lift_subset ky.X')) i

lemma l41boost {pp : book_params} {nip : book_nip pp (V := V) (r := r)} {ky : key_out nip.inp} :
    let newY (i : Fin r) := if i = ky.l then ky.Y' i else nip.inp.Y i
    let newΛs (i : Fin r) := if i = ky.l then ky.Λ :: (nip.Λs i) else nip.Λs i
    ∀ (i : Fin r), pp.δ * ((1 - 1 / ↑pp.t) ^ (nip.T i).card * (List.map (fun Λ ↦ 1 + Λ / (pp.t : ℝ)) (newΛs i)).prod) ≤
    p (lift ky.X') (newY i) pp.χ i - pp.p₀ + pp.δ := by
  intro newY newΛs i

  have grm : 0 ≤ 1 + ky.Λ / pp.t := by
    suffices h : -1 ≤ ky.Λ / pp.t by linarith
    trans -1 / pp.t
    rw [neg_div, neg_le_neg_iff, div_le_one]
    norm_cast; exact le_trans NeZero.one_le pp.tge
    norm_cast; exact pp.tpos
    apply div_le_div_of_nonneg_right
    exact ky.Λge
    norm_cast; exact le_of_lt pp.tpos

  unfold newΛs newY
  · by_cases h : i = ky.l
    · -- case i = ky.l: this is the color we chose
      simp only [h, ↓reduceIte, ge_iff_le]
      trans nip.inp.p' ky.l + ky.Λ * nip.inp.α ky.l - pp.p₀ + pp.δ
      · trans (1 + ky.Λ / (pp.t : ℝ)) * (nip.inp.p' ky.l - pp.p₀ + pp.δ)
        have (k s t u : ℝ) : k * (t * (s * u)) = s * (k * (t * u)) := by linarith
        rw [List.map_cons, List.prod_cons, this]
        gcongr
        · exact nip.l41 ky.l
        · unfold key_in.α
          ring_nf
          exact le_of_eq rfl
      · gcongr; exact ky.f

    · simp only [h, ↓reduceIte, ite_self]
      exact l41nothing (lift ky.X') (lift_subset ky.X') i

lemma l46 {pp : book_params} {nip : book_nip pp (V := V) (r := r)} :
    ((nip.Λs i).map (λ Λ ↦ √(1 + Λ))).sum ≤ pp.t * 7 * r * Real.log (1 / pp.δ) / √pp.Λ₀ := sorry

----------------------------------------------------------------------------------------------------
-- correctness: the output T and Y always form a monochromatic book

lemma mau {pp : book_params (V := V) (r := r)} {nip : book_nip pp} {ky : key_out nip.inp} (i : Fin r) :
    Disjoint (nip.T i) (ky.Y' i) := by
  refine disjoint_coe.mp (Set.disjoint_of_subset_right (trans (ky.Y'sub i) inter_subset_right) ?_)
  exact disjoint_coe.mpr (nip.mbook i).1


lemma mono_boost  {pp : book_params (V := V) (r := r)} {nip : book_nip pp} {ky : key_out nip.inp} (i : Fin r) :
    let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i
    pp.χ.MonochromaticBook i (nip.T i) (newY i) := by
  apply pp.χ.monochromaticBook_subset (nip.mbook i)
  simp; split_ifs; exact (Subset.trans (ky.Y'sub i) inter_subset_right); simp


lemma mono  {pp : book_params} {nip : book_nip pp (V := V) (r := r)} {ky : key_out nip.inp} (i : Fin r) :
    let newY (i : Fin r) := if i = j then ky.Y' i else nip.inp.Y i
    let newT (i : Fin r) := if i = j then insert ky.x (nip.T i) else nip.T i
    pp.χ.MonochromaticBook i (newT i) (newY i) := by
  intros newY newT
  unfold newT newY
  split
  · repeat any_goals constructor
    · -- disjoint
      simp only [disjoint_insert_left]
      constructor
      · apply Set.notMem_subset ?_ (EdgeLabelling.coloredNeighborSet_not_mem (EC := pp.χ) i ky.x)
        convert (Subset.trans (ky.Y'sub i) inter_subset_left)
        simp only [reh, Set.subset_toFinset]
      · exact mau i
    · --newT monochromatic
      push_cast
      apply (pp.χ.monochromaticOf_monochromaticBetween_insert i ky.x (nip.T i)).mpr
      constructor
      · exact (nip.mbook i).2.1
      · refine pp.χ.monochromaticBetween_neighbors ?_
        convert λ y yy ↦ nip.rainbow i y yy ky.x ky.xX
        ext; simp
    · -- mono between newT and newY
      rw [insert_eq]
      apply TopEdgeLabelling.monochromaticBetween_union_left.mpr ⟨?_, ?_⟩
      · refine (pp.χ.monochromaticBetween_neighbors ?_).symm
        intros y yY
        rw [EdgeLabelling.coloredNeighborSet.symm]
        convert Finset.mem_of_subset (Subset.trans (ky.Y'sub i) inter_subset_left) yY
        ext; simp
      · exact (nip.mbook i).2.2.subset_right (Trans.trans (ky.Y'sub i) inter_subset_right)
  exact nip.mbook i

----------------------------------------------------------------------------------------------------
-- big holes in the "algo"

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
lemma choice_j {pp : book_params (V := V) (r := r)} {nip : book_nip pp} (ky : key_out nip.inp) :
    ∃ j, j ≠ ky.l ∧ (N pp.χ j ky.x ∩ (lift ky.X')).card ≤ (ky.X'.card - 1) / r := sorry -- issue #25

----------------------------------------------------------------------------------------------------
-- here comes the action

-- one good (color) step of the "algorithm". we recurse upon encountering a boost situation, and
-- return only after we did one color step. termination is guaranteed by lemma 4.3 (l43) which
-- bounds the number of boost steps.
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
      · simp [disjoint_insert_right, this, EdgeLabelling.coloredNeighborSet_not_mem]
      · exact this

    have rainbow : ∀ i, ∀ x ∈ newT i, ∀ y ∈ X'', y ∈ N pp.χ i x := by
      intros i x xT y yX
      have (h : x ∈ nip.T i) := nip.rainbow _ _ h _ (lift_subset ky.X' (mem_inter.mp yX).2)
      unfold newT at xT
      split at xT
      · cases mem_insert.mp xT
        · expose_names; rw [h_1, h_2]
          exact mem_of_mem_filter y yX
        · expose_names; exact this h_2
      · exact this xT

    -- keep track of input for next iteration, state and inductive lemmata
    let newnip : book_nip pp := ⟨new_in,
      newT, newTle, Xsub, nip.Λs, nip.Λsge,
      l41color j Tsub jn, l44color ky j Tsub, l45color ky j jn, rainbow, mono⟩

    -- to ensure termination we also give a proof that T grew
    have Tcard : ∑ i, (nip.T i).card < ∑ i, (newnip.T i).card := by
      simp [newnip, newT, ← sum_erase_add (a := j), Tsub, sum_apply_ite_of_false]

    exact ⟨newnip, Tcard⟩

  · -- boost step!
    -- update our key sets
    let newY (i : Fin r) := if i = ky.l then ky.Y' i else nip.inp.Y i
    let new_in : key_in pp := ⟨lift ky.X', newY,  λ i ↦ pypos _⟩

    -- keep track of the Λs used for boost steps
    let newΛs (i : Fin r) := if i = ky.l then ky.Λ :: (nip.Λs i) else nip.Λs i
    have newΛslt (i : Fin r) : ∀ Λ ∈ newΛs i, pp.Λ₀ < Λ := by
      unfold newΛs; split
      · exact List.forall_mem_cons.mpr ⟨lt_of_not_ge h, nip.Λsge i⟩
      · exact nip.Λsge i

    have disjn (i : Fin r) := disjoint_of_subset_left (lift_subset ky.X') (nip.Tdisj i)

    have rainbow (i : Fin r) : ∀ y ∈ nip.T i, ∀ x ∈ lift ky.X', x ∈ N pp.χ i y := by
      intros y yT x xX
      refine (nip.rainbow i y yT x) (Finset.mem_of_subset (lift_subset ky.X') xX)

    let newnip : book_nip pp := ⟨new_in,
      nip.T, nip.Tle, disjn,
      newΛs, newΛslt,
      l41boost, l44boost, l45boost, rainbow, mono_boost⟩

    exact step newnip Tlt

termination_by r * pp.B + 1 - nip.maxB
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


-- recurse and do another step unless one of the Ts has appropriate size. termination is guaranteed
-- since the output type of each step includes a proof that some T has grown in size.
noncomputable def stepper {pp : book_params (V := V) (r := r)} (nip : book_nip pp) :
    ∃ sn : book_nip pp, ∃ j, pp.t = #(sn.T j) ∧ pp.δp ^ (pp.t + pp.B) * #(pp.Y₀ j) ≤ #(sn.inp.Y j) := by
  by_cases h : ∀ i, #(nip.T i) < pp.t
  · exact stepper (step nip h).nip -- book not big enough yet. take another step
  · push_neg at h
    obtain ⟨j, jp⟩ := h
    have teqT := jp.antisymm (nip.Tle j)
    refine ⟨nip, j, ⟨teqT, ?_⟩⟩
    trans pp.δp ^ (#(nip.T j) + (nip.Λs j).length) * #(pp.Y₀ j)
    · rw [← teqT]
      gcongr ?_ * #(pp.Y₀ j)
      exact Real.pow_le_rpow_of_exponent_ge pp.pnn (pl1 nip j) (by gcongr; exact l43 nip j)
    · exact nip.l44 j

termination_by (r * pp.t) - nip.maxT
decreasing_by
  unfold book_nip.maxT
  apply Nat.sub_lt_sub_left
  refine Nat.lt_of_lt_of_le (m :=  ∑ _ : Fin r, pp.t) ?_ ?_
  gcongr with i
  · expose_names; exact univ_nonempty_iff.mpr inst_3
  · exact h i
  simp
  convert (step nip h).step_inc


-- thm 2.1
lemma book (t m : ℕ) (χ : TopEdgeLabelling V (Fin r))
  (tpos : 0 < t) (mpos : 0 < m)
  (X : Finset V) [nenX : Nonempty X]
  (Y : Fin r → (Finset V))
  (p : ℝ) (ppos : 0 < p)
  (μ : ℝ) (μge : 2^10 * r^3 ≤ μ)
  (tge : μ^5 / p ≤ t)
  (Ycard : ∀ i x, (p * ((Y i).card : ℝ) ≤ #((N χ i x) ∩ (Y i))))
  (Xge : (μ^2 / p)^(μ * r * t) ≤ #X)
  (Yge : ∀ i, (Real.exp (2^13 * r^3 / μ^2)) ^ t * m ≤ #(Y i))
  :
  ∃ c : Fin r, ∃ T M : Finset V, #T = t ∧ m ≤ #M ∧ χ.MonochromaticBook c T M := by
  let δ := p / μ^2
  have : 0 < r := Fin.pos'
  have : 0 < μ := lt_of_lt_of_le (by positivity) μge
  have δpos : 0 < δ := by simp [δ, ppos, sq_pos_of_pos this]
  let inp : book_params (V := V) (r := r) :=
    ⟨t, tpos,
     (μ * Real.log (1 / δ) / 8 * (C r))^2, le_trans (by simp) (sq_nonneg _),
     δ, δpos,
     χ, X, Y,
     sorry, -- issue #15
     sorry, sorry, sorry, sorry⟩

  -- run the "algorithm" and use its book
  obtain ⟨sn, ⟨j, ⟨a, b⟩⟩⟩ := stepper inp.nip

  use j
  use sn.T j
  use sn.inp.Y j
  refine ⟨a.symm, ⟨?_, sn.mbook j⟩⟩

  -- now we need to bound size of Y to prove our book has the required size
  have : 0 ≤ inp.δp := δppos inp
  apply (Nat.cast_le (α := ℝ)).mp
  trans Real.exp (-2 * δ * ↑t / p) * Real.exp (2 ^ 12 * ↑r ^ 3 / μ ^ 2) ^ (t : ℝ) * ↑m
  · apply le_mul_of_one_le_left (Nat.cast_nonneg' m)
    simp_rw [← Real.exp_mul, ← Real.exp_add]
    simp only [neg_mul, Real.one_le_exp_iff]
    sorry -- apparently follows from δ/p = 1/μ^2, as claimed on p12
  · trans Real.exp (-2 * δ * ↑t / p) * (p ^ inp.B * Real.exp (2 ^ 13 * ↑r ^ 3 / μ ^ 2) ^ (t : ℝ)) * ↑m
    · gcongr Real.exp (-2 * δ * ↑t / p) * ?_ * m
      trans Real.exp (-2 ^ 12 * ↑r ^ 3 / μ ^ 2) * Real.exp (2 ^ 13 * ↑r ^ 3 / μ ^ 2) ^ (t : ℝ)
      · sorry -- no idea but paper says so
      · gcongr
        sorry -- eq (16) somehow
    · trans inp.δp ^ (inp.t + inp.B) * ↑(#(inp.Y₀ j))
      · trans inp.δp ^ (inp.t + inp.B) * ((Real.exp (2^13 * r^3 / μ^2)) ^ t * m)
        · rw [show ∀ a b c d, a * (b * c) * d = (a * b) * (c * d) by sorry]
          gcongr
          sorry -- idk!
          norm_num
        · gcongr; exact Yge j
      · exact b
