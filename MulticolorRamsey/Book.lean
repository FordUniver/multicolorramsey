import MulticolorRamsey.BookPrereq
import ExponentialRamsey.Prereq.Ramsey


import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

open Finset SimpleGraph

variable {V : Type} {r : ℕ} [Fintype V] [DecidableEq V] [Nonempty V] [Nonempty (Fin r)]
variable {param : BookParams V r} {bin : BookIn param} {kout : KeyOut bin.toKeyIn}


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
    let Y' (i : Fin r) := if i = j then kout.Y i else bin.Y i
    let newT (i : Fin r) := if i = j then insert kout.x (bin.T i) else bin.T i
    param.χ.MonochromaticBook i (newT i) (Y' i) := by
  intros Y' newT
  unfold newT Y'
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
    · -- mono between newT and Y'
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
    let Y' (i : Fin r) := if i = j then kout.Y i else bin.Y i
    ∀ (i : Fin r), 0 < (Saga.mk (χ := param.χ) X' Y').pY i := by
  sorry

-- TODO yamaan says this is ok issue #15
lemma pypos :
    let X' := kout.X
    let Y' (i : Fin r) := if i = kout.l then kout.Y i else bin.Y i
    ∀ {i : Fin r}, 0 < (Saga.mk X' Y').pY (χ := χ) i := by
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

    have nenX' : X'.Nonempty:= by
      refine card_pos.mp ((Nat.cast_pos (α := ℝ)).mp ?_)
      exact lt_of_lt_of_le Xbound_pos (l45color kout j jn j)

    -- update the book fringe
    let Y' (i : Fin r) := if i = j then kout.Y i else bin.Y i

    have {i : Fin r} : param.s.p i ≤ p'p param.χ X' Y' i := by
      apply le_trans bin.mono
      apply le_trans <| p_mono_x _ (inter_subset_right.trans kout.X'sub) nenX' _ i
      apply le_trans (p_mono_y _ _ Y' _ i) le_rfl
      intros k
      convert ite_subset_union _ _ _
      apply (union_eq_right.mpr _).symm
      exact subset_trans (kout.Y'sub k) (inter_subset_right.trans subset_rfl)

    let new_in : KeyIn param := ⟨⟨X', Y'⟩, fun _ => pyposcolor _, this⟩

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

    -- keep track of input for next iteration, state and inductive lemmata
    let newbi : BookIn param := ⟨new_in,
      newT, newTle, Xsub, bin.Λs, bin.Λsge,
      l41color j Tsub jn nenX', l44color kout j Tsub, l45color kout j jn, rainbow, mono⟩

    -- to ensure termination we also give a proof that T grew
    have Tcard : ∑ i, (bin.T i).card < ∑ i, (newbi.T i).card := by
      simp [newbi, newT, ← sum_erase_add (a := j), Tsub, sum_apply_ite_of_false]

    exact ⟨newbi, Tcard⟩

  · -- boost step!
    have {i : Fin r} : param.s.p i ≤ p'p param.χ kout.X (newYb kout) i := by
      apply le_trans bin.mono
      apply le_trans (p_mono_x (χ := param.χ) kout.X'sub kout.nen bin.Y i)
      apply le_trans le_rfl (p_mono_y param.χ bin.Y (newYb kout) _ i)
      intro k
      convert ite_subset_union _ _ _
      apply (union_eq_right.mpr _).symm
      exact subset_trans (kout.Y'sub k) (inter_subset_right.trans subset_rfl)

    -- update our key sets
    let new_in : KeyIn param := ⟨⟨kout.X, newYb kout⟩,  fun _ => pypos, this⟩

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
    apply lt_of_lt_of_le (Order.lt_add_one_iff.mpr (sum_le_sum (fun i _ => l43 bin i)))
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
  (X : Finset V) -- [nenX : Nonempty X]
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
