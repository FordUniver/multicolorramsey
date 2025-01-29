import Mathlib.Combinatorics.SimpleGraph.Basic

import Mathlib.Probability.Distributions.Uniform

open MeasureTheory ProbabilityTheory

namespace SimpleGraph

variable {V : Type α} (G : SimpleGraph V)

/-- An edge coloring maps each member of the graph's edge set to a colour in `C` --/
abbrev EdgeColoring (C : Type) := G.edgeSet → C

end SimpleGraph


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (n r : ℕ)

lemma moments (X : Type) [Fintype X] [Nonempty X] [MeasureSpace X]
    (U U' : Ω → X) (_ : IndepFun U U' P)
    (u : P.map U =  (PMF.uniformOfFintype X).toMeasure)
    (u' : P.map U' = (PMF.uniformOfFintype X).toMeasure)
    (σ : Fin r → (X → (Fin n → ℝ))) (l : Fin r → ℕ)
    (i : Fin r)
    : 0 ≤ 𝔼[ fun (x, x') => ∏ i, (dotProduct (σ i x) (σ i x')) ^ (l i) ] :=
  sorry
