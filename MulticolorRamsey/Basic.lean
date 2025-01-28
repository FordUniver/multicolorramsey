import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

variable {V : Type α} (G : SimpleGraph V)

/-- An edge coloring maps each member of the graph's edge set to a colour in `C` --/
abbrev EdgeColoring (C : Type) := G.edgeSet → C

end SimpleGraph
