import Mathlib.Combinatorics.SimpleGraph.Basic


namespace SSPRHannenhalliPevznerTheory



structure TwoColoredGraph {n : ℕ} where
  blackEdgesGraph : SimpleGraph (Fin n)
  grayEdgesGraph : SimpleGraph (Fin n)

def TwoColoredGraph.fullGraph {n : ℕ} (two_colored_graph : TwoColoredGraph (n := n))
  : SimpleGraph (Fin n) :=
  two_colored_graph.blackEdgesGraph ⊔ two_colored_graph.grayEdgesGraph

end SSPRHannenhalliPevznerTheory
