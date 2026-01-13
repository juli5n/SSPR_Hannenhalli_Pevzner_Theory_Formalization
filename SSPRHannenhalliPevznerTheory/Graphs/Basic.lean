import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace SSPRHannenhalliPevznerTheory



structure TwoColoredGraph {n : ℕ} where
  blackEdgesGraph : SimpleGraph (Fin n)
  grayEdgesGraph : SimpleGraph (Fin n)

namespace TwoColoredGraph
def fullGraph {n : ℕ} (two_colored_graph : TwoColoredGraph (n := n))
  : SimpleGraph (Fin n) :=
  two_colored_graph.blackEdgesGraph ⊔ two_colored_graph.grayEdgesGraph

/-- A predicate that checks if two edges in a `TwoColoredGraph` have different colors. -/
def colorsDiffer {n : ℕ} (G : TwoColoredGraph (n := n)) (e₁ e₂ : Sym2 (Fin n)) : Prop :=
  (e₁ ∈ G.blackEdgesGraph.edgeSet ∧ e₂ ∈ G.grayEdgesGraph.edgeSet) ∨
  (e₁ ∈ G.grayEdgesGraph.edgeSet ∧ e₂ ∈ G.blackEdgesGraph.edgeSet)

/-- A walk is alternating if its sequence of edges forms a chain of differing colors. -/
def isAlternatingWalk {n : ℕ} {G : TwoColoredGraph (n := n)} {u v : Fin n}
    (p : G.fullGraph.Walk u v) : Prop :=
  List.IsChain (colorsDiffer G) p.edges

/- A walk is an alternating cycle if it is a cycle and an alternating walk. -/
def isAlternatingCycle {n : ℕ} {G : TwoColoredGraph (n := n)} {u : Fin n}
  (walk : G.fullGraph.Walk u u) : Prop :=
  walk.IsCycle ∧ isAlternatingWalk walk

def getGrayEdgesOfWalk {n : ℕ} {G : TwoColoredGraph (n := n)} {u v : Fin n}
  (walk : G.fullGraph.Walk u v)
  [DecidableRel G.grayEdgesGraph.Adj] :
    Finset (Sym2 (Fin n)) :=
  walk.edges.toFinset.filter (fun e => e ∈ G.grayEdgesGraph.edgeSet)

end TwoColoredGraph
end SSPRHannenhalliPevznerTheory
