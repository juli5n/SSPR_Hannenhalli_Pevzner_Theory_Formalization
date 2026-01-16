import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.MinMax
import SSPRHannenhalliPevznerTheory.Graphs.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Interleaving Graph of Alternating Cycles

This file defines the interleaving graph of a two-colored graph using
the connected components as vertices. This is equivalent to using the
cycles in the breakpoint graph in the case of unsigned
permutations that represent signed permutation.
Edges exist between two vertices if the connected components contain gray edges that interleave.
-/

namespace SSPRHannenhalliPevznerTheory.InterleavingGraph

/-- Helper function to map an undirected edge
to an ordered pair (min, max). -/
def sym2ToInterval {n : ℕ} (edge : Sym2 (Fin n)) : Fin n × Fin n :=
  edge.lift ⟨fun u v => (min u v, max u v), by
    intro vertex₁ vertex₂
    dsimp only
    rw [min_comm, max_comm]⟩

/-- Two edges `e₁` and `e₂` interleave if their endpoints
are interlaced in the linear order of `Fin n`. -/
def edgesInterleave {n : ℕ} (edge₁ edge₂ : Sym2 (Fin n)) : Prop :=
  let (u₁, v₁) := sym2ToInterval edge₁
  let (u₂, v₂) := sym2ToInterval edge₂
  (u₁ < u₂ ∧ u₂ < v₁ ∧ v₁ < v₂) ∨ (u₂ < u₁ ∧ u₁ < v₂ ∧ v₂ < v₁)

/-- Interleaving relation on edges is commutative. -/
theorem edgesInterleave_comm {n : ℕ} (edge₁ edge₂ : Sym2 (Fin n)) :
    edgesInterleave edge₁ edge₂ ↔ edgesInterleave edge₂ edge₁ := by
  unfold edgesInterleave
  tauto

/-- What it means that an edge is gray and lies in a connected component. -/
def isGrayEdgeOfComponent {n : ℕ} (G : TwoColoredGraph (n := n))
    (component : G.fullGraph.ConnectedComponent) (edge : Sym2 (Fin n)) : Prop :=
  edge ∈ G.grayEdgesGraph.edgeSet ∧
  (edge : Set (Fin n)) ⊆ (component : Set (Fin n))

def ComponentsInterleave {n : ℕ} (G : TwoColoredGraph (n := n))
    (comp₁ comp₂ : G.fullGraph.ConnectedComponent) : Prop :=
  comp₁ ≠ comp₂ ∧
  ∃ edge₁ edge₂, isGrayEdgeOfComponent G comp₁ edge₁ ∧
           isGrayEdgeOfComponent G comp₂ edge₂ ∧
           edgesInterleave edge₁ edge₂

/--
The interleaving graph $H_G$ where nodes are alternating cycles.
Two cycles are adjacent if they are distinct and have at least one pair of
interleaving gray edges. We only consider the case of signed permutations represented by
unsigned permutations so this corresponds to the connected components
-/
def InterleavingGraphRepresented {n : ℕ} (G : TwoColoredGraph (n := n))
  [DecidableRel G.grayEdgesGraph.Adj] :
    SimpleGraph (G.fullGraph.ConnectedComponent) where
  Adj := ComponentsInterleave G
  symm := by
    intro comp₁ comp₂ comps_interleave
    rcases comps_interleave with
      ⟨comps_ne, edge₁, edge₂, edge₁_in_comp₁, edge₂_in_comp₂, edges_interleave⟩
    refine ⟨comps_ne.symm, edge₂, edge₁, edge₂_in_comp₂, edge₁_in_comp₁, ?_⟩
    rw [edgesInterleave_comm]
    exact edges_interleave

  loopless := by
    intro component interleave_itself
    exact interleave_itself.1 rfl

end SSPRHannenhalliPevznerTheory.InterleavingGraph
