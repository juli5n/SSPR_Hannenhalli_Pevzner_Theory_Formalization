import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.MinMax
import SSPRHannenhalliPevznerTheory.Graphs.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Interleaving Graph of Alternating Cycles

This file defines the interleaving graph of a two-colored graph, specifically for the
Hannenhalli-Pevzner theory. The nodes of this graph are alternating cycles, and edges
exist between cycles if their gray edges interleave.

-/

namespace SSPRHannenhalliPevznerTheory.InterleavingGraph

/-- Helper function to map an undirected edge
to an ordered pair (min, max). -/
def sym2ToInterval {n : ℕ} (e : Sym2 (Fin n)) : Fin n × Fin n :=
  e.lift ⟨fun u v => (min u v, max u v), by
    intros u v
    dsimp only
    rw [min_comm, max_comm]⟩

/-- Two edges `e₁` and `e₂` interleave if their endpoints
are interlaced in the linear order of `Fin n`. -/
def edgesInterleave {n : ℕ} (e₁ e₂ : Sym2 (Fin n)) : Prop :=
  let (u₁, v₁) := sym2ToInterval e₁
  let (u₂, v₂) := sym2ToInterval e₂
  (u₁ < u₂ ∧ u₂ < v₁ ∧ v₁ < v₂) ∨ (u₂ < u₁ ∧ u₁ < v₂ ∧ v₂ < v₁)

/-- The geometric interleaving relation is commutative. -/
theorem edgesInterleave_comm {n : ℕ} (e₁ e₂ : Sym2 (Fin n)) :
    edgesInterleave e₁ e₂ ↔ edgesInterleave e₂ e₁ := by
  unfold edgesInterleave
  tauto

namespace edgesInterleave

theorem comm {n : ℕ} {e₁ e₂ : Sym2 (Fin n)} (h : edgesInterleave e₁ e₂) :
  edgesInterleave e₂ e₁ := by
  exact (edgesInterleave_comm e₁ e₂).mp h

end edgesInterleave

def isGrayEdgeOfComponent {n : ℕ} (G : TwoColoredGraph (n := n))
    (component : G.fullGraph.ConnectedComponent) (edge : Sym2 (Fin n)) : Prop :=
  edge ∈ G.grayEdgesGraph.edgeSet ∧
  (edge : Set (Fin n)) ⊆ (component : Set (Fin n))

def ComponentsInterleave {n : ℕ} (G : TwoColoredGraph (n := n))
    (c₁ c₂ : G.fullGraph.ConnectedComponent) : Prop :=
  c₁ ≠ c₂ ∧
  ∃ e₁ e₂, isGrayEdgeOfComponent G c₁ e₁ ∧
           isGrayEdgeOfComponent G c₂ e₂ ∧
           edgesInterleave e₁ e₂

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
    intro component₁ component₂ components_interleave
    rcases components_interleave with
      ⟨components_ne, edge₁, edge₂, edge₁_in_component₁, edge₂_in_component₂, edges_interleave⟩
    refine ⟨components_ne.symm, edge₂, edge₁, edge₂_in_component₂, edge₁_in_component₁, ?_⟩
    apply edgesInterleave.comm
    exact edges_interleave

  loopless := by
    intros component interleave_itself
    exact interleave_itself.1 rfl

end SSPRHannenhalliPevznerTheory.InterleavingGraph
