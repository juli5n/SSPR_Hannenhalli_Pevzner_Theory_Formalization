import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.MinMax
import SSPRHannenhalliPevznerTheory.Graphs.Basic


namespace SSPRHannenhalliPevznerTheory.InterleavingGraph

open TwoColoredGraph


structure Vertex {n : ℕ} (G : TwoColoredGraph (n := n)) where
  baseNode : Fin n
  walk : G.fullGraph.Walk baseNode baseNode
  is_alternating_cycle : isAlternatingCycle walk
  base_node_is_support_min : ∀ v ∈ walk.support, baseNode ≤ v

/-
structure CycleVertex' {n : ℕ} (G : SimpleGraph (Fin n)) where
  baseNode : Fin n
  walk : G.Walk baseNode baseNode
  is_cycle: walk.IsCycle
  base_node_is_support_min : ∀ v ∈ walk.support, baseNode ≤ v

structure CycleVertex {n : ℕ} (G : SimpleGraph (Fin n)) where
  baseNode : Fin n
  property : ∃ (walk : G.Walk baseNode baseNode),
  walk.IsCycle ∧
  ∀ v ∈ walk.support, baseNode ≤ v
  -- walk : G.Walk baseNode baseNode
  -- is_cycle: walk.IsCycle
  -- base_node_is_support_min : ∀ v ∈ walk.support, baseNode ≤ v
-/

namespace Vertex

def getGrayEdges {n : ℕ} {G : TwoColoredGraph (n := n)}
  (vertex : Vertex G)
  [DecidableRel G.grayEdgesGraph.Adj] :
    Finset (Sym2 (Fin n)) :=
  vertex.walk.edges.toFinset.filter (fun e => e ∈ G.grayEdgesGraph.edgeSet)

end Vertex


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


/--
The interleaving graph $H_G$ where nodes are alternating cycles.
Two cycles are adjacent if they are distinct and have at least one pair of
interleaving gray edges.
-/
def InterleavingGraph {n : ℕ} (G : TwoColoredGraph (n := n))
  [DecidableRel G.grayEdgesGraph.Adj] :
    SimpleGraph (Vertex G) where
  Adj Vertex₁ Vertex₂ :=
    let grayEdges₁ := Vertex₁.getGrayEdges
    let grayEdges₂ := Vertex₂.getGrayEdges

    (Vertex₁.getGrayEdges ≠ Vertex₂.getGrayEdges) ∧
    (∃ e₁ ∈ Vertex₁.getGrayEdges, ∃ e₂ ∈ Vertex₂.getGrayEdges, edgesInterleave e₁ e₂)

  symm := by
    intros cycle₁ cycle₂ h
    rcases h with ⟨cycles_ne, grey₁, grey₁_in_cycle, grey₂, grey₂_in_cycle, interleave_1_and_2⟩
    refine ⟨cycles_ne.symm, grey₂, grey₂_in_cycle, grey₁, grey₁_in_cycle, ?_⟩
    rw [edgesInterleave_comm]
    exact interleave_1_and_2

  loopless := by
    intros cycle h
    exact h.1 rfl

end SSPRHannenhalliPevznerTheory.InterleavingGraph
