import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks
import Mathlib.Combinatorics.SimpleGraph.Paths
import SSPRHannenhalliPevznerTheory.Graphs.Basic

/-!
# Interleaving Graph of Alternating Cycles

This file defines the interleaving graph of a two-colored graph, specifically for the
Hannenhalli-Pevzner theory. The nodes of this graph are alternating cycles, and edges
exist between cycles if their gray edges interleave.

## Main definitions

* `IsAlternatingWalk`: A predicate for walks with alternating edge colors.
* `AlternatingCycleVertex`: The type of vertices in the interleaving graph.
* `edgesInterleave`: Geometric interleaving of two edges based on their endpoints.
* `InterleavingGraph`: The resulting simple graph of cycles.
-/

namespace SSPRHannenhalliPevznerTheory.GeneralInterleaving

/-- A predicate that checks if two edges in a `TwoColoredGraph` have different colors. -/
def colorsDiffer {n : ℕ} (G : TwoColoredGraph (n := n)) (e₁ e₂ : Sym2 (Fin n)) : Prop :=
  (e₁ ∈ G.blackEdgesGraph.edgeSet ∧ e₂ ∈ G.grayEdgesGraph.edgeSet) ∨
  (e₁ ∈ G.grayEdgesGraph.edgeSet ∧ e₂ ∈ G.blackEdgesGraph.edgeSet)

/-- A walk is alternating if its sequence of edges forms a chain of differing colors. -/
def IsAlternatingWalk {n : ℕ} {G : TwoColoredGraph (n := n)} {u v : Fin n}
    (p : G.fullGraph.Walk u v) : Prop :=
  List.IsChain (colorsDiffer G) p.edges

/--
A vertex in the interleaving graph is an alternating cycle in the `fullGraph`.
Represented as a sigma type to allow the base vertex `u` to vary.
-/
abbrev AlternatingCycleVertex {n : ℕ} (G : TwoColoredGraph (n := n)) :=
  Σ (u : Fin n), {p : G.fullGraph.Walk u u // p.IsCycle ∧ IsAlternatingWalk p}

/-- Extract the set of gray edges from an alternating cycle. -/
def getGrayEdges {n : ℕ} {G : TwoColoredGraph (n := n)} (c : AlternatingCycleVertex G) :
    Finset (Sym2 (Fin n)) :=
  c.2.1.edges.toFinset.filter (fun e => e ∈ G.grayEdgesGraph.edgeSet)

/-- Helper function to map an undirected edge to an ordered pair (min, max).
  Uses `Sym2.lift` with a bundled symmetry proof to remain computable. -/
def sym2ToInterval {n : ℕ} (e : Sym2 (Fin n)) : Fin n × Fin n :=
  e.lift ⟨fun u v => (min u v, max u v), by
    intros u v
    dsimp
    rw [min_comm, max_comm]⟩

/-- Two edges `e₁` and `e₂` interleave if their endpoints are interlaced
in the linear order of `Fin n`.
-/
def edgesInterleave {n : ℕ} (e₁ e₂ : Sym2 (Fin n)) : Prop :=
  let (u₁, v₁) := sym2ToInterval e₁
  let (u₂, v₂) := sym2ToInterval e₂
  (u₁ < u₂ ∧ u₂ < v₁ ∧ v₁ < v₂) ∨ (u₂ < u₁ ∧ u₁ < v₂ ∧ v₂ < v₁)

/-- The geometric interleaving relation is symmetric. -/
theorem edgesInterleave_symm {n : ℕ} (e₁ e₂ : Sym2 (Fin n)) :
    edgesInterleave e₁ e₂ ↔ edgesInterleave e₂ e₁ := by
  unfold edgesInterleave
  tauto

/--
The interleaving graph $H_G$ where nodes are alternating cycles.
Two cycles are adjacent if they are distinct and have at least one pair of
interleaving gray edges.
-/
def InterleavingGraph {n : ℕ} (G : TwoColoredGraph (n := n)) :
    SimpleGraph (AlternatingCycleVertex G) where
  Adj cycle₁ cycle₂ :=
    let grayEdges₁ := getGrayEdges cycle₁
    let grayEdges₂ := getGrayEdges cycle₂
    (grayEdges₁ ≠ grayEdges₂) ∧
    (∃ e₁ ∈ grayEdges₁, ∃ e₂ ∈ grayEdges₂, edgesInterleave e₁ e₂)

  symm := by
    intros cycle₁ cycle₂ h
    rcases h with ⟨cycles_ne, grey₁, grey₁_in_cycle, grey₂, grey₂_in_cycle, interleave_1_and_2⟩
    refine ⟨cycles_ne.symm, grey₂, grey₂_in_cycle, grey₁, grey₁_in_cycle, ?_⟩
    rw [edgesInterleave_symm]
    exact interleave_1_and_2

  loopless := by
    intros cycle h
    exact h.1 rfl

end SSPRHannenhalliPevznerTheory.GeneralInterleaving
