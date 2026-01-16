import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Walks.Subwalks
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

namespace SSPRHannenhalliPevznerTheory

structure Cycle {n : ℕ} (graph : SimpleGraph (Fin n)) where
  baseNode : Fin n
  walk : graph.Walk baseNode baseNode
  is_cycle: walk.IsCycle

structure DisjointCycles {n : ℕ} (G : SimpleGraph (Fin n)) where
  Cycles : Finset (Cycle G)
  cycles_pairwise_disjoint :
    (SetLike.coe Cycles).PairwiseDisjoint (fun cycle ↦ cycle.walk.edgeSet)

namespace DisjointCycles

def empty {n : ℕ} (G : SimpleGraph (Fin n)) : DisjointCycles G :=
  {
    Cycles := {}
    cycles_pairwise_disjoint := by
      intro c₁ c₁_mem
      have := Finset.notMem_empty c₁ c₁_mem
      contradiction
  }

end DisjointCycles


open Classical in
theorem three_mul_card_cycles_le_card_edgeFinset {n : ℕ}
  {G : SimpleGraph (Fin n)} (disjoint_cycles : DisjointCycles G) :
  3 * disjoint_cycles.Cycles.card ≤ G.edgeFinset.card := by

  rw [mul_comm, ← smul_eq_mul]

  rw [← (Finset.sum_const 3)]

  let f := fun (cycle : Cycle G) ↦ cycle.walk.edgeSet.toFinset

  let disjoint_cycles_union := disjoint_cycles.Cycles.biUnion f

  have images_pairwise_disjoint : (SetLike.coe (disjoint_cycles.Cycles)).PairwiseDisjoint f := by
    unfold f
    unfold Set.PairwiseDisjoint
    intros c₁ c₁_mem c₂ c₂_mem c₁_neq_c₂
    simp only [Set.disjoint_toFinset]
    exact disjoint_cycles.cycles_pairwise_disjoint c₁_mem c₂_mem c₁_neq_c₂

  have h_card_union :
    disjoint_cycles_union.card =
    ∑ c ∈ disjoint_cycles.Cycles, c.walk.edgeSet.toFinset.card := by
    rw [Finset.card_biUnion images_pairwise_disjoint]

  calc
  G.edgeFinset.card ≥ disjoint_cycles_union.card := by
    apply Finset.card_le_card
    intro edge edge_in_union
    simp only [disjoint_cycles_union, f, Finset.mem_biUnion, Set.mem_toFinset] at edge_in_union
    obtain ⟨cycle, _, edge_in_edgeSet⟩ := edge_in_union
    rw [G.mem_edgeFinset]
    rw [SimpleGraph.Walk.mem_edgeSet] at edge_in_edgeSet
    exact cycle.walk.edges_subset_edgeSet edge_in_edgeSet

  _ = ∑ c ∈ disjoint_cycles.Cycles, c.walk.edgeSet.toFinset.card := h_card_union
  _ ≥ ∑ c ∈ disjoint_cycles.Cycles, 3 := by
    apply Finset.sum_le_sum
    intro cycle _

    have edgeSet_toFinset_eq_edges_toFinset :
      cycle.walk.edgeSet.toFinset = cycle.walk.edges.toFinset := by
      ext e
      simp only [Set.mem_toFinset, List.mem_toFinset]
      exact SimpleGraph.Walk.mem_edgeSet

    rw [
      edgeSet_toFinset_eq_edges_toFinset,
      List.toFinset_card_of_nodup cycle.is_cycle.isTrail.edges_nodup,
      cycle.walk.length_edges
    ]

    exact cycle.is_cycle.three_le_length




noncomputable def maxDisjointCycleCount
  {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by

  have exists_some_set_of_disjoint_cycles : ∃ (n : ℕ),
    ∃ (disjoint_cycles : DisjointCycles G), disjoint_cycles.Cycles.card = n := by sorry

  let possible_cycle_counts : Set ℕ :=
    { n | ∃ (disjoint_cycles : DisjointCycles G), disjoint_cycles.Cycles.card = n }


  open Classical in
  let elements_bounded :
    ∀ (n : possible_cycle_counts), n ≤ G.edgeFinset.card := by sorry

  have possible_cycle_counts_finite : possible_cycle_counts.Finite := by
    apply BddAbove.finite
    unfold BddAbove
    use G.edgeFinset.card
    unfold upperBounds
    rw [Set.mem_setOf_eq]
    intro n n_possible_cycle_count
    rw [Set.mem_setOf_eq] at n_possible_cycle_count
    obtain ⟨disjoint_cycles, _⟩ := n_possible_cycle_count
    have := three_mul_card_cycles_le_card_edgeFinset disjoint_cycles
    linarith

  have possible_cycle_counts_nonempty : possible_cycle_counts.Nonempty := by
    use 0
    rw [Set.mem_setOf_eq]
    use DisjointCycles.empty G
    unfold DisjointCycles.empty
    exact Finset.card_empty

  exact possible_cycle_counts_finite.toFinset.max' (by
    rw [Set.Finite.toFinset_nonempty]
    exact possible_cycle_counts_nonempty
  )

end SSPRHannenhalliPevznerTheory
