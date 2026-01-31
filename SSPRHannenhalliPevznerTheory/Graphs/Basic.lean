import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Linarith
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

def addFrameToPermutation {n : ℕ} (permutation : Equiv.Perm (Fin n)) :
  Equiv.Perm (Fin (n+2)) :=
  {
    toFun :=
      fun (x : (Fin (n + 2))) ↦
        if h : (x.val = 0 ∨ x.val = (n + 1)) then
          x
        else
          ⟨permutation  ⟨x-1, by
            rw [not_or] at h
            obtain ⟨h1, h2⟩ := h
            omega
          ⟩ + 1, by omega⟩
    invFun :=
      fun (x : (Fin (n + 2))) ↦
        if h : (x.val = 0 ∨ x.val = (n + 1)) then
          x
        else
          ⟨permutation.symm  ⟨x-1, by
            rw [not_or] at h
            obtain ⟨h1, h2⟩ := h
            omega
          ⟩ + 1, by omega⟩
    left_inv := by
      intro x
      apply Fin.eq_of_val_eq
      simp only
      split_ifs with if1_case if2_case
      · rfl
      · · cases if2_case with
          | inl if2_case_a =>
            simp only at if2_case_a
            linarith
          | inr if2_case_b =>
            simp only at if2_case_b
            omega
      · simp_rw [Nat.add_one_sub_one]
        rw [Equiv.symm_apply_apply]
        simp only
        omega
    right_inv := by
      intro x
      apply Fin.eq_of_val_eq
      simp only
      split_ifs with if1_case if2_case
      · rfl
      · · cases if2_case with
          | inl if2_case_a =>
            simp only at if2_case_a
            linarith
          | inr if2_case_b =>
            simp only at if2_case_b
            omega
      · simp only
        simp_rw [Nat.add_one_sub_one]
        rw [Equiv.apply_symm_apply]
        simp only
        omega
  }

namespace addFrameToPermutation

lemma maps_inner_inner {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : Fin (n + 2)}
    (i_inner : 1 ≤ i ∧ i ≤ n) :
    1 ≤ (addFrameToPermutation σ i) ∧ (addFrameToPermutation σ i) ≤ n := by
  sorry

lemma maps_last_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (addFrameToPermutation σ ⟨n + 1, Nat.lt_add_one (n + 1)⟩) = ⟨n + 1, Nat.lt_add_one (n + 1)⟩ := by
  sorry

lemma maps_first_first {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (addFrameToPermutation σ ⟨0, Nat.zero_lt_succ (n + 1)⟩) = ⟨0, Nat.zero_lt_succ (n + 1)⟩ := by
  sorry

lemma commutes_with_inv {n : ℕ} {σ : Equiv.Perm (Fin n)} :
    Equiv.symm (addFrameToPermutation σ) = addFrameToPermutation (Equiv.symm σ) := by
  sorry

end addFrameToPermutation

end SSPRHannenhalliPevznerTheory
