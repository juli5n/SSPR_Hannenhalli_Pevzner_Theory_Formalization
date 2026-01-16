import SSPRHannenhalliPevznerTheory.Basic
import SSPRHannenhalliPevznerTheory.Graphs.Basic
import SSPRHannenhalliPevznerTheory.DisjointCycles


namespace SSPRHannenhalliPevznerTheory

namespace BreakpointGraph



def fromPermutationDirect {n : ℕ} (σ : Equiv.Perm (Fin n)) : TwoColoredGraph (n := n) :=
  {
    blackEdgesGraph := {
      Adj (x : Fin n) (y : Fin n) :=
        (isConsecutive x y) ∧ (¬ isConsecutive (σ x) (σ y))
      symm := by dsimp only [isConsecutive]; tauto
      loopless := by dsimp only [Irreflexive, isConsecutive]; omega
    }
    grayEdgesGraph := {
      Adj (x : Fin n) (y : Fin n) :=
        (isConsecutive (σ x) (σ y)) ∧ (¬ isConsecutive x y)
      symm := by dsimp only [isConsecutive]; tauto
      loopless := by dsimp only [Irreflexive, isConsecutive]; omega
    }
  }

def fromPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : TwoColoredGraph (n := n+2) :=
  fromPermutationDirect (addFrameToPermutation σ)

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) :
  DecidableRel (fromPermutation σ).blackEdgesGraph.Adj := by
  intro x y
  dsimp only [fromPermutationDirect, fromPermutation, isConsecutive.eq_1]
  exact instDecidableAnd

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) :
  DecidableRel (fromPermutation σ).grayEdgesGraph.Adj := by
  intro x y
  dsimp only [fromPermutationDirect, fromPermutation, isConsecutive.eq_1]
  exact instDecidableAnd


end BreakpointGraph

def num_breakpoints {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (BreakpointGraph.fromPermutation σ).blackEdgesGraph.edgeFinset.card

noncomputable def max_disjoint_cycles {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  maxDisjointCycleCount (BreakpointGraph.fromPermutation σ).fullGraph


scoped notation "b(" π ")" => num_breakpoints π
scoped notation "c(" π ")" => max_disjoint_cycles π

end SSPRHannenhalliPevznerTheory
