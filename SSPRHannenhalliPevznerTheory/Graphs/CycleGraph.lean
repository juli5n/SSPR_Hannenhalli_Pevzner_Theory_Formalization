import SSPRHannenhalliPevznerTheory.Basic
import SSPRHannenhalliPevznerTheory.Graphs.Basic

namespace SSPRHannenhalliPevznerTheory.CycleGraph

def isPaired {n : ℕ} (x : Fin n) (y : Fin n) :=
  (¬ x = y) ∧ (x.val / 2 = y.val / 2)

def fromPermutationDirect {n : ℕ} (σ : Equiv.Perm (Fin n))
  : TwoColoredGraph (n := n) :=
  {
    blackEdgesGraph := {
      Adj (x : Fin n) (y : Fin n) := isPaired x y
      symm := by dsimp only [isPaired]; tauto
      loopless := by dsimp only [isPaired]; tauto
    }
    grayEdgesGraph := {
      Adj (x : Fin n) (y : Fin n) := isPaired (σ x) (σ y)
      symm := by dsimp only [isPaired]; tauto
      loopless := by dsimp only [isPaired]; tauto
    }
  }

def fromPermutation {n : ℕ} (σ : Equiv.Perm (Fin n))
  : TwoColoredGraph (n := n+2) :=
  fromPermutationDirect (addFrameToPermutation σ)

end SSPRHannenhalliPevznerTheory.CycleGraph
