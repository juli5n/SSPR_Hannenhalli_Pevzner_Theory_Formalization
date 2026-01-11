import SSPRHannenhalliPevznerTheory.Basic
import SSPRHannenhalliPevznerTheory.Graphs.Basic

namespace SSPRHannenhalliPevznerTheory

namespace BreakpointGraph



def fromPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : TwoColoredGraph (n := n) :=
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
    decidableBlack := by
      intro x y
      dsimp
      exact instDecidableAnd
    decidableGray := by
      intro x y
      dsimp
      exact instDecidableAnd
  }



end BreakpointGraph
end SSPRHannenhalliPevznerTheory
