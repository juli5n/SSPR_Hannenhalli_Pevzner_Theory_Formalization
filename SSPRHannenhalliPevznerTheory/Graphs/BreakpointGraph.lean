import SSPRHannenhalliPevznerTheory.Basic
import SSPRHannenhalliPevznerTheory.Graphs.Basic
import SSPRHannenhalliPevznerTheory.DisjointCycles
import SSPRHannenhalliPevznerTheory.SignedPermutation.Basic


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

lemma deg_le_two {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ (vertex : Fin (n + 2)), (fromPermutation σ).blackEdgesGraph.degree vertex ≤ 2 := by sorry

lemma deg_black_eq_deg_gray {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ (vertex : Fin (n + 2)), (fromPermutation σ).blackEdgesGraph.degree vertex =
    (fromPermutation σ).grayEdgesGraph.degree vertex := by sorry



end BreakpointGraph

def num_breakpoints {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (BreakpointGraph.fromPermutation σ).blackEdgesGraph.edgeFinset.card

noncomputable def max_disjoint_cycles {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  maxDisjointCycleCount (BreakpointGraph.fromPermutation σ).fullGraph


scoped notation "b(" π ")" => num_breakpoints π
scoped notation "c(" π ")" => max_disjoint_cycles π

noncomputable def delta_max_disjoint_cycles {n : ℕ}
(π : Equiv.Perm (Fin n)) (ρ : Reversal (n := n)) : ℤ :=
  (max_disjoint_cycles (ρ • π) : ℤ) - (max_disjoint_cycles π : ℤ)

noncomputable def delta_num_breakpoints {n : ℕ}
(π : Equiv.Perm (Fin n)) (ρ : Reversal (n := n)) : ℤ :=
  (max_disjoint_cycles (ρ • π) : ℤ) - (max_disjoint_cycles π : ℤ)

scoped notation "Δb(" π ", " ρ ")" => delta_num_breakpoints π ρ
scoped notation "Δc(" π ", " ρ ")" => delta_max_disjoint_cycles π ρ

def Reversal.Proper {n : ℕ} (reversal : Reversal (n := n))
(π : Equiv.Perm (Fin n)) : Prop :=
  Δb(π,reversal) - Δc(π,reversal) = -1

end SSPRHannenhalliPevznerTheory
