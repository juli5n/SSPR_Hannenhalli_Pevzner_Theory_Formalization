import SSPRHannenhalliPevznerTheory.Basic
import SSPRHannenhalliPevznerTheory.Graphs.Basic
import SSPRHannenhalliPevznerTheory.DisjointCycles
import SSPRHannenhalliPevznerTheory.SignedPermutation.Basic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix


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
    ∀ (vertex : Fin (n + 2)), (fromPermutation σ).blackEdgesGraph.degree vertex ≤ 2 := by
  intro vertex
  unfold fromPermutation fromPermutationDirect
  dsimp
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  dsimp
  have : {w | (vertex.val = w.val + 1 ∨ w.val = vertex.val + 1) ∧
      ¬(((addFrameToPermutation σ) vertex).val = ((addFrameToPermutation σ) w).val + 1 ∨
      ((addFrameToPermutation σ) w).val = ((addFrameToPermutation σ) vertex).val + 1)} ⊆
      {w | (vertex.val = w.val + 1 ∨ w.val = vertex.val + 1)} := by
    simp only [not_or, Set.setOf_subset_setOf, and_imp]
    exact fun a a_1 a_2 a_3 ↦ a_1
  have := Set.toFinset_mono this
  grw [this]
  simp only [Set.toFinset_setOf, ge_iff_le]
  rw [Finset.filter_or]
  grw [Finset.card_union_le]
  simp_rw [show (2 : ℕ) = 1 + 1 from rfl]
  gcongr
  · rw [Finset.card_le_one_iff_subset_singleton]
    use vertex - 1
    rw [Finset.subset_singleton_iff']
    intro x x_elem
    rw [Finset.mem_filter_univ x] at x_elem
    by_cases one_le_vertex : 1 ≤ vertex.val
    · rw [Nat.Simproc.eq_add_le ↑x one_le_vertex] at x_elem
      rw [Fin.ext_iff]
      rw [Fin.val_sub_one_of_ne_zero ?_]
      · exact x_elem
      · rw [Fin.ne_iff_vne]
        exact Ne.symm (Nat.ne_of_lt one_le_vertex)
    · rw [Nat.not_le,Nat.lt_one_iff] at one_le_vertex
      have : vertex = 0 := Fin.eq_of_val_eq one_le_vertex
      rw [this]
      simp only [zero_sub]
      omega
  · rw [Finset.card_le_one_iff_subset_singleton]
    by_cases vertex_last : vertex = Fin.last (n + 1)
    · rw [← Fin.natCast_eq_last (n + 1)] at vertex_last
      rw [Fin.ext_iff] at vertex_last
      rw [vertex_last]
      use 0
      rw [Finset.subset_singleton_iff']
      intro x x_elem
      rw [Finset.mem_filter_univ x] at x_elem
      rw [Fin.val_cast_of_lt (Nat.lt_add_one (n + 1))] at x_elem
      have : x.val < n + 1 + 1 := x.isLt
      exact False.elim ((Nat.ne_of_lt this) x_elem)
    · use vertex + 1
      rw [Finset.subset_singleton_iff']
      intro x x_elem
      rw [Finset.mem_filter_univ x] at x_elem
      apply Fin.eq_of_val_eq
      rw[x_elem]
      rw [Fin.val_add_one]
      simp only [vertex_last, ↓reduceIte]

lemma add_frame_map_inner_inner {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : Fin (n + 2)}
    (i_inner : 0 < i ∧ i < n + 1) :
    0 < (addFrameToPermutation σ i) ∧ (addFrameToPermutation σ i) < n + 1 := by
  sorry

lemma deg_black_eq_deg_gray {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ (vertex : Fin (n + 2)), (fromPermutation σ).blackEdgesGraph.degree vertex =
    (fromPermutation σ).grayEdgesGraph.degree vertex := by
  intro vertex
  unfold fromPermutation fromPermutationDirect
  dsimp
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  --apply Finset.card_bijective

  sorry



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
