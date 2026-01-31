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




def black_to_gray {n : ℕ} (σ : Equiv.Perm (Fin n)) (base : Fin (n + 2)) (i : Fin (n + 2))
    (_ : i ∈
      {w |
          (base.val = w.val + 1 ∨ w.val = base.val + 1) ∧
            ¬((addFrameToPermutation σ base).val = (addFrameToPermutation σ w).val + 1 ∨
                (addFrameToPermutation σ w).val = (addFrameToPermutation σ base).val + 1)
      }.toFinset) : Fin (n + 2) :=
  let σ' := addFrameToPermutation σ
  if i = base - 1
  then
    if base + 1 ≠ σ'.invFun ((σ' base) - 1)
    then σ'.invFun ((σ' base) - 1)
    else σ'.invFun ((σ' base) + 1)
  else
    if base - 1 ≠ σ'.invFun ((σ' base) + 1)
    then σ'.invFun ((σ' base) + 1)
    else σ'.invFun ((σ' base) - 1)

def gray_to_black {n : ℕ} (σ : Equiv.Perm (Fin n)) (base : Fin (n + 2)) (j : Fin (n + 2))
    (_ : j ∈
      {w |
          ((addFrameToPermutation σ base).val = (addFrameToPermutation σ w).val + 1 ∨
              (addFrameToPermutation σ w).val =
                (addFrameToPermutation σ base).val + 1) ∧
            ¬(base.val = w.val + 1 ∨ w.val = base.val + 1)
      }.toFinset) : Fin (n + 2) :=
  let σ' := addFrameToPermutation σ
  if j = σ'.invFun ((σ' base) - 1)
  then
    if base + 1 ≠ σ'.invFun ((σ' base) - 1)
    then base - 1
    else base + 1
  else
    if base - 1 ≠ σ'.invFun ((σ' base) + 1)
    then base + 1
    else base - 1

noncomputable def myPerm : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective
    ![2, 1, 0]  -- Die explizite Abbildung
    (by decide)

example : (fromPermutation myPerm).blackEdgesGraph.degree 4 =
    (fromPermutation myPerm).grayEdgesGraph.degree 4 := by
  unfold fromPermutation fromPermutationDirect
  dsimp
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  dsimp
  apply Finset.card_bij' (i := black_to_gray myPerm 4) (j := gray_to_black myPerm 4)
  · intro i i_black_adj
    simp only [not_or, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
      true_and] at i_black_adj
    unfold gray_to_black black_to_gray
    simp
    by_cases hi : i = 3
    · simp [hi]
      unfold myPerm addFrameToPermutation
      simp
    · simp [hi]
      unfold myPerm addFrameToPermutation
      simp
      have : ((4 : Fin 5) + 1 = 0) := by
        dsimp only [Fin.reduceAdd]

      sorry
  · sorry
  · sorry
  · sorry



/-a = (Equiv.symm (addFrameToPermutation σ)) ((addFrameToPermutation σ) b)
↔ ((addFrameToPermutation σ) a) = ((addFrameToPermutation σ) b)
↔ a = b
-/


--set_option pp.coercions false
lemma deg_black_eq_deg_gray {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ (base : Fin (n + 2)), (fromPermutation σ).blackEdgesGraph.degree base =
    (fromPermutation σ).grayEdgesGraph.degree base := by
  intro base
  unfold fromPermutation fromPermutationDirect
  dsimp
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  dsimp
  apply Finset.card_bij' (i := black_to_gray σ base) (j := gray_to_black σ base)
  · intro i i_black_adj
    simp only [not_or, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
      true_and] at i_black_adj
    unfold gray_to_black black_to_gray
    simp only [Equiv.invFun_as_coe, ne_eq, ite_not]
    obtain base_eq_succ_i | i_eq_succ_base := i_black_adj.1
    · have one_le_base : 1 ≤ base.val := by omega
      rw [Nat.Simproc.eq_add_le i.val one_le_base] at base_eq_succ_i
      rw [← Fin.val_sub_one_of_ne_zero ?_] at base_eq_succ_i
      · rw [Fin.val_inj] at base_eq_succ_i
        simp only [base_eq_succ_i, ↓reduceIte, ite_eq_right_iff, EmbeddingLike.apply_eq_iff_eq]
        by_cases succ_base_eq :
          base + 1 = (Equiv.symm (addFrameToPermutation σ)) ((addFrameToPermutation σ) base - 1)
        · simp only [succ_base_eq, forall_const, ↓reduceIte]
          by_cases base_last : base = ⟨n + 1, Nat.lt_add_one (n + 1)⟩
          · simp only [base_last]
            simp only [addFrameToPermutation.maps_last_last]
            simp only [addFrameToPermutation.commutes_with_inv]
            have pred_succ_n_eq_n : (⟨n + 1, Nat.lt_add_one (n + 1)⟩ : Fin (n + 2)) - 1 =
                ⟨n, by simp only [lt_add_iff_pos_right, Nat.ofNat_pos]⟩ := by
              rw [Fin.eq_mk_iff_val_eq]
              rw [Fin.val_sub_one_of_ne_zero (Ne.symm (not_eq_of_beq_eq_false rfl))]
              rfl
            rw [pred_succ_n_eq_n]
            have succ_succ_n_eq_0:
                (⟨ n + 1, Nat.lt_add_one (n + 1)⟩ : Fin (n + 2)) + 1 = 0 := by
              rw [Fin.eq_mk_iff_val_eq]

              rw [Fin.val_add ⟨n + 1, Nat.lt_add_one (n + 1)⟩ 1]
              norm_num
            rw [succ_succ_n_eq_0]

            by_cases n_eq_0 : (0 : Fin (n + 2)) = ⟨ n, by omega⟩
            · simp only [n_eq_0, ↓reduceIte]
              rw [← n_eq_0]
              exact addFrameToPermutation.maps_first_first (Equiv.symm σ)
            · simp only [Fin.zero_eq_mk] at n_eq_0
              rw [base_last, succ_succ_n_eq_0, Equiv.eq_symm_apply (addFrameToPermutation σ),
                ← Fin.mk_zero' (n + 2), addFrameToPermutation.maps_first_first σ,
                addFrameToPermutation.maps_last_last σ, pred_succ_n_eq_n, Fin.ext_iff
              ] at succ_base_eq
              dsimp at succ_base_eq
              exact False.elim (n_eq_0 succ_base_eq.symm)
          · set σ' := addFrameToPermutation σ with σ'_def
            by_cases n_eq_0 : 0 = n
            · have succ_eq_pred (x : Fin (n + 2)) : x + 1 = x - 1 := by
                rw [eq_sub_iff_add_eq]
                rw [add_assoc]
                norm_num
                rw [Fin.add_def 1 1]
                norm_num
                rw [← n_eq_0]
              simp only [succ_eq_pred (σ' base), ↓reduceIte]
              nth_rw 1 [Equiv.symm_apply_eq σ']
              have one_eq_succ_n : @OfNat.ofNat (Fin (n + 2)) 1 Fin.instOfNat =
                    ⟨n+1, Nat.lt_add_one (n + 1)⟩ := by
                rw [Fin.ext_iff]
                dsimp
                rw [← n_eq_0]
              by_cases base_eq_0 : base = 0
              · rw [base_eq_0]
                rw [σ'_def]
                nth_rw 1 [← Fin.mk_zero' (n + 2)]
                rw [addFrameToPermutation.maps_first_first σ]
                rw [← succ_eq_pred 0]
                norm_num
                have := addFrameToPermutation.maps_last_last σ

                rw [← one_eq_succ_n] at this
                rw [this]
                rw [← add_right_inj 0]
                rw [succ_eq_pred 0]
                norm_num
              · have base_eq_1 : base = 1 := by grind
                rw [base_eq_1]
                norm_num
                rw [σ'_def]
                rw [show (addFrameToPermutation σ) 0 = 0 from rfl]
                have := addFrameToPermutation.maps_last_last σ
                rw [← one_eq_succ_n] at this
                rw [this]
                norm_num
            · have succ_neq_pred (x : Fin (n + 2)) : ¬ (x + 1) = (x - 1) := by
                rw [eq_sub_iff_add_eq]
                rw [add_assoc]
                norm_num
                rw [show 1 + 1 = Fin.add 1 1 from rfl]
                unfold Fin.add
                norm_num
                rw [@Nat.succ_mod_succ_eq_zero_iff]
                norm_num
                exact fun a ↦ n_eq_0 (id (Eq.symm a))
              simp only [succ_neq_pred, ↓reduceIte, ite_eq_left_iff]
              intro pred_base_neq
              rw [Equiv.symm_apply_eq σ']
              rw [Equiv.eq_symm_apply σ'] at succ_base_eq pred_base_neq

              sorry
        · sorry
      · exact Ne.symm (Fin.ne_of_lt one_le_base)
    · sorry
  · sorry
  · sorry
  · sorry



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
