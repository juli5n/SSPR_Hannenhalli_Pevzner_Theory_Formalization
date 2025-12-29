import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.IntervalCases
-- set_option pp.coercions false
-- set_option pp.all true

namespace SSPRHannenhalliPevznerTheory.Basic

inductive Sign
  | positive
  | negative
deriving DecidableEq, Repr

def Sign.toZ (s : Sign) : ℤ :=
  match s with
  | positive => 1
  | negative => -1

def Sign.toZeroOne (s : Sign) : Nat :=
  match s with
  | positive => 1
  | negative => 0


def Sign.flip (s : Sign) : Sign :=
  match s with
  | positive => negative
  | negative => positive


abbrev SignFunction (n : ℕ) := Fin n → Sign


instance : Inhabited Sign where
  default := Sign.positive

structure SignedPermutation (n : ℕ) where
  values : Equiv.Perm (Fin n)
  signs : SignFunction n

structure Reversal {n : ℕ} where
  start_index : Fin n
  end_index : Fin n
  start_index_le_end_index : start_index ≤ end_index


def Reversal.permutationFunction {n : ℕ} (reversal : Reversal (n := n)) (i : Fin n) : Fin n :=
  if index_within_reversal_segment : reversal.start_index ≤ i ∧ i ≤ reversal.end_index then
    ({
      val := reversal.end_index - (i  - reversal.start_index)
      isLt := by omega
    } : Fin n)
  else
    i


def Reversal.permutation {n : ℕ} (reversal : Reversal (n := n)) : (Equiv.Perm (Fin n)) :=
  ({
    toFun := reversal.permutationFunction
    invFun := reversal.permutationFunction
    left_inv := by
      dsimp [Function.LeftInverse]
      intro x
      simp only [permutationFunction]
      split_ifs with if_split_1 if_split_2
      <;> apply Fin.eq_of_val_eq
      <;> dsimp only [Fin.val, Fin.le_def] at *
      · omega
      · simp only [Fin.le_def] at if_split_2
        omega
    right_inv := by
      dsimp [Function.RightInverse, Function.LeftInverse]
      intro x
      simp only [permutationFunction]
      split_ifs with if_split_1 if_split_2
      <;> apply Fin.eq_of_val_eq
      <;> dsimp only [Fin.val, Fin.le_def] at *
      · omega
      · simp only [Fin.le_def] at if_split_2
        omega
  })

def SignFunction.applyReversal {n : ℕ} (sign_function : SignFunction n)
(reversal : Reversal (n := n)) (i : Fin n) : Sign :=
  if reversal.start_index ≤ i ∧ i ≤ reversal.end_index then
    (sign_function i).flip
  else
    (sign_function i)


def SignedPermutation.applyReversal {n : ℕ} (signed_permutation : SignedPermutation n)
(reversal : Reversal (n := n)) : (SignedPermutation n) :=
  ({
    values := signed_permutation.values * reversal.permutation
    signs := signed_permutation.signs.applyReversal reversal
  } : SignedPermutation n)

structure TwoColoredGraph {n : ℕ} where
  blackEdgesGraph : SimpleGraph (Fin n)
  grayEdgesGraph : SimpleGraph (Fin n)

def TwoColoredGraph.fullGraph {n : ℕ} (two_colored_graph : TwoColoredGraph (n := n))
  : SimpleGraph (Fin n) :=
  two_colored_graph.blackEdgesGraph ⊔ two_colored_graph.grayEdgesGraph


namespace BreakpointGraph

def isConsecutive {n : ℕ} (a b : Fin n) : Prop :=
  a.val = b.val + 1 ∨ b.val = a.val + 1

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

  }



end BreakpointGraph


namespace CycleGraph

def isPaired {n : ℕ} (x : Fin n) (y : Fin n) :=
  (¬ x = y) ∧ (x.val / 2 = y.val / 2)

def fromPermutation {n : ℕ} (σ : Equiv.Perm (Fin n))
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

end CycleGraph

example {n : ℕ} (σ : Equiv.Perm (Fin n)) :
  (BreakpointGraph.fromPermutation σ).blackEdgesGraph ≤
  (CycleGraph.fromPermutation σ).blackEdgesGraph := by sorry

example {n : ℕ} (σ : Equiv.Perm (Fin n)) :
  (BreakpointGraph.fromPermutation σ).grayEdgesGraph ≤
  (CycleGraph.fromPermutation σ).grayEdgesGraph := by sorry

example {n : ℕ} (σ : Equiv.Perm (Fin n)) :
  (BreakpointGraph.fromPermutation σ).fullGraph ≤
  (CycleGraph.fromPermutation σ).fullGraph := by sorry


def unsignedPermutationFromSigned {n : ℕ}
(signed_permutation : SignedPermutation (n := n)) :
Equiv.Perm (Fin (2*n)) :=
  {
    toFun (i : Fin (2*n)) :=

      let cor_base_index : Fin n :=
        ⟨i.val/2, by have := i.isLt; omega⟩

      let sign_at_base_index := signed_permutation.signs cor_base_index

      let value_at_base_index : Fin n := signed_permutation.values cor_base_index

      let cor_pair_values : Array Nat :=
        #[value_at_base_index * 2, value_at_base_index * 2 + 1]

      let pair_values_index :=
        (i.val + sign_at_base_index.flip.toZeroOne) % 2

      have array_index_in_bounds : pair_values_index < cor_pair_values.size := by
        change pair_values_index < 2
        exact Nat.mod_lt _ (by decide)

      let result := cor_pair_values[pair_values_index]'array_index_in_bounds

      ⟨result, by
        simp only [List.getElem_toArray, result, cor_pair_values]
        have : pair_values_index < 2 := by exact array_index_in_bounds
        interval_cases pair_values_index
        · simp only [List.getElem_cons_zero, gt_iff_lt]
          linarith [value_at_base_index.isLt]
        · simp only [List.getElem_cons_succ, List.getElem_cons_zero, gt_iff_lt]
          linarith [value_at_base_index.isLt]
      ⟩
    invFun (i : Fin (2*n)) :=

      -- Inverse of the unsigned permutation of the signed permutation
      let inverse_of_up_of_sp : Equiv.Perm (Fin n) := signed_permutation.values.symm

      let cor_signed_permutation_index : Fin n :=
        ⟨i.val/2, by have := i.isLt; omega⟩

      let base_index : Fin n := inverse_of_up_of_sp cor_signed_permutation_index

      let sign_at_base_index := signed_permutation.signs base_index
      let index_within_pair : ℕ := (i + sign_at_base_index.flip.toZeroOne) % 2

      ⟨base_index * 2 + index_within_pair, by omega⟩

    left_inv := by
      have mul_two_p_1_div_2_eq_id (i : ℕ) : (i * 2 + 1) / 2 = i := by omega

      dsimp only [Lean.Elab.WF.paramLet, List.getElem_toArray]
      intro x


      obtain x_even | x_odd := Nat.even_or_odd x.val
      · obtain ⟨k, x_val_eq_2k⟩ := x_even
        simp only [x_val_eq_2k]
        have simplify_base_index_calculation : (k + k) / 2 = k := by omega
        simp only [simplify_base_index_calculation]
        have kpk_mod_2_eq_0 (k : ℕ): (k + k) % 2 = 0 := by omega
        have kpkp1_mod_2_eq_1 (k : ℕ): (k + k + 1) % 2 = 1 := by omega
        let base_index : Fin n := ⟨k, by omega⟩
        let sign_at_base_index : Sign := (signed_permutation.signs base_index)
        cases sign_at_base_index_case : sign_at_base_index
        · simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne, add_zero]
          simp only [kpk_mod_2_eq_0, List.getElem_cons_zero, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, mul_div_cancel_right₀, Fin.eta, Equiv.symm_apply_apply,
            Nat.mul_add_mod_self_right]
          simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          apply Fin.eq_of_val_eq
          simp only [x_val_eq_2k]
          omega
        · simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne]
          simp only [kpkp1_mod_2_eq_1, List.getElem_cons_succ, List.getElem_cons_zero]
          simp only [mul_two_p_1_div_2_eq_id, Fin.eta, Equiv.symm_apply_apply]
          simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          apply Fin.eq_of_val_eq
          simp only [x_val_eq_2k]
          omega
      · obtain ⟨k, x_val_eq_2k_p_1⟩ := x_odd
        simp only [x_val_eq_2k_p_1]
        have simplify_base_index_calculation : (2*k + 1) / 2 = k := by omega
        simp only [simplify_base_index_calculation]
        let base_index : Fin n := ⟨k, by omega⟩
        let sign_at_base_index : Sign := (signed_permutation.signs base_index)
        have _2k_p_1_mod_2_eq_1: (2*k+1)  % 2 = 1 := by omega
        cases sign_at_base_index_case : sign_at_base_index
        · simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne, add_zero]
          simp only [_2k_p_1_mod_2_eq_1, List.getElem_cons_succ, List.getElem_cons_zero]
          simp only [mul_two_p_1_div_2_eq_id]
          apply Fin.eq_of_val_eq
          simp only [Fin.eta, Equiv.symm_apply_apply]
          simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          omega
        · simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne]
          have : (2 * k + 1 + 1) % 2 = 0 := by omega
          simp only [this, List.getElem_cons_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            mul_div_cancel_right₀, Fin.eta, Equiv.symm_apply_apply, Nat.mul_add_mod_self_right]
          simp only [sign_at_base_index, base_index, sign_at_base_index_case]
          apply Fin.eq_of_val_eq
          simp only [x_val_eq_2k_p_1]
          omega
    right_inv := by
      dsimp only [List.getElem_toArray]
      intro y

      obtain y_even | y_odd := Nat.even_or_odd y.val
      · obtain ⟨k, y_val_eq_2k⟩ := y_even
        have simplify_base_index_calculation : (k + k) / 2 = k := by omega
        have kpk_mod_2_eq_0 (k : ℕ): (k + k) % 2 = 0 := by omega
        have kpkp1_mod_2_eq_1 (k : ℕ): (k + k + 1) % 2 = 1 := by omega
        have k_mul_2_p1_div2(k : ℕ): (k * 2 + 1) / 2 = k := by omega
        --set base_val : Fin n := ⟨y.val / 2, by omega⟩ with base_val_prop
        --let base_index : Fin n := (Equiv.symm signed_permutation.values) ⟨y.val / 2, by omega⟩
        --let sign_at_base_index : Sign :=
        --(signed_permutation.signs ((Equiv.symm signed_permutation.values) ⟨y.val / 2, by omega⟩))
        cases sign_at_base_index_case :
          (signed_permutation.signs ((Equiv.symm signed_permutation.values) ⟨y.val / 2, by omega⟩))
        · simp only [sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne]
          simp only [y_val_eq_2k] at ⊢ sign_at_base_index_case
          norm_num
          simp only [simplify_base_index_calculation, kpk_mod_2_eq_0] at ⊢ sign_at_base_index_case
          norm_num
          rw [← Fin.val_eq_val]
          dsimp
          simp only [sign_at_base_index_case]
          norm_num
          simp only [y_val_eq_2k]
          exact Nat.mul_two k
        · simp only [sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne]
          simp only [y_val_eq_2k] at ⊢ sign_at_base_index_case
          simp only [simplify_base_index_calculation, kpkp1_mod_2_eq_1, k_mul_2_p1_div2]
            at ⊢ sign_at_base_index_case
          simp only [sign_at_base_index_case]
          norm_num
          rw [← Fin.val_eq_val]
          dsimp
          have (k : ℕ): (k * 2 + 1 + 1)%2 = 0 := by omega
          simp only [this]
          dsimp
          omega
      · obtain ⟨k, y_val_eq_2k⟩ := y_odd
        have simplify_base_index_calculation (m : ℕ) : (2 * m + 1) / 2 = m := by omega
        have simplify_base_index_calculation' (m : ℕ) : (m * 2 + 1) / 2 = m := by omega
        rw [← Fin.val_eq_val]
        cases sign_at_base_index_case :
          (signed_permutation.signs ((Equiv.symm signed_permutation.values) ⟨y.val / 2, by omega⟩))
        · simp only [sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne]
          simp only [y_val_eq_2k] at ⊢ sign_at_base_index_case
          norm_num
          simp only [simplify_base_index_calculation, simplify_base_index_calculation']
            at ⊢ sign_at_base_index_case
          simp only [sign_at_base_index_case]
          norm_num
          rw [mul_comm]
        · simp only [sign_at_base_index_case]
          simp only [Sign.flip, Sign.toZeroOne]
          simp only [y_val_eq_2k] at ⊢ sign_at_base_index_case
          simp only [simplify_base_index_calculation] at ⊢ sign_at_base_index_case
          have (k : ℕ): (2 * k + 1 + 1) % 2 = 0 := by omega
          simp only [this]
          norm_num
          simp only [sign_at_base_index_case]
          norm_num
          rw [mul_comm]
  }

def test_SP1 : SignedPermutation 4 := {
  values := Equiv.refl (Fin 4)
  signs := fun _ ↦ Sign.positive
}
def test_SP2 : SignedPermutation 4 := {
  values := Equiv.refl (Fin 4)
  signs := fun _ ↦ Sign.negative
}

def test_SP3 : SignedPermutation 4 := {
  values := Equiv.refl (Fin 4) * (Equiv.swap 0 1)
  signs := fun _ ↦ Sign.positive
}

def result_UP1 := unsignedPermutationFromSigned test_SP1
def result_UP2 := unsignedPermutationFromSigned test_SP2
def result_UP3 := unsignedPermutationFromSigned test_SP3


#eval! (List.range 8).map (fun i => result_UP1 (Fin.ofNat (2*4) i))
#eval! (List.range 8).map (fun i => result_UP2 (Fin.ofNat (2*4) i))
#eval! (List.range 8).map (fun i => result_UP3 (Fin.ofNat (2*4) i))

#eval! (List.range 8).map (fun i =>
  let x := Fin.ofNat 8 i
  result_UP1.symm (result_UP1 x)
)

#eval! (List.range 8).map (fun i =>
  let x := Fin.ofNat 8 i
  result_UP2.symm (result_UP2 x)
)

#eval! (List.range 8).map (fun i =>
  let x := Fin.ofNat 8 i
  result_UP3.symm (result_UP3 x)
)


end SSPRHannenhalliPevznerTheory.Basic
