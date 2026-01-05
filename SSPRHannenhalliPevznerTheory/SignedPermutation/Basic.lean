import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Nat.Find

namespace SSPRHannenhalliPevznerTheory

inductive Sign
  | positive
  | negative
deriving DecidableEq, Repr

namespace Sign

@[simp]
def toZ (s : Sign) : ℤ :=
  match s with
  | positive => 1
  | negative => -1

@[simp]
def toZeroOne (s : Sign) : Nat :=
  match s with
  | positive => 1
  | negative => 0


@[simp]
def flip (s : Sign) : Sign :=
  match s with
  | positive => negative
  | negative => positive

end Sign


abbrev SignFunction (n : ℕ) := Fin n → Sign


instance : Inhabited Sign where
  default := Sign.positive

structure SignedPermutation (n : ℕ) where
  values : Equiv.Perm (Fin n)
  signs : SignFunction n

namespace SignedPermutation

def identity (n : ℕ) : SignedPermutation (n := n) :=
  {
    values := Equiv.refl (Fin n),
    signs := fun _ ↦ Sign.positive
  }

end SignedPermutation

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


def SignedPermutation.sortable {n : ℕ} (π : SignedPermutation (n := n)) :
∃ reversal_list : List (Reversal (n := n)),
(SignedPermutation.identity n) = (reversal_list.foldl SignedPermutation.applyReversal π) := by
  sorry



noncomputable def SignedPermutation.reversalDistance
{n : ℕ} (π : SignedPermutation (n := n)) : ℕ :=
  have exists_k_st_π_is_sortable_in_k_steps : ∃ (k : ℕ), ∃ reversal_list : List (Reversal (n := n)),
  reversal_list.length = k ∧
  (SignedPermutation.identity n) = (reversal_list.foldl SignedPermutation.applyReversal π) := by
    obtain ⟨reversal_list, _⟩ := π.sortable
    use reversal_list.length
    use reversal_list
  open Classical in Nat.find exists_k_st_π_is_sortable_in_k_steps

end SSPRHannenhalliPevznerTheory
