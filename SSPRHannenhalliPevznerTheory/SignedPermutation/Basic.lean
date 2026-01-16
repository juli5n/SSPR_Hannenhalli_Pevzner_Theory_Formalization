import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Nat.Find

namespace SSPRHannenhalliPevznerTheory

/-- A positive or negative sign -/
inductive Sign
  | positive
  | negative
deriving DecidableEq, Repr

namespace Sign
/-- Maps a positive sign to 1 and a negative sign to -1 -/
@[simp]
def toZ (s : Sign) : ℤ :=
  match s with
  | positive => 1
  | negative => -1

/-- Maps a negative sign to 0 and a positive sign to 1 -/
@[simp]
def toZeroOne (s : Sign) : Nat :=
  match s with
  | positive => 1
  | negative => 0


/-- Flips a sign from positive to negative and from negative to positive -/
@[simp]
def flip (s : Sign) : Sign :=
  match s with
  | positive => negative
  | negative => positive

end Sign


abbrev SignFunction (n : ℕ) := Fin n → Sign


instance : Inhabited Sign where
  default := Sign.positive

/-- A signed permutation is a permutation of the set $\{0, ..., n-1\}$ with
a positive or negative `Sign` attached to each element.

An example of a signed permutation is $\{-2, +1, +3\}$.

Signed permutations are reprented using two components: a regular permutation `Equiv.Perm (Fin n)`
and a `SignFunction n`:=`Fin n → Sign`. -/
structure SignedPermutation (n : ℕ) where
  values : Equiv.Perm (Fin n)
  signs : SignFunction n

namespace SignedPermutation

/-- The "identity" signed permutation of size `n`
denotes the signed permutation $\{+1, ..., +n\}$ -/
def identity (n : ℕ) : SignedPermutation (n := n) :=
  {
    values := Equiv.refl (Fin n),
    signs := fun _ ↦ Sign.positive
  }

end SignedPermutation

/-- A `Reversal` denotes a certain type of operation
on signed permutations, that reverses the order and flips
the signs of a continuous segment of the permutation.

A reversal is represented by the `start_index` and `end_index`
of the affected segment. The `end_index` must be greater than or equal
to the `start_index`.

In literature, a reversal that affects the segment from index `i` to index `j`
is often denoted by ρ(i,j).
 -/
structure Reversal {n : ℕ} where
  start_index : Fin n
  end_index : Fin n
  start_index_le_end_index : start_index ≤ end_index

def Reversal.permutationFunction {n : ℕ} (reversal : Reversal (n := n))
  (i : Fin n) : Fin n :=
  if index_within_reversal_segment : reversal.start_index ≤ i ∧ i ≤ reversal.end_index then
    ({
      val := reversal.end_index - (i  - reversal.start_index)
      isLt := by omega
    } : Fin n)
  else
    i


/-- The (unsigned) permutation that can be associated with a
reversal, that reverses the order of the elements in the segment
of the underlying unsigned permutation that the reversal affects. -/
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




/-- Applies a reversal to a `SignFunction` of a `SignedPermutation`,
i.e. flips the signs of the elements in the segment affected by the reversal. -/
def SignFunction.applyReversal {n : ℕ} (sign_function : SignFunction n)
(reversal : Reversal (n := n)) (i : Fin n) : Sign :=
  if reversal.start_index ≤ i ∧ i ≤ reversal.end_index then
    (sign_function i).flip
  else
    (sign_function i)

/-- Applies a reversal to a `SignedPermutation`, i.e. reverses the order of
and flips the signs of the elements of the segment that is affected by the reversal.

For example, applying the reversal ρ(0,2) to the signed identity permutation
$\{1, 2, 3, 4\}$ results in $\{-3, -2, -1, 4\}$. -/
def SignedPermutation.applyReversal {n : ℕ} (signed_permutation : SignedPermutation n)
(reversal : Reversal (n := n)) : (SignedPermutation n) :=
  ({
    values := signed_permutation.values * reversal.permutation
    signs := signed_permutation.signs.applyReversal reversal
  } : SignedPermutation n)


instance {n : ℕ} : HSMul (Reversal (n := n)) (SignedPermutation n) (SignedPermutation n) where
  hSMul reversal signed_permutation := signed_permutation.applyReversal reversal

instance {n : ℕ} : HSMul (Reversal (n := n)) (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) where
  hSMul reversal unsigned_permutation := unsigned_permutation * reversal.permutation



section
variable {n : ℕ}
{unsigned_permutation : Equiv.Perm (Fin n)}
{signed_permutation : SignedPermutation (n := n)}
{reversal : Reversal (n := n)}

#check (reversal • unsigned_permutation)
#check (reversal • signed_permutation)


end

/-- For every `SignedPermutation` exists a sequence of `Reversal`s that "sorts" it,
i.e. transforms it into the signed identity permutation. -/
def SignedPermutation.sortable {n : ℕ} (π : SignedPermutation (n := n)) :
∃ reversal_list : List (Reversal (n := n)),
(SignedPermutation.identity n) = (reversal_list.foldl SignedPermutation.applyReversal π) := by
  sorry


/-- The `reversalDistance` of a signed permutation is the minimum number
of reversals needed to "sort" it, i.e. to transform it into the
signed identity permutation. -/
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
