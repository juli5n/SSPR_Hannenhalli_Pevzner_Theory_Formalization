import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Cast.Order.Basic

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

lemma flip_inj (s : Sign) (s' : Sign) : s = s' ↔ s.flip = s'.flip := by
  constructor
  · intro s_eq_s'
    rw [s_eq_s']
  · intro s_flip_eq_s'_flip
    dsimp at s_flip_eq_s'_flip
    cases s'
    · cases s
      · rfl
      · dsimp at s_flip_eq_s'_flip
        exact s_flip_eq_s'_flip.symm
    · cases s
      · dsimp at s_flip_eq_s'_flip
        exact s_flip_eq_s'_flip.symm
      · rfl

lemma flip_flip_eq_self (s : Sign) : s.flip.flip = s := by
  unfold flip
  cases s
  · dsimp
  · dsimp

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

namespace Reversal

def permutationFunction {n : ℕ} (reversal : Reversal (n := n))
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
def permutation {n : ℕ} (reversal : Reversal (n := n)) : (Equiv.Perm (Fin n)) :=
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

lemma in_range_iff_not_left_or_right {n : ℕ} (ρ : Reversal (n := n)) (i : Fin n) :
    (ρ.start_index ≤ i ∧ i ≤ ρ.end_index) ↔ ¬(i < ρ.start_index ∨ ρ.end_index < i) := by
  push_neg
  repeat rw [Fin.not_lt]

lemma left_or_right_iff_outside_range {n : ℕ} (ρ : Reversal (n := n)) (i : Fin n) :
    (i < ρ.start_index ∨ ρ.end_index < i) ↔ ¬(ρ.start_index ≤ i ∧ i ≤ ρ.end_index) :=
  iff_not_comm.mp (in_range_iff_not_left_or_right ρ i)

lemma is_id_outside_range {n : ℕ} (ρ : Reversal (n := n)) (i : Fin n)
    (i_outside_range : i < ρ.start_index ∨ ρ.end_index < i) :
    ρ.permutation i = i := by
  unfold permutation permutationFunction
  simp_rw [ρ.left_or_right_iff_outside_range i] at i_outside_range
  simp only [dite_eq_ite, Equiv.coe_fn_mk, i_outside_range, reduceIte]

lemma reverses_in_range {n : ℕ} (ρ : Reversal (n := n)) (i : Fin n)
    (i_inside_range : ρ.start_index ≤ i ∧ i ≤ ρ.end_index) :
    ρ.permutation i = ρ.end_index - (i - ρ.start_index) := by
  unfold permutation permutationFunction
  simp only [dite_eq_ite, Equiv.coe_fn_mk, i_inside_range, and_self, ↓reduceIte]
  rw [Fin.ext_iff]
  push_cast
  rw [Fin.sub_val_of_le ?_]
  · rw [Fin.sub_val_of_le i_inside_range.1]
  · calc
      i - ρ.start_index ≤ i := by
        rw [Fin.le_def]
        rw [Fin.sub_val_of_le i_inside_range.1]
        exact Nat.sub_le i.val ρ.start_index.val
      _ ≤ ρ.end_index := i_inside_range.2

end Reversal

namespace SignFunction

/-- Applies a reversal to a `SignFunction` of a `SignedPermutation`,
i.e. flips the signs of the elements in the segment affected by the reversal. -/
def applyReversal {n : ℕ} (sign_function : SignFunction n)
    (reversal : Reversal (n := n)) (i : Fin n) : Sign :=
  if reversal.start_index ≤ i ∧ i ≤ reversal.end_index then
    (sign_function i).flip
  else
    (sign_function i)

lemma reversal_flips_in_range {n : ℕ} (sign_function : SignFunction n)
    (ρ : Reversal (n := n)) (i : Fin n)
    (i_outside_range : ρ.start_index ≤ i ∧ i ≤ ρ.end_index) :
    (sign_function.applyReversal ρ) i = (sign_function i).flip := by
  unfold applyReversal
  simp only [i_outside_range, and_self, ↓reduceIte, Sign.flip]

lemma reversal_passes_val_outside_range {n : ℕ} (sign_function : SignFunction n)
    (ρ : Reversal (n := n)) (i : Fin n)
    (i_not_in_range : i < ρ.start_index ∨ ρ.end_index < i) :
    (sign_function.applyReversal ρ) i = sign_function i := by
  unfold applyReversal
  rw [ρ.left_or_right_iff_outside_range] at i_not_in_range
  simp only [i_not_in_range, ↓reduceIte]

end SignFunction

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

namespace SignedPermutation

lemma reversal_flips_sign_in_range {n : ℕ} (π : SignedPermutation n)
    (ρ : Reversal (n := n)) (i : Fin n)
    (i_outside_range : ρ.start_index ≤ i ∧ i ≤ ρ.end_index) :
    (π.applyReversal ρ).signs i = (π.signs i).flip := by
  simp only [applyReversal]
  exact SignFunction.reversal_flips_in_range π.signs ρ i i_outside_range


lemma reversal_reverses_val_in_range {n : ℕ} (π : SignedPermutation n)
    (ρ : Reversal (n := n)) (i : Fin n)
    (i_outside_range : ρ.start_index ≤ i ∧ i ≤ ρ.end_index) :
    (π.applyReversal ρ).values i = π.values (ρ.end_index - (i - ρ.start_index)) := by
  simp only [SignedPermutation.applyReversal]
  rw [Equiv.Perm.mul_apply π.values ρ.permutation i]
  refine Equiv.Perm.congr_arg (Reversal.reverses_in_range ρ i i_outside_range)


/-- |ρ•π(i)| = |π(i)|, for all i not between start index and end index of ρ -/
lemma reversal_passes_val_outside_range {n : ℕ} (π : SignedPermutation n)
    (ρ : Reversal (n := n)) (i : Fin n)
    (i_not_in_range : i < ρ.start_index ∨ ρ.end_index < i) :
    (π.applyReversal ρ).values i = π.values i := by
  unfold SignedPermutation.applyReversal
  dsimp
  have := ρ.is_id_outside_range i i_not_in_range
  exact congrArg (⇑π.values) this

/-- the sign of ρ•π(i) equals the sign of π(i)
for all i not between start index and end index of ρ -/
lemma reversal_passes_sign_outside_range {n : ℕ} (π : SignedPermutation n)
    (ρ : Reversal (n := n)) (i : Fin n)
    (i_not_in_range : i < ρ.start_index ∨ ρ.end_index < i) :
    (π.applyReversal ρ).signs i = π.signs i := by
  unfold SignedPermutation.applyReversal
  dsimp
  exact π.signs.reversal_passes_val_outside_range ρ i i_not_in_range


end SignedPermutation

def IsSortedUpTo {n : ℕ} (π : SignedPermutation n) (k : ℕ) : Prop :=
  ∀ (i : Fin n), i < k → π.values i = i ∧ π.signs i = Sign.positive

def isSortedUpTo_implies_isSortedUpTo_smaller {n : ℕ} (π : SignedPermutation n)
    {k : ℕ} (isSortedUpTo_k : IsSortedUpTo π k) {i : ℕ} (i_lt_k : i < k) :
    IsSortedUpTo π i := by
  intro l l_lt_k
  exact isSortedUpTo_k l (Nat.lt_trans l_lt_k i_lt_k)

/-- For a `SignedPermutation` that is sorted up to exclusively index k,
construct a list of one or two reversals σ₁(, σ₂) s.t. πσ₁(σ₂) is sorted up to index k. -/
def sortingStep {n : ℕ} (π : SignedPermutation n) {k : Fin n}
    (first_k_sorted : IsSortedUpTo π k) :
    List (Reversal (n := n)) :=
  let start_index : Fin n := k
  let end_index := π.values.invFun start_index
  let reversal₁ : Reversal := {
    start_index := start_index
    end_index := end_index
    start_index_le_end_index := by
      unfold start_index
      unfold IsSortedUpTo at first_k_sorted
      rw [Fin.le_def]
      by_contra π_inv_end_index_small
      simp only [not_le] at π_inv_end_index_small
      have π_π_inv_eq_end_index := (first_k_sorted end_index π_inv_end_index_small).1
      unfold end_index at π_π_inv_eq_end_index π_inv_end_index_small
      have : π.values (π.values.invFun start_index) = start_index := by
        rw [Equiv.invFun_as_coe π.values]
        exact Equiv.apply_symm_apply π.values start_index
      rw [this] at π_π_inv_eq_end_index
      grind
  }
  match (π.applyReversal reversal₁).signs start_index with
  | Sign.positive => [reversal₁]
  | Sign.negative =>
    [
      reversal₁, {
      start_index := start_index,
      end_index := start_index,
      start_index_le_end_index := Fin.ge_of_eq rfl
      }
    ]


theorem sortingStep_sorts {n : ℕ} (π : SignedPermutation n) {k : Fin n}
    (first_k_sorted : IsSortedUpTo π k) :
    IsSortedUpTo ((sortingStep π first_k_sorted).foldl SignedPermutation.applyReversal π)
    (k + 1) := by
  intro i i_lt_k_plus_1

  let ρ : Reversal (n := n) :={
    start_index := k,
    end_index := (Equiv.symm π.values) k,
    start_index_le_end_index := sortingStep._proof_1 π first_k_sorted
    }
  have ρ_start_eq_k : ρ.start_index = k := rfl
  have ρ_end_eq_def : ρ.end_index = (Equiv.symm π.values) k := rfl
  have start_le_end : ρ.start_index ≤ ρ.end_index := ρ.start_index_le_end_index
  have k_in_range : ρ.start_index ≤ k ∧ k ≤ ρ.end_index := by
    constructor
    · rw [ρ_start_eq_k]
      exact Fin.ge_of_eq rfl
    · rw [show k = ρ.start_index from rfl]
      exact ρ.start_index_le_end_index
  let k_k_reversal : Reversal := {
    start_index := k,
    end_index := k,
    start_index_le_end_index := sortingStep._proof_3
  }
  have k_k_end_eq_k : k_k_reversal.end_index = k := rfl
  have k_k_start_eq_k : k_k_reversal.start_index = k := rfl
  have k_in_k_k_range : k_k_reversal.start_index ≤ k ∧ k ≤ k_k_reversal.end_index := by
    rw [k_k_start_eq_k, k_k_end_eq_k]
    tauto
  have : (i.val = k.val) ∨ (i.val < k.val) := Or.symm
    ((fun {m n} ↦ Nat.lt_succ_iff_lt_or_eq.mp) i_lt_k_plus_1)
  obtain i_eq_k | i_lt_k := this
  · unfold IsSortedUpTo at first_k_sorted
    unfold sortingStep List.foldl
    dsimp

    rw [Fin.val_inj] at i_eq_k
    have k_minus_k_eq_0 : (k - k) = ⟨0, Fin.pos k⟩ := by
      rw [Fin.eq_mk_iff_val_eq]
      rw [Fin.sub_val_of_le Nat.le.refl]
      exact Nat.sub_self ↑k
    have fin_n_minus_zero_eq_end (x : Fin n) : x - ⟨0, Fin.pos k⟩ = x := by
      rw [Fin.ext_iff]
      rw [Fin.sub_val_of_le]
      · exact rfl
      · rw [Fin.le_def]
        exact Nat.zero_le x.val
    cases π_apply_ρ_sign : (π.applyReversal ρ).signs k
    · dsimp
      constructor
      · have := SignedPermutation.reversal_reverses_val_in_range π ρ k k_in_range
        rw [i_eq_k]
        rw [ρ_start_eq_k, k_minus_k_eq_0, fin_n_minus_zero_eq_end ρ.end_index, ρ_end_eq_def] at this
        rw [Equiv.apply_symm_apply π.values k] at this
        exact this
      · rw [i_eq_k]
        rw [SignedPermutation.reversal_flips_sign_in_range π ρ k k_in_range] at ⊢ π_apply_ρ_sign
        exact π_apply_ρ_sign
    · dsimp
      rw [i_eq_k] at *
      let outer_permutation : SignedPermutation n := π.applyReversal ρ

      constructor
      · have := SignedPermutation.reversal_reverses_val_in_range π ρ k k_in_range
        rw [ρ_start_eq_k, k_minus_k_eq_0, fin_n_minus_zero_eq_end ρ.end_index, ρ_end_eq_def,
          Equiv.apply_symm_apply π.values k] at this

        have outer_application_eq_to := SignedPermutation.reversal_reverses_val_in_range
          outer_permutation k_k_reversal k k_in_k_k_range
        rw [k_k_end_eq_k, k_k_start_eq_k] at outer_application_eq_to
        rw [k_minus_k_eq_0,
          fin_n_minus_zero_eq_end k_k_reversal.end_index] at outer_application_eq_to
        rw [outer_application_eq_to, k_k_end_eq_k]
        exact this
      · dsimp
        have :=
          SignedPermutation.reversal_flips_sign_in_range π ρ k k_in_range
        have outer_application_eq_to := SignedPermutation.reversal_flips_sign_in_range
          outer_permutation k_k_reversal k k_in_k_k_range
        rw [outer_application_eq_to, this]
        rw [this] at π_apply_ρ_sign
        rw [π_apply_ρ_sign]
        rfl
  · unfold sortingStep
    dsimp
    have i_not_in_range : i < ρ.start_index ∨ ρ.end_index < i := by
      left
      rw [ show ρ.start_index = k by rfl ]
      exact i_lt_k
    have i_not_in_k_k_range : i < k_k_reversal.start_index ∨ k_k_reversal.end_index < i := by
      left
      rw [k_k_start_eq_k]
      exact i_lt_k
    rw [π.reversal_flips_sign_in_range ρ k k_in_range]
    constructor
    · cases π_sign_k : π.signs k
      · simp only [Sign.flip, List.foldl_cons, List.foldl_nil]
        rw [(π.applyReversal ρ).reversal_passes_val_outside_range k_k_reversal i i_not_in_k_k_range]
        rw [π.reversal_passes_val_outside_range ρ i i_not_in_range]
        exact (first_k_sorted i i_lt_k).1
      · simp only [Sign.flip, List.foldl_cons, List.foldl_nil]
        rw [π.reversal_passes_val_outside_range ρ i i_not_in_range]
        exact (first_k_sorted i i_lt_k).1
    · cases π_sign_k : π.signs k
      · simp only [Sign.flip, List.foldl_cons, List.foldl_nil]
        rw [(π.applyReversal ρ).reversal_passes_sign_outside_range
          k_k_reversal i i_not_in_k_k_range]
        rw [π.reversal_passes_sign_outside_range ρ i i_not_in_range]
        exact (first_k_sorted i i_lt_k).2
      · simp only [Sign.flip, List.foldl_cons, List.foldl_nil]
        rw [π.reversal_passes_sign_outside_range ρ i i_not_in_range]
        exact (first_k_sorted i i_lt_k).2


structure k_sorting_reversals {n : ℕ} (π : SignedPermutation n) (k : ℕ) where
  reversals : List (Reversal (n := n))
  sorts_up_to_k : IsSortedUpTo (reversals.foldl SignedPermutation.applyReversal π) k

namespace k_sorting_reversals

def emptyPermutationIsSorted (π : SignedPermutation 0) {k : ℕ} :
  IsSortedUpTo π k := by
  intro i i_lt_k
  have := Fin.isEmpty.false i
  contradiction

def everyPermutationSortedUpToZero {n : ℕ} {π : SignedPermutation n} :
  IsSortedUpTo π 0 := by
  intro i i_lt_zero
  omega


def fromK {n : ℕ} (π : SignedPermutation n) (k : ℕ) :
(k_sorting_reversals π k) :=
  if case_n : n = 0 then
    {
      reversals := []
      sorts_up_to_k := by
        rw [@List.foldl_nil]
        subst case_n
        exact emptyPermutationIsSorted π
    }
  else if case_k : k = 0 then
    {
    reversals := []
    sorts_up_to_k := by
      rw [case_k]
      exact everyPermutationSortedUpToZero
    }
  else if case_k' : k > n then
    sorry
  else
    let previous:= fromK π (k-1)
    let previous_permutation := previous.reversals.foldl
      SignedPermutation.applyReversal π

    let additional_reversals:= (@sortingStep
      n
      previous_permutation
      ⟨k-1, by omega⟩
      previous.sorts_up_to_k
    )

    {
    reversals := previous.reversals ++ additional_reversals
    sorts_up_to_k := by
      rw [@List.foldl_append]
      have := @sortingStep_sorts
        n
        previous_permutation
        ⟨k-1, by omega⟩
        previous.sorts_up_to_k
      rw [show (k - 1 + 1 = k) by omega] at this
      exact this
    }




end k_sorting_reversals

private def recursive_simple_sort {n : ℕ} (π : SignedPermutation n) (k : ℕ)
    (sorting_reversals : k_sorting_reversals π k) :
    if k = n then k_sorting_reversals π n else k_sorting_reversals π (k + 1) :=
  sorry

def simple_sort_by_signed_permutations {n : ℕ} (π : SignedPermutation (n := n)) :
    k_sorting_reversals π n := sorry

lemma simple_sort_sorts {n : ℕ} (π : SignedPermutation n)
    (k_sorting_reversals : k_sorting_reversals π n) :
    (k_sorting_reversals.reversals.foldl SignedPermutation.applyReversal π) =
    SignedPermutation.identity n := sorry




/-- For every `SignedPermutation` exists a sequence of `Reversal`s that "sorts" it,
i.e. transforms it into the signed identity permutation. -/
theorem SignedPermutation.sortable {n : ℕ} (π : SignedPermutation (n := n)) :
    ∃ reversals : List (Reversal (n := n)),
    (SignedPermutation.identity n) = (reversals.foldl SignedPermutation.applyReversal π) := by
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
