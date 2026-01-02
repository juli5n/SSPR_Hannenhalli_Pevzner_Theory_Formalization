import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.Group.Even
import Mathlib.Order.Defs.PartialOrder

-- set_option pp.coercions false
-- set_option pp.all true

namespace SSPRHannenhalliPevznerTheory.Basic

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

structure TwoColoredGraph {n : ℕ} where
  blackEdgesGraph : SimpleGraph (Fin n)
  grayEdgesGraph : SimpleGraph (Fin n)

def TwoColoredGraph.fullGraph {n : ℕ} (two_colored_graph : TwoColoredGraph (n := n))
  : SimpleGraph (Fin n) :=
  two_colored_graph.blackEdgesGraph ⊔ two_colored_graph.grayEdgesGraph


@[simp]
def isConsecutive {n : ℕ} (a b : Fin n) : Prop :=
a.val = b.val + 1 ∨ b.val = a.val + 1

def isConsecutive.refl {n : ℕ} (a b : Fin n) :
isConsecutive a b ↔ isConsecutive b a := by
  unfold isConsecutive
  tauto


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

}



end BreakpointGraph


namespace CycleGraph

def isPaired (x : Fin n) (y : Fin n) :=
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


structure UnsignedRepresentationOfSP {n : ℕ} where
  val : Equiv.Perm (Fin (2*n))
  property : ∀ (i : Fin n), isConsecutive (val ⟨2*i, by omega⟩) (val ⟨2*i+1, by omega⟩)

def UnsignedRepresentationOfSP.property' {n : ℕ}
  (unsigned_representation : UnsignedRepresentationOfSP (n := n)) :
  ∀ (x : Fin (2*n)), ∀ (y : Fin (2*n)), x≠y → ((x.val/2) = (y.val/2)) →
  isConsecutive (unsigned_representation.val x) (unsigned_representation.val y) := by
  sorry


#check Fin.rec
#check Nat.strongRec
#check le_trans
#check Fin.induction


def partner {n : ℕ} (x : Fin (2*n)) : Fin (2*n) :=
  ⟨if x.val % 2 = 0 then x.val + 1 else x.val - 1, by split <;> omega⟩

def partner.samePairIndex {n : ℕ} (x : Fin (2*n)) : ((x/2) : ℕ) = ((partner x)/2 : ℕ) := by
  unfold partner
  split
  <;> simp only
  <;> omega

def partner.notEq {n : ℕ} (x : Fin (2 * n)) : x ≠ (partner x) := by
  apply Fin.ne_of_val_ne
  unfold partner
  split
  <;> simp only
  <;> omega

def UnsignedRepresentationOfSP.imagesOfPairConsecutive
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) (i : Fin (2 * n)) :
  isConsecutive (representation.val i) (representation.val (partner i)) :=
  representation.property' i (partner i) (partner.notEq i) (partner.samePairIndex i)

theorem partner.involutive {n : ℕ} : Function.Involutive (partner (n := n)) := by
  intro x
  apply Fin.eq_of_val_eq
  unfold partner
  simp only
  split_ifs with h1 h2
  <;> omega

#check congrArg

theorem partner.eq_iff {n : ℕ} {x : Fin (2 * n)} {y : Fin (2 * n)} :
  partner x = y ↔ x = partner y :=
  Function.Involutive.eq_iff partner.involutive


def minOfPairIsEvenHelper
{n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
∀ (y₀ : Fin (2*n)),
  let x₀ := representation.val.symm y₀
  let x₁ := partner x₀
  let y₁ := representation.val x₁
  Even (min y₀.val y₁.val) := by
  intro y₀
  induction h : y₀.val generalizing y₀ with
  | zero =>
      intro x₀ x₁ y₁
      have : min 0 y₁.val = 0 := by
        apply le_antisymm
        · exact min_le_left 0 y₁.val
        · exact Nat.zero_le (min 0 y₁.val)
      rw [this]
      exact Nat.even_iff.mpr this
  | succ i induction_hypothesis =>
    intro x₀ x₁ y₁


    have y₀_eq_image_x₀ : y₀ = representation.val x₀ :=
      (Equiv.symm_apply_eq representation.val).mp rfl


    -- let pair_index_x₀ : ℕ := x₀ / 2
    -- let pair_index_x₁ : ℕ := x₁ / 2

    -- have same_pair_index :pair_index_x₀ = pair_index_x₁ := by
    --   dsimp [pair_index_x₀, pair_index_x₁, x₀, x₁]
    --   split <;> omega

    have x₀_neq_x₁ : x₀ ≠ x₁ := partner.notEq x₀


    have y₀_y₁_consecutive : isConsecutive y₀ y₁ := by
      have := representation.imagesOfPairConsecutive x₀
      rw [← y₀_eq_image_x₀] at this
      exact this


    let min := min (i + 1) y₁.val
    unfold isConsecutive at y₀_y₁_consecutive
    obtain min_is_y₁|min_is_ip1 := (min_choice (i+1) y₁).symm

    -- If y₁ is the minimum, then y₁ must be i and we can apply
    -- the induction hypothesis
    ·
      have y₁_eq_i : y₁ = i := by omega

      specialize induction_hypothesis y₁ y₁_eq_i

      -- Rewrite the induction_hypothesis using the existing
      -- bindings x₀, x₁, y₁ and y₂
      dsimp only at induction_hypothesis

      have preimage_y₁_eq_x₁ : (Equiv.symm representation.val) y₁ = x₁ :=
        Equiv.symm_apply_apply representation.val x₁
      simp only [preimage_y₁_eq_x₁] at induction_hypothesis

      have x₀_eq_partner_x₁ : x₀ = partner x₁ := by
        have : x₁ = partner x₀ := rfl
        exact partner.eq_iff.mp this

      rw [← y₁_eq_i] at induction_hypothesis
      rw [← x₀_eq_partner_x₁] at induction_hypothesis

      rw [← y₀_eq_image_x₀] at induction_hypothesis


      rw [← h, min_comm]
      exact induction_hypothesis


    -- Case: y₀ (=i+1) is minimum and y₁=i+2
    · have y₁_eq_y₀p1 : y₁ = i + 2 := by omega
      -- Assume the minimum y₀ is odd
      by_contra min_is_odd
      rw [Nat.not_even_iff_odd] at min_is_odd

      -- Since y₀ is odd, y₀-1=i must be even
      have i_is_even : Even i := by
        rw [min_is_ip1] at min_is_odd
        rw [← Nat.not_even_iff_odd] at min_is_odd
        rw [Nat.even_add_one] at min_is_odd
        exact of_not_not min_is_odd

      --
      have i_le_2n : i < 2*n := by omega
      let i_as_fin_2n : Fin (2*n) := ⟨i, i_le_2n⟩

      specialize induction_hypothesis i_as_fin_2n rfl

      let y₀' := i_as_fin_2n
      let x₀' := (Equiv.symm representation.val) i_as_fin_2n
      let x₁' : Fin (2*n) := partner x₀'
      let y₁' := representation.val x₁'

      dsimp only at induction_hypothesis

      change Even (Min.min y₀'.val y₁'.val) at induction_hypothesis

      have image_x₀'_is_y₀' : representation.val x₀' = y₀' :=
        Equiv.apply_symm_apply representation.val i_as_fin_2n

      have y₀'_y₁'_consecutive : isConsecutive (representation.val x₀') y₁' :=
        (representation.imagesOfPairConsecutive x₀')
      rw [image_x₀'_is_y₀'] at y₀'_y₁'_consecutive

      unfold isConsecutive at *
      rw [← h] at min_is_ip1


      -- Since the minimum of y₀' y₁' is even after the induction hypothesis
      -- and y₀'=i is even, the minimum of y₀' and y₁' must be y₀'

      have min_y₀'_y₁'_is_y₀': (Min.min y₀' y₁') = y₀' := by
        by_contra min_y₀'_y₁'_is_y₁'
        replace min_y₀'_y₁'_is_y₁' := Or.resolve_left (min_choice y₀' y₁') min_y₀'_y₁'_is_y₁'

        have y₁'_le_y₀' : y₁' ≤ y₀' := by
          have := min_le_left y₀' y₁'
          rw [min_y₀'_y₁'_is_y₁'] at this
          exact this

        have y₀'_eq_y₁'p1: y₀'.val = y₁'.val + 1 := by omega

        have y₁'_is_odd: Odd y₁'.val := by
          have : Even y₀'.val := by assumption
          rw [y₀'_eq_y₁'p1] at this
          exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp this)

        rw [← min_y₀'_y₁'_is_y₁'] at y₁'_is_odd
        rw [← Nat.not_even_iff_odd] at y₁'_is_odd
        contradiction

      have y₀'_le_y₁' : y₀' ≤ y₁' := by
        have := min_le_right y₀' y₁'
        rw [min_y₀'_y₁'_is_y₀'] at this
        exact this

      have y₁'_eq_y₀'p1: y₁'.val = y₀'.val + 1 := by omega

      have y₁'_eq_y₀ : y₁' = y₀ := by
        apply Fin.eq_of_val_eq
        change y₁'.val = i + 1 at y₁'_eq_y₀'p1
        rw [← h] at y₁'_eq_y₀'p1
        exact y₁'_eq_y₀'p1

      -- We now have:
      -- i   = y₀'
      -- i+1 = y₀ = y₁'
      -- i+2 = y₁
      -- But at the same time we have:
      -- y₀' = image (pair (preimage y₀)) and
      -- y₁ = image (pair (preimage y₀))
      -- Therefore y₀' = y₁, a contradiction
      have : i = i+2 :=
        calc
        i = y₀' := by rfl
        _ = representation.val x₀' := by exact Fin.val_eq_of_eq image_x₀'_is_y₀'.symm
        _ = representation.val (partner x₁') := by
          rw [← partner.eq_iff.mpr (show x₁' = partner x₀' by rfl)]
        _ = representation.val (partner (representation.val.symm y₁')) := by
          have : y₁' = representation.val x₁' := rfl
          rw [(Equiv.symm_apply_eq representation.val).mpr this]
        _ = representation.val (partner (representation.val.symm y₀)) := by rw [y₁'_eq_y₀]
        _ = representation.val (partner (x₀)) := by rfl
        _ = representation.val (x₁) := rfl
        _ = y₁ := rfl
        _ = i + 2 := by exact y₁_eq_y₀p1


      linarith






def UnsignedRepresentationOfSP.minOfPairIsEven
{n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
∀ (i : Fin n),
let first : Fin (2*n) := representation.val ⟨2*i, by omega⟩
let second : Fin (2*n) := representation.val ⟨2*i+1, by omega⟩
Even (min first second).val := by
  by_cases n_eq_0_case : n = 0
  · intro i; have := i.isLt; linarith

  have n_positive : 0 < n := Nat.pos_of_ne_zero n_eq_0_case

  let min_of_corresponding_pair_even (y : Fin (2*n)) : Prop :=
    let x₀ := representation.val.symm y
    let x₁ : Fin (2*n) := ⟨x₀ + ((x₀.val + 1) % 2), by omega⟩
    Even (min y.val (representation.val x₁).val)


  have induction_step : ∀ (i : Fin (2*n)),
    (∀ (j : Fin (2*n)), j < i → min_of_corresponding_pair_even j) →
    min_of_corresponding_pair_even i := by
    intro i induction_requirement
    by_cases i_eq_0 : i.val = 0
    · unfold min_of_corresponding_pair_even
      intro x₀ x₁
      have : min i.val (representation.val x₁).val = 0 := by
        apply le_antisymm
        · exact (le_trans
            (min_le_left i.val (representation.val x₁))
            (show i.val ≤ 0 by rw [i_eq_0])
          )
        · exact Nat.zero_le (min ↑i ↑(representation.val x₁))
      rw [this]
      exact Nat.even_iff.mpr rfl
    · sorry

    -- Beweis per Induktion:
    -- Für 0 ist dies klar
    -- Für n > 0: Angenommen das Minimum von representation x₀ und representation x₁
    -- wäre nicht gerade.
    -- Dann ist das minimum m ungerade
    -- Dann ist m-1 gerade
    -- Nach induktionsvoraussetzung ist m-1 in einem Paar enthalten dessen minimum
    -- gerade ist.
    -- Dann muss m-1 aber mit m zsm im Paar sein
    -- Dann ist aber der andere Wert im Paar sowohl minimum als auch maximum







  sorry


instance {n : ℕ} : Coe (UnsignedRepresentationOfSP (n := n)) (Equiv.Perm (Fin (2*n))) where
  coe x := x.val

def SignedPermutation.toUnsignedDirect {n : ℕ}
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
      let index_within_pair : ℕ := (i +  sign_at_base_index.flip.toZeroOne) % 2

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
    right_inv := by sorry
  }

def SignedPermutation.toUnsigned {n : ℕ}
(signed_permutation : SignedPermutation n) :
UnsignedRepresentationOfSP (n := n) :=
  {
    val := signed_permutation.toUnsignedDirect,
    property := by
      intro i
      unfold isConsecutive
      let sign_at_i : Sign := signed_permutation.signs i
      have helper1: (2*i.val + 1) / 2 = i := by omega
      have helper2: (2*i.val + 1 + 1) % 2 = 0 := by omega
      cases sign_at_i_case : sign_at_i
      · simp only [toUnsignedDirect, Sign.toZeroOne, Sign.flip, List.getElem_toArray,
        Equiv.coe_fn_mk, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
        Fin.eta, sign_at_i_case, add_zero, Nat.mul_mod_right, List.getElem_cons_zero, helper1,
        Nat.mul_add_mod_self_left, Nat.mod_succ, List.getElem_cons_succ,
        or_true, sign_at_i]
      · simp only [toUnsignedDirect, Sign.toZeroOne, Sign.flip, List.getElem_toArray,
        Equiv.coe_fn_mk, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
        Fin.eta, sign_at_i_case, Nat.mul_add_mod_self_left, Nat.mod_succ, List.getElem_cons_succ,
        List.getElem_cons_zero, helper1, helper2, true_or, sign_at_i]
  }

#check Equiv.Perm.inv_eq_iff_eq
#check Nat.div_eq_iff
#check Order.le_and_le_succ_iff

example : (⟨0, by norm_num⟩ : Fin 2).val = 0 := by exact rfl

def SignedPermutation.fromUnsigned {n : ℕ}
(unsigned_permutation : UnsignedRepresentationOfSP (n := n)) :
SignedPermutation (n := n) :=
  {
    values := {
      toFun :=
        fun i ↦
        ⟨(unsigned_permutation.val ⟨2*i, by omega⟩) / 2, by omega⟩
      invFun :=
        fun i ↦
        ⟨unsigned_permutation.val.invFun ⟨2*i, by omega⟩ / 2, by omega⟩
      left_inv := by
        intro i
        simp only
        apply Fin.eq_of_val_eq
        rw [Nat.div_eq_iff (by norm_num : 0 < 2)]
        simp only [Equiv.invFun_as_coe, Nat.add_one_sub_one]
        rw [Nat.le_and_le_add_one_iff]

        sorry

      right_inv := sorry
    },
    signs :=
      fun i ↦
        let first := unsigned_permutation.val ⟨2*i, by omega⟩
        let second := unsigned_permutation.val ⟨2*i+1, by omega⟩
        if first < second then Sign.positive else Sign.negative
  }


-- example {n : ℕ} (σ : SignedPermutation n) :
--   (BreakpointGraph.fromPermutation (UnsignedPermutation.fromSigned σ)).blackEdgesGraph ≤
--   (CycleGraph.fromPermutation (UnsignedPermutation.fromSigned σ)).blackEdgesGraph := by sorry

-- example {n : ℕ} (σ : SignedPermutation n) :
--   (BreakpointGraph.fromPermutation (UnsignedPermutation.fromSigned σ)).grayEdgesGraph ≤
--   (CycleGraph.fromPermutation (UnsignedPermutation.fromSigned σ)).grayEdgesGraph := by sorry

-- example {n : ℕ} (σ : SignedPermutation n) :
--   (BreakpointGraph.fromPermutation (UnsignedPermutation.fromSigned σ)).fullGraph ≤
--   (CycleGraph.fromPermutation (UnsignedPermutation.fromSigned σ)).fullGraph := by sorry



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

def result_UP1 := test_SP1.toUnsignedDirect
def result_UP2 := test_SP2.toUnsignedDirect
def result_UP3 := test_SP3.toUnsignedDirect


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






end SSPRHannenhalliPevznerTheory.Basic
