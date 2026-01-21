import SSPRHannenhalliPevznerTheory.Basic
import SSPRHannenhalliPevznerTheory.SignedPermutation.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases


namespace SSPRHannenhalliPevznerTheory

/-- An unsigned permutation σ' of size $2n$ for n ∈ ℕ is called
an unsigned representation of a signed permutation, if
∀ i ∈ {1,...,n}, `isConsecutive` σ'(2*i) σ'(2*i+1) holds,
i.e. the images of 2i and 2i+1 under σ' are consecutive.

Every signed permutation σ of size $n$ can be associated with
a unique `UnsignedRepresentationOfSP` σ' of size 2n and vice versa
via the following bijective mapping: From a signed permutation σ, an
`UnsignedRepresentationOfSP` σ' is constructed by replacing each
positive element +i of the signed permutation by the the two numbers
(2i-1) and 2i (in that order!) and each negative element -i by the two numbers
(2i) and (2i-1). -/
structure UnsignedRepresentationOfSP {n : ℕ} where
  val : Equiv.Perm (Fin (2*n))
  property : ∀ (i : Fin n), isConsecutive (val ⟨2*i, by omega⟩) (val ⟨2*i+1, by omega⟩)


instance {n : ℕ} : CoeFun (UnsignedRepresentationOfSP (n := n))
(fun _ ↦ (Fin (2 * n)) → (Fin (2 * n))) where
  coe unsigned_representation := unsigned_representation.val

instance {n : ℕ} : Coe (UnsignedRepresentationOfSP (n := n)) (Equiv.Perm (Fin (2 * n))) where
  coe u := u.val

namespace UnsignedRepresentationOfSP

/-- An equivalent reformulation of `UnsignedRepresentationOfSP.property`. -/
def property' {n : ℕ}
    (unsigned_representation : UnsignedRepresentationOfSP (n := n)) :
    ∀ (x : Fin (2*n)), ∀ (y : Fin (2*n)), x≠y → ((x.val/2) = (y.val/2)) →
    isConsecutive (unsigned_representation x) (unsigned_representation y) := by
  intro x y x_ne_y x_half_eq_y_half
  have : x.val < y.val ∨ y.val < x.val := by omega
  obtain x_lt_y | y_lt_x := this
  · have x_plus_1_eq_y : x.val + 1 = y.val := by omega
    simp only [isConsecutive]
    obtain ⟨k, k_times_2_eq_x | k_times_2_plus_one_eq_x⟩ := Nat.even_or_odd' x.val
    · have := unsigned_representation.property ⟨k, by omega⟩
      simp_rw[← k_times_2_eq_x, x_plus_1_eq_y] at this
      exact this
    · have := unsigned_representation.property ⟨k, by omega⟩
      omega
  · have y_plus_1_eq_x : y.val + 1 = x.val := by omega
    simp only [isConsecutive]
    obtain ⟨k, y_eq_2_times_k | y_eq_2_times_k_plus_one⟩ := Nat.even_or_odd' y.val
    · have := unsigned_representation.property ⟨k, by omega⟩
      simp_rw[← y_eq_2_times_k, y_plus_1_eq_x] at this
      exact Or.symm this
    · have := unsigned_representation.property ⟨k, by omega⟩
      omega

end UnsignedRepresentationOfSP


/-- The function `toggleLSB` flips the least significant bit
of a number in the range `Fin (2 * n)`. -/
def toggleLSB {n : ℕ} (x : Fin (2 * n)) : Fin (2*n) :=
  ⟨if x.val % 2 = 0 then x.val + 1 else x.val - 1, by split <;> omega⟩

namespace toggleLSB

private lemma even_succ_lt_2n {n : ℕ} (x : Fin (2 * n))
    (x_even : Even x.val) : x.val + 1 < 2 * n := by
  obtain ⟨ k, hk ⟩ := even_iff_exists_two_mul.mp x_even
  omega

theorem at_even {n : ℕ} (x : Fin (2 * n)) (x_even : Even x.val) :
    toggleLSB x = ⟨x + 1, even_succ_lt_2n x x_even⟩ := by
  unfold toggleLSB
  rw [Nat.even_iff] at x_even
  simp only [x_even, ↓reduceIte]

theorem at_odd {n : ℕ} (x : Fin (2 * n)) (x_odd : Odd x.val) :
    toggleLSB x = ⟨x - 1, by omega⟩ := by
  unfold toggleLSB
  rw [Nat.odd_iff] at x_odd
  simp only [x_odd, one_ne_zero, ↓reduceIte]

/-- Division by two is invariant under `toggleLSB` since
the toggled bit is shifted away during the division. -/
theorem div_two_eq {n : ℕ} (x : Fin (2 * n)) : ((x/2) : ℕ) = ((toggleLSB x)/2 : ℕ) := by
  unfold toggleLSB
  split
  <;> simp only
  <;> omega

/-- The function `toggleLSB` is fixed-point-free. -/
theorem not_eq {n : ℕ} (x : Fin (2 * n)) : x ≠ (toggleLSB x) := by
  apply Fin.ne_of_val_ne
  unfold toggleLSB
  split
  <;> simp only
  <;> omega

/-- The function `toggleLSB` is involutive, i.e.
it is it's own inverse. -/
theorem involutive {n : ℕ} : Function.Involutive (toggleLSB (n := n)) := by
  intro x
  apply Fin.eq_of_val_eq
  unfold toggleLSB
  simp only
  split_ifs with h1 h2
  <;> omega

theorem eq_iff {n : ℕ} {x : Fin (2 * n)} {y : Fin (2 * n)} :
  toggleLSB x = y ↔ x = toggleLSB y :=
  Function.Involutive.eq_iff toggleLSB.involutive

theorem odd_iff {n : ℕ} {x : Fin (2 * n)} :
  Odd x.val ↔ Even (toggleLSB x).val := by
  unfold toggleLSB
  constructor
  · intro x_odd
    dsimp
    rw [Nat.odd_iff.mp x_odd]
    dsimp
    refine Nat.Odd.sub_odd x_odd ?_
    exact Nat.odd_iff.mpr rfl
  · dsimp
    intro even_if_condition
    by_contra x_even
    simp_rw [Nat.not_odd_iff.mp x_even] at even_if_condition
    dsimp at even_if_condition
    rw [Nat.even_add_one, Nat.not_even_iff_odd] at even_if_condition
    exact x_even even_if_condition


end toggleLSB


/-- The images of x ∈ `Fin (2 * n)` and `toggleLSB`(x)
under an unsigned representation of a signed permutation
(`UnsignedRepresentationOfSP`) are consecutive. -/
theorem UnsignedRepresentationOfSP.images_of_toggleLSB_consecutive
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) (i : Fin (2 * n)) :
  isConsecutive (representation i) (representation (toggleLSB i)) :=
  representation.property' i (toggleLSB i) (toggleLSB.not_eq i) (toggleLSB.div_two_eq i)

theorem UnsignedRepresentationOfSP.image_even_iff_toggleLSB_odd
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) (x : Fin (2 * n)) :
  Even (representation x).val ↔ Odd (representation (toggleLSB x)).val := by
  rw [Nat.even_iff, Nat.odd_iff]
  have := representation.images_of_toggleLSB_consecutive x
  unfold isConsecutive at this
  cases this <;> rename_i consecutive_case
  <;> omega

theorem UnsignedRepresentationOfSP.image_odd_iff_toggleLSB_even
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) (i : Fin (2 * n)) :
  Odd (representation i).val ↔ Even (representation (toggleLSB i)).val := by
  rw [← Nat.not_even_iff_odd,
    representation.image_even_iff_toggleLSB_odd,
    Nat.not_odd_iff_even]



private theorem UnsignedRepresentationOfSP.min_of_preimage_toggleLSB_pair_image_is_even
{n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
∀ (y₀ : Fin (2*n)),
  let x₀ := representation.val.symm y₀
  let x₁ := toggleLSB x₀
  let y₁ := representation x₁
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
    rw [← h]

    have y₀_eq_image_x₀ : y₀ = representation x₀ :=
      (Equiv.symm_apply_eq representation.val).mp rfl

    have x₀_neq_x₁ : x₀ ≠ x₁ := toggleLSB.not_eq x₀

    have y₀_y₁_consecutive : isConsecutive y₀ y₁ := by
      have := representation.images_of_toggleLSB_consecutive x₀
      rw [← y₀_eq_image_x₀] at this
      exact this

    let min_y₀_y₁ := min (i + 1) y₁.val
    unfold isConsecutive at y₀_y₁_consecutive
    obtain min_is_y₁|min_is_y₀ := (min_choice y₀.val y₁.val).symm

    -- If y₁ is the minimum, then y₁ must be i and we can apply
    -- the induction hypothesis
    · have y₁_eq_i : y₁ = i := by omega

      specialize induction_hypothesis y₁ y₁_eq_i

      -- Rewrite the induction_hypothesis using the existing
      -- bindings x₀, x₁, y₁ and y₂
      dsimp only at induction_hypothesis

      have preimage_y₁_eq_x₁ : (Equiv.symm representation.val) y₁ = x₁ :=
        Equiv.symm_apply_apply representation.val x₁
      simp only [preimage_y₁_eq_x₁] at induction_hypothesis

      have x₀_eq_toggleLSB_x₁ : x₀ = toggleLSB x₁ := by
        have : x₁ = toggleLSB x₀ := rfl
        exact toggleLSB.eq_iff.mp this

      rw [← y₁_eq_i] at induction_hypothesis
      rw [← x₀_eq_toggleLSB_x₁] at induction_hypothesis

      rw [← y₀_eq_image_x₀] at induction_hypothesis

      rw [min_comm]
      exact induction_hypothesis


    -- Case: y₀ (=i+1) is minimum and y₁=i+2
    · have y₁_eq_y₀p1 : y₁ = i + 2 := by omega

      -- Assume the minimum y₀ is odd
      by_contra min_is_odd
      rw [Nat.not_even_iff_odd] at min_is_odd

      -- Since y₀ is odd, y₀-1=i must be even
      have i_is_even : Even i := by
        have y₀_odd := min_is_y₀ ▸ min_is_odd
        rw [← Nat.not_even_iff_odd] at y₀_odd
        rw [h] at y₀_odd
        rw [Nat.even_add_one] at y₀_odd
        exact of_not_not y₀_odd

      have i_le_2n : i < 2*n := by omega
      let i_as_fin_2n : Fin (2*n) := ⟨i, i_le_2n⟩

      specialize induction_hypothesis i_as_fin_2n rfl

      let y₀' := i_as_fin_2n
      let x₀' := (Equiv.symm representation.val) i_as_fin_2n
      let x₁' : Fin (2*n) := toggleLSB x₀'
      let y₁' := representation x₁'

      dsimp only at induction_hypothesis

      change Even (Min.min y₀'.val y₁'.val) at induction_hypothesis

      have image_x₀'_is_y₀' : representation x₀' = y₀' :=
        Equiv.apply_symm_apply representation.val i_as_fin_2n

      have y₀'_y₁'_consecutive : isConsecutive (representation x₀') y₁' :=
        (representation.images_of_toggleLSB_consecutive x₀')
      rw [image_x₀'_is_y₀'] at y₀'_y₁'_consecutive

      unfold isConsecutive at *


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
        _ = representation x₀' := by exact Fin.val_eq_of_eq image_x₀'_is_y₀'.symm
        _ = representation (toggleLSB x₁') := by
          rw [← toggleLSB.eq_iff.mpr (show x₁' = toggleLSB x₀' by rfl)]
        _ = representation (toggleLSB (representation.val.symm y₁')) := by
          have : y₁' = representation.val x₁' := rfl
          rw [(Equiv.symm_apply_eq representation.val).mpr this]
        _ = representation (toggleLSB (representation.val.symm y₀)) := by rw [y₁'_eq_y₀]
        _ = representation (toggleLSB (x₀)) := by rfl
        _ = representation (x₁) := rfl
        _ = y₁ := rfl
        _ = i + 2 := by exact y₁_eq_y₀p1


      linarith



/-- The minimum of the images of x ∈ `Fin (2 * n)` and `toggleLSB`(x)
under an unsigned representation of a signed permutation
(`UnsignedRepresentationOfSP`) is even. -/
private theorem UnsignedRepresentationOfSP.min_of_toggleLSB_pair_image_is_even
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
  ∀ (x : Fin (2*n)),
  Even (min (representation x).val (representation (toggleLSB x)).val) := by
  intro x
  let image_x := representation x
  have := representation.min_of_preimage_toggleLSB_pair_image_is_even image_x
  dsimp only at this
  have preimage_image_x_eq_x: representation.val.symm image_x = x :=
    Equiv.symm_apply_apply representation.val x

  rw [preimage_image_x_eq_x] at this
  exact this

/-- A permutation that represents a signed permutation commutes with
`toggleLSB` -/
theorem UnsignedRepresentationOfSP.map_toggleLSB
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
  ∀ (x : Fin (2*n)), representation (toggleLSB x) = toggleLSB (representation x) := by
    intro x
    apply Fin.eq_of_val_eq

    let image_x := representation x

    cases (Nat.mod_two_eq_zero_or_one (representation x))
    <;> rename_i mod2_case
    <;> nth_rw 2 [toggleLSB]
    <;> simp only [mod2_case, ↓reduceIte, one_ne_zero]
    <;> cases (representation.images_of_toggleLSB_consecutive x)
    <;> rename_i images_consecutive_case
    <;> rw [images_consecutive_case]
    <;> have min_even :=  representation.min_of_toggleLSB_pair_image_is_even x
    <;> rw [images_consecutive_case] at min_even

    · have image_x_even := (Nat.even_iff.mpr mod2_case)
      rw [min_eq_right _] at min_even
      · have := Even.add_one min_even
        rw [← images_consecutive_case] at this
        rw [← Nat.not_even_iff_odd] at this
        contradiction
      · exact Nat.le_add_right (↑(representation (toggleLSB x))) 1
    · omega
    · have image_x_odd := (Nat.odd_iff.mpr mod2_case)
      rw [min_eq_left _] at min_even
      · have := Even.add_one min_even
        rw [← Nat.not_even_iff_odd] at image_x_odd
        contradiction
      · exact Nat.le_add_right (↑(representation x)) 1


/-- If the image of x is even under an `UnsignedRepresentationOfSP` σ',
then σ'(`toggleLSB`(x)) = σ'(x)+1. -/
theorem UnsignedRepresentationOfSP.image_toggleLSB_eq_of_image_even
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
  ∀ (x : Fin (2*n)),
  (h : Even (representation x).val) →
  (representation (toggleLSB x)) =
  ⟨(representation x) + 1, by rw [Nat.even_iff] at h; omega⟩ := by
  intro x image_x_even
  rw [Nat.even_iff] at image_x_even
  have := representation.map_toggleLSB x
  nth_rw 2 [toggleLSB] at this
  simp only [image_x_even, ↓reduceIte] at this
  exact this


/-- If the image of x is odd under an `UnsignedRepresentationOfSP` σ',
then σ'(`toggleLSB`(x)) = σ'(x)-1. -/
theorem UnsignedRepresentationOfSP.image_toggleLSB_eq_of_image_odd
  {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
  ∀ (x : Fin (2*n)),
  (h : Odd (representation x).val) →
  (representation (toggleLSB x)) =
  ⟨(representation x) - 1, by omega⟩ := by
  intro x image_x_odd
  rw [Nat.odd_iff] at image_x_odd
  have := representation.map_toggleLSB x
  nth_rw 2 [toggleLSB] at this
  simp only [image_x_odd, one_ne_zero, ↓reduceIte] at this
  exact this

theorem UnsignedRepresentationOfSP.im_toggle_pair_is_even_even_succ
    {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) (x : Fin (2 * n)) :
    ∃ (k : Fin n),
    ((representation x = ⟨ 2 * k, by omega ⟩) ∧
    representation (toggleLSB x) = ⟨ 2 * k + 1, by omega⟩) ∨
    ((representation x = ⟨ 2 * k + 1, by omega⟩ ∧
    representation (toggleLSB x) = ⟨ 2 * k, by omega ⟩)) := by
  by_cases repr_x_even : Even (representation x).val
  · obtain ⟨ k, repr_x_eq_2k⟩ := even_iff_exists_two_mul.mp repr_x_even
    use ⟨k, by omega⟩
    left
    constructor
    · rw [Fin.ext_iff]
      exact repr_x_eq_2k
    · rw [representation.map_toggleLSB x]
      have : representation.val x = ⟨2 * k, by omega⟩ := Fin.eq_mk_iff_val_eq.mpr repr_x_eq_2k
      rw [this]
      dsimp
      apply toggleLSB.at_even
      exact even_two_mul k
  · rw [Nat.not_even_iff_odd] at repr_x_even
    obtain ⟨ k, repr_x_eq_succ_2k⟩ := odd_iff_exists_bit1.mp repr_x_even
    use ⟨k, by omega⟩
    right
    constructor
    · rw [Fin.ext_iff]
      exact repr_x_eq_succ_2k
    · rw [representation.map_toggleLSB x]
      have : representation.val x = ⟨2 * k + 1, by omega⟩ := Fin.eq_mk_iff_val_eq.mpr
        repr_x_eq_succ_2k
      rw [this]
      dsimp
      apply toggleLSB.at_odd
      exact odd_two_mul_add_one k


theorem UnsignedRepresentationOfSP.div_two_eq_toggleLSB_div_two
    {n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) (x : Fin (2 * n)) :
    (representation x).val / 2 = (representation (toggleLSB x)).val / 2 := by
  obtain ⟨k, repr_x_eq_2k | repr_x_eq_succ_2k⟩ := representation.im_toggle_pair_is_even_even_succ x
  · rw [repr_x_eq_2k.1, repr_x_eq_2k.2]
    dsimp
    omega
  · rw [repr_x_eq_succ_2k.1, repr_x_eq_succ_2k.2]
    dsimp
    omega


/-theorem UnsignedRepresentationOfSP.minOfPairIsEven
{n : ℕ} (representation : UnsignedRepresentationOfSP (n := n)) :
∀ (i : Fin n),
let y₀ : Fin (2*n) := representation.val ⟨2*i, by omega⟩
let y₁ : Fin (2*n) := representation.val ⟨2*i+1, by omega⟩
Even (min y₀.val y₁.val) := by
  intro i y₀ y₁
  let x₀ : Fin (2*n) := ⟨2*i, by omega⟩
  let x₁ : Fin (2*n) := ⟨2*i+1, by omega⟩

  have partner_x₀_eq_x₁ : toggleLSB x₀ = x₁ := by
    apply Fin.eq_of_val_eq
    unfold toggleLSB
    simp [x₀, x₁]

  have preimage_y₀_is_x₀: representation.val.symm y₀ = x₀ := by
    rw [Equiv.symm_apply_eq]

  have helper_result := min_of_preimage_toggleLSB_pair_image_is_even representation y₀
  dsimp only at helper_result
  rw [preimage_y₀_is_x₀, partner_x₀_eq_x₁] at helper_result
  exact helper_result-/





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


example : (⟨0, by norm_num⟩ : Fin 2).val = 0 := by exact rfl

#check Function.LeftInverse

def SignedPermutation.fromUnsigned {n : ℕ}
(unsigned_permutation : UnsignedRepresentationOfSP (n := n)) :
SignedPermutation (n := n) :=
  {
    values := {
      toFun :=
        fun i ↦
        ⟨(unsigned_permutation ⟨2*i, by omega⟩) / 2, by omega⟩
      invFun :=
        fun i ↦
        ⟨unsigned_permutation.val.invFun ⟨2*i, by omega⟩ / 2, by omega⟩
      left_inv := by
        -- We have to prove invFun (toFun x) = x
        intro i
        simp only
        apply Fin.eq_of_val_eq
        rw [Nat.div_eq_iff (by norm_num : 0 < 2)]
        simp only [Equiv.invFun_as_coe, Nat.add_one_sub_one]
        rw [Nat.le_and_le_add_one_iff]


        set! first_uindex : Fin (2*n) := ⟨2*i, by omega⟩ with h_first_uindex
        set! second_uindex : Fin (2*n) := ⟨2*i+1, by omega⟩ with ← h2
        set! first_uvalue := unsigned_permutation first_uindex with h_first_uvalue
        set! second_uvalue := unsigned_permutation second_uindex with ← h4

        set considered_value := 2 * ((first_uvalue.val) / 2) with h_considered_value
        simp_rw [ ← h_first_uindex, ← h_first_uvalue, ← h_considered_value]

        have :
          considered_value = first_uvalue ∨ considered_value = second_uvalue
          := by

          obtain first_uvalue_even|first_uvalue_odd :=  (Nat.even_or_odd first_uvalue)
          · left
            rw [Nat.even_iff] at first_uvalue_even
            rw [h_considered_value]
            omega
          · right
            -- have second_uvalue :=
            -- rw [h_considered_value]

            -- rw [Nat.odd_iff] at first_uvalue_odd

            sorry

        sorry

      right_inv :=
        -- We have to prove toFun (invFun x) = x

        sorry
    },
    signs :=
      fun i ↦
        let first := unsigned_permutation.val ⟨2*i, by omega⟩
        let second := unsigned_permutation.val ⟨2*i+1, by omega⟩
        if first < second then Sign.positive else Sign.negative
  }


  /-

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
  -/


def Reversal.scaleUp {n : ℕ} (reversal : Reversal (n := n)) : Reversal (n := 2 * n) :=
  {
    start_index := ⟨reversal.start_index * 2, by omega⟩
    end_index := ⟨reversal.end_index * 2 + 1, by omega⟩
    start_index_le_end_index := by
      apply Fin.val_le_of_le
      simp only [Fin.mk_le_mk]
      have := reversal.start_index_le_end_index
      omega
  }

instance {n : ℕ} : HSMul (Reversal (n := n)) (Equiv.Perm (Fin (2*n))) (Equiv.Perm (Fin (2*n))) where
  hSMul reversal unsigned_permutation := unsigned_permutation * reversal.scaleUp.permutation


instance {n : ℕ} : HSMul
  (Reversal (n := n))
  (UnsignedRepresentationOfSP (n:=n))
  (UnsignedRepresentationOfSP (n:=n)) where
  hSMul reversal unsigned_representation :=
  {
    val := reversal • unsigned_representation.val
    property := by
      intro i

      dsimp only [HSMul.hSMul]
      dsimp only [Reversal.permutation]
      simp only [Equiv.Perm.coe_mul, Equiv.coe_fn_mk, Function.comp_apply]
      dsimp only [Reversal.permutationFunction]
      dsimp only [Reversal.scaleUp]
      simp only [Fin.mk_le_mk, add_le_add_iff_right, isConsecutive]
      split_ifs with if1 if2
      · apply UnsignedRepresentationOfSP.property'
        · rw [Fin.ne_iff_vne]
          dsimp only
          omega
        · dsimp only
          omega
      · apply UnsignedRepresentationOfSP.property'
        · omega
        · omega
      · apply UnsignedRepresentationOfSP.property'
        · omega
        · omega
      · apply UnsignedRepresentationOfSP.property'
        · rw [Fin.ne_iff_vne]
          dsimp only
          exact Nat.two_mul_ne_two_mul_add_one
        · dsimp only
          omega

  }

end SSPRHannenhalliPevznerTheory
