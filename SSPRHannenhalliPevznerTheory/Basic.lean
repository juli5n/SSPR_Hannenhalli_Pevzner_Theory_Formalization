import Mathlib.Tactic.Tauto
-- import Mathlib.Logic.Equiv.Defs
-- import Mathlib.Tactic.Linarith
-- import Mathlib.GroupTheory.Perm.Basic
-- import Mathlib.Combinatorics.SimpleGraph.Basic
-- import Mathlib.Tactic.IntervalCases
-- import Mathlib.Data.Nat.SuccPred
-- import Mathlib.Algebra.Group.Even
-- import Mathlib.Order.Defs.PartialOrder


namespace SSPRHannenhalliPevznerTheory

@[simp]
def isConsecutive {n : ℕ} (a b : Fin n) : Prop :=
a.val = b.val + 1 ∨ b.val = a.val + 1

def isConsecutive.refl {n : ℕ} (a b : Fin n) :
isConsecutive a b ↔ isConsecutive b a := by
  unfold isConsecutive
  tauto

end SSPRHannenhalliPevznerTheory
