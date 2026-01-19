import Mathlib.Tactic.Tauto
import Mathlib.Logic.Equiv.Defs


namespace SSPRHannenhalliPevznerTheory

/--
`isConsecutive a b` states that `a` and `b` are consecutive natural numbers, i.e.
one is the successor of the other
-/
@[simp]
def isConsecutive (a b : ℕ) : Prop :=
a = b + 1 ∨ b = a + 1

def isConsecutive.comm {n : ℕ} (a b : Fin n) :
isConsecutive a b ↔ isConsecutive b a := by
  unfold isConsecutive
  tauto


end SSPRHannenhalliPevznerTheory
