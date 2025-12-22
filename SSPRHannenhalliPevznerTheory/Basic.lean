import Mathlib.Logic.Equiv.Defs

namespace SSPRHannenhalliPevznerTheory.Basic

inductive Sign
  | positive
  | negative
deriving DecidableEq, Repr

instance : Inhabited Sign where
  default := Sign.positive

structure SignedPermutation (length : ℕ) where
  values : Equiv.Perm (Fin length)
  signs : Fin n → Sign


end SSPRHannenhalliPevznerTheory.Basic
