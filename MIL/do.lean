import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Basic
import Mathlib.Tactic.Common

variable (X Y Z : Type)

def soma : ℕ → ℕ → ℕ
  | a, .zero => a
  | a, .succ n => .succ (soma a n)
