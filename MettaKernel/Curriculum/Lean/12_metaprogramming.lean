/- Lean 12 — metaprogramming: macros, syntax + macro_rules, a custom tactic, and a
   term elaborator. (Source: Lean Reference Manual / Metaprogramming in Lean 4.)
   Uses `import Lean` (Lean's own metaprogramming API, NOT Mathlib). -/
import Lean
open Lean

namespace L12

-- a term-level macro (syntactic sugar that expands before elaboration)
macro "twice " n:term : term => `(2 * $n)
example : (twice 21) = 42 := rfl
#eval twice 21

-- a `syntax` declaration plus `macro_rules` giving its expansion
syntax "thrice " term : term
macro_rules | `(thrice $n) => `(3 * $n)
example : (thrice 4) = 12 := rfl

-- a custom TACTIC defined by macro
macro "splitGoal" : tactic => `(tactic| constructor)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  splitGoal <;> assumption

-- a term ELABORATOR producing an `Expr` directly
elab "seven" : term => return (mkNatLit 7)
example : seven = 7 := rfl
#eval seven

end L12
