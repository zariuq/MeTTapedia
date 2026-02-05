import Mathlib.Data.Finset.Basic

/-!
# π-Calculus Syntax

Asynchronous, choice-free π-calculus following Lybech (2022).

Key difference from ρ-calculus: Names are ATOMIC (countably infinite set),
not structured/quoted processes.

## References
- Lybech (2022): "Encodability and Separation for a Reflective Higher-Order Calculus", Section 3, page 98
-/

namespace Mettapedia.OSLF.PiCalculus

/-- Atomic names (countably infinite) -/
def Name : Type := String

instance : DecidableEq Name := inferInstanceAs (DecidableEq String)
instance : Repr Name := inferInstanceAs (Repr String)

/-- Process syntax for π-calculus -/
inductive Process : Type where
  | nil : Process                              -- 0
  | par : Process → Process → Process          -- P | Q
  | input : Name → Name → Process → Process    -- x(y).P
  | output : Name → Name → Process             -- x<z> (asynchronous)
  | nu : Name → Process → Process              -- (νx)P (restriction)
  | replicate : Name → Name → Process → Process -- !x(y).P (input-guarded)
  deriving DecidableEq, Repr

namespace Process

/-- Parallel composition notation -/
infixl:50 " ||| " => Process.par

/-- Free names in a process -/
def freeNames : Process → Finset Name
  | nil => ∅
  | par P Q => freeNames P ∪ freeNames Q
  | input x y P => insert x (freeNames P \ {y})
  | output x z => {x, z}
  | nu x P => freeNames P \ {x}
  | replicate x y P => insert x (freeNames P \ {y})

/-- Bound names in a process -/
def boundNames : Process → Finset Name
  | nil => ∅
  | par P Q => boundNames P ∪ boundNames Q
  | input _ y P => insert y (boundNames P)
  | output _ _ => ∅
  | nu x P => insert x (boundNames P)
  | replicate _ y P => insert y (boundNames P)

/-- All names in a process -/
def names (P : Process) : Finset Name :=
  P.freeNames ∪ P.boundNames

/-- Capture-avoiding substitution P[z/y]
Uses if-then-else for easier proof automation (split_ifs) -/
def substitute : Process → Name → Name → Process
  | nil, _, _ => nil
  | par P Q, y, z => par (substitute P y z) (substitute Q y z)
  | input x w P, y, z =>
      if x = y then input z w (substitute P y z)
      else if w = y then input x w P  -- w binds y, no substitution
      else input x w (substitute P y z)
  | output x w, y, z =>
      output (if x = y then z else x) (if w = y then z else w)
  | nu x P, y, z =>
      if x = y then nu x P  -- x binds y
      else nu x (substitute P y z)
  | replicate x w P, y, z =>
      if x = y then replicate z w (substitute P y z)
      else if w = y then replicate x w P  -- w binds y
      else replicate x w (substitute P y z)

/-- Check if a name is fresh for a process -/
def isFresh (x : Name) (P : Process) : Prop :=
  x ∉ P.names

end Process

end Mettapedia.OSLF.PiCalculus
