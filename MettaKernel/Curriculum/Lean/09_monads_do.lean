/- Lean 09 — Functor / Monad and do-notation.
   (MeTTaKernel curriculum; source: Functional Programming in Lean, FunctorApplicativeMonad.)
   Vanilla Lean 4.  `do` desugars to `>>=`; the monad laws are proved; a user-defined
   Monad instance shows `do` working over a custom type. -/
namespace L09

-- the Option monad via do-notation (short-circuits on none)
def safeDiv (a b : Nat) : Option Nat := if b = 0 then none else some (a / b)
def chain (a b c : Nat) : Option Nat := do
  let x ← safeDiv a b
  let y ← safeDiv x c
  pure y
#eval chain 100 5 2     -- some 10
#eval chain 100 0 2     -- none

-- the three monad laws for Option, proved
theorem opt_left_id  {α β} (a : α) (f : α → Option β) : (pure a >>= f) = f a := rfl
theorem opt_right_id {α} (m : Option α) : (m >>= pure) = m := by cases m <;> rfl
theorem opt_assoc {α β γ} (m : Option α) (f : α → Option β) (g : β → Option γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by cases m <;> rfl

-- a USER-DEFINED monad; do-notation works over it once the instance is given
inductive Res (ε α : Type) where
  | ok  : α → Res ε α
  | err : ε → Res ε α
  deriving Repr

def Res.bind {ε α β} : Res ε α → (α → Res ε β) → Res ε β
  | .ok a,  f => f a
  | .err e, _ => .err e

instance {ε : Type} : Monad (Res ε) where
  pure a := .ok a
  bind   := Res.bind

def incr {ε} (r : Res ε Nat) : Res ε Nat := do
  let x ← r
  pure (x + 1)
#eval (incr (.ok 41)  : Res String Nat)   -- Res.ok 42
#eval (incr (.err "boom") : Res String Nat) -- Res.err "boom"

end L09
