namespace Mettapedia.Logic.HOL

universe u

/-- Simple types for Church-style HOL. -/
inductive Ty (Base : Type u) where
  | prop : Ty Base
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base
deriving DecidableEq, Repr

scoped infixr:61 " ⇒ " => Ty.arr

/-- Type contexts for intrinsically typed terms. -/
abbrev Ctx (Base : Type u) := List (Ty Base)

/-- The distinguished proposition type. -/
abbrev propTy {Base : Type u} : Ty Base := Ty.prop

/-- Iterate an arrow type `n` times on the left. -/
def iterArrow {Base : Type u} (n : Nat) (σ τ : Ty Base) : Ty Base :=
  Nat.rec τ (fun _ ih => σ ⇒ ih) n

end Mettapedia.Logic.HOL
