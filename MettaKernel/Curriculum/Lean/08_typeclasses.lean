/- Lean 08 — type classes and instance resolution.
   (MeTTaKernel curriculum; sources: TPiL4 `TypeClasses`, Functional Programming in Lean.)
   Vanilla Lean 4, no Mathlib.  These are core to how real Lean proofs dispatch. -/
namespace L08

-- a type class with one method
class Describable (α : Type) where
  describe : α → String

instance : Describable Bool where
  describe b := if b then "yes" else "no"

instance : Describable Nat where
  describe n := s!"n={n}"

-- INSTANCE RESOLUTION: the right instance is found automatically, by type
def tell {α : Type} [Describable α] (a : α) : String := Describable.describe a
#eval tell true          -- "yes"
#eval tell (7 : Nat)     -- "n=7"

-- a LAW-carrying class, with an instance that must discharge the law
class CommutativeOp (α : Type) where
  op   : α → α → α
  comm : ∀ a b, op a b = op b a

instance : CommutativeOp Nat where
  op   := Nat.add
  comm := Nat.add_comm

-- code polymorphic over the class, USING the law it guarantees
theorem op_comm {α : Type} [CommutativeOp α] (a b : α) :
    CommutativeOp.op a b = CommutativeOp.op b a :=
  CommutativeOp.comm a b

-- inheritance via `extends`: a Greetable IS a Pointed
class Pointed (α : Type) where
  point : α
class Greetable (α : Type) extends Pointed α where
  greet : α → String

instance : Greetable Bool where
  point   := true
  greet b := if b then "hi" else "lo"

-- the inherited `Pointed Bool` instance resolves through `Greetable Bool`
def getPoint {α : Type} [Pointed α] : α := Pointed.point
#eval (getPoint : Bool)      -- true, via Greetable's parent
#eval Greetable.greet true

end L08
