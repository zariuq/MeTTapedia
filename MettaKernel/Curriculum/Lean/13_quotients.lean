/- Lean 13 — KERNEL FEATURE: quotient types.
   `Quot` is a Lean kernel PRIMITIVE: `Quot.lift f h (Quot.mk r a)` reduces to `f a`
   definitionally, and `Quot.sound` makes r-related elements equal.  A kernel without
   quotients cannot check real Lean/Mathlib (Int, Rat, ... are quotients). -/
namespace L13

def sameParity (a b : Nat) : Prop := a % 2 = b % 2
def QP := Quot sameParity

-- a function OUT of the quotient (must respect the relation)
def par : QP → Nat := Quot.lift (fun n => n % 2) (fun a b h => h)

-- the COMPUTATION rule (definitional): lift on a mk reduces to the function
example : par (Quot.mk sameParity 4) = 0 := rfl
example : par (Quot.mk sameParity 7) = 1 := rfl

-- Quot.sound: r-related representatives are EQUAL in the quotient
example : Quot.mk sameParity 0 = Quot.mk sameParity 2 := Quot.sound rfl

-- Quot.ind: prove a property for every quotient element
example (q : QP) : par q < 2 := by
  induction q using Quot.ind with
  | _ n => show n % 2 < 2; omega

end L13
