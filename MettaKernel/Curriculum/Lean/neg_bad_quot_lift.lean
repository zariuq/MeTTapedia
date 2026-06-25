/- Negative: Quot.lift must be invariant under the quotient relation.
   SameLen only proves equal lengths, so it cannot justify returning the whole
   representative list. -/
namespace NegBadQuotLift

def SameLen (xs ys : List Nat) : Prop := xs.length = ys.length
def LenQuot : Type := Quot SameLen

def badLift : LenQuot → List Nat :=
  Quot.lift (fun xs : List Nat => xs) (by
    intro xs ys h
    exact h)

end NegBadQuotLift
