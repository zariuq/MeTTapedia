import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedHEBoundary
import Mettapedia.Languages.MeTTa.OSLFCore.MinimalOps

/-!
# Scoped equation source for typed squaring

The example uses the existing HE scoped equation matcher and the existing
integer multiplication service. Its exact query result retains the fresh
equation binding, for every integer and every depth above the stated bound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedSquareCollection

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue executeGroundedOp)

def num (n : Int) : Atom := .grounded (.int n)
def apply (head : String) (args : List Atom) : Atom := .expression (.symbol head :: args)
def number : Atom := .symbol "Number"

def squareSpace : Space := Space.ofList [
  .expression [.symbol ":", .symbol "sq", arrowType [number] number],
  .expression [.symbol ":", .symbol "*", arrowType [number, number] number],
  .expression [.symbol "=", apply "sq" [.var "x"], apply "*" [.var "x", .var "x"]]]

/-- Only multiplication is executable here. Its arithmetic is the shared
grounded operation, not a second definition of MeTTa evaluation. -/
def multiplication : GroundedDispatch where
  isExecutable := fun head => head == .symbol "*"
  execute := fun head args => match executeGroundedOp head args with
    | some value => .ok [(value, Bindings.empty)]
    | none => .incorrectArgument

theorem multiplication_integer (m n : Int) :
    multiplication.execute (.symbol "*") [num m, num n] =
      .ok [(num (m * n), Bindings.empty)] := rfl

def squareBindings (n : Int) : Bindings := Bindings.empty.assign "x#2" (num n)

set_option maxHeartbeats 2000000 in
theorem square_query (n : Int) (k : Nat) :
    rawQueryResults squareSpace (apply "sq" [num n]) number Bindings.empty (k + 12) [] =
      [(apply "*" [num n, num n], squareBindings n)] := by
  cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedSquareCollection
