import Mettapedia.Languages.Maude.ConditionalMax

/-! An independent value observation for closed Nat expressions of the max
module. Unknown constructors remain unobserved. The native implementation
executes compiled source equations, not this observer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ConditionalMax

def value? : Term → Option Nat
  | .app "max.zero" [] => some 0
  | .app "max.succ" [source] => Nat.succ <$> value? source
  | .app "max.max" [left, right] => do pure (max (← value? left) (← value? right))
  | _ => none

theorem value?_numeral (value : Nat) : value? (numeral value) = some value := by
  induction value with
  | zero => simp only [numeral, Examples.numeral, Examples.constant, String.reduceAppend, value?]
  | succ value ih =>
    change value? (.app "max.succ" [numeral value]) = some (value + 1)
    rw [value?, ih]
    rfl

def maxLeftFrame (right : Term) (typed : HasSort Examples.conditional.signature [] right "Nat") :
    ArgumentContext Examples.conditional.signature [] "Nat" "Nat" :=
  ⟨maxOperator, max_member, [], ["Nat"], [], [right], rfl, rfl, .nil, .cons typed .nil⟩

def maxRightFrame (left : Term) (typed : HasSort Examples.conditional.signature [] left "Nat") :
    ArgumentContext Examples.conditional.signature [] "Nat" "Nat" :=
  ⟨maxOperator, max_member, ["Nat"], [], [left], [], rfl, rfl, .cons typed .nil, .nil⟩

theorem maximum_congruent {left left' right right' : Term}
    (first : Equivalent Examples.conditional [] "Nat" left left')
    (second : Equivalent Examples.conditional [] "Nat" right right') :
    Equivalent Examples.conditional [] "Nat" (maximum left right) (maximum left' right') :=
  .trans (.argument (maxLeftFrame right second.sorted.1) first)
    (.argument (maxRightFrame left' first.sorted.2) second)

#print axioms maximum_congruent

end Mettapedia.Languages.Maude.ConditionalMax
