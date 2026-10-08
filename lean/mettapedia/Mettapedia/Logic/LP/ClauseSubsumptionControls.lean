import Mettapedia.Logic.LP.ClauseSubsumption

/-! Positive, negative and occurrence-sensitive clause controls. -/

namespace Mettapedia.Logic.LP.ClauseSubsumption.Controls

abbrev sig : LPSignature :=
  { constants := Bool, vars := Nat, relationSymbols := Bool,
    relationArity := fun _ => 1, functionSymbols := Unit,
    functionArity := fun _ => 2 }

def p (term : Term sig) : SignedAtom sig := (true, Atom.mk true (fun _ => term))
def q (term : Term sig) : SignedAtom sig := (true, Atom.mk false (fun _ => term))
def neg (literal : SignedAtom sig) : SignedAtom sig := (!literal.1, literal.2)

def accepts (consume : Bool) (source target : Clause sig) : Bool :=
  (search consume source target).isSome

-- One shared substitution; reordering and extra target literals are allowed.
/-- info: true -/
#guard_msgs in
#eval accepts false [p (.var 0), q (.var 0)]
  [q (.const true), p (.const true), q (.const false)]

/-- info: false -/
#guard_msgs in
#eval accepts false [p (.var 0), q (.var 0)] [p (.const true), q (.const false)]

/-- info: false -/
#guard_msgs in
#eval accepts false [p (.var 0)] [neg (p (.const true))]

/-- info: false -/
#guard_msgs in
#eval accepts false [p (.var 0), q (.var 0)] [p (.const true)]

-- A repeated pattern may capture one rigid variable, but may not merge two.
/-- info: true -/
#guard_msgs in
#eval accepts false [p (.var 0), q (.var 0)] [p (.var 1), q (.var 1)]

/-- info: false -/
#guard_msgs in
#eval accepts false [p (.var 0), q (.var 0)] [p (.var 1), q (.var 2)]

-- Even a variable in an unused target literal stays protected.
/-- info: false -/
#guard_msgs in
#eval accepts false [p (.var 0)] [p (.const true), q (.var 0)]

-- Set coverage and occurrence consumption deliberately differ.
/-- info: true -/
#guard_msgs in
#eval accepts false [p (.var 0), p (.var 1)] [p (.const true)]

/-- info: false -/
#guard_msgs in
#eval accepts true [p (.var 0), p (.var 1)] [p (.const true)]

/-- info: true -/
#guard_msgs in
#eval accepts true [p (.var 0), p (.var 1)] [p (.const true), p (.const true)]

/-- info: true -/
#guard_msgs in
#eval accepts false [] []

/-- info: true -/
#guard_msgs in
#eval accepts false [] [p (.const true)]

/-- info: false -/
#guard_msgs in
#eval accepts false [p (.var 0)] []

-- The witness exposes the selected target occurrences and a usable binding.
/-- info: some ([1, 0], true) -/
#guard_msgs in
#eval match search false [p (.var 0), q (.var 0)] [q (.const true), p (.const true)] with
  | some (indices, answer) =>
    match answer 0 with
    | .const value => some (indices.map Fin.val, value)
    | _ => none
  | none => none

#print axioms check_sound
#print axioms check_complete
#print axioms search_sound
#print axioms search_set_complete
#print axioms search_alignment_complete
#print axioms search_set_none_iff
#print axioms search_entails

end Mettapedia.Logic.LP.ClauseSubsumption.Controls
