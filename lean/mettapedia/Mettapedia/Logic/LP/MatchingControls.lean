import Mettapedia.Logic.LP.Matching

/-!
# Ground matching consistency controls

These executable controls distinguish repeated pattern holes from independent
holes, including repetitions across separate atom arguments. The public
soundness laws are `matchTerm_sound` and `matchAtom_sound` in `Matching`.
-/

namespace Mettapedia.Logic.LP.MatchingControls

abbrev signature : LPSignature :=
  { constants := Bool, vars := Nat, relationSymbols := Unit,
    relationArity := fun _ => 2, functionSymbols := Unit,
    functionArity := fun _ => 2 }

def repeated : Term signature := .app () (fun _ => .var 0)
def independent : Term signature := .app () (fun i => .var i.val)
def unequal : GroundTerm signature := .app () (fun i => .const (i.val == 0))
def equal : GroundTerm signature := .app () (fun _ => .const true)

def accepts (pattern : Term signature) (target : GroundTerm signature) : Bool :=
  match matchTerm pattern target with
  | .success _ => true
  | .failure => false

/-- info: false -/
#guard_msgs in
#eval accepts repeated unequal

/-- info: true -/
#guard_msgs in
#eval accepts repeated equal

/-- info: true -/
#guard_msgs in
#eval accepts independent unequal

/-- info: false -/
#guard_msgs in
#eval accepts (.const false) (.const true)

/-- info: false -/
#guard_msgs in
#eval match matchAtom
    (Atom.mk () (fun _ => .var 0) : Atom signature)
    (GroundAtom.mk () (fun i => .const (i.val == 0))) with
  | .success _ => true
  | .failure => false

/-- info: some (true, false) -/
#guard_msgs in
#eval match matchTerm independent unequal with
  | .success substitution =>
    match substitution 0, substitution 1 with
    | .const first, .const second => some (first, second)
    | _, _ => none
  | .failure => none

#print axioms matchTerm_sound
#print axioms matchAtom_sound
#print axioms matchTerm_complete
#print axioms matchAtom_complete

end Mettapedia.Logic.LP.MatchingControls
