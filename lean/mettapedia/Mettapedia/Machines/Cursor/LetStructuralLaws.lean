import Mettapedia.Machines.Cursor.LetPlacement

/-!
# Discarding, copying and commuting a let computation

Moving a binding across branch structure can change whether it runs, how
many independent choices it supplies, and its order relative to other code.
These are separate laws. Total constant values earn all three; read-only,
nondeterministic and generative computations need their own qualifications.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetStructuralLaws

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)
open LetPlacement (yieldOne yield_bind)

variable {World Value Other : Type}

def discard (code : Search World Value) : Search World Unit :=
  code.bind (fun _ => yieldOne ())

def shared (code : Search World Value) : Search World (Value × Value) :=
  code.bind (fun value => yieldOne (value, value))

def independent (code : Search World Value) : Search World (Value × Value) :=
  code.bind (fun first => code.bind (fun second => yieldOne (first, second)))

def leftThenRight (left : Search World Value) (right : Search World Other) :
    Search World (Value × Other) :=
  left.bind (fun first => right.bind (fun second => yieldOne (first, second)))

def rightThenLeft (left : Search World Value) (right : Search World Other) :
    Search World (Value × Other) :=
  right.bind (fun second => left.bind (fun first => yieldOne (first, second)))

theorem discard_constant (value : Value) :
    discard (yieldOne (World := World) value) = yieldOne () := by
  simp only [discard, yield_bind]

theorem copy_constant (value : Value) :
    independent (yieldOne (World := World) value) = shared (yieldOne value) := by
  simp only [independent, shared, yield_bind]

/-- A total constant value commutes with arbitrary other search. No effect
order or world assumption is imposed on the other computation. -/
theorem constant_commutes (value : Value) (other : Search World Other) :
    leftThenRight (yieldOne value) other = rightThenLeft (yieldOne value) other := by
  simp only [leftThenRight, rightThenLeft, yield_bind]

namespace Controls

def nondeterministic : Search Nat Nat := Search.superpose [0, 1]

theorem independent_choices_change_correlation :
    (shared nondeterministic 0).drain.1 = [(0, 0), (1, 1)] ∧
      (independent nondeterministic 0).drain.1 = [(0, 0), (0, 1), (1, 0), (1, 1)] := by decide

theorem equal_valued_choices_still_have_multiplicity :
    (shared (Search.superpose [7, 7]) 0).drain.1.length = 2 ∧
      (independent (Search.superpose [7, 7]) 0).drain.1.length = 4 := by decide

theorem no_answer_is_not_discardable :
    (discard (Search.superpose [] : Search Nat Nat) 0).drain = ([], 0) ∧
      (yieldOne (World := Nat) () 0).drain = ([()], 0) := by decide

def readState : Search Nat Nat := fun world => .answer world world .done
def writeState : Search Nat Unit := fun world => .answer () (world + 1) .done

theorem read_only_can_copy_but_not_commute :
    (shared readState 0).drain = (independent readState 0).drain ∧
      (leftThenRight readState writeState 0).drain = ([(0, ())], 1) ∧
      (rightThenLeft readState writeState 0).drain = ([(1, ())], 1) := by decide

def fresh : Search Nat Nat := fun next => .answer next (next + 1) .done

/-- Allocation identity is visible to a sharing observer even if a printer
would display both fresh values under the same generic variable name. -/
theorem generation_is_not_world_independent :
    (shared fresh 0).drain = ([(0, 0)], 1) ∧
      (independent fresh 0).drain = ([(0, 1)], 2) := by decide

end Controls

end Mettapedia.Machines.Cursor.LetStructuralLaws
