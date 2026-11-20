import Mettapedia.Machines.OperatorChoice.HeadDispatchDesigns
import Mettapedia.Machines.SourceRoleElaboration

/-!
# Head selection consumes existing occurrence authority

The source occurrence classifier already distinguishes values, constructors,
static calls and dynamic calls. Candidate selection may consume that authority;
it need not guess code-versus-data from the payload's spelling a second time.
This bridge concerns this entry boundary only: it does not choose whether a
held parameter is later forced by a dialect's body semantics.

The classifier's value-origin input is established evidence. Neither this
module nor SourceRoleElaboration proves a native producer has supplied it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.HeadRoleBridge

open HeadDispatchDesigns
open ExecutionControl.Occurrence (Authority)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

variable {Payload : Type}

def isCall : Authority → Bool
  | .staticCall | .dynamicCall => true
  | .value | .constructor => false

def request (role : Authority) (head : String) (arity : Nat) : Request :=
  ⟨head, arity, !isCall role⟩

theorem value_origin_keeps_general_rules_inactive (design : Design) (scope : Nat)
    (facts : SourceRoleElaboration.Facts) (direct : Bool) (term : Atom)
    (head : String) (arity : Nat) (rows : List (Rule Payload)) :
    select { design with protectHeld := true } scope
      (request (SourceRoleElaboration.classify facts true direct term) head arity) rows = [] := by
  apply held_is_inert rfl
  rfl

theorem value_origin_survives_different_callability_metadata (design : Design) (scope : Nat)
    (first second : SourceRoleElaboration.Facts) (firstDirect secondDirect : Bool)
    (term : Atom) (head : String) (arity : Nat) (rows : List (Rule Payload)) :
    select { design with protectHeld := true } scope
        (request (SourceRoleElaboration.classify first true firstDirect term) head arity) rows =
      select { design with protectHeld := true } scope
        (request (SourceRoleElaboration.classify second true secondDirect term) head arity) rows := by
  rw [value_origin_keeps_general_rules_inactive, value_origin_keeps_general_rules_inactive]

theorem existing_value_and_call_roles_still_differ :
    isCall .value = false ∧ isCall .staticCall = true ∧ isCall .dynamicCall = true := by decide

namespace Controls

def codeLookingValue : Atom := .expression [.symbol "double", .grounded (.int 4)]
def facts : SourceRoleElaboration.Facts := ⟨∅, {"double"}, ∅⟩

theorem the_same_spelling_can_be_a_value_or_an_invocation :
    SourceRoleElaboration.classify facts true false codeLookingValue = .value ∧
      SourceRoleElaboration.classify facts false false codeLookingValue = .staticCall := by decide

theorem general_head_power_does_not_force_value_reinterpretation :
    select HeadDispatchDesigns.Controls.scopedGeneral 0
        (request .value "double" 1) [HeadDispatchDesigns.Controls.generalUnary] = [] ∧
      select HeadDispatchDesigns.Controls.scopedGeneral 0
        (request .staticCall "double" 1) [HeadDispatchDesigns.Controls.generalUnary] = [8] := by decide

end Controls

end Mettapedia.Machines.OperatorChoice.HeadRoleBridge
