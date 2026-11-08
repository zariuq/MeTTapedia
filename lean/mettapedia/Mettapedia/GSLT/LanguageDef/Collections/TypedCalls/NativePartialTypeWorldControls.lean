import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativePartialTypeWorld

/-! # Missing, rejected, malformed and resource-sensitive type observations -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativePartialTypeWorld.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open TypeDependencyAdmission TypeScopeMatcher NativeTypeDemand NativeTypeCallGraphSafety
open RetainedTypePayloads (ExternalView)

def value : Atom := .symbol "sample"
def raw : ExternalView := fun tag key => .grounded (.custom tag key)

def kindOnly : Store
  | .kind _ => some (.kind (.symbol "Symbol"))
  | _ => none

def emptyTypes : Store
  | .kind _ => some (.kind (.symbol "Symbol"))
  | .inferred _ => some (.types [])
  | _ => none

def argument (world : ExternalView) (available : Store) (formal : Atom) :=
  run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
    (NativeTypeDemand.argsPlan (ops world id (fun _ => [])) [formal] [value] Atom.var))

theorem held_position_needs_no_inferred_reply :
    (argument raw kindOnly Atom.atomType).answer = some (.ok (some Atom.var)) ∧
    (argument raw kindOnly Atom.atomType).reads =
      [(.kind value, some (.kind (.symbol "Symbol")))] := by cbv

theorem missing_reply_retains_first_missing_read :
    (argument raw kindOnly (.symbol "Number")).answer = none ∧
    (argument raw kindOnly (.symbol "Number")).reads =
      [(.kind value, some (.kind (.symbol "Symbol"))), (.inferred value, none)] := by
  cbv

theorem completed_rejection_is_not_missing :
    (argument raw emptyTypes (.symbol "Number")).answer = some (.ok none) ∧
    (argument raw emptyTypes (.symbol "Number")).answer ≠
      (argument raw kindOnly (.symbol "Number")).answer := by
  cbv
  intro impossible
  cases impossible

def malformed : Store := fun _ => some (.types [.symbol "Number"])

theorem malformed_kind_is_a_separate_status :
    (argument raw malformed (.symbol "Number")).answer = some (.error ()) ∧
    (argument raw malformed (.symbol "Number")).reads =
      [(.kind value, some (.types [.symbol "Number"]))] := by cbv

def accepted : Option (Except Unit (Option TypeScopeMatcher.State)) → Bool
  | some (.ok (some _)) => true
  | _ => false

def resourceTypes : Store
  | .kind _ => some (.kind (.symbol "Symbol"))
  | .inferred _ => some (.types [RetainedTypePayloads.Controls.state "A"])
  | _ => none

theorem mutable_type_reply_changes_selection :
    accepted (argument RetainedTypePayloads.Controls.initial resourceTypes (.grounded (.int 1))).answer = true ∧
    accepted (argument RetainedTypePayloads.Controls.changed resourceTypes (.grounded (.int 1))).answer = false := by
  cbv

theorem mutable_type_reply_is_not_safe : ¬ StoreSafe resourceTypes := by
  intro safe
  have impossible := safe (.inferred value) (.types [RetainedTypePayloads.Controls.state "A"]) rfl
  simp [ReplySafe, RetainedTypePayloads.Controls.state, resourceFreeList, resourceFree] at impossible

def rowCheck (normalizer : Atom → Atom) :=
  run (fun _ => none : Store) (Mettapedia.Machines.ReadOnlyQueryDemand.demand
    (NativeTypeDemand.rowsPlan (ops raw normalizer (fun _ => [])) ([] : List Atom)
      [.expression [.symbol "->", .symbol "Number"]]))

theorem normalizer_agreement_is_required :
    (rowCheck (fun _ => .symbol "Left")).answer = some (.ok [.symbol "Left"]) ∧
    (rowCheck (fun _ => .symbol "Right")).answer = some (.ok [.symbol "Right"]) ∧
    (rowCheck (fun _ => .symbol "Left")).answer ≠ (rowCheck (fun _ => .symbol "Right")).answer := by
  decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativePartialTypeWorld.Controls
