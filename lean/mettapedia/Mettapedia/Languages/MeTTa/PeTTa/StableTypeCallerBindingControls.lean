import Mettapedia.Languages.MeTTa.PeTTa.StableTypeCallerBinding
import Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQueryControls

/-! Actual ordered query/caller-merge controls, including shared public aliases. -/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MeTTa.PeTTa.StableTypeCallerBinding.Controls

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (TypeTerm Declaration named)
open IndependentTypeOutput (freshSupply callerName)

def symbolName : TypeTerm → Option String
  | .const (.symbol name) => some name
  | _ => none

def observed (result : Result) (names : List Nat) : Option (List (List (Option String))) :=
  match result with
  | .complete deliveries => some (deliveries.map fun delivery =>
      names.map fun name => symbolName (delivery.bindings.applyTerm (.var name)))
  | _ => none

def aliasRecord : Equations := [(.var (callerName 1), .var (callerName 0))]
def expected : TypeTerm := .var (callerName 0)
def subject : TypeTerm := .const (.number "1")
def publicNames : List Nat := [callerName 0, callerName 1]

theorem original_caller_aliases_are_retained :
    observed (call [] freshSupply 1 [] aliasRecord subject expected) publicNames =
      some [[some "Number", some "Number"]] := by cbv

theorem discarding_caller_record_loses_alias :
    observed (.complete (deliver [] expected [named "Number"])) publicNames =
      some [[some "Number", none]] := by cbv

def tagLibrary : List Declaration :=
  [⟨0, .symbol "tag", named "First"⟩, ⟨1, .symbol "tag", named "Second"⟩]

theorem every_reply_retains_the_same_caller :
    observed (call tagLibrary freshSupply 1 [] aliasRecord (named "tag") expected) publicNames =
      some [[some "First", some "First"], [some "Second", some "Second"]] := by cbv

theorem open_value_is_not_protected_from_refinement :
    observed (call [] freshSupply 1 [] [] subject expected) [callerName 0] =
      some [[some "Number"]] ∧ symbolName expected = none := by
  constructor
  · cbv
  · rfl

theorem bound_alias_query_does_not_become_late_filter :
    call StableIntrinsicTypeQuery.Controls.library freshSupply 3 [] []
      StableIntrinsicTypeQuery.Controls.subject StableIntrinsicTypeQuery.Controls.required =
      .complete [] := by
  simp [call, unifyTotal, Subst.applyTerm_id,
    StableIntrinsicTypeQuery.Controls.shared_subject_is_rejected, deliver, deliverFrom]

theorem insufficient_query_budget_retains_pending :
    call [] freshSupply 0 [] aliasRecord subject expected = .pending := by cbv

end Mettapedia.Languages.MeTTa.PeTTa.StableTypeCallerBinding.Controls
