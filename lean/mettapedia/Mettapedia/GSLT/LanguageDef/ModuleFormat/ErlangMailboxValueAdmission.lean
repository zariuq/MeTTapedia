import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangValueTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangValueShape
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangValueCanonical
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxModelAgreement

/-! Uniform admission for source-valued mailbox requests. Typing, canonical
binder metadata, object shape and scope follow from the shared declarations
and structural encoding. No queue-length, pid-size or closure-capture bound
is imposed by this proof. Operational enabling remains separate from typing. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Admission

open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.Erlang
open ErlangCompilation (value valueList valueList_typed valueList_vector mailbox_vector mapped_values)

theorem mailbox_typed (free : FreeTypeContext) (bound : List TypeExpr) (box : Mailbox Value) :
    HasType language free bound (mailbox value box) (.base "ErMailboxData") := by
  unfold mailbox
  simp only [mapped_values]
  exact ConstructorCertificates.simple
    [("savedRev", .base "ErValues"), ("front", .base "ErValues"), ("rearRev", .base "ErValues")] _
    (by decide +kernel)
    (.cons (valueList_typed free bound box.savedRev)
      (.cons (valueList_typed free bound box.front) (.cons (valueList_typed free bound box.rearRev) .nil)))

theorem model_sorted {pattern : Pattern} (shape : VectorFirstOrder pattern)
    (typed : HasType language Model.environment.free [] pattern (.base "ErMailboxConfig")) : Model.Sorted pattern := by
  have actual : HasType Model.environment.language Model.environment.free [] pattern (.base "ErMailboxConfig") :=
    HasType.of_terms_subset (source := language) (target := Model.environment.language) (fun _ member => member) typed
  exact ⟨actual, GeneralRuleBindingInference.vector_canonical shape,
    GeneralRuleBindingInference.vector_object shape, actual.isWellScopedAt⟩

private theorem unary_sorted (label : String)
    (declared : (language.terms.find? (fun row => row.label == label)).map
      (fun row => (row.category, row.params, ConstructorCertificates.ordinary row)) =
      some ("ErMailboxConfig", [.simple "mailbox" (.base "ErMailboxData")], true))
    (box : Mailbox Value) : Model.Sorted (node label [mailbox value box]) := by
  apply model_sorted
  · exact .constructor _ _ (by simpa only [List.mem_singleton, forall_eq] using mailbox_vector box)
  · exact ConstructorCertificates.simple [("mailbox", .base "ErMailboxData")] _ declared
      (.cons (mailbox_typed Model.environment.free [] box) .nil)

private theorem binary_sorted (label : String)
    (declared : (language.terms.find? (fun row => row.label == label)).map
      (fun row => (row.category, row.params, ConstructorCertificates.ordinary row)) =
      some ("ErMailboxConfig", [.simple "value" (.base "ErValue"), .simple "mailbox" (.base "ErMailboxData")], true))
    (message : Value) (box : Mailbox Value) : Model.Sorted (node label [value message, mailbox value box]) := by
  apply model_sorted
  · apply VectorFirstOrder.constructor
    simpa [List.mem_cons] using
      And.intro (ErlangCompilation.value_vector message) (mailbox_vector box)
  · exact ConstructorCertificates.simple [("value", .base "ErValue"), ("mailbox", .base "ErMailboxData")] _ declared
      (.cons (ErlangCompilation.value_typed Model.environment.free [] message)
        (.cons (mailbox_typed Model.environment.free [] box) .nil))

theorem peek_sorted (box : Mailbox Value) : Model.Sorted (node "ErPeek" [mailbox value box]) :=
  unary_sorted "ErPeek" (by decide +kernel) box

theorem next_sorted (box : Mailbox Value) : Model.Sorted (node "ErNext" [mailbox value box]) :=
  unary_sorted "ErNext" (by decide +kernel) box

theorem remove_sorted (box : Mailbox Value) : Model.Sorted (node "ErRemove" [mailbox value box]) :=
  unary_sorted "ErRemove" (by decide +kernel) box

theorem wait_sorted (box : Mailbox Value) : Model.Sorted (node "ErWait" [mailbox value box]) :=
  unary_sorted "ErWait" (by decide +kernel) box

theorem deliver_sorted (message : Value) (box : Mailbox Value) :
    Model.Sorted (node "ErDeliver" [value message, mailbox value box]) :=
  binary_sorted "ErDeliver" (by decide +kernel) message box

theorem wake_sorted (message : Value) (box : Mailbox Value) :
    Model.Sorted (node "ErWake" [value message, mailbox value box]) :=
  binary_sorted "ErWake" (by decide +kernel) message box

theorem unary_canonical (label : String) (box : Mailbox Value) :
    CanonicalBags.canon (node label [mailbox value box]) = node label [mailbox value box] := by
  simp only [node, CanonicalBags.canon_apply, List.map_cons, List.map_nil, ErlangCompilation.mailbox_canonical]

theorem binary_canonical (label : String) (message : Value) (box : Mailbox Value) :
    CanonicalBags.canon (node label [value message, mailbox value box]) = node label [value message, mailbox value box] := by
  simp only [node, CanonicalBags.canon_apply, List.map_cons, List.map_nil,
    ErlangCompilation.value_canonical, ErlangCompilation.mailbox_canonical]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Admission
