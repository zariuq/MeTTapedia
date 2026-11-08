import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedSlotJoin

/-!
# The demanded source program under the current reader and publication rule

All five required read families are earned from the actual occurrence-scoped
driver with supplement annotations. The same operational source derivation
then selects fresh shared formals, executes the constructor and its wrapper,
captures the completed result, and returns it through the emitted slot.
Neither reader agreement nor successful source execution is assumed.
Native pointer, frame, wildcard and mark codecs remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Mettapedia.Machines
open HEDemandedConstructorEdge (space heldResult)
open HEDemandedConstructorInferred (rangeDemand)

def environment (minimal : Minimal.Services) : WorldEnvironment Space Unit :=
  HEDemandedReadInterface.environment HEDemandedCurrentReads.reads minimal

theorem source_call (minimal : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope HEDemandedWholeProgram.sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.unchangedPreservingReady .preserve) :=
  HEDemandedWholeProgram.source_call_with_marking_of_reads HEDemandedCurrentReads.reads minimal
    .unchangedPreserving (Or.inr rfl) live scope

theorem source_and_slot_agree {L O P H : Type}
    (minimal : Minimal.Services) (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (destination next : Nat) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () [] [] HEDemandedWholeProgram.sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.unchangedPreservingReady .preserve) ∧
      RegisterCode.exec sem answer (RegisterCode.compile fuses (.slot 0) true destination next).1
        HEDemandedSlotJoin.localRegisters = some (.ret heldResult) :=
  HEDemandedSlotJoin.source_and_slot_agree_of_reads HEDemandedCurrentReads.reads minimal
    .unchangedPreserving (Or.inr rfl) sem answer fuses destination next

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentSource
