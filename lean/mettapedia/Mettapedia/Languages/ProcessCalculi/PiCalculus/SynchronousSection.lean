import Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousSteps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSection
import Mettapedia.GSLT.LanguageDef.Continued.Presentation

/-!
# The canonical section of synchronous pi, and its three clauses

Synchronous pi authors the laws of restriction and replication. On closed processes the canonical form with
replication is a computable section of its static equivalence (`piSyncCanonicalSection`, the replication theory's
`replicationCanonicalSection`). With the interaction cut of its reaction and the retyping plan of its continuations,
that section makes synchronous pi a continued interactive GSLT (`piSyncContinuedPresentation`, `piSync_isContinued`).

The section is computed on closed processes, all of whose names are restricted:
- the two orders of the exchange have one representative (`exchange_orders_normalize_alike`);
- a replicated process is a copy beside itself (`unfold_equivalent`), two replicated copies are one
  (`replicated_twice_equivalent`), and a replicated inaction is inaction (`replicated_nil_equivalent`);
- a restriction no component uses is dropped (`garbage_equivalent`);
- inequivalent processes are told apart: an output and an input on a private name (`output_input_apart`), and a
  replicated output and its single copy (`replicated_not_single`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (canonR)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piRepBlock)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousSteps (piSyncReplicationLanguage)

/-- **The canonical section of synchronous pi**: the canonical form with replication. -/
def piSyncCanonicalSection : ComputableCanonicalSection piSyncIGSLT :=
  replicationCanonicalSection (laws := piSyncReplicationLanguage) piSyncIGSLT piRepBlock

/-- The section computes the canonical form with replication of the underlying pattern. -/
theorem piSyncCanonicalSection_normalize_val (term : piSyncIGSLT.toGSLT.Term) :
    (piSyncCanonicalSection.normalize term).1 = canonR piRepBlock term.1 :=
  rfl

/-- The three clauses for synchronous pi. -/
def piSyncContinuedPresentation : ContinuedPresentation piSyncIGSLT where
  cut := piSyncInteractionCut
  canonical := piSyncCanonicalSection
  retyping := ContinuationDecorationProfile.ofRetypingPlan piSyncContinuationRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      piSyncContinuationRetyping_redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr
      piSyncContinuationRetyping_wrappable

/-- **Synchronous pi is continued.** -/
theorem piSync_isContinued : IsContinued piSyncIGSLT := ⟨piSyncContinuedPresentation⟩

/-! ## The section on closed processes -/

namespace SectionControls

/-- Inaction. -/
def zero : Pattern := .apply "PiNil" []
/-- A composition. -/
def par (items : List Pattern) : Pattern := .collection .hashBag items none
/-- An output of `datum` on `channel`, followed by `continuation`. -/
def send (channel datum continuation : Pattern) : Pattern := .apply "PiOutK" [channel, datum, continuation]
/-- An input on `channel`. -/
def receive (channel body : Pattern) : Pattern := .apply "PiInp" [channel, .lambda none body]
/-- A replication. -/
def replicate (process : Pattern) : Pattern := .apply "PiRep" [process]
/-- A restriction. -/
def restrict (body : Pattern) : Pattern := .apply "PiNu" [.lambda none body]

/-- A closed process. -/
abbrev Term := piSyncInteractivePresentation.Term

/-- `(νx)(νd)(x⟨d⟩.x(w).0 | x(y).y⟨y⟩.0)`: the exchange with its two components in the other order. -/
def exchangeSwapped : Pattern :=
  restrict (restrict (par [send (.bvar 1) (.bvar 0) (receive (.bvar 1) zero),
    receive (.bvar 1) (send (.bvar 0) (.bvar 0) zero)]))

/-- `(νa) a⟨a⟩.0`. -/
def sender : Pattern := restrict (send (.bvar 0) (.bvar 0) zero)

/-- `(νa) a(y).0`. -/
def listener : Pattern := restrict (receive (.bvar 0) zero)

/-- `(νa) !a⟨a⟩.0`. -/
def replicatedSender : Pattern := restrict (replicate (send (.bvar 0) (.bvar 0) zero))

/-- `(νa)(a⟨a⟩.0 | !a⟨a⟩.0)`. -/
def unfoldedSender : Pattern :=
  restrict (par [send (.bvar 0) (.bvar 0) zero, replicate (send (.bvar 0) (.bvar 0) zero)])

/-- `(νa)(!a⟨a⟩.0 | !a⟨a⟩.0)`. -/
def twiceReplicatedSender : Pattern :=
  restrict (par [replicate (send (.bvar 0) (.bvar 0) zero), replicate (send (.bvar 0) (.bvar 0) zero)])

/-- `(νa)(νb) b⟨b⟩.0`: the outer restriction is used by no component. -/
def garbageSender : Pattern := restrict sender

def exchangeSwappedTerm : Term := ClosedTerm.ofCheck exchangeSwapped (by decide +kernel)
def senderTerm : Term := ClosedTerm.ofCheck sender (by decide +kernel)
def listenerTerm : Term := ClosedTerm.ofCheck listener (by decide +kernel)
def replicatedSenderTerm : Term := ClosedTerm.ofCheck replicatedSender (by decide +kernel)
def unfoldedSenderTerm : Term := ClosedTerm.ofCheck unfoldedSender (by decide +kernel)
def twiceReplicatedSenderTerm : Term := ClosedTerm.ofCheck twiceReplicatedSender (by decide +kernel)
def garbageSenderTerm : Term := ClosedTerm.ofCheck garbageSender (by decide +kernel)
def replicatedNilTerm : Term := ClosedTerm.ofCheck (replicate zero) (by decide +kernel)
def nilTerm : Term := ClosedTerm.ofCheck zero (by decide +kernel)

/-- **The two orders of the exchange have one representative.** -/
theorem exchange_orders_normalize_alike :
    piSyncCanonicalSection.normalize piSyncExchangeTerm = piSyncCanonicalSection.normalize exchangeSwappedTerm :=
  Subtype.ext (by decide +kernel)

/-- **A replicated process is a copy beside itself**: `(νa) !a⟨a⟩.0` is `(νa)(a⟨a⟩.0 | !a⟨a⟩.0)`. -/
theorem unfold_equivalent : piSyncIGSLT.toGSLT.equations.r replicatedSenderTerm unfoldedSenderTerm :=
  (piSyncCanonicalSection.equivalent_iff_normalize_eq _ _).mpr (Subtype.ext (by decide +kernel))

/-- **Two replicated copies are one**: `(νa)(!a⟨a⟩.0 | !a⟨a⟩.0)` is `(νa) !a⟨a⟩.0`. -/
theorem replicated_twice_equivalent :
    piSyncIGSLT.toGSLT.equations.r twiceReplicatedSenderTerm replicatedSenderTerm :=
  (piSyncCanonicalSection.equivalent_iff_normalize_eq _ _).mpr (Subtype.ext (by decide +kernel))

/-- **A replicated inaction is inaction.** -/
theorem replicated_nil_equivalent : piSyncIGSLT.toGSLT.equations.r replicatedNilTerm nilTerm :=
  (piSyncCanonicalSection.equivalent_iff_normalize_eq _ _).mpr (Subtype.ext (by decide +kernel))

/-- **A restriction no component uses is dropped**: `(νa)(νb) b⟨b⟩.0` is `(νb) b⟨b⟩.0`. -/
theorem garbage_equivalent : piSyncIGSLT.toGSLT.equations.r garbageSenderTerm senderTerm :=
  (piSyncCanonicalSection.equivalent_iff_normalize_eq _ _).mpr (Subtype.ext (by decide +kernel))

/-- **An output and an input on a private name are not equivalent.** -/
theorem output_input_apart : ¬ piSyncIGSLT.toGSLT.equations.r senderTerm listenerTerm := by
  intro equivalent
  have same := congrArg Subtype.val ((piSyncCanonicalSection.equivalent_iff_normalize_eq _ _).mp equivalent)
  revert same
  decide +kernel

/-- **A replicated output is not its single copy**: `(νa) !a⟨a⟩.0` and `(νa) a⟨a⟩.0` are not equivalent. -/
theorem replicated_not_single : ¬ piSyncIGSLT.toGSLT.equations.r replicatedSenderTerm senderTerm := by
  intro equivalent
  have same := congrArg Subtype.val ((piSyncCanonicalSection.equivalent_iff_normalize_eq _ _).mp equivalent)
  revert same
  decide +kernel

end SectionControls

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
