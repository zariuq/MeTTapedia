import Mettapedia.OSLF.Framework.RhoScopedDependentEventFutures
import Mettapedia.OSLF.Syntax.RhoScopedReactionReceiptControls

/-!
# Original dependent target and receipt distinctions across admitted futures

Two distinct process origins inhabit the same quotation postcondition of an
actual reflected target. The source-indexed native certificates distinguish
these witnesses. Infinitely many supplied original rule receipts also share
their endpoints and target witness while remaining distinct. Fresh-variable
extension preserves both distinctions through the actual native action.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopedDependentEventFutureControls

open _root_.CategoryTheory Mettapedia.OSLF.Binding Mettapedia.TypeTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open RhoScopedDependentEventFutures RhoScopedReactionReceiptControls
open DisplayedPresheafTransport DisplayedPresheafComprehension PresheafEventCertificates
open SyntacticRetractionContexts SyntacticRetractionEventAbsence

def closedWorld : (Syntactic.Ctxt sig)ᵒᵖ := Opposite.op ⟨[]⟩

def visibleRoot : Root sourceRules withReflection [] :=
  ⟨⟨.reflection, trivial⟩, RhoScopedInstanceReadout.reflection RhoSourceOutputPredicate.output null⟩

def visibleEvent : (RhoScopedEventPresheaf.events withReflection).obj closedWorld :=
  (visibleRoot, zero [])

theorem visible_event_target : join visibleEvent.1.target visibleEvent.2 = visible :=
  join_zero_right visible

def originCertificate (origin : Process []) (same : quote origin = quote visible) :
    (totalSpace (certificates withReflection quotedTargetOrigins)).obj closedWorld :=
  ⟨join visibleEvent.1.source visibleEvent.2,
    RhoScopedDependentEventFutures.introduce withReflection quotedTargetOrigins closedWorld visibleEvent
      ⟨origin, same.trans (congrArg quote visible_event_target).symm⟩⟩

theorem original_target_reaction :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
      (join visibleEvent.1.source visibleEvent.2) visible := by
  apply (step_iff_root_surrounding _ _).mpr
  exact ⟨visibleRoot, zero [], rfl, visible_event_target.symm⟩

theorem exact_origin_readout (origin : Process []) (same : quote origin = quote visible) :
    ((targetReadout withReflection quotedTargetOrigins).app closedWorld
      (originCertificate origin same)).2.val = origin := rfl

theorem equal_quotation_distinct_target_certificates :
    originCertificate visible rfl ≠ originCertificate suspended same_actual_name := by
  intro same
  have origins := congrArg (fun receipt :
      (totalSpace (certificates withReflection quotedTargetOrigins)).obj closedWorld =>
    show Process [] from
      ((targetReadout withReflection quotedTargetOrigins).app closedWorld receipt).2.val) same
  exact suspended_not_visible origins.symm

def freshName : world (S := sig) [Srt.nm] ⟶ world (S := sig) [] :=
  fresh (S := sig) [] Srt.nm (quoteRaw null)

theorem target_witnesses_remain_distinct_at_fresh_name :
    (totalSpace (certificates withReflection quotedTargetOrigins)).map freshName.val.op
      (originCertificate visible rfl) ≠
    (totalSpace (certificates withReflection quotedTargetOrigins)).map freshName.val.op
      (originCertificate suspended same_actual_name) :=
  fun same => equal_quotation_distinct_target_certificates
    (action_injective (totalSpace (certificates withReflection quotedTargetOrigins)) freshName same)

def nullEvent (count : Nat) : (RhoScopedEventPresheaf.events withReflection).obj closedWorld :=
  ((authoredReceipt count).val, zero [])

def ruleCertificate (count : Nat) :
    (totalSpace (certificates withReflection quotedTargetOrigins)).obj closedWorld :=
  ⟨join (nullEvent count).1.source (nullEvent count).2,
    RhoScopedDependentEventFutures.introduce withReflection quotedTargetOrigins closedWorld
      (nullEvent count) ⟨zero [], (congrArg quote (join_zero_right (zero []))).symm⟩⟩

theorem rule_certificate_event (count : Nat) :
    ((span withReflection).eventReadout quotedTargetOrigins).app closedWorld
      (ruleCertificate count) = nullEvent count :=
  supplied_event_recovered withReflection quotedTargetOrigins closedWorld (nullEvent count) _

theorem rule_certificates_injective : Function.Injective ruleCertificate := by
  intro first second same
  have events := congrArg (((span withReflection).eventReadout quotedTargetOrigins).app closedWorld) same
  rw [rule_certificate_event, rule_certificate_event] at events
  exact authoredReceipt_injective (Subtype.ext (congrArg Prod.fst events))

theorem same_target_certificate_all_rule_receipts (first second : Nat) :
    (targetReadout withReflection quotedTargetOrigins).app closedWorld (ruleCertificate first) =
      (targetReadout withReflection quotedTargetOrigins).app closedWorld (ruleCertificate second) := by
  change (⟨join (zero []) (zero []), ⟨zero [], _⟩⟩ :
    (totalSpace quotedTargetOrigins).obj closedWorld) = ⟨join (zero []) (zero []), ⟨zero [], _⟩⟩
  rfl

theorem rule_receipt_distinctions_survive_fresh_name : Function.Injective
    (fun count => (totalSpace (certificates withReflection quotedTargetOrigins)).map
      freshName.val.op (ruleCertificate count)) :=
  (action_injective (totalSpace (certificates withReflection quotedTargetOrigins)) freshName).comp
    rule_certificates_injective

end Mettapedia.OSLF.Framework.RhoScopedDependentEventFutureControls
