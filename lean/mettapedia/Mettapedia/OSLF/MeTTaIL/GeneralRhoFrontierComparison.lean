import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralRhoExecution

/-!
# Original reflective COMM in an exhaustive general frontier

Every derived rho body, payload and parallel remainder in the selected
quotation-sealed domain produces an actual general-frontier receipt. Its
source body and matcher origin remain exact, and its target is the
independent semantic substitution from LanguageDefAdequacy into the body with
its quotations of drops resolved; on the literal-quotation fiber, into the body
itself. The closed
ambient comparison allows arbitrary intervening input binders in the body.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open DerivedPresentationSyntax ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy

def frontierRequest (bound : List TypeExpr) (pattern : Pattern) : GeneralOccurrenceFrontier.Request :=
  .fromSnapshot snapshot permissions bound (.base "Proc") pattern

theorem frontier_profile_checked :
    GeneralRhoFamily.check plan.snapshot plan.permissions = true :=
  GeneralRhoFamily.original_comm_profile_recognized

theorem source_frontier_admitted {bound : List TypeExpr} {pattern : Pattern}
    (typed : OpenPatternWellSorted language snapshot.free bound (.base "Proc") pattern) :
    GeneralOccurrenceFrontier.Admitted (frontierRequest bound pattern) :=
  GeneralOccurrenceFrontier.fromSnapshot_admitted compilation_complete typed.1 typed.2.2.1 typed.2.2.2

theorem source_frontier_complete {bound : List TypeExpr} {pattern : Pattern}
    (typed : OpenPatternWellSorted language snapshot.free bound (.base "Proc") pattern) :
    GeneralOccurrenceFrontier.complete (frontierRequest bound pattern)
      (GeneralOccurrenceFrontier.finish _ (source_frontier_admitted typed)) = true :=
  GeneralOccurrenceFrontier.finish_complete_of_local_resolution (source_frontier_admitted typed)
    (GeneralOccurrenceFrontier.rho_equation_resolution (source_frontier_admitted typed) frontier_profile_checked)
    (GeneralOccurrenceFrontier.rho_rule_resolution (source_frontier_admitted typed) frontier_profile_checked)

theorem source_frontier_certificate {bound : List TypeExpr} {pattern : Pattern}
    (typed : OpenPatternWellSorted language snapshot.free bound (.base "Proc") pattern) :
    GeneralOccurrenceFrontier.checkCertificate (frontierRequest bound pattern)
      (GeneralOccurrenceFrontier.finish _ (source_frontier_admitted typed)) = true :=
  GeneralOccurrenceFrontier.finish_certificate_of_local_resolution (source_frontier_admitted typed)
    (GeneralOccurrenceFrontier.rho_equation_resolution (source_frontier_admitted typed) frontier_profile_checked)
    (GeneralOccurrenceFrontier.rho_rule_resolution (source_frontier_admitted typed) frontier_profile_checked)

/-- The target of the root receipt is the paper-facing COMM result of the body
with its quotations of drops resolved. -/
theorem rootReceipt_target_resolved {channel body payload : Pattern} {rest : List Pattern}
    (bodyTyped : ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"] body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] payload)
    (restTyped : ProcListWellSorted rhoReflectivePresentation (fun _ => none) [] rest) :
    (rootReceipt [] channel body payload rest).target =
      .collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: rest) none := by
  have bodyOpen := derived_process_open bodyTyped
  have payloadOpen := derived_process_open payloadTyped
  have restTypes := derived_processes_typed restTyped
  have original := reflective_reduct_resolved (channel := channel)
    bodyTyped payloadTyped restTypes.isWellScopedListAt
  have actual := reflective_reduct (ambient := 0) (channel := channel)
    (show body.isWellScopedAt 1 = true from bodyOpen.2.2.2)
    (show payload.isWellScopedAt 0 = true from payloadOpen.2.2.2)
    (show Pattern.isWellScopedListAt 0 rest = true from restTypes.isWellScopedListAt)
  rw [actual] at original
  change Pattern.collection .hashBag (reflectiveBody body payload :: rest) none = _
  exact Option.some.inj original

theorem arbitrary_original_comm_in_actual_frontier_resolved {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : NameWellSorted rhoReflectivePresentation (fun _ => none) [] channel)
    (bodyTyped : ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"] body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] payload)
    (restTyped : ProcListWellSorted rhoReflectivePresentation (fun _ => none) [] rest) :
    let query := frontierRequest [] (source channel body payload rest)
    ∃ fuel,
      GeneralOccurrenceFrontier.complete query
        (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)) = true ∧
      GeneralOccurrenceFrontier.checkCertificate query
        (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)) = true ∧
      ∃ answer ∈ (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)).answers,
        answer.val.representative = source channel body payload rest ∧
        answer.val.firing = rootReceipt [] channel body payload rest ∧
        answer.val.target =
          .collection .hashBag (semanticCommSubst (ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: rest) none := by
  have channelOpen := derived_name_open channelTyped
  have bodyOpen := derived_process_open bodyTyped
  have payloadOpen := derived_process_open payloadTyped
  have restTypes := derived_processes_typed restTyped
  have restRepresentation := derived_processes_represented restTyped
  have valid := root_receipt_valid channelOpen bodyOpen sealed
    (derived_names_admitted bodyTyped sealed) payloadOpen restTypes restRepresentation
  have represented := source_represented ⟨channelOpen.2.1, channelOpen.2.2.1⟩
    ⟨bodyOpen.2.1, bodyOpen.2.2.1⟩ ⟨payloadOpen.2.1, payloadOpen.2.2.1⟩ restRepresentation
  have sourceType := source_typed channelOpen.1 bodyOpen.1 payloadOpen.1 restTypes
  have sourceOpen : OpenPatternWellSorted language snapshot.free [] (.base "Proc")
      (source channel body payload rest) :=
    ⟨sourceType, represented.1, represented.2, sourceType.isWellScopedAt⟩
  let query := frontierRequest [] (source channel body payload rest)
  have admitted : GeneralOccurrenceFrontier.Admitted query := source_frontier_admitted sourceOpen
  have checked : GeneralOccurrenceFrontier.checkCertificate query
      (GeneralOccurrenceFrontier.finish query admitted) = true := source_frontier_certificate sourceOpen
  have rootSame : query.root = source channel body payload rest :=
    Pattern.eraseBinderMetadata_eq_self_of_canonical represented.1
  obtain ⟨answer, member, representative, firing⟩ :=
    GeneralOccurrenceFrontier.certified_physical_occurrence admitted checked
      (source channel body payload rest) (rootSame ▸ .refl _) (rootReceipt [] channel body payload rest) valid
  have comparison := rootReceipt_target_resolved (channel := channel) bodyTyped payloadTyped restTyped
  obtain ⟨fuel, actual⟩ := GeneralOccurrenceFrontier.finish_actual_run query admitted
  refine ⟨fuel, ?_, ?_, answer, ?_, representative, firing, ?_⟩
  · rw [actual]
    exact source_frontier_complete sourceOpen
  · rw [actual]
    exact checked
  · rw [actual]
    exact member
  · change answer.val.firing.target = _
    rw [firing]
    exact comparison

/-- On a body in the literal-quotation fiber the frontier target is the
paper-facing COMM result. -/
theorem arbitrary_original_comm_in_actual_frontier {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : NameWellSorted rhoReflectivePresentation (fun _ => none) [] channel)
    (bodyTyped : ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"] body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true)
    (fiber : ReflectiveCoherent.quotesLiteral rhoReflectivePresentation body = true)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation (fun _ => none) [] payload)
    (restTyped : ProcListWellSorted rhoReflectivePresentation (fun _ => none) [] rest) :
    let query := frontierRequest [] (source channel body payload rest)
    ∃ fuel,
      GeneralOccurrenceFrontier.complete query
        (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)) = true ∧
      GeneralOccurrenceFrontier.checkCertificate query
        (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)) = true ∧
      ∃ answer ∈ (GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)).answers,
        answer.val.representative = source channel body payload rest ∧
        answer.val.firing = rootReceipt [] channel body payload rest ∧
        answer.val.target = .collection .hashBag (semanticCommSubst body payload :: rest) none := by
  have resolved := arbitrary_original_comm_in_actual_frontier_resolved channelTyped bodyTyped sealed
    payloadTyped restTyped
  rwa [semanticCommSubst_resolveQuotes_of_fiber bodyTyped fiber payloadTyped] at resolved

#print axioms arbitrary_original_comm_in_actual_frontier
#print axioms arbitrary_original_comm_in_actual_frontier_resolved
#print axioms source_frontier_complete

end Mettapedia.OSLF.MeTTaIL.GeneralRho
