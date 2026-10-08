import Mettapedia.TypeTheory.PresheafScopedEvents
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInteractionCertificates
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversionControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionProtocolComparison
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Native scope and event certificates on an authored rho synchronization

Observer stages grow along the natural numbers. A name scope opens after
the initial stage. The nonconstant postcondition specifies the actual
communication result and retains a bounded witness whose available values
grow with the stage. Two selected equal messages reach the same endpoint
while their native certificates retain distinct occurrence positions.

The complete closed-rho occurrence presentation supplies a separate exact
comparison with the whole operational may-step predicate. Header selection
is a sound positional profile, not an assumed whole-theory presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FindingMindNativeInteraction

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.PresheafEventCertificates
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion HeaderInversionControls HeaderExecution
open HeaderInteractionCertificates ParameterizedRewriteSystem

abbrev Stages := Natᵒᵖ

def world (stage : Nat) : Stagesᵒᵖ := Opposite.op (Opposite.op stage)

def stageIndex (point : Stagesᵒᵖ) : Nat := point.unop.unop

def advance (stage : Nat) : world stage ⟶ world (stage + 1) :=
  (homOfLE (Nat.le_succ stage)).op.op

abbrev communication := presentation FreeSortContext.empty
abbrev states := communication.states (C := Stages)
abbrev events := communication.eventSpan (C := Stages)

def source : (theory FreeSortContext.empty).Term :=
  headerProcess duplicateMessages duplicateMessages_typed duplicateMessages_safe

def firstEvent : communication.Enabled source :=
  selectedEvent FreeSortContext.empty duplicateMessages duplicateMessages_typed
    duplicateMessages_safe firstMessage

def secondEvent : communication.Enabled source :=
  selectedEvent FreeSortContext.empty duplicateMessages duplicateMessages_typed
    duplicateMessages_safe secondMessage

theorem selected_endpoints_agree : firstEvent.target = secondEvent.target := rfl

/-- The postcondition holds at the actual target, with genuinely varying
future witness types, rather than a predicate of immediate source success. -/
def postcondition : DisplayedFamily states where
  obj point := PLift (point.2.val = firstMessage.contractum) × Fin (stageIndex point.1 + 1)
  map {first second} move := TypeCat.ofHom fun evidence =>
    ⟨⟨(congrArg Subtype.val (show first.2 = second.2 from move.property)).symm.trans
      evidence.1.down⟩,
      ⟨evidence.2.val, Nat.lt_of_lt_of_le evidence.2.isLt
        (Nat.succ_le_succ (leOfHom move.val.unop.unop))⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def firstCertificate (stage : Nat) (value : Fin (stage + 1)) :
    (events.certificates postcondition).obj ⟨world stage, source⟩ :=
  events.introduce postcondition (world stage) ⟨source, firstEvent⟩ ⟨⟨rfl⟩, value⟩

def secondCertificate (stage : Nat) (value : Fin (stage + 1)) :
    (events.certificates postcondition).obj ⟨world stage, source⟩ :=
  events.introduce postcondition (world stage) ⟨source, secondEvent⟩ ⟨⟨rfl⟩, value⟩

/-- An actual source event produces a certificate in the independent native
family at its actual communication endpoint. -/
theorem certificate_actual_step (stage : Nat) (value : Fin (stage + 1)) :
    ∃ target, (theory FreeSortContext.empty).Step source target ∧
      Nonempty (postcondition.obj ⟨world stage, target⟩) :=
  communication.certificate_sound postcondition (world stage) source
    (firstCertificate stage value)

/-- The result readout agrees although the complete occurrence receipts differ. -/
theorem equal_result_readouts (stage : Nat) (value : Fin (stage + 1)) :
    (events.resultReadout postcondition).app (world stage)
        ⟨source, firstCertificate stage value⟩ =
      (events.resultReadout postcondition).app (world stage)
        ⟨source, secondCertificate stage value⟩ := rfl

theorem distinct_occurrence_certificates (stage : Nat) (value : Fin (stage + 1)) :
    firstCertificate stage value ≠ secondCertificate stage value := by
  intro same
  have positions := congrArg (fun receipt : (events.certificates postcondition).obj
      ⟨world stage, source⟩ => receipt.val.1.2.evidence.selected.outputIndex) same
  exact Nat.zero_ne_one positions

/-- The endpoint postcondition does not already hold at the source. -/
theorem source_fails_postcondition (stage : Nat) :
    ¬ Nonempty (postcondition.obj ⟨world stage, source⟩) := by
  rintro ⟨evidence⟩
  exact (show source.val ≠ firstMessage.contractum by decide +kernel) evidence.1.down

def names : Stagesᵒᵖ ⥤ Type := (Functor.const Stagesᵒᵖ).obj Pattern

/-- A selected occurrence names its actual input channel. -/
def eventName : events.events ⟶ names where
  app _ := TypeCat.ofHom (fun event => event.2.evidence.selected.inputChannel)
  naturality _ _ _ := rfl

/-- A future-sensitive name predicate, closed under context extension. -/
def openScope : Subfunctor names where
  obj point := {name | name = channel ∧ 0 < stageIndex point}
  map move := fun _ admitted =>
    ⟨admitted.1, Nat.lt_of_lt_of_le admitted.2 (leOfHom move.unop.unop)⟩

abbrev scopedEvents := events.inScope eventName openScope

/-- The actual enabled reaction is initially outside the declared scope. -/
theorem no_scoped_certificate_initial :
    ¬ Nonempty ((scopedEvents.certificates postcondition).obj ⟨world 0, source⟩) := by
  intro certificate
  obtain ⟨_, _, admitted, _⟩ :=
    (events.scoped_nonempty_iff eventName openScope postcondition (world 0) source).mp certificate
  exact Nat.not_lt_zero 0 admitted.2

def openedCertificate :
    (scopedEvents.certificates postcondition).obj ⟨world 1, source⟩ :=
  scopedEvents.introduce postcondition (world 1)
    ⟨⟨source, firstEvent⟩, ⟨rfl, by decide⟩⟩ ⟨⟨rfl⟩, ⟨0, by decide⟩⟩

theorem opened_scope_retains_occurrence :
    (events.scopeErasure eventName openScope).app (world 1)
      ((scopedEvents.eventReadout postcondition).app (world 1)
        ⟨source, openedCertificate⟩) = ⟨source, firstEvent⟩ := rfl

theorem opened_scope_retains_target_evidence :
    (scopedEvents.resultReadout postcondition).app (world 1)
      ⟨source, openedCertificate⟩ = ⟨firstEvent.target, ⟨⟨rfl⟩, ⟨0, by decide⟩⟩⟩ := rfl

/-- Future transport keeps the selected occurrence and supplied witness value. -/
theorem future_readout (stage : Nat) (value : Fin (stage + 1)) :
    (events.resultReadout postcondition).app (world (stage + 1))
      ((totalSpace (events.certificates postcondition)).map (advance stage)
        ⟨source, firstCertificate stage value⟩) =
      ⟨firstEvent.target,
        ⟨⟨rfl⟩, ⟨value.val, Nat.lt_of_lt_of_le value.isLt (Nat.le_succ _)⟩⟩⟩ := rfl

/-- Every future stage admits an additional actual target certificate; it
cannot be obtained by transporting a certificate from the previous stage. -/
theorem new_certificate_not_previous (stage : Nat) :
    ¬ ∃ earlier : (events.certificates postcondition).obj ⟨world stage, source⟩,
      (totalSpace (events.certificates postcondition)).map (advance stage) ⟨source, earlier⟩ =
        ⟨source, firstCertificate (stage + 1) ⟨stage + 1, Nat.lt_succ_self _⟩⟩ := by
  rintro ⟨earlier, same⟩
  have values := congrArg (fun packet : (totalSpace (events.certificates postcondition)).obj
      (world (stage + 1)) => packet.2.val.2.2.val) same
  change earlier.val.2.2.val = stage + 1 at values
  exact (Nat.ne_of_lt earlier.val.2.2.isLt) values

/-- A syntactically visible reaction under an input guard is not an enabled
firing, at every supplied contextual depth. -/
theorem inert_guarded_cut {depth : Nat} {target : Pattern} :
    ¬ DerivedContextualStep.RhoStepAt depth suspendedReaction.pattern target :=
  input_guard_blocks_descent

abbrev completeRho := ReductionProtocolComparison.occurrenceInteraction

/-- The complete occurrence presentation interprets may-step with an
arbitrary dependent contextual postcondition on the established closed rho
carrier, rather than only the selected header profile. -/
theorem complete_native_mayStep
    (A : DisplayedFamily (completeRho.states (C := Stages)))
    (point : Stagesᵒᵖ) (program : LanguageDefGSLT.RhoProcess) :
    Nonempty (((completeRho.eventSpan (C := Stages)).certificates A).obj ⟨point, program⟩) ↔
      ∃ target, LanguageDefGSLT.rhoLanguageDefGSLT.Step program target ∧
        Nonempty (A.obj ⟨point, target⟩) :=
  completeRho.certificate_nonempty_iff
    ReductionProtocolComparison.occurrenceInteraction_complete A point program

/-- No dependent postcondition can turn the established inert dropped-name
process into an enabled operational event. -/
theorem inert_no_native_certificate
    (A : DisplayedFamily (completeRho.states (C := Stages))) (point : Stagesᵒᵖ) :
    ¬ Nonempty (((completeRho.eventSpan (C := Stages)).certificates A).obj
      ⟨point, LanguageDefRewriteSystem.closedFreeDrop⟩) := by
  intro certificate
  obtain ⟨target, step, _⟩ :=
    (complete_native_mayStep A point LanguageDefRewriteSystem.closedFreeDrop).mp certificate
  exact LanguageDefGSLT.closedFreeDrop_irreducible_in_gslt target step

/-- The source specification cannot be reused as a target certificate merely
because a genuine communication is available. -/
theorem wrong_target_specification_rejected (stage : Nat) :
    ¬ Nonempty (PLift (firstEvent.target.val = source.val) × Fin (stage + 1)) := by
  rintro ⟨evidence⟩
  exact (show firstEvent.target.val ≠ source.val by decide +kernel) evidence.1.down

end Mettapedia.OSLF.Framework.FindingMindNativeInteraction
