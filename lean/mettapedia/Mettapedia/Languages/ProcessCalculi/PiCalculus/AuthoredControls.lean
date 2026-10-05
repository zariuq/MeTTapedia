import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PresentationBoundary
/-!
# Controls for authored pi binding and execution

The controls distinguish captured and free received names, nested binder
indices, guarded-server retention, occurrence multiplicity, and synchronous
output continuations. They also separate raw engine endpoints from the
monoid quotient and the atomic-name fragment from process-valued messages
admitted by the one-sort presentation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open PiCalcInstance
open Synchronous

def captureExchange : Process :=
  .par (.input "a" "x" (.nu "z" (.output "x" "z"))) (.output "a" "z")

theorem capture_exchange_exact_result :
    piCalcReducts 1 (piToPattern captureExchange) =
      [.collection .hashBag [.apply "PiNu" [.lambda none
        (.apply "PiOut" [.fvar "z", .bvar 0])]] none] := by
  decide +kernel

theorem capture_exchange_wrong_result_rejected :
    .collection .hashBag [.apply "PiNu" [.lambda none
      (.apply "PiOut" [.bvar 0, .bvar 0])]] none ∉
      piCalcReducts 1 (piToPattern captureExchange) := by
  decide +kernel

def boundChannelExchange : Process :=
  .nu "x" (.par (.input "x" "y" (.output "y" "x")) (.output "x" "z"))

theorem restriction_keeps_outer_bound_index :
    piCalcReducts 2 (piToPattern boundChannelExchange) =
      [.apply "PiNu" [.lambda none (.collection .hashBag
        [.apply "PiOut" [.fvar "z", .bvar 0]] none)]] := by
  decide +kernel

theorem restriction_wrong_received_name_rejected :
    .apply "PiNu" [.lambda none (.collection .hashBag
      [.apply "PiOut" [.bvar 0, .bvar 0]] none)] ∉
      piCalcReducts 2 (piToPattern boundChannelExchange) := by
  decide +kernel

def shadowServer : Process := .replicate "x" "x" (.output "x" "a")
def serverExchange : Process := .par shadowServer (.output "x" "z")
def serverResult : Pattern := .collection .hashBag
  [piToPattern (.output "z" "a"), piToPattern shadowServer] none

theorem server_retains_original_subject :
    piCalcReducts 1 (piToPattern serverExchange) = [serverResult] := by
  decide +kernel

theorem changed_server_subject_rejected :
    .collection .hashBag [piToPattern (.output "z" "a"),
      piToPattern (.replicate "z" "x" (.output "x" "a"))] none ∉
      piCalcReducts 1 (piToPattern serverExchange) := by
  decide +kernel

theorem duplicate_messages_keep_occurrence_multiplicity :
    (piCalcReducts 1 (piToPattern
      (.par serverExchange (.output "x" "z")))).length = 2 := by
  decide +kernel

theorem server_needs_a_message (target : Pattern) :
    ¬ Step (engineBasePremises RelationEnv.empty) piCalc (piToPattern shadowServer) target :=
  PresentationBoundary.piCalc_no_internal_step_from_application "PiRep" _ (by decide) target

def outputContinuation : Pattern :=
  .apply "PiOutK" [.fvar "k", .fvar "a", .apply "PiNil" []]
def syncServerBody : Pattern :=
  .apply "PiOutK" [.bvar 0, .fvar "w", .apply "PiNil" []]
def syncServer : Pattern := .apply "PiRep" [.fvar "x", .lambda none syncServerBody]

theorem synchronous_server_releases_output_continuation :
    Step (engineBasePremises RelationEnv.empty) piSyncCalc
      (.collection .hashBag [syncServer,
        .apply "PiOutK" [.fvar "x", .fvar "z", outputContinuation]] none)
      (.collection .hashBag [
        .apply "PiOutK" [.fvar "z", .fvar "w", .apply "PiNil" []],
        syncServer, outputContinuation] none) := by
  simpa [syncServer, syncServerBody, instantiateBVar, instantiateBVarAt, liftBVars] using
    piSyncRepComm_step (.fvar "x") syncServerBody (.fvar "z") outputContinuation []

theorem synchronous_server_cannot_discard_output_continuation :
    .collection .hashBag [
      .apply "PiOutK" [.fvar "z", .fvar "w", .apply "PiNil" []], syncServer] none ∉
      rewriteAt (engineBasePremises RelationEnv.empty) piSyncCalc 1
        (.collection .hashBag [syncServer,
          .apply "PiOutK" [.fvar "x", .fvar "z", outputContinuation]] none) := by
  decide +kernel

theorem named_exchange_reaches_inaction_modulo_declared_laws :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern PresentationBoundary.exchange) (piToPattern .nil) := by
  simpa [PresentationBoundary.exchange, Process.substitute_nil] using
    piComm_named_semantic_step "a" "x" "b" .nil

theorem raw_exchange_cannot_reach_bare_inaction :
    ¬ Step (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern PresentationBoundary.exchange) (piToPattern .nil) :=
  PresentationBoundary.piCalc_no_internal_step_to_inaction _

theorem typed_closing_uses_the_declared_name_sort :
    HasType piCalc piNameContext [.base "Proc"] (.bvar 0) (.base "Proc") := by
  simpa [closeFVar] using
    (show HasType piCalc piNameContext [] (.fvar "x") (.base "Proc") from
      .fvar rfl).closeFVar "x" (.base "Proc") rfl

theorem wrong_sort_for_closed_name_rejected :
    ¬ HasType piCalc piNameContext [.base "Other"] (.bvar 0) (.base "Proc") := by
  intro typed
  cases typed with
  | bvar present => simp at present

/-- The one-sort authored presentation can send a process-valued datum. -/
theorem authored_process_valued_message_executes :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag [
        .apply "PiInp" [.fvar "x", .lambda none (.bvar 0)],
        .apply "PiOut" [.fvar "x", .apply "PiNil" []]] none)
      (.collection .hashBag [.apply "PiNil" []] none) := by
  simpa [instantiateBVar, instantiateBVarAt, liftBVars] using
    piComm_step (.fvar "x") (.bvar 0) (.apply "PiNil" []) []

/-- Such an output is outside the image of atomic-name processes. -/
theorem process_valued_output_not_named_image :
    ¬ ∃ P : Process, piToPattern P = .apply "PiOut" [.fvar "x", .apply "PiNil" []] := by
  rintro ⟨P, encoded⟩
  cases P with
  | par P Q => simp only [piToPattern, piPar_components] at encoded; cases encoded
  | output channel datum => simp [piToPattern] at encoded
  | _ => simp [piToPattern] at encoded

end Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredControls
