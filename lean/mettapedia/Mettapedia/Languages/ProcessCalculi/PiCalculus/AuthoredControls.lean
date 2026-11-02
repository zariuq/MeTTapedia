import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PresentationBoundary
/-!
# Controls for authored pi binding and execution

The controls distinguish captured and free received names, nested binder
indices, a server receiving only through its unfolding and keeping its subject,
occurrence multiplicity, and synchronous output continuations. They also separate raw engine endpoints from the
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

/-- A server and a message as its unfolding presents them: the copy `x(x).x⟨a⟩` beside the server and `x⟨z⟩`. -/
def unfoldedExchange (messages : List Pattern) : Pattern := .collection .hashBag
  ([piToPattern (.input "x" "x" (.output "x" "a")), piToPattern shadowServer] ++ messages) none

/-- **A server receives through its unfolding**: the raw rules do not fire on a replicated server beside a message,
which communicates only once the law `!P = {P, !P}` puts a copy beside it. -/
theorem server_waits_for_its_unfolding :
    piCalcReducts 1 (piToPattern serverExchange) = [] := by
  decide +kernel

theorem server_retains_original_subject :
    piCalcReducts 1 (unfoldedExchange [piToPattern (.output "x" "z")]) = [serverResult] := by
  decide +kernel

theorem changed_server_subject_rejected :
    .collection .hashBag [piToPattern (.output "z" "a"),
      piToPattern (.replicate "z" "x" (.output "x" "a"))] none ∉
      piCalcReducts 1 (unfoldedExchange [piToPattern (.output "x" "z")]) := by
  decide +kernel

theorem duplicate_messages_keep_occurrence_multiplicity :
    (piCalcReducts 1 (unfoldedExchange
      [piToPattern (.output "x" "z"), piToPattern (.output "x" "z")])).length = 2 := by
  decide +kernel

theorem server_needs_a_message (target : Pattern) :
    ¬ Step (engineBasePremises RelationEnv.empty) piCalc (piToPattern shadowServer) target :=
  PresentationBoundary.piCalc_no_internal_step_from_application "PiRep" _ (by decide) target

def outputContinuation : Pattern :=
  .apply "PiOutK" [.fvar "k", .fvar "a", .apply "PiNil" []]
def syncServerBody : Pattern :=
  .apply "PiOutK" [.bvar 0, .fvar "w", .apply "PiNil" []]
/-- The input `x(y).y⟨w⟩.0` a synchronous server replicates. -/
def syncServerInput : Pattern := .apply "PiInp" [.fvar "x", .lambda none syncServerBody]
def syncServer : Pattern := .apply "PiRep" [syncServerInput]

/-- **A synchronous server receives through its unfolding**: the raw rules do not fire on a replicated server beside
an output, which communicates only once the law `!P = {P, !P}` puts a copy beside it. -/
theorem synchronous_server_waits_for_its_unfolding :
    rewriteAt (engineBasePremises RelationEnv.empty) piSyncCalc 1
      (.collection .hashBag [syncServer, .apply "PiOutK" [.fvar "x", .fvar "z", outputContinuation]] none) = [] := by
  decide +kernel

/-- **The server's copy receives and the output's continuation is released**, the server staying beside them. -/
theorem synchronous_server_releases_output_continuation :
    Step (engineBasePremises RelationEnv.empty) piSyncCalc
      (.collection .hashBag [syncServerInput,
        .apply "PiOutK" [.fvar "x", .fvar "z", outputContinuation], syncServer] none)
      (.collection .hashBag [
        .apply "PiOutK" [.fvar "z", .fvar "w", .apply "PiNil" []],
        outputContinuation, syncServer] none) := by
  simpa [syncServerInput, syncServerBody, instantiateBVar, instantiateBVarAt, liftBVars] using
    piSyncComm_step (.fvar "x") syncServerBody (.fvar "z") outputContinuation [syncServer]

theorem synchronous_server_cannot_discard_output_continuation :
    .collection .hashBag [
      .apply "PiOutK" [.fvar "z", .fvar "w", .apply "PiNil" []], syncServer] none ∉
      rewriteAt (engineBasePremises RelationEnv.empty) piSyncCalc 1
        (.collection .hashBag [syncServerInput,
          .apply "PiOutK" [.fvar "x", .fvar "z", outputContinuation], syncServer] none) := by
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
    HasType piCalc piNameContext [.base "Name"] (.bvar 0) (.base "Name") := by
  simpa [closeFVar] using
    (show HasType piCalc piNameContext [] (.fvar "x") (.base "Name") from
      .fvar rfl).closeFVar "x" (.base "Name") rfl

theorem wrong_sort_for_closed_name_rejected :
    ¬ HasType piCalc piNameContext [.base "Other"] (.bvar 0) (.base "Name") := by
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
