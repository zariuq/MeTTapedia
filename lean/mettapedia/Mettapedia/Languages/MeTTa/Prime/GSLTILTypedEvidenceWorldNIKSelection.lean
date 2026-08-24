import Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms
import Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKTransport

/-!
# NIK selection derived from typed proof-world routes

A typed evidence route already carries the executable internal action, its
agreement with structural language transport, and the dependent action on
elaboration evidence.  Restricting that route to an authored command therefore
constructs the complete-world transport consumed by NIK; no unrelated runtime
function or route-name dispatch is required.

For a complete-history request, the existing maximal-native selection theorem
chooses the full-world face.  Current activation executes the carried map
directly.  Reflection is available only when the typed route separately earns
the corresponding capability, and revision staleness preserves the original
source history for fallback.

The construction also lifts pointwise to every program in a finite authored
route signature.  Thus primitive capabilities compose through the same typed
free-path syntax that determines structural language transport.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldNIKSelection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes.TypedEvidenceRoute
open Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature
open Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKSelection
open Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKTransport
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms.SignatureEvidenceInterpretation

variable {sourcePresentation targetPresentation : ValidatedLanguageDef}
variable {source : EvidenceProfileOver sourcePresentation}
  {target : EvidenceProfileOver targetPresentation}

/-! ## One typed route, restricted to one authored command -/

/-- The NIK complete-world transport is derived from the typed route at the
requested command. -/
abbrev routeTransport (route : TypedEvidenceRoute source target)
    (command : source.profile.Command) :
    EvidenceWorldMap source.profile command target.profile
      (route.mapCommand command) :=
  route.atCommand command

/-- Current maximal-native execution runs the route's retained proof-world
map both as semantics and as the requested complete-world observation. -/
@[simp] theorem current_route_run
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (history : List (source.profile.World command)) :
    (active (routeTransport route command)).runPrepared
        (prepared (routeTransport route command) history)
        (requestedCompleteWorldPolicy (routeTransport route command)) =
      ((route.atCommand command).mapHistory history,
        (route.atCommand command).mapHistory history) :=
  current_run_transports_semantics_and_worlds
    (routeTransport route command) history

/-- A typed route that earns world reflection also earns injectivity of the
selected complete-world native operation. -/
theorem selected_route_operation_injective
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (reflects : route.ReflectsWorlds) :
    Function.Injective
      ((completeWorldTransportRequest (routeTransport route command))
        |>.toCapabilityRequest
        |>.strongestOperation
          (completeWorldTransportSelection (routeTransport route command))).run :=
  selected_operation_injective (routeTransport route command)
    (reflects command)

/-- Revision change refuses native activation and retains the untransported
source history for ordinary fallback. -/
theorem stale_route_preserves_source
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (history : List (source.profile.World command)) :
    (¬ (selectedAt (routeTransport route command)).Active true) /\
      (prepared (routeTransport route command) history).fallback =
        (history, history) :=
  stale_refuses_transport_and_preserves_source
    (routeTransport route command) history

/-! ## Every intrinsic program in a finite authored route signature -/

variable {signature : Signature}

/-- Interpret a typed route program and restrict the resulting compositional
proof-world route to one source command. -/
abbrev programTransport
    (interpretation : SignatureEvidenceInterpretation signature)
    {sourceLanguage targetLanguage : signature.Language}
    (program : signature.Program sourceLanguage targetLanguage)
    (command : (interpretation.profileAt sourceLanguage).profile.Command) :=
  (interpretation.mapProgram program).atCommand command

/-- NIK's current execution theorem consequently holds for every intrinsic
typed route program, not only for primitive generators. -/
@[simp] theorem current_program_run
    (interpretation : SignatureEvidenceInterpretation signature)
    {sourceLanguage targetLanguage : signature.Language}
    (program : signature.Program sourceLanguage targetLanguage)
    (command : (interpretation.profileAt sourceLanguage).profile.Command)
    (history : List
      ((interpretation.profileAt sourceLanguage).profile.World command)) :
    (active (programTransport interpretation program command)).runPrepared
        (prepared (programTransport interpretation program command) history)
        (requestedCompleteWorldPolicy
          (programTransport interpretation program command)) =
      ((programTransport interpretation program command).mapHistory history,
        (programTransport interpretation program command).mapHistory history) :=
  current_run_transports_semantics_and_worlds
    (programTransport interpretation program command) history

/-- Primitive reflection proofs compose through a program and license the
selected complete-world operation as an injective realization. -/
theorem selected_program_operation_injective
    (interpretation : SignatureEvidenceInterpretation signature)
    (generatorReflects : interpretation.GeneratorReflects)
    {sourceLanguage targetLanguage : signature.Language}
    (program : signature.Program sourceLanguage targetLanguage)
    (command : (interpretation.profileAt sourceLanguage).profile.Command) :
    Function.Injective
      ((completeWorldTransportRequest
          (programTransport interpretation program command))
        |>.toCapabilityRequest
        |>.strongestOperation
          (completeWorldTransportSelection
            (programTransport interpretation program command))).run := by
  apply selected_operation_injective
  exact (interpretation.mapProgram_reflects generatorReflects program).2 command

/-! ## Positive and negative selection controls -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms.SignatureEvidenceInterpretation.Canary

abbrev richPromoteTransport := richRoute.atCommand ()
abbrev collapsePromoteTransport := collapseRoute.atCommand ()

/-- The strongest current face retains both proof histories and their order. -/
theorem rich_current_retains_both_histories :
    (active richPromoteTransport).runPrepared
        (prepared richPromoteTransport [firstWorld, secondWorld])
        (requestedCompleteWorldPolicy richPromoteTransport) =
      ([firstWorld, secondWorld], [firstWorld, secondWorld]) :=
  rfl

/-- Reflection earned by the rich route reaches the selected native
operation. -/
theorem rich_selected_operation_injective :
    Function.Injective
      ((completeWorldTransportRequest richPromoteTransport)
        |>.toCapabilityRequest
        |>.strongestOperation
          (completeWorldTransportSelection richPromoteTransport)).run :=
  selected_operation_injective richPromoteTransport
    (richRoute_reflectsWorlds ())

/-- The equally sound collapsing route remains non-reflecting after strongest
selection; NIK does not invent a capability absent from the route. -/
theorem collapse_selected_operation_not_injective :
    ¬ Function.Injective
      ((completeWorldTransportRequest collapsePromoteTransport)
        |>.toCapabilityRequest
        |>.strongestOperation
          (completeWorldTransportSelection collapsePromoteTransport)).run := by
  intro injective
  change Function.Injective collapsePromoteTransport.mapHistory at injective
  have sourceSingletonsDistinct : [firstWorld] ≠ [secondWorld] := by
    intro equal
    exact sourceWorlds_distinct (List.cons.inj equal).1
  exact sourceSingletonsDistinct (injective (by rfl))

/-- Stale fallback still distinguishes the two source histories that the
forward collapsing route would identify. -/
theorem collapse_stale_preserves_distinct_sources :
    (prepared collapsePromoteTransport [firstWorld]).fallback ≠
      (prepared collapsePromoteTransport [secondWorld]).fallback := by
  intro equal
  exact sourceWorlds_distinct
    (List.cons.inj (congrArg Prod.fst equal)).1

end Canary

#print axioms current_route_run
#print axioms selected_route_operation_injective
#print axioms stale_route_preserves_source
#print axioms current_program_run
#print axioms selected_program_operation_injective
#print axioms Canary.rich_current_retains_both_histories
#print axioms Canary.rich_selected_operation_injective
#print axioms Canary.collapse_selected_operation_not_injective
#print axioms Canary.collapse_stale_preserves_distinct_sources

end Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldNIKSelection
