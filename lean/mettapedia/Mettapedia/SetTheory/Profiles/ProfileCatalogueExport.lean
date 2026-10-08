import Mettapedia.SetTheory.Profiles.ProfileCatalogue
import Mettapedia.SetTheory.Profiles.ProfileChoiceHost
import Mettapedia.Logic.KernelFoundationManifest

/-!
# Inspectable catalogue export

The export keeps all four evidence stages and each evidence item's exact
scope and checking source. Local declarations are audited from their checked
types and transitive dependencies. The final MeTTa value is informational
catalogue data; it neither selects a profile nor adopts an assumption.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileCatalogueExport

open Lean Elab Command Meta
open ProfileCatalogue
open Mettapedia.Logic.KernelFoundationManifest

def sourceJson (source : Source) : Json := Json.mkObj [
  ("kind", .str source.kind), ("reference", .str source.reference),
  ("anchor", .str source.anchor)]

def evidenceJson (evidence : Evidence) : Json := Json.mkObj [
  ("stage", .str evidence.stage.spelling), ("scope", .str evidence.scope.spelling),
  ("source", sourceJson evidence.source), ("statement", .str evidence.statement),
  ("commitments", .arr (evidence.commitments.map Json.str).toArray),
  ("modelChecking", .str (if evidence.stage != .constructedModel then "not-model-evidence"
    else if evidence.source.localDeclaration?.isSome then "local-kernel-reference"
    else "reported-external-construction"))]

def choiceJson (choice : ChoiceRecord) : Json := Json.mkObj [
  ("level", .str choice.level.spelling), ("stance", .str choice.stance.spelling),
  ("source", match choice.evidence with | some source => sourceJson source | none => .null),
  ("statement", .str choice.statement)]

def profileJson (profile : Profile) : Json := Json.mkObj [
  ("kind", .str "profile"), ("schemaVersion", toJson (1 : Nat)),
  ("id", .str profile.id.spelling), ("signature", .str profile.signature),
  ("statuses", Json.mkObj (stages.map fun stage =>
    (stage.spelling, .arr ((profile.atStage stage).map evidenceJson).toArray))),
  ("reportedComparisons", .arr (profile.reportedComparisons.map evidenceJson).toArray),
  ("choiceSelection", match profile.choiceSelection with
    | some choice => .str choice.spelling | none => .null),
  ("choice", .arr (profile.choice.map choiceJson).toArray),
  ("readableNotes", .arr (profile.bounds.map Json.str).toArray),
  ("nativeAssumptionAuthority", .bool false)]

private def quote (value : String) : String := (Json.str value).compress

private def node (head : String) (fields : List String) : String :=
  "(" ++ String.intercalate " " (head :: fields) ++ ")"

def sourceMetta (source : Source) : String :=
  node "Source" [source.kind, quote source.reference, quote source.anchor]

def evidenceMetta (evidence : Evidence) : String := node "Evidence" [
  node "Scope" [evidence.scope.spelling], sourceMetta evidence.source,
  node "Statement" [quote evidence.statement],
  node "Commitments" (evidence.commitments.map quote)]

def choiceMetta (choice : ChoiceRecord) : String := node "ChoiceLevel" [
  choice.level.spelling, choice.stance.spelling,
  match choice.evidence with | some source => sourceMetta source | none => "NoEvidence",
  quote choice.statement]

def profileMetta (profile : Profile) : String := node "Profile" [
  profile.id.spelling, node "Signature" [quote profile.signature],
  node "Statuses" (stages.map fun stage =>
    node "Status" (stage.spelling :: (profile.atStage stage).map evidenceMetta)),
  node "ReportedComparisons" (profile.reportedComparisons.map evidenceMetta),
  node "SelectedChoice" [match profile.choiceSelection with
    | some choice => choice.spelling | none => "unspecified"],
  node "Choice" (profile.choice.map choiceMetta),
  node "Bounds" (profile.bounds.map quote)]

def catalogueMetta : String := node "SetTheoryCatalogue" [
  node "SchemaVersion" ["1"], node "Informational" ["NoAssumptionAuthority"],
  node "BareDefault" [bareDefault.spelling],
  node "TypeTheoreticPiSigmaChoice" [
    "theorem",
    quote (``ProfileChoice.piSigmaChoice_exists).toString,
    quote "The premise supplies actual Sigma witnesses; extensional Choice remains a separate axis."],
  node "Profiles" (catalogue.map profileMetta)]

def localReferences : List Name :=
  (catalogue.flatMap fun profile =>
    (profile.evidence.filterMap fun evidence => evidence.source.localDeclaration?) ++
      (profile.choice.filterMap fun choice => choice.evidence.bind Source.localDeclaration?)) ++
  [``ProfileChoice.piSigmaChoice, ``ProfileChoice.piSigmaChoice_exists,
    ``ProfileChoice.witnesses_roundTrip, ``ProfileChoice.selection_roundTrip,
    ``ProfileChoice.erase_witnesses,
    ``ProfileChoice.witnessedDependentRun,
    ``ProfileChoice.witnessedDependentReceipt,
    ``ProfileChoice.witnessedDependentRun_initial,
    ``ProfileChoice.Controls.growing_family_choice,
    ``ProfileChoice.Controls.growing_family_retains_evidence,
    ``ProfileChoice.Controls.receipt_choice_does_not_descend,
    ``ProfileChoice.Controls.erased_inhabitedness_does_not_recover_original,
    ``ProfileChoiceHost.extractMerelyInhabited,
    ``ProfileChoiceHost.chooseFromMerelyInhabited,
    ``ProfileChoiceHost.host_choice_assembles_merely_inhabited,
    ``ProfileChoice.extensional_pair_choice_implies_excluded_middle,
    ``ProfileChoice.no_extensional_pair_selector_of_no_excluded_middle,
    ``ProfileChoice.universal_set_refutes_russell_separation,
    ``ProfileChoice.universal_set_refutes_separation,
    ``ProfileChoiceModels.wellFounded_pair_choice_implies_excluded_middle,
    ``ProfileChoiceModels.hyperset_pair_choice_implies_excluded_middle,
    ``ProfileChoiceModels.universal_set_refutes_common_bounded_instance,
    ``ProfileChoiceModels.common_bounded_instance_has_adoption,
    ``ProfileChoiceModels.wellFounded_has_no_universal_set,
    ``ProfileChoiceModels.hyperset_has_no_universal_set,
    ``lem_of_choice, ``lem_of_pairSubsetChoice,
    ``ProfileCatalogue.primeCommon, ``ProfileCatalogue.foundationCommon,
    ``ProfileCatalogue.classicalCommon, ``ProfileCatalogue.classicalFoundationCommon,
    ``ProfileCatalogue.foundation, ``ProfileCatalogue.afa, ``ProfileCatalogue.safa,
    ``ProfileCatalogue.fafa, ``ProfileCatalogue.bafa, ``ProfileCatalogue.nf,
    ``ProfileCatalogue.nfu, ``ProfileCatalogue.gpkPlusInfinity, ``ProfileCatalogue.hol,
    ``ProfileCatalogue.megalodonHotg, ``ProfileCatalogue.hotgTheory]

def finiteFragmentReferences : List Name :=
  [``ProfileCatalogue.native_replay_has_no_local_credit,
    ``ProfileCatalogue.finite_fragment_has_no_full_model_credit,
    ``ProfileCatalogue.raw_unfolding_has_no_canonical_scott_credit,
    ``ProfileCatalogue.afa_retains_finite_execution,
    ``ProfileCatalogue.foundation_retains_finite_execution,
    ``ProfileCatalogue.safa_retains_finite_execution,
    ``ProfileCatalogue.safa_retains_raw_diagnostic,
    ``ProfileCatalogue.finite_executable_evidence_has_no_local_credit,
    ``ProfileCatalogue.canonical_scott_certificate_is_not_full_model,
    ``ProfileCatalogue.raw_certificate_is_not_canonical_scott]

/-- Audit all references, not just the names cited by mathematical models.
Hypotheses remain in the complete types. A rejected unsafe declaration or
admission fails generation before any catalogue is emitted. -/
def emitCatalogue : CommandElabM Unit := do
  for profile in catalogue do
    for evidence in profile.atStage .checkedInterpretation do
      unless evidence.source.hasInterpretationChecker do
        throwError "checked interpretation for {profile.id.spelling} has no kernel checker"
    for evidence in profile.reportedComparisons do
      if evidence.source.hasInterpretationChecker then
        throwError "reported comparison for {profile.id.spelling} has an ambiguous checker classification"
  let checking ← liftTermElabM checkingEnvironment
  let names := (localReferences ++ finiteFragmentReferences).eraseDups
  let audited ← liftTermElabM do
    names.mapM fun name => do
      let info ← getConstInfo name
      unless hasCheckedBody info do
        throwError "catalogue reference {name} does not have a safe checked body"
      let dependencies ← collectAxioms name
      if dependencies.contains ``sorryAx then
        throwError "catalogue reference {name} depends on an admission"
      return Json.mkObj [
        ("kind", .str "local-reference"), ("reference", .str name.toString),
        ("manifest", ← declarationManifest name)]
  liftIO (IO.println (Json.mkObj [
    ("kind", .str "checking-environment"), ("checkingEnvironment", checking)]).compress)
  for row in audited do
    liftIO (IO.println row.compress)
  for profile in catalogue do
    liftIO (IO.println (profileJson profile).compress)
  liftIO (IO.println (Json.mkObj [
    ("kind", .str "type-theoretic-choice"), ("form", .str "PiSigma"),
    ("proof", .str (``ProfileChoice.piSigmaChoice_exists).toString),
    ("computedWitnesses", .str (``ProfileChoice.piSigmaChoice).toString),
    ("requiresConstructedWitnesses", .bool true),
    ("adoptsExtensionalChoice", .bool false)]).compress)
  liftIO (IO.println (Json.mkObj [
    ("kind", .str "metta-catalogue"), ("schemaVersion", toJson (1 : Nat)),
    ("text", .str catalogueMetta), ("nativeAssumptionAuthority", .bool false)]).compress)

syntax (name := profileCatalogueCommand) "#profile_catalogue" : command

@[command_elab profileCatalogueCommand]
def elabProfileCatalogue : CommandElab := fun _ => emitCatalogue

end Mettapedia.SetTheory.Profiles.ProfileCatalogueExport
