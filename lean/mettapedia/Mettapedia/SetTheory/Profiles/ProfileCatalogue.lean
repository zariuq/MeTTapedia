import Lean.Data.Json
import Mettapedia.SetTheory.Profiles.CommonSetProfiles
import Mettapedia.SetTheory.Profiles.AntiFoundationViews
import Mettapedia.SetTheory.Profiles.ProfileChoice
import Mettapedia.SetTheory.Profiles.ProfileChoiceModels
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFiniteBoolean
import Mettapedia.SetTheory.Profiles.ProfileFiniteScottEvaluation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.SetIndexedAntiFoundation
import Mettapedia.SetTheory.CarveOuts.HOTGCoverage
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation

/-!
# Evidence-scoped set-theory catalogue

Declaration, model construction, proof interpretation and executable
fragment are separate lists of evidence. A finite carrier does not establish
a full set-theory model. External proof projects and literature are retained
as external evidence and confer no native assumption authority.

Choice is recorded separately from logic, anti-foundation and universe
strength. A selection of `none` means that no extensional Choice axiom is
adopted; it does not refute each Choice principle. The product/sum theorem
of `ProfileChoice` is retained outside the extensional Choice axis.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileCatalogue

open Lean (Name)

inductive ProfileId where
  | primeCommon | foundationCommon | classicalCommon | classicalFoundationCommon
  | foundation | afa | safa | fafa | bafa | nf | nfu | gpkPlusInfinity
  | hol | megalodonHotg | hotgTheory
  deriving DecidableEq, BEq, Repr

def ProfileId.spelling : ProfileId → String
  | .primeCommon => "prime-common"
  | .foundationCommon => "foundation-common"
  | .classicalCommon => "classical-common"
  | .classicalFoundationCommon => "classical-foundation-common"
  | .foundation => "foundation"
  | .afa => "afa"
  | .safa => "safa"
  | .fafa => "fafa"
  | .bafa => "bafa"
  | .nf => "nf"
  | .nfu => "nfu"
  | .gpkPlusInfinity => "gpk-plus-infinity"
  | .hol => "hol"
  | .megalodonHotg => "megalodon-hotg"
  | .hotgTheory => "hotg-theory"

inductive Stage where
  | declaredTheory | constructedModel | checkedInterpretation | executableFragment
  deriving DecidableEq, BEq, Repr

def Stage.spelling : Stage → String
  | .declaredTheory => "declared-theory"
  | .constructedModel => "constructed-model"
  | .checkedInterpretation => "checked-interpretation"
  | .executableFragment => "executable-fragment"

def stages : List Stage :=
  [.declaredTheory, .constructedModel, .checkedInterpretation, .executableFragment]

inductive Scope where
  | wholeDeclaredTheory | commonFirstOrder | commonCollectionExtension
  | foundationCommonExtension | classicalCommonExtension | classicalFoundationCommonExtension
  | boundedGraphDecoration | finitePictureMenu | membershipInduction
  | finiteAczelMaterialReadout | finiteAccessibleFoundationReadout
  | finiteCanonicalScottReadout | finiteRawUnfoldingComparison
  | univalentMaterialFragment | auxiliaryTangledTypeTheory | consistencyReduction
  | holSetInterpretation | hotgLawsUnderUniverseHypothesis
  | runtimeGrammarFragment | profileBlueprint | compatibilityClaim | choicePrinciple
  deriving DecidableEq, BEq, Repr

def Scope.spelling : Scope → String
  | .wholeDeclaredTheory => "whole-declared-theory"
  | .commonFirstOrder => "common-first-order"
  | .commonCollectionExtension => "common-collection-extension"
  | .foundationCommonExtension => "foundation-common-extension"
  | .classicalCommonExtension => "classical-common-extension"
  | .classicalFoundationCommonExtension => "classical-foundation-common-extension"
  | .boundedGraphDecoration => "bounded-graph-decoration"
  | .finitePictureMenu => "finite-picture-menu"
  | .finiteAczelMaterialReadout => "finite-aczel-material-readout"
  | .finiteAccessibleFoundationReadout => "finite-accessible-foundation-readout"
  | .finiteCanonicalScottReadout => "finite-canonical-scott-readout"
  | .finiteRawUnfoldingComparison => "finite-raw-unfolding-comparison"
  | .membershipInduction => "membership-induction"
  | .univalentMaterialFragment => "univalent-material-fragment"
  | .auxiliaryTangledTypeTheory => "auxiliary-tangled-type-theory"
  | .consistencyReduction => "consistency-reduction"
  | .holSetInterpretation => "hol-set-interpretation"
  | .hotgLawsUnderUniverseHypothesis => "hotg-laws-under-universe-hypothesis"
  | .runtimeGrammarFragment => "runtime-grammar-fragment"
  | .profileBlueprint => "profile-blueprint"
  | .compatibilityClaim => "compatibility-claim"
  | .choicePrinciple => "choice-principle"

/-- The source determines where checking occurred. A primary citation is
not promoted to a local kernel declaration. -/
inductive Source where
  | localKernel (declaration : Name)
  | externalKernel (project anchor : String)
  | primaryLiterature (url anchor : String)
  | nativeReplay (reference : String)
  | declaredSpecification (reference : String)
  deriving DecidableEq, Repr

def Source.kind : Source → String
  | .localKernel _ => "local-kernel-declaration"
  | .externalKernel _ _ => "external-kernel-project"
  | .primaryLiterature _ _ => "primary-literature"
  | .nativeReplay _ => "native-replay"
  | .declaredSpecification _ => "declared-specification"

def Source.reference : Source → String
  | .localKernel name => name.toString
  | .externalKernel project _ => project
  | .primaryLiterature url _ => url
  | .nativeReplay reference => reference
  | .declaredSpecification reference => reference

def Source.anchor : Source → String
  | .externalKernel _ anchor | .primaryLiterature _ anchor => anchor
  | _ => ""

def Source.localDeclaration? : Source → Option Name
  | .localKernel name => some name
  | _ => none

/-- Literature describes an interpretation; a checked interpretation must
also name the kernel where its checking took place. -/
def Source.hasInterpretationChecker : Source → Bool
  | .localKernel _ | .externalKernel _ _ => true
  | _ => false

structure Evidence where
  stage : Stage
  scope : Scope
  source : Source
  statement : String
  commitments : List String := []
  deriving Repr

/-- Local kernel credit is attached only to a local declaration at the
requested stage and the exact stated scope. The exporter audits that name's
actual complete type and proof dependencies in the checked environment. -/
def Evidence.localCredit (evidence : Evidence) (stage : Stage) (scope : Scope) : Prop :=
  evidence.stage = stage ∧ evidence.scope = scope ∧
    ∃ name, evidence.source.localDeclaration? = some name

theorem external_kernel_has_no_local_credit (project anchor statement : String)
    (evidenceStage requestedStage : Stage) (evidenceScope requestedScope : Scope)
    (commitments : List String) :
    ¬ Evidence.localCredit
      ⟨evidenceStage, evidenceScope, .externalKernel project anchor, statement, commitments⟩
      requestedStage requestedScope := by
  rintro ⟨_, _, name, impossible⟩
  cases impossible

theorem literature_has_no_local_credit (url anchor statement : String)
    (evidenceStage requestedStage : Stage) (evidenceScope requestedScope : Scope)
    (commitments : List String) :
    ¬ Evidence.localCredit
      ⟨evidenceStage, evidenceScope, .primaryLiterature url anchor, statement, commitments⟩
      requestedStage requestedScope := by
  rintro ⟨_, _, name, impossible⟩
  cases impossible

theorem native_replay_has_no_local_credit (reference statement : String)
    (evidenceStage requestedStage : Stage) (evidenceScope requestedScope : Scope)
    (commitments : List String) :
    ¬ Evidence.localCredit
      ⟨evidenceStage, evidenceScope, .nativeReplay reference, statement, commitments⟩
      requestedStage requestedScope := by
  rintro ⟨_, _, name, impossible⟩
  cases impossible

/-- Finite construction and decision scopes do not claim a complete
material universe or all axioms of its named set theory. -/
def Scope.isFiniteFragment : Scope → Bool
  | .finitePictureMenu | .finiteAczelMaterialReadout | .finiteAccessibleFoundationReadout
    | .finiteCanonicalScottReadout | .finiteRawUnfoldingComparison => true
  | _ => false

theorem finite_fragment_has_no_full_model_credit (evidence : Evidence)
    (finite : evidence.scope.isFiniteFragment = true) :
    ¬ evidence.localCredit .constructedModel .wholeDeclaredTheory := by
  rintro ⟨_, full, _⟩
  rw [full] at finite
  cases finite

theorem raw_unfolding_has_no_canonical_scott_credit (evidence : Evidence)
    (raw : evidence.scope = .finiteRawUnfoldingComparison) (stage : Stage) :
    ¬ evidence.localCredit stage .finiteCanonicalScottReadout := by
  rintro ⟨_, canonical, _⟩
  have impossible : Scope.finiteRawUnfoldingComparison = .finiteCanonicalScottReadout :=
    raw.symm.trans canonical
  cases impossible

theorem finite_menu_has_no_full_model_credit (evidence : Evidence)
    (finite : evidence.scope = .finitePictureMenu) :
    ¬ evidence.localCredit .constructedModel .wholeDeclaredTheory := by
  rintro ⟨_, full, _⟩
  have impossible : Scope.finitePictureMenu = .wholeDeclaredTheory := finite.symm.trans full
  cases impossible

theorem interpretation_is_not_execution (evidence : Evidence)
    (interpreted : evidence.stage = .checkedInterpretation) (scope : Scope) :
    ¬ evidence.localCredit .executableFragment scope := by
  rintro ⟨executed, _, _⟩
  have impossible : Stage.checkedInterpretation = .executableFragment := interpreted.symm.trans executed
  cases impossible

inductive ChoiceLevel where
  | none | countable | dependent | full
  deriving DecidableEq, BEq, Repr

def ChoiceLevel.spelling : ChoiceLevel → String
  | .none => "none"
  | .countable => "countable"
  | .dependent => "dependent"
  | .full => "full"

inductive ChoiceStance where
  | unspecified | notAdopted | adopted | refuted
  deriving DecidableEq, BEq, Repr

def ChoiceStance.spelling : ChoiceStance → String
  | .unspecified => "unspecified"
  | .notAdopted => "not-adopted"
  | .adopted => "adopted"
  | .refuted => "refuted"

structure ChoiceRecord where
  level : ChoiceLevel
  stance : ChoiceStance
  evidence : Option Source := none
  statement : String
  deriving Repr

structure Profile where
  id : ProfileId
  signature : String
  evidence : List Evidence
  choiceSelection : Option ChoiceLevel
  choice : List ChoiceRecord
  bounds : List String
  deriving Repr

def Profile.atStage (profile : Profile) (stage : Stage) : List Evidence :=
  profile.evidence.filter (fun evidence => evidence.stage == stage &&
    (stage != .checkedInterpretation || evidence.source.hasInterpretationChecker))

/-- Paper comparisons remain inspectable without entering the
machine-checked interpretation status. -/
def Profile.reportedComparisons (profile : Profile) : List Evidence :=
  profile.evidence.filter (fun evidence => evidence.stage == .checkedInterpretation &&
    !evidence.source.hasInterpretationChecker)

theorem checked_interpretation_has_checker (profile : Profile) (evidence : Evidence)
    (present : evidence ∈ profile.atStage .checkedInterpretation) :
    evidence.source.hasInterpretationChecker = true := by
  simp only [Profile.atStage, List.mem_filter, Bool.and_eq_true] at present
  exact present.2.2

theorem reported_comparison_is_not_checked (profile : Profile) (evidence : Evidence)
    (reported : evidence ∈ profile.reportedComparisons) :
    evidence ∉ profile.atStage .checkedInterpretation := by
  intro checked
  have checking := checked_interpretation_has_checker profile evidence checked
  simp only [Profile.reportedComparisons, List.mem_filter, Bool.and_eq_true] at reported
  have notChecking := reported.2.2
  rw [checking] at notChecking
  exact Bool.noConfusion notChecking

def kernel (stage : Stage) (scope : Scope) (name : Name) (statement : String)
    (commitments : List String := []) : Evidence :=
  ⟨stage, scope, .localKernel name, statement, commitments⟩

def literature (stage : Stage) (scope : Scope) (url anchor statement : String)
    (commitments : List String := []) : Evidence :=
  ⟨stage, scope, .primaryLiterature url anchor, statement, commitments⟩

def declared (reference statement : String) (scope : Scope := .profileBlueprint) : Evidence :=
  ⟨.declaredTheory, scope, .declaredSpecification reference, statement, []⟩

def replay (reference statement : String) : Evidence :=
  ⟨.executableFragment, .runtimeGrammarFragment, .nativeReplay reference, statement, []⟩

def scopedReplay (scope : Scope) (reference statement : String) : Evidence :=
  ⟨.executableFragment, scope, .nativeReplay reference, statement, []⟩

def finiteAczelExecution : Evidence := scopedReplay .finiteAczelMaterialReadout
  "scripts/check_prime_finite_graph_readouts.py; tests/prime/set_profiles/finite_graph_readouts.metta"
  "Finite graph value, equality, membership and member enumeration were replayed against independently checked expectations on default, specialization and fuel routes. This is native replay evidence, not a proof of C implementation correctness or a complete AFA theory."

def finiteFoundationExecution : Evidence := scopedReplay .finiteAccessibleFoundationReadout
  "scripts/check_prime_finite_graph_readouts.py; tests/prime/set_profiles/finite_graph_readouts.metta"
  "Finite Foundation eligibility and guarded value/equality/membership were replayed on all three routes. Reachable cycles are refused; unreachable cycles do not invalidate an accessible selected root. This is a partial finite interpretation, not a complete Foundation set theory or a proof of C correctness."

def finiteScottExecution : Evidence := scopedReplay .finiteCanonicalScottReadout
  "scripts/check_prime_finite_graph_readouts.py; tests/prime/set_profiles/scott_canonical_readouts.metta"
  "Finite canonical Scott equality, membership and authored member representatives were replayed against checked certificates on default, specialization and fuel routes. The operation recounts after quotienting; no complete SAFA universe or C correctness proof is claimed."

def rawUnfoldingExecution : Evidence := scopedReplay .finiteRawUnfoldingComparison
  "scripts/check_prime_finite_graph_readouts.py; tests/prime/set_profiles/finite_graph_readouts.metta"
  "The separately named raw-unfolding diagnostic was replayed on all three routes. It compares the original rooted unfoldings and is not canonical Scott equality on arbitrary finite graphs."

def noChoice : List ChoiceRecord := [
  ⟨.none, .notAdopted, none, "No extensional Choice axiom is adopted; this is not its negation."⟩,
  ⟨.countable, .notAdopted, none, "Countable extensional Choice is not an adopted law."⟩,
  ⟨.dependent, .notAdopted, none, "Dependent extensional Choice is not an adopted law."⟩,
  ⟨.full, .notAdopted, none, "Full extensional Choice is not an adopted law."⟩]

def unspecifiedChoice : List ChoiceRecord := [
  ⟨.none, .unspecified, none, "The anti-foundation or logic name does not choose a Choice extension."⟩,
  ⟨.countable, .unspecified, none, "No countable Choice profile is selected by this name."⟩,
  ⟨.dependent, .unspecified, none, "No dependent Choice profile is selected by this name."⟩,
  ⟨.full, .unspecified, none, "No full Choice profile is selected by this name."⟩]

def commonEvidence : List Evidence := [
  declared "SetTheory/Profiles/CommonCore.lean"
    "Independently authored common first-order laws and separate Collection extensions."
    .commonCollectionExtension,
  kernel .constructedModel .commonCollectionExtension
    ``CommonCoreConstructive.validateExtension
    "Actual varying constructed-witness graph realizers for the declared Collection extension."
    ["Small graph presentations and constructed existential witnesses; explicit Lean universe parameters."],
  kernel .constructedModel .commonCollectionExtension
    ``CommonCoreClassicalCollection.wellFounded_extension
    "The same extension is interpreted in the concrete well-founded set carrier."
    ["Ordinary propositional existence uses host Choice for Strong Collection."],
  kernel .constructedModel .commonCollectionExtension
    ``CommonCoreClassicalCollection.hyperset_extension
    "The same extension is interpreted in the concrete hyperset carrier."
    ["Ordinary propositional existence uses host Choice for Strong Collection."],
  kernel .checkedInterpretation .commonCollectionExtension
    ``CommonCoreConstructive.interpretExtension
    "Actual indexed derivations compute realizers while retaining assumption receipts.",
  kernel .checkedInterpretation .commonCollectionExtension
    ``CommonCoreClassicalCollection.hyperset_extension
    "Ordinary first-order derivations are interpreted in HSet, independently of the native checker.",
  replay "tests/prime/common_set/default_core.metta; tests/prime/common_set/schema_resources.metta"
    "Qualified common-law compilation and scoped proof examples; no all-input C checker soundness claim."]

def primeCommon : Profile :=
  ⟨.primeCommon, "Pure material membership and equality; independently authored intuitionistic first-order calculus.",
    commonEvidence, some .none, noChoice,
    ["Bounded Separation; separately adopted Strong Collection and Subset Collection.",
      "No power-set, unrestricted Separation, Foundation or classical-logic adoption.",
      "Finite native examples are an executable fragment, not the complete mathematical model."]⟩

def commonExtension (id : ProfileId) (scope : Scope) (description : String) : Profile :=
  let laws : List Evidence :=
    (if id = .classicalCommon then [] else [
      kernel .constructedModel scope ``CommonCoreClassical.wellFounded_foundation
        "The concrete well-founded carrier validates the Foundation sentence."]) ++
    (if id = .foundationCommon then [] else [
      kernel .constructedModel scope ``Classical.em
        "The host truth semantics of this concrete well-founded model validates excluded middle."])
  ⟨id, "Pure material membership and equality with explicit logical extensions.",
    commonEvidence ++ laws ++ [declared "docs/theory-profiles.md" description scope,
      kernel .checkedInterpretation .commonCollectionExtension
        ``CommonCoreClassicalCollection.wellFounded_extension
        "Underlying common derivations are interpreted; interpretation of every added native rule is separate.",
      replay "tests/prime/common_set/assumption_origins.metta"
        "Explicit common-profile extension selections and scoped assumption receipts were replayed."],
    some .none, noChoice,
    ["The listed extension is a declared fragment; it is not a complete ZF or CZF presentation.",
      "Host classical semantics does not adopt an object-language extensional Choice operator."]⟩

def foundationCommon : Profile := commonExtension .foundationCommon .foundationCommonExtension
  "Common material laws plus the ordinary Foundation sentence."

def classicalCommon : Profile := commonExtension .classicalCommon .classicalCommonExtension
  "Common material laws plus classical logic; Foundation is not adopted."

def classicalFoundationCommon : Profile := commonExtension .classicalFoundationCommon
  .classicalFoundationCommonExtension "Common material laws plus Foundation and classical logic."

def foundation : Profile :=
  ⟨.foundation, "Membership-inductive material sets; the base set-theory axioms must be stated separately.",
    [declared "SetTheory/Profiles/Principles.lean" "The membership-induction principle is independently stated." .membershipInduction,
      kernel .constructedModel .membershipInduction ``zfSet_memInduction
        "ZFSet validates the complete membership-induction principle.",
      kernel .checkedInterpretation .commonCollectionExtension
        ``CommonCoreClassicalCollection.wellFounded_extension
        "The common Collection extension has an actual well-founded interpretation.",
      kernel .constructedModel .finitePictureMenu ``antiFoundationLedger
        "The finite picture menu has its own Foundation comparison, not a complete set-theory model.",
      kernel .constructedModel .finiteAccessibleFoundationReadout
        ``ProfileGraphReadout.FiniteBoolean.Foundation.eligible_material_domain
        "The enumerated finite eligibility algorithm accepts exactly roots whose actual HSet decoration is well-founded; the accepted values form a restricted interpretation.",
      kernel .checkedInterpretation .finiteAccessibleFoundationReadout
        ``ProfileGraphReadout.FiniteBoolean.Foundation.eligible_accessibility
        "Finite eligibility is equivalent to accessibility for the selected root, with child-to-parent orientation of the accessibility relation.",
      finiteFoundationExecution],
    none, unspecifiedChoice,
    ["Foundation is a distinct axis from classical logic, Choice and universe strength.",
      "A total readout of arbitrary hypersets into well-founded sets need not preserve membership.",
      "The executable Foundation readout is partial on finite presentations; it does not select the logic, Choice or complete base axioms."]⟩

def hottPaper : String := "https://arxiv.org/html/2001.06696v8"

def afa : Profile :=
  ⟨.afa, "Material sets with Aczel graph decoration; logic, base laws, Choice and graph bound are explicit.",
    [declared "TypeTheory/MaterialSets/Hypersets/SetIndexedAntiFoundation.lean"
        "The local Aczel model has a set-indexed bounded decoration law." .boundedGraphDecoration,
      kernel .constructedModel .boundedGraphDecoration
        ``Mettapedia.TypeTheory.MaterialSets.Hypersets.SetIndexedAntiFoundation.existsUnique_setDecoration
        "Every graph indexed by members of a given small material set has a unique decoration in HSet."
        ["Member smallness and explicit universe parameters."],
      kernel .checkedInterpretation .commonCollectionExtension
        ``CommonCoreClassicalCollection.hyperset_extension
        "HSet interprets the independently stated common Collection extension.",
      kernel .constructedModel .finitePictureMenu ``antiFoundationLedger
        "The finite picture-menu factorization comparisons remain explicitly finite.",
      kernel .constructedModel .finiteAczelMaterialReadout
        ``ProfileGraphReadout.Presentations.membership_eq_true
        "Validated finite authored presentations have actual HSet values whose membership is exactly the computed finite graph membership reading.",
      kernel .checkedInterpretation .finiteAczelMaterialReadout
        ``ProfileGraphReadout.FiniteBoolean.equivalent_material_kernel
        "The finite Boolean refinement decision identifies exactly equal Aczel decorations of the selected roots.",
      kernel .checkedInterpretation .finiteAczelMaterialReadout
        ``ProfileGraphReadout.Presentations.equality_eq_true
        "Equality on validated authored presentations preserves and reflects their actual HSet material values.",
      finiteAczelExecution,
      literature .constructedModel .univalentMaterialFragment hottPaper
        "Aczel-Mendler construction and accompanying Agda development"
        "The external HoTT AFA model is a separate construction."
        ["HoTT model hypotheses; propositional resizing is required by this AFA construction."]],
    none, unspecifiedChoice,
    ["No unrestricted powerset final coalgebra on a set-sized carrier is claimed.",
      "Native cyclic values are qualified only for the explicitly finite graph readout, not all AFA set-forming operations.",
      "Adjacency support determines material membership; authored occurrences and origins remain separate evidence."]⟩

def alternativeAntiFoundation (id : ProfileId) (name : String) : Profile :=
  ⟨id, "Material membership with the " ++ name ++ " anti-foundation principle; remaining axes unspecified.",
    [declared "SetTheory/Profiles/AntiFoundationViews.lean"
        ("The local " ++ name ++ " comparison is authored on a finite picture menu.") .finitePictureMenu,
      kernel .constructedModel .finitePictureMenu ``antiFoundationLedger
        "The actual finite carriers, distinguishing decorations and factorization laws, are checked."],
    none, unspecifiedChoice,
    ["The finite carriers are not full alternative set-theory universes.",
      "Factorization on the finite menu is not implication between complete anti-foundation theories."]⟩

def safa : Profile :=
  let finite := alternativeAntiFoundation .safa "Scott"
  { finite with
    evidence := finite.evidence ++ [
    kernel .constructedModel .finiteCanonicalScottReadout
      ``ProfileFiniteScottCollapse.FiniteGraph.canonicalGraph_scottExtensional
      "Every explicitly enumerated finite graph is normalized to an actual Scott-extensional finite membership graph at its cardinal stage; this does not construct a complete SAFA universe.",
    kernel .constructedModel .finiteCanonicalScottReadout
      ``ProfileFiniteScottCollapse.FiniteGraph.canonicalDecoration
      "The finite canonical quotient has a constructed membership relation and a decoration preserving and reflecting its declared identification kernel.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottCoherence.FiniteGraph.normalizedEqual_unfolding_kernel
      "Pair equality is exactly isomorphism of the independently canonicalized rooted unfoldings, with quotienting and recounting retained.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottCoherence.FiniteGraph.normalizedMember_unfolding_kernel
      "Pair membership is exactly membership in the complete canonical member fibre, using full unfolding identity on its elements.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottCoherence.FiniteGraph.normalizedEqual_disjoint_padding
      "Canonical pair equality is stable under disjoint padding, using complete successor-fibre closed embeddings.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottCoherence.Presentations.member_selected_children
      "Canonical membership is represented exactly by selected children of the authored source row, retaining an actual occurrence representative.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottEvaluation.Presentations.stageEqual_correct
      "An early stopped stage computes the final pair equality when each stage count is bounded by its source cardinal and the stopped certificates hold.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottEvaluation.Presentations.stageMember_correct
      "The same bounded stopped-stage contract computes the final pair membership.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottEvaluation.Presentations.stageMembers_correct
      "Bounded stopped-stage member enumeration agrees with final canonical enumeration while retaining authored children.",
    kernel .checkedInterpretation .finiteCanonicalScottReadout
      ``ProfileFiniteScottCollapse.Controls.second_recount_is_necessary
      "An explicit finite graph separates one-pass quotienting from the full canonical reading: a second recount identifies roots the first pass leaves distinct.",
    kernel .checkedInterpretation .finiteRawUnfoldingComparison
      ``ProfileFiniteScottReadout.Presentations.rawUnfoldingEqual_kernel
      "The raw diagnostic's kernel is isomorphism of original unfoldings; its scope is separate from canonical Scott equality.",
    finiteScottExecution, rawUnfoldingExecution,
    literature .constructedModel .univalentMaterialFragment hottPaper
      "SAFA model and higher SAFA hierarchy; accompanying Agda development"
      "The external HoTT SAFA construction is model-specific identity-type evidence."
      ["HoTT, M-types and the stated universe/truncation hypotheses."]]
    bounds := finite.bounds ++ [
      "The native scott-canonical operation normalizes finite graphs repeatedly; raw-unfolding is a separate diagnostic and receives no canonical Scott credit.",
      "Finite Scott-extensional carriers and replayed operations do not validate complete SAFA, arbitrary graph existence or a C implementation theorem.",
      "Cross-presentation coherence uses closed successor-fibre embeddings; edge preservation alone is insufficient."] }

def fafa : Profile := alternativeAntiFoundation .fafa "Finsler"
def bafa : Profile := alternativeAntiFoundation .bafa "Boffa"

theorem afa_retains_finite_execution :
    finiteAczelExecution ∈ afa.atStage .executableFragment := by
  apply List.mem_filter.mpr
  exact ⟨by simp [afa], rfl⟩

theorem foundation_retains_finite_execution :
    finiteFoundationExecution ∈ foundation.atStage .executableFragment := by
  apply List.mem_filter.mpr
  exact ⟨by simp [foundation], rfl⟩

theorem safa_retains_finite_execution :
    finiteScottExecution ∈ safa.atStage .executableFragment := by
  apply List.mem_filter.mpr
  exact ⟨by simp [safa], rfl⟩

theorem safa_retains_raw_diagnostic :
    rawUnfoldingExecution ∈ safa.atStage .executableFragment := by
  apply List.mem_filter.mpr
  exact ⟨by simp [safa], rfl⟩

theorem finite_executable_evidence_has_no_local_credit (evidence : Evidence)
    (present : evidence ∈ [finiteAczelExecution, finiteFoundationExecution,
      finiteScottExecution, rawUnfoldingExecution]) (stage : Stage) (scope : Scope) :
    ¬ evidence.localCredit stage scope := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with first | second | third | fourth <;> subst evidence <;>
    exact native_replay_has_no_local_credit _ _ _ _ _ _ _

theorem canonical_scott_certificate_is_not_full_model :
    ¬ (kernel .constructedModel .finiteCanonicalScottReadout
      ``ProfileFiniteScottCollapse.FiniteGraph.canonicalDecoration
      "Constructed finite canonical carrier.").localCredit .constructedModel .wholeDeclaredTheory :=
  finite_fragment_has_no_full_model_credit _ rfl

theorem raw_certificate_is_not_canonical_scott :
    ¬ (kernel .checkedInterpretation .finiteRawUnfoldingComparison
      ``ProfileFiniteScottReadout.Presentations.rawUnfoldingEqual_kernel
      "Original unfolding kernel.").localCredit .checkedInterpretation .finiteCanonicalScottReadout :=
  raw_unfolding_has_no_canonical_scott_credit _ rfl _

def nfFullChoiceRefutation : Source := .primaryLiterature
  "https://doi.org/10.1073/pnas.39.9.972" "Specker 1953, pp. 972-975: NF refutes the Axiom of Choice."

def nf : Profile :=
  ⟨.nf, "Pure membership and equality with extensionality and stratified comprehension.",
    [literature .declaredTheory .wholeDeclaredTheory
        "https://randall-holmes.github.io/Papers/tangled.pdf" "Definition of NF"
        "NF has stratified comprehension and a universal set; the Russell predicate is unstratified.",
      ⟨.constructedModel, .auxiliaryTangledTypeTheory,
        .externalKernel "https://github.com/leanprover-community/con-nf"
          "ConNF/Model/Result.lean", "ConNF constructs a Lean TTT model; this project has not imported it.",
        ["The external Lean host and the cardinal/universe parameters of that development."]⟩,
      literature .checkedInterpretation .consistencyReduction
        "https://randall-holmes.github.io/Papers/tangled.pdf" "Theorem 1 and the ConNF README objective"
        "The TTT-to-NF consistency link is a paper argument, separate from the external kernel construction."],
    none,
    [⟨.none, .unspecified, none, "The catalogue does not select an NF Choice extension."⟩,
      ⟨.countable, .unspecified, none, "No countable Choice assertion is made here."⟩,
      ⟨.dependent, .unspecified, none, "No dependent Choice assertion is made here."⟩,
      ⟨.full, .refuted, some nfFullChoiceRefutation,
        "NF refutes full extensional Choice; this is primary-literature evidence, not a local proof."⟩],
    ["No local NF model, proof interpreter or executable fragment is credited.",
      "Its universal set excludes the unstratified Russell Separation instance of the common language."]⟩

def nfu : Profile :=
  ⟨.nfu, "Membership, equality and a set predicate; stratified comprehension with urelements.",
    [literature .declaredTheory .wholeDeclaredTheory
        "https://link.springer.com/article/10.1007/BF00568059" "Jensen: NF with urelements"
        "NFU weakens extensionality to permit atoms; the atom/set distinction belongs to its signature.",
      literature .constructedModel .wholeDeclaredTheory
        "https://link.springer.com/article/10.1007/BF00568059" "Jensen model construction"
        "NFU model and relative-consistency evidence remain external literature."],
    none,
    [⟨.none, .unspecified, none, "The catalogue does not select an NFU Choice extension."⟩,
      ⟨.countable, .unspecified, none, "No countable Choice assertion is made here."⟩,
      ⟨.dependent, .unspecified, none, "No dependent Choice assertion is made here."⟩,
      ⟨.full, .notAdopted,
        some (.primaryLiterature "https://randall-holmes.github.io/Papers/tangled.pdf"
          "Discussion of Jensen models with Choice"),
        "Full Choice is a compatible named extension of NFU; it is not adopted in this catalogue entry."⟩],
    ["No local NFU model, proof interpreter or executable fragment is credited.",
      "Atoms preclude silently identifying this signature with pure material extensionality."]⟩

def gpkFullChoiceRefutation : Source := .primaryLiterature
  "https://doi.org/10.2307/2695086" "Esser 2000, JSL 65(4), pp. 1911-1916."

def gpkPlusInfinity : Profile :=
  ⟨.gpkPlusInfinity, "Positive comprehension theory with universal set and its stated infinity strengthening.",
    [literature .declaredTheory .wholeDeclaredTheory
        "https://doi.org/10.2307/2695086" "Esser: GPK plus infinity"
        "The positive comprehension language and universal-set laws require a separate presentation.",
      literature .checkedInterpretation .consistencyReduction
        "https://onlinelibrary.wiley.com/doi/abs/10.1002/malq.19990450110"
        "Mutual interpretation under the restricted well-founded Choice extension"
        "The class-theoretic comparison has additional named commitments."
        ["Restricted AC on well-founded sets; Kelley-Morse with global Choice and On ramifiable."],
      literature .checkedInterpretation .compatibilityClaim
        "https://onlinelibrary.wiley.com/doi/abs/10.1002/malq.19960420109"
        "Esser 1996: Inconsistency of GPK + AFA"
        "GPK and Aczel AFA cannot be amalgamated over the same membership relation under those axioms."],
    none,
    [⟨.none, .unspecified, none, "No particular compatible Choice subprinciple is selected."⟩,
      ⟨.countable, .unspecified, none, "No countable Choice assertion is made here."⟩,
      ⟨.dependent, .unspecified, none, "No dependent Choice assertion is made here."⟩,
      ⟨.full, .refuted, some gpkFullChoiceRefutation,
        "GPK plus infinity refutes full Choice; this is primary-literature evidence, not a local proof."⟩],
    ["No local full GPK model, proof interpreter or executable fragment is credited.",
      "Positive comprehension is not the common bounded Separation schema.",
      "A profile-relative interpretation does not merge incompatible membership axioms."]⟩

def hol : Profile :=
  ⟨.hol, "Simply typed higher-order logic; a material set carrier is an interpretation, not a native logic axiom.",
    [declared "Logic/HOL/Derivation.lean; docs/theory-profiles.md"
        "HOL has its own typed proof syntax and explicit native selection.",
      kernel .constructedModel .holSetInterpretation
        ``Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.theory_valid
        "The independently stated HOL set laws hold in the actual ZFSet interpretation."
        ["Full higher-order domains and the inspected host dependencies."],
      kernel .checkedInterpretation .holSetInterpretation
        ``Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation.proofValue_agreement
        "Actual retained HOL proofs agree with their material family interpretation."
        ["The CofinalInaccessibles hypothesis of this family-enclosing interpretation."],
      replay "tests/prime/theory_profiles"
        "Native HOL scoped judgments were replayed; this does not by itself prove general C checker soundness."],
    none, unspecifiedChoice,
    ["HOL is a logic selection; it alone does not adopt any material set theory."]⟩

def megalodonHotg : Profile :=
  ⟨.megalodonHotg, "Preserved native HOTG-style seed fragment; Eps_set is typed without its Choice law.",
    [declared "docs/theory-profiles.md; SetTheory/CarveOuts/HOTGCoverage.lean"
        "The preserved guest seeds Separation and omits function/propositional extensionality laws.",
      kernel .constructedModel .hotgLawsUnderUniverseHypothesis
        ``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.hotgLawsInZFSet
        "A stronger HOL interpretation validates the seeded set and universe laws."
        ["Host Choice; CofinalInaccessibles remains a hypothesis of universe laws."],
      replay "tests/prime/profiles/megalodon_hotg/scoped"
        "The preserved native seed fragment has retained replay qualification; it is not faithful complete HOTG."],
    some .none, noChoice,
    ["Megalodon's own preamble derives Separation using its epsilon Choice law.",
      "This preserved seed fragment has no complete native HOTG interpretation certificate."]⟩

def hotgTheory : Profile :=
  ⟨.hotgTheory, "Megalodon HOTG with its own preamble, extensional HOL, epsilon Choice and least-universe laws.",
    [declared "megalodon/set_carveouts/hotg_law_inventory.tsv"
        "The external Megalodon preamble is inventoried separately from the preserved native guest.",
      kernel .constructedModel .hotgLawsUnderUniverseHypothesis
        ``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.hotgLawsInZFSet
        "The HOL set and least-universe laws are valid in the actual ZFSet interpretation."
        ["Host Choice; CofinalInaccessibles for every universe law; full higher-order domains."],
      kernel .checkedInterpretation .holSetInterpretation
        ``Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation.proofValue_agreement
        "Retained HOL proof values have an actual material-family interpretation."
        ["CofinalInaccessibles and inspected host dependencies; not a complete Megalodon parser translation." ]],
    some .full,
    [⟨.none, .notAdopted, none, "The faithful HOTG theory includes epsilon Choice."⟩,
      ⟨.countable, .unspecified, none, "The exact internal countable-Choice derivation is not separately inventoried here."⟩,
      ⟨.dependent, .unspecified, none, "The exact internal dependent-Choice derivation is not separately inventoried here."⟩,
      ⟨.full, .adopted, some (.declaredSpecification "megalodon/set_carveouts/hotg_law_inventory.tsv"),
        "Megalodon's epsilon operator has its explicit extensional Choice law."⟩],
    ["The universe hypothesis is not proved by graph circularity or by well-foundedness.",
      "No faithful native executable HOTG profile is credited by this separate theory entry."]⟩

def catalogue : List Profile := [primeCommon, foundationCommon, classicalCommon,
  classicalFoundationCommon, foundation, afa, safa, fafa, bafa, nf, nfu,
  gpkPlusInfinity, hol, megalodonHotg, hotgTheory]

def lookup (id : ProfileId) : Option Profile :=
  catalogue.find? (fun profile => profile.id == id)

def bareDefault : ProfileId := .primeCommon

theorem catalogue_ids_unique : (catalogue.map Profile.id).Nodup := by decide

theorem every_profile_is_in_catalogue (id : ProfileId) :
    ∃ profile, profile ∈ catalogue ∧ profile.id = id := by
  cases id <;> decide

theorem catalogue_does_not_select_a_foreign_default : bareDefault = .primeCommon := rfl

theorem none_is_not_a_refutation (entry : ChoiceRecord)
    (notAdopted : entry.stance = .notAdopted) : entry.stance ≠ .refuted := by
  rw [notAdopted]
  decide

theorem nf_has_no_local_model_credit :
    ∀ evidence ∈ nf.evidence, ¬ evidence.localCredit .constructedModel .wholeDeclaredTheory := by
  intro evidence member
  simp only [nf, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second | third
  · subst evidence
    exact literature_has_no_local_credit _ _ _ _ _ _ _ _
  · subst evidence
    exact external_kernel_has_no_local_credit _ _ _ _ _ _ _ _
  · subst evidence
    exact literature_has_no_local_credit _ _ _ _ _ _ _ _

theorem alternative_finite_models_are_not_full (id : ProfileId) (name : String) :
    ∀ evidence ∈ (alternativeAntiFoundation id name).evidence,
      ¬ evidence.localCredit .constructedModel .wholeDeclaredTheory := by
  intro evidence member
  have scope : evidence.scope = .finitePictureMenu := by
    simp only [alternativeAntiFoundation, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second <;> subst evidence <;> rfl
  exact finite_menu_has_no_full_model_credit evidence scope

/-- Propositions with type-theoretic witnesses are rearranged by a theorem,
not by adopting a level on the extensional Choice axis. -/
def typeTheoreticChoiceEvidence : Evidence :=
  kernel .checkedInterpretation .choicePrinciple ``ProfileChoice.piSigmaChoice
    "A dependent function of Sigma witnesses computes a Sigma function with all dependent evidence."

namespace Controls

def claimedPaperInterpretation : Profile :=
  ⟨.nf, "Control profile", [literature .checkedInterpretation .consistencyReduction
    "https://randall-holmes.github.io/Papers/tangled.pdf" "Theorem 1"
    "An externally reported consistency reduction."], none, unspecifiedChoice, []⟩

theorem paper_comparison_retained :
    claimedPaperInterpretation.reportedComparisons = claimedPaperInterpretation.evidence := rfl

theorem paper_comparison_not_checked :
    claimedPaperInterpretation.atStage .checkedInterpretation = [] := rfl

def checkedPairInterpretation : Profile :=
  ⟨.primeCommon, "Control profile", [kernel .checkedInterpretation .commonFirstOrder
    ``CommonCoreClassical.wellFounded_interpret
    "A locally checked interpretation of actual first-order derivations."], none, noChoice, []⟩

theorem kernel_interpretation_retained :
    checkedPairInterpretation.atStage .checkedInterpretation = checkedPairInterpretation.evidence := rfl

theorem kernel_interpretation_not_reported :
    checkedPairInterpretation.reportedComparisons = [] := rfl

end Controls

end Mettapedia.SetTheory.Profiles.ProfileCatalogue
