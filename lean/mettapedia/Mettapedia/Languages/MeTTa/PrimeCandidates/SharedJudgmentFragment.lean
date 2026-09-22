import Mettapedia.TypeTheory.DesignStudy
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MatchedIndexDependentTransport
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.OpaqueRelatorScopedComputation

/-!
# One partially specified assembly of shared native judgments

The data below select actual declarations, scoped execution, receipt
reconstruction, intrinsic HOL proof production and contextual readouts.
Every requirement concerns these same components. Native rules come from
the assembly's declarations; contextual operations come from its primitive
execution, whose separate realization requirement connects them to its
handler. Neither operation support nor logical admission is stored as a
proof field in the assembly.

The HOL output boundary is the existing intrinsic proof object: it contains
an already admitted source HOL derivation. The producer independently checks
submitted chart certificates before constructing that object. This is not
an external HOL byte checker, and formed native representation is not a
dependent proof inhabitant of the represented HOL proposition.

These seven fragment obligations are not the six draft decision families.
Set interpretation, universe adequacy, OSLF, unrestricted evaluation and a
joint specification of all those families remain outside this assembly.
Its inhabitant is a compatibility example, not a selected final language.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentFragment

open Mettapedia.TypeTheory.DesignStudy
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.ScopedComputation
open Mettapedia.GSLT.Core Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-- All fields are actual data or operations. The sole proof-bearing output
type is the explicitly intrinsic source-HOL boundary described above. -/
structure Assembly where
  declarations : Signature Tower.Head
  execution : ∀ n, ImplementationStudy.Implementation Tower.Head NativeExamples.Operation Bool Nat n
  reconstructMatch : PolarizedNeedMatchedIndex.Request → NativeWireData.Wire →
    Option (Tower.Tm 0 × Tower.Tm 0)
  produceHOL : ∀ gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort,
    UniformListChartNIKService.ReplayRequest gamma →
      Option (UniformListChartNIKService.intrinsicProofSystem gamma).ProofObject
  View : ContextViews.Scope → Type
  observe : ∀ scope, ContextViews.State scope → View scope
  compactResume : View .producer → View .resumed

namespace Assembly

def rules (assembly : Assembly) : Rules Tower.Head :=
  OpaqueRelatorExtension.rules assembly.declarations

/-- The permitted resumption runs the actual primitive worlds belonging to
this assembly, with the selected answer substituted into the native body. -/
def resume (assembly : Assembly) (worlds : ContextViews.State .producer) :
    ContextViews.State .resumed :=
  worlds.flatMap fun prior =>
    (Code.worlds (assembly.execution 2).primitive (consSub prior.answer ids)
      NativeExamples.body prior.state prior.branch).map fun later =>
        (prior.intents.length,
          { branch := later.branch, answer := .pair prior.answer later.answer,
            state := later.state, intents := prior.intents ++ later.intents })

def execute (assembly : Assembly) {a b : ContextViews.Scope}
    (operation : a ⟶ b) : ContextViews.State a → ContextViews.State b :=
  match operation with
  | .resume => assembly.resume

def observations (assembly : Assembly) (scope : ContextViews.Scope) :
    PolicyFamily (ContextViews.State scope) :=
  PolicyFamily.ContextClosure.family assembly.execute ContextViews.base scope

def executeView (assembly : Assembly) {a b : ContextViews.Scope}
    (operation : a ⟶ b) : assembly.View a → assembly.View b :=
  match operation with
  | .resume => assembly.compactResume

end Assembly

/-! ## Semantic requirements on that same raw assembly -/

def DeclarationsPreserved (assembly : Assembly) : Prop :=
  FormationSensitiveHOLUniformList.declarations.Extends assembly.declarations ∧
  NativeWireData.signature.Extends assembly.declarations ∧
  (∀ name type,
    FormationSensitiveHOLUniformList.rules.constantType name = some type →
      assembly.rules.constantType name = some type) ∧
  (∀ name type, NativeWireData.rules.constantType name = some type →
    assembly.rules.constantType name = some type)

/-- Exactness concerns the actual existing conversion certificates.
Preservation quantifies over every source admitted by the assembly's rules,
not just the image of an older component's judgments. -/
def ConversionQualified (assembly : Assembly) : Prop :=
  (∀ n (left right : Tower.Tm n),
    Conv assembly.rules.headEq left right assembly.rules.computation ↔
      ∃ code, NativeRelatorConversionChecking.check code left right = true) ∧
  FormationSensitive.RootPreservation assembly.rules ∧
  (∀ n (context : Tower.Ctx n) (source target type : Tower.Tm n),
    FormationSensitive.Judgment assembly.rules context source type →
    Step assembly.rules.headEq source target assembly.rules.computation →
      FormationSensitive.Judgment assembly.rules context target type) ∧
  (∀ n (context : Tower.Ctx n) (source target type : Tower.Tm n)
    (code : NativeRelatorConversionChecking.StepCode n),
    FormationSensitive.Judgment assembly.rules context source type →
    NativeRelatorConversionChecking.checkStep code source target = true →
      FormationSensitive.Judgment assembly.rules context target type)

/-- The returned source may be any admitted proof term of the exact selected
proposition. It need not equal the reference J reconstruction syntactically. -/
def MatchAdmission (assembly : Assembly) : Prop :=
  ∀ request input source proposition,
    assembly.reconstructMatch request input = some (source, proposition) →
    ∃ transport : MatchedIndexDependentTransport.Transport,
      MatchedIndexDependentTransport.consume? request input = some transport ∧
      proposition = transport.proposition ∧
      FormationSensitive.Judgment assembly.rules .nil source proposition

/-- Coverage includes every validated receipt, not just a displayed example.
It is phrased through the independent consumer, which validates the whole
receipt and reads its submitted index before returning the selected value. -/
def MatchCoverage (assembly : Assembly) : Prop :=
  ∀ request input transport,
    MatchedIndexDependentTransport.consume? request input = some transport →
      ∃ source, assembly.reconstructMatch request input = some (source, transport.proposition)

def RepresentationAdmitted (assembly : Assembly)
    (gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (claim : UniformListChartNIKService.SourceClaim gamma) : Prop :=
  ∃ (conclusion : Tower.Tm gamma.length) (assumptions : List (Tower.Tm gamma.length)),
    FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature claim.2 =
      some conclusion ∧
    claim.1.map (FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature) =
      assumptions.map some ∧
    FormationSensitive.Judgment assembly.rules
      (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma)
      conclusion (.const `HOLUniformList.prop) ∧
    (∀ formula ∈ assumptions,
      FormationSensitive.Judgment assembly.rules
        (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma)
        formula (.const `HOLUniformList.prop))

/-- Replay acceptance is independent of this assembly's producer. Exact
claim binding and native representation formation are additional obligations;
the derivation inside the output subtype does not discharge either one. -/
def HOLReplayQualified (assembly : Assembly) : Prop :=
  (∀ gamma request, (assembly.produceHOL gamma request).isSome = true ↔
    UniformListChartNIKService.replayAccepted gamma request = true) ∧
  (∀ gamma request proof, assembly.produceHOL gamma request = some proof →
    proof.1 = request.claim ∧ RepresentationAdmitted assembly gamma request.claim)

def ExecutionQualified (assembly : Assembly) : Prop :=
  ∀ scope, (ImplementationStudy.specification assembly.rules NativeExamples.signature).Satisfies
    (assembly.execution scope)

/-- Sufficiency observes paths built from the assembly's own execution.
The compact resumption must also realize that very operation. -/
def ContextualViewsQualified (assembly : Assembly) : Prop :=
  (∀ scope, (assembly.observations scope).SupportsReadout (assembly.observe scope)) ∧
  (∀ worlds, assembly.observe .resumed (assembly.resume worlds) =
    assembly.compactResume (assembly.observe .producer worlds))

inductive Requirement where
  | declarations
  | conversion
  | matchAdmission
  | matchCoverage
  | holReplay
  | execution
  | contextualViews
  deriving DecidableEq, Repr

def specification : Specification Assembly Requirement where
  holds
    | .declarations => DeclarationsPreserved
    | .conversion => ConversionQualified
    | .matchAdmission => MatchAdmission
    | .matchCoverage => MatchCoverage
    | .holReplay => HOLReplayQualified
    | .execution => ExecutionQualified
    | .contextualViews => ContextualViewsQualified
  required := [.declarations, .conversion, .matchAdmission, .matchCoverage,
    .holReplay, .execution, .contextualViews]

/-! ## Composed consequences for any qualified assembly -/

variable {assembly : Assembly} {n m : Nat}

theorem match_acceptance_iff
    (admission : MatchAdmission assembly) (coverage : MatchCoverage assembly)
    (request : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire) :
    (assembly.reconstructMatch request input).isSome = true ↔
      (MatchedIndexDependentTransport.consume? request input).isSome = true := by
  constructor
  · intro accepted
    cases returned : assembly.reconstructMatch request input with
    | none => rw [returned] at accepted; cases accepted
    | some pair =>
        obtain ⟨transport, consumed, _, _⟩ := admission _ _ _ _ returned
        simp only [consumed, Option.isSome_some]
  · intro accepted
    cases consumed : MatchedIndexDependentTransport.consume? request input with
    | none => rw [consumed] at accepted; cases accepted
    | some transport =>
        obtain ⟨source, returned⟩ := coverage _ _ _ consumed
        simp only [returned, Option.isSome_some]

theorem match_rejects_invalid
    (admission : MatchAdmission assembly)
    {request : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    (rejected : MatchedIndexDependentTransport.consume? request input = none) :
    assembly.reconstructMatch request input = none := by
  cases returned : assembly.reconstructMatch request input with
  | none => rfl
  | some pair =>
      obtain ⟨_, consumed, _, _⟩ := admission _ _ _ _ returned
      rw [rejected] at consumed
      cases consumed

theorem validated_receipt_admitted
    (admission : MatchAdmission assembly) (coverage : MatchCoverage assembly)
    (request : PolarizedNeedMatchedIndex.Request) (receipt : PolarizedNeedMatchedIndex.Receipt)
    (checked : PolarizedNeedMatchedIndex.validate request receipt = true) :
    ∃ source,
      assembly.reconstructMatch request (PolarizedNeedMatchedIndex.admittedWire receipt) =
        some (source, (MatchedIndexDependentTransport.Transport.mk receipt receipt.output).proposition) ∧
      FormationSensitive.Judgment assembly.rules .nil source
        (MatchedIndexDependentTransport.Transport.mk receipt receipt.output).proposition := by
  obtain ⟨source, reconstructed⟩ := coverage _ _ _
    (MatchedIndexDependentTransport.consume_checked_receipt request receipt checked)
  obtain ⟨_, _, _, admitted⟩ := admission _ _ _ _ reconstructed
  exact ⟨source, reconstructed, admitted⟩

theorem reconstructed_selection
    (admission : MatchAdmission assembly) {request input source proposition}
    (reconstructed : assembly.reconstructMatch request input = some (source, proposition)) :
    ∃ transport : MatchedIndexDependentTransport.Transport,
      MatchedIndexDependentTransport.decodeAdmitted input = some transport.receipt ∧
      Nonempty (PolarizedNeedMatchedIndex.Evidence request transport.receipt) ∧
      getElem? transport.receipt.values request.index = some transport.selected ∧
      transport.selected = transport.receipt.output ∧
      proposition = transport.proposition ∧
      FormationSensitive.Judgment assembly.rules .nil source proposition := by
  obtain ⟨transport, consumed, exactType, admitted⟩ := admission _ _ _ _ reconstructed
  obtain ⟨evidence, selected, endpoint⟩ := MatchedIndexDependentTransport.consume_selection consumed
  exact ⟨transport, ((MatchedIndexDependentTransport.consume_iff _ _ _).mp consumed).1,
    evidence, selected, endpoint, exactType, admitted⟩

theorem reconstructed_checked_target
    (admission : MatchAdmission assembly) (conversion : ConversionQualified assembly)
    {request input source proposition target}
    (reconstructed : assembly.reconstructMatch request input = some (source, proposition))
    {code : NativeRelatorConversionChecking.StepCode 0}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    FormationSensitive.Judgment assembly.rules .nil target proposition := by
  obtain ⟨_, _, _, admitted⟩ := admission _ _ _ _ reconstructed
  exact conversion.2.2.2 _ _ _ _ _ code admitted checked

theorem produced_hol_admission
    (qualified : HOLReplayQualified assembly) {gamma request proof}
    (produced : assembly.produceHOL gamma request = some proof) :
    (UniformListChartNIKService.intrinsicKernel gamma).decide request.claim proof = true ∧
    Mettapedia.Logic.HOL.ExtDerivation Mettapedia.Logic.HOL.UniformListInduction.Symbol
      request.claim.1 request.claim.2 ∧
    RepresentationAdmitted assembly gamma request.claim := by
  obtain ⟨binding, represented⟩ := qualified.2 _ _ _ produced
  have accepted := (UniformListChartNIKService.intrinsicKernel gamma).correct _ _ |>.mpr binding
  exact ⟨accepted, UniformListChartNIKService.native_acceptance_derivation _ _ _ accepted,
    represented⟩

theorem produced_hol_exact_claim
    (qualified : HOLReplayQualified assembly) {gamma request proof}
    (produced : assembly.produceHOL gamma request = some proof)
    (claim : UniformListChartNIKService.SourceClaim gamma) :
    (UniformListChartNIKService.intrinsicKernel gamma).decide claim proof = true ↔
      claim = request.claim := by
  rw [(UniformListChartNIKService.intrinsicKernel gamma).correct]
  change proof.1 = claim ↔ claim = request.claim
  rw [(qualified.2 _ _ _ produced).1]
  exact eq_comm

theorem qualified_execution
    (qualified : ExecutionQualified assembly)
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {code : Code Tower.Head NativeExamples.Operation n} {resultType : Tower.Tm n}
    (admitted : Judgment assembly.rules NativeExamples.signature sourceContext code resultType)
    {environment : Sub Tower.Head n m}
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    (typed : FormationSensitive.CtxMor assembly.rules sourceContext targetContext environment)
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm m) Nat}
    (returned : output ∈ runWorldsAt
      (Code.interpret (assembly.execution m).handler environment code) state branch) :
    FormationSensitive.Judgment assembly.rules targetContext output.answer
      (subst environment resultType) :=
  ImplementationStudy.qualified_interpretation (assembly.execution m) (qualified m)
    admitted target typed returned

/-- Erasing the intent-prefix annotations recovers execution of the same
dependent source program by the same assembly's actual handler. -/
theorem resume_erases_to_execution
    (qualified : ExecutionQualified assembly)
    (producer : Code Tower.Head NativeExamples.Operation 2) (state : Bool) (branch : BranchTrace) :
    (assembly.resume (runWorldsAt
      (Code.interpret (assembly.execution 2).handler ids producer) state branch)).map Prod.snd =
    runWorldsAt (Code.interpret (assembly.execution 2).handler ids
      (.sequenceSigma producer NativeExamples.body)) state branch := by
  rw [ImplementationStudy.qualified_worlds (assembly.execution 2) (qualified 2),
    ImplementationStudy.qualified_worlds (assembly.execution 2) (qualified 2)]
  simp only [Assembly.resume, Code.worlds, List.map_flatMap, List.map_map, Function.comp_def]

theorem observe_runPath (qualified : ContextualViewsQualified assembly)
    {a b : ContextViews.Scope} (path : Quiver.Path a b) (worlds : ContextViews.State a) :
    assembly.observe b (PolicyFamily.ContextClosure.runPath assembly.execute path worlds) =
      PolicyFamily.ContextClosure.runPath assembly.executeView path (assembly.observe a worlds) := by
  induction path with
  | nil => rfl
  | cons previous operation ih =>
      change ContextViews.Operation _ _ at operation
      cases operation
      change assembly.observe .resumed (assembly.resume _) = assembly.compactResume _
      rw [qualified.2, ih]

theorem observed_resumption_is_native
    (execution : ExecutionQualified assembly) (views : ContextualViewsQualified assembly)
    (producer : Code Tower.Head NativeExamples.Operation 2)
    {resultType : Tower.Tm 2}
    (admitted : Judgment assembly.rules NativeExamples.signature NativeExamples.context
      (.sequenceSigma producer NativeExamples.body) resultType)
    (formed : FormationSensitive.ContextFormation assembly.rules NativeExamples.context)
    (state : Bool) (branch : BranchTrace) :
    let worlds := runWorldsAt (Code.interpret (assembly.execution 2).handler ids producer) state branch
    assembly.observe .resumed (assembly.resume worlds) =
      assembly.compactResume (assembly.observe .producer worlds) ∧
    ∀ entry ∈ assembly.resume worlds,
      FormationSensitive.Judgment assembly.rules NativeExamples.context entry.2.answer resultType := by
  dsimp only
  refine ⟨views.2 _, ?_⟩
  intro entry member
  have erased : entry.2 ∈ (assembly.resume (runWorldsAt
      (Code.interpret (assembly.execution 2).handler ids producer) state branch)).map Prod.snd :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [resume_erases_to_execution execution] at erased
  have identityTyped : FormationSensitive.CtxMor assembly.rules
      NativeExamples.context NativeExamples.context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := assembly.rules) (Γ := NativeExamples.context) index)
  simpa only [subst_ids] using qualified_execution execution admitted formed identityTyped erased

/-! ## One actual inhabitant, without proof fields selecting its verdicts -/

def common : Assembly where
  declarations := HOLNativeRelatorCompatibility.signature
  execution := ImplementationStudy.Native.implementation
  reconstructMatch := MatchedIndexDependentTransport.reconstruct?
  produceHOL := UniformListChartNIKService.produce?
  View := ContextViews.Readout
  observe := ContextViews.readout
  compactResume := ContextViews.resumeReadout

theorem common_declarations : DeclarationsPreserved common :=
  ⟨HOLNativeRelatorCompatibility.signature_extends_hol,
    HOLNativeRelatorCompatibility.signature_extends_wire,
    fun _ _ known => HOLNativeRelatorCompatibility.hol_constant_preserved known,
    fun _ _ known => HOLNativeRelatorCompatibility.wire_relator_constant_preserved
      (NativeWireRelatorCompatibility.wire_constant_preserved known)⟩

theorem common_conversion : ConversionQualified common :=
  ⟨fun _ _ _ => HOLNativeRelatorCompatibility.checked_conversion_iff,
    HOLNativeRelatorCompatibility.root_preservation,
    fun _ _ _ _ _ => HOLNativeRelatorCompatibility.step_preserves,
    fun _ _ _ _ _ _ admitted checked =>
      HOLNativeRelatorCompatibility.checked_step_preserves admitted checked⟩

theorem common_match_admission : MatchAdmission common := by
  intro request input source proposition reconstructed
  obtain ⟨transport, accepted, same⟩ := Option.map_eq_some_iff.mp reconstructed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨transport, accepted, rfl, HOLNativeRelatorCompatibility.wire_relator_judgment
    (MatchedIndexDependentTransport.consume_source_admitted accepted)⟩

theorem common_match_coverage : MatchCoverage common := by
  intro request input transport accepted
  exact ⟨transport.source, congrArg
    (Option.map fun transport : MatchedIndexDependentTransport.Transport =>
      (transport.source, transport.proposition)) accepted⟩

theorem common_hol_replay : HOLReplayQualified common := by
  refine ⟨UniformListChartNIKService.produce_isSome_iff, ?_⟩
  intro gamma request proof produced
  obtain ⟨_, _, represented, assumptions, conclusionFormed, premisesFormed⟩ :=
    HOLNativeRelatorCompatibility.produced_source_admission_and_common_formation
      gamma request proof produced
  exact ⟨UniformListChartNIKService.produce_binds_request gamma request proof produced,
    FormationSensitiveHOLUniformList.rawMapLength, FormationSensitiveHOLUniformList.rawTheory,
    represented, assumptions, conclusionFormed, premisesFormed⟩

theorem common_execution : ExecutionQualified common :=
  OpaqueRelatorScopedComputation.qualified HOLNativeRelatorCompatibility.signature

theorem common_contextual_views : ContextualViewsQualified common :=
  ⟨fun scope => ⟨ContextViews.realization scope⟩, ContextViews.readout_resume⟩

def evidence : specification.Evidence common where
  supported := specification.required
  verifies := by
    intro requirement _
    cases requirement with
    | declarations => exact common_declarations
    | conversion => exact common_conversion
    | matchAdmission => exact common_match_admission
    | matchCoverage => exact common_match_coverage
    | holReplay => exact common_hol_replay
    | execution => exact common_execution
    | contextualViews => exact common_contextual_views

theorem remaining_empty : evidence.remaining = [] := by
  simp [Specification.Evidence.remaining, evidence, specification]

/-- Completion concerns exactly the seven named fragment obligations. -/
theorem common_qualified : specification.Satisfies common := evidence.complete remaining_empty

theorem fragment_inhabited : ∃ assembly, specification.Satisfies assembly :=
  ⟨common, common_qualified⟩

/-! ## An admitted reconstruction need not use the reference J syntax -/

def reflexiveMatch : Assembly :=
  { common with reconstructMatch := fun request input =>
      (MatchedIndexDependentTransport.consume? request input).map fun transport =>
        (transport.proof, transport.proposition) }

theorem reflexive_match_admission : MatchAdmission reflexiveMatch := by
  intro request input source proposition reconstructed
  obtain ⟨transport, accepted, same⟩ := Option.map_eq_some_iff.mp reconstructed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨transport, accepted, rfl, HOLNativeRelatorCompatibility.wire_relator_judgment
    (MatchedIndexDependentTransport.consume_proof_admitted accepted)⟩

theorem reflexive_match_coverage : MatchCoverage reflexiveMatch := by
  intro request input transport accepted
  exact ⟨transport.proof, congrArg
    (Option.map fun transport : MatchedIndexDependentTransport.Transport =>
      (transport.proof, transport.proposition)) accepted⟩

/-- All other components remain unchanged, while a different admitted proof
term reconstructs every validated receipt's exact selected proposition. -/
theorem reflexive_match_qualified : specification.Satisfies reflexiveMatch := by
  intro requirement member
  cases requirement with
  | matchAdmission => exact reflexive_match_admission
  | matchCoverage => exact reflexive_match_coverage
  | declarations => exact common_declarations
  | conversion => exact common_conversion
  | holReplay => exact common_hol_replay
  | execution => exact common_execution
  | contextualViews => exact common_contextual_views

theorem reference_and_reflexive_sources_differ
    (transport : MatchedIndexDependentTransport.Transport) :
    transport.source ≠ transport.proof := by
  intro equality
  cases equality

/-! ## Nonvacuity and implementation-sensitive controls -/

def decliningMatch : Assembly := { common with reconstructMatch := fun _ _ => none }

theorem declining_match_sound : MatchAdmission decliningMatch := by
  intro request input source proposition impossible
  cases impossible

theorem declining_match_not_covered : ¬ MatchCoverage decliningMatch := by
  intro covered
  obtain ⟨source, impossible⟩ := covered _ _ _
    (MatchedIndexDependentTransport.consume_checked_receipt _ _
      PolarizedNeedMatchedIndex.Examples.canonical_checked)
  cases impossible

theorem declining_match_not_qualified : ¬ specification.Satisfies decliningMatch := by
  intro qualified
  exact declining_match_not_covered (qualified .matchCoverage (by simp [specification]))

def decliningHOL : Assembly := { common with produceHOL := fun _ _ => none }

theorem declining_hol_not_qualified : ¬ HOLReplayQualified decliningHOL := by
  intro qualified
  have impossible := (qualified.1 [] (UniformListChartNIKService.actualRequest [])).mpr
    (UniformListChartNIKService.actual_replay_accepted [])
  cases impossible

def answerOnly : Assembly where
  declarations := common.declarations
  execution := common.execution
  reconstructMatch := common.reconstructMatch
  produceHOL := common.produceHOL
  View scope := match scope with
    | .producer => List (Tower.Tm 2)
    | .resumed => ContextViews.Readout .resumed
  observe scope := match scope with
    | .producer => ObservationStudy.answerView
    | .resumed => ContextViews.readout .resumed
  compactResume := fun answers => answers.map fun answer => (.pair answer (.refl answer), [])

theorem answer_only_execution_qualified : ExecutionQualified answerOnly := common_execution

theorem answer_only_not_supported : ¬ ContextualViewsQualified answerOnly := by
  intro supported
  exact ContextViews.Native.answer_only_failure.2.2 (supported.1 .producer)

/-- Both altered execution components agree with each other. That agreement
still does not qualify the wrong dependent result at scope two. -/
def misindexed : Assembly :=
  { common with execution := fun n =>
      if same : n = 2 then same ▸ ImplementationStudy.Native.misindexed
      else common.execution n }

theorem misindexed_realizes : ImplementationStudy.Realizes (misindexed.execution 2) := by
  simpa [misindexed] using ImplementationStudy.Native.misindexed_realizes

theorem misindexed_not_qualified : ¬ ExecutionQualified misindexed := by
  intro qualified
  apply (OpaqueRelatorScopedComputation.wrong_result_control
    HOLNativeRelatorCompatibility.opacity).2
  simpa [misindexed, Assembly.rules, common] using qualified 2

def collidingDeclarations : Assembly :=
  { common with declarations := HOLNativeRelatorCompatibility.collidingSignature }

theorem collision_not_preserved : ¬ DeclarationsPreserved collidingDeclarations := by
  intro preserved
  have unchanged := preserved.2.2.2 NativeWireData.dataName (sortTm Tower.zero) (by decide)
  have changed := HOLNativeRelatorCompatibility.collision_changes_wire_declaration.2.1
  have impossible := unchanged.symm.trans changed
  cases impossible

/-! ## Actual accepted and rejected workload inputs -/

theorem actual_match_admitted :
    ∃ source,
      common.reconstructMatch PolarizedNeedMatchedIndex.Examples.canonical.request
        (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.canonical) =
          some (source, (MatchedIndexDependentTransport.Transport.mk
            PolarizedNeedMatchedIndex.Examples.canonical PolarizedNeedMatchedIndex.Examples.b).proposition) ∧
      FormationSensitive.Judgment common.rules .nil source
        (MatchedIndexDependentTransport.Transport.mk
          PolarizedNeedMatchedIndex.Examples.canonical PolarizedNeedMatchedIndex.Examples.b).proposition :=
  validated_receipt_admitted common_match_admission common_match_coverage _ _
    PolarizedNeedMatchedIndex.Examples.canonical_checked

/-- The positive receipt is an answer of the actual matching service, not a
manually asserted authorization token. The same receipt drives admission. -/
theorem executed_match_admitted :
    ∃ fuel source,
      PolarizedNeedMatchedIndex.replyOutcome
          (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.canonical) ∈
        PolarizedNeedMatchedIndex.answers PolarizedNeedMatchedIndex.Examples.canonical.request
          PolarizedNeedMatchedIndex.Examples.canonical.request
          PolarizedNeedMatchedIndex.Examples.emptyWorld {} fuel ∧
      common.reconstructMatch PolarizedNeedMatchedIndex.Examples.canonical.request
        (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.canonical) =
          some (source, (MatchedIndexDependentTransport.Transport.mk
            PolarizedNeedMatchedIndex.Examples.canonical PolarizedNeedMatchedIndex.Examples.b).proposition) ∧
      FormationSensitive.Judgment common.rules .nil source
        (MatchedIndexDependentTransport.Transport.mk
          PolarizedNeedMatchedIndex.Examples.canonical PolarizedNeedMatchedIndex.Examples.b).proposition := by
  obtain ⟨fuel, observed⟩ := PolarizedNeedMatchedIndex.Examples.canonical_run
  obtain ⟨source, reconstructed, admitted⟩ := actual_match_admitted
  exact ⟨fuel, source, observed, reconstructed, admitted⟩

theorem altered_match_output_rejected :
    common.reconstructMatch PolarizedNeedMatchedIndex.Examples.canonical.request
      (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.changedOutput) = none :=
  match_rejects_invalid common_match_admission
    (MatchedIndexDependentTransport.consume_rejects_invalid
      PolarizedNeedMatchedIndex.Examples.changed_output_rejected)

theorem actual_hol_admitted_and_represented :
    (UniformListChartNIKService.intrinsicKernel []).decide
      (UniformListChartNIKService.mapLengthClaim [])
      (UniformListChartNIKService.actualNativeProof []) = true ∧
    Mettapedia.Logic.HOL.ExtDerivation Mettapedia.Logic.HOL.UniformListInduction.Symbol
      (UniformListChartNIKService.mapLengthClaim []).1
      (UniformListChartNIKService.mapLengthClaim []).2 ∧
    RepresentationAdmitted common [] (UniformListChartNIKService.mapLengthClaim []) :=
  produced_hol_admission common_hol_replay
    (gamma := []) (request := UniformListChartNIKService.actualRequest [])
    (proof := UniformListChartNIKService.actualNativeProof [])
    (UniformListChartNIKService.actual_produced [])

#print axioms match_acceptance_iff
#print axioms match_rejects_invalid
#print axioms validated_receipt_admitted
#print axioms reconstructed_selection
#print axioms reconstructed_checked_target
#print axioms produced_hol_admission
#print axioms produced_hol_exact_claim
#print axioms qualified_execution
#print axioms resume_erases_to_execution
#print axioms observe_runPath
#print axioms observed_resumption_is_native
#print axioms common_declarations
#print axioms common_conversion
#print axioms common_match_admission
#print axioms common_match_coverage
#print axioms common_hol_replay
#print axioms common_execution
#print axioms common_contextual_views
#print axioms common_qualified
#print axioms reflexive_match_qualified
#print axioms reference_and_reflexive_sources_differ
#print axioms declining_match_not_covered
#print axioms declining_hol_not_qualified
#print axioms answer_only_not_supported
#print axioms misindexed_not_qualified
#print axioms collision_not_preserved
#print axioms actual_match_admitted
#print axioms executed_match_admitted
#print axioms altered_match_output_rejected
#print axioms actual_hol_admitted_and_represented

#eval (common.reconstructMatch PolarizedNeedMatchedIndex.Examples.canonical.request
  (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.canonical)).isSome
#eval (common.reconstructMatch PolarizedNeedMatchedIndex.Examples.canonical.request
  (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.changedOutput)).isSome
#eval (common.produceHOL [] (UniformListChartNIKService.actualRequest [])).isSome

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentFragment
