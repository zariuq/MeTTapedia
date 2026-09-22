import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentSemanticRequirements
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentRetainedIdentityInterpretation

/-!
# Shared semantic requirements with retained native identity inputs

This comparison record keeps the same interpretation, universes, products,
sums, identity geometry, services and declarations. Only elimination consumes
a retained typed motive function on an independently qualified scope. The
original family-only record and its 31 requirements are unchanged.

Twenty-eight original predicate bodies and IDs are reused without changing
their native quantifiers. Five new clauses cover retained frames, scope,
constructor meaning, beta and substitution. Their new IDs do not discharge
the original family-only constructor-meaning requirement. All data are raw;
qualification and the caller's service/declaration requirements are separate.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentRetainedSemanticRequirements

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.DesignStudy
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive SharedJudgmentFragment
open Mettapedia.GSLT.LanguageDef
open KernelAuthority NIKMetalogic
open Mettapedia.TypeTheory

universe u v w w' uIndex uArtifact uEvidence

/-- No law, coverage witness or result-meaning proof is a field. The run
must produce its dependent output from membership in the supplied scope. -/
structure Data (assembly : Assembly) (C : Cwf.{u, v, w, w'})
    {Index : Type uIndex} (targets : Index → AdmissionObject.{uArtifact}) where
  interpretation : SharedJudgmentInterpretation.Data assembly C
  universes : SharedJudgmentUniverseInterpretation.Operations C
  products : ContextualTypeOperations.PiOperations C
  sums : ContextualTypeOperations.SigmaOperations C
  frames : SharedJudgmentTypeInterpretation.FrameOperations C
  scope : ContextualRetainedIdentityOperations.Input frames.identity frames.reflSection → Prop
  run : ContextualRetainedIdentityOperations.Run scope
  reindexing : ContextualBasedIdentityOperations.Reindexing frames.identity
  registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence} targets interpretation
  declarations : SharedJudgmentDeclarationInterpretation.Data interpretation

inductive SharedRequirement where
  | admittedTotal | substitutionsTotal | substitutionConstructors
  | typeSubstitution | termSubstitution | conversion | annotation
  | comprehension | families
  | piFormation | piIntroduction | piElimination | piBeta
  | sigmaFormation | sigmaIntroduction | sigmaElimination | sigmaBeta
  | identityFormation | reflexivity | motives | basedBoundary
  | sortMeaning | codeTotal | codesDecode | cumulativeMeaning
  | universeSubstitution | piCodeMeaning | sigmaCodeMeaning
  deriving DecidableEq, Repr

def SharedRequirement.original : SharedRequirement → SharedJudgmentSemanticRequirements.Requirement
  | .admittedTotal => .admittedTotal
  | .substitutionsTotal => .substitutionsTotal
  | .substitutionConstructors => .substitutionConstructors
  | .typeSubstitution => .typeSubstitution
  | .termSubstitution => .termSubstitution
  | .conversion => .conversion
  | .annotation => .annotation
  | .comprehension => .comprehension
  | .families => .families
  | .piFormation => .piFormation
  | .piIntroduction => .piIntroduction
  | .piElimination => .piElimination
  | .piBeta => .piBeta
  | .sigmaFormation => .sigmaFormation
  | .sigmaIntroduction => .sigmaIntroduction
  | .sigmaElimination => .sigmaElimination
  | .sigmaBeta => .sigmaBeta
  | .identityFormation => .identityFormation
  | .reflexivity => .reflexivity
  | .motives => .motives
  | .basedBoundary => .basedBoundary
  | .sortMeaning => .sortMeaning
  | .codeTotal => .codeTotal
  | .codesDecode => .codesDecode
  | .cumulativeMeaning => .cumulativeMeaning
  | .universeSubstitution => .universeSubstitution
  | .piCodeMeaning => .piCodeMeaning
  | .sigmaCodeMeaning => .sigmaCodeMeaning

def sharedRequirements : List SharedRequirement :=
  [.admittedTotal, .substitutionsTotal, .substitutionConstructors,
    .typeSubstitution, .termSubstitution, .conversion, .annotation,
    .comprehension, .families,
    .piFormation, .piIntroduction, .piElimination, .piBeta,
    .sigmaFormation, .sigmaIntroduction, .sigmaElimination, .sigmaBeta,
    .identityFormation, .reflexivity, .motives, .basedBoundary,
    .sortMeaning, .codeTotal, .codesDecode, .cumulativeMeaning,
    .universeSubstitution, .piCodeMeaning, .sigmaCodeMeaning]

/-- Exactly the three operation-dependent clauses change; the original
native motive-coverage and boundary clauses remain required verbatim. -/
theorem shared_requirements_exact :
    sharedRequirements.map SharedRequirement.original =
      SharedJudgmentSemanticRequirements.requirements.filter
        (fun requirement => requirement != .basedJ && requirement != .basedBeta &&
          requirement != .basedSubstitution) := by decide

inductive RetainedRequirement where
  | frameCoverage | scopeCoverage | constructorMeaning | admittedBeta | admittedSubstitution
  deriving DecidableEq, Repr

def RetainedRequirement.id : RetainedRequirement → String
  | .frameCoverage => "SEM-RID-001"
  | .scopeCoverage => "SEM-RID-002"
  | .constructorMeaning => "SEM-RID-003"
  | .admittedBeta => "SEM-RID-004"
  | .admittedSubstitution => "SEM-RID-005"

def retainedRequirements : List RetainedRequirement :=
  [.frameCoverage, .scopeCoverage, .constructorMeaning, .admittedBeta, .admittedSubstitution]

inductive Requirement where
  | shared : SharedRequirement → Requirement
  | retained : RetainedRequirement → Requirement
  deriving DecidableEq, Repr

def Requirement.id : Requirement → String
  | .shared requirement => requirement.original.id
  | .retained requirement => requirement.id

def Requirement.references : Requirement → List String
  | .shared requirement => requirement.original.references
  | .retained _ => ["INV-TT-001", "INV-TT-004", "INV-TT-007"]

def requirements : List Requirement :=
  sharedRequirements.map .shared ++ retainedRequirements.map .retained

theorem requirement_mem (requirement : Requirement) : requirement ∈ requirements := by
  cases requirement with
  | shared requirement => cases requirement <;> decide
  | retained requirement => cases requirement <;> decide

theorem requirement_count : requirements.length = 33 := by decide

theorem requirement_ids_unique : (requirements.map Requirement.id).Nodup := by decide

theorem changed_original_ids_absent :
    "SEM-ID-004" ∉ requirements.map Requirement.id ∧
      "SEM-ID-005" ∉ requirements.map Requirement.id ∧
      "SEM-ID-007" ∉ requirements.map Requirement.id := by decide

theorem combined_requirement_ids_unique :
    (requirements.map Requirement.id ++
      SharedJudgmentSemanticRequirements.declarationRequirements.map
        SharedJudgmentSemanticRequirements.DeclarationRequirement.id).Nodup := by decide

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}
  {Index : Type uIndex} {targets : Index → AdmissionObject.{uArtifact}}

def sharedHolds (requirement : SharedRequirement)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) : Prop :=
  match requirement with
  | .admittedTotal => SharedJudgmentInterpretation.AdmittedTotal data.interpretation
  | .substitutionsTotal => SharedJudgmentInterpretation.AdmittedSubstitutionsTotal data.interpretation
  | .substitutionConstructors => SharedJudgmentInterpretation.SubstitutionConstructors data.interpretation
  | .typeSubstitution => SharedJudgmentInterpretation.TypeSubstitutionStable data.interpretation
  | .termSubstitution => SharedJudgmentInterpretation.TermSubstitutionStable data.interpretation
  | .conversion => SharedJudgmentInterpretation.ConversionInvariant data.interpretation
  | .annotation => SharedJudgmentInterpretation.AnnotationTransport data.interpretation
  | .comprehension => SharedJudgmentTypeInterpretation.ComprehensionCoverage data.interpretation
  | .families => SharedJudgmentTypeInterpretation.FamilyCoverage data.interpretation
  | .piFormation => SharedJudgmentTypeInterpretation.PiFormationMeaning data.interpretation data.products
  | .piIntroduction => SharedJudgmentTypeInterpretation.PiIntroductionMeaning data.interpretation data.products
  | .piElimination => SharedJudgmentTypeInterpretation.PiEliminationMeaning data.interpretation data.products
  | .piBeta => SharedJudgmentTypeInterpretation.AdmittedPiBeta data.interpretation data.products
  | .sigmaFormation => SharedJudgmentTypeInterpretation.SigmaFormationMeaning data.interpretation data.sums
  | .sigmaIntroduction => SharedJudgmentTypeInterpretation.SigmaIntroductionMeaning data.interpretation data.sums
  | .sigmaElimination => SharedJudgmentTypeInterpretation.SigmaEliminationMeaning data.interpretation data.sums
  | .sigmaBeta => SharedJudgmentTypeInterpretation.AdmittedSigmaBeta data.interpretation data.sums
  | .identityFormation => SharedJudgmentTypeInterpretation.IdentityFormationMeaning data.interpretation data.frames.identity
  | .reflexivity => SharedJudgmentTypeInterpretation.ReflexivityMeaning data.interpretation data.frames.reflexivity
  | .motives => SharedJudgmentTypeInterpretation.BasedMotiveCoverage data.interpretation data.frames
  | .basedBoundary => SharedJudgmentTypeInterpretation.AdmittedBasedBoundary data.interpretation data.frames
  | .sortMeaning => SharedJudgmentUniverseInterpretation.SortMeaning data.interpretation data.universes
  | .codeTotal => SharedJudgmentUniverseInterpretation.CodeTotal data.interpretation data.universes
  | .codesDecode => SharedJudgmentUniverseInterpretation.CodesDecode data.interpretation data.universes
  | .cumulativeMeaning => SharedJudgmentUniverseInterpretation.CumulativeMeaning data.interpretation data.universes
  | .universeSubstitution => data.universes.universe.SubstitutionStable
  | .piCodeMeaning => SharedJudgmentUniverseTypeCoherence.PiCodeMeaning data.interpretation data.universes
  | .sigmaCodeMeaning => SharedJudgmentUniverseTypeCoherence.SigmaCodeMeaning data.interpretation data.universes

def retainedHolds (requirement : RetainedRequirement)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) : Prop :=
  match requirement with
  | .frameCoverage => SharedJudgmentRetainedIdentityInterpretation.FrameCoverage data.interpretation data.frames
  | .scopeCoverage => SharedJudgmentRetainedIdentityInterpretation.ScopeCoverage data.interpretation data.frames data.scope
  | .constructorMeaning => SharedJudgmentRetainedIdentityInterpretation.ConstructorMeaning data.interpretation data.frames data.scope data.run
  | .admittedBeta => SharedJudgmentRetainedIdentityInterpretation.AdmittedBeta data.interpretation data.frames data.scope data.run
  | .admittedSubstitution => SharedJudgmentRetainedIdentityInterpretation.AdmittedSubstitution data.interpretation data.frames data.scope data.run data.reindexing

def holds (requirement : Requirement)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) : Prop :=
  match requirement with
  | .shared requirement => sharedHolds requirement data
  | .retained requirement => retainedHolds requirement data

def semanticSpecification :
    Specification (Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) Requirement :=
  ⟨holds, requirements⟩

/-- The service contract and required declaration instances are external
parameters, exactly as in the original profile. -/
def serviceSpecification
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets) :
    Specification (Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
      (SharedJudgmentServiceRegistry.Requirement ⊕ SharedJudgmentServiceRegistry.BindingRequirement) where
  holds requirement data :=
    (SharedJudgmentServiceRegistry.requiredSpecification contract data.interpretation).holds requirement data.registry
  required := [.inl .faces, .inl .services, .inl .native, .inl .meaning,
    .inr .requests, .inr .surfaces]

def declarationHolds (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (requirement : SharedJudgmentSemanticRequirements.DeclarationRequirement)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) : Prop :=
  match requirement with
  | .present => ∀ slot, required slot → slot.Admitted assembly
  | .coverage => SharedJudgmentDeclarationInterpretation.Coverage required data.declarations
  | .typeMeaning => SharedJudgmentDeclarationInterpretation.ClosedTypeAgreement data.declarations
  | .headMeaning => SharedJudgmentDeclarationInterpretation.ClosedHeadAgreement data.declarations

def declarationSpecification (required : SharedJudgmentDeclarationInterpretation.Instance → Prop) :
    Specification (Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
      SharedJudgmentSemanticRequirements.DeclarationRequirement :=
  ⟨declarationHolds required, SharedJudgmentSemanticRequirements.declarationRequirements⟩

def specification
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop) :=
  (((SharedJudgmentFragment.specification.pullback
    (fun _ : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets => assembly)).conjoin
      semanticSpecification).conjoin (serviceSpecification contract)).conjoin
        (declarationSpecification required)

theorem satisfies_iff
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) :
    (specification contract required).Satisfies data ↔
      SharedJudgmentFragment.specification.Satisfies assembly ∧
      (∀ requirement, holds requirement data) ∧
      (SharedJudgmentServiceRegistry.requiredSpecification contract data.interpretation).Satisfies data.registry ∧
      (∀ requirement, declarationHolds required requirement data) := by
  have service : (serviceSpecification contract).Satisfies data ↔
      (SharedJudgmentServiceRegistry.requiredSpecification contract data.interpretation).Satisfies data.registry := Iff.rfl
  simp only [specification, Specification.satisfies_conjoin_iff,
    Specification.satisfies_pullback_iff, service]
  constructor
  · rintro ⟨⟨⟨source, semantics⟩, services⟩, declarations⟩
    exact ⟨source, fun requirement => semantics requirement (requirement_mem requirement), services,
      fun requirement => declarations requirement
        (SharedJudgmentSemanticRequirements.declarationRequirement_mem requirement)⟩
  · rintro ⟨source, semantics, services, declarations⟩
    exact ⟨⟨⟨source, fun requirement _ => semantics requirement⟩, services⟩,
      fun requirement _ => declarations requirement⟩

/-- Restrict an existing full operation without altering any of its common
data. The supplied scope is not automatically covered or substitution closed. -/
def Data.ofFull
    (data : SharedJudgmentSemanticRequirements.Data.{u, v, w, w', uIndex, uArtifact, uEvidence}
      assembly C targets)
    (scope : ContextualRetainedIdentityOperations.Input
      data.constructors.frames.identity data.constructors.frames.reflSection → Prop) :
    Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets where
  interpretation := data.interpretation
  universes := data.universes
  products := data.constructors.products
  sums := data.constructors.sums
  frames := data.constructors.frames
  scope := scope
  run := SharedJudgmentRetainedIdentityInterpretation.fullRun data.constructors scope
  reindexing := data.constructors.based.reindexing
  registry := data.registry
  declarations := data.declarations

/-- Reuse is literal equality of predicate bodies, not an implication
obtained by narrowing the original native quantifiers. -/
theorem shared_ofFull_exact
    (data : SharedJudgmentSemanticRequirements.Data.{u, v, w, w', uIndex, uArtifact, uEvidence}
      assembly C targets)
    (scope : ContextualRetainedIdentityOperations.Input
      data.constructors.frames.identity data.constructors.frames.reflSection → Prop)
    (requirement : SharedRequirement) :
    sharedHolds requirement (Data.ofFull data scope) =
      SharedJudgmentSemanticRequirements.holds requirement.original data := by
  cases requirement <;> rfl

theorem declaration_ofFull_exact
    (data : SharedJudgmentSemanticRequirements.Data.{u, v, w, w', uIndex, uArtifact, uEvidence}
      assembly C targets)
    (scope : ContextualRetainedIdentityOperations.Input
      data.constructors.frames.identity data.constructors.frames.reflSection → Prop)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (requirement : SharedJudgmentSemanticRequirements.DeclarationRequirement) :
    declarationHolds required requirement (Data.ofFull data scope) =
      SharedJudgmentSemanticRequirements.declarationHolds required requirement data := by
  cases requirement <;> rfl

/-- Full-profile qualification implies retained constructor and beta
meaning and extends all qualified frames. It does not imply scope coverage,
the section square, or closure of an independently proposed scope. -/
theorem full_qualified_restricts
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : SharedJudgmentSemanticRequirements.Data.{u, v, w, w', uIndex, uArtifact, uEvidence}
      assembly C targets)
    (scope : ContextualRetainedIdentityOperations.Input
      data.constructors.frames.identity data.constructors.frames.reflSection → Prop)
    (qualified : (SharedJudgmentSemanticRequirements.specification contract required).Satisfies data) :
    (∀ requirement, sharedHolds requirement (Data.ofFull data scope)) ∧
      retainedHolds .frameCoverage (Data.ofFull data scope) ∧
      retainedHolds .constructorMeaning (Data.ofFull data scope) ∧
      retainedHolds .admittedBeta (Data.ofFull data scope) := by
  have semantics := ((SharedJudgmentSemanticRequirements.satisfies_iff contract required data).mp qualified).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro requirement
    rw [shared_ofFull_exact]
    exact semantics requirement.original
  · exact SharedJudgmentRetainedIdentityInterpretation.frameCoverage_of_admittedTotal
      data.interpretation data.constructors.frames (semantics .motives) (semantics .admittedTotal)
  · exact SharedJudgmentRetainedIdentityInterpretation.full_induces_meaning
      data.interpretation data.constructors scope (semantics .basedJ)
  · exact SharedJudgmentRetainedIdentityInterpretation.full_induces_beta
      data.interpretation data.constructors scope (semantics .basedBeta)

/-- Even a raw run on an empty scope cannot evade a required, genuinely
admitted native tuple. Frame coverage and scope coverage are both essential. -/
theorem empty_scope_excluded
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (empty : ∀ input, ¬ data.scope input)
    (coverage : retainedHolds .frameCoverage data)
    {n : Nat} {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) : ¬ retainedHolds .scopeCoverage data := by
  intro scopes
  obtain ⟨retained, meaning⟩ := coverage.exists_frame parameters
  exact empty retained.input (scopes n source type left motive method retained parameters meaning)

/-- The source tuple exists for every assembly: all four parameters of the
actual native identity declaration are variables in its formed telescope. -/
theorem qualified_scope_nonempty
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (qualified : semanticSpecification.Satisfies data) : ∃ input, data.scope input := by
  have coverage : SharedJudgmentRetainedIdentityInterpretation.FrameCoverage data.interpretation data.frames :=
    qualified (.retained .frameCoverage) (requirement_mem _)
  have scopes : SharedJudgmentRetainedIdentityInterpretation.ScopeCoverage data.interpretation data.frames data.scope :=
    qualified (.retained .scopeCoverage) (requirement_mem _)
  obtain ⟨retained, meaning⟩ := coverage.exists_frame
    (source := SharedJudgmentTypeInterpretation.Controls.sourceContext assembly)
    (SharedJudgmentTypeInterpretation.Controls.parameters assembly)
  exact ⟨retained.input, scopes _ _ _ _ _ _ retained
    (SharedJudgmentTypeInterpretation.Controls.parameters assembly) meaning⟩

#print axioms full_qualified_restricts
#print axioms empty_scope_excluded
#print axioms qualified_scope_nonempty

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentRetainedSemanticRequirements
