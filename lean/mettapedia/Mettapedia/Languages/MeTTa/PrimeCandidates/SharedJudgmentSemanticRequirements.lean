import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseTypeCoherence
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceRegistry
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceTypeCoherence
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentDeclarationInterpretation

/-!
# Semantic requirements on one shared native candidate

The assembly, semantic CwF and required service targets are supplied outside
the proposed interpretation. Raw interpretation, universe operations, type
operations, declaration meanings and the registry inhabit one dependent record. No qualification
proof is a field of that record.

This collects the existing native-fragment contracts using `DesignStudy`.
It does not claim that they are jointly inhabited, or that the finite source
protocol covers all required public CBPV operations. The declaration clauses
require the caller's exact instances, including their installation and closed
formation; an empty partial table cannot evade that request. Presheaf
comparison, public consumers and the full mixed model still need their own
same-data qualification. In particular, this is not TRACE-004's
complete six-family specification or ASM-005's model.

The clauses retain the comparison conventions of their source interfaces.
No strict context-object equality, global code uniqueness, K/UIP or enclosing
universe operator is added. These are requirements for the displayed
interpretation class, not a proof that every possible host must use it.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentSemanticRequirements

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.DesignStudy
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive SharedJudgmentFragment
open Mettapedia.GSLT.LanguageDef
open KernelAuthority NIKMetalogic


universe u v w w' uIndex uArtifact uEvidence

structure Data (assembly : Assembly) (C : Cwf.{u, v, w, w'})
    {Index : Type uIndex} (targets : Index → AdmissionObject.{uArtifact}) where
  interpretation : SharedJudgmentInterpretation.Data assembly C
  universes : SharedJudgmentUniverseInterpretation.Operations C
  constructors : SharedJudgmentTypeInterpretation.Operations C
  registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence} targets interpretation
  declarations : SharedJudgmentDeclarationInterpretation.Data interpretation

inductive Requirement where
  | admittedTotal | substitutionsTotal | substitutionConstructors
  | typeSubstitution | termSubstitution | conversion | annotation
  | comprehension | families
  | piFormation | piIntroduction | piElimination | piBeta
  | sigmaFormation | sigmaIntroduction | sigmaElimination | sigmaBeta
  | identityFormation | reflexivity | motives | basedJ | basedBeta
  | basedBoundary | basedSubstitution
  | sortMeaning | codeTotal | codesDecode | cumulativeMeaning
  | universeSubstitution | piCodeMeaning | sigmaCodeMeaning
  deriving DecidableEq, Repr

/-- Stable requirement identities, distinct from IDs of theorem evidence. -/
def Requirement.id : Requirement → String
  | .admittedTotal => "SEM-ADM-001"
  | .substitutionsTotal => "SEM-ADM-002"
  | .substitutionConstructors => "SEM-ADM-003"
  | .typeSubstitution => "SEM-ADM-004"
  | .termSubstitution => "SEM-ADM-005"
  | .conversion => "SEM-ADM-006"
  | .annotation => "SEM-ADM-007"
  | .comprehension => "SEM-TY-001"
  | .families => "SEM-TY-002"
  | .piFormation => "SEM-TY-003"
  | .piIntroduction => "SEM-TY-004"
  | .piElimination => "SEM-TY-005"
  | .piBeta => "SEM-TY-006"
  | .sigmaFormation => "SEM-TY-007"
  | .sigmaIntroduction => "SEM-TY-008"
  | .sigmaElimination => "SEM-TY-009"
  | .sigmaBeta => "SEM-TY-010"
  | .identityFormation => "SEM-ID-001"
  | .reflexivity => "SEM-ID-002"
  | .motives => "SEM-ID-003"
  | .basedJ => "SEM-ID-004"
  | .basedBeta => "SEM-ID-005"
  | .basedBoundary => "SEM-ID-006"
  | .basedSubstitution => "SEM-ID-007"
  | .sortMeaning => "SEM-U-001"
  | .codeTotal => "SEM-U-002"
  | .codesDecode => "SEM-U-003"
  | .cumulativeMeaning => "SEM-U-004"
  | .universeSubstitution => "SEM-U-005"
  | .piCodeMeaning => "SEM-U-006"
  | .sigmaCodeMeaning => "SEM-U-007"

/-- Normative source references motivate the obligations; this mapping
does not assert that the source determines a unique interpretation class. -/
def Requirement.references : Requirement → List String
  | .sortMeaning | .codeTotal | .codesDecode | .cumulativeMeaning
  | .universeSubstitution | .piCodeMeaning | .sigmaCodeMeaning =>
      ["INV-TT-001", "INV-TT-006", "INV-TT-009"]
  | .identityFormation | .reflexivity | .motives | .basedJ | .basedBeta
  | .basedBoundary | .basedSubstitution => ["INV-TT-001", "INV-TT-004", "INV-TT-007"]
  | _ => ["INV-TT-001", "INV-TT-003", "INV-TT-004"]

def requirements : List Requirement :=
  [.admittedTotal, .substitutionsTotal, .substitutionConstructors,
    .typeSubstitution, .termSubstitution, .conversion, .annotation,
    .comprehension, .families,
    .piFormation, .piIntroduction, .piElimination, .piBeta,
    .sigmaFormation, .sigmaIntroduction, .sigmaElimination, .sigmaBeta,
    .identityFormation, .reflexivity, .motives, .basedJ, .basedBeta,
    .basedBoundary, .basedSubstitution,
    .sortMeaning, .codeTotal, .codesDecode, .cumulativeMeaning,
    .universeSubstitution, .piCodeMeaning, .sigmaCodeMeaning]

theorem requirement_mem (requirement : Requirement) : requirement ∈ requirements := by
  cases requirement <;> decide

theorem requirement_ids_unique : (requirements.map Requirement.id).Nodup := by decide

inductive DeclarationRequirement where
  | present | coverage | typeMeaning | headMeaning
  deriving DecidableEq, Repr

def DeclarationRequirement.id : DeclarationRequirement → String
  | .present => "SEM-DECL-001"
  | .coverage => "SEM-DECL-002"
  | .typeMeaning => "SEM-DECL-003"
  | .headMeaning => "SEM-DECL-004"

def DeclarationRequirement.references (_requirement : DeclarationRequirement) : List String :=
  ["INV-TT-001", "INV-TT-003", "INV-TT-004", "INV-TT-006"]

def declarationRequirements : List DeclarationRequirement :=
  [.present, .coverage, .typeMeaning, .headMeaning]

theorem declarationRequirement_mem (requirement : DeclarationRequirement) :
    requirement ∈ declarationRequirements := by
  cases requirement <;> decide

theorem combined_requirement_ids_unique :
    (requirements.map Requirement.id ++ declarationRequirements.map DeclarationRequirement.id).Nodup := by
  decide

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}
  {Index : Type uIndex} {targets : Index → AdmissionObject.{uArtifact}}

/-- The caller specifies exact schema/level instances. Presence and native
formation are separate from semantic coverage, so an absent requested entry
cannot make coverage true by an empty admission domain. -/
def declarationHolds (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (requirement : DeclarationRequirement)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) : Prop :=
  match requirement with
  | .present => ∀ slot, required slot → slot.Admitted assembly
  | .coverage => SharedJudgmentDeclarationInterpretation.Coverage required data.declarations
  | .typeMeaning => SharedJudgmentDeclarationInterpretation.ClosedTypeAgreement data.declarations
  | .headMeaning => SharedJudgmentDeclarationInterpretation.ClosedHeadAgreement data.declarations

def declarationSpecification (required : SharedJudgmentDeclarationInterpretation.Instance → Prop) :
    Specification (Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
      DeclarationRequirement :=
  ⟨declarationHolds required, declarationRequirements⟩

def holds (requirement : Requirement)
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
  | .piFormation => SharedJudgmentTypeInterpretation.PiFormationMeaning data.interpretation data.constructors.products
  | .piIntroduction => SharedJudgmentTypeInterpretation.PiIntroductionMeaning data.interpretation data.constructors.products
  | .piElimination => SharedJudgmentTypeInterpretation.PiEliminationMeaning data.interpretation data.constructors.products
  | .piBeta => SharedJudgmentTypeInterpretation.AdmittedPiBeta data.interpretation data.constructors.products
  | .sigmaFormation => SharedJudgmentTypeInterpretation.SigmaFormationMeaning data.interpretation data.constructors.sums
  | .sigmaIntroduction => SharedJudgmentTypeInterpretation.SigmaIntroductionMeaning data.interpretation data.constructors.sums
  | .sigmaElimination => SharedJudgmentTypeInterpretation.SigmaEliminationMeaning data.interpretation data.constructors.sums
  | .sigmaBeta => SharedJudgmentTypeInterpretation.AdmittedSigmaBeta data.interpretation data.constructors.sums
  | .identityFormation => SharedJudgmentTypeInterpretation.IdentityFormationMeaning data.interpretation data.constructors.identity
  | .reflexivity => SharedJudgmentTypeInterpretation.ReflexivityMeaning data.interpretation data.constructors.reflexivity
  | .motives => SharedJudgmentTypeInterpretation.BasedMotiveCoverage data.interpretation data.constructors.frames
  | .basedJ => SharedJudgmentTypeInterpretation.BasedJMeaning data.interpretation data.constructors
  | .basedBeta => SharedJudgmentTypeInterpretation.AdmittedBasedBeta data.interpretation data.constructors
  | .basedBoundary => SharedJudgmentTypeInterpretation.AdmittedBasedBoundary data.interpretation data.constructors.frames
  | .basedSubstitution => SharedJudgmentTypeInterpretation.AdmittedBasedSubstitution data.interpretation data.constructors
  | .sortMeaning => SharedJudgmentUniverseInterpretation.SortMeaning data.interpretation data.universes
  | .codeTotal => SharedJudgmentUniverseInterpretation.CodeTotal data.interpretation data.universes
  | .codesDecode => SharedJudgmentUniverseInterpretation.CodesDecode data.interpretation data.universes
  | .cumulativeMeaning => SharedJudgmentUniverseInterpretation.CumulativeMeaning data.interpretation data.universes
  | .universeSubstitution => data.universes.universe.SubstitutionStable
  | .piCodeMeaning => SharedJudgmentUniverseTypeCoherence.PiCodeMeaning data.interpretation data.universes
  | .sigmaCodeMeaning => SharedJudgmentUniverseTypeCoherence.SigmaCodeMeaning data.interpretation data.universes

def semanticSpecification :
    Specification (Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) Requirement :=
  ⟨holds, requirements⟩

/-- The service predicates read the registry indexed by this very
interpretation. The contract's required inputs do not come from that registry. -/
def serviceSpecification (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets) :
    Specification (Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
      (SharedJudgmentServiceRegistry.Requirement ⊕ SharedJudgmentServiceRegistry.BindingRequirement) where
  holds requirement data :=
    (SharedJudgmentServiceRegistry.requiredSpecification contract data.interpretation).holds requirement data.registry
  required := [.inl .faces, .inl .services, .inl .native, .inl .meaning,
    .inr .requests, .inr .surfaces]

theorem service_satisfies_iff
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets) :
    (serviceSpecification contract).Satisfies data ↔
      (SharedJudgmentServiceRegistry.requiredSpecification contract data.interpretation).Satisfies data.registry :=
  Iff.rfl

/-- This is the native fragment collection, not the final language contract.
All four components use the same assembly and interpretation. The declaration
requirement domain is supplied by the caller, not selected by the proposed table. -/
def specification (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
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
  simp only [specification, Specification.satisfies_conjoin_iff,
    Specification.satisfies_pullback_iff, service_satisfies_iff]
  constructor
  · rintro ⟨⟨⟨source, semantics⟩, services⟩, declarations⟩
    exact ⟨source, fun requirement => semantics requirement (requirement_mem requirement), services,
      fun requirement => declarations requirement (declarationRequirement_mem requirement)⟩
  · rintro ⟨source, semantics, services, declarations⟩
    exact ⟨⟨⟨source, fun requirement _ => semantics requirement⟩, services⟩,
      fun requirement _ => declarations requirement⟩

/-- In the opaque declaration class, qualification interprets the actual
native conversion rule, including its change of displayed annotation. This
uses the independent annotation clause, not only equality of normal forms. -/
theorem qualified_conversion_rule
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    (qualified : (specification contract required).Satisfies data) :
    SharedJudgmentInterpretation.ConversionRuleSound data.interpretation := by
  have semantics := ((satisfies_iff contract required data).mp qualified).2.1
  have conversion : SharedJudgmentInterpretation.ConversionInvariant data.interpretation :=
    semantics .conversion
  have annotation : SharedJudgmentInterpretation.AnnotationTransport data.interpretation :=
    semantics .annotation
  have developed :=
    (SharedJudgmentInterpretation.conversion_invariant_iff_development_invariant
      opacity data.interpretation).mp conversion
  exact (SharedJudgmentInterpretation.conversion_rule_sound_iff_annotation_transport
    opacity data.interpretation developed.1).mpr annotation

/-- Service use and native type-code coverage read this very record's
interpretation. A successful request does not supply formation of its type;
that premise is independently stated at the returned attachment's context. -/
theorem qualified_accepted_type_has_code
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (qualified : (specification contract required).Satisfies data)
    (index : Index)
    (request : NIKServiceInvocation.Request
      (data.registry.serviceAt
        (SharedJudgmentServiceTypeCoherence.requiredQualification contract data.registry
          ((satisfies_iff contract required data).mp qualified).2.2.1) index))
    (input : NIKServiceInvocation.InputAdmission request)
    {claim : (targets index).Carrier}
    (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some claim)
    {level : LevelExpr Nat}
    (formed : Judgment assembly.rules ((data.registry.attachment index).context claim)
      ((data.registry.attachment index).nativeType claim) (sortTm level)) :
    ∃ code : C.Tm (data.interpretation.ctx (SharedJudgmentInterpretation.Context.ofJudgment formed))
        (data.universes.universe.univ
          (data.interpretation.ctx (SharedJudgmentInterpretation.Context.ofJudgment formed)) level),
      data.interpretation.term (SharedJudgmentInterpretation.Context.ofJudgment formed)
        ((data.registry.attachment index).nativeType claim) (sortTm level)
        (data.universes.universe.univ
          (data.interpretation.ctx (SharedJudgmentInterpretation.Context.ofJudgment formed)) level) code ∧
      data.interpretation.ty (SharedJudgmentInterpretation.Context.ofJudgment formed)
        ((data.registry.attachment index).nativeType claim) (data.universes.universe.el code) ∧
      data.interpretation.term (SharedJudgmentInterpretation.Context.ofJudgment formed)
        ((data.registry.attachment index).payload claim) ((data.registry.attachment index).nativeType claim)
        ((data.registry.attachment index).semanticType claim formed.context)
        ((data.registry.attachment index).value claim formed.context) := by
  have semantics := ((satisfies_iff contract required data).mp qualified).2.1
  obtain ⟨_, _, payloadMeaning, code, codeMeaning, decoded, _⟩ :=
    SharedJudgmentServiceTypeCoherence.accepted_type_has_code contract data.registry
      ((satisfies_iff contract required data).mp qualified).2.2.1 data.universes
      (semantics .codesDecode) index request input accepted formed (semantics .codeTotal)
  exact ⟨code, codeMeaning, decoded, payloadMeaning⟩

/-- The required declaration is genuinely installed and formed, and its
closed meaning extends to any formed caller context via the same native and
semantic substitution actions used by the rest of this record. -/
theorem qualified_required_head
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (qualified : (specification contract required).Satisfies data)
    (slot : SharedJudgmentDeclarationInterpretation.Instance) (needed : required slot)
    {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n)
    (formed : ContextFormation assembly.rules context.raw) :
    slot.Admitted assembly ∧
      ∃ (meaning : SharedJudgmentDeclarationInterpretation.Meaning data.interpretation)
        (semantic : C.Sub (data.interpretation.ctx context) (data.interpretation.ctx .nil)),
        data.declarations.meaning slot = some meaning ∧
        data.interpretation.sub .nil context (renSub Fin.elim0) semantic ∧
        Judgment assembly.rules context.raw (.const slot.name) (liftClosed slot.entry.type) ∧
        data.interpretation.ty context (liftClosed slot.entry.type) (C.tySub meaning.type semantic) ∧
        data.interpretation.term context (.const slot.name) (liftClosed slot.entry.type)
          (C.tySub meaning.type semantic) (C.tmSub meaning.value semantic) := by
  have semantics := ((satisfies_iff contract required data).mp qualified).2.1
  have declarations := ((satisfies_iff contract required data).mp qualified).2.2.2
  have admitted := declarations .present slot needed
  refine ⟨admitted, ?_⟩
  exact SharedJudgmentDeclarationInterpretation.required_declared_head_meaning
    data.interpretation data.declarations required
    (declarations .coverage) (declarations .typeMeaning) (declarations .headMeaning)
    ⟨semantics .typeSubstitution, semantics .termSubstitution⟩
    (semantics .substitutionsTotal) slot needed admitted context formed

/-- A required missing declaration is rejected even when the partial
semantic table vacuously agrees on every entry it happens to contain. -/
theorem required_entry_missing_excluded
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (slot : SharedJudgmentDeclarationInterpretation.Instance) (needed : required slot)
    (missing : assembly.declarations.entries slot.name = none) :
    ¬ (specification contract required).Satisfies data := by
  intro qualified
  have installed := (((satisfies_iff contract required data).mp qualified).2.2.2
    .present slot needed).1.1
  rw [missing] at installed
  cases installed

/-- Original source qualification supplies no semantic evidence merely
because a proposed raw record has that source as its index. -/
def sourceEvidence
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (qualified : SharedJudgmentFragment.specification.Satisfies assembly) :
    (specification contract required).Evidence data where
  supported := SharedJudgmentFragment.specification.required.map (fun r => Sum.inl (Sum.inl (Sum.inl r)))
  verifies := by
    intro requirement member
    obtain ⟨source, required, rfl⟩ := List.mem_map.mp member
    exact qualified source required

/-- The entire semantic interface remains outstanding until evidence is
provided at the actual interpretation index, even for a qualified source. -/
theorem source_evidence_retains_semantic_obligations
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (qualified : SharedJudgmentFragment.specification.Satisfies assembly)
    (requirement : Requirement) :
    Sum.inl (Sum.inl (Sum.inr requirement)) ∈ (sourceEvidence contract required data qualified).remaining := by
  simp [Specification.Evidence.remaining, sourceEvidence, specification,
    Specification.conjoin, Specification.pullback, semanticSpecification, requirement_mem]

theorem source_evidence_retains_declaration_obligations
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (qualified : SharedJudgmentFragment.specification.Satisfies assembly)
    (requirement : DeclarationRequirement) :
    Sum.inr requirement ∈ (sourceEvidence contract required data qualified).remaining := by
  simp [Specification.Evidence.remaining, sourceEvidence, specification,
    Specification.conjoin, Specification.pullback, declarationSpecification, declarationRequirement_mem]

/-- An empty interpretation cannot qualify, regardless of its separately
supplied operations or already qualified source syntax. -/
theorem empty_interpretation_excluded
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} assembly C targets)
    (context : C.Ctx)
    (empty : data.interpretation = SharedJudgmentInterpretation.emptyRaw assembly C context) :
    ¬ (specification contract required).Satisfies data := by
  intro qualified
  have total := ((satisfies_iff contract required data).mp qualified).2.1 .admittedTotal
  change SharedJudgmentInterpretation.AdmittedTotal data.interpretation at total
  rw [empty] at total
  exact SharedJudgmentInterpretation.empty_raw_not_admitted_total context total

/-- A nonempty annotation-sensitive relation is also excluded. Its fixed-
annotation conversion law alone does not interpret the native conversion rule. -/
theorem annotation_sensitive_interpretation_excluded
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (data : Data.{u, v, w, w', uIndex, uArtifact, uEvidence} common C targets)
    (context : C.Ctx) (type : C.Ty context) (value : C.Tm context type)
    (agrees : data.interpretation = SharedJudgmentInterpretation.annotationSensitiveRaw context type value)
    (wire : NativeWireData.Wire) :
    ¬ (specification contract required).Satisfies data := by
  intro qualified
  have transport := ((satisfies_iff contract required data).mp qualified).2.1 .annotation
  change SharedJudgmentInterpretation.AnnotationTransport data.interpretation at transport
  rw [agrees] at transport
  exact SharedJudgmentInterpretation.annotation_sensitive_not_transport context type value wire transport

#print axioms satisfies_iff
#print axioms qualified_conversion_rule
#print axioms qualified_accepted_type_has_code
#print axioms qualified_required_head
#print axioms required_entry_missing_excluded
#print axioms source_evidence_retains_semantic_obligations
#print axioms source_evidence_retains_declaration_obligations
#print axioms empty_interpretation_excluded
#print axioms annotation_sensitive_interpretation_excluded

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentSemanticRequirements
