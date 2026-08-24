import Mettapedia.Languages.MeTTa.PureKernel.Universe.LegacyTowerConservativity
import Mettapedia.Languages.MeTTa.PureKernel.Universe.BoundaryJudgments
import Mettapedia.TypeTheory.Authority

/-!
# Evidence-bearing authority outcomes

An authority returns one of four semantic outcomes.  The sum representation
makes contradictory status/coverage pairs unrepresentable.  Positive and
negative decisions carry their distinct evidence; fragment abstention and
resource incompleteness carry the information needed to refine them.

Operational failure is not a semantic outcome.  It lives in `RunResult` and
therefore cannot be confused with either refutation or abstention.  A compact
status is only a display quotient.  The raw two-tag native vocabulary is kept
at the edge as a transitional wire encoding with a checked decoder.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation

namespace OutcomeContract

universe u v w x y z b

open Mettapedia.TypeTheory.AuthorityTheory

/-! ## Authority and fragment scopes -/

inductive Profile where
  | sealedLegacy
  | monomorphicRegular
  | towerRussell
  | generatedTarski
  | gradualAnalysis
deriving DecidableEq, Repr

inductive JudgmentClass where
  | sealedLegacy
  | monomorphicRegular
  | rawLegacySyntax
  | towerGenerated
  | towerPolymorphicSchema
  | towerTypeLevelEquality
  | towerLargeFormation
  | towerUpperSort
  | tarskiGenerated
  | tarskiNeutralSchema
  | gradualOnly
  | unknownMeaningful
  | malformedArtifact
deriving DecidableEq, Repr

inductive BoundaryReason where
  | rawLegacyNeedsSeal
  | requiresUniverseTower
  | neutralCodesUnavailable
  | differentProfile
  | unknownMeaningful
deriving DecidableEq, Repr

inductive FaultReason where
  | malformedArtifact
  | brokenInvariant
  | engineUnavailable
deriving DecidableEq, Repr

inductive Scope where
  | inClass
  | outOfClass (reason : BoundaryReason)
  | fault (reason : FaultReason)
deriving DecidableEq, Repr

def classify : Profile → JudgmentClass → Scope
  | _, .malformedArtifact => .fault .malformedArtifact
  | _, .unknownMeaningful => .outOfClass .unknownMeaningful
  | _, .rawLegacySyntax => .outOfClass .rawLegacyNeedsSeal
  | .sealedLegacy, .sealedLegacy => .inClass
  | .monomorphicRegular, .monomorphicRegular => .inClass
  | .towerRussell, .sealedLegacy => .inClass
  | .towerRussell, .monomorphicRegular => .inClass
  | .towerRussell, .towerGenerated => .inClass
  | .towerRussell, .towerPolymorphicSchema => .inClass
  | .towerRussell, .towerTypeLevelEquality => .inClass
  | .towerRussell, .towerLargeFormation => .inClass
  | .towerRussell, .towerUpperSort => .inClass
  | .generatedTarski, .tarskiGenerated => .inClass
  | .generatedTarski, .tarskiNeutralSchema =>
      .outOfClass .neutralCodesUnavailable
  | .gradualAnalysis, .gradualOnly => .inClass
  | .monomorphicRegular, .towerPolymorphicSchema =>
      .outOfClass .requiresUniverseTower
  | .monomorphicRegular, .towerTypeLevelEquality =>
      .outOfClass .requiresUniverseTower
  | .monomorphicRegular, .towerLargeFormation =>
      .outOfClass .requiresUniverseTower
  | .monomorphicRegular, .towerUpperSort =>
      .outOfClass .requiresUniverseTower
  | _, _ => .outOfClass .differentProfile

structure AuthorityKey where
  root : Nat
  profile : Profile
  revision : Nat
deriving DecidableEq, Repr

/-- A restartable resource boundary records both the requested bound and the
remaining frontier. -/
structure ResourceReceipt where
  requested : Nat
  spent : Nat
  frontier : Nat
deriving DecidableEq, Repr

/-! Prime specializes generic receipts with natural-number work and its
revisioned authority key. -/
abbrev Receipt {Judgment : Type u} (authority : Authority Judgment)
    (Boundary : Type x) (Incomplete : Type y) (Failure : Type z)
    (Budget : Type b) (Provenance : Type w) (key : AuthorityKey)
    (requested : Budget) (judgment : Judgment) :=
  Mettapedia.TypeTheory.AuthorityTheory.Receipt authority Boundary Incomplete
    Failure Budget Nat Provenance AuthorityKey key requested judgment

abbrev CachedReceipt {Judgment : Type u} (authority : Authority Judgment)
    (Boundary : Type x) (Incomplete : Type y) (Failure : Type z)
    (Budget : Type b) (Provenance : Type w) (judgment : Judgment) :=
  Mettapedia.TypeTheory.AuthorityTheory.CachedReceipt authority Boundary
    Incomplete Failure Budget Nat Provenance AuthorityKey judgment

/-! ## Transitional native wire encoding -/

inductive NativeDecisionTag where
  | open
  | established
  | refuted
deriving DecidableEq, Repr

inductive NativeCoverageTag where
  | decided
  | outsideFragment
  | resourceIncomplete
  | engineUnavailable
deriving DecidableEq, Repr

/-- Raw wire data.  This is not the semantic carrier because it admits
illegal combinations. -/
structure NativePair where
  decision : NativeDecisionTag
  coverage : NativeCoverageTag
deriving DecidableEq, Repr

inductive NativeOutcomeTag where
  | established
  | refuted
  | outsideFragment
  | incomplete
deriving DecidableEq, Repr

inductive NativeRunTag where
  | ok (outcome : NativeOutcomeTag)
  | fault
deriving DecidableEq, Repr

namespace NativeRunTag

def encode : NativeRunTag → NativePair
  | .ok .established => ⟨.established, .decided⟩
  | .ok .refuted => ⟨.refuted, .decided⟩
  | .ok .outsideFragment => ⟨.open, .outsideFragment⟩
  | .ok .incomplete => ⟨.open, .resourceIncomplete⟩
  | .fault => ⟨.open, .engineUnavailable⟩

def asBool : NativeRunTag → Option Bool
  | .ok .established => some true
  | .ok .refuted => some false
  | _ => none

def publicObservation : NativeRunTag → PublicObservation Unit
  | .ok .established => .status .established
  | .ok .refuted => .status .refuted
  | .ok .outsideFragment => .status .undetermined
  | .ok .incomplete => .status .incomplete
  | .fault => .operationalFault ()

end NativeRunTag

namespace NativePair

def decode : NativePair → Option NativeRunTag
  | ⟨.established, .decided⟩ => some (.ok .established)
  | ⟨.refuted, .decided⟩ => some (.ok .refuted)
  | ⟨.open, .outsideFragment⟩ => some (.ok .outsideFragment)
  | ⟨.open, .resourceIncomplete⟩ => some (.ok .incomplete)
  | ⟨.open, .engineUnavailable⟩ => some .fault
  | _ => none

def publicObservation (pair : NativePair) : PublicObservation Unit :=
  match pair.decode with
  | some tag => tag.publicObservation
  | none => .invalidProtocol

inductive Valid : NativePair → Prop where
  | established : Valid ⟨.established, .decided⟩
  | refuted : Valid ⟨.refuted, .decided⟩
  | outsideFragment : Valid ⟨.open, .outsideFragment⟩
  | incomplete : Valid ⟨.open, .resourceIncomplete⟩
  | fault : Valid ⟨.open, .engineUnavailable⟩

@[simp] theorem decode_encode (tag : NativeRunTag) :
    decode tag.encode = some tag := by
  cases tag with
  | ok outcome => cases outcome <;> rfl
  | fault => rfl

theorem encode_injective : Function.Injective NativeRunTag.encode := by
  intro left right equality
  have decoded := congrArg decode equality
  simpa using decoded

theorem encode_valid (tag : NativeRunTag) : tag.encode.Valid := by
  cases tag with
  | ok outcome => cases outcome <;> constructor
  | fault => constructor

theorem valid_has_unique_decoding {pair : NativePair} (valid : pair.Valid) :
    ∃! tag, pair.decode = some tag := by
  cases valid
  · refine ⟨.ok .established, rfl, ?_⟩
    intro tag equality
    have tagEquality : some (.ok .established) = some tag := equality
    exact (Option.some.inj tagEquality).symm
  · refine ⟨.ok .refuted, rfl, ?_⟩
    intro tag equality
    have tagEquality : some (.ok .refuted) = some tag := equality
    exact (Option.some.inj tagEquality).symm
  · refine ⟨.ok .outsideFragment, rfl, ?_⟩
    intro tag equality
    have tagEquality : some (.ok .outsideFragment) = some tag := equality
    exact (Option.some.inj tagEquality).symm
  · refine ⟨.ok .incomplete, rfl, ?_⟩
    intro tag equality
    have tagEquality : some (.ok .incomplete) = some tag := equality
    exact (Option.some.inj tagEquality).symm
  · refine ⟨.fault, rfl, ?_⟩
    intro tag equality
    have tagEquality : some .fault = some tag := equality
    exact (Option.some.inj tagEquality).symm

/-- A representative illegal raw pair is rejected at the wire boundary. -/
theorem illegal_established_outside_rejected :
    decode ⟨.established, .outsideFragment⟩ = none :=
  rfl

end NativePair

/-- Erase the evidence-bearing semantic outcome at the native wire edge. -/
def eraseOutcome :
    Outcome Established Refuted Boundary Incomplete → NativeOutcomeTag
  | .established _ => .established
  | .refuted _ => .refuted
  | .outsideFragment _ => .outsideFragment
  | .incomplete _ => .incomplete

/-- Erase a complete semantic-or-operational result at the native wire edge. -/
def eraseRun {Failure : Type u} {Established : Sort v} {Refuted : Sort w}
    {Boundary : Type x} {Incomplete : Type y} :
    RunResult Failure (Outcome Established Refuted Boundary Incomplete) →
      NativeRunTag
  | .ok outcome => .ok (eraseOutcome outcome)
  | .fault _ => .fault

@[simp] theorem publicObservation_erase
    {Failure : Type u} {Established : Sort v} {Refuted : Sort w}
    {Boundary : Type x} {Incomplete : Type y}
    (result : RunResult Failure
      (Outcome Established Refuted Boundary Incomplete)) :
    (eraseRun result).publicObservation =
      result.publicObservation.eraseFailure := by
  cases result with
  | ok outcome =>
      cases outcome <;>
        simp [eraseRun, eraseOutcome, NativeRunTag.publicObservation,
          RunResult.publicObservation, Outcome.publicStatus,
          PublicObservation.eraseFailure]
  | fault failure =>
      simp [eraseRun, NativeRunTag.publicObservation,
        RunResult.publicObservation, PublicObservation.eraseFailure]

/-! ## Exact Prime authority and the eight judgment packages -/

abbrev BoundaryRow := BoundaryJudgments.BoundaryRow
abbrev ExactJudgment := BoundaryJudgments.ExactJudgment
abbrev ExactEvidence (judgment : ExactJudgment) := judgment.Meaning

def exactAuthority : Authority ExactJudgment where
  Holds := ExactEvidence
  Evidence := ExactEvidence
  Obstruction := fun judgment => ¬ ExactEvidence judgment
  evidenceSound := fun _ evidence => evidence
  obstructionSound := fun _ obstruction => obstruction

abbrev ExactOutcome (judgment : ExactJudgment) :=
  AuthorizedOutcome exactAuthority BoundaryReason ResourceReceipt judgment

abbrev ExactRun (judgment : ExactJudgment) :=
  RunResult FaultReason (ExactOutcome judgment)

def BoundaryRow.judgmentClass : BoundaryRow → JudgmentClass
  | .positiveInhabitant => .monomorphicRegular
  | .selfApplication => .monomorphicRegular
  | .lambdaAtNonFunction => .monomorphicRegular
  | .distinctIdentityEndpoints => .monomorphicRegular
  | .polymorphicModusPonens => .towerPolymorphicSchema
  | .typeLevelEquality => .towerTypeLevelEquality
  | .largeSigma => .towerLargeFormation
  | .upperSortSynthesis => .towerUpperSort

def resolutionToOutcome {judgment : ExactJudgment} :
    BoundaryJudgments.Resolution judgment → ExactOutcome judgment
  | .established evidence => .established evidence
  | .refuted obstruction => .refuted obstruction

/-- Every row is decided by its actual tower derivation or obstruction. -/
def BoundaryRow.towerOutcome (row : BoundaryRow) : ExactOutcome row.judgment :=
  resolutionToOutcome row.towerResolution

/-- The regular authority uses the same proved row objects and abstains only
on the four tower judgments. -/
def BoundaryRow.monomorphicOutcome (row : BoundaryRow) :
    ExactOutcome row.judgment :=
  match row with
  | .positiveInhabitant =>
      .established BoundaryJudgments.RegularRows.positive_evidence
  | .selfApplication =>
      .refuted BoundaryJudgments.RegularRows.selfApplication_obstruction
  | .lambdaAtNonFunction =>
      .refuted BoundaryJudgments.RegularRows.lambdaAtNonFunction_obstruction
  | .distinctIdentityEndpoints =>
      .refuted BoundaryJudgments.RegularRows.distinctIdentity_obstruction
  | .polymorphicModusPonens => .outsideFragment .requiresUniverseTower
  | .typeLevelEquality => .outsideFragment .requiresUniverseTower
  | .largeSigma => .outsideFragment .requiresUniverseTower
  | .upperSortSynthesis => .outsideFragment .requiresUniverseTower

def BoundaryRow.towerRunTag (row : BoundaryRow) : NativeRunTag :=
  eraseRun (RunResult.ok row.towerOutcome : ExactRun row.judgment)

def BoundaryRow.monomorphicRunTag (row : BoundaryRow) : NativeRunTag :=
  eraseRun (RunResult.ok row.monomorphicOutcome : ExactRun row.judgment)

theorem boundaryRow_tower_decided (row : BoundaryRow) :
    row.towerOutcome.isDecided = true := by
  cases row <;>
    rfl

theorem boundaryRow_scope_agrees (row : BoundaryRow) :
    classify .monomorphicRegular row.judgmentClass =
      if row.monomorphicOutcome.isDecided then .inClass
      else .outOfClass .requiresUniverseTower := by
  cases row <;> rfl

theorem towerOnlyRow_abstains
    (row : BoundaryRow)
    (towerOnly : row = .polymorphicModusPonens ∨ row = .typeLevelEquality ∨
      row = .largeSigma ∨ row = .upperSortSynthesis) :
    ∃ reason, row.monomorphicOutcome = .outsideFragment reason := by
  rcases towerOnly with rfl | rfl | rfl | rfl
  all_goals exact ⟨.requiresUniverseTower, rfl⟩

theorem towerOnlyRow_not_refuted
    (row : BoundaryRow)
    (towerOnly : row = .polymorphicModusPonens ∨ row = .typeLevelEquality ∨
      row = .largeSigma ∨ row = .upperSortSynthesis) :
    row.monomorphicOutcome.asBool ≠ some false := by
  rcases towerOnly with rfl | rfl | rfl | rfl
  all_goals intro equality
  all_goals cases equality

open SchemaElaboration

def composeJudgment : ExactJudgment :=
  .tower .check BoundaryJudgments.emptyTowerContext
    composeSchemaTerm composeSchemaType

def composeEvidence : ExactEvidence composeJudgment :=
  ⟨composeSchemaTerm_hasType,
    ⟨composeSchemaLevel, composeSchemaType_hasType⟩⟩

def composeOutcome : ExactOutcome composeJudgment :=
  .established composeEvidence

@[simp] theorem composeOutcome_public :
    composeOutcome.publicStatus = .established :=
  rfl

def churchMapJudgment : ExactJudgment :=
  .tower .check BoundaryJudgments.emptyTowerContext
    churchMapSchemaTerm churchMapSchemaType

def churchMapEvidence : ExactEvidence churchMapJudgment :=
  ⟨churchMapSchemaTerm_hasType,
    ⟨churchMapSchemaLevel, churchMapSchemaType_hasType⟩⟩

def churchMapOutcome : ExactOutcome churchMapJudgment :=
  .established churchMapEvidence

@[simp] theorem churchMapOutcome_public :
    churchMapOutcome.publicStatus = .established :=
  rfl

theorem churchMapSchema_outside_generated_code_image :
    RussellTarski.reify churchMapSchemaType = none := by
  decide

theorem compose_tower_authorized :
    classify .towerRussell .towerPolymorphicSchema = .inClass ∧
      ExactEvidence composeJudgment :=
  ⟨rfl, composeEvidence⟩

theorem compose_generatedTarski_abstains :
    classify .generatedTarski .tarskiNeutralSchema =
        .outOfClass .neutralCodesUnavailable ∧
      RussellTarski.reify composeSchemaType = none :=
  ⟨rfl, composeSchema_outside_generated_code_image⟩

theorem churchMap_generatedTarski_abstains :
    classify .generatedTarski .tarskiNeutralSchema =
        .outOfClass .neutralCodesUnavailable ∧
      RussellTarski.reify churchMapSchemaType = none :=
  ⟨rfl, churchMapSchema_outside_generated_code_image⟩

def legacyLeakJudgment : ExactJudgment :=
  .sealedCheck .nil Legacy.legacyUniverseLeak (.head .marker)

theorem legacyLeakObstruction :
    exactAuthority.Obstruction legacyLeakJudgment :=
  Legacy.legacyUniverseLeak_not_hasType

def legacyLeakOutcome : ExactOutcome legacyLeakJudgment :=
  .refuted legacyLeakObstruction

@[simp] theorem legacyLeakOutcome_public :
    legacyLeakOutcome.publicStatus = .refuted :=
  rfl

theorem rawLegacy_requires_seal :
    classify .towerRussell .rawLegacySyntax =
        .outOfClass .rawLegacyNeedsSeal ∧
      ¬ (∀ (context : Legacy.Ctx 0) (term type : Legacy.Tm 0),
        Tower.HasType (Legacy.embedCtx context) (Legacy.embed term)
            (Legacy.embed type) →
          Legacy.HasType context term type) :=
  ⟨rfl, Legacy.unrestricted_raw_reflection_is_false⟩

/-! ## Checked casts and proposal separation -/

structure CheckedCastReceipt (judgment : ExactJudgment) where
  evidence : exactAuthority.Evidence judgment

def CheckedCastReceipt.outcome {judgment : ExactJudgment}
    (receipt : CheckedCastReceipt judgment) : ExactOutcome judgment :=
  .established receipt.evidence

def composeCheckedCastReceipt : CheckedCastReceipt composeJudgment :=
  ⟨composeEvidence⟩

@[simp] theorem checkedCast_asBool_true
    {judgment : ExactJudgment} (receipt : CheckedCastReceipt judgment) :
    receipt.outcome.asBool = some true :=
  rfl

def GradualObservation (_ : ExactJudgment) := Unit

theorem gradualObservation_inhabited (judgment : ExactJudgment) :
    Nonempty (GradualObservation judgment) :=
  ⟨()⟩

theorem no_total_gradual_laundering :
    ¬ (∀ judgment, GradualObservation judgment →
      exactAuthority.Evidence judgment) := by
  intro laundering
  exact Legacy.legacyUniverseLeak_not_hasType
    (laundering legacyLeakJudgment ())

def ForeignProposal (_ : ExactJudgment) := Unit

theorem no_total_foreign_authority_laundering :
    ¬ (∀ judgment, ForeignProposal judgment →
      exactAuthority.Evidence judgment) := by
  intro laundering
  exact Legacy.legacyUniverseLeak_not_hasType
    (laundering legacyLeakJudgment ())

/-! ## Axiom audit -/

#print axioms boundaryRow_tower_decided
#print axioms compose_tower_authorized
#print axioms towerOnlyRow_not_refuted
#print axioms no_total_gradual_laundering

end OutcomeContract

end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
