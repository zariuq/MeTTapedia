import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
import Mettapedia.GSLT.LanguageDef.NIKCompositionCapabilitySelection
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionTransport
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptGeneratorSubstitutionAction
import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionFunctoriality

/-!
# NIK selection of strict dependent-receipt substitution

The maximal-native boundary for substitution is capability-indexed.

* Exact raw retention is always a legitimate fallback face.
* A target-side native cell is available only when the hosted generator
  family supplies substitution naturality.
* Composition of several such transports is a still stronger capability:
  the proof-relevant root action must satisfy identity and composition laws.

The concrete family below compares fallback with one genuinely strict Prime
transport under a common semantic contract.  NIK selects the target-cell face
for the exact request, activates the retained operation only at a current
revision, and retains the original cell independently for stale fallback.
An empty target-generator fibre supplies the refusing control.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeDependentReceiptSubstitutionNIKSelection

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKCompositionCapabilitySelection
open Mettapedia.TypeTheory.FreeWhiskeredCell
open Mettapedia.TypeTheory.FreeWhiskeredCell.CoherenceObservation
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptComputad
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceCandidates.Canaries
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionTransport
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionTransport.Canaries
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptGeneratorSubstitutionAction
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionFunctoriality
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.ProofRelevantStructuralComputation

/-! ## The exact capability supplied by a hosted generator family -/

/-- Evidence that this exact Prime generator family admits strict transport
for the concrete nonidentity substitution. -/
structure StrictGeneratorCapability
    (TargetGenerator : {left right : Tower.Tm 0} →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right →
      StructuralConversionReceipt retainedTower.computation
        Tower.rules.headEq left right → Type) where
  naturality : ReceiptGeneratorNaturality closeVariable
    (TaggedGenerator 1) TargetGenerator

def taggedStrictCapability : StrictGeneratorCapability (TaggedGenerator 0) :=
  ⟨taggedNaturality⟩

/-- A target with no generator cannot advertise the strict native face. -/
theorem emptyTarget_has_no_strictCapability :
    IsEmpty (StrictGeneratorCapability (EmptyGenerator 0)) :=
  ⟨fun capability =>
    no_empty_generator_naturality.false capability.naturality⟩

/-! ## One common semantic contract for fallback and strict transport -/

abbrev OpenWhiskeredCell :=
  Cell (receiptBase retainedTower.computation Tower.rules.headEq 1)
    (TaggedGenerator 1)
    (.trans variableOneReflexivity variableDoubledReflexivity)
    (.trans variableOneReflexivity variableOneReflexivity)

abbrev ClosedWhiskeredCell :=
  Cell (receiptBase retainedTower.computation Tower.rules.headEq 0)
    (TaggedGenerator 0)
    (.trans oneReflexivity doubledReflexivity)
    (.trans oneReflexivity oneReflexivity)

/-- Preparation never discards the source cell.  A successful native face
additionally carries the target-side cell. -/
structure TransportResult where
  source : OpenWhiskeredCell
  target : Option ClosedWhiskeredCell

/-- The common target invariant distinguishes an honest retained fallback
from a transported result whose full construction shape agrees with source. -/
def TransportResult.Valid (result : TransportResult) : Prop :=
  result.target = none ∨
    ∃ target, result.target = some target ∧
      rawShape target = rawShape result.source

@[reducible] def sourceObject : AdmissionObject where
  Carrier := OpenWhiskeredCell
  Meaning := fun cell => generatorCount cell = 1

@[reducible] def targetObject : AdmissionObject where
  Carrier := TransportResult
  Meaning := TransportResult.Valid

/-- The always-available face retains the exact source for ordinary
execution or a later higher comparison. -/
def fallbackOperation : AdmissionHom sourceObject targetObject where
  run := fun cell => ⟨cell, none⟩
  preserves := by
    intro cell meaningful
    exact Or.inl rfl

/-- Generator naturality upgrades the same request to a direct target-side
native cell while preserving the entire free-cell shape. -/
def strictOperation
    (capability : StrictGeneratorCapability (TaggedGenerator 0)) :
    AdmissionHom sourceObject targetObject where
  run := fun cell =>
    ⟨cell, some (substituteCell closeVariable capability.naturality cell)⟩
  preserves := by
    intro cell meaningful
    exact Or.inr ⟨_, rfl,
      rawShape_substituteCell closeVariable capability.naturality cell⟩

/-! ## Request-local maximal-native selection -/

/-- Rank zero is exact fallback retention; rank one additionally constructs
the target native cell. -/
def transportFamily
    (capability : StrictGeneratorCapability (TaggedGenerator 0)) :
    RecognizedFamily (Fin 2) sourceObject targetObject where
  package
    | ⟨0, _⟩ => fallbackOperation
    | ⟨1, _⟩ => strictOperation capability
  Capability := Fin 2
  supports := fun realization requested => requested ≤ realization
  supports_mono := by
    intro weaker stronger related requested supported
    exact supported.trans related
  strict_support_gain := by
    intro weaker stronger strict
    exact ⟨stronger, le_rfl, not_le_of_gt strict⟩
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := Finset.univ_nonempty

def targetCellCapability
    (capability : StrictGeneratorCapability (TaggedGenerator 0)) :
    (transportFamily capability).Capability :=
  (1 : Fin 2)

def targetCellRequest
    (capability : StrictGeneratorCapability (TaggedGenerator 0)) :
    (transportFamily capability).CapabilityRequest where
  required := fun requested => requested = targetCellCapability capability
  candidates := {(1 : Fin 2)}
  candidates_exact := by
    intro candidate
    constructor
    · intro member
      have equal : candidate = (1 : Fin 2) := by simpa using member
      subst candidate
      constructor
      · simp [transportFamily]
      · intro requested required
        rcases required with rfl
        exact le_rfl
    · rintro ⟨licensed, supportsRequired⟩
      have supportsTarget := supportsRequired
        (targetCellCapability capability) rfl
      change (1 : Fin 2) ≤ candidate at supportsTarget
      fin_cases candidate
      · simp at supportsTarget
      · simp
  candidates_nonempty := by simp

def targetCellSelection
    (capability : StrictGeneratorCapability (TaggedGenerator 0)) :
    (targetCellRequest capability).StrongestNativeCalculusPrinciple where
  val := (1 : Fin 2)
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        targetCellRequest]
    · intro candidate candidateMember
      have equal : candidate = (1 : Fin 2) := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          targetCellRequest] using candidateMember
      subst candidate
      exact le_rfl

theorem targetCellRequest_uniqueStrongest
    (capability : StrictGeneratorCapability (TaggedGenerator 0)) :
    ∃! chosen,
      (targetCellRequest capability).restrictedFamily.IsGreatestLicensed
        chosen := by
  refine ⟨(1 : Fin 2), (targetCellSelection capability).2, ?_⟩
  intro candidate candidateGreatest
  exact RecognizedFamily.greatestLicensed_unique
    (targetCellRequest capability).restrictedFamily
    candidateGreatest (targetCellSelection capability).2

/-! ## Revision-current execution and retained stale fallback -/

def dependencies : DependencySystem where
  Revision := Nat
  Dependency := Unit
  Value := Nat
  read := fun revision _ => revision

def initialRevision : dependencies.Revision := by
  change Nat
  exact 0

def changedRevision : dependencies.Revision := by
  change Nat
  exact 1

def strictAdmission :=
  admitStrongestAt (transportFamily taggedStrictCapability)
    (targetCellRequest taggedStrictCapability)
    (targetCellSelection taggedStrictCapability)
    dependencies initialRevision

def currentStrict : strictAdmission.Active initialRevision :=
  strictAdmission.activate
    (dependencies.sameDependencies_refl initialRevision)

/-- The current hot route is exactly the constructional substitution
operation selected above; it produces the closed cell, not a replay token. -/
theorem currentStrict_constructs_target :
    (currentStrict.run whiskeredTaggedCell).target =
      some substitutedWhiskeredTaggedCell :=
  rfl

/-- A relevant revision change prevents activation of the retained native
operation. -/
theorem changedRevision_has_no_active_strict :
    ¬ Nonempty (strictAdmission.Active changedRevision) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies, initialRevision, changedRevision] at changed

/-- Staleness does not consume or reinterpret the original receipt cell. -/
theorem changedRevision_preserves_exact_fallback :
    (¬ Nonempty (strictAdmission.Active changedRevision)) ∧
      (fallbackOperation.run whiskeredTaggedCell).source =
        whiskeredTaggedCell ∧
      (fallbackOperation.run whiskeredTaggedCell).target = none :=
  ⟨changedRevision_has_no_active_strict, rfl, rfl⟩

/-! ## Composition is a stronger, separately licensed capability -/

/-- The root computation must discharge this interface before NIK may claim
that successive strict transports compose as one strict native action.  The
mere existence of each individual substitution map is insufficient. -/
abbrev ComposableRootSubstitutionCapability : Prop :=
  retainedTower.computation.SubstitutionCoherent

/-- The canonical retained Prime tower supplies the stronger composition
capability.  This is derived from the authored rule presentation: it is not
inferred from the mere existence of a substitution operation. -/
def retainedTowerComposableRootSubstitution :
    ComposableRootSubstitutionCapability := by
  change
    (SyntacticJudgmentalPi.RetainedRoot.ofRules Tower.rules).computation
      |>.SubstitutionCoherent
  exact
    SyntacticJudgmentalPi.RetainedRoot.ofRulesSubstitutionCoherent Tower.rules

/-- The tagged comparison-generator family also supplies the independent
identity and composition laws needed above the retained root. -/
abbrev ComposableGeneratorSubstitutionCapability : Prop :=
  (Tagged.action (computation := retainedTower.computation)
    (headEq := Tower.rules.headEq)).Functorial

def taggedComposableGeneratorSubstitution :
    ComposableGeneratorSubstitutionCapability :=
  Tagged.actionFunctorial

/-- The generic root interface really admits non-compositional models, so the
composable capability cannot be inferred by a dispatcher. -/
theorem rootSubstitution_does_not_entail_composableCapability :
    ¬ (SubstitutionCoherenceCanary.arityChangingStampComputation
      |>.SubstitutionCoherent) :=
  SubstitutionCoherenceCanary.arityChangingStamp_not_substitutionCoherent

/-! ## A request-local fused composite face -/

/-- A closed dependent cell packaged with all of its indices and retained
receipts.  Packaging changes no evidence; it only gives the three native
faces below one common result carrier. -/
structure PackedTaggedCell (n : Nat) where
  left : Tower.Tm n
  right : Tower.Tm n
  first : StructuralConversionReceipt retainedTower.computation
    Tower.rules.headEq left right
  second : StructuralConversionReceipt retainedTower.computation
    Tower.rules.headEq left right
  cell : Cell (receiptBase retainedTower.computation Tower.rules.headEq n)
    (TaggedGenerator n) first second

def PackedTaggedCell.ofCell {n : Nat} {left right : Tower.Tm n}
    {first second : StructuralConversionReceipt retainedTower.computation
      Tower.rules.headEq left right}
    (cell : Cell
      (receiptBase retainedTower.computation Tower.rules.headEq n)
      (TaggedGenerator n) first second) : PackedTaggedCell n where
  left := left
  right := right
  first := first
  second := second
  cell := cell

/-- Equality of packaged dependent cells is heterogeneous equality of their
complete cell trees.  Every endpoint and receipt occurs in the type of
`cell`, so this relation forgets only the transports needed to compare those
indices; it does not quotient the constructor history. -/
def PackedTaggedCell.heterogeneousSetoid (n : Nat) :
    Setoid (PackedTaggedCell n) where
  r := fun first second => HEq first.cell second.cell
  iseqv := ⟨
    fun _ => HEq.rfl,
    fun related => HEq.symm related,
    fun first second => HEq.trans first second⟩

/-- The transport-insensitive class of a complete dependent cell. -/
abbrev PackedTaggedCell.HeterogeneousClass (n : Nat) :=
  Quotient (PackedTaggedCell.heterogeneousSetoid n)

def PackedTaggedCell.toHeterogeneousClass {n : Nat}
    (cell : PackedTaggedCell n) : PackedTaggedCell.HeterogeneousClass n :=
  Quotient.mk _ cell

/-- The quotient identifies exactly heterogeneous equality, so it does not
silently collapse distinct proof trees of the same indexed type. -/
theorem PackedTaggedCell.toHeterogeneousClass_eq_iff {n : Nat}
    (first second : PackedTaggedCell n) :
    first.toHeterogeneousClass = second.toHeterogeneousClass ↔
      HEq first.cell second.cell :=
  by
    constructor
    · exact Quotient.exact
    · intro related
      exact Quotient.sound related

/-- On every fixed dependent fibre, the quotient embedding is injective.
Consequently different receipt-cell programs of the same indexed type remain
different observations. -/
theorem PackedTaggedCell.toHeterogeneousClass_ofCell_injective
    {n : Nat} {left right : Tower.Tm n}
    {first second : StructuralConversionReceipt retainedTower.computation
      Tower.rules.headEq left right} :
    Function.Injective (fun cell :
      Cell (receiptBase retainedTower.computation Tower.rules.headEq n)
        (TaggedGenerator n) first second =>
      (PackedTaggedCell.ofCell cell).toHeterogeneousClass) := by
  intro earlier later classesEqual
  have related :=
    (PackedTaggedCell.toHeterogeneousClass_eq_iff
      (PackedTaggedCell.ofCell earlier)
      (PackedTaggedCell.ofCell later)).mp classesEqual
  exact eq_of_heq related

/-- A one-node identity cell and a two-node vertical identity cell inhabit the
same dependent fibre but have different construction histories. -/
def oneNodeIdentityCell :
    Cell (receiptBase retainedTower.computation Tower.rules.headEq 0)
      (TaggedGenerator 0) oneReflexivity oneReflexivity :=
  Cell.refl
    (base := receiptBase retainedTower.computation Tower.rules.headEq 0)
    (Generator := TaggedGenerator 0) oneReflexivity

def twoNodeIdentityCell :
    Cell (receiptBase retainedTower.computation Tower.rules.headEq 0)
      (TaggedGenerator 0) oneReflexivity oneReflexivity :=
  Cell.vertical
    (Cell.refl
      (base := receiptBase retainedTower.computation Tower.rules.headEq 0)
      (Generator := TaggedGenerator 0) oneReflexivity)
    (Cell.refl
      (base := receiptBase retainedTower.computation Tower.rules.headEq 0)
      (Generator := TaggedGenerator 0) oneReflexivity)

theorem heterogeneousClass_retains_constructor_history :
    PackedTaggedCell.toHeterogeneousClass
        (PackedTaggedCell.ofCell oneNodeIdentityCell) ≠
      PackedTaggedCell.toHeterogeneousClass
        (PackedTaggedCell.ofCell twoNodeIdentityCell) := by
  intro classesEqual
  have cellsEqual :=
    PackedTaggedCell.toHeterogeneousClass_ofCell_injective classesEqual
  simp [oneNodeIdentityCell, twoNodeIdentityCell] at cellsEqual

structure CompositeTransportResult where
  source : OpenWhiskeredCell
  target : Option (PackedTaggedCell 1)

def CompositeTransportResult.Valid
    (result : CompositeTransportResult) : Prop :=
  result.target = none ∨
    ∃ target, result.target = some target ∧
      rawShape target.cell = rawShape result.source

/-- The complete observable result of dependent transport.  The source is
retained literally.  The target retains the entire proof-relevant cell modulo
only the heterogeneous index transports characterized above. -/
structure CompositeTransportObservation where
  source : OpenWhiskeredCell
  target : Option (PackedTaggedCell.HeterogeneousClass 1)

def observeCompositeTransport
    (result : CompositeTransportResult) : CompositeTransportObservation where
  source := result.source
  target := result.target.map PackedTaggedCell.toHeterogeneousClass

@[reducible] def compositeSourceObject : AdmissionObject where
  Carrier := OpenWhiskeredCell
  Meaning := fun cell => generatorCount cell = 1

@[reducible] def compositeTargetObject : AdmissionObject where
  Carrier := CompositeTransportResult
  Meaning := CompositeTransportResult.Valid

def sequentialRoundTrip (cell : OpenWhiskeredCell) :=
  substituteCell reopenEmpty (primeTaggedAction.map reopenEmpty)
    (substituteCell closeVariable
      (primeTaggedAction.map closeVariable) cell)

def directRoundTrip (cell : OpenWhiskeredCell) :=
  substituteCell (fun index => subst reopenEmpty (closeVariable index))
    (primeTaggedAction.map
      (fun index => subst reopenEmpty (closeVariable index))) cell

/-- The actual intermediate object of the two-stage construction.  It retains
the source cell alongside the closed cell so the second stage neither
reconstructs nor forgets provenance. -/
structure ClosedTransportStage where
  source : OpenWhiskeredCell
  closed : PackedTaggedCell 0

def ClosedTransportStage.Valid (stage : ClosedTransportStage) : Prop :=
  rawShape stage.closed.cell = rawShape stage.source

@[reducible] def compositeMiddleObject : AdmissionObject where
  Carrier := ClosedTransportStage
  Meaning := ClosedTransportStage.Valid

/-- The first admitted stage closes the dependent receipt cell while retaining
its exact source. -/
def closeStageOperation :
    AdmissionHom compositeSourceObject compositeMiddleObject where
  run := fun cell =>
    ⟨cell, PackedTaggedCell.ofCell
      (substituteCell closeVariable
        (primeTaggedAction.map closeVariable) cell)⟩
  preserves := by
    intro cell meaningful
    exact rawShape_substituteCell closeVariable
      (primeTaggedAction.map closeVariable) cell

/-- The second admitted stage reopens the retained closed cell and returns a
complete target result with the original source still attached. -/
def reopenStageOperation :
    AdmissionHom compositeMiddleObject compositeTargetObject where
  run := fun stage =>
    ⟨stage.source, some (PackedTaggedCell.ofCell
      (substituteCell reopenEmpty
        (primeTaggedAction.map reopenEmpty) stage.closed.cell))⟩
  preserves := by
    intro stage valid
    refine Or.inr ⟨_, rfl, ?_⟩
    exact
      (rawShape_substituteCell reopenEmpty
        (primeTaggedAction.map reopenEmpty) stage.closed.cell).trans valid

/-- The always-available face preserves the exact source independently of
whether direct composite construction is licensed. -/
def compositeFallbackOperation :
    AdmissionHom compositeSourceObject compositeTargetObject where
  run := fun cell => ⟨cell, none⟩
  preserves := by
    intro cell meaningful
    exact Or.inl rfl

/-- The ordinary strict face performs the two already-licensed substitutions
successively and retains the resulting complete cell. -/
def sequentialRoundTripOperation :
    AdmissionHom compositeSourceObject compositeTargetObject :=
  AdmissionHom.comp closeStageOperation reopenStageOperation

/-- The stronger face performs one direct composite substitution.  Its
admission requires the functorial generator law even though the raw function
can be written without that proof. -/
def directRoundTripOperation
    (_capability : primeTaggedAction.Functorial) :
    AdmissionHom compositeSourceObject compositeTargetObject where
  run := fun cell =>
    ⟨cell, some (PackedTaggedCell.ofCell (directRoundTrip cell))⟩
  preserves := by
    intro cell meaningful
    refine Or.inr ⟨_, rfl, ?_⟩
    exact rawShape_substituteCell
      (fun index => subst reopenEmpty (closeVariable index))
      (primeTaggedAction.map
        (fun index => subst reopenEmpty (closeVariable index))) cell

/-- The semantic reason the direct face is a realization of the sequential
one: agreement holds for every source cell, including all dependent receipt
and generator data. -/
theorem sequentialRoundTrip_heq_direct (cell : OpenWhiskeredCell) :
    HEq (sequentialRoundTrip cell) (directRoundTrip cell) :=
  substituteCell_ofRules_comp_heq Tower.rules primeTaggedAction
    Tagged.actionFunctorial reopenEmpty closeVariable cell

/-- Direct and sequential transport have the same complete dependent
observation.  This is stronger than raw-shape agreement: quotient exactness
recovers heterogeneous equality of the entire retained cell. -/
theorem directRoundTripObservation_eq_sequentialStages
    (capability : primeTaggedAction.Functorial)
    (cell : OpenWhiskeredCell) :
    observeCompositeTransport
        ((directRoundTripOperation capability).run cell) =
      observeCompositeTransport
        ((AdmissionHom.comp closeStageOperation reopenStageOperation).run
          cell) := by
  change
    CompositeTransportObservation.mk cell
        (some (PackedTaggedCell.toHeterogeneousClass
          (PackedTaggedCell.ofCell (directRoundTrip cell)))) =
      CompositeTransportObservation.mk cell
        (some (PackedTaggedCell.toHeterogeneousClass
          (PackedTaggedCell.ofCell (sequentialRoundTrip cell))))
  apply congrArg (fun target =>
    CompositeTransportObservation.mk cell (some target))
  apply Quotient.sound
  exact HEq.symm (sequentialRoundTrip_heq_direct cell)

/-- The Prime substitution instance of request-local native composition.
Root coherence and generator functoriality are capabilities required to form
the specification; its comparison is the complete dependent observation
above, not a raw-shape or endpoint-only projection. -/
def compositeCompositionSpec
    (_rootCapability : ComposableRootSubstitutionCapability)
    (capability : primeTaggedAction.Functorial) :
    CompositionSpec compositeSourceObject compositeMiddleObject
      compositeTargetObject where
  Observation := CompositeTransportObservation
  observe := observeCompositeTransport
  fallback := compositeFallbackOperation
  earlier := closeStageOperation
  later := reopenStageOperation
  direct := directRoundTripOperation capability
  direct_agrees := directRoundTripObservation_eq_sequentialStages capability

/-- The generic composition family supplies the three genuine constructional
faces: exact source retention, successive strict transport, and direct
composite transport. -/
def compositeFamily
    (rootCapability : ComposableRootSubstitutionCapability)
    (capability : primeTaggedAction.Functorial) :
    RecognizedFamily (Fin 3) compositeSourceObject compositeTargetObject :=
  (compositeCompositionSpec rootCapability capability).family

def directCompositeRequest
    (rootCapability : ComposableRootSubstitutionCapability)
    (capability : primeTaggedAction.Functorial) :
    (compositeFamily rootCapability capability).CapabilityRequest :=
  (compositeCompositionSpec rootCapability capability).directRequest

def directCompositeSelection
    (rootCapability : ComposableRootSubstitutionCapability)
    (capability : primeTaggedAction.Functorial) :
    (directCompositeRequest rootCapability capability)
      |>.StrongestNativeCalculusPrinciple :=
  (compositeCompositionSpec rootCapability capability).directSelection

theorem directCompositeRequest_uniqueStrongest
    (rootCapability : ComposableRootSubstitutionCapability)
    (capability : primeTaggedAction.Functorial) :
    ∃! chosen,
      (directCompositeRequest rootCapability capability).restrictedFamily
        |>.IsGreatestLicensed chosen := by
  exact
    (compositeCompositionSpec rootCapability capability)
      |>.directRequest_uniqueStrongest

def directCompositeAdmission :=
  (compositeCompositionSpec retainedTowerComposableRootSubstitution
      taggedComposableGeneratorSubstitution).admitDirectAt
    dependencies initialRevision

def currentDirectComposite :
    directCompositeAdmission.Active initialRevision :=
  (compositeCompositionSpec retainedTowerComposableRootSubstitution
      taggedComposableGeneratorSubstitution).activateDirectAt
    dependencies initialRevision initialRevision
    (dependencies.sameDependencies_refl initialRevision)

/-- The current selected operation is the direct constructional action, not
a checker replay or a certificate token. -/
theorem currentDirectComposite_constructs_direct :
    (currentDirectComposite.run whiskeredTaggedCell).target =
      some (PackedTaggedCell.ofCell
        (directRoundTrip whiskeredTaggedCell)) :=
  rfl

/-- The generic NIK composition theorem applies to the concrete current Prime
operation: hot direct construction and the two-stage construction agree under
the complete heterogeneous-cell observation. -/
theorem currentDirectComposite_observation_agrees
    (cell : OpenWhiskeredCell) :
    observeCompositeTransport (currentDirectComposite.run cell) =
      observeCompositeTransport (sequentialRoundTripOperation.run cell) := by
  exact
    (compositeCompositionSpec retainedTowerComposableRootSubstitution
      taggedComposableGeneratorSubstitution)
      |>.activateDirectAt_observation_agrees dependencies initialRevision
        initialRevision (dependencies.sameDependencies_refl initialRevision)
        cell

/-- The same dependency currentness law governs the fused face: a relevant
revision change makes the retained operation unavailable without destroying
the source cell needed by a weaker route. -/
theorem changedRevision_has_no_active_directComposite :
    ¬ Nonempty (directCompositeAdmission.Active changedRevision) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies, initialRevision, changedRevision] at changed

/-- The refusing generator model supplies every local map but cannot even
construct the capability required to form the direct request family. -/
theorem stampingMaps_have_no_directCompositeCapability :
    ¬ Nonempty StampCanary.action.Functorial := by
  rintro ⟨capability⟩
  exact StampCanary.action_not_functorial capability

/-- The complete request-local handoff to NIK.  The direct face is uniquely
strongest only after both root and generator composition laws are supplied;
its result agrees with sequential transport on every complete dependent
cell, is usable only at the admitting revision, and is refused by the
nonfunctorial generator model. -/
theorem nikDirectCompositeSubstitutionBoundary :
    (∃! chosen,
      (directCompositeRequest retainedTowerComposableRootSubstitution
        taggedComposableGeneratorSubstitution).restrictedFamily
        |>.IsGreatestLicensed chosen) ∧
      (∀ cell : OpenWhiskeredCell,
        HEq (sequentialRoundTrip cell) (directRoundTrip cell)) ∧
      (∀ cell : OpenWhiskeredCell,
        observeCompositeTransport (currentDirectComposite.run cell) =
          observeCompositeTransport
            (sequentialRoundTripOperation.run cell)) ∧
      (currentDirectComposite.run whiskeredTaggedCell).target =
        some (PackedTaggedCell.ofCell
          (directRoundTrip whiskeredTaggedCell)) ∧
      ¬ Nonempty (directCompositeAdmission.Active changedRevision) ∧
      ComposableRootSubstitutionCapability ∧
      ComposableGeneratorSubstitutionCapability ∧
      ¬ Nonempty StampCanary.action.Functorial :=
  ⟨directCompositeRequest_uniqueStrongest
      retainedTowerComposableRootSubstitution
      taggedComposableGeneratorSubstitution,
    sequentialRoundTrip_heq_direct,
    currentDirectComposite_observation_agrees,
    currentDirectComposite_constructs_direct,
    changedRevision_has_no_active_directComposite,
    retainedTowerComposableRootSubstitution,
    taggedComposableGeneratorSubstitution,
    stampingMaps_have_no_directCompositeCapability⟩

/-- One theorem-sized handoff for native selection: the exact strict face is
uniquely strongest for its request and runs while current; missing generator
naturality or missing substitution coherence remains an explicit refusal. -/
theorem nikStrictSubstitutionBoundary :
    (∃! chosen,
      (targetCellRequest taggedStrictCapability).restrictedFamily
        |>.IsGreatestLicensed chosen) ∧
      (currentStrict.run whiskeredTaggedCell).target =
        some substitutedWhiskeredTaggedCell ∧
      IsEmpty (StrictGeneratorCapability (EmptyGenerator 0)) ∧
      ¬ Nonempty (strictAdmission.Active changedRevision) ∧
      ComposableRootSubstitutionCapability ∧
      ComposableGeneratorSubstitutionCapability ∧
      ¬ StampCanary.action.Functorial ∧
      ¬ (SubstitutionCoherenceCanary.arityChangingStampComputation
        |>.SubstitutionCoherent) :=
  ⟨targetCellRequest_uniqueStrongest taggedStrictCapability,
    currentStrict_constructs_target,
    emptyTarget_has_no_strictCapability,
    changedRevision_has_no_active_strict,
    retainedTowerComposableRootSubstitution,
    taggedComposableGeneratorSubstitution,
    StampCanary.action_not_functorial,
    rootSubstitution_does_not_entail_composableCapability⟩

/-! ## Axiom audit -/

#print axioms emptyTarget_has_no_strictCapability
#print axioms fallbackOperation
#print axioms strictOperation
#print axioms targetCellRequest_uniqueStrongest
#print axioms currentStrict_constructs_target
#print axioms changedRevision_has_no_active_strict
#print axioms retainedTowerComposableRootSubstitution
#print axioms taggedComposableGeneratorSubstitution
#print axioms nikStrictSubstitutionBoundary
#print axioms sequentialRoundTrip_heq_direct
#print axioms PackedTaggedCell.toHeterogeneousClass_eq_iff
#print axioms PackedTaggedCell.toHeterogeneousClass_ofCell_injective
#print axioms heterogeneousClass_retains_constructor_history
#print axioms directRoundTripObservation_eq_sequentialStages
#print axioms directCompositeRequest_uniqueStrongest
#print axioms currentDirectComposite_constructs_direct
#print axioms currentDirectComposite_observation_agrees
#print axioms changedRevision_has_no_active_directComposite
#print axioms stampingMaps_have_no_directCompositeCapability
#print axioms nikDirectCompositeSubstitutionBoundary

end NativeDependentReceiptSubstitutionNIKSelection
end Mettapedia.Languages.MeTTa.Prime
