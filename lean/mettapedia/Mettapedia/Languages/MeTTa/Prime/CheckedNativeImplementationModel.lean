import Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
import Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
import Mettapedia.Languages.MeTTa.PureKernel.Universe.MILCheckedNativePresentation

/-!
# Checked native programs as abstract Prime implementation models

The generic inference checker, a calculus-specific native realization, and the
abstract Prime execution contract were previously connected pairwise.  This
module closes the remaining generic triangle.

An ingress state contains an externally authored raw proof together with an
exact-erasing checked derivation.  Its native state is the retained graph of
semantic evidence and calculus-specific artifact.  Revision-indexed execution
maps the already-checked state directly to that graph; checking is not an
argument of active execution.  Exact codecs retain the complete ingress for
fallback and the complete graph for receipts.

The construction is deliberately discrete at this boundary: it models one
checked construction event, not the subsequent operational behavior of the
native artifact.  That behavior composes through the existing abstract model.
An artifact-only receipt is proved insufficient whenever native projection is
non-faithful.
-/

namespace Mettapedia.Languages.MeTTa.Prime.CheckedNativeImplementationModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

universe uGoal uEvidence uArtifact

/-! ## Exact checked ingress -/

/-- One raw proof at one named goal together with the exact-erasing checked
program established at the external boundary. -/
structure CheckedIngress
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal) (raw : RawProof) where
  program : waist.CheckedRawProgram goal raw

/-- Runtime states retain both the authored raw proof and its checked ingress.
Two different raw proof trees therefore remain different states even if their
native artifact projection later collides. -/
abbrev CheckedState
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal) : Type _ :=
  Sigma fun raw => CheckedIngress waist goal raw

namespace CheckedState

variable {presentation : ValidatedPresentation}
variable {waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation}
variable {goal : waist.Goal}

/-- The exact raw proof retained for fallback and audit. -/
def raw (state : CheckedState waist goal) : RawProof := state.1

/-- The checked program whose erasure is the retained raw proof. -/
def checked (state : CheckedState waist goal) : waist.CheckedProgram goal :=
  state.2.program.toChecked

/-- Independent semantic evidence interpreted from the checked tree. -/
def evidence (state : CheckedState waist goal) :
    waist.Meaning (waist.surface goal) :=
  state.checked.evidence

/-- Proof-retaining native realization of the checked program. -/
def realized (state : CheckedState waist goal) : waist.native.Graph goal :=
  state.checked.realized

/-- The hot artifact projection, available without discarding `realized`. -/
def artifact (state : CheckedState waist goal) : waist.native.Artifact goal :=
  state.realized.artifact

@[simp] theorem checked_erase (state : CheckedState waist goal) :
    state.checked.checked.erase = state.raw :=
  state.2.program.toChecked_erase

@[simp] theorem realized_evidence (state : CheckedState waist goal) :
    state.realized.evidence = state.evidence :=
  rfl

end CheckedState

/-- Universe-raised checked state used beside an arbitrary evidence/artifact
graph in one indexed operational object. -/
abbrev CheckedRuntimeState
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal) : Type (max uEvidence uArtifact) :=
  ULift.{max uEvidence uArtifact} (CheckedState waist goal)

namespace CheckedRuntimeState

variable {presentation : ValidatedPresentation}
variable {waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation}
variable {goal : waist.Goal}

def raw (state : CheckedRuntimeState waist goal) : RawProof := state.down.raw

def checked (state : CheckedRuntimeState waist goal) : waist.CheckedProgram goal :=
  state.down.checked

def evidence (state : CheckedRuntimeState waist goal) :
    waist.Meaning (waist.surface goal) :=
  state.down.evidence

def realized (state : CheckedRuntimeState waist goal) :
    waist.native.Graph goal :=
  state.down.realized

def artifact (state : CheckedRuntimeState waist goal) :
    waist.native.Artifact goal :=
  state.realized.artifact

@[simp] theorem checked_erase (state : CheckedRuntimeState waist goal) :
    state.checked.checked.erase = state.raw :=
  state.down.checked_erase

@[simp] theorem realized_evidence (state : CheckedRuntimeState waist goal) :
    state.realized.evidence = state.evidence :=
  rfl

end CheckedRuntimeState

/-! ## The construction event as an indexed execution -/

/-- A proof-relevant discrete execution family.  It records the construction
occurrence without pretending that ingress itself performs the artifact's
later operational reductions. -/
inductive DiscreteExecution (State : Type u) : State → State → Type u where
  | refl (state : State) : DiscreteExecution State state state

/-- Checked ingress as an indexed semantic object.  `accepts` is an independent
semantic predicate on retained evidence; it is not regenerated by NIK. -/
def sourceOperational
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop) :
    IndexedOperationalObject.{max uEvidence uArtifact} where
  State := CheckedRuntimeState waist goal
  Execution := DiscreteExecution (CheckedRuntimeState waist goal)
  Meaning := fun state => accepts state.evidence

/-- The retained native graph is the target state.  Meaning is evaluated on
the very same semantic evidence, not reconstructed from the artifact. -/
def targetOperational
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop) :
    IndexedOperationalObject.{max uEvidence uArtifact} where
  State := waist.native.Graph goal
  Execution := DiscreteExecution (waist.native.Graph goal)
  Meaning := fun point => accepts point.evidence

/-- The declared observation is the native artifact, while the operational
state and receipt continue to retain its semantic-evidence fibre. -/
def sourceObserved
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop) :
    IndexedObservedOperationalObject.{max uEvidence uArtifact, uArtifact}
      (waist.native.Artifact goal) where
  operational := sourceOperational waist goal accepts
  observe := fun {first _last} _execution => some first.artifact

/-- Native graph observation projects the same artifact as checked ingress. -/
def targetObserved
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop) :
    IndexedObservedOperationalObject.{max uEvidence uArtifact, uArtifact}
      (waist.native.Artifact goal) where
  operational := targetOperational waist goal accepts
  observe := fun {first _last} _execution => some first.artifact

/-- Checked-to-native construction is an observation-preserving indexed cell.
Its state map is exactly the retained graph embedding. -/
def observedRefinement
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop) :
    IndexedObservedRefinement
      (sourceObserved waist goal accepts)
      (targetObserved waist goal accepts) where
  refinement :=
    { mapState := CheckedRuntimeState.realized
      mapExecution := by
        intro first last execution
        cases execution
        exact DiscreteExecution.refl _
      preservesMeaning := by
        intro state meaningful
        exact meaningful }
  commutes := by
    intro first last execution
    cases execution
    rfl

/-! ## Exact codecs and revision-indexed implementation -/

/-- A checked ingress state is an exact representation of its discrete source
trace.  In particular, fallback retains the authored raw tree and derivation. -/
def sourceTraceCodec
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop) :
    ExactCodec (ExecutionTrace (sourceObserved waist goal accepts).operational) where
  Representation := CheckedRuntimeState waist goal
  encode := fun trace => trace.1
  decode := fun state => ⟨state, state, DiscreteExecution.refl state⟩
  decode_encode := by
    rintro ⟨first, last, execution⟩
    cases execution
    rfl

/-- The retained evidence/artifact graph is an exact runtime receipt. -/
def targetTraceCodec
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop) :
    ExactCodec (ExecutionTrace (targetObserved waist goal accepts).operational) where
  Representation := waist.native.Graph goal
  encode := fun trace => trace.1
  decode := fun point => ⟨point, point, DiscreteExecution.refl point⟩
  decode_encode := by
    rintro ⟨first, last, execution⟩
    cases execution
    rfl

/-- Every checked-native waist induces an abstract Prime implementation model
at every selected dependency revision. -/
def model
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    AdmittedExecutionModel dependencies revision
      (sourceObserved waist goal accepts)
      (targetObserved waist goal accepts) where
  admission :=
    { refinement := observedRefinement waist goal accepts }
  rawCodec := sourceTraceCodec waist goal accepts
  receiptCodec := targetTraceCodec waist goal accepts

/-- Activation at the admitted revision retains no checker argument. -/
def active
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    (model waist goal accepts dependencies revision).admission.Active revision :=
  (model waist goal accepts dependencies revision).admission.activate
    (dependencies.sameDependencies_refl revision)

/-- Current execution constructs the retained native graph directly from an
already checked state. -/
@[simp] theorem compile_state
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (state : CheckedRuntimeState waist goal) :
    (model waist goal accepts dependencies revision).compileTrace
        (active waist goal accepts dependencies revision)
        ⟨state, state, DiscreteExecution.refl state⟩ =
      ⟨state.realized, state.realized,
        DiscreteExecution.refl state.realized⟩ :=
  rfl

/-- Decoding fallback recovers the complete checked ingress, including its raw
proof and exact erasure witness. -/
theorem fallback_state
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (state : CheckedRuntimeState waist goal) :
    let prepared := (model waist goal accepts dependencies revision).prepare
      ⟨state, state, DiscreteExecution.refl state⟩
    (model waist goal accepts dependencies revision).rawCodec.decode
        prepared.fallback = prepared.sourceTrace := by
  exact (model waist goal accepts dependencies revision).prepare
    ⟨state, state, DiscreteExecution.refl state⟩ |>.fallback_adequate

/-- Emitted receipts decode to the full evidence/artifact graph occurrence. -/
theorem receipt_state
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (state : CheckedRuntimeState waist goal) :
    let implementation := model waist goal accepts dependencies revision
    let current := active waist goal accepts dependencies revision
    let prepared := implementation.prepare
      ⟨state, state, DiscreteExecution.refl state⟩
    implementation.receiptCodec.decode
        (implementation.emitReceipt current prepared) =
      ⟨state.realized, state.realized,
        DiscreteExecution.refl state.realized⟩ := by
  dsimp only
  rw [(model waist goal accepts dependencies revision).emitReceipt_adequate]
  rfl

/-- Artifact observation commutes exactly across checked construction. -/
theorem compile_state_observationAgreement
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal)
    (accepts : waist.Meaning (waist.surface goal) → Prop)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (state : CheckedRuntimeState waist goal) :
    (targetObserved waist goal accepts).observe
        ((model waist goal accepts dependencies revision).compileTrace
          (active waist goal accepts dependencies revision)
          ⟨state, state, DiscreteExecution.refl state⟩).2.2 =
      some state.artifact :=
  rfl

/-- Generic raw checking is exactly the existence of an ingress state at the
same raw proof, not merely existence of some proof with the same endpoint. -/
theorem checkRaw_iff_nonempty_ingress
    {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist.{uGoal, uEvidence, uArtifact} presentation)
    (goal : waist.Goal) (raw : RawProof) :
    checkRaw presentation (waist.surface goal) raw = true ↔
      Nonempty (CheckedIngress waist goal raw) := by
  constructor
  · intro accepted
    rcases (waist.checkRaw_iff_nonempty goal raw).mp accepted with ⟨program⟩
    exact ⟨⟨program⟩⟩
  · rintro ⟨⟨program⟩⟩
    exact (waist.checkRaw_iff_nonempty goal raw).mpr ⟨program⟩

/-! ## Artifact-only receipts are conditional, not a default -/

/-- If two retained graph points share an artifact, no decoder from artifacts
alone can be exact on both. -/
theorem no_artifactOnlyReceipt_of_collision
    {Goal : Type uGoal} {Evidence : Goal → Type uEvidence}
    (realization : NativeRealization.{uGoal, uEvidence, uArtifact} Goal Evidence)
    {goal : Goal} {first second : realization.Graph goal}
    (different : first ≠ second)
    (collision : first.artifact = second.artifact) :
    ¬ ∃ decode : realization.Artifact goal → realization.Graph goal,
        ∀ point, decode point.artifact = point := by
  rintro ⟨decode, recovers⟩
  apply different
  calc
    first = decode first.artifact := (recovers first).symm
    _ = decode second.artifact := congrArg decode collision
    _ = second := recovers second

namespace ProjectionCanary

open NativeRealization.ProjectionCanary

/-- The existing collapsing native projection cannot serve as an exact
receipt representation.  The retained graph is semantically necessary. -/
theorem collapsing_artifact_cannot_be_exact_receipt :
    ¬ ∃ decode : collapsing.Artifact () → collapsing.Graph (),
        ∀ point, decode point.artifact = point :=
  no_artifactOnlyReceipt_of_collision collapsing retained_points_distinct
    projected_artifacts_equal

end ProjectionCanary

/-! ## Prime MIL instance: checked chain to intrinsic native term -/

namespace MILCanary

open Mettapedia.Languages.MeTTa.PureKernel.Universe
open Mettapedia.Languages.MeTTa.PureKernel.Universe.MILLearnedProofRelevantAdmission
open Mettapedia.Languages.MeTTa.PureKernel.Universe.MILCheckedNativePresentation

noncomputable section

/-- The concrete formed Prime vocabulary and its generic checked-native waist. -/
def waist := checkedNativeWaist FormedQuotationCanary.quotation

def grandparentGoal : waist.Goal := (MILCheckedChain.alice, MILCheckedChain.carol)

/-- The semantic fibre used by the canary retains the exact learned
grandparent evidence, rather than endpoint reachability alone. -/
def acceptsGrandparent
    (evidence : Reach MILCheckedChain.alice MILCheckedChain.carol) : Prop :=
  evidence = grandparentEvidence

/-- The accepted authored proof with its exact raw tree. -/
def grandparentIngress :
    CheckedIngress waist grandparentGoal MILCheckedChain.grandparentProof where
  program := (grandparent FormedQuotationCanary.quotation).toWaist

def grandparentState : CheckedRuntimeState waist grandparentGoal :=
  ULift.up ⟨MILCheckedChain.grandparentProof, grandparentIngress⟩

@[simp] theorem grandparentState_raw :
    grandparentState.raw = MILCheckedChain.grandparentProof :=
  rfl

theorem grandparentState_meaningful :
    acceptsGrandparent grandparentState.evidence :=
  rfl

def grandparentModel :=
  model waist grandparentGoal acceptsGrandparent dependencies false

def grandparentActive : grandparentModel.admission.Active false :=
  active waist grandparentGoal acceptsGrandparent dependencies false

/-- One current activation maps the exact checked proof directly to its
intrinsic typed native graph, retaining the raw proof for fallback. -/
theorem grandparent_checked_ingress_runs_directly :
    grandparentModel.compileTrace grandparentActive
        ⟨grandparentState, grandparentState,
          DiscreteExecution.refl grandparentState⟩ =
      ⟨grandparentState.realized, grandparentState.realized,
        DiscreteExecution.refl grandparentState.realized⟩ ∧
      grandparentState.checked.checked.erase = MILCheckedChain.grandparentProof :=
  ⟨rfl, grandparentState.checked_erase⟩

def grandparentPrepared := grandparentModel.prepare
  ⟨grandparentState, grandparentState,
    DiscreteExecution.refl grandparentState⟩

/-- A relevant revision change disables activation while leaving the complete
checked ingress available for exact fallback. -/
theorem changed_revision_prevents_activation_and_preserves_checked_fallback :
    (¬ grandparentModel.admission.Active true) ∧
      grandparentModel.rawCodec.decode grandparentPrepared.fallback =
        grandparentPrepared.sourceTrace := by
  have stale : grandparentModel.StaleAt true := by
    intro same
    have contradiction := same ()
    simp [dependencies] at contradiction
  exact ⟨grandparentModel.stale_prevents_activation stale,
    grandparentModel.stale_preserves_fallback stale grandparentPrepared⟩

/-- The ill-shared-middle proof cannot become an ingress state and therefore
cannot enter any native implementation model derived from this waist. -/
theorem wrong_middle_has_no_checked_ingress :
    ¬ Nonempty
      (CheckedIngress waist (MILCheckedChain.alice, MILCheckedChain.bob)
        MILCheckedChain.wrongMiddleProof) := by
  rintro ⟨⟨program⟩⟩
  exact concrete_wrong_middle_has_no_common_waist_program ⟨program⟩

end

end MILCanary

#print axioms CheckedState.checked_erase
#print axioms CheckedRuntimeState.checked_erase
#print axioms observedRefinement
#print axioms compile_state
#print axioms fallback_state
#print axioms receipt_state
#print axioms compile_state_observationAgreement
#print axioms checkRaw_iff_nonempty_ingress
#print axioms no_artifactOnlyReceipt_of_collision
#print axioms ProjectionCanary.collapsing_artifact_cannot_be_exact_receipt
#print axioms MILCanary.grandparent_checked_ingress_runs_directly
#print axioms MILCanary.changed_revision_prevents_activation_and_preserves_checked_fallback
#print axioms MILCanary.wrong_middle_has_no_checked_ingress

end Mettapedia.Languages.MeTTa.Prime.CheckedNativeImplementationModel
