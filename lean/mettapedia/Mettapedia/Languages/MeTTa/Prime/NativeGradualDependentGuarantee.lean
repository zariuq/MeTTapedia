import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentNaturality
import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentInteraction
import Mettapedia.Languages.MeTTa.Prime.NativeProgramGradualGuarantee
import Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee

/-!
# The lazy gradual-dependent guarantee for Prime

Prime graduality is displayed over unchanged raw semantics.  Precision fills
an exact-evidence fibre or records local blame; it does not add an unknown term
to kernel conversion.  This file closes the generic laws needed to use that
design compositionally:

* every state refines suspension while exact evidence and current blame remain
  rigid;
* constructional maps preserve precision and compose on safely transported
  states;
* safe transport invalidates blame, whereas an explicit reflection capability
  transports it functorially;
* revision activation commutes with construction, dependent construction, and
  evidence transport;
* proof-relevant naturality squares commute on every safely transported state;
* an undemanded checked plan runs by raw erasure, first demand evaluates once,
  and revision staleness returns only the optional capability to suspension.

The domain instances are the existing cumulative Pi/Sigma/identity
constructors, proof-relevant interaction paths, source-preserving program
islands, and certified parallel rho worlds.  Dependent second-Sigma beta keeps
its two conversion receipts and therefore remains at its explicit higher-cell
boundary; this guarantee does not identify proof trees by proof irrelevance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee

open CategoryTheory
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State

universe uRaw uExact uRaw' uExact' uRaw'' uExact'' uRevision uKey uCell
  uRetry uTy uOutput

/-! ## The unchanged-raw precision core -/

/-- Every live capability state is a precision refinement of suspension.
This is the static gradual direction: adding exact evidence or local blame
adds information without changing the raw index. -/
theorem refines_suspended {fibre : Fibre.{uRaw, uExact}}
    {raw : fibre.Raw} (state : State fibre raw) :
    Refines state (.suspended : State fibre raw) := by
  cases state with
  | suspended => exact .refl _
  | exact evidence => exact .exact_suspended evidence
  | refuted blame => exact .refuted_suspended blame

/-- Forgetting a cached capability is exactly loss of precision, never a
change to the raw value. -/
theorem invalidate_is_coarser {fibre : Fibre.{uRaw, uExact}}
    {raw : fibre.Raw} (state : State fibre raw) :
    Refines state state.invalidate :=
  refines_invalidate state

/-! ## Compositional safe and reflecting transport -/

/-- Safe transport is compositional.  In the negative case both sides forget
the unsupported blame at the first forward-only boundary. -/
@[simp] theorem mapSafe_comp
    {first : Fibre.{uRaw, uExact}}
    {second : Fibre.{uRaw', uExact'}}
    {third : Fibre.{uRaw'', uExact''}}
    (later : ExactMap second third) (earlier : ExactMap first second)
    {raw : first.Raw} (state : State first raw) :
    mapSafe later (mapSafe earlier state) =
      mapSafe (later.comp earlier) state := by
  cases state <;> rfl

/-- The safe identity map is identity on suspension and exact evidence.  On
blame it performs the deliberate forward-only invalidation. -/
theorem mapSafe_id_refines
    {fibre : Fibre.{uRaw, uExact}} {raw : fibre.Raw}
    (state : State fibre raw) :
    Refines state (mapSafe (ExactMap.id fibre) state) := by
  cases state with
  | suspended => exact .refl _
  | exact evidence => exact .refl _
  | refuted blame => exact .refuted_suspended blame

/-- Once exact reflection is supplied, identity transport preserves every
state, including its local blame path. -/
@[simp] theorem mapFull_id
    {fibre : Fibre.{uRaw, uExact}} {raw : fibre.Raw}
    (state : State fibre raw) :
    mapFull (ExactMap.id fibre) (ExactMap.reflects_id fibre) state = state := by
  cases state <;> rfl

/-- Reflecting transport is fully functorial, including proof-relevant blame.
The reflection proof is the extra capability that makes the negative case
sound. -/
@[simp] theorem mapFull_comp
    {first : Fibre.{uRaw, uExact}}
    {second : Fibre.{uRaw', uExact'}}
    {third : Fibre.{uRaw'', uExact''}}
    (later : ExactMap second third) (earlier : ExactMap first second)
    (laterReflects : later.ReflectsExact)
    (earlierReflects : earlier.ReflectsExact)
    {raw : first.Raw} (state : State first raw) :
    mapFull later laterReflects (mapFull earlier earlierReflects state) =
      mapFull (later.comp earlier)
        (ExactMap.reflects_comp laterReflects earlierReflects) state := by
  cases state <;> rfl

/-! ## Revision coherence -/

/-- Revision activation commutes with every safe constructional map. -/
theorem mapSafe_activateAt
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target)
    {raw : source.Raw} {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) (state : State source raw) :
    mapSafe map (state.activateAt cached current) =
      (mapSafe map state).activateAt cached current := by
  by_cases same : cached = current
  · subst current
    simp
  · simp [activateAt, same, invalidate]
    rfl

/-- Revision activation also commutes with reflecting transport, so stable
blame is retained exactly while current and forgotten exactly when stale. -/
theorem mapFull_activateAt
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (reflects : map.ReflectsExact)
    {raw : source.Raw} {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) (state : State source raw) :
    mapFull map reflects (state.activateAt cached current) =
      (mapFull map reflects state).activateAt cached current := by
  by_cases same : cached = current
  · subst current
    simp
  · simp [activateAt, same, invalidate]
    rfl

/-- Independent native premises can be revision-activated before or after
their constructional product is formed. -/
theorem combine_activateAt
    {left : Fibre.{uRaw, uExact}}
    {right : Fibre.{uRaw', uExact'}}
    {leftRaw : left.Raw} {rightRaw : right.Raw}
    {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision)
    (leftState : State left leftRaw) (rightState : State right rightRaw) :
    (State.combine leftState rightState).activateAt cached current =
      State.combine (leftState.activateAt cached current)
        (rightState.activateAt cached current) := by
  by_cases same : cached = current
  · subst current
    simp
  · simp [activateAt, same, invalidate, State.combine]

/-- The same revision law holds for genuinely dependent Sigma premises; the
second fibre remains indexed by the unchanged first raw value. -/
theorem combineDependent_activateAt
    {base : Fibre.{uRaw, uExact}}
    {next : base.Raw -> Fibre.{uRaw', uExact'}}
    {baseRaw : base.Raw} {nextRaw : (next baseRaw).Raw}
    {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision)
    (baseState : State base baseRaw)
    (nextState : State (next baseRaw) nextRaw) :
    (State.combineDependent baseState nextState).activateAt cached current =
      State.combineDependent (baseState.activateAt cached current)
        (nextState.activateAt cached current) := by
  by_cases same : cached = current
  · subst current
    simp
  · simp [activateAt, same, invalidate, State.combineDependent]

/-! ## Reusable earned-capability records -/

/-- Laws earned by every forward constructional map.  This is the exact
capability NIK may request from a native realization without assuming
reflection of negative evidence. -/
structure SafeTransportLaws
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target) : Prop where
  exact_preserved : forall {raw : source.Raw} (evidence : source.Exact raw),
    mapSafe map (.exact evidence) = .exact (map.mapExact evidence)
  blame_invalidated : forall {raw : source.Raw}
    (blame : Refutation source raw),
    mapSafe map (.refuted blame) = .suspended
  precision_monotone : forall {raw : source.Raw}
    {refined coarse : State source raw}, Refines refined coarse ->
      Refines (mapSafe map refined) (mapSafe map coarse)

/-- Every constructional map earns the safe laws without replaying a checker
or manufacturing a negative judgment. -/
def safeTransportLaws
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target) :
    SafeTransportLaws map where
  exact_preserved := mapSafe_exact map
  blame_invalidated := mapSafe_refuted map
  precision_monotone := fun precision => precision.mapSafe

/-- Strong transport laws are earned only by an exact-reflecting map. -/
structure ReflectingTransportLaws
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target)
    (reflects : map.ReflectsExact) : Prop where
  exact_preserved : forall {raw : source.Raw} (evidence : source.Exact raw),
    mapFull map reflects (.exact evidence) = .exact (map.mapExact evidence)
  blame_preserved : forall {raw : source.Raw}
    (blame : Refutation source raw),
    mapFull map reflects (.refuted blame) =
      .refuted (mapRefutation map reflects blame)
  precision_monotone : forall {raw : source.Raw}
    {refined coarse : State source raw}, Refines refined coarse ->
      Refines (mapFull map reflects refined) (mapFull map reflects coarse)

def reflectingTransportLaws
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target)
    (reflects : map.ReflectsExact) : ReflectingTransportLaws map reflects where
  exact_preserved := fun _ => rfl
  blame_preserved := fun _ => rfl
  precision_monotone := fun precision => precision.mapFull reflects

/-- Reflection is a genuine additional capability: identity earns it. -/
def identityReflectingTransportLaws
    (fibre : Fibre.{uRaw, uExact}) :
    ReflectingTransportLaws (ExactMap.id fibre)
      (ExactMap.reflects_id fibre) :=
  reflectingTransportLaws _ _

/-- Every proof-relevant construction square earns state-level naturality for
suspension, exact evidence, and safely invalidated blame. -/
structure SafeSquareLaws
    {northWest : Fibre.{uRaw, uExact}}
    {northEast : Fibre.{uRaw', uExact'}}
    {southWest : Fibre.{uRaw'', uExact''}}
    {southEast : Fibre.{uKey, uRetry}}
    {north : ExactMap northWest northEast}
    {west : ExactMap northWest southWest}
    {east : ExactMap northEast southEast}
    {south : ExactMap southWest southEast}
    (square : ExactMap.Square north west east south) : Prop where
  gradual_commutes : forall {raw : northWest.Raw}
    (state : State northWest raw),
    HEq (mapSafe east (mapSafe north state))
      (mapSafe south (mapSafe west state))

def safeSquareLaws
    {northWest : Fibre.{uRaw, uExact}}
    {northEast : Fibre.{uRaw', uExact'}}
    {southWest : Fibre.{uRaw'', uExact''}}
    {southEast : Fibre.{uKey, uRetry}}
    {north : ExactMap northWest northEast}
    {west : ExactMap northWest southWest}
    {east : ExactMap northEast southEast}
    {south : ExactMap southWest southEast}
    (square : ExactMap.Square north west east south) : SafeSquareLaws square :=
  ⟨square.mapSafe_commutes⟩

/-! ## Lazy demand and raw execution -/

/-- A checked capability executes by raw erasure with no checker parameter in
the runner.  The typing relation is arbitrary because the checked branch does
not inspect it. -/
theorem checked_run_is_raw
    {fibre : Fibre.{uRaw, uExact}}
    {Key : Type uKey} {Ty : Type uTy}
    {HasType : fibre.Raw -> Ty -> Prop}
    {Output : Type uOutput}
    (key : Key) (raw : fibre.Raw) (runRaw : fibre.Raw -> Output) :
    (Plan.checked (Ty := Ty) (HasType := HasType)
      (Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.checkedPlan
        (fibre := fibre) key raw)).run
        runRaw = runRaw raw :=
  rfl

/-- Current demand information may be used, while the identical cached state
at a stale revision becomes suspension.  In both cases the raw index is the
same by construction. -/
theorem demand_revision_dichotomy
    {fibre : Fibre.{uRaw, uExact}} {Retry : Type uRetry}
    (checker :
      Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Checker
        fibre Retry)
    (raw : fibre.Raw) {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) :
    (cached = current ->
      (checker.demandState raw).activateAt cached current =
        checker.demandState raw) /\
    (cached ≠ current ->
      (checker.demandState raw).activateAt cached current =
        (State.suspended : State fibre raw)) := by
  constructor
  · intro same
    subst current
    simp
  · intro stale
    exact activateAt_stale stale _

/-- The full generic lazy guarantee at one boundary: demand can only refine
suspension, and its first evaluation count is exactly one. -/
theorem demand_refines_once
    {fibre : Fibre.{uRaw, uExact}} {Retry : Type uRetry}
    (checker :
      Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Checker
        fibre Retry)
    {Key : Type uKey} {Cell : Type uCell}
    (key : Key) (raw : fibre.Raw) (cell : Cell) :
    Refines (checker.demandState raw)
        (.suspended : State fibre raw) /\
      ((Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.checkedPlan
        (fibre := fibre) key raw).demandCheck checker.toNeedChecker cell).2.evaluationCount = 1 :=
  ⟨checker.demandState_refines_suspended raw,
    Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.demandCheck_evaluationCount
      checker key raw cell⟩

/-! ## Domain-level controls and the higher boundary -/

open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentNaturality
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticContextual
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalPi
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.SyntacticJudgmentalSigmaId

/-- Formed-context substitution receives its gradual laws from the generic
constructional interface. -/
def formedSubstitutionSafeTransportLaws
    {Head : Type} {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target) :
    SafeTransportLaws (reindexJudgmentMap morphism) :=
  safeTransportLaws _

/-- Proof-relevant GSLT-IL interaction transport receives the same laws; its
raw endpoint path remains present when occurrence evidence is unavailable. -/
def interactionSafeTransportLaws
    {theory targetTheory : Mettapedia.GSLT.GSLT}
    (presentation : Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation theory)
    (translation :
      Mettapedia.GSLT.IndexedOperational.OperationalTranslation theory targetTheory)
    {source target : theory.Term} :
    SafeTransportLaws
      (Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentInteraction.transportMap
        presentation translation (source := source) (target := target)) :=
  safeTransportLaws _

/-- The cumulative Prime lambda naturality square is an earned safe gradual
square, not an independently postulated gradual rule. -/
def lambdaSafeSquareLaws
    {Head : Type}
    {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    SafeSquareLaws (lambdaNaturalitySquare product morphism) :=
  safeSquareLaws _

/-- The existing non-reflecting collapse is the permanent negative control:
safe transport exists, but stable blame transport cannot be manufactured. -/
theorem forward_transport_does_not_imply_reflection :
    Not (Nonempty
      Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Canary.collapse.ReflectsExact) :=
  Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Canary.collapse_not_reflects

/-- The capability hierarchy is strict: the collapse earns all forward-safe
laws but cannot earn reflection and therefore cannot soundly retain blame. -/
theorem safe_transport_strictly_below_reflecting :
    SafeTransportLaws
        Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Canary.collapse /\
      Not (Nonempty
        Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Canary.collapse.ReflectsExact) :=
  ⟨safeTransportLaws _, forward_transport_does_not_imply_reflection⟩

/-- Dependent second-Sigma beta cannot be collapsed to a homogeneous equality
step: its source and target type codes are genuinely different. -/
theorem dependent_beta_requires_conversion_dimension :
    ((sigmaSecondBetaMap Canary.sigmaRetainedTower
      Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers.Canary.dependentSum).mapRaw
      Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers.Canary.dependentPairInput).sourceType ≠
    ((sigmaSecondBetaMap Canary.sigmaRetainedTower
      Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers.Canary.dependentSum).mapRaw
      Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentTermFormers.Canary.dependentPairInput).targetType :=
  Canary.dependentSigmaSecondBeta_sourceType_ne_targetType

/-! ## Axiom audit -/

#print axioms refines_suspended
#print axioms mapSafe_comp
#print axioms mapFull_comp
#print axioms mapSafe_activateAt
#print axioms combineDependent_activateAt
#print axioms safeTransportLaws
#print axioms reflectingTransportLaws
#print axioms identityReflectingTransportLaws
#print axioms safeSquareLaws
#print axioms checked_run_is_raw
#print axioms demand_revision_dichotomy
#print axioms demand_refines_once
#print axioms lambdaSafeSquareLaws
#print axioms formedSubstitutionSafeTransportLaws
#print axioms interactionSafeTransportLaws
#print axioms forward_transport_does_not_imply_reflection
#print axioms safe_transport_strictly_below_reflecting
#print axioms dependent_beta_requires_conversion_dimension

end Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee
