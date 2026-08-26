import Mettapedia.Languages.Lean.Lean4LeanEnvironmentGrowth
import Mettapedia.GSLT.Core.ProofRelevantPresentation
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.OSLF.Framework.IndexedModalFunctor
import Mettapedia.OSLF.Framework.OSLFCertificateGSLTAuthority

/-!
# Directed Lean reduction as a GSLT and OSLF/NTT input

Lean4Lean's `IsDefEq` is a typed, symmetric, transitive declarative judgment.
It is therefore not the directed operational relation from which OSLF should
derive behavioral modalities.  This module supplies a separate axiom-clean
operational fragment.

`CoreRawHeadEvent` presents the evaluator-facing beta, delta, and
head-application steps without presupposing typing.  `CoreHeadEvent` is the
typed proof-relevant refinement.  OSLF therefore analyzes the raw operational
relation, while a separate translation records which steps have already paid
their typing obligations.  The comparison theorem maps every typed event into
Lean4Lean's declarative `IsDefEq` judgment.

The fragment is intentionally smaller than Lean's full reduction system.
Lean4Lean's current `WHRed` and executable environment-verification crowns
depend on unfinished metatheory, so they are comparison candidates rather
than imported authority here.
-/

namespace Mettapedia.Languages.Lean.Lean4LeanDirectedReduction

open Lean4Lean
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.ProofRelevantPresentation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.OSLF.Framework.OSLFCertificateGSLTAuthority

/-! ## Raw directed events -/

/-- The evaluator-facing directed core.  Beta and head-application do not
presuppose a typing derivation.  Delta retains only the environment membership
and universe-instantiation evidence needed to identify the authored equation.

This is intentionally a smaller relation than Lean's complete weak-head
reduction: recursor/iota, projection, quotient, primitive, and native reduction
remain later extensions. -/
inductive CoreRawHeadEvent (environment : VEnv) (universeParameters : Nat) :
    VExpr -> VExpr -> Type where
  | beta {domain body argument : VExpr} :
      CoreRawHeadEvent environment universeParameters
        (.app (.lam domain body) argument)
        (body.inst argument)
  | delta {definition : VDefEq} {levels : List VLevel}
      (member : environment.defeqs definition)
      (levelsWellFormed : forall level, level ∈ levels ->
        level.WF universeParameters)
      (levelCount : levels.length = definition.uvars) :
      CoreRawHeadEvent environment universeParameters
        (definition.lhs.instL levels)
        (definition.rhs.instL levels)
  | app {function function' argument : VExpr}
      (head : CoreRawHeadEvent environment universeParameters function function') :
      CoreRawHeadEvent environment universeParameters
        (.app function argument)
        (.app function' argument)

namespace CoreRawHeadEvent

variable {environment extended : VEnv} {universeParameters : Nat}

/-- Raw core steps transport monotonically across environment growth. -/
def mapEnvironment (extension : environment <= extended) :
    forall {source target : VExpr},
    CoreRawHeadEvent environment universeParameters source target ->
    CoreRawHeadEvent extended universeParameters source target
  | _, _, .beta => .beta
  | _, _, .delta member levelsWellFormed levelCount =>
      .delta (extension.defeqs member) levelsWellFormed levelCount
  | _, _, .app head => .app (mapEnvironment extension head)

/-- Raw sources are applications or installed definitional left sides. -/
theorem sourceShape
    {source target : VExpr}
    (event : CoreRawHeadEvent environment universeParameters source target) :
    (Exists fun function => Exists fun argument =>
      source = .app function argument) \/
      Exists fun definition => environment.defeqs definition := by
  cases event with
  | beta => exact Or.inl ⟨_, _, rfl⟩
  | delta member _ _ => exact Or.inr ⟨_, member⟩
  | app => exact Or.inl ⟨_, _, rfl⟩

end CoreRawHeadEvent

/-! ## Typed directed events -/

/-- A proof-relevant directed head-reduction event in the axiom-clean
Lean4Lean declarative fragment.  The first index is the common type of both
endpoints.

The constructors are deliberately oriented: beta and delta do not acquire
their symmetric converses merely because `IsDefEq` is symmetric. -/
inductive CoreHeadEvent (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) :
    (expectedType source target : VExpr) -> Type where
  | beta {domain body argument codomain : VExpr}
      (bodyTyped :
        environment.HasType universeParameters (domain :: context) body codomain)
      (argumentTyped :
        environment.HasType universeParameters context argument domain) :
      CoreHeadEvent environment universeParameters context
        (codomain.inst argument)
        (.app (.lam domain body) argument)
        (body.inst argument)
  | delta {definition : VDefEq} {levels : List VLevel}
      (member : environment.defeqs definition)
      (levelsWellFormed : forall level, level ∈ levels ->
        level.WF universeParameters)
      (levelCount : levels.length = definition.uvars) :
      CoreHeadEvent environment universeParameters context
        (definition.type.instL levels)
        (definition.lhs.instL levels)
        (definition.rhs.instL levels)
  | app {domain codomain function function' argument : VExpr}
      (head : CoreHeadEvent environment universeParameters context
        (.forallE domain codomain) function function')
      (argumentTyped :
        environment.HasType universeParameters context argument domain) :
      CoreHeadEvent environment universeParameters context
        (codomain.inst argument)
        (.app function argument)
        (.app function' argument)

namespace CoreHeadEvent

variable {environment extended : VEnv} {universeParameters : Nat}
  {context : List VExpr}

/-- Forget the typing evidence while preserving the exact directed event. -/
def toRaw : forall {expectedType source target : VExpr},
    CoreHeadEvent environment universeParameters context
      expectedType source target ->
    CoreRawHeadEvent environment universeParameters source target
  | _, _, _, .beta _ _ => .beta
  | _, _, _, .delta member levelsWellFormed levelCount =>
      .delta member levelsWellFormed levelCount
  | _, _, _, .app head _ => .app (toRaw head)

/-- Every directed event is sound for Lean4Lean's independently authored
declarative conversion judgment. -/
def defEq : forall {expectedType source target : VExpr},
    CoreHeadEvent environment universeParameters context
      expectedType source target ->
    environment.IsDefEq universeParameters context source target expectedType
  | _, _, _, .beta bodyTyped argumentTyped => .beta bodyTyped argumentTyped
  | _, _, _, .delta member levelsWellFormed levelCount =>
      .extra member levelsWellFormed levelCount
  | _, _, _, .app head argumentTyped => .appDF (defEq head) argumentTyped

/-- Both endpoints of a directed event have its indexed type. -/
theorem endpointsTyped
    {expectedType source target : VExpr}
    (event : CoreHeadEvent environment universeParameters context
      expectedType source target) :
    environment.HasType universeParameters context source expectedType /\
      environment.HasType universeParameters context target expectedType :=
  event.defEq.hasType

/-- Core directed events transport monotonically across environment growth. -/
def mapEnvironment (extension : environment <= extended) :
    forall {expectedType source target : VExpr},
    CoreHeadEvent environment universeParameters context
      expectedType source target ->
    CoreHeadEvent extended universeParameters context expectedType source target
  | _, _, _, .beta bodyTyped argumentTyped =>
      .beta (bodyTyped.mono extension) (argumentTyped.mono extension)
  | _, _, _, .delta member levelsWellFormed levelCount =>
      .delta (extension.defeqs member) levelsWellFormed levelCount
  | _, _, _, .app head argumentTyped =>
      .app (mapEnvironment extension head) (argumentTyped.mono extension)

/-- A source of a core head event is either an application or the left side
of an installed definitional equation. -/
theorem sourceShape
    {expectedType source target : VExpr}
    (event : CoreHeadEvent environment universeParameters context
      expectedType source target) :
    (Exists fun function => Exists fun argument =>
      source = .app function argument) \/
      Exists fun definition => environment.defeqs definition := by
  cases event with
  | beta => exact Or.inl ⟨_, _, rfl⟩
  | delta member _ _ => exact Or.inr ⟨_, member⟩
  | app => exact Or.inl ⟨_, _, rfl⟩

end CoreHeadEvent

/-! ## Extensional and proof-relevant GSLT presentations -/

/-- The evaluator-facing core GSLT.  Its steps are raw directed machine
events; typing is not smuggled into the operational relation. -/
def coreRawHeadGSLT (environment : VEnv) (universeParameters : Nat) : GSLT where
  Term := VExpr
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty (CoreRawHeadEvent environment universeParameters source target)
  rewrites_resp_left := by
    intro source source' target equal event
    subst source'
    exact ⟨target, event, rfl⟩
  rewrites_resp_right := by
    intro source target target' event equal
    subst target'
    exact event

@[simp] theorem coreRawHeadGSLT_step_iff
    (environment : VEnv) (universeParameters : Nat)
    (source target : VExpr) :
    (coreRawHeadGSLT environment universeParameters).Step source target <->
      Nonempty (CoreRawHeadEvent environment universeParameters source target) :=
  Iff.rfl

/-- Exact raw event fibres present the evaluator-facing GSLT. -/
def coreRawHeadStepPresentation (environment : VEnv) (universeParameters : Nat) :
    StepPresentation (coreRawHeadGSLT environment universeParameters) where
  Evidence := CoreRawHeadEvent environment universeParameters
  erases_iff := by
    intro source target
    rfl

/-- The evaluator-facing core bundled with raw event occurrences. -/
def coreRawHeadPresentedGSLT (environment : VEnv) (universeParameters : Nat) :
    PresentedGSLT where
  theory := coreRawHeadGSLT environment universeParameters
  steps := coreRawHeadStepPresentation environment universeParameters

/-- The proposition-valued typed refinement obtained by forgetting exact
typed-event identity.  Structural equations are syntactic equality; typed
definitional equality remains the separate declarative comparison relation. -/
def coreHeadGSLT (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) : GSLT where
  Term := VExpr
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty (CoreHeadEvent environment universeParameters context
      expectedType source target)
  rewrites_resp_left := by
    intro source source' target equal event
    subst source'
    exact ⟨target, event, rfl⟩
  rewrites_resp_right := by
    intro source target target' event equal
    subst target'
    exact event

@[simp] theorem coreHeadGSLT_step_iff
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr) :
    (coreHeadGSLT environment universeParameters context expectedType).Step
        source target <->
      Nonempty (CoreHeadEvent environment universeParameters context
        expectedType source target) :=
  Iff.rfl

/-- The authored event fibres present exactly the extensional GSLT steps. -/
def coreHeadStepPresentation (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) :
    StepPresentation
      (coreHeadGSLT environment universeParameters context expectedType) where
  Evidence := CoreHeadEvent environment universeParameters context expectedType
  erases_iff := by
    intro source target
    rfl

/-- The directed core bundled with its proof-relevant event presentation. -/
def coreHeadPresentedGSLT (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) : PresentedGSLT where
  theory := coreHeadGSLT environment universeParameters context expectedType
  steps := coreHeadStepPresentation environment universeParameters context expectedType

/-- The typed operational refinement embeds into the evaluator-facing raw
calculus by erasing only typing evidence. -/
def typedToRawTranslation
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) :
    OperationalTranslation
      (coreHeadGSLT environment universeParameters context expectedType)
      (coreRawHeadGSLT environment universeParameters) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := by
    rintro source target ⟨event⟩
    exact ⟨event.toRaw⟩

/-! ## OSLF/NTT analysis and comparison with Lean4Lean -/

abbrev CoreRawHeadNativeType (environment : VEnv)
    (universeParameters : Nat) : Type :=
  GSLTNativeType (coreRawHeadGSLT environment universeParameters)

abbrev exactCoreRawHeadTargetType
    (environment : VEnv) (universeParameters : Nat) (target : VExpr) :
    CoreRawHeadNativeType environment universeParameters :=
  exactTargetNativeType (coreRawHeadGSLT environment universeParameters) target

/-- Raw OSLF exact-target inhabitation is exactly one evaluator-facing event. -/
theorem satisfies_exactCoreRawHeadTargetType_iff_event
    (environment : VEnv) (universeParameters : Nat)
    (source target : VExpr) :
    (gsltOSLF (coreRawHeadGSLT environment universeParameters)).satisfies
        source
        (exactCoreRawHeadTargetType environment universeParameters target).pred <->
      Nonempty (CoreRawHeadEvent environment universeParameters source target) := by
  rw [satisfies_exactTargetNativeType_iff_step]
  rfl

/-- Exact raw-step decision is the first executable comparison contract.  A
Lean4Lean realization inhabits it only by deciding precisely the GSLT relation,
not by agreeing on selected examples. -/
theorem rawStepDecision_accepts_iff_exactCoreRawHeadTargetType
    (environment : VEnv) (universeParameters : Nat)
    (source target : VExpr)
    (decision : EffectiveStructure.StepDecision
      (coreRawHeadGSLT environment universeParameters)) :
    decision.decideStep source target = true <->
      (gsltOSLF (coreRawHeadGSLT environment universeParameters)).satisfies
        source
        (exactCoreRawHeadTargetType environment universeParameters target).pred := by
  rw [decision.correct]
  exact (satisfies_exactCoreRawHeadTargetType_iff_event environment
    universeParameters source target).symm

/-- OSLF exact-target type for finite raw reduction, obtained by applying the
same construction to the canonical reflexive-transitive GSLT closure. -/
abbrev exactCoreRawHeadClosureTargetType
    (environment : VEnv) (universeParameters : Nat) (target : VExpr) :
    GSLTNativeType (coreRawHeadGSLT environment universeParameters).closure :=
  exactTargetNativeType
    (coreRawHeadGSLT environment universeParameters).closure target

/-- Any proved executable normalizer lands in the OSLF type generated from
the finite-reduction closure.  This is the comparison contract for
Lean4Lean-style weak-head normalization. -/
theorem reductionNormalizer_result_inhabits_closure_ntt
    (environment : VEnv) (universeParameters : Nat)
    (normalizer : EffectiveStructure.ReductionNormalizer
      (coreRawHeadGSLT environment universeParameters))
    (source : VExpr) :
    (gsltOSLF (coreRawHeadGSLT environment universeParameters).closure).satisfies
      source
      (exactCoreRawHeadClosureTargetType environment universeParameters
        (normalizer.normalize source)).pred := by
  rw [satisfies_exactTargetNativeType_iff_step]
  exact ⟨normalizer.normalize source, normalizer.reduces source, rfl⟩

/-- The same realization contract exposes terminality separately from
reachability; OSLF exact-target inhabitation alone does not imply normality. -/
theorem reductionNormalizer_result_is_normal
    (environment : VEnv) (universeParameters : Nat)
    (normalizer : EffectiveStructure.ReductionNormalizer
      (coreRawHeadGSLT environment universeParameters))
    (source : VExpr) :
    (coreRawHeadGSLT environment universeParameters).IsNormalForm
      (normalizer.normalize source) :=
  normalizer.normal source

abbrev CoreHeadNativeType (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) : Type :=
  GSLTNativeType
    (coreHeadGSLT environment universeParameters context expectedType)

abbrev exactCoreHeadTargetType
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType target : VExpr) :
    CoreHeadNativeType environment universeParameters context expectedType :=
  exactTargetNativeType
    (coreHeadGSLT environment universeParameters context expectedType) target

/-- The complete `Lean GSLT -> OSLF -> NTT` one-step claim.  Its native type
is generated by the generic OSLF construction; no Lean-specific checker is
hidden in this definition. -/
def coreHeadNativeClaim
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr) :
    NativeClaim
      (gsltOSLF
        (coreHeadGSLT environment universeParameters context expectedType)) :=
  exactStepNativeClaim
    (coreHeadGSLT environment universeParameters context expectedType)
    source target

/-- Unlike the declarative-relation presentation, this exact-target modality
means the existence of an oriented beta/delta/head-application occurrence. -/
theorem satisfies_exactCoreHeadTargetType_iff_event
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr) :
    (gsltOSLF
      (coreHeadGSLT environment universeParameters context expectedType)).satisfies
        source
        (exactCoreHeadTargetType environment universeParameters context
          expectedType target).pred <->
      Nonempty (CoreHeadEvent environment universeParameters context
        expectedType source target) := by
  rw [satisfies_exactTargetNativeType_iff_step]
  rfl

/-- Any inhabitant of the typed exact-target type also inhabits the raw
evaluator-facing exact-target type.  The converse is precisely a subject-
reduction/inversion obligation and is not asserted. -/
theorem exactCoreHeadTargetType_to_raw
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr)
    (inhabited :
      (gsltOSLF
        (coreHeadGSLT environment universeParameters context expectedType)).satisfies
          source
          (exactCoreHeadTargetType environment universeParameters context
            expectedType target).pred) :
    (gsltOSLF (coreRawHeadGSLT environment universeParameters)).satisfies
      source
      (exactCoreRawHeadTargetType environment universeParameters target).pred := by
  obtain ⟨event⟩ :=
    (satisfies_exactCoreHeadTargetType_iff_event environment universeParameters
      context expectedType source target).mp inhabited
  exact (satisfies_exactCoreRawHeadTargetType_iff_event environment
    universeParameters source target).mpr ⟨event.toRaw⟩

/-- The generic OSLF native claim is extensionally complete for the authored
directed event relation.  This is the exact comparison point for a future
Lean4Lean step checker. -/
theorem coreHeadNativeClaim_meaning_iff_event
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr) :
    (coreHeadNativeClaim environment universeParameters context expectedType
      source target).Meaning <->
      Nonempty (CoreHeadEvent environment universeParameters context
        expectedType source target) := by
  unfold coreHeadNativeClaim
  rw [exactStepNativeClaim_meaning_iff_step]
  rfl

/-- The load-bearing OSLF-to-Lean4Lean comparison: every inhabitant of the
generated directed one-step type denotes a valid declarative conversion. -/
theorem exactCoreHeadTargetType_sound_defEq
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr)
    (inhabited :
      (gsltOSLF
        (coreHeadGSLT environment universeParameters context expectedType)).satisfies
          source
          (exactCoreHeadTargetType environment universeParameters context
            expectedType target).pred) :
    environment.IsDefEq universeParameters context source target expectedType := by
  obtain ⟨event⟩ :=
    (satisfies_exactCoreHeadTargetType_iff_event environment universeParameters
      context expectedType source target).mp inhabited
  exact event.defEq

/-- Generated directed-step inhabitation preserves the independently authored
Lean4Lean typing judgment at both endpoints. -/
theorem exactCoreHeadTargetType_endpoints_typed
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr)
    (inhabited :
      (gsltOSLF
        (coreHeadGSLT environment universeParameters context expectedType)).satisfies
          source
          (exactCoreHeadTargetType environment universeParameters context
            expectedType target).pred) :
    environment.HasType universeParameters context source expectedType /\
      environment.HasType universeParameters context target expectedType :=
  (exactCoreHeadTargetType_sound_defEq environment universeParameters context
    expectedType source target inhabited).hasType

/-- Exact step decision is the algorithmic contract required of any proposed
Lean4Lean realization of this GSLT fragment.  The theorem compares a checker
result to OSLF/NTT meaning without identifying the checker with that meaning. -/
theorem stepDecision_accepts_iff_exactCoreHeadTargetType
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType source target : VExpr)
    (decision : EffectiveStructure.StepDecision
      (coreHeadGSLT environment universeParameters context expectedType)) :
    decision.decideStep source target = true <->
      (gsltOSLF
        (coreHeadGSLT environment universeParameters context expectedType)).satisfies
          source
          (exactCoreHeadTargetType environment universeParameters context
            expectedType target).pred := by
  rw [decision.correct]
  exact (satisfies_exactCoreHeadTargetType_iff_event environment
    universeParameters context expectedType source target).symm

/-! ## Environment-indexed transport -/

/-- Environment growth transports evaluator-facing raw steps forward. -/
def coreRawHeadEnvironmentTranslation
    {environment extended : VEnv} (extension : environment <= extended)
    (universeParameters : Nat) :
    OperationalTranslation
      (coreRawHeadGSLT environment universeParameters)
      (coreRawHeadGSLT extended universeParameters) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := by
    rintro source target ⟨event⟩
    exact ⟨event.mapEnvironment extension⟩

/-- The evaluator-facing GSLT at one stage of environment growth. -/
def coreRawHeadStageTheory
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) (stage : Nat) : OperationalTheory :=
  ⟨coreRawHeadGSLT (growth.stage stage) universeParameters⟩

/-- An adjacent environment-growth arrow for the evaluator-facing GSLT. -/
def coreRawHeadStageArrow
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) (stage : Nat) :
    coreRawHeadStageTheory growth universeParameters stage ⟶
      coreRawHeadStageTheory growth universeParameters (stage + 1) :=
  coreRawHeadEnvironmentTranslation
    (growth.transition stage).environmentLE universeParameters

/-- The evaluator-facing Lean core as a `Nat`-indexed forward diagram, which
is the concrete presentation needed for a later `Ind(GSLT)` construction.
New definitions may add delta steps, so the diagram is intentionally forward.
No free filtered-colimit completion is claimed here. -/
def coreRawHeadEnvironmentDiagram
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) : Diagram Nat :=
  CategoryTheory.Functor.ofSequence
    (coreRawHeadStageArrow growth universeParameters)

/-- Pointwise OSLF over evaluator-facing environment growth.  Since a later
environment may add delta behavior, this is a lax modal diagram indexed by
the opposite growth order rather than an exact modal diagram. -/
def coreRawHeadIndexedOSLF
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) :=
  forwardIndexedOSLF (coreRawHeadEnvironmentDiagram growth universeParameters)

@[simp] theorem coreRawHeadIndexedOSLF_obj
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters stage : Nat) :
    (coreRawHeadIndexedOSLF growth universeParameters).obj
        (Opposite.op stage) =
      oslfForwardModalObject
        (coreRawHeadGSLT (growth.stage stage) universeParameters) :=
  rfl

/-- Raw OSLF/NTT exact-target inhabitation transports across environment
growth. -/
theorem environment_growth_preserves_coreRawHead_type
    {environment extended : VEnv} (extension : environment <= extended)
    (universeParameters : Nat) (source target : VExpr)
    (event : CoreRawHeadEvent environment universeParameters source target) :
    (gsltOSLF (coreRawHeadGSLT extended universeParameters)).satisfies
      source
      (exactCoreRawHeadTargetType extended universeParameters target).pred :=
  (satisfies_exactCoreRawHeadTargetType_iff_event extended universeParameters
    source target).mpr ⟨event.mapEnvironment extension⟩

/-- Forward environment growth satisfies the lax diamond law: an old
possible reduction remains possible after transport. -/
theorem environment_growth_diamond_lax
    {environment extended : VEnv} (extension : environment <= extended)
    (universeParameters : Nat)
    (predicate : Set (coreRawHeadGSLT extended universeParameters).Term) :
    gsltDiamond (coreRawHeadGSLT environment universeParameters)
        (Set.preimage id predicate) <=
      Set.preimage id
        (gsltDiamond (coreRawHeadGSLT extended universeParameters) predicate) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.preimage_diamond_le
    (coreRawHeadEnvironmentTranslation extension universeParameters) predicate

/-- The contravariant lax box law also survives forward growth. -/
theorem environment_growth_box_lax
    {environment extended : VEnv} (extension : environment <= extended)
    (universeParameters : Nat)
    (predicate : Set (coreRawHeadGSLT extended universeParameters).Term) :
    Set.preimage id
        (gsltBox (coreRawHeadGSLT extended universeParameters) predicate) <=
      gsltBox (coreRawHeadGSLT environment universeParameters)
        (Set.preimage id predicate) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.preimage_box_le
    (coreRawHeadEnvironmentTranslation extension universeParameters) predicate

/-- Environment growth transports directed events forward while retaining
their beta/delta/application constructor. -/
def coreHeadEnvironmentTranslation
    {environment extended : VEnv} (extension : environment <= extended)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) :
    OperationalTranslation
      (coreHeadGSLT environment universeParameters context expectedType)
      (coreHeadGSLT extended universeParameters context expectedType) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := by
    rintro source target ⟨event⟩
    exact ⟨event.mapEnvironment extension⟩

/-- The directed operational GSLT at one stage of an ordered Lean environment
growth. -/
def coreHeadStageTheory (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) (stage : Nat) : OperationalTheory :=
  ⟨coreHeadGSLT (growth.stage stage) universeParameters context expectedType⟩

/-- An adjacent environment-growth arrow between directed Lean GSLT fibres. -/
def coreHeadStageArrow (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) (stage : Nat) :
    coreHeadStageTheory growth universeParameters context expectedType stage ⟶
      coreHeadStageTheory growth universeParameters context expectedType (stage + 1) :=
  coreHeadEnvironmentTranslation
    (growth.transition stage).environmentLE universeParameters context expectedType

/-- The directed Lean fragment as a sequence-valued diagram in the forward
operational category.  It is an `Ind(GSLT)` presentation candidate, not yet an
object equipped with the free filtered-colimit completion's universal
property.  Each fibre separately receives its OSLF/NTT semantics; growth
itself is not claimed to reflect newly added delta behavior. -/
def coreHeadEnvironmentDiagram
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) : Diagram Nat :=
  CategoryTheory.Functor.ofSequence
    (coreHeadStageArrow growth universeParameters context expectedType)

/-- Pointwise lax OSLF over the typed environment-indexed reduction fibres. -/
def coreHeadIndexedOSLF
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) :=
  forwardIndexedOSLF
    (coreHeadEnvironmentDiagram growth universeParameters context expectedType)

@[simp] theorem coreHeadIndexedOSLF_obj
    (growth : Lean4LeanEnvironmentGrowth.CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) (stage : Nat) :
    (coreHeadIndexedOSLF growth universeParameters context expectedType).obj
        (Opposite.op stage) =
      oslfForwardModalObject
        (coreHeadGSLT (growth.stage stage) universeParameters context
          expectedType) :=
  rfl

/-- OSLF/NTT inhabitation generated from a directed event survives a valid
environment extension.  No converse is claimed. -/
theorem environment_growth_preserves_coreHead_type
    {environment extended : VEnv} (extension : environment <= extended)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType source target : VExpr)
    (event : CoreHeadEvent environment universeParameters context
      expectedType source target) :
    (gsltOSLF
      (coreHeadGSLT extended universeParameters context expectedType)).satisfies
        source
        (exactCoreHeadTargetType extended universeParameters context
          expectedType target).pred :=
  (satisfies_exactCoreHeadTargetType_iff_event extended universeParameters
    context expectedType source target).mpr
      ⟨event.mapEnvironment extension⟩

/-! ## Nondegeneracy canaries -/

namespace Canary

def domain : VExpr := .sort .zero
def argument : VExpr :=
  .const Lean4LeanEnvironmentGrowth.Canary.typeName []
def body : VExpr := .bvar 0
def betaSource : VExpr := .app (.lam domain body) argument
def betaType : VExpr := domain.lift.inst argument
def betaTarget : VExpr := body.inst argument

/-! ### Environment growth need not be modally covered -/

def freshDefEq : VDefEq where
  uvars := 0
  lhs := .sort .zero
  rhs := .sort (.succ .zero)
  type := .sort (.succ (.succ .zero))

def afterFreshDefEq : VEnv := VEnv.empty.addDefEq freshDefEq

def freshDeltaEvent :
    CoreRawHeadEvent afterFreshDefEq 0 freshDefEq.lhs freshDefEq.rhs :=
  CoreRawHeadEvent.delta (definition := freshDefEq) (levels := [])
    VEnv.addDefEq_self (by simp) rfl

theorem freshDelta_is_new_target_step :
    (coreRawHeadGSLT afterFreshDefEq 0).Step freshDefEq.lhs freshDefEq.rhs :=
  ⟨freshDeltaEvent⟩

theorem empty_has_no_step_from_freshDelta_source
    (target : VExpr) :
    Not ((coreRawHeadGSLT VEnv.empty 0).Step freshDefEq.lhs target) := by
  rintro ⟨event⟩
  obtain ⟨function, argument, impossible⟩ | ⟨definition, member⟩ :=
    event.sourceShape
  · cases impossible
  · exact member.elim

/-- Adding a definitional equation preserves old steps but is not locally
step-reflecting at old terms.  Therefore this genuine environment extension
is not an arrow in the exact modal source category of OSLF. -/
theorem addDefEq_raw_growth_not_covered :
    Not (Nonempty (Mettapedia.GSLT.Ultrainfinite.StepCover
      (coreRawHeadGSLT VEnv.empty 0)
      (coreRawHeadGSLT afterFreshDefEq 0) id)) := by
  rintro ⟨cover⟩
  obtain ⟨sourceTarget, sourceStep, _⟩ :=
    cover.liftStep freshDelta_is_new_target_step
  exact empty_has_no_step_from_freshDelta_source sourceTarget sourceStep

/-- Consequently the actual forward operational translation induced by this
extension has no exact modal extension. -/
theorem addDefEq_translation_has_no_modal_extension :
    Not (Exists fun modal : ModalTranslation
      (coreRawHeadGSLT VEnv.empty 0)
      (coreRawHeadGSLT afterFreshDefEq 0) =>
      modal.toCoveredTranslation.toOperational =
        coreRawHeadEnvironmentTranslation VEnv.addDefEq_le 0) := by
  rintro ⟨modal, agrees⟩
  have mapAgrees : modal.toCoveredTranslation.mapTerm = id := by
    have := congrArg OperationalTranslation.mapTerm agrees
    exact this
  have targetStep :
      (coreRawHeadGSLT afterFreshDefEq 0).Step
        (modal.toCoveredTranslation.mapTerm freshDefEq.lhs) freshDefEq.rhs := by
    rw [mapAgrees]
    exact freshDelta_is_new_target_step
  obtain ⟨sourceTarget, sourceStep, _⟩ :=
    modal.toCoveredTranslation.cover.liftStep targetStep
  exact empty_has_no_step_from_freshDelta_source sourceTarget sourceStep

/-- The lax diamond law for definition growth is strict: exact diamond
commutation would reconstruct the outgoing step cover just refuted above. -/
theorem addDefEq_diamond_lax_is_not_exact :
    Not (forall predicate : Set
        (coreRawHeadGSLT afterFreshDefEq 0).Term,
      Set.preimage id
          (gsltDiamond (coreRawHeadGSLT afterFreshDefEq 0) predicate) =
        gsltDiamond (coreRawHeadGSLT VEnv.empty 0)
          (Set.preimage id predicate)) := by
  intro exactDiamond
  have covered : Nonempty (Mettapedia.GSLT.Ultrainfinite.StepCover
      (coreRawHeadGSLT VEnv.empty 0)
      (coreRawHeadGSLT afterFreshDefEq 0) id) :=
    (Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.OperationalTranslation.diamondCommutation_iff_covered
      (coreRawHeadEnvironmentTranslation VEnv.addDefEq_le 0)).mp exactDiamond
  exact addDefEq_raw_growth_not_covered covered

@[simp] theorem betaType_eq_domain : betaType = domain := by
  rfl

@[simp] theorem betaTarget_eq_argument : betaTarget = argument := by
  rfl

theorem bodyTyped :
    Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom.HasType
      0 [domain] body domain.lift := by
  simpa [domain, body] using
    (VEnv.HasType.bvar
      (env := Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom) (U := 0)
      (Lookup.zero : Lookup [domain] 0 domain.lift))

/-- The concrete declaration history gives a nontrivial first arrow of the
directed diagram underlying the future `Ind(GSLT)` construction. -/
theorem singleAxiomDirectedDiagram_first_map :
    (coreHeadEnvironmentDiagram
      Lean4LeanEnvironmentGrowth.Canary.singleAxiomGrowth 0 [] domain).map
        Lean4LeanEnvironmentGrowth.Canary.firstGrowth =
      coreHeadEnvironmentTranslation
        Lean4LeanEnvironmentGrowth.Canary.typeAxiomStep.environment_le
        0 [] domain := by
  exact CategoryTheory.Functor.ofSequence_map_homOfLE_succ
    (coreHeadStageArrow
      Lean4LeanEnvironmentGrowth.Canary.singleAxiomGrowth 0 [] domain) 0

/-- The same concrete history gives a nontrivial first arrow of the raw
evaluator-facing diagram. -/
theorem singleAxiomRawDirectedDiagram_first_map :
    (coreRawHeadEnvironmentDiagram
      Lean4LeanEnvironmentGrowth.Canary.singleAxiomGrowth 0).map
        Lean4LeanEnvironmentGrowth.Canary.firstGrowth =
      coreRawHeadEnvironmentTranslation
        Lean4LeanEnvironmentGrowth.Canary.typeAxiomStep.environment_le 0 := by
  exact CategoryTheory.Functor.ofSequence_map_homOfLE_succ
    (coreRawHeadStageArrow
      Lean4LeanEnvironmentGrowth.Canary.singleAxiomGrowth 0) 0

def rawBetaEvent :
    CoreRawHeadEvent Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom
      0 betaSource betaTarget := by
  simpa [betaSource, betaTarget, argument, domain, body] using
    (CoreRawHeadEvent.beta (environment :=
      Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom)
      (universeParameters := 0) (domain := domain)
      (body := body) (argument := argument))

theorem beta_inhabits_raw_directed_ntt :
    (gsltOSLF (coreRawHeadGSLT
      Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0)).satisfies
      betaSource
      (exactCoreRawHeadTargetType
        Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 betaTarget).pred :=
  (satisfies_exactCoreRawHeadTargetType_iff_event
    Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0
    betaSource betaTarget).mpr ⟨rawBetaEvent⟩

def betaEvent :
    CoreHeadEvent Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom
      0 [] betaType betaSource betaTarget := by
  simpa [betaType, betaSource, betaTarget, argument, domain, body] using
    (CoreHeadEvent.beta bodyTyped
      Lean4LeanEnvironmentGrowth.Canary.typeConstant_available)

theorem beta_inhabits_directed_ntt :
    (gsltOSLF (coreHeadGSLT
      Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] betaType)).satisfies
      betaSource
      (exactCoreHeadTargetType
        Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] betaType
        betaTarget).pred :=
  (satisfies_exactCoreHeadTargetType_iff_event
    Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 []
    betaType betaSource betaTarget).mpr ⟨betaEvent⟩

/-- The directed event maps into Lean4Lean conversion. -/
theorem beta_is_declaratively_equal :
    Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom.IsDefEq
      0 [] betaSource betaTarget betaType :=
  betaEvent.defEq

/-- Declarative conversion also contains the reverse edge by symmetry. -/
theorem declarative_relation_accepts_beta_reverse :
    (Lean4LeanEnvironmentGrowth.defEqRelationGSLT
      Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] betaType).Step
        betaTarget betaSource :=
  beta_is_declaratively_equal.symm

/-- But the authored operational calculus has no reverse beta event. -/
theorem no_beta_reverse_event :
    Not (Nonempty (CoreHeadEvent
      Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 []
      betaType betaTarget betaSource)) := by
  rintro ⟨event⟩
  obtain ⟨function, argument, impossible⟩ | ⟨definition, member⟩ :=
    event.sourceShape
  · cases impossible
  · exact member.elim

/-- The raw evaluator-facing calculus also rejects reverse beta. -/
theorem no_raw_beta_reverse_event :
    Not (Nonempty (CoreRawHeadEvent
      Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0
      betaTarget betaSource)) := by
  rintro ⟨event⟩
  obtain ⟨function, argument, impossible⟩ | ⟨definition, member⟩ :=
    event.sourceShape
  · cases impossible
  · exact member.elim

theorem raw_directed_ntt_rejects_beta_reverse :
    Not
      ((gsltOSLF (coreRawHeadGSLT
        Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0)).satisfies
        betaTarget
        (exactCoreRawHeadTargetType
          Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 betaSource).pred) := by
  rw [satisfies_exactCoreRawHeadTargetType_iff_event]
  exact no_raw_beta_reverse_event

/-- Therefore the reverse declarative equality does not inhabit the directed
OSLF/NTT one-step type. -/
theorem directed_ntt_rejects_beta_reverse :
    Not
      ((gsltOSLF (coreHeadGSLT
        Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] betaType)).satisfies
        betaTarget
        (exactCoreHeadTargetType
          Lean4LeanEnvironmentGrowth.Canary.afterTypeAxiom 0 [] betaType
          betaSource).pred) := by
  rw [satisfies_exactCoreHeadTargetType_iff_event]
  exact no_beta_reverse_event

end Canary

section AxiomAudit

#print axioms CoreRawHeadEvent.mapEnvironment
#print axioms CoreHeadEvent.defEq
#print axioms CoreHeadEvent.toRaw
#print axioms CoreHeadEvent.mapEnvironment
#print axioms satisfies_exactCoreRawHeadTargetType_iff_event
#print axioms rawStepDecision_accepts_iff_exactCoreRawHeadTargetType
#print axioms reductionNormalizer_result_inhabits_closure_ntt
#print axioms reductionNormalizer_result_is_normal
#print axioms exactCoreHeadTargetType_to_raw
#print axioms coreHeadNativeClaim_meaning_iff_event
#print axioms exactCoreHeadTargetType_sound_defEq
#print axioms exactCoreHeadTargetType_endpoints_typed
#print axioms stepDecision_accepts_iff_exactCoreHeadTargetType
#print axioms environment_growth_preserves_coreRawHead_type
#print axioms environment_growth_diamond_lax
#print axioms environment_growth_box_lax
#print axioms environment_growth_preserves_coreHead_type
#print axioms Canary.addDefEq_raw_growth_not_covered
#print axioms Canary.addDefEq_translation_has_no_modal_extension
#print axioms Canary.addDefEq_diamond_lax_is_not_exact
#print axioms Canary.beta_inhabits_raw_directed_ntt
#print axioms Canary.beta_inhabits_directed_ntt
#print axioms Canary.singleAxiomRawDirectedDiagram_first_map
#print axioms Canary.singleAxiomDirectedDiagram_first_map
#print axioms Canary.declarative_relation_accepts_beta_reverse
#print axioms Canary.raw_directed_ntt_rejects_beta_reverse
#print axioms Canary.directed_ntt_rejects_beta_reverse

end AxiomAudit

end Mettapedia.Languages.Lean.Lean4LeanDirectedReduction
