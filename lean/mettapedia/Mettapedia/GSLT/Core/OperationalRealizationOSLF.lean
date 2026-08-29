import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.OSLF.Framework.IndexedModalFunctor

/-!
# OSLF for path-valued GSLT realizations

Language lowering rarely maps one guest step to exactly one target step.  A
guest step may expand into several administrative target steps, or fuse to no
target step at all.  `OperationalRealization` already records that situation
honestly by mapping each source step to a finite target execution path.

This module supplies the categorical bridge to OSLF.  A path-valued
realization extends to a strict operational translation between the
reflexive-transitive closure GSLTs.  OSLF can then act on those closure GSLTs,
producing the native modal theory of reachability-scale macro-steps.

The closure modal theory is intentionally not identified with the primitive
one-step native theory of the target.  They answer different questions:

* primitive OSLF observes individual runtime transitions;
* closure OSLF observes the finite paths used as compilation macro-steps.

The construction is functorial.  Staging two path-valued realizations and
then applying closure OSLF agrees with applying the construction to each stage
and composing in the contravariant native-theory direction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

universe uTerm uSourceTerm uMiddleTerm uTargetTerm

/-! ## Proof-relevant paths and proposition-valued closure -/

/-- Forget only the proof relevance of a finite execution path. -/
def executionPathToMultiStep {system : GSLT.{uTerm}}
    {source target : system.Term} :
    ExecutionPath system source target -> system.MultiStep source target
  | .refl object => .refl object
  | .cons step rest =>
      .step step.down (executionPathToMultiStep rest)

/-- The older GSLT path carrier and the free-category execution path retain
the same ordered one-step evidence. -/
def rewritePathToExecutionPath {system : GSLT}
    {source target : system.Term} :
    system.RewritePath source target -> ExecutionPath system source target
  | .nil object => .refl object
  | .cons step rest =>
      .cons ⟨step⟩ (rewritePathToExecutionPath rest)

/-- Recover the original GSLT path carrier without erasing any step. -/
def executionPathToRewritePath {system : GSLT}
    {source target : system.Term} :
    ExecutionPath system source target -> system.RewritePath source target
  | .refl object => .nil object
  | .cons step rest =>
      .cons step.down (executionPathToRewritePath rest)

@[simp] theorem executionPathToRewritePath_toExecutionPath
    {system : GSLT} {source target : system.Term}
    (path : system.RewritePath source target) :
    executionPathToRewritePath (rewritePathToExecutionPath path) = path := by
  induction path with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp [rewritePathToExecutionPath, executionPathToRewritePath,
        inductionHypothesis]

@[simp] theorem rewritePathToExecutionPath_toRewritePath
    {system : GSLT} {source target : system.Term}
    (path : ExecutionPath system source target) :
    rewritePathToExecutionPath (executionPathToRewritePath path) = path := by
  induction path with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step
      simp [executionPathToRewritePath, rewritePathToExecutionPath,
        inductionHypothesis]

@[simp] theorem rewritePathToExecutionPath_length
    {system : GSLT} {source target : system.Term}
    (path : system.RewritePath source target) :
    (rewritePathToExecutionPath path).length = path.length := by
  induction path with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp [rewritePathToExecutionPath, GSLT.RewritePath.length,
        Mettapedia.GSLT.Ultrainfinite.Route.length,
        inductionHypothesis, Nat.add_comm]

/-- Concatenate proposition-valued finite runs. -/
def multiStepAppend {system : GSLT.{uTerm}}
    {source middle target : system.Term} :
    system.MultiStep source middle -> system.MultiStep middle target ->
      system.MultiStep source target
  | .refl _, remaining => remaining
  | .step step remaining, later =>
      .step step (multiStepAppend remaining later)

/-! ## Realizations as strict translations of closure GSLTs -/

namespace OperationalRealization

@[ext (iff := false)]
theorem ext {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    {first second : OperationalRealization source target}
    (mapTerm : first.mapTerm = second.mapTerm)
    (mapStep : HEq
      (@OperationalRealization.mapStep source target first)
      (@OperationalRealization.mapStep source target second)) : first = second := by
  cases first with
  | mk firstMap firstEquiv firstStep =>
      cases second with
      | mk secondMap secondEquiv secondStep =>
          dsimp at mapTerm
          cases mapTerm
          cases mapStep
          rfl

/-- Map a proposition-valued source run by retaining each realization path
until the final, explicitly lossy erasure into proposition-valued target
reachability.  No inverse is claimed: a proposition does not determine which
proof occurrence produced it. -/
def mapMultiStep
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (realization : OperationalRealization source target) :
    {sourceTerm targetTerm : source.Term} ->
      source.MultiStep sourceTerm targetTerm ->
        target.MultiStep (realization.mapTerm sourceTerm)
          (realization.mapTerm targetTerm)
  | _, _, .refl object => .refl (realization.mapTerm object)
  | _, _, .step step remaining =>
      multiStepAppend
        (executionPathToMultiStep (realization.mapStep step))
        (realization.mapMultiStep remaining)

/-- A path-valued realization is a strict one-step translation when the
target regards a finite runtime path as one reachability-scale macro-step. -/
def toClosureTranslation
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (realization : OperationalRealization source target) :
    OperationalTranslation source target.closure where
  mapTerm := realization.mapTerm
  mapEquiv := realization.mapEquiv
  mapStep := by
    intro sourceTerm targetTerm step
    exact
      ⟨realization.mapTerm targetTerm,
        executionPathToMultiStep (realization.mapStep step),
        target.equations.iseqv.refl _⟩

/-- A path-valued realization acts on an already closed source by mapping its
entire finite run and retaining the final equation. -/
def onClosures
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (realization : OperationalRealization source target) :
    OperationalTranslation source.closure target.closure where
  mapTerm := realization.mapTerm
  mapEquiv := realization.mapEquiv
  mapStep := by
    intro sourceTerm targetTerm step
    obtain ⟨reached, path, reachedEquivalent⟩ := step
    exact
      ⟨realization.mapTerm reached,
        realization.mapMultiStep path,
        realization.mapEquiv reachedEquivalent⟩

@[simp] theorem onClosures_id (system : GSLT.{uTerm}) :
    (OperationalRealization.id system).onClosures =
      OperationalTranslation.id system.closure := by
  apply OperationalTranslation.ext
  rfl

@[simp] theorem onClosures_comp
    {first : GSLT.{uSourceTerm}} {middle : GSLT.{uMiddleTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalRealization first middle)
    (later : OperationalRealization middle last) :
    (earlier.comp later).onClosures =
      earlier.onClosures.comp later.onClosures := by
  apply OperationalTranslation.ext
  rfl

/-- Closing only after the complete staged realization agrees with entering
the middle closure first and then mapping its finite macro-step. -/
theorem toClosureTranslation_comp
    {first : GSLT.{uSourceTerm}} {middle : GSLT.{uMiddleTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalRealization first middle)
    (later : OperationalRealization middle last) :
    (earlier.comp later).toClosureTranslation =
      earlier.toClosureTranslation.comp later.onClosures := by
  apply OperationalTranslation.ext
  rfl

/-- OSLF predicate transport for one path-valued compiler stage.  The source
and target are closure GSLTs, so this is explicitly the native modal theory of
finite compilation macro-steps. -/
def closureOSLFPullback
    {source target : GSLT.{uTerm}}
    (realization : OperationalRealization source target) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject target.closure)
      (oslfForwardModalObject source.closure) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.pullbackLax
    realization.onClosures

/-- OSLF reverses the stage direction by predicate pullback, while preserving
the compiler's execution order through composition. -/
@[simp] theorem closureOSLFPullback_comp
    {first middle last : GSLT.{uTerm}}
    (earlier : OperationalRealization first middle)
    (later : OperationalRealization middle last) :
    (earlier.comp later).closureOSLFPullback =
      later.closureOSLFPullback.comp earlier.closureOSLFPullback := by
  apply ForwardModalPredicateTheory.Hom.ext
  rfl

end OperationalRealization

/-! ## The realization category and its OSLF functor -/

/-- GSLTs whose arrows may lower one source step to a finite target path. -/
structure RealizationTheory where
  theory : GSLT.{uTerm}

instance : CategoryTheory.Category RealizationTheory where
  Hom source target :=
    OperationalRealization source.theory target.theory
  id source := OperationalRealization.id source.theory
  comp earlier later := earlier.comp later
  id_comp morphism := by
    refine OperationalRealization.ext
      (first := (OperationalRealization.id _).comp morphism)
      (second := morphism) rfl ?_
    apply heq_of_eq
    funext source target step
    change (morphism.mapStep step).append (.refl _) = morphism.mapStep step
    exact Mettapedia.GSLT.Ultrainfinite.Route.append_refl (morphism.mapStep step)
  comp_id morphism := by
    refine OperationalRealization.ext
      (first := morphism.comp (OperationalRealization.id _))
      (second := morphism) rfl ?_
    apply heq_of_eq
    funext source target step
    exact OperationalRealization.mapRoute_id (morphism.mapStep step)
  assoc first second third := by
    refine OperationalRealization.ext
      (first := (first.comp second).comp third)
      (second := first.comp (second.comp third)) rfl ?_
    apply heq_of_eq
    funext source target step
    exact (OperationalRealization.mapRoute_comp second third
      (first.mapStep step)).symm

/-- Reachability closure turns a path-valued realization into an ordinary
one-step operational translation. -/
def realizationClosureFunctor :
    CategoryTheory.Functor RealizationTheory.{uTerm}
      OperationalTheory.{uTerm} where
  obj system := ⟨system.theory.closure⟩
  map realization := realization.onClosures
  map_id system := by
    apply OperationalTranslation.ext
    rfl
  map_comp earlier later := by
    apply OperationalTranslation.ext
    rfl

/-- OSLF for path-valued transformations: first form the reachability-closure
GSLT, then derive its contravariant lax native modal theory. -/
def realizationClosureOSLF :
    CategoryTheory.Functor RealizationTheory.{uTerm}ᵒᵖ
      ForwardModalPredicateTheory.{uTerm} :=
  realizationClosureFunctor.op.comp oslfForwardModalFunctor

/-! ## Positive lowering and negative strictness controls -/

namespace LoweringCanary

inductive TargetState where
  | start
  | middle
  | finish
deriving DecidableEq

inductive TargetStep : TargetState -> TargetState -> Prop where
  | first : TargetStep .start .middle
  | second : TargetStep .middle .finish

def target : GSLT where
  Term := TargetState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TargetStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def mapTerm : OperationalRealization.FusionCanary.source.Term ->
    LoweringCanary.target.Term
  | false => .start
  | true => .finish

/-- One source action genuinely lowers to two target actions. -/
def lowering : OperationalRealization
    OperationalRealization.FusionCanary.source target where
  mapTerm := mapTerm
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := by
    intro sourceTerm targetTerm step
    rcases step with ⟨sourceFalse, targetTrue⟩
    subst sourceTerm
    subst targetTerm
    exact .cons ⟨TargetStep.first⟩
      (.cons ⟨TargetStep.second⟩ (.refl TargetState.finish))

theorem lowering_uses_two_target_steps :
    (lowering.mapStep
      OperationalRealization.FusionCanary.source_step).length = 2 := by
  let concrete : OperationalRealization.FusionCanary.source.Step false true :=
    ⟨rfl, rfl⟩
  have proofEqual : OperationalRealization.FusionCanary.source_step = concrete :=
    Subsingleton.elim _ _
  rw [proofEqual]
  rfl

/-- A strict one-step map with the same endpoint representation cannot pretend
that the two target actions are one primitive action. -/
theorem no_strict_translation_with_lowering_map :
    ¬ ∃ translation : OperationalTranslation
        OperationalRealization.FusionCanary.source target,
      translation.mapTerm = lowering.mapTerm := by
  rintro ⟨translation, mapAgrees⟩
  have impossible := translation.mapStep
    OperationalRealization.FusionCanary.source_step
  have falseAgrees := congrFun mapAgrees false
  have trueAgrees := congrFun mapAgrees true
  change TargetStep (translation.mapTerm false) (translation.mapTerm true) at impossible
  rw [falseAgrees, trueAgrees] at impossible
  cases impossible

/-- The same lowering is a genuine strict translation into reachability
closure, where the two-step path is one macro-step. -/
theorem closure_translation_exists :
    Nonempty (OperationalTranslation
      OperationalRealization.FusionCanary.source target.closure) :=
  ⟨lowering.toClosureTranslation⟩

/-- Fusion is covered by the same abstraction: the already-established
zero-step realization becomes a closure translation, although no primitive
strict translation exists. -/
theorem fusion_closure_translation_exists :
    Nonempty (OperationalTranslation
      OperationalRealization.FusionCanary.source
      OperationalRealization.FusionCanary.target.closure) :=
  ⟨OperationalRealization.FusionCanary.fused.toClosureTranslation⟩

end LoweringCanary

#print axioms multiStepAppend
#print axioms executionPathToRewritePath_toExecutionPath
#print axioms rewritePathToExecutionPath_toRewritePath
#print axioms rewritePathToExecutionPath_length
#print axioms OperationalRealization.mapMultiStep
#print axioms OperationalRealization.onClosures_comp
#print axioms OperationalRealization.toClosureTranslation_comp
#print axioms OperationalRealization.closureOSLFPullback_comp
#print axioms realizationClosureFunctor
#print axioms realizationClosureOSLF
#print axioms LoweringCanary.lowering_uses_two_target_steps
#print axioms LoweringCanary.no_strict_translation_with_lowering_map
#print axioms LoweringCanary.closure_translation_exists
#print axioms LoweringCanary.fusion_closure_translation_exists

end Mettapedia.GSLT.IndexedOperational
