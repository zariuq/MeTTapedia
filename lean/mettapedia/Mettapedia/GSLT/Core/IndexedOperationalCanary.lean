import Mathlib.CategoryTheory.Functor.OfSequence
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Positive and negative canaries for indexed operational GSLTs

The positive fixture is a genuine two-stage growth map.  A source computation
can run before or after transport, producing the carried naturality square and
the generated OSLF exact-target judgment.

The negative fixture retains equation and forward-step preservation but adds
one target escape from an image state.  No covered operational translation can
use that carrier map.  A second negative witness shows that an observer which
merely reports the stage cannot be natural under the growth map.
-/

namespace Mettapedia.GSLT.IndexedOperational.Canary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational

private def systemOf (Term : Type) (Step : Term → Term → Prop) : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

private inductive SourceState where
  | ready
  | done
  deriving DecidableEq

private inductive SourceStep : SourceState → SourceState → Prop where
  | finish : SourceStep .ready .done

private def sourceTheory : GSLT := systemOf SourceState SourceStep

private inductive TargetState where
  | image (state : SourceState)
  | unrelated
  deriving DecidableEq

private def embed : SourceState → TargetState := .image

private inductive TargetStep : TargetState → TargetState → Prop where
  | image {source target : SourceState} : SourceStep source target →
      TargetStep (.image source) (.image target)

private def targetTheory : GSLT := systemOf TargetState TargetStep

private def sourceTargetTranslation :
    CoveredTranslation sourceTheory targetTheory where
  mapTerm := embed
  mapEquiv := by
    intro left right equal
    cases equal
    rfl
  cover :=
    { mapStep := fun step => .image step
      liftStep := by
        intro source target step
        cases step with
        | image sourceStep => exact ⟨_, sourceStep, rfl⟩ }

/-! ## A two-stage sequence -/

private def stageTheory : Nat → OperationalTheory
  | 0 => ⟨sourceTheory⟩
  | _ + 1 => ⟨targetTheory⟩

private def stageArrow : ∀ stage : Nat,
    stageTheory stage ⟶ stageTheory (stage + 1)
  | 0 => sourceTargetTranslation.toOperational
  | _ + 1 => OperationalTranslation.id targetTheory

private def diagram : Diagram Nat :=
  CategoryTheory.Functor.ofSequence stageArrow

private def firstGrowth : (0 : Nat) ⟶ 1 :=
  CategoryTheory.homOfLE (by omega)

private abbrev sourceReady : SemanticTerm sourceTheory :=
  Quotient.mk sourceTheory.equations SourceState.ready

private abbrev sourceDone : SemanticTerm sourceTheory :=
  Quotient.mk sourceTheory.equations SourceState.done

private abbrev targetReady : SemanticTerm targetTheory :=
  Quotient.mk targetTheory.equations (TargetState.image .ready)

private abbrev targetDone : SemanticTerm targetTheory :=
  Quotient.mk targetTheory.equations (TargetState.image .done)

private theorem firstGrowth_map : diagram.map firstGrowth =
    sourceTargetTranslation.toOperational := by
  exact CategoryTheory.Functor.ofSequence_map_homOfLE_succ stageArrow 0

@[simp] private theorem transport_ready :
    transportTerm diagram firstGrowth sourceReady = targetReady := by
  change (diagram.map firstGrowth).mapSemantic sourceReady = targetReady
  rw [firstGrowth_map]
  rfl

@[simp] private theorem transport_done :
    transportTerm diagram firstGrowth sourceDone = targetDone := by
  change (diagram.map firstGrowth).mapSemantic sourceDone = targetDone
  rw [firstGrowth_map]
  rfl

private def sourceSemanticStep :
    SemanticStep sourceTheory sourceReady sourceDone :=
  semanticStep_mk SourceStep.finish

/-- Positive: the two execution orders around the first genuine stage growth
form a filled, proof-relevant naturality diamond. -/
def firstGrowthDiamond :
    FilledDiamond (Command.Step diagram) (Command.TransportCell diagram)
      (.via firstGrowth sourceReady) (.via firstGrowth sourceDone)
      (.at 1 targetReady) := by
  simpa using Command.naturalityDiamond diagram firstGrowth sourceSemanticStep

/-- Both sides of the naturality square contain exactly the source-fibre
computation and the stage transport, in opposite orders. -/
theorem firstGrowth_routes_have_equal_length :
    (Command.reduceBeforeRoute diagram firstGrowth sourceSemanticStep).length =
      (Command.transportBeforeRoute diagram firstGrowth
        sourceSemanticStep).length := by
  rfl

/-- Positive: OSLF automatically recognizes the explicit stage crossing as
an inhabitant of its exact-target native type. -/
theorem firstGrowth_has_generated_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (Command.commandGSLT diagram)).satisfies
      (.via firstGrowth sourceReady)
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
        (Command.commandGSLT diagram) (.at 1 targetReady)).pred := by
  have generated := Command.applyVia_satisfies_nativeType
    diagram firstGrowth sourceReady
  rw [transport_ready] at generated
  exact generated

/-! ## Negative coverage and observation witnesses -/

private inductive EscapingStep : TargetState → TargetState → Prop where
  | image {source target : SourceState} : SourceStep source target →
      EscapingStep (.image source) (.image target)
  | escape : EscapingStep (.image .ready) .unrelated

private def escapingTheory : GSLT := systemOf TargetState EscapingStep

private def escapingForwardTranslation :
    OperationalTranslation sourceTheory escapingTheory where
  mapTerm := embed
  mapEquiv := by
    intro left right equal
    cases equal
    rfl
  mapStep := fun step => .image step

/-- Negative: equation preservation and forward-step preservation do not
manufacture local coverage.  The target escape has no source preimage. -/
theorem forward_translation_does_not_give_covered_translation :
    Nonempty (OperationalTranslation sourceTheory escapingTheory) ∧
    ¬ ∃ translation : CoveredTranslation sourceTheory escapingTheory,
      translation.mapTerm = embed := by
  refine ⟨⟨escapingForwardTranslation⟩, ?_⟩
  rintro ⟨translation, mapTermEq⟩
  have escapeStep : escapingTheory.Step
      (translation.mapTerm SourceState.ready) TargetState.unrelated := by
    rw [mapTermEq]
    exact EscapingStep.escape
  obtain ⟨sourceTarget, sourceStep, targetEq⟩ :=
    translation.cover.liftStep escapeStep
  cases sourceStep
  have mappedDone : translation.mapTerm SourceState.done =
      TargetState.image SourceState.done := by
    simpa [embed] using congrFun mapTermEq SourceState.done
  rw [mappedDone] at targetEq
  cases targetEq

/-- A natural observer cannot report only which side of a genuine stage
transport it is on: the transported state must retain the declared
observation. -/
theorem no_stage_tag_transport_observer
    (observer : Command.TransportObserver diagram)
    (tag : observer.Result → Bool)
    (sourceTag : tag (observer.observe 0 sourceReady) = false)
    (targetTag : tag (observer.observe 1 targetReady) = true) : False := by
  have natural := observer.natural firstGrowth sourceReady
  have tagged := congrArg tag natural
  rw [transport_ready, targetTag, sourceTag] at tagged
  cases tagged

#print axioms firstGrowth_routes_have_equal_length
#print axioms firstGrowth_has_generated_native_type
#print axioms forward_translation_does_not_give_covered_translation
#print axioms no_stage_tag_transport_observer

end Mettapedia.GSLT.IndexedOperational.Canary
