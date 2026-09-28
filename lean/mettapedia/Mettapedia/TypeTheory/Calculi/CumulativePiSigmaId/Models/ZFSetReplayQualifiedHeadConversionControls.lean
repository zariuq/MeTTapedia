import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedHeadConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplaySupportedLambdaControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayUniverseFormation

/-!
# Computed dependent argument across a checked universe-head conversion

The argument constructs a dependent pair and projects its first component.
Its structural certificate is qualified at one cumulative universe head. A
retained head-conversion step displays an extensionally equal but syntactically
different universe head. The actual set-universe interpretation validates that
step, so the converted argument still inhabits its displayed universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedHeadConversionControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayApplicationComparisonControls
  (context contextCode context_checked context_assembles valid)
open ZFSetReplaySupportedLambdaControls
  (computedArgument computedArgumentCode computed_argument_checked
    computed_argument_qualified)
open ZFSetTypeExpressionInterpretation (Environment)
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

local instance : DecidableRel Tower.rules.headEq := Tower.instDecidableHeadEq

abbrev SourceHead : Tower.Head := .sort (.succ Tower.zero)
abbrev TargetHead : Tower.Head :=
  .sort (.max Tower.zero (.succ Tower.zero))
abbrev SourceLevel : Tower.Head := .sort (.succ (.succ Tower.zero))
abbrev TargetLevel : Tower.Head :=
  .sort (.succ (.max Tower.zero (.succ Tower.zero)))
abbrev EmptyRoot (_ : Nat) := Empty

def noRootDecode {n : Nat} (impossible : EmptyRoot n) :
    Option (Tower.Tm n × Tower.Tm n) := nomatch impossible

theorem heads_related : Tower.HeadEq SourceHead TargetHead := by decide +kernel

theorem heads_syntactically_different : SourceHead ≠ TargetHead := by decide

private def divergentHeads : Tower.Head → ZFSet.{u} :=
  fun head => if head = SourceHead then ∅ else ZFSet.powerset ∅

/-- A checked head step by itself cannot constrain an arbitrary interpretation
of head symbols. This is why the positive theorem names head-equivalence
soundness as a model obligation. -/
theorem checked_step_arbitrary_heads_disagree :
    headStepCheck Tower.rules noRootDecode
      (.single (.head SourceHead TargetHead) :
        StructuralConversionCode.Code Tower.Head EmptyRoot 0)
      (.head SourceHead) (.head TargetHead) = true ∧
    (divergentHeads.{u} SourceHead : ZFSet.{u}) ≠
      divergentHeads.{u} TargetHead := by
  constructor
  · exact head_step_checked (n := 0) Tower.rules noRootDecode
      SourceHead TargetHead heads_related
  · have atSource : divergentHeads SourceHead = (∅ : ZFSet.{u}) := by
      simp [divergentHeads]
    have atTarget : divergentHeads TargetHead = (ZFSet.powerset ∅ : ZFSet.{u}) := by
      simp [divergentHeads, heads_syntactically_different.symm]
    rw [atSource, atTarget]
    intro equal
    have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
      ZFSet.mem_powerset.mpr (fun _ inside => inside)
    rw [← equal] at member
    exact ZFSet.notMem_empty _ member

/-- The computed projection retains an accepted converted tree and inhabits
the interpreted target universe on every context-valid environment. -/
theorem computed_argument_head_converted (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
    ∃ meaning : Meaning.{u} 1,
      check Tower.rules (headStepCheck Tower.rules noRootDecode) context
        computedArgument (.head TargetHead)
        (headConvertedCode (RootCode := EmptyRoot) computedArgumentCode
          SourceHead TargetHead TargetLevel) = true ∧
      assemble heads constants
        (headConvertedCode (RootCode := EmptyRoot) computedArgumentCode
          SourceHead TargetHead TargetLevel)
        computedArgument (.head TargetHead) = some meaning ∧
      ∀ env : Environment.{u} 1,
        valid h env → meaning.value env ∈ heads TargetHead := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨meaning, _, checked, assembled, membership⟩ :=
    qualified_head_conversion_membership Tower.rules noRootDecode heads constants
      (fun left right related =>
        ZFSetReplayUniverseFormation.headEq_values h ∅ (twoCode h).1
          (fun _ => 0) related)
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified
      (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants)
      context contextCode (valid h) context_checked (context_assembles h constants)
      computedArgument computedArgumentCode SourceHead TargetHead
      SourceLevel TargetLevel computed_argument_checked computed_argument_qualified
      (Tower.HeadTyping.sort _) (Tower.HeadTyping.sort _) (Tower.IsUniverse.sort _)
      heads_related
  exact ⟨meaning, checked, assembled, membership⟩

#print axioms heads_related
#print axioms heads_syntactically_different
#print axioms checked_step_arbitrary_heads_disagree
#print axioms computed_argument_head_converted

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedHeadConversionControls
