import Mettapedia.OSLF.Syntax.IntrinsicScopedRhoClassifiedInstance
import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison

/-!
# Authored rho execution through the same classified interpretation

The established well-sorted payload translation connects the actual COMM,
ParCong and book Drop executor to the interpreted generic reduction.
Reflection keeps its necessary structural-congruence and target-class
qualification; it is not a bijection of executor histories.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedRhoExecutorClassifiedInstance

open RhoPayloadPresentation
open IntrinsicScopedRhoClassifiedInstance
open IntrinsicScopedAuthoredClassifiedReduction (ExtendedReduction)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.OSLF.Binding.RhoSchema.Authored

/-- Every actual well-sorted strict executor step is classified at its translated program classes. -/
theorem strict_simulation {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoStep source target) {initial : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) source = some initial) :
    ∃ final, tProc (Env.empty []) target = some final ∧
      ExtendedReduction strictLocalRules equations initial final := by
  obtain ⟨final, reads, fires⟩ := rhoStep_simulation sourceTyped step translated
  exact ⟨final, reads, (extension_iff_steps _ _ _).mpr fires⟩

/-- The same classification covers the authored book executor with its actual Drop rule. -/
theorem book_simulation {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoCombinedInterpretedStep.RhoStepWithDrop source target)
    {initial : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) source = some initial) :
    ∃ final, tProc (Env.empty []) target = some final ∧
      ExtendedReduction bookLocalRules equations initial final := by
  obtain ⟨final, reads, fires⟩ := rhoStepWithDrop_simulation sourceTyped step translated
  exact ⟨final, reads, (extension_iff_steps _ _ _).mpr fires⟩

/-- An interpreted strict step from an admitted closed source reflects to
actual execution after structural rearrangement, with the same target class. -/
theorem strict_reflection {free : FreeSortContext} {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    {initial : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) source = some initial)
    {final : Term sig [] Srt.pr}
    (step : ExtendedReduction strictLocalRules equations initial final) :
    ∃ rearranged target, StructuralCongruence source rearranged ∧
      RhoStep rearranged target ∧
        ∃ output, tProc (Env.empty []) target = some output ∧ cls output = cls final :=
  RhoPayloadPresentation.strict_reflection typed translated
    ((extension_iff_steps _ _ _).mp step)

/-- Book reflection retains exactly the established authored-source admission boundary. -/
theorem book_reflection {free : FreeSortContext} {source : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    {initial : Term sig [] Srt.pr}
    (translated : tProc (Env.empty []) source = some initial)
    {final : Term sig [] Srt.pr}
    (step : ExtendedReduction bookLocalRules equations initial final) :
    ∃ rearranged target, StructuralCongruence source rearranged ∧
      RhoCombinedInterpretedStep.RhoStepWithDrop rearranged target ∧
        ∃ output, tProc (Env.empty []) target = some output ∧ cls output = cls final :=
  RhoPayloadPresentation.book_reflection typed translated
    ((extension_iff_steps _ _ _).mp step)

end Mettapedia.OSLF.Binding.IntrinsicScopedRhoExecutorClassifiedInstance
