import Mettapedia.Languages.Metamath.InferenceAssertionResultFrame

/-!
# Stack-invariant preservation for generated Metamath assertion steps

This module supplies the direct induction-step invariant for recursive source
proofs.  Shrinking a frame-respecting stack preserves the invariant, and an
independently justified generated assertion result can then be pushed without
violating it.

No runtime transition or successful checker result is assumed.
-/

namespace Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceAssertionResultFrame
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Generic stack operations -/

/-- Taking an initial array segment cannot introduce a formula that violates
the frame respected by the original stack. -/
theorem stackRespectsFrame_shrink
    (db : RuntimeDB) (frame : RuntimeFrame)
    (stack : Array RuntimeFormula) (size : Nat)
    (hstack : Metamath.Kernel.StackRespectsFrame db frame stack) :
    Metamath.Kernel.StackRespectsFrame db frame (stack.shrink size) := by
  intro index hindex
  have hindexOriginal : index < stack.size := by
    have hsize := Array.size_shrink (xs := stack) (i := size)
    omega
  have hget : (stack.shrink size)[index]! = stack[index]! := by
    have hshrink :
        (stack.shrink size)[index]! =
          (stack.shrink size)[index]'hindex :=
      getElem!_pos (stack.shrink size) index hindex
    have horiginal : stack[index]! = stack[index]'hindexOriginal :=
      getElem!_pos stack index hindexOriginal
    rw [hshrink, horiginal]
    exact Array.getElem_shrink hindex
  rw [hget]
  exact hstack index hindexOriginal

/-- Conversely, pushing a formula known to violate the frame necessarily
breaks the stack invariant, even when the existing prefix is valid. -/
theorem not_stackRespectsFrame_push_of_result_false
    (db : RuntimeDB) (frame : RuntimeFrame)
    (stack : Array RuntimeFormula) (result : RuntimeFormula)
    (hresult : db.formulaSymsRespectFrame result frame = false) :
    ¬ Metamath.Kernel.StackRespectsFrame db frame (stack.push result) := by
  intro hstack
  have hnew := hstack stack.size (by simp)
  rw [Metamath.Kernel.Array.getElem!_push_eq] at hnew
  rw [hresult] at hnew
  contradiction

/-! ## Canonical assertion update -/

/-- Independent assertion semantics preserves `StackRespectsFrame` across the
canonical shrink-and-push update used by the live verifier.  Result respect is
derived by `InferenceAssertionResultFrame`, not assumed here. -/
theorem assertionApplicationSemantics_stackResult_respects_callerFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView) (stack : Array RuntimeFormula)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result)
    (hwindow :
      stack.extract (stack.size - assertion.frame.hyps.size) stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame stack) :
    Metamath.Kernel.StackRespectsFrame db db.frame
      ((stack.shrink (stack.size - assertion.frame.hyps.size)).push
        result.toRuntime) := by
  have hprefix := stackRespectsFrame_shrink db db.frame stack
    (stack.size - assertion.frame.hyps.size) hstackRespects
  have hresult :=
    assertionApplicationSemantics_result_respects_callerFrame
      db projection assertion stack actuals result hproject hmember
        hsemantics hwindow hstackRespects
  exact Metamath.Kernel.stackRespectsFrame_push
    db db.frame
      (stack.shrink (stack.size - assertion.frame.hyps.size))
      result.toRuntime hprefix hresult

/-- The same canonical update invariant follows from proof-relevant generated
assertion evidence, still without executing the runtime checker. -/
theorem generatedAssertionNode_stackResult_respects_callerFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (assertion : AssertionView) (stack : Array RuntimeFormula)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hnode : Nonempty
      (Σ substitution : FiniteSubstitution,
        GeneratedAssertionNode projection target assertion actuals result
          substitution))
    (hwindow :
      stack.extract (stack.size - assertion.frame.hyps.size) stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame stack) :
    Metamath.Kernel.StackRespectsFrame db db.frame
      ((stack.shrink (stack.size - assertion.frame.hyps.size)).push
        result.toRuntime) := by
  have hsemantics :
      AssertionApplicationSemantics projection.callerFrame assertion
        actuals result :=
    (generatedAssertionNode_nonempty_iff_semantics projection target
      hprojection hmember actuals result).mp hnode
  exact assertionApplicationSemantics_stackResult_respects_callerFrame
    db projection assertion stack actuals result hproject hmember
      hsemantics hwindow hstackRespects

/-! ## Boundaries -/

/-- Positive boundary: every shrink of a valid stack remains valid. -/
example (db : RuntimeDB) (frame : RuntimeFrame)
    (stack : Array RuntimeFormula)
    (hstack : Metamath.Kernel.StackRespectsFrame db frame stack) :
    Metamath.Kernel.StackRespectsFrame db frame
      (stack.shrink (stack.size + 7)) :=
  stackRespectsFrame_shrink db frame stack (stack.size + 7) hstack

/-- Negative boundary: prefix validity alone cannot justify an unchecked
result push. -/
example (db : RuntimeDB) (frame : RuntimeFrame)
    (stack : Array RuntimeFormula) (result : RuntimeFormula)
    (_hstack : Metamath.Kernel.StackRespectsFrame db frame stack)
    (hresult : db.formulaSymsRespectFrame result frame = false) :
    ¬ Metamath.Kernel.StackRespectsFrame db frame (stack.push result) :=
  not_stackRespectsFrame_push_of_result_false
    db frame stack result hresult

end Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant
