import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.CheckedRowsNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Controls.CheckedCalls

/-!
# The dependent append example through the actual compiled public query

The development is evaluated by the real compiler. Its native public query
uses the existing tagged-tuple node implementation and explicit discipline.
Append reaches its declared answer; a shorter answer is excluded by the
joined theorem, not by a post-processing filter.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CheckedRowsControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open NativeTypesOnTheStep.Computing.DirectedAnswers
open TelescopeAbstraction (applyClosed)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (two twoThree single)
open SourceLanguage SourceLanguage.Elaboration

def built : Compiled addAppendDev := (compile addAppendDev).get (by decide +kernel)

theorem native_rows : built.nativeRows = addAppendRows :=
  Option.some.inj (built.native.symm.trans addAppend_rules)

def supply (index : Nat) : MClosed := nodeC "space" [encodeNat index]

abbrev appendCall : Tower.Tm 0 := applyClosed appendRDef.telescope groundSub (.const appendName)

theorem append_answer_iff (value : Tower.Tm 0) :
    NativeExecution.Answer built untyped.discipline Hosting.mettaNodes appendCall value ↔
      CheckedCalls.NativeAnswer appendR_checked groundSub_typed value := by
  have reach := append_rowsReach
  rw [← native_rows] at reach
  exact CheckedRowsNative.answer_iff_qualified built untyped.discipline Hosting.mettaNodes supply
    addAppend_devCheck appendR_checked reach groundSub_typed
      (appendR_result_data groundSub_typed .num) value

theorem append_reaches_expected :
    NativeExecution.Answer built untyped.discipline Hosting.mettaNodes appendCall twoThree :=
  (append_answer_iff twoThree).mpr Controls.CheckedCalls.append_native_answer

theorem shorter_answer_is_impossible :
    ¬ NativeExecution.Answer built untyped.discipline Hosting.mettaNodes appendCall (single two) := by
  intro answered
  exact Controls.CheckedCalls.shorter_native_answer_refused ((append_answer_iff _).mp answered)

theorem result_keeps_dependent_type :
    Typed ProgrammingOnTheStep.IndexedFamilies.Eliminator.pkg .nil twoThree
      (subst groundSub appendRDef.result) :=
  CheckedCalls.native_answer_keeps_type appendR_checked groundSub_typed
    ((append_answer_iff _).mp append_reaches_expected)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CheckedRowsControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CheckedRowsControls.append_reaches_expected
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CheckedRowsControls.shorter_answer_is_impossible
