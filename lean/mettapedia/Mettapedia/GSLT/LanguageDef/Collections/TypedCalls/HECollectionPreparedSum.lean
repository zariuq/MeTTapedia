import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericFold
import Mettapedia.Machines.PrivateScalarCompletion
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RecognizedFolds

/-!
# A private checked-sum attempt refines the authored HE fold region

The target is the existing private scalar-fold machine, instantiated with
checked signed addition. Its local callback law is derived from arithmetic;
the adapter also earns the actual HE arithmetic and function executions.
Late refusal may restart from the original pure region. Interruption remains
distinct and does not authorize replay or a successful source answer.

This is a semantic instance, not a C recognizer, Int64 ABI, snapshot layout,
instruction-cost or fuel-accounting theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedSum

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number numbers)
open Mettapedia.Machines

def sourceStep : FoldNativeCompletion.Step Int Int World := fun world accumulator item =>
  (world, .ok (accumulator + item))

def checkedStep (accumulator item : Int) : Option Int :=
  if RecognizedFolds.I64 (accumulator + item) then some (accumulator + item) else none

theorem step_refines (world : World) : PrivateScalarFold.StepRefines sourceStep checkedStep world := by
  intro accumulator item next accepted
  unfold checkedStep at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

theorem checked_step_exact (accumulator item next : Int) :
    checkedStep accumulator item = some next ↔
      next = accumulator + item ∧ RecognizedFolds.I64 next := by
  simp only [checkedStep]
  by_cases fits : RecognizedFolds.I64 (accumulator + item)
  · simp only [if_pos fits, Option.some.injEq]
    constructor
    · intro same
      subst next
      exact ⟨rfl, fits⟩
    · exact fun same => same.1.symm
  · simp [fits]
    intro same
    simpa only [same] using fits

theorem source_fold (world : World) (values : List Int) (init : Int) :
    FoldNativeCompletion.produce sourceStep values world init = (world, .ok (values.foldl (· + ·) init)) := by
  induction values generalizing init with
  | nil => rfl
  | cons item rest ih => simpa only [FoldNativeCompletion.produce, sourceStep, List.foldl_cons] using ih (init + item)

theorem uncancelled_result (cancel : Nat → Bool) (values : List Int) (world : World) (init : Int)
    (clear : ∀ offset < values.length, cancel offset = false) :
    PrivateScalarFold.dispatch sourceStep checkedStep cancel values world init =
      .completed world (.ok (values.foldl (· + ·) init)) := by
  simpa only [source_fold] using PrivateScalarCompletion.uncancelled_dispatch_exact
    sourceStep checkedStep cancel values world init (step_refines world) clear

theorem accepted_value (world : World) (cancel : Nat → Bool) (index : Nat)
    (values : List Int) (init result : Int)
    (accepted : PrivateScalarFold.attempt checkedStep cancel index values init = .value result) :
    result = values.foldl (· + ·) init := by
  have equality := PrivateScalarFold.accepted_fold_refines sourceStep checkedStep cancel world (step_refines world) index values init result accepted
  rw [source_fold] at equality
  exact (Except.ok.inj (congrArg Prod.snd equality)).symm

theorem completed_value (cancel : Nat → Bool) (values : List Int) (world afterWorld : World)
    (init : Int) (reply : Except Int Int)
    (completed : PrivateScalarFold.dispatch sourceStep checkedStep cancel values world init = .completed afterWorld reply) :
    afterWorld = world ∧ reply = .ok (values.foldl (· + ·) init) := by
  have equality := PrivateScalarFold.completed_exact sourceStep checkedStep cancel values world init
    (step_refines world) afterWorld reply completed
  rw [source_fold] at equality
  exact ⟨(congrArg Prod.fst equality).symm, (congrArg Prod.snd equality).symm⟩

theorem uncancelled_completed_iff (cancel : Nat → Bool) (values : List Int) (world afterWorld : World)
    (init : Int) (reply : Except Int Int) (clear : ∀ offset < values.length, cancel offset = false) :
    PrivateScalarFold.dispatch sourceStep checkedStep cancel values world init = .completed afterWorld reply ↔
      afterWorld = world ∧ reply = .ok (values.foldl (· + ·) init) := by
  constructor
  · exact completed_value cancel values world afterWorld init reply
  · rintro ⟨rfl, rfl⟩
    exact uncancelled_result cancel values _ init clear

theorem refusal_falls_back_without_wrapping (cancel : Nat → Bool) (values : List Int) (world : World) (init : Int)
    (refused : PrivateScalarFold.attempt checkedStep cancel 0 values init = .refused) :
    PrivateScalarFold.dispatch sourceStep checkedStep cancel values world init =
      .completed world (.ok (values.foldl (· + ·) init)) := by
  rw [PrivateScalarFold.refusal_restarts_original sourceStep checkedStep cancel values world init refused, source_fold]

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem source_step_is_actual_arithmetic (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (accumulator item next : Int)
    (accepted : checkedStep accumulator item = some next) :
    Stateful.AtomRel current sourceSpace world live scope
      (HEBinaryNumericSource.addition.call accumulator item) Atom.undefinedType before [(number next, before)] world (policy := policy) := by
  have same := ((checked_step_exact accumulator item next).mp accepted).1
  subst next
  exact HECollectionArithmetic.addition_source minimal nativePolicy external active primitive subtypes world policy before live scope accumulator item

theorem accepted_source_function (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right spaceName : String)
    (different : left ≠ right) (leftSpace : left ≠ spaceName) (rightSpace : right ≠ spaceName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right)
    (values : List Int) (init result : Int) (itemsMark : Entry.Status) (cancel : Nat → Bool) (index : Nat)
    (accepted : PrivateScalarFold.attempt checkedStep cancel index values init = .value result) :
    Stateful.MinimalRel current sourceSpace world live scope caller
      (HECollectionFoldFunction.function (numbers values) (number init) left right spaceName .active
        (operatorName := "+") (itemsMark := itemsMark)) before [(number result, before)] world (policy := policy) := by
  rw [accepted_value world cancel index values init result accepted]
  exact HECollectionNumericFold.function_source minimal nativePolicy external active primitive subtypes world policy before left right spaceName
    different leftSpace rightSpace leftFixed rightFixed values init live scope caller itemsMark

theorem completed_source_function (world afterWorld : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right spaceName : String)
    (different : left ≠ right) (leftSpace : left ≠ spaceName) (rightSpace : right ≠ spaceName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right)
    (values : List Int) (init result : Int) (itemsMark : Entry.Status) (cancel : Nat → Bool)
    (completed : PrivateScalarFold.dispatch sourceStep checkedStep cancel values world init = .completed afterWorld (.ok result)) :
    Stateful.MinimalRel current sourceSpace world live scope caller
      (HECollectionFoldFunction.function (numbers values) (number init) left right spaceName .active
        (operatorName := "+") (itemsMark := itemsMark)) before [(number result, before)] afterWorld (policy := policy) := by
  obtain ⟨worldEq, same⟩ := completed_value cancel values world afterWorld init (.ok result) completed
  rw [worldEq, Except.ok.inj same]
  exact HECollectionNumericFold.function_source minimal nativePolicy external active primitive subtypes world policy before left right spaceName
    different leftSpace rightSpace leftFixed rightFixed values init live scope caller itemsMark

theorem completed_retained_region (world afterWorld : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right spaceName : String)
    (different : left ≠ right) (leftSpace : left ≠ spaceName) (rightSpace : right ≠ spaceName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right)
    (values : List Int) (init result : Int) (itemsMark : Entry.Status) (cancel : Nat → Bool)
    (completed : PrivateScalarFold.dispatch sourceStep checkedStep cancel values world init = .completed afterWorld (.ok result))
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    RecursiveMachine.Contextual.WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.minimal live scope caller
        (HECollectionFoldFunction.function (numbers values) (number init) left right spaceName .active
          (operatorName := "+") (itemsMark := itemsMark)) before), stack, emitted⟩
      ⟨afterWorld, sourceSpace, .returning [(number result, before)], stack, emitted⟩ (admission := (current).arguments) := by
  have executed := completed_source_function minimal nativePolicy external active primitive subtypes world afterWorld policy before live scope caller
    left right spaceName different leftSpace rightSpace leftFixed rightFixed values init result itemsMark cancel completed
  exact RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.minimal_complete executed stack) emitted

theorem uncancelled_retained_region (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right spaceName : String)
    (different : left ≠ right) (leftSpace : left ≠ spaceName) (rightSpace : right ≠ spaceName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right)
    (values : List Int) (init : Int) (itemsMark : Entry.Status) (cancel : Nat → Bool)
    (clear : ∀ offset < values.length, cancel offset = false)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    RecursiveMachine.Contextual.WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.minimal live scope caller
        (HECollectionFoldFunction.function (numbers values) (number init) left right spaceName .active
          (operatorName := "+") (itemsMark := itemsMark)) before), stack, emitted⟩
      ⟨world, sourceSpace, .returning [(number (values.foldl (· + ·) init), before)], stack, emitted⟩ (admission := (current).arguments) :=
  completed_retained_region minimal nativePolicy external active primitive subtypes world world policy before live scope caller
    left right spaceName different leftSpace rightSpace leftFixed rightFixed values init _ itemsMark cancel
      (uncancelled_result cancel values world init clear) stack emitted

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionPreparedSum
