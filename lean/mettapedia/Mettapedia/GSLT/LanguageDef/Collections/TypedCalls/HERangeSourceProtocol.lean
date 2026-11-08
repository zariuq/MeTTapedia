import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSuperposeSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeEquationFrontiers

/-!
# Local source ports for the authored range induction

The recursive range result and the conditional body are not ports. The
interface contains only literal reads, addition, conditional activation
(head and arguments, before its equation body), and superpose composition
from independently earned per-item source derivations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProtocol

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open HERangeSourceProgram (space)
open HERangeSuperposeSource (NumericOrEmpty)

structure Ports where
  environment : WorldEnvironment Space Unit
  view : environment.view () space = space
  dispatch : environment.dispatch = HERangeSourceProgram.dispatch
  undefinedHead : ∀ (names : List String) (before : Frame) (name : String),
    name = "range" ∨ name = "empty" →
    environment.lookup names space before.bindings (.symbol name) Atom.undefinedType [Atom.undefinedType]
  number : ∀ (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (value : Int),
    Stateful.AtomRel environment space () live scope (.grounded (.int value)) Atom.undefinedType before
      [(.grounded (.int value), before)] () (policy := policy)
  addition : ∀ (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (left right : Int),
    Stateful.AtomRel environment space () live scope (HEBinaryNumericSource.addition.call left right) Atom.undefinedType before
      [(.grounded (.int (left + right)), before)] () (policy := policy)
  conditional : ∀ (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom),
    expected = .symbol "Number" ∨ expected = Atom.undefinedType →
    ∃ name selected after,
      environment.arguments.selection space environment.lookup policy live scope
        (HEFreshEquationFrames.Range.bodyAt (HEFreshEquationFrames.Range.number lower) (HEFreshEquationFrames.Range.number upper))
        (.symbol "if") expected before (.selected (HEIfSourceSelection.signature name) [selected]) ∧
      Stateful.FunctionRel environment space ()
        (invocationReturnType (HEIfSourceSelection.signature name) :: live) scope expected (HEIfSourceSelection.signature name)
        (.symbol "if") (HEIfSourceActivation.operands lower upper) selected
        [(HEIfSourceActivation.reachedCall lower upper, after)] () (policy := policy)
  superpose : ∀ (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (outputs : List (List Result)) (expected : Atom),
    expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
    TypeSubst.typeVarsList (items.map Entry.Value.erase) = [] → items ≠ [] →
    List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel environment space () live scope item Atom.undefinedType before rows () (policy := policy)) items outputs →
    (∀ row ∈ outputs.flatten, NumericOrEmpty row.1) →
    Stateful.AtomRel environment space () live scope (HERangeSuperposeSource.call items) expected before outputs.flatten ()
      (policy := policy)

def historical (minimal : Minimal.Services) : Ports where
  environment := HERangeSourceProgram.environment minimal
  view := rfl
  dispatch := rfl
  undefinedHead names before name member := by
    apply HEIfSourceSelection.unknown_lookup
    rcases member with rfl | rfl <;> rfl
  number := HERangeSuperposeSource.number_undefined minimal
  addition := HERangeSourceProgram.plus_source minimal
  conditional := HERangeConditionalActivation.source_activation minimal
  superpose := HERangeSuperposeSource.source minimal

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProtocol
