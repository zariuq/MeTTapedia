import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualArithmeticSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeFrame
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshEquationFrames
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEBinaryNumericSource

/-!
# Source applicability of the schematic standard conditional

The condition and both held branches are queried as authored syntax before
any value is delivered. A fresh result variable is constrained by the caller's
Number demand, producing an actual selected frame with its old aliases intact.
This is the application boundary, not a proof of the conditional body run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

def signature (name : String) : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [.symbol "Bool", Atom.atomType, Atom.atomType] (.var name),
    [.symbol "Bool", Atom.atomType, Atom.atomType], .var name, rfl⟩

def call (condition yes no : Atom) : Atom :=
  .expression [.symbol "if", condition, yes, no]

theorem signature_variant (names : List String) (name : String) (fresh : name ∉ names) :
    TypeCandidateAlphaVariantRel names (signature "t").functionType (signature name).functionType := by
  refine ⟨Equiv.swap "t" name, (Equiv.swap "t" name).injective, ?_, ?_⟩
  · simp [signature, CompletedDelivery.arrowType, Atom.atomType]
  · intro key present
    have same : key = "t" := by
      simpa [signature, CompletedDelivery.arrowType, TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.atomType]
        using present
    simpa [same] using fresh

theorem signature_lookup (space : Space) (names : List String) (before : Frame)
    (expected : Atom) (name : String)
    (declared : getAtomTypes space (.symbol "if") = [(signature "t").functionType])
    (fresh : name ∉ invocationTypeScope names [] (.symbol "if") expected before.bindings) :
    scopedLookup names space before.bindings (.symbol "if") expected [(signature name).functionType] :=
  ⟨[(signature "t").functionType], by
      simpa only [declared] using FirstSuccessSourceReplies.source_types space (.symbol "if"),
    .cons (signature_variant _ name fresh) (.nil _)⟩

theorem unknown_lookup (space : Space) (names : List String) (before : Frame)
    (subject expected : Atom) (unknown : getAtomTypes space subject = [Atom.undefinedType]) :
    scopedLookup names space before.bindings subject expected [Atom.undefinedType] :=
  ⟨[Atom.undefinedType], by simpa only [unknown] using FirstSuccessSourceReplies.source_types space subject,
    .cons ⟨id, Function.injective_id, by simp, by simp [Atom.undefinedType, TypeSubst.typeVars]⟩ (.nil _)⟩

theorem unknown_argument (space : Space) (names : List String) (policy : Policy) (before : Frame)
    (expression subject expected : Atom) (position : Nat)
    (unknown : getAtomTypes space subject = [Atom.undefinedType]) :
    ArgumentChecksRel space (scopedLookup names space) policy expression subject expected position
      [before] [before] [] := by
  have checked : TypeCheckRel policy expected before Atom.undefinedType (.inr before) :=
    .accepted (.unchanged (before.preserved_type_match policy (.undefinedRight _ _)))
  simpa [checkedFrames, checkedFailures] using
    (ArgumentChecksRel.cons (expression := expression) (position := position)
      (unknown_lookup space names before subject expected unknown) (.cons checked .nil) .nil)

/-- Actual source selection, including the private range constraint. The
static facts concern the three authored arguments, not their future values. -/
theorem selection (space : Space) (policy : Policy) (before : Frame) (live : List Atom)
    (scope : List String) (condition yes no : Atom) (name : String)
    (declared : getAtomTypes space (.symbol "if") = [(signature "t").functionType])
    (conditionUnknown : getAtomTypes space condition = [Atom.undefinedType])
    (yesUnknown : getAtomTypes space yes = [Atom.undefinedType])
    (noUnknown : getAtomTypes space no = [Atom.undefinedType])
    (fresh : name ∉ invocationTypeScope
      (invocationTypeScope scope live (call condition yes no) (.symbol "Number") before.bindings)
      [] (.symbol "if") (.symbol "Number") before.bindings) :
    ∃ after,
      InvocationSelectionRel space scopedLookup policy live scope (call condition yes no)
        (.symbol "if") (.symbol "Number") before (.selected (signature name) [after]) ∧
      after.bindings = HEFreshRangeFrame.extend before.bindings name (.symbol "Number") ∧
      ∀ readingPolicy, after.read readingPolicy (.var name) = .symbol "Number" := by
  let names := invocationTypeScope scope live (call condition yes no) (.symbol "Number") before.bindings
  have bindingFresh : name ∉ specBindingVars before.bindings := by
    intro present
    exact fresh (by simp [invocationTypeScope, present])
  obtain ⟨after, retained, renewed, observed⟩ :=
    HEFreshRangeFrame.number_range_frame policy before name bindingFresh
  have first := unknown_argument space names policy before (call condition yes no) condition
    (.symbol "Bool") 1 conditionUnknown
  have second := unknown_argument space names policy before (call condition yes no) yes Atom.atomType 2 yesUnknown
  have third := unknown_argument space names policy before (call condition yes no) no Atom.atomType 3 noUnknown
  have checked : ApplicationChecksRel space (scopedLookup names space) policy
      (call condition yes no) (.symbol "Number") (signature name) before [after] [] := by
    simpa [signature, checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (expression := call condition yes no) (expected := .symbol "Number")
        (selected := signature name) (before := before)
        (operator := .symbol "if") (arguments := [condition, yes, no]) rfl
        (.cons first (.cons second (.cons third .nil)))
        (.cons (TypeCheckRel.accepted renewed) .nil))
  exact ⟨after,
    ⟨[(signature name).functionType], signature_lookup space names before _ name declared fresh,
      .selected checked (by simp)⟩,
    retained, observed⟩

namespace Range

open HEFreshEquationFrames.Range (number bodyAt pattern body)

def condition (lower upper : Int) : Atom := .expression [.symbol ">=", number lower, number upper]
def yes : Atom := .expression [.symbol "empty"]
def no (lower upper : Int) : Atom :=
  .expression [.symbol "superpose", .expression [number lower,
    .expression [.symbol "range", .expression [.symbol "+", number lower, number 1], number upper]]]

/-- The source equations are retained alongside their signatures; the
application theorem does not replace either conditional branch by a value. -/
def space : Space := Space.ofList
  [.expression [.symbol ":", .symbol "if", (signature "t").functionType],
   .expression [.symbol ":", .symbol "+", HEBinaryNumericSource.addition.signature.functionType],
   .expression [.symbol ":", .symbol ">=", HEBinaryNumericSource.greaterEqual.signature.functionType],
   .expression [.symbol "=", pattern, body],
   .expression [.symbol "=", .expression [.symbol "if", .grounded (.bool true), .var "then", .var "else"], .var "then"],
   .expression [.symbol "=", .expression [.symbol "if", .grounded (.bool false), .var "then", .var "else"], .var "else"]]

theorem source_shape (lower upper : Int) :
    bodyAt (number lower) (number upper) = call (condition lower upper) yes (no lower upper) := rfl

theorem condition_unknown (lower upper : Int) :
    getAtomTypes space (condition lower upper) = [Atom.undefinedType] := rfl

theorem yes_unknown : getAtomTypes space yes = [Atom.undefinedType] := rfl

theorem no_unknown (lower upper : Int) :
    getAtomTypes space (no lower upper) = [Atom.undefinedType] := rfl

theorem if_declared : getAtomTypes space (.symbol "if") = [(signature "t").functionType] := rfl

/-- The actual ground range body earns its fresh schematic selection under
every certified caller frame, including frames with old variable aliases. -/
theorem source_selection (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) :
    ∃ name after,
      InvocationSelectionRel space scopedLookup policy live scope (bodyAt (number lower) (number upper))
        (.symbol "if") (.symbol "Number") before (.selected (signature name) [after]) ∧
      after.bindings = HEFreshRangeFrame.extend before.bindings name (.symbol "Number") ∧
      ∀ readingPolicy, after.read readingPolicy (.var name) = .symbol "Number" := by
  let avoid := invocationTypeScope
    (invocationTypeScope scope live (call (condition lower upper) yes (no lower upper)) (.symbol "Number") before.bindings)
    [] (.symbol "if") (.symbol "Number") before.bindings
  let name := instanceName avoid ["t"] 0 "t"
  have fresh : name ∉ avoid := instanceName_not_mem avoid ["t"] 0 "t"
  obtain ⟨after, selected, retained, read⟩ := selection space policy before live scope
    (condition lower upper) yes (no lower upper) name if_declared
    (condition_unknown lower upper) yes_unknown (no_unknown lower upper) fresh
  exact ⟨name, after, selected, retained, read⟩

/-- Adding an annotation to the raw condition changes applicability before
the comparison executes. Delivered Bool results cannot justify erasing it. -/
theorem raw_annotation_changes_applicability (lower upper : Int) :
    getAtomTypes (Space.ofList
      [.expression [.symbol ":", condition lower upper, .symbol "String"]])
      (condition lower upper) ≠ [Atom.undefinedType] := by
  simp [getAtomTypes, getAnnotatedTypes, Space.ofList, Atom.undefinedType, condition]

end Range

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection
