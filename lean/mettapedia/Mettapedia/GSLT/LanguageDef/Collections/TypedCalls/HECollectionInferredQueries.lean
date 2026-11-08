import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionTypeReadApplications
import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission

/-! Reached operator and argument queries for the collection program.
The relation is bound to its actual source space. An undeclared range call
is admitted through Undefined; its eventual numeric answers are not used
as a fictitious type-query result. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionInferredQueries

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open NativeTypeCallGraph NativeTypeSourcePorts
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)
open HECollectionTypeReadPrimitives (source)

def inferredRead (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (scope : List String) : TypeLookupRel := fun bindings subject expected types =>
  ∃ supply : Supply, ∃ depth : Nat,
    (∀ name ∈ invocationTypeScope scope [] subject expected bindings, name ∈ supply.used) ∧
    (NativeTypeScopedReads.evaluate ops source world depth (.infer true subject) supply).1 = some (.types types)

def lookup (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView) : CastLookup :=
  fun scope space bindings subject expected types =>
    space = HECollectionSpaceExtension.space ∧ inferredRead ops world scope bindings subject expected types

def currentOps (world : ExternalView) (active : String → Bool) (primitive : TypeNormalizationScope.Primitive)
    (subtypes : List Atom → List Atom) : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom :=
  TypeScopeMatcher.currentOps world (InertTypeDependencies.normalize active (TypeNormalizationScope.observed world primitive)) subtypes

theorem number_query (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (value : Int) (expected : Atom) :
    lookup ops world scope HECollectionSpaceExtension.space before.bindings (.grounded (.int value)) expected [.symbol "Number"] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.grounded (.int value)) expected before.bindings, 0⟩
  exact ⟨rfl, supply, 1, fun _ member => member,
    congrArg Prod.fst (HERangeTypeReadPrimitives.number_read ops source world 0 value supply)⟩

theorem boolean_query (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (value : Bool) (expected : Atom) :
    lookup ops world scope HECollectionSpaceExtension.space before.bindings (.grounded (.bool value)) expected [.symbol "Bool"] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.grounded (.bool value)) expected before.bindings, 0⟩
  exact ⟨rfl, supply, 1, fun _ member => member,
    congrArg Prod.fst (HERangeTypeReadPrimitives.boolean_read ops source world 0 value supply)⟩

theorem closed_head (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (name : String) (type expected : Atom)
    (declared : getAnnotatedTypes HECollectionSpaceExtension.space (.symbol name) = [type])
    (closed : atomVariables type = []) :
    lookup ops world scope HECollectionSpaceExtension.space before.bindings (.symbol name) expected [type] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.symbol name) expected before.bindings, 0⟩
  refine ⟨rfl, supply, 1, fun _ member => member, ?_⟩
  exact HECollectionTypeReadPrimitives.closed_symbol ops world 0 supply name type
    ((HECollectionTypeReadPrimitives.declarations_eq world _).trans declared) closed

theorem undefined_head (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (name : String) (expected : Atom)
    (absent : getAnnotatedTypes HECollectionSpaceExtension.space (.symbol name) = []) :
    lookup ops world scope HECollectionSpaceExtension.space before.bindings (.symbol name) expected [ops.undefined] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.symbol name) expected before.bindings, 0⟩
  exact ⟨rfl, supply, 1, fun _ member => member, congrArg Prod.fst
    (HECollectionTypeReadPrimitives.undeclared_symbol ops world 0 supply name
      ((HECollectionTypeReadPrimitives.declarations_eq world _).trans absent))⟩

theorem if_query (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (expected : Atom) :
    ∃ name, lookup ops world scope HECollectionSpaceExtension.space before.bindings (.symbol "if") expected
      [(HEIfSourceSelection.signature name).functionType] ∧
      name ∉ invocationTypeScope scope [] (.symbol "if") expected before.bindings := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.symbol "if") expected before.bindings, 0⟩
  obtain ⟨name, completed, fresh⟩ := HECollectionTypeReadApplications.if_head_type ops world 0 supply
  exact ⟨name, ⟨rfl, supply, 1, fun _ member => member, completed⟩, fresh⟩

theorem comparison_query (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (scope : List String) (before : Frame) (lower upper : Int) (expected : Atom) :
    lookup (currentOps world active primitive subtypes) world scope HECollectionSpaceExtension.space before.bindings
      (HEIfSourceSelection.Range.condition lower upper) expected [.symbol "Bool"] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (HEIfSourceSelection.Range.condition lower upper) expected before.bindings, 0⟩
  refine ⟨rfl, supply, 2, fun _ member => member, ?_⟩
  change (NativeTypeScopedReads.evaluate
    { HERangeTypeReadApplications.ops world active primitive subtypes with
      annotationPolicy := .supplement (fun left right => RetainedTypePayloads.observe world left == RetainedTypePayloads.observe world right) }
    source world 2 (.infer true (HEIfSourceSelection.Range.condition lower upper)) supply).1 = _
  rw [HECollectionTypeReadApplications.current_policy_agrees]
  simpa only [HEIfSourceSelection.Range.condition, HEFreshEquationFrames.Range.number] using
    HECollectionTypeReadApplications.comparison_type world active primitive subtypes 0 supply lower upper

theorem range_query (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (lower upper : Int) (expected : Atom) :
    lookup ops world scope HECollectionSpaceExtension.space before.bindings
      (.expression [.symbol "range", .grounded (.int lower), .grounded (.int upper)]) expected [ops.undefined] := by
  let subject := Atom.expression [.symbol "range", .grounded (.int lower), .grounded (.int upper)]
  let supply : Supply := ⟨invocationTypeScope scope [] subject expected before.bindings, 0⟩
  exact ⟨rfl, supply, 2, fun _ member => member, HECollectionTypeReadApplications.range_type ops world 0 supply lower upper⟩

theorem wrong_space_refused (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (space : Space) (different : space ≠ HECollectionSpaceExtension.space)
    (bindings : Bindings) (subject expected : Atom) (types : List Atom) :
    ¬lookup ops world scope space bindings subject expected types := fun supplied => different supplied.1

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionInferredQueries
