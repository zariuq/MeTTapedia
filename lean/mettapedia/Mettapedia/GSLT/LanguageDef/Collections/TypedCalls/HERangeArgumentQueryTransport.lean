import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadApplications

/-!
# Demanded inference and the comparison argument's exact frame observation

The inferred-read relation below contains actual scoped-reader executions.
It is used only by the inference arm of argument admission. Successful
metatype cuts remain separate and do not manufacture replies for this port.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeArgumentQueryTransport

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type
open Spec.Type.RuntimeRefinement
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)
open HERangeTypeReadPrimitives (source)

def inferredRead (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) : TypeLookupRel :=
  fun bindings subject expected types => ∃ supply : Supply, ∃ depth : Nat,
    (∀ name ∈ invocationTypeScope scope [] subject expected bindings, name ∈ supply.used) ∧
    (NativeTypeScopedReads.evaluate ops source world depth (.infer true subject) supply).1 = some (.types types)

theorem comparison_read (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (scope : List String) (before : Frame) (lower upper : Int) (expected : Atom) :
    inferredRead (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope
      before.bindings (HEIfSourceSelection.Range.condition lower upper) expected [.symbol "Bool"] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (HEIfSourceSelection.Range.condition lower upper) expected before.bindings, 0⟩
  refine ⟨supply, 2, fun _ member => member, ?_⟩
  simpa only [HEIfSourceSelection.Range.condition, HEFreshEquationFrames.Range.number] using
    HERangeTypeReadApplications.comparison_type world active primitive unobservedClosure 0 supply lower upper

theorem comparison_read_unique (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (scope : List String) (before : Frame) (lower upper : Int) (expected : Atom) (types : List Atom)
    (queried : inferredRead (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope
      before.bindings (HEIfSourceSelection.Range.condition lower upper) expected types) : types = [.symbol "Bool"] := by
  obtain ⟨supply, depth, _, completed⟩ := queried
  exact HERangeTypeReadApplications.comparison_types_unique world active primitive unobservedClosure depth supply lower upper types
    (by simpa only [HEIfSourceSelection.Range.condition, HEFreshEquationFrames.Range.number] using completed)

/-- Every caller and demand is protected before the actual arrow query.
The range name in the result is the name returned by that read occurrence. -/
theorem if_read (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (expected : Atom) :
    ∃ name,
      inferredRead currentOps world scope before.bindings (.symbol "if") expected [(HEIfSourceSelection.signature name).functionType] ∧
      name ∉ invocationTypeScope scope [] (.symbol "if") expected before.bindings := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.symbol "if") expected before.bindings, 0⟩
  obtain ⟨name, completed, fresh⟩ := HERangeTypeReadApplications.if_head_type currentOps world 0 supply
  exact ⟨name, ⟨supply, 1, fun _ member => member, completed⟩, fresh⟩

theorem bool_has_no_metatype_cut (kind : Atom) : ¬HEArgumentMetatypeRole.KindCut (.symbol "Bool") kind := by
  intro cut
  have success := HEArgumentMetatypeRole.native_cut cut
  have absent : TypeScopeMatcher.metaCheckAtom (.symbol "Bool") kind = none := rfl
  rw [absent] at success
  cases success

/-- The actual inferred Bool reply checks successfully in exactly the old
caller frame. No caller satisfiability or result-frame identity is assumed. -/
theorem comparison_admission (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (scope : List String) (expression : Atom) (position : Nat) (lower upper : Int) :
    HEArgumentMetatypeRole.Admission HERangeSourceProgram.space
      (inferredRead (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope)
      policy expression (HEIfSourceSelection.Range.condition lower upper) (.symbol "Bool") position before [before] [] := by
  apply HEArgumentMetatypeRole.singleton_inferred
  · exact fun kind _ => bool_has_no_metatype_cut kind
  · exact comparison_read world active primitive unobservedClosure scope before lower upper (.symbol "Bool")
  · exact .unchanged (before.preserved_type_match policy
      (HEContextualArithmeticSource.same_symbol_match "Bool" before.bindings (by decide) (by decide)))

/-- Historical Undefined and actual inferred Bool are different replies,
but these two real checks have the same exact frame/error observation. -/
theorem comparison_local_frame_transport (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (scope : List String) (expression : Atom) (position : Nat) (lower upper : Int) :
    ArgumentChecksRel HERangeSourceProgram.space (scopedLookup scope HERangeSourceProgram.space) policy expression
      (HEIfSourceSelection.Range.condition lower upper) (.symbol "Bool") position [before] [before] [] ∧
    HEArgumentMetatypeRole.Admission HERangeSourceProgram.space
      (inferredRead (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope)
      policy expression (HEIfSourceSelection.Range.condition lower upper) (.symbol "Bool") position before [before] [] := by
  exact ⟨HEIfSourceSelection.unknown_argument HERangeSourceProgram.space scope policy before expression
    (HEIfSourceSelection.Range.condition lower upper) (.symbol "Bool") position rfl,
    comparison_admission world active primitive unobservedClosure policy before scope expression position lower upper⟩

theorem held_branch_cut (policy : Policy) (before : Frame)
    (expression subject : Atom) (position : Nat) (lookup : TypeLookupRel) :
    HEArgumentMetatypeRole.Admission HERangeSourceProgram.space lookup policy expression subject Atom.atomType position
      before [before] [] := by
  cases subject with
  | symbol name => exact .kind (.symbol name) (.atom _)
  | var name => exact .kind (.variable name) (.atom _)
  | grounded value => exact .kind (.grounded value) (.atom _)
  | expression children => exact .kind (.expression children) (.atom _)

theorem held_tuple_cut (policy : Policy) (before : Frame) (expression : Atom)
    (children : List Atom) (position : Nat) (lookup : TypeLookupRel) :
    HEArgumentMetatypeRole.Admission HERangeSourceProgram.space lookup policy expression (.expression children)
      Atom.expressionType position before [before] [] :=
  .kind (.expression children) .expression

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeArgumentQueryTransport
