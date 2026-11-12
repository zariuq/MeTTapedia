import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericSource
import Mettapedia.Languages.MeTTa.HE.ContextualAliasControls

/-! # Marked data ingress and supported variables in the actual fold source -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionMarkedControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionFoldEmission HECollectionFoldNativeEntry
open ContextualAliasControls (before policy)

theorem fixed_other : before.read policy (.var "other") = .var "other" := by
  have fresh : "other" ∉ specBindingVars before.bindings := by
    simp [before, Entry.Value.Controls.sourceAliasOutput, Entry.Value.Controls.matchedAlias, Entry.Value.Controls.aliasBindings,
      Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, specBindingVars,
      Entry.Value.Controls.openHeldValue, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]
  simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before "other" fresh

variable (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
  (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal policy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem both_container_marks_have_actual_typed_numeric_runs (world : World) (itemsMark : Entry.Status) :
    ∃ after, Stateful.AtomRel current sourceSpace world [] []
      (HECollectionNumericSource.query [1, 0, 1] 0 "z" "other" (itemsMark := itemsMark)) Atom.undefinedType before
      [(HECollectionNumericFold.number 2, after)] world (policy := policy) := by
  simpa using HECollectionNumericSource.source_fixed (itemsMark := itemsMark) minimal policy external active primitive subtypes
    world policy before [] [] [1, 0, 1] 0 "z" "other" (by decide) ContextualAliasControls.supported_but_unassigned.2 fixed_other

def heldChild : Entry.Value := .expression .held
  [.symbol "function", .expression .active [.symbol "return", .symbol "Kept"]]

theorem held_function_data_enters_as_data :
    Entry.Rel policy.reentry heldChild.status heldChild.erase Atom.undefinedType .deliver := by
  simp only [heldChild, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
  apply Entry.Rel.held
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · decide
  · rfl
  · rfl

theorem clearing_the_child_mark_changes_its_entry_action :
    Entry.Rel policy.reentry (heldChild.withStatus .active).status (heldChild.withStatus .active).erase Atom.undefinedType .interpret := by
  simpa only [heldChild, Entry.Value.withStatus, Entry.Value.erase, Entry.Value.status, List.map_cons, List.map_nil] using
    (Entry.Rel.expression (policy := policy.reentry) (status := .active)
      (head := Atom.symbol "function") (tail := [.expression [.symbol "return", .symbol "Kept"]])
      (expected := Atom.undefinedType)
      (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))

theorem one_fold_emission_retains_the_whole_held_child (world : World) (itemsMark : Entry.Status) :
    Stateful.InvocationRel current sourceSpace world [] [] none
      (call [heldChild] (HECollectionNumericFold.number 0) "acc" "item" (.var "item")
        (.grounded (minimal.contextPayload sourceSpace)) (itemsMark := itemsMark)) Frame.empty
      [(emission (HECollectionWorld.hidden world) [] [] Frame.empty [heldChild] (HECollectionNumericFold.number 0)
        "acc" "item" (.var "item") (.grounded (minimal.contextPayload sourceSpace)), Frame.empty)] world (policy := policy) :=
  marked_invocation (HECollectionFoldWorldServices.marked_emitter minimal policy external active primitive subtypes world)
    policy [] [] none Frame.empty [heldChild] (HECollectionNumericFold.number 0) "acc" "item" (.var "item")
      (.grounded (minimal.contextPayload sourceSpace)) itemsMark

theorem template_replacement_does_not_clear_the_child_mark (avoid : List String) :
    rewritten avoid (HECollectionNumericFold.number 0) heldChild "acc" "item" (.var "item") = heldChild := by
  simp [rewritten, Entry.Value.substitute]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionMarkedControls
