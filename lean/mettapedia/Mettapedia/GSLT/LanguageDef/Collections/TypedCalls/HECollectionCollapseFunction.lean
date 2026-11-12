import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControl

/-!
# The authored collapse function shell

The context-space instruction supplies the live source context. The existing
square/range child is captured there, its saved occurrences pass through the
authored fold, and the function consumes the resulting return instruction.
The input is source syntax, not an assumed collection result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFunction

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)

def template (lower upper : Int) (context : Entry.Value) (captureName resultName left right : String) : Entry.Value :=
  .expression .active [.symbol "chain", .expression .active [.symbol "collapse-bind",
    .expression .active [.symbol "metta", HECollectionSquareRange.call lower upper, .symbol "%Undefined%", context]],
    .var captureName, HECollectionCollapseControl.foldContinuation (.var captureName) left right resultName]

def body (lower upper : Int) (spaceName captureName resultName left right : String) : Entry.Value :=
  .expression .active [.symbol "chain", .expression .active [.symbol "context-space"], .var spaceName,
    template lower upper (.var spaceName) captureName resultName left right]

def function (lower upper : Int) (spaceName captureName resultName left right : String) : Entry.Value :=
  .expression .active [.symbol "function", body lower upper spaceName captureName resultName left right]

theorem context_substitution (policy : Policy) (lower upper : Int) (spaceName captureName resultName left right : String)
    (context : Entry.Value) (captureDifferent : captureName ≠ spaceName) (resultDifferent : resultName ≠ spaceName)
    (leftDifferent : left ≠ spaceName) (rightDifferent : right ≠ spaceName) :
    substituteBinder policy spaceName context (template lower upper (.var spaceName) captureName resultName left right) =
      template lower upper context captureName resultName left right := by
  cases rebuilding : policy.rebuilding <;>
    simp [template, HECollectionSquareRange.call, HERangeUntypedEntry.rangeCall,
      HECollectionCollapseControl.foldContinuation, HECollectionCollapseControl.foldCall,
      HECollectionFoldSourceLoop.operation, substituteBinder, Entry.Value.substitute,
      Entry.Value.rebuildStatus, rebuilding, captureDifferent, resultDifferent, leftDifferent, rightDifferent]

theorem squares_closed (lower : Int) (count : Nat) :
    TypeSubst.typeVarsList ((HECollectionSquareRange.squares lower count).map Entry.Value.erase) = [] := by
  apply HECollectionCollapseControl.values_closed
  intro value member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  simp [Entry.Value.erase, TypeSubst.typeVars]

theorem source_scoped (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (lower upper : Int) (spaceName captureName resultName left right : String)
    (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (captureSpace : captureName ≠ spaceName) (resultSpace : resultName ≠ spaceName)
    (leftSpace : left ≠ spaceName) (rightSpace : right ≠ spaceName)
    (resultCapture : resultName ≠ captureName) (leftCapture : left ≠ captureName) (rightCapture : right ≠ captureName) :
    let current := environment minimal nativePolicy external active primitive subtypes
    ∃ afterWorld after mark, Stateful.MinimalRel current HECollectionSpaceExtension.space world live scope caller
      (function lower upper spaceName captureName resultName left right) before
      [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)] afterWorld (policy := policy) ∧
      HECollectionScopedFold.PreservesUnrelated live before after left right := by
  let current := environment minimal nativePolicy external active primitive subtypes
  let functionBody := body lower upper spaceName captureName resultName left right
  let functionLive := (.expression [.symbol "function", functionBody.erase]) :: live
  let functionCaller : Option Atom := some (.expression [.symbol "function", functionBody.erase])
  let context := Entry.Value.grounded (minimal.contextPayload HECollectionSpaceExtension.space)
  obtain ⟨afterWorld, after, mark, innerRun, kept⟩ := HECollectionCollapseControl.source_inner_scoped minimal nativePolicy external active
    primitive subtypes world policy before functionLive scope functionCaller lower upper captureName resultName left right
    different leftFresh rightFresh resultCapture leftCapture rightCapture
  let result := Entry.Value.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat)
  let returned := Entry.Value.expression .active [.symbol "return", result]
  have closed : TypeSubst.typeVars returned.erase = [] := by
    simp only [returned, result, Entry.Value.erase, List.map_cons, List.map_nil, TypeSubst.typeVars,
      TypeSubst.typeVarsList, squares_closed, List.nil_append]
  have contextClosed : TypeSubst.typeVars context.erase = [] := by simp [context, Entry.Value.erase, TypeSubst.typeVars]
  refine ⟨afterWorld, after, mark, ?_, ?_⟩
  ·
    apply Stateful.MinimalRel.function (world1 := afterWorld) (raw := [(returned, after)]) rfl
    · apply Stateful.BodyRel.run (world1 := afterWorld) (raw := [(returned, after)])
      · apply Stateful.MinimalRel.chain (world1 := world) (selected := [(context, before)])
        · exact .contextSpace
        · apply Stateful.BoundaryBatchRel.single_iff.mpr
          apply Stateful.BoundaryRel.chain
          rw [HECollectionClosedAppend.closed_read policy before context contextClosed,
            context_substitution policy lower upper spaceName captureName resultName left right context
              captureSpace resultSpace leftSpace rightSpace]
          exact innerRun
      · apply Stateful.BoundaryBatchRel.single_iff.mpr
        have fixed := HECollectionClosedAppend.closed_read policy after returned closed
        simpa only [fixed] using
          (Stateful.BoundaryRel.bodyTerminal (value := returned) (frame := after) (policy := policy)
            (by rw [fixed]; simp [returned, Entry.Value.erase, Minimal.embeddedInstruction]))
    · apply Stateful.BoundaryBatchRel.single_iff.mpr
      exact .functionReturn
  · intro name visible unbound notLeft notRight
    obtain ⟨atom, member, occurs⟩ := visible
    exact kept name ⟨atom, List.mem_cons_of_mem _ member, occurs⟩ unbound notLeft notRight

theorem source (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (lower upper : Int) (spaceName captureName resultName left right : String)
    (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (captureSpace : captureName ≠ spaceName) (resultSpace : resultName ≠ spaceName)
    (leftSpace : left ≠ spaceName) (rightSpace : right ≠ spaceName)
    (resultCapture : resultName ≠ captureName) (leftCapture : left ≠ captureName) (rightCapture : right ≠ captureName) :
    let current := environment minimal nativePolicy external active primitive subtypes
    ∃ afterWorld after mark, Stateful.MinimalRel current HECollectionSpaceExtension.space world live scope caller
      (function lower upper spaceName captureName resultName left right) before
      [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)] afterWorld (policy := policy) := by
  obtain ⟨afterWorld, after, mark, executed, _kept⟩ := source_scoped minimal nativePolicy external active primitive subtypes
    world policy before live scope caller lower upper spaceName captureName resultName left right different leftFresh rightFresh
    captureSpace resultSpace leftSpace rightSpace resultCapture leftCapture rightCapture
  exact ⟨afterWorld, after, mark, executed⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFunction
