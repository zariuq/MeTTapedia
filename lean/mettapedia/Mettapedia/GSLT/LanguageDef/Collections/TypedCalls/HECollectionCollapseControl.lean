import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareCapture
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionScopedFold

/-! Actual capture-to-fold-to-return control inside the collapse definition.
The input pairs are produced by the executed square/range child, and the
source fold invocation consumes them at the reached snapshot world. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControl

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment snapshots)

def foldCall (packed : Entry.Value) (left right : String) : Entry.Value :=
  .expression .active [.symbol "foldl-atom", packed, .expression .active [], .var left, .var right,
    HECollectionFoldSourceLoop.operation .active left right]

def foldContinuation (packed : Entry.Value) (left right resultName : String) : Entry.Value :=
  .expression .active [.symbol "chain", .expression .active [.symbol "eval", foldCall packed left right],
    .var resultName, .expression .active [.symbol "return", .var resultName]]

def inner (minimal : Minimal.Services) (lower upper : Int) (captureName resultName left right : String) : Entry.Value :=
  .expression .active [.symbol "chain", HECollectionSquareCapture.operand minimal lower upper, .var captureName,
    foldContinuation (.var captureName) left right resultName]

theorem values_closed (values : List Entry.Value)
    (closed : ∀ value ∈ values, TypeSubst.typeVars value.erase = []) :
    TypeSubst.typeVarsList (values.map Entry.Value.erase) = [] := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, TypeSubst.typeVarsList, closed value (by simp),
        ih (fun child member => closed child (List.mem_cons_of_mem _ member)), List.nil_append]

theorem row_values_closed (rows : List Result)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    TypeSubst.typeVars (.expression .active (rows.map Prod.fst) : Entry.Value).erase = [] := by
  simp only [Entry.Value.erase, TypeSubst.typeVars]
  apply values_closed
  intro value member
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  exact closed row present

theorem capture_substitution (policy : Policy) (captureName resultName left right : String) (packed : Entry.Value)
    (resultDifferent : resultName ≠ captureName) (leftDifferent : left ≠ captureName) (rightDifferent : right ≠ captureName) :
    substituteBinder policy captureName packed (foldContinuation (.var captureName) left right resultName) =
      foldContinuation packed left right resultName := by
  cases rebuilding : policy.rebuilding <;>
    simp [foldContinuation, foldCall, HECollectionFoldSourceLoop.operation, substituteBinder,
      Entry.Value.substitute, Entry.Value.rebuildStatus, rebuilding, resultDifferent, leftDifferent, rightDifferent]

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem fold_then_return_scoped (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right resultName : String)
    (different : left ≠ right) (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots sourceSpace world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    ∃ after mark, Stateful.MinimalRel current sourceSpace world live scope caller
      (foldContinuation (.expression .active pairs) left right resultName) before
      [(.expression .active [.symbol "return", .expression mark (rows.map Prod.fst)], after)] world (policy := policy) ∧
      HECollectionScopedFold.PreservesUnrelated live before after left right := by
  let code := foldContinuation (.expression .active pairs) left right resultName
  obtain ⟨after, mark, folded, kept⟩ := HECollectionScopedFold.source minimal nativePolicy external active primitive subtypes
    world policy before (code.erase :: live) scope (some code.erase) left right different leftFresh rightFresh rows pairs stored closed
  refine ⟨after, mark, ?_, ?_⟩
  ·
    refine Stateful.MinimalRel.chain (world1 := world)
      (selected := [(.expression mark (rows.map Prod.fst), after)]) ?_ ?_
    · simpa only [code, foldContinuation, foldCall, HEFoldParameterCapture.query, Entry.Value.erase,
        List.map_cons, List.map_nil] using folded
    · apply Stateful.BoundaryBatchRel.single_iff.mpr
      apply Stateful.BoundaryRel.chain
      have valueClosed : TypeSubst.typeVars (.expression mark (rows.map Prod.fst) : Entry.Value).erase = [] := by
        simpa only [Entry.Value.erase] using row_values_closed rows closed
      rw [HECollectionClosedAppend.closed_read policy after _ valueClosed, substituteBinder_return]
      exact .data (by simp [Entry.Value.erase, Minimal.embeddedInstruction])
  · intro name visible unbound notLeft notRight
    obtain ⟨atom, member, occurs⟩ := visible
    exact kept name ⟨atom, List.mem_cons_of_mem _ member, occurs⟩ unbound notLeft notRight

theorem fold_then_return (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right resultName : String)
    (different : left ≠ right) (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots sourceSpace world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    ∃ after mark, Stateful.MinimalRel current sourceSpace world live scope caller
      (foldContinuation (.expression .active pairs) left right resultName) before
      [(.expression .active [.symbol "return", .expression mark (rows.map Prod.fst)], after)] world (policy := policy) := by
  obtain ⟨after, mark, executed, _kept⟩ := fold_then_return_scoped minimal nativePolicy external active primitive subtypes
    world policy before live scope caller left right resultName different leftFresh rightFresh rows pairs stored closed
  exact ⟨after, mark, executed⟩

theorem source_inner_scoped (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (lower upper : Int)
    (captureName resultName left right : String)
    (different : left ≠ right) (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (resultDifferent : resultName ≠ captureName) (leftDifferent : left ≠ captureName) (rightDifferent : right ≠ captureName) :
    ∃ afterWorld after mark, Stateful.MinimalRel current sourceSpace world live scope caller
      (inner minimal lower upper captureName resultName left right) before
      [(.expression .active [.symbol "return", .expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat)], after)]
      afterWorld (policy := policy) ∧
      HECollectionScopedFold.PreservesUnrelated live before after left right := by
  let code := inner minimal lower upper captureName resultName left right
  obtain ⟨afterWorld, pairs, rows, captured, stored, seen, closed, _, _⟩ :=
    HECollectionSquareCapture.source minimal nativePolicy external active primitive subtypes world policy before
      (code.erase :: live) scope (some code.erase) lower upper
  obtain ⟨after, mark, folded, kept⟩ := fold_then_return_scoped minimal nativePolicy external active primitive subtypes afterWorld policy before
    live scope caller left right resultName different leftFresh rightFresh rows pairs stored closed
  refine ⟨afterWorld, after, mark, ?_, kept⟩
  refine Stateful.MinimalRel.chain (world1 := afterWorld)
    (selected := [(.expression .active pairs, before)]) ?_ ?_
  · simpa only [code, inner, Entry.Value.erase, List.map_cons, List.map_nil] using captured
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    apply Stateful.BoundaryRel.chain
    have packedClosed : TypeSubst.typeVars (.expression .active pairs : Entry.Value).erase = [] := by
      simpa only [Entry.Value.erase, TypeSubst.typeVars] using HECollectionFoldSourceLoop.pairs_closed stored closed
    rw [HECollectionClosedAppend.closed_read policy before _ packedClosed,
      capture_substitution policy captureName resultName left right _ resultDifferent leftDifferent rightDifferent]
    simpa only [seen] using folded

theorem source_inner (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (lower upper : Int)
    (captureName resultName left right : String)
    (different : left ≠ right) (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (resultDifferent : resultName ≠ captureName) (leftDifferent : left ≠ captureName) (rightDifferent : right ≠ captureName) :
    ∃ afterWorld after mark, Stateful.MinimalRel current sourceSpace world live scope caller
      (inner minimal lower upper captureName resultName left right) before
      [(.expression .active [.symbol "return", .expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat)], after)]
      afterWorld (policy := policy) := by
  obtain ⟨afterWorld, after, mark, executed, _kept⟩ := source_inner_scoped minimal nativePolicy external active primitive subtypes
    world policy before live scope caller lower upper captureName resultName left right different leftFresh rightFresh
    resultDifferent leftDifferent rightDifferent
  exact ⟨afterWorld, after, mark, executed⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseControl
