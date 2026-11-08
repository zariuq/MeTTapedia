import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedWorld
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReadControls

/-! # Scope, world and unfinished-run controls for recursive inference -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedWorld.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph
open NativeTypeScopedReads
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

theorem polymorphic_world_equality_keeps_final_supply (first second : ExternalView)
    (depth : Nat) (supply : Supply) :
    evaluate (TypeScopeMatcher.ops first id (fun _ => [])) NativeTypeFreshReadControls.source
        first depth NativeTypeFreshReadControls.call supply =
      evaluate (TypeScopeMatcher.ops second id (fun _ => [])) NativeTypeFreshReadControls.source
        second depth NativeTypeFreshReadControls.call supply :=
  evaluate_world NativeTypeFreshReadControls.source
    NativeTypeFreshReadControls.resource_safety_does_not_supply_freshness first second id id
    (fun _ safe => safe) (fun _ _ => rfl) _ _ depth _ supply

theorem unfinished_child_keeps_earlier_allocation :
    (evaluate NativeTypeRecursiveControls.ops NativeTypeScopedReads.Controls.tupleSource
      NativeTypeRecursiveControls.world 2 NativeTypeScopedReads.Controls.tupleCall ⟨[], 0⟩).1 = none ∧
    (evaluate NativeTypeRecursiveControls.ops NativeTypeScopedReads.Controls.tupleSource
      NativeTypeRecursiveControls.world 2 NativeTypeScopedReads.Controls.tupleCall ⟨[], 0⟩).2.next = 1 := by cbv

def mutableSource : NativeTypeSourcePorts.Source :=
  { NativeTypeFreshReadControls.source with
    rows := [NativeTypeRecursiveControls.row "mutable-typed" (RetainedTypePayloads.Controls.state "A")] }

theorem mutable_source_is_not_admitted : ¬ NativeTypeSourcePorts.Safe mutableSource := by
  unfold NativeTypeSourcePorts.Safe
  decide

theorem unsafe_primitive_can_change_across_worlds :
    (primitive mutableSource RetainedTypePayloads.Controls.initial ⟨[], 0⟩
      (.annotations (.symbol "mutable-typed"))).1 = some (.types [.grounded (.int 1)]) ∧
    (primitive mutableSource RetainedTypePayloads.Controls.changed ⟨[], 0⟩
      (.annotations (.symbol "mutable-typed"))).1 = some (.types [.grounded (.int 2)]) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedWorld.Controls
