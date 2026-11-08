import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeClosureReadWorlds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeClosureControls

/-! # Closure-port completion and retained-alias controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeClosureReadControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph NativeTypeSourcePorts
open ScopedSubtypeClosureControls (a b c duplicateRows external)

def source : Source where
  rows := duplicateRows
  intrinsicRows := []
  rename := fun _ _ name => name
  subtypeBudget := 3
  subtypeFresh := "out"
  alpha := TypeAlphaComparison.check

def first : TypeReadSupply.Supply := ⟨["caller", "alias"], 0⟩
def second : TypeReadSupply.Supply := ⟨["caller", "alias", "unobserved#4"], 8⟩

theorem source_rows_safe : ScopedSubtypeReadSafety.RowsSafe source.rows := by
  apply ScopedSubtypeReadSafety.rowsSafe_of_resourceFree
  decide

theorem actual_port_keeps_order_and_duplicates :
    (NativeTypeScopedReads.primitive source external first (.closure [a])).1 = some (.types [a, b, b, c, c]) := by cbv

theorem unfinished_port_retains_its_allocations :
    (NativeTypeScopedReads.primitive { source with subtypeBudget := 1 } external first (.closure [a])).1 = none ∧
    (NativeTypeScopedReads.primitive { source with subtypeBudget := 1 } external first (.closure [a])).2.next > first.next := by
  cbv

theorem unrelated_private_allocations_preserve_the_retained_answer :
    (NativeTypeScopedReads.primitive source external second (.closure [a])).1 = some (.types [a, b, b, c, c]) :=
  NativeTypeClosureReadWorlds.retained_closure_equal source external source_rows_safe
    TypeAlphaComparison.equivariant [a] (by decide) first second [a, b, b, c, c]
    actual_port_keeps_order_and_duplicates (by decide)

theorem actual_closure_preserves_a_retained_caller_alias :
    ∃ next : Equiv.Perm String,
      TypeScopeRenaming.renameState next TypeReadWorlds.Controls.callerState =
        TypeScopeRenaming.renameState (Equiv.refl String) TypeReadWorlds.Controls.callerState ∧
      (NativeTypeScopedReads.primitive source external second (.closure [a])).1 =
        (NativeTypeScopedReads.primitive source external first (.closure [a])).1.map
          (NativeTypeReadWorlds.renameReply next) := by
  simpa only [List.map_cons, List.map_nil, a, renameAtom] using
    NativeTypeClosureReadWorlds.closure_keeps_existing_state source external source_rows_safe
      TypeAlphaComparison.equivariant (Equiv.refl String) ["caller", "alias"] first second
      (by simp [first]) (by simp [second]) [a] (by decide) TypeReadWorlds.Controls.callerState
      TypeReadWorlds.Controls.caller_alias_is_supported

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeClosureReadControls
