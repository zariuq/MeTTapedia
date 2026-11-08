import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeReadWorlds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeClosureCoordinates

/-!
# Coordinate extension at the actual completed-closure port

The occurrence-scoped native-reader adapter runs the real bounded closure
algorithm and retains its returned names. Different earlier private
allocations preserve completion status, ordered replies and the protected
caller interface. This is a primitive-port law; simulation of arbitrary
recursive cached call graphs is a separate composition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeClosureReadWorlds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph NativeTypeSourcePorts NativeTypeReadWorlds TypeReadWorlds
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

theorem closure_coordinates (source : Source) (world : ExternalView)
    (safe : ScopedSubtypeReadSafety.RowsSafe source.rows)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (previous : Equiv.Perm String) (live : List String) (first second : Supply)
    (firstProtected : live ⊆ first.used) (secondProtected : live.map previous ⊆ second.used)
    (seeds : List Atom) (seedSafe : TypeDependencyAdmission.resourceFreeList seeds = true) :
    let types := (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha
      source.subtypeBudget seeds first).1.toList.flatten
    let left := NativeTypeScopedReads.primitive source world first (.closure seeds)
    let right := NativeTypeScopedReads.primitive source world second (.closure (seeds.map (renameAtom previous)))
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live ++ atomListVariables seeds, next name = previous name) ∧
      right.1 = left.1.map (renameReply next) ∧
      ((live ++ atomListVariables seeds) ++ atomListVariables types) ⊆ left.2.used ∧
      ((live ++ atomListVariables seeds) ++ atomListVariables types).map next ⊆ right.2.used := by
  dsimp only
  obtain ⟨next, agrees, carried, firstKeeps, secondKeeps⟩ :=
    ScopedSubtypeClosureCoordinates.completeTypes_read_coordinates world source.rows safe source.subtypeFresh
      source.alpha alpha previous live source.subtypeBudget seeds seedSafe first second firstProtected secondProtected
  refine ⟨next, agrees, ?_, ?_, ?_⟩
  · change ((ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha
        source.subtypeBudget (seeds.map (renameAtom previous)) second).1.map
          (fun types => (NativeTypeDemand.ViewReply.types types : Reply))) = _
    rw [carried]
    simp only [NativeTypeScopedReads.primitive, Option.map_map, Function.comp_def, renameReply]
  · intro name member
    exact NativeTypeScopedReads.retain_old _ _ (firstKeeps member)
  · intro name member
    exact NativeTypeScopedReads.retain_old _ _ (secondKeeps member)

theorem closure_keeps_existing_state (source : Source) (world : ExternalView)
    (safe : ScopedSubtypeReadSafety.RowsSafe source.rows)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (previous : Equiv.Perm String) (live : List String) (first second : Supply)
    (firstProtected : live ⊆ first.used) (secondProtected : live.map previous ⊆ second.used)
    (seeds : List Atom) (seedSafe : TypeDependencyAdmission.resourceFreeList seeds = true)
    (state : TypeScopeMatcher.State) (supported : Supported live state) :
    ∃ next : Equiv.Perm String,
      TypeScopeRenaming.renameState next state = TypeScopeRenaming.renameState previous state ∧
      (NativeTypeScopedReads.primitive source world second (.closure (seeds.map (renameAtom previous)))).1 =
        (NativeTypeScopedReads.primitive source world first (.closure seeds)).1.map (renameReply next) := by
  obtain ⟨next, agrees, reply, _, _⟩ := closure_coordinates source world safe alpha previous live first second
    firstProtected secondProtected seeds seedSafe
  exact ⟨next, supported_readout live state supported previous next
    (fun name member => agrees name (List.mem_append_left _ member)), reply⟩

/-- A closed retained result can be reused after unrelated private
allocations. This statement does not identify the two allocator histories. -/
theorem retained_closure_equal (source : Source) (world : ExternalView)
    (safe : ScopedSubtypeReadSafety.RowsSafe source.rows)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (seeds : List Atom) (seedSafe : TypeDependencyAdmission.resourceFreeList seeds = true)
    (first second : Supply) (types : List Atom)
    (completed : (NativeTypeScopedReads.primitive source world first (.closure seeds)).1 = some (.types types))
    (retained : RetainedTypePayloads.admittedList types = true) :
    (NativeTypeScopedReads.primitive source world second (.closure seeds)).1 = some (.types types) := by
  change (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha
    source.subtypeBudget seeds first).1.map (fun types => (NativeTypeDemand.ViewReply.types types : Reply)) =
      some (.types types) at completed
  obtain ⟨values, returned, equal⟩ := Option.map_eq_some_iff.mp completed
  cases NativeTypeDemand.ViewReply.types.inj equal
  have same := ScopedSubtypeClosureCoordinates.retained_completeTypes_equal world source.rows safe
    source.subtypeFresh source.alpha alpha source.subtypeBudget seeds seedSafe first second types returned retained
  simp only [NativeTypeScopedReads.primitive, same, Option.map_some]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeClosureReadWorlds
