import Mettapedia.Machines.CMemory.ReadBlock
import Mettapedia.Machines.CMemory.Array
import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalStore

/-!
# Retained post-index pointer stores on physical memory

The supplied assignment selects its array, counter and pointer operand. The
shared syntax recognizer excludes counter aliases; typed local reads resolve
the actual pointer and UInt32 index. The store uses the old index, and the
resulting local environment records one unsigned increment.

The append contract derives physical room from an owned dynamic array. It
does not assume a successful assignment or reconstruct the statement from an
expected result. Native byte layout and general C expression sequencing remain
outside this fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.PostIndexWrites

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

def execute (environment : Environment) (statement : CStatement) : CProg CVal Environment := do
  let site ← resolved (LocalStore.site? statement)
  let array ← resolved (environment site.array) >>= pointer
  let index ← resolved (environment site.counter) >>= word
  let value ← resolved (environment site.value) >>= pointer
  match array with
  | none => CProg.undefined
  | some address => do
      CProg.store (address + index.toNat) (.ptr value)
      pure (Function.update environment site.counter (some (.u32 (index + 1))))

def assign (layout : Layout) (environment : Environment) : CStatement → CProg CVal Environment
  | statement@(.assign (.identifier _) _) => ReadBlock.assign layout environment statement
  | statement@(.compoundAssign _ _ _) => ReadBlock.assign layout environment statement
  | statement => execute environment statement

theorem resolved_site_uses_actual_old_index (environment : Environment) (site : LocalStore.Site)
    (address : Ptr) (index : UInt32) (value : Option Ptr)
    (arraySeparated : site.array ≠ site.counter) (rhsSeparated : site.value ≠ site.counter)
    (arrayRead : environment site.array = some (.ptr (some address)))
    (indexRead : environment site.counter = some (.u32 index))
    (valueRead : environment site.value = some (.ptr value)) :
    execute environment site.statement =
      (CProg.store (address + index.toNat) (.ptr value) >>= fun _ =>
        pure (Function.update environment site.counter (some (.u32 (index + 1))))) := by
  unfold execute
  rw [LocalStore.authored_site_is_retained site arraySeparated rhsSeparated]
  simp only [resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [arrayRead, indexRead, valueRead]
  rfl

theorem local_assignment_reuses_read_service (layout : Layout) (environment : Environment)
    (name : Name) (rhs : CExpr) :
    assign layout environment (.assign (.identifier name) rhs) =
      ReadBlock.assign layout environment (.assign (.identifier name) rhs) := rfl

theorem compound_assignment_reuses_read_service (layout : Layout) (environment : Environment)
    (operator : BinaryOperator) (location rhs : CExpr) :
    assign layout environment (.compoundAssign operator location rhs) =
      ReadBlock.assign layout environment (.compoundAssign operator location rhs) := rfl

theorem nullable_store_keeps_actual_operand (environment : Environment) (site : LocalStore.Site)
    (address : Ptr) (index : UInt32)
    (arraySeparated : site.array ≠ site.counter) (rhsSeparated : site.value ≠ site.counter)
    (arrayRead : environment site.array = some (.ptr (some address)))
    (indexRead : environment site.counter = some (.u32 index))
    (valueRead : environment site.value = some (.ptr none)) :
    execute environment site.statement =
      (CProg.store (address + index.toNat) (.ptr none) >>= fun _ =>
        pure (Function.update environment site.counter (some (.u32 (index + 1))))) :=
  resolved_site_uses_actual_old_index environment site address index none arraySeparated
    rhsSeparated arrayRead indexRead valueRead

section Specifications

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem triple_preserves_wellFormed {α : Type} {P : Heap L → Prop}
    {Q : α → Heap L → Prop} {program : CProg CVal α} (spec : CTriple P program Q) :
    CTriple (fun σ => WellFormed σ ∧ P σ) program
      (fun result σ => WellFormed σ ∧ Q result σ) := by
  intro σ holds
  have checked := spec σ holds.2
  refine ⟨checked.1, ?_⟩
  intro result σ' runs
  exact ⟨runs_wellFormed program holds.1 checked.1 runs, checked.2 result σ' runs⟩

theorem physical_append_refines_initialized_prefix (environment : Environment)
    (site : LocalStore.Site) (address : Ptr) (index : UInt32) (value : Option Ptr)
    (capacity : Nat) (initialized : List CVal)
    (arraySeparated : site.array ≠ site.counter) (rhsSeparated : site.value ≠ site.counter)
    (arrayRead : environment site.array = some (.ptr (some address)))
    (indexRead : environment site.counter = some (.u32 index))
    (valueRead : environment site.value = some (.ptr value))
    (position : index.toNat = initialized.length) (room : initialized.length < capacity) :
    CTriple (L := L) (DynArray (some address) capacity initialized)
      (execute environment site.statement)
      (fun result σ => result = Function.update environment site.counter
        (some (.u32 (index + 1))) ∧
          DynArray (some address) capacity (initialized ++ [.ptr value]) σ) := by
  rw [resolved_site_uses_actual_old_index environment site address index value arraySeparated
    rhsSeparated arrayRead indexRead valueRead, position]
  refine triple_bind _ (store_append address capacity initialized (.ptr value) room) fun _ => ?_
  exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)

theorem append_counter_does_not_wrap (index : UInt32) (capacity : Nat)
    (initialized : List CVal) (position : index.toNat = initialized.length)
    (room : initialized.length < capacity) (bounded : capacity < 2 ^ 32) :
    (index + 1).toNat = initialized.length + 1 := by
  rw [UInt32.toNat_add]
  have strict : index.toNat + 1 < 2 ^ 32 := by omega
  simpa only [UInt32.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32), position]
    using Nat.mod_eq_of_lt strict

end Specifications

namespace Controls

def site : LocalStore.Site := ⟨"pending".toList, "added".toList, "dependency".toList⟩

def environment (address : Option Ptr) (index : UInt32) (value : Option Ptr) : Environment :=
  fun name =>
    if name = site.array then some (.ptr address)
    else if name = site.counter then some (.u32 index)
    else if name = site.value then some (.ptr value) else none

theorem retained_assignment_writes_old_slot (address value : Ptr) :
    execute (environment (some address) 1 (some value)) site.statement =
      (CProg.store (address + 1) (.ptr (some value)) >>= fun _ =>
        pure (Function.update (environment (some address) 1 (some value)) site.counter
          (some (.u32 2)))) := rfl

theorem null_destination_is_not_empty_success (index : UInt32) (value : Option Ptr) :
    execute (environment none index value) site.statement = CProg.undefined := rfl

theorem missing_rhs_is_not_allocation_failure (address : Ptr) (index : UInt32) :
    execute (Function.update (environment (some address) index none) site.value none)
      site.statement = CProg.undefined := by
  simp [execute, site, LocalStore.site?, LocalStore.Site.statement, environment,
    resolved, pointer, word, Prog.bind_assoc]
  exact undefined_bind _

theorem wrong_counter_type_is_not_repaired (address : Ptr) :
    execute (Function.update (environment (some address) 0 none) site.counter
      (some (.bool false))) site.statement = CProg.undefined := by
  simp [execute, site, LocalStore.site?, LocalStore.Site.statement, environment,
    resolved, pointer, word]
  exact undefined_bind _

theorem rhs_counter_alias_is_not_admitted (environment : Environment) :
    execute environment (⟨"pending".toList, "added".toList, "added".toList⟩ : LocalStore.Site).statement =
      CProg.undefined := by
  unfold execute
  rw [show LocalStore.site? (⟨"pending".toList, "added".toList,
    "added".toList⟩ : LocalStore.Site).statement = none from by decide +kernel]
  exact undefined_bind _

theorem altered_index_is_not_repaired (environment : Environment) :
    execute environment (.assign (.index (.identifier "pending".toList)
      (.identifier "added".toList)) (.identifier "dependency".toList)) =
      CProg.undefined := by
  change (CProg.undefined >>= _) = CProg.undefined
  exact undefined_bind _

end Controls

end Mettapedia.Machines.CMemory.PostIndexWrites
