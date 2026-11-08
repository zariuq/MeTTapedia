import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotReadback

/-! # Source-emitted EXPR/BIND/SAME origins and negative controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Mettapedia.Machines
open HEPatternSlotOrigins HEPatternSlotReadback

def slots (name : String) : Option Nat :=
  if name == "x" then some 0 else if name == "y" then some 1 else none

def patterns : List Atom :=
  [.expression [.symbol "Pair", .var "x", .expression [.symbol "Nested", .var "y"], .var "x"]]

def generated : Emitted :=
  ⟨[.expr 0 1 4, .atom 1 (.symbol "Pair"), .bind 2 0,
    .expr 3 5 2, .atom 5 (.symbol "Nested"), .bind 6 1, .same 4 0], 7, [1, 0]⟩

theorem exact_source_emission : compile slots patterns = some generated := by cbv

theorem actual_emission_earns_allocation : Allocated 1 generated.code 7 :=
  compiled_allocated slots patterns generated exact_source_emission

theorem actual_emission_never_rebinds : boundSlots generated.code = [0, 1] ∧ (boundSlots generated.code).Nodup :=
  ⟨rfl, compiled_bindings_unique slots patterns generated exact_source_emission⟩

def held : Entry.Value := .expression .held [.symbol "Data", .grounded (.int 7)]
def inside : Entry.Value := .grounded (.int 9)
def argument : Entry.Value :=
  .expression .held [.symbol "Pair", held, .expression .held [.symbol "Nested", inside], held]
def args : List Entry.Value := [argument]
def empty : RegisterCode.Regs Entry.Value := fun _ => none
def equality (left right : Atom) : Bool := left == right

theorem first_field_is_recovered_from_emitted_ops :
    recoverSlot 0 generated.code (initialOrigins 1) = some (0, some 1) := by decide

theorem nested_field_is_not_mislabelled_first_level :
    recoverSlot 1 generated.code (initialOrigins 1) = none := by decide

theorem successful_same_retains_original_binding :
    (run equality generated.code (fun index => args[index]?) empty).map
      (fun state => (state.2 0, state.2 1)) = some (some held, some inside) := by cbv

theorem different_repeated_value_fails :
    run equality generated.code
      (fun index => ([.expression .held [.symbol "Pair", held,
        .expression .held [.symbol "Nested", inside], .grounded (.int 8)]] : List Entry.Value)[index]?) empty = none := by cbv

theorem missing_slot_mapping_declines_compilation : compile (fun _ => none) patterns = none := by cbv

def overlapCode : List Op := [.expr 0 1 2, .expr 2 0 2, .bind 0 0]
def overlapArg : Entry.Value :=
  .expression .held [.symbol "Outer", .expression .held [.symbol "Inner", .grounded (.int 7)]]

/-- Reusing a nested load's registers corrupts a whole-argument origin.
The actual emitter's derived allocation rule excludes this program. -/
theorem overlapping_load_breaks_origin :
    recoverSlot 0 overlapCode (initialOrigins 1) = some (0, none) ∧
    ((run equality overlapCode (fun index => ([overlapArg] : List Entry.Value)[index]?) empty).bind
      fun state => state.2 0) = some (.symbol "Inner") ∧
    readOrigin [overlapArg] (0, none) = some overlapArg := by exact ⟨by decide, by cbv, rfl⟩

theorem overlapping_program_is_not_emittable : ¬Allocated 1 overlapCode 2 := by
  intro allocated
  cases allocated with
  | expr _ rest => cases rest

theorem key_skip_retains_loaded_fields (rest : List Op) (locals : RegisterCode.Regs Entry.Value) :
    run equality (.expr 0 1 4 :: .atom 1 (.symbol "Pair") :: rest)
      (fun index => args[index]?) locals =
      run equality rest (writeBlock 1 [.symbol "Pair", held, .expression .held [.symbol "Nested", inside], held]
        (fun index => args[index]?)) locals :=
  run_key_prefix equality 0 1 "Pair" [held, .expression .held [.symbol "Nested", inside], held] .held rest
    (fun index => args[index]?) locals rfl (by decide)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotControls
