import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeClosureCoordinates

/-! # Positive and negative controls for fresh-name closure transport -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeClosureControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open SubtypeClosureRounds SubtypeClosureCoordinates
open TypeReadSupply (Supply)

def external : RetainedTypePayloads.ExternalView := fun tag key => .grounded (.custom tag key)
def first : Supply := ⟨["caller"], 0⟩
def second : Supply := ⟨["caller", "dead#1", "dead#2"], 9⟩
def a : Atom := .symbol "A"
def b : Atom := .symbol "B"
def c : Atom := .symbol "C"
def box (value : Atom) : Atom := .expression [.symbol "Box", value]
def row (lower upper : Atom) : Atom := .expression [.symbol ":<", lower, upper]
def duplicateRows : List Atom := [row a b, row a b, row b c]

def duplicateRun (supply : Supply) :=
  ScopedSubtypeReads.run external duplicateRows "out" TypeAlphaComparison.check 3 (start [a]) supply

theorem duplicate_discoveries_and_parents_survive :
    (duplicateRun first).1 = .complete
      ⟨[⟨a, none, false⟩, ⟨b, some 0, false⟩, ⟨b, some 0, false⟩,
        ⟨c, some 1, false⟩, ⟨c, some 2, false⟩], 3⟩ := by cbv

theorem another_allocation_history_keeps_the_closed_result :
    (ScopedSubtypeReads.completeTypes external duplicateRows "out" TypeAlphaComparison.check 3 [a] second).1 =
      some [a, b, b, c, c] := by cbv

theorem exact_supply_equality_is_not_required :
    (duplicateRun first).2 ≠ (duplicateRun second).2 := by
  cbv
  simp

theorem short_budget_is_not_an_empty_closure :
    (ScopedSubtypeReads.completeTypes external duplicateRows "out" TypeAlphaComparison.check 1 [a] first).1 = none ∧
    (ScopedSubtypeReads.completeTypes external duplicateRows "out" TypeAlphaComparison.check 1 [a] second).1 = none := by
  cbv

def openRows : List Atom := [row a (box (.var "element"))]

theorem open_closures_are_not_literal_cache_values :
    (ScopedSubtypeReads.completeTypes external openRows "out" TypeAlphaComparison.check 2 [a] first).1 ≠
      (ScopedSubtypeReads.completeTypes external openRows "out" TypeAlphaComparison.check 2 [a] second).1 := by
  cbv
  simp

theorem open_closures_still_complete_in_both_histories :
    (ScopedSubtypeReads.completeTypes external openRows "out" TypeAlphaComparison.check 2 [a] first).1.isSome = true ∧
    (ScopedSubtypeReads.completeTypes external openRows "out" TypeAlphaComparison.check 2 [a] second).1.isSome = true := by
  cbv

def cyclicRows : List Atom := [row (box (.var "x")) (box (.var "y"))]

theorem alpha_ancestor_closes_a_fresh_name_cycle :
    (ScopedSubtypeReads.completeTypes external cyclicRows "out" TypeAlphaComparison.check 1
      [box (.var "caller")] first).1 = some [box (.var "caller")] := by cbv

theorem literal_comparison_misses_that_cycle :
    (ScopedSubtypeReads.completeTypes external cyclicRows "out" (· == ·) 1
      [box (.var "caller")] first).1 = none := by cbv

def growingRows : List Atom := [row (.var "x") (box (.var "x"))]

theorem a_growing_prefix_is_still_unfinished :
    (ScopedSubtypeReads.completeTypes external growingRows "out" TypeAlphaComparison.check 2 [a] first).1 = none := by
  cbv

def nameSensitive (left : Atom) (_ : Atom) : Bool := left == .var "caller"

theorem a_name_sensitive_ancestor_test_changes_admission :
    accept nameSensitive (start [.var "caller"]) 0 (.var "other") = false ∧
    accept nameSensitive (renameState (Equiv.swap "caller" "renamed") (start [.var "caller"]))
      0 (renameAtom (Equiv.swap "caller" "renamed") (.var "other")) = true := by decide

theorem name_sensitive_is_not_equivariant : ¬ AlphaEquivariant nameSensitive := by
  intro equivariant
  have same := equivariant (Equiv.swap "caller" "renamed") (.var "caller") (.var "other")
  simp [nameSensitive, renameAtom] at same

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeClosureControls
