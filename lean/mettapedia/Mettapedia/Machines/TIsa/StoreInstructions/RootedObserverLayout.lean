import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardInstall

/-!
# One occurrence window for multiple observers

Each observer has one pattern coordinate. All observers of
the same snapshot share a single suffix of occurrence roots.
The physical words carry values, not identities. Identity
is taken from exactly the original occurrence at that offset.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.RootedObserverLayout

open Mettapedia.Logic.LP
open NativeRootSlices (View)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def operands (patterns : List (Term σ)) (atoms : List (SymbolicExecution.Atom σ)) : List (Term σ) :=
  patterns ++ atoms.map Prod.snd

def view (patterns : List (Term σ)) (atoms : List (SymbolicExecution.Atom σ)) (words : Array Word)
    (length : words.size = patterns.length + atoms.length) (pattern : Fin patterns.length) : View words :=
  ⟨⟨pattern.val, by rw [length]; exact pattern.isLt.trans_le (Nat.le_add_right _ _)⟩,
    patterns.length, atoms.length, length.ge⟩

theorem width (patterns : List (Term σ)) (atoms : List (SymbolicExecution.Atom σ)) (words : Array Word)
    (length : words.size = patterns.length + atoms.length) (pattern : Fin patterns.length) :
    (view patterns atoms words length pattern).occurrences.size = atoms.length :=
  (view patterns atoms words length pattern).size

theorem read_width (symbols : UnifierHeaders.Symbols σ) (graph : PackedTerms.Arena) (words : Array Word)
    (patterns : List (Term σ)) (atoms : List (SymbolicExecution.Atom σ)) (answer : Subst σ)
    (decoded : PackedRootedMeaning.roots symbols graph words = some ((operands patterns atoms).map answer.applyTerm)) :
    words.size = patterns.length + atoms.length := by
  have length := (PackedOccursPrefix.mapM_coordinates (PackedTerms.lookup symbols graph) words.toList
    ((operands patterns atoms).map answer.applyTerm) decoded).1
  simpa only [operands, List.length_map, List.length_append, Array.length_toList] using length.symm

/-- Reading the root directory by coordinates after the
native solve constructs the normalized guard input. There
is no second graph traversal in the emitted path. -/
theorem normalized (symbols : UnifierHeaders.Symbols σ) (graph : PackedTerms.Arena) (words : Array Word)
    (patterns : List (Term σ)) (atoms : List (SymbolicExecution.Atom σ)) (answer : Subst σ)
    (decoded : PackedRootedMeaning.roots symbols graph words = some ((operands patterns atoms).map answer.applyTerm))
    (size : words.size = patterns.length + atoms.length) (pattern : Fin patterns.length) :
    let selected := view patterns atoms words size pattern
    NativeGuardLoop.Normalized symbols graph selected.needle selected.occurrences
        (answer.applyTerm patterns[pattern]) (NativeGuardRegion.operand answer atoms (width patterns atoms words size pattern)) := by
  let selected := view patterns atoms words size pattern
  obtain ⟨_, atNeedle, atOccurrence⟩ := selected.read symbols graph _ decoded
  constructor
  · change PackedTerms.lookup symbols graph selected.needle = some (answer.applyTerm patterns[pattern])
    have coordinate : selected.pattern.val = pattern.val := rfl
    have within : selected.pattern.val < patterns.length := coordinate.symm ▸ pattern.isLt
    simp only [operands, List.getElem_map, List.getElem_append_left within] at atNeedle
    simpa only [coordinate, Fin.getElem_fin] using atNeedle
  · intro i
    have found := atOccurrence i
    have ordinal : selected.offset = patterns.length := rfl
    have intoRight : patterns.length ≤ selected.offset + i.val := by rw [ordinal]; omega
    simp only [operands, List.getElem_map, List.getElem_append_right intoRight] at found
    have back : selected.offset + i.val - patterns.length = i.val := by rw [ordinal]; omega
    simpa only [List.getElem_map, back, NativeGuardRegion.operand] using found

namespace Examples

private def entries : Array Word := #[0, 3, 7, 7]
private def first : View entries := ⟨⟨0, by decide⟩, 2, 2, by decide⟩
private def second : View entries := ⟨⟨1, by decide⟩, 2, 2, by decide⟩

theorem differing_patterns_share_a_window :
    first.needle ≠ second.needle ∧ first.occurrences = second.occurrences := by decide +kernel

theorem one_handle_in_two_slots_is_not_one_occurrence :
    first.occurrences ≠ #[7] := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.RootedObserverLayout
