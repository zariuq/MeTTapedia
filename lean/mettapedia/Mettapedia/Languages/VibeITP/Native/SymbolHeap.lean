import Mettapedia.Languages.VibeITP.Native.HeapCells

/-!
# Independent symbol meaning of native storage

A symbol is identified by its complete stored radix counter. Its independent
signature information is read from the kind, arity and binder cells. Pointer
equality is not used as a substitute for allocation identity. This relation
does not assert ownership, lifetime or preservation by a guest operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.SymbolHeap

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells

def kindCode : Spec.SymKind → Nat
  | .constant => 0
  | .fvar => 1

theorem kind_code_injective : Function.Injective kindCode := by
  intro left right same
  cases left <;> cases right <;> simp_all [kindCode]

def Meaning (memory : SourceMemory) (cell : SymbolCell) (symbol : Spec.SymId)
    (info : Spec.SymInfo) : Prop :=
  cell.kind.val = kindCode info.kind ∧
  cell.arity.val = info.arity ∧
  words memory cell.binders = some info.binders ∧
  ∃ digits, words memory cell.identity = some digits ∧
    identityValue digits = RadixCounters.symbolIdentity symbol

def At (memory : SourceMemory) (address : Address) (symbol : Spec.SymId)
    (info : Spec.SymInfo) : Prop :=
  ∃ cell, sourceRead memory address = some cell.sourceValue ∧ Meaning memory cell symbol info

theorem meaning_unique (memory : SourceMemory) (cell : SymbolCell)
    (first second : Spec.SymId) (firstInfo secondInfo : Spec.SymInfo)
    (left : Meaning memory cell first firstInfo) (right : Meaning memory cell second secondInfo) :
    first = second ∧ firstInfo = secondInfo := by
  rcases left with ⟨firstKind, _, firstBinders, firstDigits, firstRead, firstIdentity⟩
  rcases right with ⟨secondKind, _, secondBinders, secondDigits, secondRead, secondIdentity⟩
  have sameDigits : firstDigits = secondDigits := Option.some.inj (firstRead.symm.trans secondRead)
  have sameSymbol : first = second := RadixCounters.symbolIdentity_injective
    (firstIdentity.symm.trans ((congrArg identityValue sameDigits).trans secondIdentity))
  have sameKind : firstInfo.kind = secondInfo.kind :=
    kind_code_injective (firstKind.symm.trans secondKind)
  have sameBinders : firstInfo.binders = secondInfo.binders :=
    Option.some.inj (firstBinders.symm.trans secondBinders)
  refine ⟨sameSymbol, ?_⟩
  cases firstInfo; cases secondInfo
  cases sameKind; cases sameBinders
  rfl

theorem at_unique (memory : SourceMemory) (address : Address)
    (first second : Spec.SymId) (firstInfo secondInfo : Spec.SymInfo)
    (left : At memory address first firstInfo) (right : At memory address second secondInfo) :
    first = second ∧ firstInfo = secondInfo := by
  obtain ⟨firstCell, firstRead, firstMeaning⟩ := left
  obtain ⟨secondCell, secondRead, secondMeaning⟩ := right
  have sameCell := symbol_cell_unique memory address firstCell secondCell firstRead secondRead
  cases sameCell
  exact meaning_unique memory firstCell first second firstInfo secondInfo firstMeaning secondMeaning

theorem kind_is_applicable (memory : SourceMemory) (cell : SymbolCell)
    (symbol : Spec.SymId) (info : Spec.SymInfo) (meaning : Meaning memory cell symbol info) :
    cell.kind.val ≤ 1 := by
  rw [meaning.1]
  cases info.kind <;> decide

theorem marker_not_applicable (memory : SourceMemory) (cell : SymbolCell)
    (marker : 1 < cell.kind.val) : ∀ symbol info, ¬ Meaning memory cell symbol info := by
  intro symbol info meaning
  exact Nat.not_lt_of_ge (kind_is_applicable memory cell symbol info meaning) marker

theorem binder_count_exact (memory : SourceMemory) (cell : SymbolCell)
    (symbol : Spec.SymId) (info : Spec.SymInfo) (meaning : Meaning memory cell symbol info) :
    cell.binders.length.val = cell.arity.val := by
  have length := words_length memory cell.binders info.binders meaning.2.2.1
  exact length.symm.trans meaning.2.1.symm

theorem stored_binders_bounded (memory : SourceMemory) (cell : SymbolCell)
    (symbol : Spec.SymId) (info : Spec.SymInfo) (meaning : Meaning memory cell symbol info) :
    ∀ value ∈ info.binders, value < Spec.wordBound :=
  words_bounded memory cell.binders info.binders meaning.2.2.1

theorem stored_identity_nonempty (memory : SourceMemory) (cell : SymbolCell)
    (symbol : Spec.SymId) (info : Spec.SymInfo) (meaning : Meaning memory cell symbol info) :
    cell.identity.length.val ≠ 0 := by
  obtain ⟨digits, read, identity⟩ := meaning.2.2.2
  have length := words_length memory cell.identity digits read
  intro zero
  have noDigits : digits = [] := List.length_eq_zero_iff.mp (length.trans zero)
  rw [noDigits] at identity
  change 0 = RadixCounters.symbolIdentity symbol at identity
  cases symbol with
  | fresh index =>
      simp only [RadixCounters.symbolIdentity] at identity
      omega
  | builtin builtin => cases builtin <;> simp [RadixCounters.symbolIdentity, Spec.Builtin.slot] at identity

theorem different_symbols_cannot_share_live_representation (memory : SourceMemory) (address : Address)
    (first second : Spec.SymId) (firstInfo secondInfo : Spec.SymInfo) (different : first ≠ second)
    (left : At memory address first firstInfo) : ¬ At memory address second secondInfo := by
  intro right
  exact different (at_unique memory address first second firstInfo secondInfo left right).1

end Mettapedia.Languages.VibeITP.Native.SymbolHeap
