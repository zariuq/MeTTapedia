import Mettapedia.Languages.VibeITP.Native.TermHeap

/-! A stored finite term graph has a unique independent term interpretation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeap

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells

theorem stored_head_unique {memory : SourceMemory} {address : Address}
    {left right : TermCell} {leftAddress rightAddress : Address} {leftHead rightHead : SymbolCell}
    (leftRead : sourceRead memory address = some left.sourceValue)
    (rightRead : sourceRead memory address = some right.sourceValue)
    (leftPointer : left.symbol = some leftAddress) (rightPointer : right.symbol = some rightAddress)
    (leftStored : sourceRead memory leftAddress = some leftHead.sourceValue)
    (rightStored : sourceRead memory rightAddress = some rightHead.sourceValue) :
    left = right ∧ leftHead = rightHead := by
  have cells := term_cell_unique memory address left right leftRead rightRead
  cases cells
  have pointers := Option.some.inj (leftPointer.symm.trans rightPointer)
  cases pointers
  exact ⟨rfl, symbol_cell_unique memory leftAddress leftHead rightHead leftStored rightStored⟩

theorem unique {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {address : Address} {term : Spec.Term} (represented : At memory signature markers address term) :
    ∀ other, At memory signature markers address other → term = other := by
  refine At.rec
    (motive_1 := fun address term _ => ∀ other, At memory signature markers address other → term = other)
    (motive_2 := fun addresses terms _ => ∀ others, ListAt memory signature markers addresses others → terms = others)
    ?_ ?_ ?_ ?_ ?_ represented
  · intro address cell marker stored symbol markerStored kind depth free noLiteral noArguments other second
    cases second with
    | @bvar _ otherCell _ otherRead _ _ _ _ _ _ _ =>
        have same := term_cell_unique memory address cell otherCell stored otherRead
        cases same
        rfl
    | @lit _ otherCell otherMarker bytes otherRead otherSymbol otherStored otherKind _ _ _ _ _ =>
        have same := (stored_head_unique stored otherRead symbol otherSymbol markerStored otherStored).2
        have clash := congrArg (fun cell : SymbolCell => cell.kind.val) same
        omega
    | @app _ symbolAddress otherCell otherSymbol info addresses terms otherRead otherHead otherMeaning
        _ _ _ _ _ _ _ =>
        obtain ⟨otherMarker, otherStored, meaning⟩ := otherMeaning
        have same := (stored_head_unique stored otherRead symbol otherHead markerStored otherStored).2
        have bound := SymbolHeap.kind_is_applicable memory otherMarker otherSymbol info meaning
        have clash := congrArg (fun cell : SymbolCell => cell.kind.val) same
        omega
  · intro address cell marker bytes stored symbol markerStored kind contents bounded depth free noArguments other second
    cases second with
    | @bvar _ otherCell otherMarker otherRead otherSymbol otherStored otherKind _ _ _ _ =>
        have same := (stored_head_unique stored otherRead symbol otherSymbol markerStored otherStored).2
        have clash := congrArg (fun cell : SymbolCell => cell.kind.val) same
        omega
    | @lit _ otherCell _ otherBytes otherRead _ _ _ otherContents _ _ _ _ =>
        have same := term_cell_unique memory address cell otherCell stored otherRead
        cases same
        exact congrArg Spec.Term.lit (Option.some.inj (contents.symm.trans otherContents))
    | @app _ symbolAddress otherCell otherSymbol info addresses terms otherRead otherHead otherMeaning
        _ _ _ _ _ _ _ =>
        obtain ⟨otherMarker, otherStored, meaning⟩ := otherMeaning
        have same := (stored_head_unique stored otherRead symbol otherHead markerStored otherStored).2
        have bound := SymbolHeap.kind_is_applicable memory otherMarker otherSymbol info meaning
        have clash := congrArg (fun cell : SymbolCell => cell.kind.val) same
        omega
  · intro address symbolAddress cell symbol info addresses terms stored head symbolStored declared
      contents children arity depth free noLiteral childUnique other second
    cases second with
    | @bvar _ otherCell otherMarker otherRead otherHead otherStored otherKind _ _ _ _ =>
        obtain ⟨marker, markerStored, meaning⟩ := symbolStored
        have same := (stored_head_unique stored otherRead head otherHead markerStored otherStored).2
        have bound := SymbolHeap.kind_is_applicable memory marker symbol info meaning
        have clash := congrArg (fun cell : SymbolCell => cell.kind.val) same
        omega
    | @lit _ otherCell otherMarker bytes otherRead otherHead otherStored otherKind _ _ _ _ _ =>
        obtain ⟨marker, markerStored, meaning⟩ := symbolStored
        have same := (stored_head_unique stored otherRead head otherHead markerStored otherStored).2
        have bound := SymbolHeap.kind_is_applicable memory marker symbol info meaning
        have clash := congrArg (fun cell : SymbolCell => cell.kind.val) same
        omega
    | @app _ otherAddress otherCell otherSymbol otherInfo otherAddresses otherTerms otherRead otherHead
        otherSymbolStored _ otherContents otherChildren _ _ _ _ =>
        have sameCell := term_cell_unique memory address cell otherCell stored otherRead
        cases sameCell
        have sameAddress := Option.some.inj (head.symm.trans otherHead)
        cases sameAddress
        have sameSymbol := (SymbolHeap.at_unique memory symbolAddress symbol otherSymbol info otherInfo
          symbolStored otherSymbolStored).1
        have sameAddresses := Option.some.inj (contents.symm.trans otherContents)
        cases sameAddresses
        exact congrArg₂ Spec.Term.app sameSymbol (childUnique otherTerms otherChildren)
  · intro others other
    cases other
    rfl
  · intro address term addresses terms head tail headUnique tailUnique others other
    cases other with
    | cons otherHead otherTail =>
        exact congrArg₂ List.cons (headUnique _ otherHead) (tailUnique _ otherTail)

theorem list_unique {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {addresses : List Address} {terms : List Spec.Term}
    (represented : ListAt memory signature markers addresses terms) :
    ∀ others, ListAt memory signature markers addresses others → terms = others := by
  induction addresses generalizing terms with
  | nil => intro others other; cases represented; cases other; rfl
  | cons address addresses ih =>
      intro others other
      cases represented with
      | cons head tail =>
          cases other with
          | cons otherHead otherTail =>
              exact congrArg₂ List.cons (unique head _ otherHead) (ih tail _ otherTail)

theorem missing_cell_unrepresented {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {address : Address} (missing : sourceRead memory address = none) :
    ∀ term, ¬ At memory signature markers address term := by
  intro term represented
  obtain ⟨cell, stored, _, _⟩ := stored_cache represented
  rw [missing] at stored
  contradiction

theorem different_terms_cannot_share_representation {memory : SourceMemory} {signature : Spec.Sig}
    {markers : Markers} {address : Address} {first second : Spec.Term}
    (different : first ≠ second) (represented : At memory signature markers address first) :
    ¬ At memory signature markers address second := by
  intro other
  exact different (unique represented second other)

end Mettapedia.Languages.VibeITP.Native.TermHeap
