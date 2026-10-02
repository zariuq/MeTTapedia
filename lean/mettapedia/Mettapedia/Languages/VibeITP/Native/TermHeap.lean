import Mettapedia.Languages.VibeITP.Native.SymbolHeap

/-!
# Finite native term graphs and the independent Vibe term syntax

The relation follows the actual argument-address arrays and reads each stored
symbol through its full identity. It permits sharing: repeated addresses may
occur in the argument list. It does not grant allocation ownership or infer
pointer injectivity from copied record contents. The distinguished marker
addresses must be obtained from the theory's actual builtin table when this
relation is connected to guest execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeap

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells

structure Markers where
  boundVariable : Address
  literal : Address
  deriving DecidableEq, Repr

mutual
  inductive At (memory : SourceMemory) (signature : Spec.Sig) (markers : Markers) :
      Address → Spec.Term → Prop where
    | bvar {address : Address} {cell : TermCell} {marker : SymbolCell}
        (stored : sourceRead memory address = some cell.sourceValue)
        (symbol : cell.symbol = some markers.boundVariable)
        (markerStored : sourceRead memory markers.boundVariable = some marker.sourceValue)
        (kind : marker.kind.val = 2)
        (depth : cell.depth.val = cell.number.val + 1)
        (free : cell.hasFreeVariable = false)
        (noLiteral : cell.literal.length.val = 0)
        (noArguments : cell.arguments.length.val = 0) :
        At memory signature markers address (.bvar cell.number.val)
    | lit {address : Address} {cell : TermCell} {marker : SymbolCell} {bytes : List UInt8}
        (stored : sourceRead memory address = some cell.sourceValue)
        (symbol : cell.symbol = some markers.literal)
        (markerStored : sourceRead memory markers.literal = some marker.sourceValue)
        (kind : marker.kind.val = 3)
        (contents : literal memory cell.literal = some bytes)
        (bounded : cell.literal.length.val + 8 < Spec.wordBound)
        (depth : cell.depth.val = 0)
        (free : cell.hasFreeVariable = false)
        (noArguments : cell.arguments.length.val = 0) :
        At memory signature markers address (.lit bytes)
    | app {address symbolAddress : Address} {cell : TermCell} {symbol : Spec.SymId}
        {info : Spec.SymInfo} {addresses : List Address} {terms : List Spec.Term}
        (stored : sourceRead memory address = some cell.sourceValue)
        (head : cell.symbol = some symbolAddress)
        (symbolStored : SymbolHeap.At memory symbolAddress symbol info)
        (declared : signature symbol = some info)
        (contents : references memory cell.arguments = some addresses)
        (children : ListAt memory signature markers addresses terms)
        (arity : cell.arguments.length.val = info.arity)
        (depth : cell.depth.val = Spec.depth signature (.app symbol terms))
        (free : cell.hasFreeVariable = Spec.hasFvar signature (.app symbol terms))
        (noLiteral : cell.literal.length.val = 0) :
        At memory signature markers address (.app symbol terms)

  inductive ListAt (memory : SourceMemory) (signature : Spec.Sig) (markers : Markers) :
      List Address → List Spec.Term → Prop where
    | nil : ListAt memory signature markers [] []
    | cons {address : Address} {term : Spec.Term} {addresses : List Address} {terms : List Spec.Term}
        (head : At memory signature markers address term)
        (tail : ListAt memory signature markers addresses terms) :
        ListAt memory signature markers (address :: addresses) (term :: terms)
end

theorem list_length {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {addresses : List Address} {terms : List Spec.Term}
    (represented : ListAt memory signature markers addresses terms) :
    terms.length = addresses.length := by
  induction addresses generalizing terms with
  | nil => cases represented; rfl
  | cons address addresses ih =>
      cases represented with
      | cons head tail => simp only [List.length_cons, ih tail]

theorem stored_cache {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {address : Address} {term : Spec.Term} (represented : At memory signature markers address term) :
    ∃ cell : TermCell, sourceRead memory address = some cell.sourceValue ∧
      cell.depth.val = Spec.depth signature term ∧
      cell.hasFreeVariable = Spec.hasFvar signature term := by
  cases represented with
  | bvar stored _ _ _ depth free _ _ => exact ⟨_, stored, depth, free⟩
  | lit stored _ _ _ _ _ depth free _ => exact ⟨_, stored, depth, free⟩
  | app stored _ _ _ _ _ _ depth free _ => exact ⟨_, stored, depth, free⟩

theorem cache_unique {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {address : Address} {term : Spec.Term} (represented : At memory signature markers address term)
    (cell : TermCell) (read : sourceRead memory address = some cell.sourceValue) :
    cell.depth.val = Spec.depth signature term ∧
      cell.hasFreeVariable = Spec.hasFvar signature term := by
  obtain ⟨actual, stored, depth, free⟩ := stored_cache represented
  have same := term_cell_unique memory address cell actual read stored
  cases same
  exact ⟨depth, free⟩

theorem wellFormed {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {address : Address} {term : Spec.Term} (represented : At memory signature markers address term) :
    Spec.WellFormed signature term = true := by
  refine At.rec (motive_1 := fun _ term _ => Spec.WellFormed signature term = true)
    (motive_2 := fun _ terms _ => Spec.WellFormedList signature terms = true)
    ?_ ?_ ?_ ?_ ?_ represented
  · intro address cell marker stored symbol markerStored kind depth free noLiteral noArguments
    simp only [Spec.WellFormed, decide_eq_true_eq]
    rw [← depth]
    exact cell.depth.isLt
  · intro address cell marker bytes stored symbol markerStored kind contents bounded depth free noArguments
    simp only [Spec.WellFormed, decide_eq_true_eq]
    rw [literal_length memory cell.literal bytes contents]
    exact bounded
  · intro address symbolAddress cell symbol info addresses terms stored head symbolStored declared
      contents children arity depth free noLiteral formed
    have shape := (list_length children).trans
      ((references_length memory cell.arguments addresses contents).trans arity)
    simp only [Spec.WellFormed, declared, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨shape, formed⟩
  · rfl
  · intro address term addresses terms head tail formedHead formedTail
    simpa only [Spec.WellFormedList, Bool.and_eq_true] using And.intro formedHead formedTail

theorem list_wellFormed {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {addresses : List Address} {terms : List Spec.Term}
    (represented : ListAt memory signature markers addresses terms) :
    Spec.WellFormedList signature terms = true := by
  induction addresses generalizing terms with
  | nil => cases represented; rfl
  | cons address addresses ih =>
      cases represented with
      | cons head tail =>
          simpa only [Spec.WellFormedList, Bool.and_eq_true] using And.intro (wellFormed head) (ih tail)

theorem shared_child_retained_twice {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {address : Address} {term : Spec.Term} (represented : At memory signature markers address term) :
    ListAt memory signature markers [address, address] [term, term] :=
  .cons represented (.cons represented .nil)

theorem overflowing_bound_variable_unrepresentable (memory : SourceMemory)
    (signature : Spec.Sig) (markers : Markers) (address : Address) :
    ¬ At memory signature markers address (.bvar (Spec.wordBound - 1)) := by
  intro represented
  have formed := wellFormed represented
  change decide (Spec.wordBound - 1 + 1 < Spec.wordBound) = true at formed
  have falseGuard : decide (Spec.wordBound - 1 + 1 < Spec.wordBound) = false := by decide +kernel
  rw [falseGuard] at formed
  contradiction

end Mettapedia.Languages.VibeITP.Native.TermHeap
