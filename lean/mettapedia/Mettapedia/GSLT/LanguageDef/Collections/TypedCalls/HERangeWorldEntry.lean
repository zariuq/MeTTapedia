import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeUntypedEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeWorldProtocol

/-! Source entry uses the reached world's lookup and locally earned
frontiers. The surrounding snapshot world is retained by these child steps. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeWorldEntry

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open HERangeWorldProtocol (Ports)
open HERangeUntypedEntry (rangeCall rangeInput)
open HERangeSuperposeSource (NumericOrEmpty)

theorem range_tuple {World : Type} (ports : Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (first : Entry.Value) (lower upper : Int)
    (firstRun : ∀ childLive, Stateful.AtomRel ports.environment ports.label world childLive scope first
      Atom.undefinedType before [(.grounded (.int lower), before)] world (policy := policy)) :
    Stateful.TupleRel ports.environment ports.label world live scope [.symbol "range", first, .grounded (.int upper)] before
      [(rangeCall lower upper, before)] world (policy := policy) :=
  HERangeUntypedEntry.range_tuple_of_sources ports.environment ports.label world policy before live scope first lower upper firstRun
    (fun childLive => HERangeUntypedEntry.symbol_undefined_of_query ports.environment ports.label world policy before
      childLive scope "range" (by decide) (ports.undefinedHead world _ before "range" (Or.inl rfl)))
    (fun childLive => ports.number world policy before childLive scope upper)

theorem ground_range_atom {World : Type} (ports : Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom) (rows : List Result)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (called : Stateful.CallRel ports.environment ports.label world live scope (rangeCall lower upper) expected before rows world (policy := policy))
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel ports.environment ports.label world live scope (rangeCall lower upper) expected before rows world (policy := policy) :=
  HERangeUntypedEntry.atom_of_call_in ports.environment ports.label world policy before live scope "range"
    [.grounded (.int lower), .grounded (.int upper)] (rangeCall lower upper) expected rows
    (by decide) notAtom notExpression (by simp [Entry.Value.erase, TypeSubst.typeVarsList, TypeSubst.typeVars])
    (ports.undefinedHead world _ before "range" (Or.inl rfl))
    (range_tuple ports world policy before (expected :: live) scope (.grounded (.int lower)) lower upper
      (fun childLive => ports.number world policy before childLive scope lower)) called numeric

theorem incremented_range_atom {World : Type} (ports : Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (rows : List Result)
    (called : Stateful.CallRel ports.environment ports.label world live scope (rangeCall (lower + 1) upper) Atom.undefinedType before rows world
      (policy := policy)) (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel ports.environment ports.label world live scope (rangeInput (HEBinaryNumericSource.addition.call lower 1) upper)
      Atom.undefinedType before rows world (policy := policy) :=
  HERangeUntypedEntry.atom_of_call_in ports.environment ports.label world policy before live scope "range"
    [HEBinaryNumericSource.addition.call lower 1, .grounded (.int upper)] (rangeCall (lower + 1) upper) Atom.undefinedType rows
    (by decide) (by decide) (by decide)
    (by simp [HEBinaryNumericSource.Operation.call, Entry.Value.erase, TypeSubst.typeVarsList, TypeSubst.typeVars])
    (ports.undefinedHead world _ before "range" (Or.inl rfl))
    (range_tuple ports world policy before (Atom.undefinedType :: live) scope (HEBinaryNumericSource.addition.call lower 1) (lower + 1) upper
      (fun childLive => ports.addition world policy before childLive scope lower 1)) called numeric

theorem empty_atom {World : Type} (ports : Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType) :
    Stateful.AtomRel ports.environment ports.label world live scope HERangeEquationFrontiers.emptyCall expected before
      [(.symbol "Empty", before)] world (policy := policy) := by
  have tuple : Stateful.TupleRel ports.environment ports.label world (expected :: live) scope [.symbol "empty"] before
      [(HERangeEquationFrontiers.emptyCall, before)] world (policy := policy) := by
    simpa [Completed.tupleSingleton, HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern, Entry.Value.ofAtom,
      Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      Stateful.TupleRel.singleton (HERangeUntypedEntry.symbol_undefined_of_query ports.environment ports.label world policy before
        (expected :: live) scope "empty" (by decide) (ports.undefinedHead world _ before "empty" (Or.inr rfl)))
  obtain ⟨work, frontier, pattern, body, bindings⟩ := ports.emptyFrontier world (expected :: live) before
  have called := HERangeEquationFrontiers.empty_call_from_frontier ports.environment ports.label world policy before live scope expected work
    frontier pattern body bindings (by
      simpa only [HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern, Entry.Value.erase_ofAtom] using
        ports.ordinary "empty" [] (by simp))
  have result := HERangeUntypedEntry.atom_of_call_in ports.environment ports.label world policy before live scope "empty" []
    HERangeEquationFrontiers.emptyCall expected [(.symbol "Empty", before)] (by decide) notAtom notExpression rfl
    (ports.undefinedHead world _ before "empty" (Or.inr rfl)) tuple called
    (by intro row member; cases List.mem_singleton.mp member; exact .empty)
  simpa [HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern, Entry.Value.ofAtom] using result

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeWorldEntry
