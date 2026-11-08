import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProtocol

/-!
# Read-only range execution inside a larger world and source context

Local frontier evidence replaces equality with the isolated source space.
The world is retained during range operations; a surrounding collector may
change its snapshot store before or after this child execution. No port
contains a completed range run or a completed conditional body.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeWorldProtocol

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation
open HERangeSuperposeSource (NumericOrEmpty)

structure Ports (World : Type) where
  environment : WorldEnvironment Space World
  label : Space
  ordinary : ∀ (name : String) (arguments : List Atom), name ∈ ["range", "if", "empty"] →
    NonGroundedCallRel environment.dispatch (.expression (.symbol name :: arguments))
  rangeFrontier : ∀ (world : World) (policy : Policy) (live : List Atom) (before : Frame) (lower upper : Int),
    ∃ (work : EquationWork) (after : Frame),
      EquationFrontierRel (environment.view world label) live (HEFreshEquationFrames.Range.call lower upper) before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (Entry.Value.ofAtom (HEFreshEquationFrames.Range.call lower upper))
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom
        (HEFreshEquationFrames.Range.bodyAt (HEFreshEquationFrames.Range.number lower) (HEFreshEquationFrames.Range.number upper))
  conditionalFrontier : ∀ (world : World) (policy : Policy) (live : List Atom) (before : Frame)
    (condition : Bool) (yes no : Entry.Value),
    TypeSubst.typeVars yes.erase = [] → TypeSubst.typeVars no.erase = [] →
    ∃ (work : EquationWork) (after : Frame),
      EquationFrontierRel (environment.view world label) live (HEConditionalEquationFrames.query condition yes no).erase
        before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (HEConditionalEquationFrames.query condition yes no)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = if condition then yes else no
  emptyFrontier : ∀ (world : World) (live : List Atom) (before : Frame),
    ∃ work : EquationWork,
      EquationFrontierRel (environment.view world label) live HERangeSourceProgram.emptyPattern before.bindings [work] ∧
      work.pattern = HERangeSourceProgram.emptyPattern ∧ work.body = .symbol "Empty" ∧ work.bindings = before.bindings
  undefinedHead : ∀ (world : World) (names : List String) (before : Frame) (name : String),
    name = "range" ∨ name = "empty" →
    environment.lookup names (environment.view world label) before.bindings (.symbol name) Atom.undefinedType [Atom.undefinedType]
  number : ∀ (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (value : Int),
    Stateful.AtomRel environment label world live scope (.grounded (.int value)) Atom.undefinedType before
      [(.grounded (.int value), before)] world (policy := policy)
  addition : ∀ (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (left right : Int),
    Stateful.AtomRel environment label world live scope (HEBinaryNumericSource.addition.call left right) Atom.undefinedType before
      [(.grounded (.int (left + right)), before)] world (policy := policy)
  conditional : ∀ (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom),
    expected = .symbol "Number" ∨ expected = Atom.undefinedType →
    ∃ name selected after,
      environment.arguments.selection (environment.view world label) environment.lookup policy live scope
        (HEFreshEquationFrames.Range.bodyAt (HEFreshEquationFrames.Range.number lower) (HEFreshEquationFrames.Range.number upper))
        (.symbol "if") expected before (.selected (HEIfSourceSelection.signature name) [selected]) ∧
      Stateful.FunctionRel environment label world
        (invocationReturnType (HEIfSourceSelection.signature name) :: live) scope expected (HEIfSourceSelection.signature name)
        (.symbol "if") (HEIfSourceActivation.operands lower upper) selected
        [(HEIfSourceActivation.reachedCall lower upper, after)] world (policy := policy)
  superpose : ∀ (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (items : List Entry.Value) (outputs : List (List Result)) (expected : Atom),
    expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
    TypeSubst.typeVarsList (items.map Entry.Value.erase) = [] → items ≠ [] →
    List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel environment label world live scope item Atom.undefinedType before rows world (policy := policy)) items outputs →
    (∀ row ∈ outputs.flatten, NumericOrEmpty row.1) →
    Stateful.AtomRel environment label world live scope (HERangeSuperposeSource.call items) expected before outputs.flatten world
      (policy := policy)

/-- The previously checked isolated profile is one instance. Its complete
frontiers are reused; no program result is imported into the interface. -/
def ofIsolated (source : HERangeSourceProtocol.Ports) : Ports Unit where
  environment := source.environment
  label := HERangeSourceProgram.space
  ordinary name arguments member := by
    rw [source.dispatch]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [NonGroundedCallRel, Minimal.HostCall, HERangeSourceProgram.dispatch, Minimal.embeddedInstruction]
  rangeFrontier world policy live before lower upper := by
    cases world
    simpa only [source.view] using HERangeEquationFrontiers.range_frontier policy live before lower upper
  conditionalFrontier world policy live before condition yes no yesClosed noClosed := by
    cases world
    obtain ⟨work, after, frontier, bound, unified, read⟩ :=
      HEConditionalSourceFrontier.complete_singleton policy live before condition yes no yesClosed noClosed
    refine ⟨work, after, ?_, bound, unified, read⟩
    rw [source.view]
    exact HERangeSourceProgram.lift_if_frontier _ _ _ _ _ _ frontier
  emptyFrontier world live before := by
    cases world
    refine ⟨HERangeEquationFrontiers.emptyWork before, ?_, rfl, rfl, rfl⟩
    simpa only [source.view] using HERangeEquationFrontiers.empty_frontier live before
  undefinedHead world names before name member := by
    cases world
    simpa only [source.view] using source.undefinedHead names before name member
  number world := by cases world; exact source.number
  addition world := by cases world; exact source.addition
  conditional world policy before live scope lower upper expected demand := by
    cases world
    simpa only [source.view] using source.conditional policy before live scope lower upper expected demand
  superpose world := by cases world; exact source.superpose

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeWorldProtocol
