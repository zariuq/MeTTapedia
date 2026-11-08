import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalSourceInvocation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceActivation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEUnconstrainedRangeAlias

/-!
# The authored finite range program and its local primitive services

The source slice keeps the real range, if and empty equations. Only addition,
comparison and superpose are primitive. Their local services do not evaluate
recursive expressions; superpose emits its actual children with their marks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProgram

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom executeGroundedOp)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation

def superposeType : Atom := CompletedDelivery.arrowType [Atom.expressionType] Atom.undefinedType
def superposeDeclaration : Atom := .expression [.symbol ":", .symbol "superpose", superposeType]
def emptyPattern : Atom := .expression [.symbol "empty"]
def emptyRule : Atom := .expression [.symbol "=", emptyPattern, .symbol "Empty"]
def declaredSpace : Space := Space.ofList (HEIfSourceSelection.Range.space.atoms ++ [superposeDeclaration])
def space : Space := Space.ofList (declaredSpace.atoms ++ [emptyRule])

def localPrimitive : Entry.Value → GroundedResult Entry.Value
  | .expression _ (.symbol "+" :: arguments) =>
      match executeGroundedOp (.symbol "+") (arguments.map Entry.Value.erase) with
      | some value => .ok [(Entry.Value.ofAtom value, Bindings.empty)]
      | none => .incorrectArgument
  | .expression _ (.symbol ">=" :: arguments) =>
      match executeGroundedOp (.symbol ">=") (arguments.map Entry.Value.erase) with
      | some value => .ok [(Entry.Value.ofAtom value, Bindings.empty)]
      | none => .incorrectArgument
  | .expression _ (.symbol "superpose" :: .expression _ children :: _) =>
      .ok (children.map fun value => (value, Bindings.empty))
  | _ => .incorrectArgument

def dispatch : Spec.Eval.GroundedDispatch where
  executable operator := operator = .symbol "+" ∨ operator = .symbol ">=" ∨ operator = .symbol "superpose"
  outcome operator arguments outcome :=
    (localPrimitive (Entry.Value.ofAtom (.expression (operator :: arguments)))).map Entry.Value.erase = outcome

def environment (minimal : Minimal.Services) : WorldEnvironment Space Unit where
  view _ := id
  services := { WorldServices.readOnly minimal with
    groundedCall := fun _ _ call outcome _ => outcome = localPrimitive call }
  dispatch := dispatch
  lookup := scopedLookup

theorem addition_primitive (left right : Int) :
    localPrimitive (HEBinaryNumericSource.addition.call left right) =
      .ok [(.grounded (.int (left + right)), Bindings.empty)] := by
  simp only [localPrimitive, HEBinaryNumericSource.Operation.call, HEBinaryNumericSource.addition,
    List.map_cons, List.map_nil, Entry.Value.erase]
  have compute := HEBinaryNumericSource.addition_executes left right
  simp only [HEBinaryNumericSource.addition] at compute
  rw [compute]
  simp [Entry.Value.ofAtom]

theorem comparison_primitive (left right : Int) :
    localPrimitive (HEBinaryNumericSource.greaterEqual.call left right) =
      .ok [(.grounded (.bool (decide (left ≥ right))), Bindings.empty)] := by
  simp only [localPrimitive, HEBinaryNumericSource.Operation.call, HEBinaryNumericSource.greaterEqual,
    List.map_cons, List.map_nil, Entry.Value.erase]
  have compute := HEBinaryNumericSource.greaterEqual_executes left right
  simp only [HEBinaryNumericSource.greaterEqual] at compute
  rw [compute]
  simp [Entry.Value.ofAtom]

theorem superpose_primitive (readiness inner : Entry.Status) (children : List Entry.Value) :
    localPrimitive (.expression readiness [.symbol "superpose", .expression inner children]) =
      .ok (children.map fun value => (value, Bindings.empty)) := rfl

/-- A completed local row scan can be appended without changing earlier
physical occurrences or their fresh contextual records. -/
theorem frontier_append_row (base : Space) (live : List Atom) (query : Atom) (before : Bindings)
    (works : List EquationWork) (row : Atom)
    (frontier : EquationFrontierRel base live query before works)
    (miss : EquationRowResultsRel live query before base.atoms.length row []) :
    EquationFrontierRel (Space.ofList (base.atoms ++ [row])) live query before works := by
  cases frontier with
  | @completed blocks paired =>
      have last : List.Forall₂ (fun pair block => EquationRowResultsRel live query before pair.2 pair.1 block)
          [(row, base.atoms.length)] [[]] := .cons miss .nil
      have extended := List.rel_append paired last
      have scanned : EquationFrontierRel (Space.ofList (base.atoms ++ [row])) live query before
          (blocks ++ [[]]).flatten := by
        apply EquationFrontierRel.completed
        simpa [Space.ofList, List.zipIdx_append] using extended
      simpa using scanned

theorem declaration_irrelevant (live : List Atom) (query : Atom) (before : Bindings) (position : Nat) :
    EquationRowResultsRel live query before position superposeDeclaration [] :=
  .irrelevant position _ (by intro left right; simp [superposeDeclaration])

/-- Empty is an authored ground equation, not an invented primitive. A
different fixed source head cannot match it through any freshening or merge. -/
theorem empty_miss (live : List Atom) (name : String) (arguments : List Atom) (before : Bindings)
    (position : Nat) (different : name ≠ "empty") :
    EquationRowResultsRel live (.expression (.symbol name :: arguments)) before position emptyRule [] := by
  have identity : AlphaVariantRel live (.expression (.symbol name :: arguments)) before
      emptyPattern (.symbol "Empty") emptyPattern (.symbol "Empty") := by
    refine ⟨id, Function.injective_id, .expression (.cons (.symbol "empty") .nil), .symbol "Empty", ?_⟩
    intro key occurs
    rcases occurs with first | second
    · have member := atomOccurs_mem_typeVars first
      simp [emptyPattern, TypeSubst.typeVars, TypeSubst.typeVarsList] at member
    · have member := atomOccurs_mem_typeVars second
      simp [TypeSubst.typeVars] at member
  apply EquationRowResultsRel.miss position emptyPattern (.symbol "Empty") emptyPattern (.symbol "Empty") identity
  intro otherPattern otherBody alpha matched output candidate
  obtain ⟨rename, _, renamed, _, _⟩ := alpha
  have patternEq := EquationFreshening.alphaRename_eq renamed
  have fixed : otherPattern = emptyPattern := by simpa [emptyPattern, renameTypeVars] using patternEq
  obtain ⟨valuation, model⟩ := candidate.2.2
  have equal := ((UnifyCandidateRel.solutions ⟨matched, candidate.1, candidate.2⟩ valuation).mp model).1
  rw [fixed] at equal
  have heads := congrArg (fun atom : Atom => match atom with
    | .expression (.symbol head :: _) => some head
    | _ => none) equal
  exact different (by simpa [emptyPattern, applyTypeValuation] using heads)

theorem lift_if_frontier (live : List Atom) (before : Bindings) (condition : Bool)
    (yes no : Entry.Value) (works : List EquationWork)
    (frontier : EquationFrontierRel HEIfSourceSelection.Range.space live
      (HEConditionalEquationFrames.query condition yes no).erase before works) :
    EquationFrontierRel space live (HEConditionalEquationFrames.query condition yes no).erase before works := by
  have declared := frontier_append_row _ _ _ _ _ superposeDeclaration frontier (declaration_irrelevant _ _ _ _)
  exact frontier_append_row declaredSpace _ _ _ _ emptyRule declared
    (by simpa only [HEConditionalEquationFrames.query, Entry.Value.erase, List.map_cons, List.map_nil] using
      empty_miss live "if" [.grounded (.bool condition), yes.erase, no.erase] before declaredSpace.atoms.length (by decide))

theorem lift_range_frontier (live : List Atom) (before : Bindings) (lower upper : Int)
    (works : List EquationWork)
    (frontier : EquationFrontierRel HEIfSourceSelection.Range.space live
      (HEFreshEquationFrames.Range.call lower upper) before works) :
    EquationFrontierRel space live (HEFreshEquationFrames.Range.call lower upper) before works := by
  have declared := frontier_append_row _ _ _ _ _ superposeDeclaration frontier (declaration_irrelevant _ _ _ _)
  exact frontier_append_row declaredSpace _ _ _ _ emptyRule declared
    (empty_miss live "range" _ before declaredSpace.atoms.length (by decide))

theorem if_declared : getAtomTypes space (.symbol "if") = [(HEIfSourceSelection.signature "t").functionType] := rfl
theorem plus_declared : getAtomTypes space (.symbol "+") = [HEBinaryNumericSource.addition.signature.functionType] := rfl
theorem compare_declared : getAtomTypes space (.symbol ">=") = [HEBinaryNumericSource.greaterEqual.signature.functionType] := rfl
theorem superpose_declared : getAtomTypes space (.symbol "superpose") = [superposeType] := rfl
theorem range_undeclared : getAtomTypes space (.symbol "range") = [Atom.undefinedType] := rfl
theorem empty_undeclared : getAtomTypes space (.symbol "empty") = [Atom.undefinedType] := rfl
theorem empty_not_primitive : ¬dispatch.executable (.symbol "empty") := by simp [dispatch]

theorem plus_source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (left right : Int) :
    Stateful.AtomRel (environment minimal) space () live scope
      (HEBinaryNumericSource.addition.call left right) Atom.undefinedType before
      [(.grounded (.int (left + right)), before)] () (policy := policy) := by
  apply HEBinaryNumericSource.source_call (environment minimal) rfl rfl HEBinaryNumericSource.addition policy
    space () live scope before left right Atom.undefinedType (by decide) (by decide) (.undefinedLeft _ _) plus_declared
  · exact Or.inl rfl
  · rfl
  · rfl
  · exact (addition_primitive left right).symm

theorem compare_source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (left right : Int) :
    Stateful.AtomRel (environment minimal) space () live scope
      (HEBinaryNumericSource.greaterEqual.call left right) (.symbol "Bool") before
      [(.grounded (.bool (decide (left ≥ right))), before)] () (policy := policy) := by
  apply HEBinaryNumericSource.source_call (environment minimal) rfl rfl HEBinaryNumericSource.greaterEqual policy
    space () live scope before left right (.symbol "Bool") (by decide) (by decide)
    (HEContextualArithmeticSource.same_symbol_match "Bool" before.bindings (by decide) (by decide)) compare_declared
  · exact Or.inr (Or.inl rfl)
  · rfl
  · rfl
  · exact (comparison_primitive left right).symm

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProgram
