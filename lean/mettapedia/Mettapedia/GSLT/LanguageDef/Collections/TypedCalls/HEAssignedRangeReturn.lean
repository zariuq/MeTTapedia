import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualArithmeticSource

/-!
# Literal return at an assigned schematic range

The expected type remains the variable written in the caller. Its actual
source type match reconciles the intrinsic type with the retained class and
returns the same whole record. The literal cast is not obtained by rewriting
the expected syntax to `Number` before evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEAssignedRangeReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Match.Merge Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Bindings.ScopeObservation

/-- The source match preserves a valued class, including repeated identical
class values. No selected evaluator output is assumed. -/
theorem valued_class_match (bindings : Bindings) (name : String) (value : Atom) (rest : List Atom)
    (closed : TypeSubst.typeVars value = [])
    (notUndefined : value ≠ Atom.undefinedType) (notAtom : value ≠ Atom.atomType)
    (classValues : bindings.classValues name = value :: rest) (agree : ValuesAgree (value :: rest)) :
    TypeMatchRel (.var name) value bindings bindings := by
  apply TypeMatchRel.structural (matched := Bindings.empty.assign name value)
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) notUndefined notAtom
  · apply MatchRel.varNonVar (HEFreshRangeFrame.closed_nonvariable value closed)
    apply semanticLoopFree_single_assignment
    intro occurs
    have present := atomOccurs_mem_typeVars occurs
    simp [closed] at present
  · apply MergeRel.mk (order := [.value name value])
    · simp [constraints, Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, List.eraseDups_cons]
    · exact .value (.same (by rw [classValues]) agree rfl) .nil

theorem number_class_match (bindings : Bindings) (name : String)
    (classValues : bindings.classValues name = [.symbol "Number"]) :
    TypeMatchRel (.var name) (.symbol "Number") bindings bindings :=
  valued_class_match bindings name (.symbol "Number") [] rfl (by decide) (by decide)
    classValues (by simp [ValuesAgree])

theorem number_class_renewal (policy : Policy) (frame : Frame) (name : String)
    (classValues : frame.bindings.classValues name = [.symbol "Number"]) :
    Frame.TypeRenewRel policy (.var name) (.symbol "Number") frame frame :=
  .unchanged (frame.preserved_type_match policy (number_class_match frame.bindings name classValues))

/-- An actual numeric source value casts at the retained variable demand,
preserving the caller frame and world exactly. -/
theorem number_at_range {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (name : String) (value : Int)
    (classValues : frame.bindings.classValues name = [.symbol "Number"]) :
    Stateful.AtomRel environment label world live scope (.grounded (.int value)) (.var name) frame
      [(.grounded (.int value), frame)] world (policy := policy) := by
  have queried := HEContextualArithmeticSource.scalar_lookup (environment.view world label)
    (invocationTypeScope scope live (.grounded (.int value)) (.var name) frame.bindings)
    frame (.int value) "Number" (.var name) rfl (by decide)
  have readValue : frame.read policy (.grounded (.int value)) = .grounded (.int value) := by
    simp [Frame.read, Entry.Value.substitute]
  have entered : Entry.Rel policy.reentry (Entry.Value.grounded (.int value)).status
      (.grounded (.int value)) (.var name) .cast := by
    apply Entry.Rel.cast (metaType := Atom.groundedType)
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact .grounded _
    · simp [Atom.atomType, Atom.groundedType, Atom.variableType]
    · exact Or.inr (Or.inl ⟨.int value, rfl⟩)
    · simp [Atom.unit]
  apply Stateful.AtomRel.cast (raw := [(.grounded (.int value), frame.bindings)])
  · simpa only [readValue, Entry.Value.erase] using entered
  · rw [lookup, readValue]
    simp only [Entry.Value.erase]
    apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
    · exact queried
    · rfl
    · simp
    · exact frame.preserved_type_match policy (number_class_match frame.bindings name classValues)
  · rw [readValue]
    exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase], .same frame,
      by simp [Entry.Value.erase]⟩ .nil

/-- Both names in the newly linked private class have the same ordered
singleton value; the right name need not have a direct assignment. -/
theorem alias_both_classes (bindings : Bindings) (left right : String) (value : Atom)
    (isolated : left ∉ bindings.eqVarsInOrder) (assigned : bindings.lookup left = some value)
    (fresh : right ∉ specBindingVars bindings) :
    (bindings.addEquality left right).classValues left = [value] ∧
    (bindings.addEquality left right).classValues right = [value] := by
  have first := HEFreshRangeAlias.alias_class_singleton bindings left right value isolated assigned fresh
  have different : left ≠ right := by
    intro same
    exact fresh (same ▸ HEFreshRangeAlias.assigned_in_support bindings left value assigned)
  have reachable : (EqualityClosure.edgeGraph (bindings.addEquality left right).equalities).Reachable left right :=
    ⟨.cons ⟨different, Or.inl (by simp [Bindings.addEquality])⟩ .nil⟩
  have sameClass := EqualityClosure.classValues_eq_of_reachable reachable
  exact ⟨first, sameClass.symm.trans first⟩

namespace Controls

def linked : Bindings :=
  (⟨[("range", .symbol "Number")], [("caller-a", "caller-b")]⟩ : Bindings).addEquality "range" "query"

theorem indirect_range_match_keeps_record :
    linked.lookup "query" = none ∧
    TypeMatchRel (.var "query") (.symbol "Number") linked linked := by
  constructor
  · rfl
  · exact number_class_match linked "query" (by decide)

theorem repeating_class_values_is_not_an_extra_cast_answer :
    let bindings : Bindings :=
      ⟨[("range", .symbol "Number"), ("query", .symbol "Number")], [("range", "query")]⟩
    TypeMatchRel (.var "query") (.symbol "Number") bindings bindings := by
  apply valued_class_match _ "query" (.symbol "Number") [.symbol "Number"]
    rfl (by decide) (by decide) (by decide)
  simp [ValuesAgree]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEAssignedRangeReturn
