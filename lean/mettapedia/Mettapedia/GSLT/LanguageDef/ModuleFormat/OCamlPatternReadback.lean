import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlScalarReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionInstantiation
import Mettapedia.Languages.OCaml.PatternMatching

/-! Compiled pattern instances read back to source matches and the same
ordered binding values. The pattern compiler is evaluated once; runtime
matching continues to use its ordinary constructor/vector representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def patternAt (pattern : OCaml.MatchPattern) (start : Nat) : CompiledPattern :=
  ((compilePattern pattern).run start).1
def patternAfter (pattern : OCaml.MatchPattern) (start : Nat) : Nat :=
  ((compilePattern pattern).run start).2
def fieldsAt (patterns : List OCaml.MatchPattern) (start : Nat) : List Pattern × List Pattern :=
  ((compilePatternFields patterns).run start).1
def fieldsAfter (patterns : List OCaml.MatchPattern) (start : Nat) : Nat :=
  ((compilePatternFields patterns).run start).2

theorem valueList_as_values (items : List OCaml.Value) : valueList items = values (items.map value) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simpa only [valueList, values, linked, List.map_cons, List.foldr_cons] using
        congrArg (fun tail => node "MlValueCons" [value first, tail]) ih

theorem values_injective : Function.Injective values := by
  intro first
  induction first with
  | nil =>
    intro second same
    cases second with
    | nil => rfl
    | cons _ _ => simp [values, linked, node] at same
  | cons head rest ih =>
    intro second same
    cases second with
    | nil => simp [values, linked, node] at same
    | cons other tail =>
      have arguments := (Pattern.apply.inj same).2
      have sameHead := (List.cons.inj arguments).1
      have sameTail := (List.cons.inj (List.cons.inj arguments).2).1
      exact congrArg₂ List.cons sameHead (ih sameTail)

theorem literal_read_value (actual : OCaml.Value) :
    readLiteral? (value actual) = (match actual with | .literal datum => some datum | _ => none) := by
  cases actual with
  | literal datum => exact literal_roundTrip datum
  | tuple _ => simp [value, node, readLiteral?]
  | cons _ _ => simp [value, node, readLiteral?]
  | variant _ _ _ => simp [value, node, readLiteral?]
  | closure function _ => cases function <;> simp [value, node, readLiteral?]

theorem literal_instance_source {datum : OCaml.Literal} {actual : OCaml.Value}
    (same : literal datum = value actual) : actual = .literal datum := by
  have read := congrArg readLiteral? same
  rw [literal_roundTrip, literal_read_value] at read
  cases actual with
  | literal other => exact congrArg OCaml.Value.literal (Option.some.inj read).symm
  | tuple | cons | variant | closure => cases read

theorem patternAt_bind (start : Nat) : patternAt .bind start =
    ⟨hole ("pattern:" ++ toString start), [hole ("pattern:" ++ toString start)]⟩ := rfl
theorem patternAt_wildcard (start : Nat) : patternAt .wildcard start =
    ⟨hole ("pattern:" ++ toString start), []⟩ := rfl
theorem patternAt_literal (datum : OCaml.Literal) (start : Nat) : patternAt (.literal datum) start =
    ⟨literal datum, []⟩ := rfl

theorem patternAt_tuple (patterns : List OCaml.MatchPattern) (start : Nat) : patternAt (.tuple patterns) start =
    ⟨node "MlTuple" [values (fieldsAt patterns start).1], (fieldsAt patterns start).2⟩ := rfl

theorem patternAt_cons (head tail : OCaml.MatchPattern) (start : Nat) : patternAt (.cons head tail) start =
    ⟨node "MlCons" [(patternAt head start).term, (patternAt tail (patternAfter head start)).term],
      (patternAt head start).bindings ++ (patternAt tail (patternAfter head start)).bindings⟩ := rfl

theorem patternAt_variant (typeId constructor : Nat) (patterns : List OCaml.MatchPattern) (start : Nat) :
    patternAt (.variant typeId constructor patterns) start =
      ⟨node "MlVariant" [tag typeId constructor, values (fieldsAt patterns start).1], (fieldsAt patterns start).2⟩ := rfl

theorem fieldsAt_nil (start : Nat) : fieldsAt [] start = ([], []) := rfl
theorem fieldsAt_cons (first : OCaml.MatchPattern) (rest : List OCaml.MatchPattern) (start : Nat) :
    fieldsAt (first :: rest) start =
      ((patternAt first start).term :: (fieldsAt rest (patternAfter first start)).1,
       (patternAt first start).bindings ++ (fieldsAt rest (patternAfter first start)).2) := rfl

theorem pattern_instance_readback (pattern : OCaml.MatchPattern) :
    ∀ (start : Nat) (actual : OCaml.Value) (assignment : Bindings),
      applyBindings assignment (patternAt pattern start).term = value actual →
      ∃ boundValues, OCaml.matchPattern pattern actual = some boundValues ∧
        (patternAt pattern start).bindings.map (applyBindings assignment) = boundValues.map value := by
  refine OCaml.MatchPattern.rec
    (motive_1 := fun pattern => ∀ (start : Nat) (actual : OCaml.Value) (assignment : Bindings),
      applyBindings assignment (patternAt pattern start).term = value actual →
      ∃ boundValues, OCaml.matchPattern pattern actual = some boundValues ∧
        (patternAt pattern start).bindings.map (applyBindings assignment) = boundValues.map value)
    (motive_2 := fun patterns => ∀ (start : Nat) (actuals : List OCaml.Value) (assignment : Bindings),
      (fieldsAt patterns start).1.map (applyBindings assignment) = actuals.map value →
      ∃ boundValues, OCaml.matchFields patterns actuals = some boundValues ∧
        (fieldsAt patterns start).2.map (applyBindings assignment) = boundValues.map value)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro start actual assignment same
    refine ⟨[actual], rfl, ?_⟩
    simpa only [patternAt_bind, List.map_cons, List.map_nil] using congrArg (fun item => [item]) same
  · intro start actual assignment _
    exact ⟨[], rfl, rfl⟩
  · intro datum start actual assignment same
    simp only [patternAt_literal, apply_literal] at same
    cases literal_instance_source same
    exact ⟨[], by simp [OCaml.matchPattern], rfl⟩
  · intro patterns ih start actual assignment same
    simp only [patternAt_tuple, apply_node, List.map_cons, List.map_nil, values, apply_linked] at same
    cases actual with
    | literal datum =>
        have impossible := congrArg readLiteral? same
        change readLiteral? _ = readLiteral? (literal datum) at impossible
        rw [literal_roundTrip] at impossible
        simp [node, readLiteral?] at impossible
    | tuple actuals =>
        have fieldsSame := (List.cons.inj (Pattern.apply.inj same).2).1
        rw [valueList_as_values] at fieldsSame
        obtain ⟨boundValues, matched, output⟩ := ih start actuals assignment (values_injective fieldsSame)
        exact ⟨boundValues, matched, output⟩
    | cons first rest => simp [value, node] at same
    | variant typeId constructor actuals => simp [value, node] at same
    | closure function captured => cases function <;> simp [value, node] at same
  · intro head tail headIH tailIH start actual assignment same
    simp only [patternAt_cons, apply_node, List.map_cons, List.map_nil] at same
    cases actual with
    | literal datum =>
        have impossible := congrArg readLiteral? same
        change readLiteral? _ = readLiteral? (literal datum) at impossible
        rw [literal_roundTrip] at impossible
        simp [node, readLiteral?] at impossible
    | tuple actuals => simp [value, node] at same
    | cons first rest =>
        have arguments := (Pattern.apply.inj same).2
        have firstSame := (List.cons.inj arguments).1
        have restSame := (List.cons.inj (List.cons.inj arguments).2).1
        obtain ⟨firstBindings, firstMatch, firstOutput⟩ := headIH start first assignment firstSame
        obtain ⟨restBindings, restMatch, restOutput⟩ :=
          tailIH (patternAfter head start) rest assignment restSame
        refine ⟨firstBindings ++ restBindings, ?_, ?_⟩
        · simp [OCaml.matchPattern, firstMatch, restMatch]
        · simp only [patternAt_cons, List.map_append, firstOutput, restOutput]
    | variant typeId constructor actuals => simp [value, node] at same
    | closure function captured => cases function <;> simp [value, node] at same
  · intro typeId constructor patterns ih start actual assignment same
    simp only [patternAt_variant, apply_node, List.map_cons, List.map_nil, apply_tag, values, apply_linked] at same
    cases actual with
    | literal datum =>
        have impossible := congrArg readLiteral? same
        change readLiteral? _ = readLiteral? (literal datum) at impossible
        rw [literal_roundTrip] at impossible
        simp [node, readLiteral?] at impossible
    | tuple actuals => simp [value, node] at same
    | cons first rest => simp [value, node] at same
    | variant actualType actualConstructor actuals =>
        have arguments := (Pattern.apply.inj same).2
        have tagSame := (List.cons.inj arguments).1
        have fieldsSame := (List.cons.inj (List.cons.inj arguments).2).1
        obtain ⟨rfl, rfl⟩ := tag_injective tagSame
        rw [valueList_as_values] at fieldsSame
        obtain ⟨boundValues, matched, output⟩ := ih start actuals assignment (values_injective fieldsSame)
        exact ⟨boundValues, by simpa [OCaml.matchPattern] using matched, output⟩
    | closure function captured => cases function <;> simp [value, node] at same
  · intro start actuals assignment same
    cases actuals with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons first rest => simp [fieldsAt_nil] at same
  · intro first rest firstIH restIH start actuals assignment same
    simp only [fieldsAt_cons, List.map_cons] at same
    cases actuals with
    | nil => cases same
    | cons actual tail =>
        obtain ⟨headSame, tailSame⟩ := List.cons.inj same
        obtain ⟨headBindings, headMatch, headOutput⟩ := firstIH start actual assignment headSame
        obtain ⟨tailBindings, tailMatch, tailOutput⟩ :=
          restIH (patternAfter first start) tail assignment tailSame
        refine ⟨headBindings ++ tailBindings, ?_, ?_⟩
        · simp [OCaml.matchFields, headMatch, tailMatch]
        · simp only [fieldsAt_cons, List.map_append, headOutput, tailOutput]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
