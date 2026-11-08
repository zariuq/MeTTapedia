import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentReturn

/-!
# Local HE completion admission and field provenance

The summary represents well-formed HeReturnAnalysis flags: scalar and variable
possibilities, at most one expression publication mode, or unknown. Its join,
field, whole-template, structural-range and final-entry operations follow the
native analysis. RAW is a preservation obligation, not an assertion that the
runtime value is unmarked.

Ready operands use their actual marks; source operands carrying a root mark
are refused before analysis. Constructor-normal-form admission is a separate
source-dependent port here, not equated with an inferred type. Whole source
call/body analysis and that port's operational adequacy are separate from the
local annotation/projection laws below. Native allocation/flag codecs are not
asserted by these semantic definitions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed

inductive Marking where
  | completed | raw | collected
  deriving DecidableEq, Repr

inductive Summary where
  | unknown
  | known (scalar hasVariable : Bool) (marking : Option Marking)
  deriving DecidableEq, Repr

def scalar : Summary := .known true false none
def freeVariable : Summary := .known false true none
def value : Summary := .known true false (some .completed)
def raw : Summary := .known false false (some .raw)
def collected : Summary := .known false false (some .collected)

def join : Summary → Summary → Summary
  | .unknown, _ | _, .unknown => .unknown
  | .known s v none, .known t w marking
  | .known s v marking, .known t w none => .known (s || t) (v || w) marking
  | .known s v (some first), .known t w (some second) =>
      if first = second then .known (s || t) (v || w) (some first) else .unknown

/-- Exact field rule of he_return_bind; scalar-only input cannot justify
an expression-pattern field. -/
def part : Summary → Summary
  | .known _ false (some .completed) | .known _ false (some .collected) => value
  | _ => .unknown

/-- A whole template is evaluated where used, unlike a held data position. -/
def template : Summary → Summary
  | .known _ _ (some .raw) | .known _ _ (some .collected) => .unknown
  | summary => summary

def structural : Summary → Summary
  | .known scalar false none => .known scalar false none
  | .known scalar false (some .completed) => .known scalar false (some .completed)
  | _ => .unknown

/-- Completion output of the final native gate. None means decline, not
the language returning no answers. -/
def finish (rustCompatible : Bool) : Summary → Option Bool
  | .unknown | .known _ _ (some .collected) => none
  | .known _ hasVariable (some .completed) => if hasVariable || rustCompatible then none else some true
  | .known _ _ _ => some false

mutual
def markedThroughout : Entry.Value → Bool
  | .expression _ [] => true
  | .expression .active (_ :: _) => false
  | .expression .held fields => markedFields fields
  | _ => true
def markedFields : List Entry.Value → Bool
  | [] => true
  | field :: fields => markedThroughout field && markedFields fields
end

mutual
/-- Native deep completion preserves an already-held subtree and an empty
expression; it does not recursively repair marks under a held root. -/
def complete : Entry.Value → Entry.Value
  | .expression .active (first :: rest) => .expression .held (complete first :: completeFields rest)
  | value => value
def completeFields : List Entry.Value → List Entry.Value
  | [] => []
  | first :: rest => complete first :: completeFields rest
end

theorem completeFields_map (fields : List Entry.Value) : completeFields fields = fields.map complete := by
  induction fields with
  | nil => rfl
  | cons field fields ih => simp [completeFields, ih]

theorem markedFields_all (fields : List Entry.Value) : markedFields fields = fields.all markedThroughout := by
  induction fields with
  | nil => rfl
  | cons field fields ih => simp [markedFields, ih]

theorem marked_complete_fixed {value : Entry.Value} (checked : markedThroughout value = true) :
    complete value = value := by
  cases value with
  | symbol _ | var _ | grounded _ => rfl
  | expression status fields =>
      cases status <;> cases fields <;> simp_all [markedThroughout, complete]

def sourceRootAllowed (value : Entry.Value) : Bool := value.status != .held

/-- The symbol port is the existing scalar-source row check. The normal
form port is the actual constructor normal-form query, not nominal typing. -/
def readyOperand (symbolAllowed : String → Bool) (normalForm : Entry.Value → Bool) : Entry.Value → Summary
  | .symbol name => if symbolAllowed name then scalar else .unknown
  | .var _ => freeVariable
  | .grounded _ => scalar
  | .expression .held fields =>
      if markedThroughout (.expression .held fields) then value else .unknown
  | .expression .active fields =>
      if normalForm (.expression .active fields) then value else raw

theorem raw_template_refused : template raw = .unknown := rfl
theorem collected_template_refused : template collected = .unknown := rfl
theorem incompatible_marks_refused (s t v w : Bool) :
    join (.known s v (some .raw)) (.known t w (some .completed)) = .unknown := by simp [join]

theorem repeated_binding_join (summary : Summary) : join summary summary = summary := by
  cases summary with
  | unknown => rfl
  | known scalar hasVariable marking => cases marking <;> simp [join]

theorem field_value_is_earned (summary : Summary) (accepted : part summary = value) :
    ∃ scalar marking, summary = .known scalar false (some marking) ∧
      (marking = .completed ∨ marking = .collected) := by
  cases summary with
  | unknown => cases accepted
  | known scalar hasVariable marking =>
      cases hasVariable <;> cases marking with
      | none => cases accepted
      | some marking =>
          cases marking <;> simp_all [part, value]

theorem structural_slot_known (summary : Summary) (accepted : structural (template summary) ≠ .unknown) :
    ∃ scalar marking, summary = .known scalar false marking ∧
      (marking = none ∨ marking = some .completed) := by
  cases summary with
  | unknown => simp [template, structural] at accepted
  | known scalar hasVariable marking =>
      cases hasVariable <;> cases marking with
      | none => simp_all [template, structural]
      | some marking => cases marking <;> simp_all [template, structural]

theorem completed_gate_excludes_variable_and_compat (rust : Bool) (summary : Summary)
    (admitted : finish rust summary = some true) :
    rust = false ∧ ∃ scalar, summary = .known scalar false (some .completed) := by
  cases summary with
  | unknown => cases admitted
  | known scalar hasVariable marking =>
      cases hasVariable <;> cases marking with
      | none => simp [finish] at admitted
      | some marking =>
          cases marking <;> cases rust <;> simp_all [finish]

/-- Accepted ready expression operands either already carry all required
marks or are unmarked roots admitted by the separate normal-form query. -/
theorem ready_expression_value_cases (symbolAllowed : String → Bool) (normalForm : Entry.Value → Bool)
    (status : Entry.Status) (fields : List Entry.Value)
    (admitted : readyOperand symbolAllowed normalForm (.expression status fields) = value) :
    (status = .held ∧ markedThroughout (.expression status fields) = true) ∨
    (status = .active ∧ normalForm (.expression status fields) = true) := by
  cases status <;> simp only [readyOperand] at admitted
  · split at admitted
    next accepted => exact .inr ⟨rfl, accepted⟩
    next => cases admitted
  · split at admitted
    next accepted => exact .inl ⟨rfl, accepted⟩
    next => cases admitted

/-- Completion commutes with the actual selected field for every ready
expression accepted as a value. Parent readiness alone would not imply it. -/
theorem ready_field_projection (symbolAllowed : String → Bool) (normalForm : Entry.Value → Bool)
    (status : Entry.Status) (fields : List Entry.Value) (index : Nat) (field : Entry.Value)
    (admitted : readyOperand symbolAllowed normalForm (.expression status fields) = value)
    (selected : fields[index]? = some field) :
    ∃ completedFields,
      complete (.expression status fields) = .expression .held completedFields ∧
      completedFields[index]? = some (complete field) := by
  obtain (⟨rfl, checked⟩ | ⟨rfl, _⟩) := ready_expression_value_cases symbolAllowed normalForm status fields admitted
  · refine ⟨fields, rfl, ?_⟩
    have nonempty : fields ≠ [] := by intro empty; subst fields; simp at selected
    have all : markedFields fields = true := by cases fields <;> simp_all [markedThroughout]
    have child := List.all_eq_true.mp (by simpa only [markedFields_all] using all) field
      (List.mem_of_getElem? selected)
    simpa only [marked_complete_fixed child] using selected
  · cases fields with
    | nil => simp at selected
    | cons first rest =>
        refine ⟨complete first :: completeFields rest, rfl, ?_⟩
        simp only [completeFields_map, ← List.map_cons, List.getElem?_map, selected, Option.map_some]

namespace Controls

def pending : Entry.Value := .expression .active [.symbol "pending"]
def partlyMarked : Entry.Value := .expression .held [.symbol "Box", pending]
def finished : Entry.Value := .expression .held [.symbol "Box", .grounded (.int 7)]

theorem parent_mark_is_not_enough :
    partlyMarked.status = .held ∧ markedThroughout partlyMarked = false ∧
      readyOperand (fun _ => true) (fun _ => true) partlyMarked = .unknown := by decide +kernel

theorem same_value_different_entry_mode :
    sourceRootAllowed finished = false ∧
      readyOperand (fun _ => true) (fun _ => false) finished = value := by decide +kernel

theorem structural_variable_return_declines : structural (template freeVariable) = .unknown := rfl
theorem collected_entry_declines : finish false collected = none := rfl
theorem known_complete_entry : finish false (structural (template value)) = some true := rfl

theorem empty_expression_is_not_root_held :
    markedThroughout (.expression .active []) = true ∧
      complete (.expression .active []) = .expression .active [] ∧
      (Entry.Value.expression .active []).status ≠ .held := ⟨rfl, rfl, by decide⟩

theorem deep_completion_does_not_repair_a_held_parent :
    complete partlyMarked = partlyMarked ∧ markedThroughout (complete partlyMarked) = false := ⟨rfl, rfl⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECompletionEntry
