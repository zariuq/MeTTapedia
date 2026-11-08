import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveSafety

/-! # Concrete recursive inference and demand controls

The declarations are closed, so the fixture's identity freshener is sufficient.
Its type expressions contain no arithmetic operation. Actual subtype rounds
still execute through the source port, including the A-to-B example.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open NativeTypeCallGraph NativeTypeRecursiveDriver NativeTypeSourcePorts

def sym (name : String) : Atom := .symbol name
def expr (atoms : List Atom) : Atom := .expression atoms
def row (head : String) (type_ : Atom) : Atom := expr [sym ":", sym head, type_]
def arrow (formals : List Atom) (returned : Atom) : Atom := expr (sym "->" :: formals ++ [returned])

def source : Source where
  rows := [row "hold" (arrow [sym "Atom"] (sym "R")),
    row "number-only" (arrow [sym "Number"] (sym "R")),
    row "make-op" (arrow [] (arrow [sym "Atom"] (sym "R"))),
    row "h" (sym "H"), row "a" (sym "A"), row "b" (sym "String"),
    expr [sym ":<", sym "A", sym "B"]]
  intrinsicRows := []
  rename := fun _ _ name => name
  subtypeBudget := 4
  subtypeFresh := "%recursive-subtype"
  alpha := (· == ·)

theorem source_safe : NativeTypeSourcePorts.Safe source := by
  unfold NativeTypeSourcePorts.Safe
  decide

def world : RetainedTypePayloads.ExternalView := fun kind key => .grounded (.custom kind key)

/-- The total-record closure slot is not read by the partial call graph;
the actual closure is the source's completed-round port. -/
def ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom :=
  TypeScopeMatcher.ops world id (fun _ => [])

def primitiveStore := NativeTypeSourcePorts.primitive source world

def unknown : Atom := expr [sym "unknown", expr [sym "deeper", sym "missing"]]
def held : Call := .infer true (expr [sym "hold", unknown])

theorem held_unknown_is_not_inferred :
    publishTypes (evaluate ops primitiveStore 2 held) = some [sym "R"] ∧
    ((run primitiveStore (expand ops 2 held)).reads.map Prod.fst) =
      [.classify (sym "hold") [unknown], .annotations (expr [sym "hold", unknown]),
        .annotations (sym "hold"), .kind unknown] := by cbv

theorem completed_child_results_are_recursive_not_annotation_only :
    publishTypes (evaluate ops primitiveStore 4
      (.infer true (expr [sym "h", expr [sym "hold", unknown]]))) =
      some [expr [sym "H", sym "R"]] := by cbv

theorem inferred_and_tuple_questions_differ :
    publishTypes (evaluate ops primitiveStore 1 (.infer true (sym "a"))) = some [sym "A", sym "B"] ∧
    publishTypes (evaluate ops primitiveStore 1 (.tuplePart false (sym "a"))) = some [sym "A"] ∧
    publishTypes (evaluate ops primitiveStore 2 (.infer true (expr [sym "h", sym "a"]))) =
      some [expr [sym "H", sym "A"]] := by cbv

theorem undeclared_expression_operator_uses_recursive_arrow :
    publishTypes (evaluate ops primitiveStore 4
      (.infer true (expr [expr [sym "make-op"], unknown]))) = some [sym "R"] := by cbv

theorem attempted_function_failure_is_completed_empty :
    publishTypes (evaluate ops primitiveStore 2
      (.infer true (expr [sym "number-only", sym "b"]))) = some [] := by cbv

theorem first_empty_tuple_part_skips_later_child :
    publishTypes (evaluate ops primitiveStore 2
      (.infer true (expr [sym "untyped-head", unknown]))) = some [sym "%Undefined%"] ∧
    ((run primitiveStore (expand ops 2 (.infer true (expr [sym "untyped-head", unknown])))).reads.map Prod.fst) =
      [.classify (sym "untyped-head") [unknown], .annotations (expr [sym "untyped-head", unknown]),
        .annotations (sym "untyped-head"), .annotations (sym "untyped-head")] := by cbv

def unfinishedPorts := NativeTypeSourcePorts.primitive { source with subtypeBudget := 0 } world

theorem unfinished_closure_is_not_a_negative_typing :
    evaluate ops unfinishedPorts 2 (.infer true (sym "a")) = none ∧
    publishTypes (evaluate ops unfinishedPorts 2 (.infer true (sym "a"))) ≠ some [] := by
  cbv
  simp

theorem unused_unfinished_closure_does_not_block_application :
    publishTypes (evaluate ops unfinishedPorts 2 held) = some [sym "R"] := by cbv

theorem native_handle_needs_only_its_literal_classification :
    publishTypes (evaluate ops unfinishedPorts 1
      (.infer true (expr [sym "NativeHandle", .grounded (.string "mork-space"), unknown]))) =
      some [sym "MorkSpace"] ∧
    ((run unfinishedPorts (expand ops 1
      (.infer true (expr [sym "NativeHandle", .grounded (.string "mork-space"), unknown])))).reads.map Prod.fst) =
      [.classify (sym "NativeHandle") [.grounded (.string "mork-space"), unknown]] := by cbv

def repeatedSource : Source := { source with rows :=
  [row "choice" (arrow [sym "Atom"] (sym "R")),
   row "choice" (arrow [sym "Atom"] (sym "S")),
   row "choice" (arrow [sym "Atom"] (sym "R"))] }

theorem recursive_driver_preserves_row_order_and_duplicates :
    publishTypes (evaluate ops (NativeTypeSourcePorts.primitive repeatedSource world) 2
      (.infer true (expr [sym "choice", unknown]))) = some [sym "R", sym "S", sym "R"] := by cbv

def openSource : Source :=
  { source with
    rows := [row "open" (expr [sym "List", .var "element"])]
    subtypeBudget := 1 }

/-- Semantic completion and resource closure do not imply the independent
ground-retention condition required by the native type-state interner. -/
theorem open_completion_is_not_retention :
    publishTypes (evaluate ops (NativeTypeSourcePorts.primitive openSource world) 1
      (.infer true (sym "open"))) = some [expr [sym "List", .var "element"]] ∧
    TypeDependencyAdmission.resourceFreeList [expr [sym "List", .var "element"]] = true ∧
    RetainedTypePayloads.admittedList [expr [sym "List", .var "element"]] = false := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveControls
