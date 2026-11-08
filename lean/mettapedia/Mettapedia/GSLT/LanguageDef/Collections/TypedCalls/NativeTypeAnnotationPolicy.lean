import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraph
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemandControls

/-!
# Current and historical application-annotation policies

The corrected internal reader keeps the annotation prefix and appends every
arrow result that is not already in that prefix. It does not deduplicate
derived occurrences against one another. This policy is separate from public
typing derivations and from structural constructor checking.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeAnnotationPolicy

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space getMetaType)
open NativeTypeViews

variable {TypeAtom Bind Kind Value : Type}

theorem sourceArgs_policy (ops : Ops TypeAtom Bind Kind) (policy : AnnotationPolicy TypeAtom)
    (reads : Reads Value TypeAtom Kind) (formals : List TypeAtom) : ∀ values state,
    sourceArgs { ops with annotationPolicy := policy } reads formals values state =
      sourceArgs ops reads formals values state := by
  induction formals with
  | nil => intro values state; cases values <;> rfl
  | cons formal formals ih =>
      intro values state
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [sourceArgs]
          split
          · exact ih values state
          · rfl
          · split
            · rfl
            · exact ih values _

theorem sourceRows_policy (ops : Ops TypeAtom Bind Kind) (policy : AnnotationPolicy TypeAtom)
    (reads : Reads Value TypeAtom Kind) (values : List Value) (rows : List TypeAtom) :
    sourceRows { ops with annotationPolicy := policy } reads values rows =
      sourceRows ops reads values rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [sourceRows]
      split
      · exact ih
      · rw [sourceArgs_policy]
        split <;> simp only [ih]

/-- The no-own-annotation path uses exactly the same row/tuple traversal.
This is local source agreement, not a global reader equivalence. -/
theorem sourceNode_without_annotations (ops : Ops TypeAtom Bind Kind) (policy : AnnotationPolicy TypeAtom)
    (reads : Reads Value TypeAtom Kind) (question : Bool) (head : Value) (values : List Value)
    (empty : (if question then reads.annotations head values else []) = []) :
    sourceNode { ops with annotationPolicy := policy } reads question head values =
      sourceNode ops reads question head values := by
  simp only [sourceNode]
  cases reads.classify head values with
  | nativeMork | listValue => rfl
  | ordinary =>
      simp only [empty, List.isEmpty_nil, if_true]
      split
      · exact sourceRows_policy ops policy reads values _
      · rfl

theorem structural_question_unchanged (ops : Ops TypeAtom Bind Kind) (policy : AnnotationPolicy TypeAtom)
    (reads : Reads Value TypeAtom Kind) (head : Value) (values : List Value) :
    sourceNode { ops with annotationPolicy := policy } reads false head values =
      sourceNode ops reads false head values :=
  sourceNode_without_annotations ops policy reads false head values rfl

/-- Argument checking does not inspect the containing application's own-row
policy. The complete adaptive program, not just its successful answers, agrees. -/
theorem argsPlan_policy (ops : Ops TypeAtom Bind Kind) (policy : AnnotationPolicy TypeAtom)
    (formals : List TypeAtom) : ∀ (values : List Value) state,
    NativeTypeDemand.argsPlan { ops with annotationPolicy := policy } formals values state =
      NativeTypeDemand.argsPlan ops formals values state := by
  induction formals with
  | nil => intro values state; cases values <;> rfl
  | cons formal formals ih =>
      intro values state
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [NativeTypeDemand.argsPlan, ih]

theorem rowsPlan_policy (ops : Ops TypeAtom Bind Kind) (policy : AnnotationPolicy TypeAtom)
    (values : List Value) (rows : List TypeAtom) :
    NativeTypeDemand.rowsPlan { ops with annotationPolicy := policy } values rows =
      NativeTypeDemand.rowsPlan ops values rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [NativeTypeDemand.rowsPlan]
      split
      · exact ih
      · rw [argsPlan_policy]
        congr 1
        funext result
        cases result with
        | error _ => rfl
        | ok result => cases result <;> simp only [ih]

theorem ordinary_policy (ops : Ops Atom TypeScopeMatcher.State Atom) (policy : AnnotationPolicy Atom)
    (head : Atom) (values : List Atom) :
    NativeTypeCallGraph.ordinary { ops with annotationPolicy := policy } head values =
      NativeTypeCallGraph.ordinary ops head values := by
  simp only [NativeTypeCallGraph.ordinary, rowsPlan_policy]

theorem prefix_retained (same : TypeAtom → TypeAtom → Bool) (annotations derived : List TypeAtom) :
    ∃ suffix, supplement same annotations derived = annotations ++ suffix :=
  ⟨_, rfl⟩

theorem derived_occurrence_kept (same : TypeAtom → TypeAtom → Bool) (annotations : List TypeAtom)
    (value : TypeAtom) (absent : annotations.any (fun prior => same prior value) = false) :
    supplement same annotations [value, value] = annotations ++ [value, value] := by
  simp [supplement, absent]

namespace Controls

open NativeTypeViewsControls (sym expr arrowView classify)

def historical : Ops Atom Unit Atom := NativeTypeViewsControls.ops Space.empty
def current : Ops Atom Unit Atom :=
  { historical with annotationPolicy := .supplement (· == ·) }

def arrow (range : Atom) : Atom := expr [sym "->", sym "Number", range]
def reads (annotations rows actuals : List Atom) : Reads Atom Atom Atom where
  classify := fun _ _ => .ordinary
  annotations := fun _ _ => annotations
  headRows := fun _ => rows
  tupleHead := fun _ => []
  kind := getMetaType
  inferred := fun _ => actuals
  tuplePart := fun _ => actuals

def rowViews : Reads Atom Atom Atom := reads [sym "Claimed"] [arrow (sym "Actual"), arrow (sym "Actual")] [sym "Number"]

theorem current_keeps_prefix_and_duplicate_derived_answers :
    sourceNode current rowViews true (sym "Box") [.grounded (.int 1)] =
      [sym "Claimed", sym "Actual", sym "Actual"] := by cbv

theorem historical_override_is_different :
    sourceNode historical rowViews true (sym "Box") [.grounded (.int 1)] = [sym "Claimed"] ∧
    sourceNode historical rowViews true (sym "Box") [.grounded (.int 1)] ≠
      sourceNode current rowViews true (sym "Box") [.grounded (.int 1)] := by
  cbv
  simp

theorem overlap_checks_only_the_annotation_prefix :
    supplement (fun left right : Atom => left == right) [sym "A", sym "A"]
      [sym "A", sym "B", sym "B"] = [sym "A", sym "A", sym "B", sym "B"] := by decide

theorem nominal_row_does_not_repair_structural_fields :
    sourceNode current (reads [sym "Claimed"] [arrow (sym "Actual")] [sym "String"])
      true (sym "Box") [.grounded (.string "bad")] = [sym "Claimed"] ∧
    sourceNode current (reads [sym "Claimed"] [arrow (sym "Actual")] [sym "String"])
      false (sym "Box") [.grounded (.string "bad")] = [] := by cbv

def annotationOnly : NativeTypeDemand.Question Atom → Option (NativeTypeDemand.ViewReply Atom Atom) :=
  NativeTypeDemandControls.retained (NativeTypeDemand.sourceStore rowViews)
    [.classify (sym "Box") [.grounded (.int 1)], .annotations (sym "Box") [.grounded (.int 1)]]

theorem current_does_not_invent_missing_operator_observation :
    (NativeTypeDemand.check historical true (sym "Box") [.grounded (.int 1)] annotationOnly).answer =
      some (.ok [sym "Claimed"]) ∧
    (NativeTypeDemand.check current true (sym "Box") [.grounded (.int 1)] annotationOnly).answer = none := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeAnnotationPolicy
