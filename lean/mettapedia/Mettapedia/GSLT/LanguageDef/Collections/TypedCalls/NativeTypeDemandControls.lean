import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemand
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViewsControls

/-!
# Controls for demand-directed type observation

The fixtures use the full Atom carrier, the existing annotation reader and
the separately proved source traversal. Their partial stores contain only
completed observations. The expected traces include negative observations,
read order and repeated reads; none is replaced by a support set.

The shared-variable fixture reuses the earlier ordered matcher control to
show first-local-match commitment. These tests do not implement C interning,
its scope/epoch guards, or arbitrary native type normalization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemandControls

open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQueryDemand
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space getAnnotatedTypes)
open NativeTypeViews NativeTypeDemand NativeTypeViewsControls

variable {Key : Type}

/-- A partial table retains complete replies for just the named questions. -/
def retained [DecidableEq Key] {Reply : Type} (source : Key → Reply)
    (keys : List Key) (key : Key) : Option Reply :=
  if key ∈ keys then some (source key) else none

theorem retained_truthful [DecidableEq Key] {Reply : Type} (source : Key → Reply)
    (keys : List Key) : Truthful source (retained source keys) := by
  intro key reply present
  unfold retained at present
  split at present
  · exact (Option.some.inj present).symm
  · simp at present

def handleKey : Question Atom := .classify (sym "NativeHandle") [sym "mork-space", zero]
def handleOnly := retained (sourceStore (reads handleSpace)) [handleKey]

theorem special_head_uses_only_classification :
    (check (ops handleSpace) true (sym "NativeHandle") [sym "mork-space", zero] handleOnly).answer =
        some (.ok [sym "MorkSpace"]) ∧
      (check (ops handleSpace) true (sym "NativeHandle") [sym "mork-space", zero] handleOnly).reads =
        [(handleKey, some (.class_ .nativeMork))] := by decide +kernel

theorem special_head_needs_no_child_views :
    handleOnly (.inferred (sym "mork-space")) = none ∧
      handleOnly (.tuplePart zero) = none ∧ handleOnly (.kind zero) = none := by decide +kernel

def annotated : Space := Space.ofList
  [expr [sym ":", expr [sym "f", sym "unknown"], sym "Declared"]]
def annotationKeys : List (Question Atom) :=
  [.classify (sym "f") [sym "unknown"], .annotations (sym "f") [sym "unknown"]]
def annotationOnly := retained (sourceStore (reads annotated)) annotationKeys

theorem annotation_shortcuts_all_children_and_head_rows :
    (check (ops annotated) true (sym "f") [sym "unknown"] annotationOnly).answer =
        some (.ok [sym "Declared"]) ∧
      (check (ops annotated) true (sym "f") [sym "unknown"] annotationOnly).reads =
        [(.classify (sym "f") [sym "unknown"], some (.class_ .ordinary)),
         (.annotations (sym "f") [sym "unknown"], some (.types [sym "Declared"]))] := by decide +kernel

theorem annotation_excludes_unused_queries :
    annotationOnly (.headRows (sym "f")) = none ∧
      annotationOnly (.inferred (sym "unknown")) = none := by decide +kernel

def heldKeys : List (Question Atom) :=
  [.classify (sym "f") [sym "unknown"], .annotations (sym "f") [sym "unknown"],
   .headRows (sym "f"), .kind (sym "unknown")]
def heldOnly := retained (sourceStore (reads heldSpace)) heldKeys
def heldResult : Atom := expr [sym "VecN", sym "Number", .grounded (.int 7)]

theorem metatype_reads_kind_not_inferred_view :
    (check (ops heldSpace) true (sym "f") [sym "unknown"] heldOnly).answer =
        some (.ok [heldResult]) ∧
      heldOnly (.inferred (sym "unknown")) = none ∧
      heldOnly (.tuplePart (sym "unknown")) = none := by decide +kernel

theorem metatype_exact_ordered_certificate :
    (check (ops heldSpace) true (sym "f") [sym "unknown"] heldOnly).reads =
      [(.classify (sym "f") [sym "unknown"], some (.class_ .ordinary)),
       (.annotations (sym "f") [sym "unknown"], some (.types [])),
       (.headRows (sym "f"), some (.types [expr [sym "->", Atom.atomType, heldResult]])),
       (.kind (sym "unknown"), some (.kind Atom.symbolType))] := by decide +kernel

def missingHead := retained (sourceStore (reads heldSpace)) annotationKeys

theorem first_missing_stops_before_children :
    (check (ops heldSpace) true (sym "f") [sym "unknown"] missingHead).answer = none ∧
      (check (ops heldSpace) true (sym "f") [sym "unknown"] missingHead).reads =
        [(.classify (sym "f") [sym "unknown"], some (.class_ .ordinary)),
         (.annotations (sym "f") [sym "unknown"], some (.types [])),
         (.headRows (sym "f"), none)] := by decide +kernel

def rejectSpace : Space := Space.ofList
  [annotation "f" (expr [sym "->", sym "Number", sym "R"]), annotation "text" (sym "String")]
def rejectKeys : List (Question Atom) :=
  [.classify (sym "f") [sym "text"], .annotations (sym "f") [sym "text"],
   .headRows (sym "f"), .kind (sym "text"), .inferred (sym "text")]
def rejectOnly := retained (sourceStore (reads rejectSpace)) rejectKeys

theorem completed_empty_is_not_missing :
    (check (ops rejectSpace) true (sym "f") [sym "text"] rejectOnly).answer = some (.ok []) ∧
      (check (ops rejectSpace) true (sym "f") [sym "text"]
        (retained (sourceStore (reads rejectSpace)) (rejectKeys.take 4))).answer = none := by decide +kernel

theorem failed_arrow_never_reads_tuple_fallback :
    rejectOnly (.tupleHead (sym "f")) = none ∧
      (check (ops rejectSpace) true (sym "f") [sym "text"] rejectOnly).reads =
        rejectKeys.map (fun key => (key, some (sourceStore (reads rejectSpace) key))) := by decide +kernel

def earlyRejectSpace : Space := Space.ofList
  [annotation "f" (expr [sym "->", sym "Number", sym "Number", sym "R"]),
   annotation "text" (sym "String")]
def earlyRejectKeys : List (Question Atom) :=
  [.classify (sym "f") [sym "text", sym "unavailable"],
   .annotations (sym "f") [sym "text", sym "unavailable"],
   .headRows (sym "f"), .kind (sym "text"), .inferred (sym "text")]

theorem early_argument_failure_skips_later_missing_views :
    (check (ops earlyRejectSpace) true (sym "f") [sym "text", sym "unavailable"]
      (retained (sourceStore (reads earlyRejectSpace)) earlyRejectKeys)).answer = some (.ok []) ∧
      (check (ops earlyRejectSpace) true (sym "f") [sym "text", sym "unavailable"]
        (retained (sourceStore (reads earlyRejectSpace)) earlyRejectKeys)).reads =
          earlyRejectKeys.map (fun key => (key, some (sourceStore (reads earlyRejectSpace) key))) := by
  decide +kernel

def emptyTupleKeys : List (Question Atom) :=
  [.classify (sym "untyped") [sym "unknown"], .annotations (sym "untyped") [sym "unknown"],
   .headRows (sym "untyped"), .tupleHead (sym "untyped")]
def emptyTupleOnly := retained (sourceStore (reads Space.empty)) emptyTupleKeys

theorem empty_tuple_head_stops_later_reads :
    (check (ops Space.empty) true (sym "untyped") [sym "unknown"] emptyTupleOnly).answer =
        some (.ok [Atom.undefinedType]) ∧
      (check (ops Space.empty) true (sym "untyped") [sym "unknown"] emptyTupleOnly).reads =
        emptyTupleKeys.map (fun key => (key, some (sourceStore (reads Space.empty) key))) := by decide +kernel

def repeatedOnly := retained (sourceStore (reads duplicateRowsSpace))
  [.classify (sym "f") [zero], .annotations (sym "f") [zero], .headRows (sym "f"), .kind zero]

theorem duplicate_rows_keep_output_and_read_occurrences :
    (check (ops duplicateRowsSpace) true (sym "f") [zero] repeatedOnly).answer =
        some (.ok [sym "R", sym "S", sym "R"]) ∧
      (check (ops duplicateRowsSpace) true (sym "f") [zero] repeatedOnly).reads =
        [(.classify (sym "f") [zero], some (.class_ .ordinary)),
         (.annotations (sym "f") [zero], some (.types [])),
         (.headRows (sym "f"), some (.types (getAnnotatedTypes duplicateRowsSpace (sym "f")))),
         (.kind zero, some (.kind Atom.groundedType)),
         (.kind zero, some (.kind Atom.groundedType)),
         (.kind zero, some (.kind Atom.groundedType))] := by decide +kernel

open StampInference.Controls in
def greedyReads (reverse : Bool) : NativeTypeViews.Reads Nat (Ty String) String where
  classify := fun _ _ => .ordinary
  annotations := fun _ _ => []
  headRows := fun _ => [arrowRow [.var "a", .var "a"] (.var "a")]
  tupleHead := fun _ => []
  kind := fun _ => "Symbol"
  inferred := fun value => if value = 0 then if reverse then [string, number] else [number, string]
    else [string]
  tuplePart := fun _ => []

theorem first_local_choice_does_not_backtrack :
    (check (legacyOps StampInference.Controls.oneVariable) true 9 [0, 1]
      (fun key => some (sourceStore (greedyReads false) key))).answer = some (.ok []) ∧
      (check (legacyOps StampInference.Controls.oneVariable) true 9 [0, 1]
        (fun key => some (sourceStore (greedyReads true) key))).answer =
          some (.ok [StampInference.Controls.string]) := by decide +kernel

/-- Changing an unobserved child inference cannot change the successful
metatype path, even though an all-fields descriptor would distinguish it. -/
theorem unused_inference_changes_preserve_admission :
    (check (ops heldSpace) true (sym "f") [sym "unknown"]
      (fun key => if key = .inferred (sym "unknown") then some (.types [sym "Wrong"])
        else heldOnly key)).answer =
      (check (ops heldSpace) true (sym "f") [sym "unknown"] heldOnly).answer := by decide +kernel

/-- A wrong-shaped available reply is distinct from an unavailable one and
from a well-formed completed empty type result. It cannot be truthful. -/
theorem malformed_reply_is_not_missing_or_empty :
    (check (ops heldSpace) true (sym "f") [sym "unknown"]
      (fun _ => some (.types []))).answer = some (.error ()) := by decide +kernel

def nullarySpace : Space := Space.ofList
  [annotation "nullary" (expr [sym "->", sym "R"])]
def nullaryKeys : List (Question Atom) :=
  [.classify (sym "nullary") [], .annotations (sym "nullary") [], .headRows (sym "nullary")]

/-- Zero parameters are a normal arrow case. No sentinel child observation
is needed to make the source-directed plan available. -/
theorem nullary_arrow_needs_no_child_slot :
    (check (ops nullarySpace) true (sym "nullary") []
      (retained (sourceStore (reads nullarySpace)) nullaryKeys)).answer = some (.ok [sym "R"]) ∧
      (check (ops nullarySpace) true (sym "nullary") []
        (retained (sourceStore (reads nullarySpace)) nullaryKeys)).reads =
          nullaryKeys.map (fun key => (key, some (sourceStore (reads nullarySpace) key))) := by decide +kernel

def indirectKeys : List (Question Atom) :=
  [.classify (sym "f") [sym "unknown"], .headRows (sym "f"), .kind (sym "unknown")]
def indirectOnly := retained (sourceStore (reads heldSpace)) indirectKeys

theorem inferred_question_does_not_read_direct_annotations :
    (check (ops heldSpace) false (sym "f") [sym "unknown"] indirectOnly).answer =
        some (.ok [heldResult]) ∧
      (check (ops heldSpace) false (sym "f") [sym "unknown"] indirectOnly).reads =
        indirectKeys.map (fun key => (key, some (sourceStore (reads heldSpace) key))) ∧
      (check (ops heldSpace) true (sym "f") [sym "unknown"] indirectOnly).answer = none := by decide +kernel

/-- Accepted results and their actual ordered read certificate are delivered
together by the general theorem, not inferred from the fixture's answer. -/
theorem held_admission_agrees_with_source :
    (check (ops heldSpace) true (sym "f") [sym "unknown"] heldOnly).answer =
        some (.ok (sourceNode (ops heldSpace) (reads heldSpace) true (sym "f") [sym "unknown"])) ∧
      (check (ops heldSpace) true (sym "f") [sym "unknown"] heldOnly).reads =
        liftedReads (run (sourceStore (reads heldSpace))
          (nodePlan (ops heldSpace) true (sym "f") [sym "unknown"])).reads := by
  have accepted := metatype_reads_kind_not_inferred_view.1
  have truthful := retained_truthful (sourceStore (reads heldSpace)) heldKeys
  have correct := check_accepted_eq_source (ops heldSpace) (reads heldSpace) true
    (sym "f") [sym "unknown"] heldOnly truthful [heldResult] accepted
  refine ⟨?_, check_accepted_reads (ops heldSpace) (reads heldSpace) true
    (sym "f") [sym "unknown"] heldOnly truthful ?_⟩
  · rw [accepted, ← correct]
  · rw [accepted]
    simp

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemandControls
