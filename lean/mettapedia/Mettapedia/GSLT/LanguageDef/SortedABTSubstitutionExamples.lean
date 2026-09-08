import Mettapedia.GSLT.LanguageDef.SortedABTSubstitution
import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics

/-!
# Cross-sort capture controls for sorted substitution

A replacement on the value axis can retain native variables and Need-cell
references. Moving it beneath a binder must weaken every captured axis.
The selected-axis opening operation does not provide that guarantee for
cross-sort replacements, even when both resulting trees pass scope and
exact-signature checks.

The finite heads below specify binding shapes, not a chosen CBPV calculus.
The operational control extracts the retained Need index from that shape
and forces its cell using the existing Prime Need machine. It introduces no
evaluator for ABTs, no new thunk semantics, and no claim that an arbitrary
cached heap was reached from an admitted source program.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedABTSubstitutionExamples

open SortedSignatureIndexedABT

inductive Axis where
  | native
  | value
  | need
deriving DecidableEq

inductive Head where
  | thunk
  | needScope
  | mixedScope
  | triple
  | four
deriving DecidableEq

abbrev Tree := Term Axis Head

def signature : Head → List (List Axis)
  | .thunk => [[]]
  | .needScope => [[.need]]
  | .mixedScope => [[.native, .value, .need, .need]]
  | .triple => [[], [], []]
  | .four => [[], [], [], []]

def thunk (body : Tree) : Tree := .node .thunk (.cons [] body .nil)

def needScope (body : Tree) : Tree :=
  .node .needScope (.cons [.need] body .nil)

def mixedScope (body : Tree) : Tree :=
  .node .mixedScope (.cons [.native, .value, .need, .need] body .nil)

def triple (first second third : Tree) : Tree :=
  .node .triple (.cons [] first (.cons [] second (.cons [] third .nil)))

def four (first second third fourth : Tree) : Tree :=
  .node .four
    (.cons [] first (.cons [] second (.cons [] third (.cons [] fourth .nil))))

/-- The thunk-shaped replacement captures the existing outer Need reference. -/
def capturedThunk : Tree := thunk (.idx .need 0)

def needBody : Tree := needScope (.idx .value 0)

def needDepth : Axis → Nat
  | .need => 1
  | _ => 0

theorem need_opening_retains_outer_reference :
    Term.substituteTop .value capturedThunk needBody =
      needScope (thunk (.idx .need 1)) := by
  rfl

theorem selected_axis_opening_captures_reference :
    Term.instantiate .value capturedThunk needBody =
      needScope (thunk (.idx .need 0)) := by
  rfl

/-- The general scope theorem applies to an independently supported body and
replacement; the resulting outer reference remains available. -/
theorem need_opening_supported :
    Term.supportedAt needDepth
      (Term.substituteTop .value capturedThunk needBody) = true := by
  exact Term.supportedAt_substituteTop (depth := needDepth) Axis.value
    (replacement := capturedThunk) (body := needBody) (by decide) (by decide)

/-- Both the captured and uncaptured trees pass the same structural gates. -/
theorem structural_checks_do_not_detect_capture :
    Term.supportedAt needDepth
        (Term.instantiate .value capturedThunk needBody) = true ∧
      Term.conforms signature
        (Term.substituteTop .value capturedThunk needBody) = true ∧
      Term.conforms signature
        (Term.instantiate .value capturedThunk needBody) = true := by
  decide

theorem cross_sort_openings_differ :
    Term.substituteTop .value capturedThunk needBody ≠
      Term.instantiate .value capturedThunk needBody := by
  decide

/-! ## Mixed binders protect locals while shifting all captured axes -/

def capturedMixed : Tree :=
  triple (.idx .native 0) (.idx .value 0) (.idx .need 0)

def mixedBody : Tree :=
  mixedScope
    (four (.idx .value 1) (.idx .native 0) (.idx .value 0) (.idx .need 0))

def mixedDepth : Axis → Nat := fun _ => 1

theorem mixed_opening_shifts_every_axis :
    Term.substituteTop .value capturedMixed mixedBody =
      mixedScope
        (four (triple (.idx .native 1) (.idx .value 1) (.idx .need 2))
          (.idx .native 0) (.idx .value 0) (.idx .need 0)) := by
  rfl

theorem mixed_selected_axis_misses_two_axes :
    Term.instantiate .value capturedMixed mixedBody =
      mixedScope
        (four (triple (.idx .native 0) (.idx .value 1) (.idx .need 0))
          (.idx .native 0) (.idx .value 0) (.idx .need 0)) := by
  rfl

theorem mixed_opening_supported :
    Term.supportedAt mixedDepth
      (Term.substituteTop .value capturedMixed mixedBody) = true := by
  exact Term.supportedAt_substituteTop (depth := mixedDepth) Axis.value
    (replacement := capturedMixed) (body := mixedBody) (by decide) (by decide)

theorem mixed_structural_checks_do_not_detect_capture :
    Term.supportedAt mixedDepth
        (Term.instantiate .value capturedMixed mixedBody) = true ∧
      Term.conforms signature
        (Term.substituteTop .value capturedMixed mixedBody) = true ∧
      Term.conforms signature
        (Term.instantiate .value capturedMixed mixedBody) = true ∧
      Term.substituteTop .value capturedMixed mixedBody ≠
        Term.instantiate .value capturedMixed mixedBody := by
  decide

/-! ## Actual Need-cell observations distinguish the captured reference -/

open Mettapedia.Languages.MeTTa.PrimeNeedReference

/-- Inspect only the exact retained reference in the preceding binding shape. -/
def capturedNeedIndex? : Tree → Option Nat
  | .node .needScope
      (.cons [.need] (.node .thunk (.cons [] (.idx .need index) .nil)) .nil) =>
      some index
  | _ => none

def outerCell : CellId := ⟨0, [], 0, 0⟩
def innerCell : CellId := ⟨0, [], 1, 0⟩

/-- The environment is viewed inside the new binder: zero is new, one outer. -/
def needEnvironment : Nat → CellId
  | 0 => innerCell
  | _ + 1 => outerCell

def completedWorld : World Nat Nat Nat Nat Nat Nat where
  lineage := 0
  path := []
  heap :=
    { current := fun cell =>
        if cell = outerCell then some ⟨0, .value 10⟩
        else if cell = innerCell then some ⟨1, .value 20⟩ else none
      spine := [.cache innerCell (.value 20), .cache outerCell (.value 10),
        .allocate innerCell 1, .allocate outerCell 0] }
  receipts := ReceiptGraph.empty
  nextCell := 2
  nextEvaluator := 2

variable {Local Resume : Type}

def forceReference (cell : CellId) :
    Machine Nat Local Resume Nat Nat Nat Nat Nat :=
  ⟨completedWorld, .force cell [], {}⟩

/-- This observation invokes the actual existing machine after selecting the
cell. The specification remains arbitrary: a completed force uses no callback. -/
def capturedAnswers
    (spec : Spec Nat Local Resume Nat Nat Nat Nat Nat) (tree : Tree) :
    Option (List (Produced Nat Nat Nat)) :=
  (capturedNeedIndex? tree).map fun index =>
    answers spec 2 (forceReference (needEnvironment index))

theorem need_opening_forces_outer_cached_value
    (spec : Spec Nat Local Resume Nat Nat Nat Nat Nat) :
    capturedAnswers spec (Term.substituteTop .value capturedThunk needBody) =
      some [.value 10] := by
  simp [capturedAnswers, need_opening_retains_outer_reference,
    capturedNeedIndex?, needScope, thunk, needEnvironment, answers, runFrontier,
    forceReference, isHalted, advance, step, completedWorld, Heap.lookup,
    outerCell, innerCell, finished, haltedOutcome]

theorem selected_axis_opening_forces_inner_cached_value
    (spec : Spec Nat Local Resume Nat Nat Nat Nat Nat) :
    capturedAnswers spec (Term.instantiate .value capturedThunk needBody) =
      some [.value 20] := by
  simp [capturedAnswers, selected_axis_opening_captures_reference,
    capturedNeedIndex?, needScope, thunk, needEnvironment, answers, runFrontier,
    forceReference, isHalted, advance, step, completedWorld, Heap.lookup,
    outerCell, innerCell, finished, haltedOutcome]

theorem cross_sort_capture_changes_actual_need_answer
    (spec : Spec Nat Local Resume Nat Nat Nat Nat Nat) :
    capturedAnswers spec (Term.substituteTop .value capturedThunk needBody) ≠
      capturedAnswers spec (Term.instantiate .value capturedThunk needBody) := by
  rw [need_opening_forces_outer_cached_value,
    selected_axis_opening_forces_inner_cached_value]
  decide

#print axioms need_opening_retains_outer_reference
#print axioms selected_axis_opening_captures_reference
#print axioms need_opening_supported
#print axioms structural_checks_do_not_detect_capture
#print axioms cross_sort_openings_differ
#print axioms mixed_opening_shifts_every_axis
#print axioms mixed_selected_axis_misses_two_axes
#print axioms mixed_opening_supported
#print axioms mixed_structural_checks_do_not_detect_capture
#print axioms need_opening_forces_outer_cached_value
#print axioms selected_axis_opening_forces_inner_cached_value
#print axioms cross_sort_capture_changes_actual_need_answer

end Mettapedia.GSLT.LanguageDef.SortedABTSubstitutionExamples
