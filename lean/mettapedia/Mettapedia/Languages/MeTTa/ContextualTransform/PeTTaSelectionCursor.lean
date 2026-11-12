import Mettapedia.Machines.EffectfulRowSelection
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec

/-!
# Resumable scoped selection and the actual PeTTa removal judgment

Each row request uses the source unifier and its own renaming number. The
generic cursor retains completed decisions across scheduler pauses. Successful
selection agrees with the independent source Removal relation and supplies an
actual tcalc effect and a source remove transition. Unifier exhaustion remains
incomplete selection; it cannot be published as a partial or negative result.

The pure source survivors function computes its recursive tail first. The
cursor visits rows from the front; completed survivor values agree because
row tests have no effects. Their internal unification work and fuel cutoffs
are not identified. Effectful tests use the generic protocol's declared order,
not this pure-source equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaSelectionCursor

open Mettapedia.Machines
open EffectfulRowSelection (reference program)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open PeTTaStoreSelection
open Unifying (unify rename resolve)
open Cursor.ReadOnlyQuery

variable {O : Type} (label : O → Atom)

def test (pattern : Atom) (_ : Unit) (key : Nat × O) : EffectfulRowSelection.Decision Unit × Unit :=
  (match unify [] pattern (rename key.1 (label key.2)) with
    | .ok _ => .ok true
    | .clash => .ok false
    | .exhausted => .error (), ())

theorem selection_scanned {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) :
    (reference (test label pattern) use rows ()).answer = .ok (kept, taken) := by
  induction selected with
  | nil => rfl
  | take matched _ ih =>
      simp [reference, test, matched, ih, EffectfulRowSelection.prepend, Except.map]
  | keep clashed _ ih =>
      simp [reference, test, clashed, ih, EffectfulRowSelection.prepend, Except.map]

theorem scanned_selection {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (scanned : (reference (test label pattern) use rows ()).answer = .ok (kept, taken)) :
    Removal label pattern use rows kept taken := by
  induction rows generalizing use kept taken with
  | nil =>
      simp only [reference, Except.ok.injEq, Prod.mk.injEq] at scanned
      rcases scanned with ⟨rfl, rfl⟩
      exact .nil _
  | cons row rest ih =>
      cases matched : unify [] pattern (rename use (label row)) with
      | exhausted => simp [reference, test, matched] at scanned
      | ok bindings =>
          cases later : (reference (test label pattern) (use + 1) rest ()).answer with
          | error reason =>
              simp [reference, test, matched, later, EffectfulRowSelection.prepend, Except.map] at scanned
          | ok result =>
              rcases result with ⟨keptLater, takenLater⟩
              simp [reference, test, matched, later, EffectfulRowSelection.prepend, Except.map] at scanned
              rcases scanned with ⟨rfl, rfl⟩
              exact .take matched (ih later)
      | clash =>
          cases later : (reference (test label pattern) (use + 1) rest ()).answer with
          | error reason =>
              simp [reference, test, matched, later, EffectfulRowSelection.prepend, Except.map] at scanned
          | ok result =>
              rcases result with ⟨keptLater, takenLater⟩
              simp [reference, test, matched, later, EffectfulRowSelection.prepend, Except.map] at scanned
              rcases scanned with ⟨rfl, rfl⟩
              exact .keep matched (ih later)

theorem scan_iff_selection (pattern : Atom) (use : Nat) (rows kept taken : List O) :
    (reference (test label pattern) use rows ()).answer = .ok (kept, taken) ↔
      Removal label pattern use rows kept taken :=
  ⟨scanned_selection label, selection_scanned label⟩

theorem selection_visits_all {pattern : Atom} {use : Nat} {rows kept taken : List O}
    (selected : Removal label pattern use rows kept taken) :
    (reference (test label pattern) use rows ()).reads.length = rows.length := by
  induction selected with
  | nil => rfl
  | take matched _ ih => simp [reference, test, matched, ih]
  | keep clashed _ ih => simp [reference, test, clashed, ih]

theorem source_iff_scan (pattern : Atom) (use : Nat) (rows : List O) (values : List Atom) :
    Unifying.survivors pattern use (rows.map label) = some values ↔
      ∃ kept taken, (reference (test label pattern) use rows ()).answer = .ok (kept, taken) ∧
        kept.map label = values := by
  constructor
  · intro completed
    obtain ⟨kept, taken, selected, decoded⟩ := source_selection label completed
    exact ⟨kept, taken, selection_scanned label selected, decoded⟩
  · rintro ⟨kept, taken, scanned, rfl⟩
    exact (scanned_selection label scanned).source label

theorem failed_scan_is_source_exhaustion (pattern : Atom) (use : Nat) (rows : List O)
    (whereAt : Nat × Unit)
    (failed : (reference (test label pattern) use rows ()).answer = .error whereAt) :
    Unifying.survivors pattern use (rows.map label) = none := by
  cases completed : Unifying.survivors pattern use (rows.map label) with
  | none => rfl
  | some values =>
      obtain ⟨kept, taken, scanned, _⟩ := (source_iff_scan label pattern use rows values).mp completed
      rw [failed] at scanned
      cases scanned

theorem cursor_has_source_selection (pattern : Atom) (use : Nat) (rows kept taken : List O)
    (selected : Removal label pattern use rows kept taken) (price : Nat × O → Nat) :
    (Sampled.completed? (test label pattern)
      (Sampled.advance (test label pattern) price (rows.length + 1) (program use rows) () []).2).map
        (fun observed => observed.answer) = some (.ok (kept, taken)) := by
  have complete := EffectfulRowSelection.cursor_reference (test label pattern) price use rows ()
  dsimp only at complete
  rw [selection_visits_all label selected, selection_scanned label selected] at complete
  exact congrArg (Option.map (fun observed => observed.answer)) complete.1

theorem cursor_selection_iff (pattern : Atom) (use : Nat) (rows kept taken : List O)
    (price : Nat × O → Nat) :
    (Sampled.completed? (test label pattern)
      (Sampled.advance (test label pattern) price (rows.length + 1) (program use rows) () []).2).map
        (fun observed => observed.answer) = some (.ok (kept, taken)) ↔
      Removal label pattern use rows kept taken := by
  rw [EffectfulRowSelection.cursor_row_budget]
  simpa [Sampled.completed?] using scan_iff_selection label pattern use rows kept taken

theorem failed_scan_prevents_remove_rows (state : Effects.State) (location head : Atom)
    (tail : List Atom) (handle : NamedSpaces.Handle) (use : Nat) (rows : List O)
    (whereAt : Nat × Unit)
    (resolved : Effects.readHandle location = some handle)
    (opened : state.read handle = some (rows.map label))
    (failed : (reference (test label (.expression (head :: tail))) use rows ()).answer = .error whereAt) :
    Unifying.removeRows state location (.expression (head :: tail)) use = none := by
  have incomplete := failed_scan_is_source_exhaustion label (.expression (head :: tail)) use rows whereAt failed
  simp [Unifying.removeRows, resolved, opened, incomplete]

theorem scan_realized [DecidableEq O] (pattern : Atom) (use : Nat) (rows kept taken : List O)
    (unique : rows.Nodup)
    (scanned : (reference (test label pattern) use rows ()).answer = .ok (kept, taken))
    (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
        (s := (knowledge, rows)) (request taken),
      ((OrderedStore.step atomFrames PUnit.unit label).result (request taken) admitted).2 = kept := by
  have selected := scanned_selection label scanned
  refine ⟨selected.admitted label unique knowledge consistent, ?_⟩
  rw [OrderedStore.result_rows]
  simpa [request, OrderedStore.publish] using selected.contracts label unique

/-- The source's own write/return convention is retained, including the
historical equation-row Boolean policy. This is not a CeTTa return-policy claim. -/
theorem completed_remove_transition (registry : SpaceSemantics.Program)
    (source : Unifying.Configuration) (bindings : Subst) (index : Nat)
    (location pattern head : Atom) (tail : List Atom) (handle : NamedSpaces.Handle)
    (rows kept taken : List O) (after : Effects.State)
    (control : source.control =
      .arguments bindings (.function "remove-atom") [] [location, pattern] index)
    (resolved : Effects.readHandle (resolve bindings location) = some handle)
    (patternShape : resolve bindings pattern = .expression (head :: tail))
    (opened : source.state.read handle = some (rows.map label))
    (scanned : (reference (test label (.expression (head :: tail))) source.uses rows ()).answer =
      .ok (kept, taken))
    (written : source.state.write handle (kept.map label) = some after) :
    Unifying.Transition registry source
      { source with
        state := after,
        control := .returned [⟨Effects.boolean
          (if Unifying.equationRow (.expression (head :: tail))
            then decide (kept.length < rows.length) else true), bindings⟩],
        uses := source.uses + rows.length } := by
  apply Unifying.Transition.remove (after := after) (used := rows.length)
    (answers := [Effects.boolean (if Unifying.equationRow (.expression (head :: tail))
      then decide (kept.length < rows.length) else true)]) control
  rw [patternShape]
  exact source_remove_rows label source.state after (resolve bindings location) head tail handle
    source.uses rows kept taken resolved opened (scanned_selection label scanned) written

theorem failed_remove_has_no_source_step (registry : SpaceSemantics.Program)
    (source : Unifying.Configuration) (bindings : Subst) (index : Nat) (location pattern : Atom)
    (control : source.control =
      .arguments bindings (.function "remove-atom") [] [location, pattern] index)
    (incomplete : Unifying.removeRows source.state (resolve bindings location)
      (resolve bindings pattern) source.uses = none) :
    Unifying.step registry source = none := by
  simp [Unifying.step, control, Eval.ioHead, incomplete]

theorem incomplete_remove_preserves_configuration (registry : SpaceSemantics.Program)
    (source : Unifying.Configuration) (bindings : Subst) (index : Nat) (location pattern : Atom)
    (control : source.control =
      .arguments bindings (.function "remove-atom") [] [location, pattern] index)
    (incomplete : Unifying.removeRows source.state (resolve bindings location)
      (resolve bindings pattern) source.uses = none) (fuel : Nat) :
    Unifying.run registry fuel source = .exhausted source := by
  have stopped := failed_remove_has_no_source_step registry source bindings index location pattern control incomplete
  cases fuel <;> simp [Unifying.run, control, stopped]

theorem failed_scan_preserves_source_configuration (registry : SpaceSemantics.Program)
    (source : Unifying.Configuration) (bindings : Subst) (index : Nat)
    (location pattern head : Atom) (tail : List Atom) (handle : NamedSpaces.Handle)
    (rows : List O) (whereAt : Nat × Unit)
    (control : source.control =
      .arguments bindings (.function "remove-atom") [] [location, pattern] index)
    (resolved : Effects.readHandle (resolve bindings location) = some handle)
    (patternShape : resolve bindings pattern = .expression (head :: tail))
    (opened : source.state.read handle = some (rows.map label))
    (failed : (reference (test label (.expression (head :: tail))) source.uses rows ()).answer = .error whereAt)
    (fuel : Nat) : Unifying.run registry fuel source = .exhausted source := by
  apply incomplete_remove_preserves_configuration registry source bindings index location pattern control
  rw [patternShape]
  exact failed_scan_prevents_remove_rows label source.state (resolve bindings location) head tail handle
    source.uses rows whereAt resolved opened failed

namespace Controls

def item (value : Atom) : Atom := .expression [.symbol "item", value]
def rows : Nat → Atom
  | 0 => item (.symbol "a")
  | 1 => item (.symbol "b")
  | _ => .expression [.symbol "other"]
def pattern := item (.var "requested")
def cut := Sampled.advance (test rows pattern) (fun _ => 1) 1 (program 8 [0, 1, 2]) () []
def finished := Sampled.resume (test rows pattern) (fun _ => 1) 3 cut

theorem independent_row_bindings_survive_resume :
    Sampled.completed? (test rows pattern) cut.2 = none ∧
      (Sampled.completed? (test rows pattern) finished.2).map (fun observed => observed.answer) =
        some (.ok ([2], [0, 1])) ∧ finished.1 = 3 := by decide

theorem open_stored_row_is_selected :
    (reference (test (fun _ : Nat => item (.var "stored")) (item (.symbol "a"))) 0 [4] ()).answer =
      .ok ([], [4]) := by decide

theorem equal_payloads_keep_distinct_occurrences :
    (reference (test (fun _ : Nat => item (.symbol "a")) pattern) 0 [4, 5] ()).answer =
      .ok ([], [4, 5]) := by decide

def registry : SpaceSemantics.Program := { equations := [], declarations := [] }
def initialStore : Effects.State := NamedSpaces.Store.new ([0, 1, 2].map rows) []
def source : Unifying.Configuration :=
  { state := initialStore
    control := .arguments [] (.function "remove-atom") [] [.symbol "&self", pattern] 2
    frames := [.collect []]
    input := [.symbol "unread"]
    output := [.symbol "earlier-effect"]
    uses := 8 }
def afterStore : Effects.State := { initialStore with core := [rows 2] }
def after : Unifying.Configuration :=
  { source with
    state := afterStore
    control := .returned [⟨Effects.boolean true, []⟩]
    uses := 11 }

theorem actual_source_removal : Unifying.Transition registry source after := by
  exact completed_remove_transition rows registry source [] 2 (.symbol "&self") pattern
    (.symbol "item") [.var "requested"] .self [0, 1, 2] [2] [0, 1] afterStore
    rfl rfl rfl rfl (by decide) rfl

theorem source_step_retains_earlier_effect_and_caller :
    (Unifying.step registry source).map (fun result =>
      (result.state.core, result.input, result.output, result.uses)) =
        some ([rows 2], [.symbol "unread"], [.symbol "earlier-effect"], 11) ∧
      after.frames = source.frames := by
  rw [Unifying.transition_step actual_source_removal]
  exact ⟨rfl, rfl⟩

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaSelectionCursor
