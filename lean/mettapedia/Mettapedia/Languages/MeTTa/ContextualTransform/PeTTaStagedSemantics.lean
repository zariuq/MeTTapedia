import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaResumptionSemantics

/-!
# Staged PeTTa evaluation

SWI-PeTTa translates a `!` query when it is reached. A function call enters
already compiled clauses. Named edits can refresh stored clauses when they
change recorded decisions. Running code keeps its translation after its own
edits and on backtracking. Each newly reached call selects its alternatives
from the clauses available at that call's entry.

`stagedAt` models a fresh translation at an entry and retention inside the
running unit. The fresh entry also describes a stored clause whose
translation reads still agree with the current world. A run-time `eval`
provides an explicit fresh translation. The Lean results concern the
abstract policy and its read-agreement condition.

The stored translations section gives that condition for the whole store.
After an edit, the store translates again each compiled clause that read a key
in the edit's footprint. Every compiled clause then stays current
(`refreshAll_current`), and entering one is a live entry
(`enter_current_eq_live`). The footprint has to cover the rows the edit
actually changed (`within_of_rows`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagedSemantics

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search Trace)
open Mettapedia.Machines.ReadOnlyQuery (Program run Agrees)
open PeTTaWorldSemantics
open PeTTaResumptionSemantics (Policy Boundary evalAt evalAt_live)

variable {World Key Fact Plan A : Type}

/-- Translate at an entry. After an edit and on resumption, keep what the
entry translated. Execution always uses the actual world. -/
def stagedAt (boundary : Boundary) (observe : World → Key → Fact)
    (preparedIn : World) (prepare : Program Key Fact Plan)
    (execute : Plan → Search World A) : Search World A :=
  match boundary with
  | .entry => DecisionStaging.enterLive observe prepare execute
  | .afterEdit => execute (run (observe preparedIn) prepare).answer
  | .resume => execute (run (observe preparedIn) prepare).answer

/-- At an entry with a fresh translation, the staged and live readings
coincide. -/
theorem staged_entry_eq_live (observe : World → Key → Fact) (preparedIn : World)
    (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    stagedAt .entry observe preparedIn prepare execute =
      evalAt .live .entry observe preparedIn prepare execute := rfl

/-- On resumption, staging keeps the prepared decisions, as edits-only does. -/
theorem staged_resume_eq_editsOnly (observe : World → Key → Fact) (preparedIn : World)
    (prepare : Program Key Fact Plan) (execute : Plan → Search World A) :
    stagedAt .resume observe preparedIn prepare execute =
      evalAt .editsOnly .resume observe preparedIn prepare execute := rfl

/-- The staged and the live readings differ only where an edit changed
something the translation read. -/
theorem staged_eq_live_of_agrees (boundary : Boundary) (observe : World → Key → Fact)
    {preparedIn current : World} (prepare : Program Key Fact Plan)
    (execute : Plan → Search World A)
    (agrees : Agrees (observe current) (run (observe preparedIn) prepare).reads) :
    stagedAt boundary observe preparedIn prepare execute current =
      evalAt .live boundary observe preparedIn prepare execute current := by
  cases boundary
  · rfl
  all_goals
    rw [evalAt_live]
    change execute (run (observe preparedIn) prepare).answer current =
      execute (run (observe current) prepare).answer current
    rw [Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees _ _ _ agrees]

/-! ## Stored translations

A compiled clause is a capture: its source, the plan a translation produced,
and the reads that translation made. The capture is current when it equals the
fresh translation of its source in the present program, and entering a
current capture is a live entry. SWI-PeTTa does not check captures at entry;
it translates them again when an edit changes what they read. An edit's
footprint is the set of keys it may have changed. Translating again every
capture that read a footprint key keeps every capture current, whatever the
captures read.

The footprint must cover every key whose rows the edit changed. This includes
the rows of each symbol that a pattern with variables matched, and, for a key
computed from several symbols, the rows of each of them. -/

section StoredTranslations

open PeTTaWorldSemantics.DecisionStaging (Capture capture enterLive)
open Mettapedia.Machines.ReadOnlyQuery (run_agrees run_eq_of_agrees)

/-- A capture is current in a program when it is that program's fresh
translation of its source. -/
def Current (store : Key → Fact) (saved : Capture Key Fact Plan) : Prop :=
  saved = capture store saved.program

/-- An edit from `before` to `after` changes no key outside its footprint. -/
def Within (before after : Key → Fact) (footprint : Key → Bool) : Prop :=
  ∀ key, footprint key = false → after key = before key

/-- After an edit, translate again each capture that read a footprint key. -/
def refreshAfter (store : Key → Fact) (footprint : Key → Bool)
    (saved : Capture Key Fact Plan) : Capture Key Fact Plan :=
  if saved.reads.any (fun read => footprint read.1) then capture store saved.program
  else saved

theorem capture_current (store : Key → Fact) (program : Program Key Fact Plan) :
    Current store (capture store program) := rfl

/-- Refreshing after an edit keeps a current capture current. A capture that
read no footprint key is kept unchanged. -/
theorem refreshAfter_current {before after : Key → Fact} {footprint : Key → Bool}
    (edit : Within before after footprint) {saved : Capture Key Fact Plan}
    (current : Current before saved) :
    Current after (refreshAfter after footprint saved) := by
  have fresh : saved = capture before saved.program := current
  generalize saved.program = program at fresh
  subst fresh
  unfold refreshAfter
  split
  · rfl
  · rename_i untouched
    have agree : Agrees after (run before program).reads := by
      intro read member
      have outside : footprint read.1 = false := by
        cases touched : footprint read.1
        · rfl
        · exact absurd (List.any_eq_true.mpr ⟨read, member, touched⟩) untouched
      rw [edit read.1 outside]
      exact run_agrees before program read member
    show capture before program = capture after program
    simp only [capture, run_eq_of_agrees before after program agree]

/-- Refreshing a whole store after an edit keeps every capture current. -/
theorem refreshAll_current {before after : Key → Fact} {footprint : Key → Bool}
    (edit : Within before after footprint) (stored : List (Capture Key Fact Plan))
    (current : ∀ saved ∈ stored, Current before saved) :
    ∀ saved ∈ stored.map (refreshAfter after footprint), Current after saved := by
  intro saved member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact refreshAfter_current edit (current old oldMember)

/-- Entering a current capture is a live entry: its stored plan is the plan a
fresh translation produces at that entry. -/
theorem enter_current_eq_live (store : World → Key → Fact) (world : World)
    (saved : Capture Key Fact Plan) (current : Current (store world) saved)
    (execute : Plan → Search World A) :
    execute saved.plan world = enterLive store saved.program execute world :=
  congrArg (fun captured : Capture Key Fact Plan => execute captured.plan world) current

/-- A footprint covers an edit when every key outside it depends only on rows
the edit left unchanged. -/
theorem within_of_rows {Symbol Rows : Type} (observe : (Symbol → Rows) → Key → Fact)
    (depends : Key → Symbol → Prop)
    (locality : ∀ key (first second : Symbol → Rows),
      (∀ symbol, depends key symbol → second symbol = first symbol) →
        observe second key = observe first key)
    {before after : Symbol → Rows} {footprint : Key → Bool}
    (covered : ∀ key, footprint key = false →
      ∀ symbol, depends key symbol → after symbol = before symbol) :
    Within (observe before) (observe after) footprint :=
  fun key outside => locality key before after (covered key outside)

end StoredTranslations

namespace FootprintControls

open PeTTaWorldSemantics.DecisionStaging (capture)

/-- Two symbols; each key reads the row count of one symbol. -/
private def counts (rows : Bool → Nat) (key : Bool) : Nat := rows key

private def readsSymbol (symbol : Bool) : Program Bool Nat Nat := .read symbol .pure

/-- A removal through a pattern with variables changes the rows of both
symbols. A footprint naming only the symbol written in the pattern leaves a
capture of the other symbol stale; the rows actually removed give a footprint
that keeps it current. -/
theorem pattern_removal_needs_removed_rows :
    let before : Bool → Nat := fun _ => 1
    let after : Bool → Nat := fun _ => 0
    let saved := capture (counts before) (readsSymbol true)
    (refreshAfter (counts after) (fun key => key == false) saved).plan = 1 ∧
      (run (counts after) (readsSymbol true)).answer = 0 ∧
      (refreshAfter (counts after) (fun _ => true) saved).plan = 0 := by
  decide

/-- A key computed from both symbols, as a translator rule's expansion is
computed from the program's equations. An edit of one symbol must still list
the combined key. -/
private def combined (rows : Bool → Nat) : Option Bool → Nat
  | some symbol => rows symbol
  | none => rows true + rows false

private def readsCombined : Program (Option Bool) Nat Nat := .read none .pure

theorem combined_key_needs_every_source :
    let before : Bool → Nat := fun _ => 1
    let after : Bool → Nat := fun symbol => if symbol then 2 else 1
    let saved := capture (combined before) readsCombined
    (refreshAfter (combined after) (fun key => key == some true) saved).plan = 2 ∧
      (run (combined after) readsCombined).answer = 3 ∧
      (refreshAfter (combined after) (fun key => key == some true || key == none) saved).plan = 3 := by
  decide

end FootprintControls

namespace Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Store)
open PeTTaWorldSemantics (Expr Model eval invokeAtEntry)
open PeTTaWorldSemantics.Search (pure append)

private def helper : Atom := .expression [.symbol "helper"]
private def value : Atom := .grounded (.int 42)
private def truth : Atom := .symbol "true"

private def equation (name : String) (body : Atom) : Atom :=
  .expression [.symbol "=", .expression [.symbol name], body]

private def installed : Atom := equation "helper" value

private def equations (world : Store) (head : String) : List Atom :=
  world.filterMap fun row => match row with
  | .expression [.symbol "=", .expression [.symbol name], body] =>
      if name = head then some body else none
  | _ => none

private def nullaryModel : Model Store String Atom Atom Atom where
  update row world := world ++ [row]
  editValue _ := truth
  argumentModes _ _ := []
  holdArgument _ := .symbol "held"
  data head args := .expression (.symbol head :: args)
  candidates := equations
  runCandidate candidate _ := pure candidate

private def install : Search Store Atom := eval nullaryModel (.edit installed)

private def observe (world : Store) (head : String) : Bool := !(equations world head).isEmpty

private def named (boundary : Boundary) (preparedIn : Store) (head : String) :
    Search Store Atom :=
  stagedAt boundary observe preparedIn (.read head .pure) fun callable =>
    if callable then invokeAtEntry nullaryModel head [] else pure (nullaryModel.data head [])

/-- `!(let $u (add-atom &self (= (helper) 42)) (helper))`: the code after the
edit keeps the decision it was translated with, so `(helper)` stays data.
A fresh translation, as in `(eval (helper))`, sees the new equation. -/
theorem edit_then_plain_or_entry :
    ((install.bind fun _ => named .afterEdit [] "helper") []).drain.1 = [helper] ∧
    ((install.bind fun _ => named .entry [] "helper") []).drain.1 = [value] := by
  decide +kernel

/-- A later `superpose` branch keeps its translation. Written with `eval`, it
is an entry and sees the equation an earlier branch added. -/
theorem later_branch_plain_or_entry :
    (append install (named .resume [] "helper") []).drain.1 = [truth, helper] ∧
    (append install (named .entry [] "helper") []).drain.1 = [truth, value] := by
  decide +kernel

/-- A function that already had an equation is a call in the translation, and
the call finds the equation added since. -/
theorem kept_call_reads_new_equations :
    let before := [equation "helper" (.symbol "old")]
    (append install (named .resume before "helper") before).drain.1 =
      [truth, .symbol "old", value] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagedSemantics
