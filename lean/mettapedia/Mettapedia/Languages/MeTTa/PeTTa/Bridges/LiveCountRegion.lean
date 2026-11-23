import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay

/-!
# A counted match region of the ordinary live space evaluator

A ready call selects its body through the current space's generated
`LanguageDef`. A single selected `size-atom (collapse (match …))` body can
enter the region when the space operand is already a value or captured value,
the space is readable, and the success template is a literal symbol.

The region rewrites an ordered occurrence cursor. It advances through every
row and increments a natural count exactly when that row matches. The native
loop computes its terminal count without constructing the collection of
template results. Soundness is a path to the same complete configuration in
the live PeTTa evaluator, including the store and suspended caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveCountRegion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT
open Eval
open ProgramReplay

structure Query where
  location : Atom
  pattern : Atom
  witness : String

def Query.expression (query : Query) : Atom :=
  .expression [.symbol "match", query.location, query.pattern, .symbol query.witness]

def Query.collection (query : Query) : Atom :=
  .expression [.symbol "collapse", query.expression]

def Query.body (query : Query) : Atom :=
  .expression [.symbol "size-atom", query.collection]

def Query.ofBody? : (body : Atom) → Option {query : Query // query.body = body}
  | .expression [.symbol "size-atom", .expression [.symbol "collapse",
      .expression [.symbol "match", location, pattern, .symbol witness]]] =>
    some ⟨⟨location, pattern, witness⟩, rfl⟩
  | _ => none

/-- Space values obtained without evaluating another call. -/
def captureAtom (bindings : Subst) : Atom → Option Atom
  | .expression _ => none
  | .var name => some (applySubst bindings (.var name))
  | .symbol name => some (.symbol name)
  | .grounded value => some (.grounded value)

def eligible (query : Query) (bindings : Subst) (row : Atom) : Bool :=
  (SpaceSemantics.matchValue bindings query.pattern row).isSome

structure Cursor where
  pending : List Atom
  count : Nat

inductive Scan (query : Query) (bindings : Subst) : Cursor → Cursor → Prop where
  | hit (row : Atom) (remaining : List Atom) (count : Nat)
      (matched : eligible query bindings row = true) :
      Scan query bindings ⟨row :: remaining, count⟩ ⟨remaining, count + 1⟩
  | miss (row : Atom) (remaining : List Atom) (count : Nat)
      (different : eligible query bindings row = false) :
      Scan query bindings ⟨row :: remaining, count⟩ ⟨remaining, count⟩

def theory (query : Query) (bindings : Subst) : GSLT where
  Term := Cursor
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Scan query bindings
  rewrites_resp_left := by
    intro _ other target same firing
    subst other
    exact ⟨target, firing, rfl⟩
  rewrites_resp_right := by
    intro _ _ other firing same
    subst other
    exact firing

def run (query : Query) (bindings : Subst) (cursor : Cursor) : Nat :=
  cursor.pending.foldl (fun count row => if eligible query bindings row then count + 1 else count)
    cursor.count

private theorem run_of_firing {query : Query} {bindings : Subst} {before after : Cursor}
    (firing : Scan query bindings before after) :
    run query bindings before = run query bindings after := by
  cases firing with
  | hit row rest count matched => simp [run, matched]
  | miss row rest count different => simp [run, different]

theorem run_reaches (query : Query) (bindings : Subst) (remaining : List Atom) (count : Nat) :
    (theory query bindings).MultiStep ⟨remaining, count⟩ ⟨[], run query bindings ⟨remaining, count⟩⟩ := by
  induction remaining generalizing count with
  | nil => exact .refl _
  | cons row rest ih =>
    cases matched : eligible query bindings row with
    | true =>
      refine .step (Scan.hit row rest count matched) ?_
      simpa [run, matched] using ih (count + 1)
    | false =>
      refine .step (Scan.miss row rest count matched) ?_
      simpa [run, matched] using ih count

private theorem run_invariant (query : Query) (bindings : Subst) :
    {before after : (theory query bindings).Term} → (theory query bindings).MultiStep before after →
      run query bindings before = run query bindings after
  | _, _, .refl _ => rfl
  | _, _, .step firing path => (run_of_firing firing).trans (run_invariant query bindings path)

theorem terminal_exact (query : Query) (bindings : Subst) (cursor : Cursor) (result : Nat) :
    (theory query bindings).MultiStep cursor ⟨[], result⟩ ↔ run query bindings cursor = result := by
  constructor
  · exact run_invariant query bindings
  · rintro rfl
    exact run_reaches query bindings cursor.pending cursor.count

private theorem run_count (query : Query) (bindings : Subst) (rows : List Atom) (initial : Nat) :
    run query bindings ⟨rows, initial⟩ = initial + rows.countP (eligible query bindings) := by
  induction rows generalizing initial with
  | nil => simp [run]
  | cons row tail ih =>
    cases matchResult : eligible query bindings row with
    | true =>
      have counted := ih (initial + 1)
      simp only [run] at counted
      simp [run, matchResult, counted, Nat.add_assoc, Nat.add_comm]
    | false =>
      have counted := ih initial
      simp only [run] at counted
      simp [run, matchResult, counted]

/-- Disjoint occurrence slices admit an additive summary. Equal atoms in
different slots still each contribute once. -/
theorem run_append (query : Query) (bindings : Subst) (left right : List Atom) (initial : Nat) :
    run query bindings ⟨left ++ right, initial⟩ =
      run query bindings ⟨left, initial⟩ + run query bindings ⟨right, 0⟩ := by
  simp [run_count, List.countP_append, Nat.add_assoc]

private def localControl (base : Configuration) (control : Control) : Configuration :=
  {base with control, frames := []}

private abbrev LivePath := LiveRegistry.theory.MultiStep

private theorem liveInstruction {before after : Configuration}
    (step : Eval.step (SpaceSemantics.index before.state.core) before = some after) :
    LiveRegistry.theory.Step before after :=
  (LiveRegistry.step_exact before after).mp ((LiveRegistry.step_eq_indexed before).trans step)

private theorem appendPath : {before mid after : LiveRegistry.theory.Term} →
    LivePath before mid → LivePath mid after → LivePath before after
  | _, _, _, .refl _, last => last
  | _, _, _, .step firing rest, last => .step firing (appendPath rest last)

private theorem inFrames (caller : List Frame) : {before after : LiveRegistry.theory.Term} →
    LivePath before after → LivePath (withFrames before caller) (withFrames after caller)
  | _, _, .refl _ => .refl _
  | _, _, .step firing rest => by
    have stepped := (LiveRegistry.step_eq_indexed _).symm.trans ((LiveRegistry.step_exact _ _).mpr firing)
    exact .step (liveInstruction (step_with_caller_frames _ _ _ caller stepped)) (inFrames caller rest)

private theorem capturedAtom_returns (base : Configuration) (bindings : Subst) (code value : Atom)
    (captured : captureAtom bindings code = some value) :
    LivePath (localControl base (.evaluate bindings code)) (localControl base (.returned [value])) := by
  cases code with
  | expression _ => simp [captureAtom] at captured
  | var _ | symbol _ | grounded _ =>
    cases captured
    exact .step (liveInstruction rfl) (.refl _)

private theorem query_replies (base : Configuration) (query : Query) (bindings : Subst)
    (rows collected : List Atom) :
    LivePath
      (localControl base (.sequence (queryBodies bindings rows query.pattern (.symbol query.witness))
        collected))
      (localControl base (.returned
        (collected ++ List.replicate (rows.countP (eligible query bindings)) (.symbol query.witness)))) := by
  induction rows generalizing collected with
  | nil =>
    simp only [queryBodies, List.filterMap_nil, List.countP_nil, List.replicate_zero, List.append_nil]
    exact .step (liveInstruction rfl) (.refl _)
  | cons row rest ih =>
    cases matched : SpaceSemantics.matchValue bindings query.pattern row with
    | none =>
      simpa [queryBodies, eligible, matched] using ih collected
    | some bound =>
      simp only [queryBodies, List.filterMap_cons, matched, Option.map_some]
      have chosen : eligible query bindings row = true := by simp [eligible, matched]
      rw [List.countP_cons_of_pos chosen, List.replicate_succ]
      have tail := ih (collected ++ [.symbol query.witness])
      rw [List.append_assoc] at tail
      exact .step (liveInstruction rfl) (.step (liveInstruction rfl) (.step (liveInstruction rfl) tail))

private def replies (query : Query) (bindings : Subst) (rows : List Atom) : List Atom :=
  List.replicate (rows.countP (eligible query bindings)) (.symbol query.witness)

private theorem match_returns (base : Configuration) (query : Query) (bindings : Subst)
    (location : Atom) (rows : List Atom)
    (captured : captureAtom bindings query.location = some location)
    (readable : (Effects.readHandle location >>= base.state.read) = some rows) :
    LivePath (localControl base (.evaluate bindings query.expression))
      (localControl base (.returned (replies query bindings rows))) := by
  refine .step (liveInstruction rfl)
    (appendPath (inFrames [.query bindings query.pattern (.symbol query.witness)]
      (capturedAtom_returns base bindings query.location location captured)) ?_)
  refine .step (u := localControl base (.sequence
    (queryBodies bindings rows query.pattern (.symbol query.witness)) [])) (liveInstruction ?_) ?_
  · change (Effects.readHandle location).bind base.state.read = some rows at readable
    simp [localControl, withFrames, Eval.step, queryAlternatives, readable]
  · simpa [replies] using query_replies base query bindings rows []

private theorem collection_returns (base : Configuration) (query : Query) (bindings : Subst)
    (location : Atom) (rows : List Atom)
    (captured : captureAtom bindings query.location = some location)
    (readable : (Effects.readHandle location >>= base.state.read) = some rows) :
    LivePath (localControl base (.evaluate bindings query.collection))
      (localControl base (.returned [.expression (replies query bindings rows)])) := by
  exact .step (liveInstruction rfl)
    (appendPath (inFrames [.collect] (match_returns base query bindings location rows captured readable))
      (.step (liveInstruction rfl) (.refl _)))

theorem body_returns (base : Configuration) (query : Query) (bindings : Subst)
    (location : Atom) (rows : List Atom)
    (captured : captureAtom bindings query.location = some location)
    (readable : (Effects.readHandle location >>= base.state.read) = some rows) :
    LivePath (localControl base (.evaluate bindings query.body))
      (localControl base (.returned [.grounded (.int (run query bindings ⟨rows, 0⟩))])) := by
  have collected := inFrames [.argument bindings (.function "size-atom") [] [] 0]
    (collection_returns base query bindings location rows captured readable)
  have size : (replies query bindings rows).length = run query bindings ⟨rows, 0⟩ := by
    simp [replies, run_count]
  rw [← size]
  refine .step (liveInstruction rfl) (.step (liveInstruction rfl) (appendPath collected ?_))
  exact .step (liveInstruction rfl) (.step (liveInstruction rfl)
    (.step (liveInstruction rfl) (.step (liveInstruction rfl) (.step (liveInstruction rfl) (.refl _)))))

structure Entry (source : Configuration) where
  selected : Configuration
  selection : LiveRegistry.step source = some selected
  query : Query
  bindings : Subst
  body : selected.control = .sequence [.evaluate bindings query.body] []
  location : Atom
  rows : List Atom
  captured : captureAtom bindings query.location = some location
  observed : (Effects.readHandle location >>= selected.state.read) = some rows

/-- Admission consumes the actual ready call's selected occurrence and reads
the space at that point. A quoted body, extra alternative, unevaluated
location or invalid space declines before advancing the caller. -/
def prepare (source : Configuration) : Option (Entry source) :=
  match source.control with
  | .arguments _ (.function head) [] _ _ =>
    if ioHead head || StdLib.known head then none
    else do
      match selection : LiveRegistry.step source with
      | none => none
      | some selected =>
        match control : selected.control with
        | .sequence [.evaluate bindings body] [] =>
          let query ← Query.ofBody? body
          match captured : captureAtom bindings query.val.location with
          | none => none
          | some location =>
            match observed : (Effects.readHandle location >>= selected.state.read) with
            | none => none
            | some rows =>
              return ⟨selected, selection, query.val, bindings, by rw [control, query.property],
                location, rows, captured, observed⟩
        | _ => none
  | _ => none

def Entry.finish {source : Configuration} (entry : Entry source) : Configuration :=
  {entry.selected with
    control := .returned [.grounded (.int (run entry.query entry.bindings ⟨entry.rows, 0⟩))]}

theorem Entry.source_path {source : Configuration} (entry : Entry source) :
    LivePath source entry.finish := by
  let base := entry.selected
  let control := Control.evaluate entry.bindings entry.query.body
  have counted := body_returns base entry.query entry.bindings entry.location entry.rows
    entry.captured entry.observed
  have sequenced := inFrames [.sequence [] []] counted
  have first : LivePath (localControl base (.sequence [control] []))
      (withFrames (localControl base control) [.sequence [] []]) :=
    .step (liveInstruction rfl) (.refl _)
  have final : LivePath
      (withFrames (localControl base entry.finish.control) [.sequence [] []])
      (localControl base entry.finish.control) := by
    exact .step (liveInstruction rfl) (.step (liveInstruction rfl) (.refl _))
  have localRun := appendPath first (appendPath sequenced final)
  have callerRun := inFrames entry.selected.frames localRun
  refine .step ((LiveRegistry.step_exact _ _).mp entry.selection) ?_
  simpa [base, control, withFrames, localControl, ← entry.body, Entry.finish] using callerRun

def attempt (source : Configuration) : Option Configuration :=
  (prepare source).map Entry.finish

theorem attempt_sound (source target : Configuration)
    (admitted : attempt source = some target) : LivePath source target := by
  obtain ⟨entry, _, rfl⟩ := Option.map_eq_some_iff.mp admitted
  exact entry.source_path

/-- A native region step accounts for a completed source segment. A caller
that observes exact source fuel should use the ordinary step directly. -/
def acceleratedStep (source : Configuration) : Option Configuration :=
  (attempt source).orElse (fun _ => LiveRegistry.step source)

theorem acceleratedStep_sound (source target : Configuration)
    (executed : acceleratedStep source = some target) : LivePath source target := by
  cases admitted : attempt source with
  | none =>
    have ordinary : LiveRegistry.step source = some target := by
      simpa [acceleratedStep, admitted] using executed
    exact .step ((LiveRegistry.step_exact _ _).mp ordinary) (.refl _)
  | some native =>
    have same : native = target := by simpa [acceleratedStep, admitted] using executed
    exact same ▸ attempt_sound _ _ admitted

def advance : Nat → Configuration → Configuration
  | 0, source => source
  | fuel + 1, source =>
    match acceleratedStep source with
    | some next => advance fuel next
    | none => source

theorem advance_sound (fuel : Nat) (source : Configuration) : LivePath source (advance fuel source) := by
  induction fuel generalizing source with
  | zero => exact .refl _
  | succ fuel ih =>
    cases executed : acceleratedStep source with
    | none => simpa [advance, executed] using (GSLT.MultiStep.refl (S := LiveRegistry.theory) source)
    | some next =>
      simpa [advance, executed] using appendPath (acceleratedStep_sound _ _ executed) (ih next)

#print axioms terminal_exact
#print axioms run_append
#print axioms body_returns
#print axioms Entry.source_path
#print axioms attempt_sound
#print axioms advance_sound

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveCountRegion
