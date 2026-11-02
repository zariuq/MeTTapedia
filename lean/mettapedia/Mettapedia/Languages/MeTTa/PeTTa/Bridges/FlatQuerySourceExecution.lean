import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryConjunctionCompilation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQuerySource

/-!
# Compiled flat conjunctions at the PeTTa evaluator boundary

Nested source matches reread one unchanged captured snapshot. Their actual
evaluator paths enumerate the source binding branches, then run an admitted
state-preserving body. The count instance uses a literal Boolean body and
the source's actual collapse and size primitives.

The theorem is uniform in the snapshot, patterns and incoming represented
bindings. Source preparation does not first enumerate the answer space.
This connects source execution to the typed conjunctive IR; variable-at-a-time
delivery additionally needs finite-domain and variable-coverage evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQuerySourceExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics
open Eval SpaceSemantics FlatQueryRowCodec FlatQueryRelationCompilation FlatQueryConjunctionCompilation

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

private theorem queryBodies_expand (bindings : Subst) (rows : List Atom) (pattern body : Atom) :
    queryBodies bindings rows pattern body =
      rows.filterMap (fun row => (matchValue bindings pattern row).map (fun bound => Control.evaluate bound body)) := rfl

private theorem queryBodies_cons (bindings : Subst) (row : Atom) (rows : List Atom) (pattern body : Atom) :
    queryBodies bindings (row :: rows) pattern body =
      ((matchValue bindings pattern row).map (fun bound => Control.evaluate bound body)).toList ++
        queryBodies bindings rows pattern body := by
  rw [queryBodies_expand, queryBodies_expand]
  cases matched : matchValue bindings pattern row <;> simp [matched]

theorem rows_return_matched (program : Program) (state : Effects.State) (bindings : Subst) (pattern body : Atom)
    (answers : Subst → List Atom) (rows : List Atom)
    (returned : ∀ row ∈ rows, ∀ bound, matchValue bindings pattern row = some bound →
      Returns program bound state body state (answers bound))
    (start : Nat) (collected : List Atom) :
    (theory program).MultiStep {state, control := .sequence (queryBodies bindings rows pattern body) collected}
      (finished state (collected ++ (sourceScan bindings pattern start rows).flatMap (fun result => answers result.2)) [] []) := by
  induction rows generalizing start collected with
  | nil =>
      simpa only [queryBodies_expand, List.filterMap_nil, sourceScan, List.flatMap_nil, List.append_nil] using
        (.step (step_transition rfl) (.refl _) : (theory program).MultiStep
          {state, control := .sequence [] collected} (finished state collected [] []))
  | cons row rows ih =>
      rw [queryBodies_cons]
      have tail := ih (fun item present => returned item (List.mem_cons_of_mem _ present))
      cases matched : matchValue bindings pattern row with
      | none => simpa [matched, sourceScan] using tail (start + 1) collected
      | some bound =>
          have rest := tail (start + 1) (collected ++ answers bound)
          have joined := sequence_cons_answers program state state state (.evaluate bound body)
            (queryBodies bindings rows pattern body) collected (answers bound)
            ((collected ++ answers bound) ++ (sourceScan bindings pattern (start + 1) rows).flatMap (fun result => answers result.2))
            (returned row (by simp) bound matched) rest
          simpa [matched, sourceScan, List.append_assoc] using joined

theorem rows_return (program : Program) (state : Effects.State) (bindings : Subst) (pattern body : Atom)
    (answers : Subst → List Atom)
    (returned : ∀ bound, Returns program bound state body state (answers bound))
    (rows : List Atom) (start : Nat) (collected : List Atom) :
    (theory program).MultiStep {state, control := .sequence (queryBodies bindings rows pattern body) collected}
      (finished state (collected ++ (sourceScan bindings pattern start rows).flatMap (fun result => answers result.2)) [] []) :=
  rows_return_matched program state bindings pattern body answers rows (fun _ _ bound _ => returned bound) start collected

theorem match_returns (program : Program) (state : Effects.State) (bindings : Subst)
    (spaceName : String) (rows : List Atom)
    (snapshot : (Effects.readHandle (.symbol spaceName) >>= state.read) = some rows)
    (pattern body : Atom) (answers : Subst → List Atom)
    (returned : ∀ bound, Returns program bound state body state (answers bound)) :
    Returns program bindings state (.expression [.symbol "match", .symbol spaceName, pattern, body]) state
      ((sourceScan bindings pattern 0 rows).flatMap (fun result => answers result.2)) := by
  refine .step (step_transition rfl) (path_trans
    (path_with_caller_frames program [.query bindings pattern body] (symbol_returns program bindings state spaceName)) ?_)
  refine .step (step_transition rfl) ?_
  simp only [withFrames, finished, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [queryAlternatives, snapshot]
  simpa [finished] using rows_return program state bindings pattern body answers returned rows 0 []

def sourceTerm (space : Atom) : List Atom → Atom → Atom
  | [], body => body
  | pattern :: patterns, body => .expression [.symbol "match", space, pattern, sourceTerm space patterns body]

theorem nested_returns (program : Program) (state : Effects.State) (bindings : Subst)
    (spaceName : String) (rows : List Atom)
    (snapshot : (Effects.readHandle (.symbol spaceName) >>= state.read) = some rows)
    (patterns : List Atom) (body : Atom) (answers : Subst → List Atom)
    (returned : ∀ bound, Returns program bound state body state (answers bound)) :
    Returns program bindings state (sourceTerm (.symbol spaceName) patterns body) state
      ((sourceRun rows bindings patterns).flatMap (fun result => answers result.1)) := by
  induction patterns generalizing bindings with
  | nil => simpa [sourceTerm, sourceRun] using returned bindings
  | cons pattern patterns ih =>
      have result := match_returns program state bindings spaceName rows snapshot pattern
        (sourceTerm (.symbol spaceName) patterns body)
        (fun bound => (sourceRun rows bound patterns).flatMap (fun result => answers result.1)) ih
      simpa only [sourceTerm, sourceRun, List.flatMap_assoc, List.flatMap_map, Function.comp_def] using result

def countSyntax (spaceName : String) (patterns : List Atom) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse", sourceTerm (.symbol spaceName) patterns (Effects.boolean true)]]

theorem count_returns (program : Program) (state : Effects.State) (bindings : Subst)
    (spaceName : String) (rows : List Atom)
    (snapshot : (Effects.readHandle (.symbol spaceName) >>= state.read) = some rows) (patterns : List Atom) :
    PureReturns program bindings state (countSyntax spaceName patterns) state
      (.grounded (.int (sourceRun rows bindings patterns).length)) := by
  have stream : Returns program bindings state (sourceTerm (.symbol spaceName) patterns (Effects.boolean true)) state
      ((sourceRun rows bindings patterns).map (fun _ => Effects.boolean true)) := by
    rw [List.map_eq_flatMap]
    exact nested_returns program state bindings spaceName rows snapshot
      patterns (Effects.boolean true) (fun _ => [Effects.boolean true])
      (fun bound => grounded_returns program bound state (.bool true))
  have collected := collapse_returns program bindings state state _ _ stream
  have counted := native_unary_call_returns program bindings state state state "size-atom"
    (.expression [.symbol "collapse", sourceTerm (.symbol spaceName) patterns (Effects.boolean true)])
    (.expression ((sourceRun rows bindings patterns).map (fun _ => Effects.boolean true)))
    (.grounded (.int ((sourceRun rows bindings patterns).map (fun _ => Effects.boolean true)).length))
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    collected rfl (by decide)
  simpa only [List.length_map, countSyntax] using counted

theorem compiled_count_returns {Value : Type} [DecidableEq Value]
    (codec : Codec Value) (names : Inventory String) (rows patterns : List Atom)
    (legs : List (Leg codec names rows)) (accepted : compile codec names rows patterns = some legs)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (program : Program) (state : Effects.State) (spaceName : String)
    (snapshot : (Effects.readHandle (.symbol spaceName) >>= state.read) = some rows) :
    PureReturns program bindings state (countSyntax spaceName patterns) state
      (.grounded (.int (ConjunctiveBindingJoin.run environment (factors legs)).length)) := by
  rw [compiled_count_exact codec names rows patterns legs accepted environment bindings represented]
  exact count_returns program state bindings spaceName rows snapshot patterns

namespace Controls

open FlatQueryConjunctionCompilation.Controls

def state : Effects.State := NamedSpaces.Store.new rows []

theorem actual_nested_count_source :
    PureReturns {equations := [], declarations := []} [] state (countSyntax "&self" patterns) state (.grounded (.int 4)) := by
  have returned := count_returns {equations := [], declarations := []} state [] "&self" rows rfl patterns
  have count : (sourceRun rows [] patterns).length = 4 := by decide +kernel
  simpa [count] using returned

theorem captured_conflict_source_count_is_zero :
    PureReturns {equations := [], declarations := []} [("y", .grounded (.int 9))] state
      (countSyntax "&self" patterns) state (.grounded (.int 0)) := by
  have returned := count_returns {equations := [], declarations := []} state [("y", .grounded (.int 9))]
    "&self" rows rfl patterns
  simpa [incompatible_capture_cannot_be_rebound_by_later_leg] using returned

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQuerySourceExecution
