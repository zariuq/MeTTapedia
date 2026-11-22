import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.Triangle
import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls
import Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls
import Mettapedia.Languages.MeTTa.PeTTa.StreamingOnTheStep

/-!
# Named differences between HE and PeTTa, as distinguishing controls

A distinction, in Ben Goertzel's sense, is an observation that tells two systems apart. Each control
below is one program, with HE's outcome and PeTTa's outcome proved on the tree's own models:

* HE: the space operations of `HE.Space` and the executable evaluator `HE.evalAtom`;
* PeTTa: the streaming machine (`PeTTa.Streaming`) and its store projection
  (`PeTTa.RunsAsFirings`).

1. `removal`: `!(remove-atom &self (p a))` on a space holding `(p a)` twice. HE removes one
   occurrence (`HE.Space.remove`): one `(p a)` remains. PeTTa's request takes every copy, and
   nothing remains. On the step this is the store reached: the triangle fails on it.
2. `return_type_reevaluation`: one body under two declared return types. HE evaluates a call's
   result again against the declared return type: `(give-atom (+ 1 2))` with `(-> Atom Atom)`
   answers `(+ 1 2)`, `(give-undef (+ 1 2))` with `(-> Atom %Undefined%)` answers `3`. PeTTa
   answers the same for both.
3. `held_argument_under_undefined`: the Prime merge's `held_arguments` case. A parameter declared
   `Atom` holds its argument as data; returned under the range `%Undefined%`, HE evaluates it
   (`(give-undef (f a))` answers `5` where `(= (f a) 5)`), PeTTa returns it as held (`(f a)`).
4. `captured_match_publishes_on_the_step` runs the stateful HE evaluator with
   the compound snapshot selector. The earlier entry-view versus per-conjunct-live
   separation remains in `PeTTaAndHE.Controls.snapshot_granularity`; it models
   the policies, not the current CeTTa implementation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep

namespace NamedDifferences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space GroundedDispatch evalAtom Bindings)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

/-! ## Programs -/

def app (name : String) (args : List Atom) : Atom := .expression (.symbol name :: args)
def arrow (args : List Atom) : Atom := .expression (.symbol "->" :: args)
def decl (name : String) (type : Atom) : Atom := .expression [.symbol ":", .symbol name, type]
def eqn (lhs rhs : Atom) : Atom := .expression [.symbol "=", lhs, rhs]

/-- `(+ 1 2)`. -/
def sum12 : Atom := app "+" [.grounded (.int 1), .grounded (.int 2)]

/-- `(f a)`, which reduces to `5`. -/
def fa : Atom := app "f" [.symbol "a"]

/-- HE's grounded `+` on integers. -/
def plus : GroundedDispatch where
  isExecutable := fun a => match a with
    | .symbol "+" => true
    | _ => false
  execute := fun op args => match op, args with
    | .symbol "+", [.grounded (.int m), .grounded (.int n)] =>
        .ok [(.grounded (.int (m + n)), default)]
    | _, _ => .noReduce

/-- The program of controls 2 and 3: `(= (f a) 5)`, and `give-atom`, `give-undef` returning their
`Atom` parameter under the ranges `Atom` and `%Undefined%`. -/
def programAtoms : List Atom :=
  [eqn fa (.grounded (.int 5)),
   decl "give-atom" (arrow [.symbol "Atom", .symbol "Atom"]),
   eqn (app "give-atom" [.var "x"]) (.var "x"),
   decl "give-undef" (arrow [.symbol "Atom", .symbol "%Undefined%"]),
   eqn (app "give-undef" [.var "x"]) (.var "x")]

def heSpace : Space := Space.ofList programAtoms

/-- The same program loaded in PeTTa. -/
def pettaProgram : SpaceSemantics.Program :=
  { equations := [⟨"f", [.symbol "a"], .grounded (.int 5)⟩,
      ⟨"give-atom", [.var "x"], .var "x"⟩, ⟨"give-undef", [.var "x"], .var "x"⟩],
    declarations := [decl "give-atom" (arrow [.symbol "Atom", .symbol "Atom"]),
      decl "give-undef" (arrow [.symbol "Atom", .symbol "%Undefined%"])] }

def pettaStore : Effects.State := NamedSpaces.Store.new programAtoms []

/-- HE's answers to an expression in the program's space. -/
def heAnswers (expression : Atom) : List Atom :=
  (evalAtom heSpace plus expression Atom.undefinedType Bindings.empty 40).map Prod.fst

/-- PeTTa's answers to an expression against the loaded program. -/
def pettaAnswers (expression : Atom) : List Atom :=
  Streaming.values (Streaming.advance pettaProgram 60 (Streaming.enter { state := pettaStore } expression))

/-! ## 1. Removal -/

/-- `(p a)`. -/
def pa : Atom := app "p" [.symbol "a"]

def dupAtoms : List Atom := [pa, pa]
def dupStore : Effects.State := NamedSpaces.Store.new dupAtoms []
def removePa : Atom := app "remove-atom" [.symbol "&self", pa]
def noProgram : SpaceSemantics.Program := { equations := [], declarations := [] }

/-- **Control 1: removal.** On a space holding `(p a)` twice, HE's removal leaves one `(p a)`;
PeTTa's `remove-atom` is one request taking both copies, and nothing remains. The HE side here
applies HE's `Space.remove` directly, not the machine; removal on HE's world machine is
`TriangleFootprints.WorldRemoval.he_removes_one_occurrence` and
`TriangleFootprints.HonestWrites.remove_takes_one`. -/
theorem removal :
    (Space.remove (Space.ofList dupAtoms) pa).atoms = [pa] ∧
      (requests rowSupply noProgram 30 (Streaming.enter { state := dupStore } removePa)
          (Row.load 0 dupAtoms)).map Controls.shape =
        [([⟨0, .self, pa⟩, ⟨1, .self, pa⟩], [], [])] ∧
      (Streaming.advance noProgram 30 (Streaming.enter { state := dupStore } removePa)).world.state.core
        = [] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 2. Re-evaluation by return type -/

/-- **Control 2: HE re-evaluates by return type.** The same body under the ranges `Atom` and
`%Undefined%` answers `(+ 1 2)` and `3` in HE; PeTTa answers `(+ 1 2)` under both. -/
theorem return_type_reevaluation :
    heAnswers (app "give-atom" [sum12]) = [sum12] ∧
      heAnswers (app "give-undef" [sum12]) = [.grounded (.int 3)] ∧
      pettaAnswers (app "give-atom" [sum12]) = [sum12] ∧
      pettaAnswers (app "give-undef" [sum12]) = [sum12] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 3. Held arguments under `%Undefined%` -/

/-- **Control 3: a held argument returned under `%Undefined%`.** HE evaluates `(f a)` on return and
answers `5`; PeTTa returns the held `(f a)`. Under the range `Atom` both return `(f a)`. -/
theorem held_argument_under_undefined :
    heAnswers (app "give-undef" [fa]) = [.grounded (.int 5)] ∧
      pettaAnswers (app "give-undef" [fa]) = [fa] ∧
      heAnswers (app "give-atom" [fa]) = [fa] ∧
      pettaAnswers (app "give-atom" [fa]) = [fa] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Authored quotation, code recovery and evaluation -/

section Quotation

open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls (World environment services)
open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.Quotation
  (quote unquote contextQuery contextQuery_closed libraryWorld prepared_quote unquote_context_space unquote_marker
    quoteCaller openQuote callerPair open_quote_retains_frame
    releaseCaller openRelease open_unquote_executes
    demandInput demandOutcome reachedByDemand authored_caller_demand)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame Result Policy)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Stateful (CallRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration Control Continuation)
open Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful (source_to_finished)

private def prepared (label : Bool) (call : Atom) (expected : Atom) : WorldConfiguration Bool World :=
  ⟨libraryWorld, label, .work (.call [] [] (Entry.Value.ofAtom call) expected Frame.empty), [], []⟩

private abbrev stores := Store World (Control Bool) Continuation Result

private theorem source_finishes_on_the_step {initial : WorldConfiguration Bool World}
    {answers : List Result} {after : World} {first : stores}
    (source : initial.SourceRel environment .unmarked answers after)
    (represented : Represents first (toWorldConfig initial)) :
    ∃ last : stores,
      Relation.ReflTransGen
        (StoreStep (heWorldMachine environment.view environment.services environment.dispatch
          environment.lookup .unmarked initial.context environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨after,initial.context,.returning [],[],answers⟩) :=
  he_world_source_prefix environment.arguments represented (source_to_finished source)

private theorem prepared_fires {label : Bool} {call expected : Atom} {answer : Result}
    (source : CallRel environment label libraryWorld [] [] (Entry.Value.ofAtom call) expected Frame.empty
      [answer] libraryWorld) :
    ∃ first last : stores, Represents first (toWorldConfig (prepared label call expected)) ∧
      Relation.ReflTransGen
        (StoreStep (heWorldMachine environment.view environment.services environment.dispatch
          environment.lookup .unmarked label environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨libraryWorld,label,.returning [],[],[answer]⟩) := by
  have evaluated : (prepared label call expected).SourceRel environment .unmarked [answer] libraryWorld :=
    ⟨_, _, _, .work source, .nil _, rfl⟩
  obtain ⟨first, here⟩ := exists_represents (toWorldConfig (prepared label call expected))
  obtain ⟨last, path, there⟩ := source_finishes_on_the_step evaluated here
  exact ⟨first, last, here, path, there⟩

/-- Authored unquote reaches the actual context operation, rather than exporting an inert
copy of the expression. Its independent source derivation lifts through publication. -/
theorem unquote_context_on_the_step (label : Bool) :
    ∃ first last : stores, ∃ frame : Frame,
      Represents first (toWorldConfig (prepared label (unquote contextQuery) Atom.undefinedType)) ∧
      Relation.ReflTransGen
        (StoreStep (heWorldMachine environment.view environment.services environment.dispatch
          environment.lookup .unmarked label environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨libraryWorld,label,.returning [],[],
        [(.grounded (services.contextPayload label), frame)]⟩) := by
  obtain ⟨frame, source⟩ := unquote_context_space label
  obtain ⟨first, last, here, path, there⟩ := prepared_fires source
  exact ⟨first, last, frame, here, path, there⟩

/-- On the same code, quote publishes the wrapper instead of a handle. -/
theorem quote_context_on_the_step (label : Bool) :
    ∃ first last : stores, ∃ frame : Frame,
      Represents first (toWorldConfig (prepared label (quote contextQuery) Atom.atomType)) ∧
      Relation.ReflTransGen
        (StoreStep (heWorldMachine environment.view environment.services environment.dispatch
          environment.lookup .unmarked label environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨libraryWorld,label,.returning [],[],
        [(Entry.Value.ofAtom (quote contextQuery), frame)]⟩) := by
  obtain ⟨frame, _, source⟩ := prepared_quote label contextQuery rfl contextQuery_closed
  obtain ⟨first, last, here, path, there⟩ := prepared_fires source
  exact ⟨first, last, frame, here, path, there⟩

private def openQuoteEntry (label : Bool) : WorldConfiguration Bool World :=
  ⟨libraryWorld,label,.work (.atom [] [] (Entry.Value.ofAtom openQuote) Atom.undefinedType quoteCaller),[],[]⟩

/-- The open source input reaches completion on the step with the original caller's
binding and a distinct fresh rule binding. No prepared-call premise is used. -/
theorem open_quote_on_the_step (label : Bool) {first : stores}
    (represented : Represents first (toWorldConfig (openQuoteEntry label))) :
    ∃ last : stores, ∃ frame : Frame,
      Relation.ReflTransGen
        (StoreStep (heWorldMachine environment.view environment.services environment.dispatch
          environment.lookup .unmarked label environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨libraryWorld,label,.returning [],[],
        [(Entry.Value.ofAtom (quote callerPair), frame)]⟩) ∧
      (frame.read .unmarked (.var "atom")).erase = .symbol "prior" ∧
      (frame.read .unmarked (.var "quote#local")).erase = callerPair := by
  obtain ⟨frame, _, source, saved, localBinding⟩ := open_quote_retains_frame label
  have completed : (openQuoteEntry label).SourceRel environment .unmarked
      [(Entry.Value.ofAtom (quote callerPair), frame)] libraryWorld :=
    ⟨_, _, _, .work source, .nil _, rfl⟩
  obtain ⟨last, path, readout⟩ := source_finishes_on_the_step completed represented
  exact ⟨last, frame, path, readout, saved, localBinding⟩

private def openReleaseEntry (label : Bool) : WorldConfiguration Bool World :=
  ⟨libraryWorld,label,.work (.atom [] [] (Entry.Value.ofAtom openRelease) Atom.undefinedType releaseCaller),[],[]⟩

/-- The open nested source term starts before the inner quote is evaluated. Its lifted
run publishes the handle, keeps the caller's code and records distinct rule bindings. -/
theorem open_unquote_on_the_step (label : Bool) {first : stores}
    (represented : Represents first (toWorldConfig (openReleaseEntry label))) :
    ∃ last : stores, ∃ frame : Frame,
      Relation.ReflTransGen
        (StoreStep (heWorldMachine environment.view environment.services environment.dispatch
          environment.lookup .unmarked label environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨libraryWorld,label,.returning [],[],
        [(.grounded (services.contextPayload label), frame)]⟩) ∧
      frame.bindings =
        (releaseCaller.bindings.assign "quote#local" contextQuery).assign "release#local" contextQuery ∧
      (frame.read .unmarked (.var "atom")).erase = contextQuery := by
  obtain ⟨frame, source, bindings, savedCode⟩ := open_unquote_executes label
  have completed : (openReleaseEntry label).SourceRel environment .unmarked
      [(.grounded (services.contextPayload label), frame)] libraryWorld :=
    ⟨_, _, _, .work source, .nil _, rfl⟩
  obtain ⟨last, path, readout⟩ := source_finishes_on_the_step completed represented
  exact ⟨last, frame, path, readout, bindings, savedCode⟩

def authoredDemandEntry (release label : Bool) : WorldConfiguration Bool World :=
  ⟨libraryWorld, label, .work (.atom [] [] (demandInput release) Atom.undefinedType Frame.empty), [], []⟩

/-- The actual outer syntax lifts through type selection, operand work
and publication, preserving the world reached by the declared demand. -/
theorem authored_demand_on_the_step (release label : Bool) {first : stores}
    (represented : Represents first (toWorldConfig (authoredDemandEntry release label))) :
    ∃ last : stores, ∃ frame : Frame,
      Relation.ReflTransGen
        (StoreStep (heWorldMachine environment.view environment.services environment.dispatch
          environment.lookup .unmarked label environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨reachedByDemand release label, label, .returning [], [],
        [(demandOutcome release, frame)]⟩) := by
  obtain ⟨frame, source⟩ := authored_caller_demand release label
  have completed : (authoredDemandEntry release label).SourceRel environment .unmarked
      [(demandOutcome release, frame)] (reachedByDemand release label) :=
    ⟨_, _, _, .work source, .nil _, rfl⟩
  obtain ⟨last, path, readout⟩ := source_finishes_on_the_step completed represented
  exact ⟨last, frame, path, readout⟩

/-- The same spelling does not denote a common operation: the prepared HE source rule restores
its original call on the marker, while PeTTa's streaming profile strips `quote` and leaves
the now-unrecognized `unquote` call as data. -/
theorem marker_dialects_separate :
    (∃ output : Frame,
      CallRel environment false libraryWorld [] [] (Entry.Value.ofAtom (unquote Atom.notReducible))
        Atom.undefinedType Frame.empty [(Entry.Value.ofAtom (unquote Atom.notReducible), output)]
        libraryWorld) ∧
    Streaming.values (Streaming.advance noProgram 40
      (Streaming.enter { state := Effects.empty } (unquote Atom.notReducible))) =
      [.expression [.symbol "unquote", Atom.notReducible]] ∧
    unquote Atom.notReducible ≠ .expression [.symbol "unquote", Atom.notReducible] := by
  obtain ⟨output, _, source⟩ := unquote_marker false
  exact ⟨⟨output, source⟩, by decide +kernel, by decide +kernel⟩

end Quotation

section CapturedMatch

open Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame Result SnapshotServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldSteps)
open Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful (source_to_finished)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry (Value)
open LocatedSubstitution.Authority (Ledger Ticket)
open Mettapedia.Machines.ProgressObservation (observePath)
open MeTTaCalculus.OccurrenceCommits (labels)

/-- From any representation of the prepared compound match, the joined
bindings are selected at entry. Both template continuations run on the
step and publish in the reached world; reopening after the first write
would discard the second join instead. -/
theorem captured_match_publishes_on_the_step
    {first : Store CapturedMatch.World (Control Bool) Continuation Result}
    (represented : Represents first (toWorldConfig CapturedMatch.initial)) :
    ∃ (last : Store CapturedMatch.World (Control Bool) Continuation Result) (a b : Frame),
      Relation.ReflTransGen
        (StoreStep (heWorldMachine CapturedMatch.environment.view CapturedMatch.environment.services
          CapturedMatch.environment.dispatch CapturedMatch.environment.lookup .unmarked true
          CapturedMatch.environment.arguments)) first last ∧
      Represents last (toWorldConfig ⟨CapturedMatch.finalWorld, true, .returning [], [],
        [(number 11, a), (number 20, b)]⟩) := by
  obtain ⟨a, b, source⟩ := CapturedMatch.source_runs_captured_templates
  obtain ⟨last, path, reached⟩ := he_world_source_prefix CapturedMatch.environment.arguments represented
    (source_to_finished source)
  exact ⟨last, a, b, path, reached⟩

/-- The authored effectful match publishes the two bound results in
the order of its actual firings, in the world reached by both writes. -/
theorem captured_match_reports_in_firing_order
    {first : Store CapturedMatch.World (Control Bool) Continuation Result}
    (represented : Represents first (toWorldConfig CapturedMatch.initial)) :
    let env := CapturedMatch.environment
    let M := heWorldMachine env.view env.services env.dispatch env.lookup .unmarked true env.arguments
    ∃ (last : Fired M) (path : Quiver.Path (show Fired M from first) last) (a b : Frame),
      Cell.control (.returning []) 0 ∈ labels Prod.fst last.present ∧
      observePath (publication M) path = [(number 11, a), (number 20, b)] ∧
      worldsOf (labels Prod.fst last.present) = {CapturedMatch.finalWorld} := by
  intro env M
  obtain ⟨a, b, source⟩ := CapturedMatch.source_runs_captured_templates
  obtain ⟨last, path, stopped, word, world⟩ :=
    (he_world_completed_ordered_iff (policy := .unmarked) env represented _ _).mp source
  exact ⟨last, path, a, b, stopped, word, world⟩

/-- A single HE publication path reads back from either ordering of
the initial history when only its bag was supplied. The new packet
is fixed, but the same physical path does not reconstruct old order. -/
theorem firing_path_does_not_order_the_prior_bag :
    let env := CapturedMatch.environment
    let M := heWorldMachine env.view env.services env.dispatch env.lookup .unmarked true env.arguments
    let a : Result := (number 11, Frame.empty)
    let b : Result := (number 20, Frame.empty)
    let report : Result := (number 30, Frame.empty)
    let starting : List Result → WorldConfiguration Bool CapturedMatch.World :=
      fun earlier => ⟨CapturedMatch.initialWorld, true, .returning [report], [], earlier⟩
    ∃ (first last : Fired M) (path : Quiver.Path first last),
      Represents first (toWorldConfig (starting [a, b])) ∧ Represents first (toWorldConfig (starting [b, a])) ∧
      observePath (publication M) path = [report] ∧ path.length = 1 ∧
      ∃ left right : WorldConfiguration Bool CapturedMatch.World,
        WorldSteps (admission := env.arguments) env.view env.services env.dispatch env.lookup .unmarked (starting [a, b]) left ∧
        WorldSteps (admission := env.arguments) env.view env.services env.dispatch env.lookup .unmarked (starting [b, a]) right ∧
        Represents last (toWorldConfig left) ∧ Represents last (toWorldConfig right) ∧
        left.emitted ≠ right.emitted := by
  intro env M a b report starting
  obtain ⟨first, represented⟩ := exists_represents (toWorldConfig (starting [a, b]))
  have equal : encode (toWorldConfig (starting [a, b])) = encode (toWorldConfig (starting [b, a])) :=
    (encode_eq_iff _ _).mpr ⟨rfl, rfl, rfl, by
      change (([a, b] : List Result) : Multiset Result) = ([b, a] : List Result)
      exact Multiset.coe_eq_coe.mpr (List.Perm.swap b a [])⟩
  have reverse : Represents first (toWorldConfig (starting [b, a])) :=
    ⟨represented.1, represented.2.trans equal⟩
  let next : Config CapturedMatch.World (Control Bool) Continuation Result :=
    ⟨CapturedMatch.initialWorld, .returning [], [], [a, b, report]⟩
  have moved : M.Step (toWorldConfig (starting [a, b])) next := .publish rfl
  obtain ⟨last, ⟨rule, member, commit⟩, reached⟩ :=
    machine_to_store (he_world_local true env.arguments) represented moved
  let selected : (show Fired M from first) ⟶ (show Fired M from last) := ⟨rule, member, commit⟩
  let path : Quiver.Path (show Fired M from first) (show Fired M from last) := Quiver.Path.cons .nil selected
  have exactReport := firing_emits_exact represented reached moved selected
  have word : observePath (publication M) path = [report] := by
    change (publication M selected).toList = [report]
    have appended : [a, b] ++ (publication M selected).toList = [a, b] ++ [report] := exactReport.symm
    simpa only [List.drop_left] using congrArg (fun rows : List Result => rows.drop ([a, b] : List Result).length)
      appended
  obtain ⟨left, follows, _, lrep, emittedL⟩ := he_world_firing_path_reads_ordered env.arguments represented path
  obtain ⟨right, follows', _, rrep, emittedR⟩ := he_world_firing_path_reads_ordered env.arguments reverse path
  refine ⟨first, last, path, represented, reverse, word, rfl, left, right, follows, follows', lrep, rrep, ?_⟩
  rw [emittedL, emittedR, word]
  intro same
  have firstValue := congrArg (fun rows : List Result => rows.head?.map Prod.fst) same
  simp [starting, a, b, number] at firstValue

/-- The two schedules of one retained match frontier have real admitted
executions. They reach the same world but publish different value bags.
Neither schedule reopens the match. -/
theorem captured_order_distinguished_on_the_step :
    let env := CapturedMatch.environment
    let machine := heWorldMachine env.view env.services env.dispatch env.lookup .unmarked true env.arguments
    let runs (selected output : List Result) :=
      ∃ first last : Store CapturedMatch.World (Control Bool) Continuation Result,
        Represents first (toWorldConfig (CapturedMatch.resumeAtMatch selected)) ∧
        Relation.ReflTransGen (StoreStep machine) first last ∧
        Represents last (toWorldConfig ⟨CapturedMatch.finalWorld,true,.returning [],[],output⟩)
    ∃ selected : List Result, ∃ a b : Frame,
      let left := [(number 11, a), (number 20, b)]
      let right := [(number 21, b), (number 11, a)]
      selected.length = 2 ∧ runs selected left ∧ runs selected.reverse right ∧
      ¬ (left.map (fun result => result.1.erase)).Perm (right.map (fun result => result.1.erase)) := by
  obtain ⟨selected,a,b,length,left,right,different⟩ := CapturedMatch.captured_order_can_change_bag
  refine ⟨selected,a,b,length,?_,?_,different⟩
  · obtain ⟨first, represented⟩ := exists_represents (toWorldConfig (CapturedMatch.resumeAtMatch selected))
    obtain ⟨last, path, reached⟩ := he_world_source_prefix CapturedMatch.environment.arguments represented
      (source_to_finished left)
    exact ⟨first,last,represented,path,reached⟩
  · obtain ⟨first, represented⟩ := exists_represents (toWorldConfig (CapturedMatch.resumeAtMatch selected.reverse))
    obtain ⟨last, path, reached⟩ := he_world_source_prefix CapturedMatch.environment.arguments represented
      (source_to_finished right)
    exact ⟨first,last,represented,path,reached⟩

/-- The same admitted trace can be cut after both templates have written but
before the collection is published. Resumption uses the saved answer frames.
The packed result preserves the child's answer order within the expression. -/
theorem captured_match_collects_on_the_step
    {first : Store CapturedMatch.World (Control Bool) Continuation Result}
    (represented : Represents first (toWorldConfig CapturedMatch.collectionStart)) :
    let env := CapturedMatch.environment
    let machine := heWorldMachine env.view env.services env.dispatch env.lookup .unmarked true env.arguments
    ∃ (cut last : Store CapturedMatch.World (Control Bool) Continuation Result) (a b : Frame),
      Relation.ReflTransGen (StoreStep machine) first cut ∧
      Represents cut (toWorldConfig (CapturedMatch.collectionPaused a b)) ∧
      Relation.ReflTransGen (StoreStep machine) cut last ∧
      Represents last (toWorldConfig ⟨(CapturedMatch.finalWorld.1, [a, b]), true, .returning [], [],
        [(CapturedMatch.pairs (number 11) (number 20), Frame.empty)]⟩) := by
  obtain ⟨a, b, child, _, resumed⟩ := CapturedMatch.collection_pauses_and_resumes
  obtain ⟨cut, before, paused⟩ := he_world_source_prefix CapturedMatch.environment.arguments represented child
  obtain ⟨last, after, completed⟩ := he_world_source_prefix CapturedMatch.environment.arguments paused
    (source_to_finished resumed)
  exact ⟨cut, last, a, b, before, paused, after, completed⟩

/-- The pending HE collector has an empty publication word but a
nonempty word of world changes. The resumed path publishes the one
packed result in the already reached world. -/
theorem captured_collection_shows_effects_before_publication
    {first : Store CapturedMatch.World (Control Bool) Continuation Result}
    (represented : Represents first (toWorldConfig CapturedMatch.collectionStart)) :
    let env := CapturedMatch.environment
    let M := heWorldMachine env.view env.services env.dispatch env.lookup .unmarked true env.arguments
    let project : CapturedMatch.World → List Atom := fun world => world.1 true
    let result : Result := (CapturedMatch.pairs (number 11) (number 20), Frame.empty)
    ∃ (cut last : Fired M) (firstPath : Quiver.Path (show Fired M from first) cut)
        (suffix : Quiver.Path cut last) (a b : Frame),
      let earlier := observePath (worldPublication M project) firstPath
      let later := observePath (worldPublication M project) suffix
      Represents cut (toWorldConfig (CapturedMatch.collectionPaused a b)) ∧
      Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.worldObserve
        (CapturedMatch.collectionPaused a b) = none ∧
      earlier ≠ [] ∧ earlier.filterMap Prod.snd = [] ∧
      earlier.foldl (fun _ item => item.1) (project CapturedMatch.initialWorld) = [] ∧
      later.filterMap Prod.snd = [result] ∧
      Represents last (toWorldConfig ⟨(CapturedMatch.finalWorld.1, [a, b]), true, .returning [], [], [result]⟩) := by
  intro env M project result
  obtain ⟨a, b, child, waiting, resumed⟩ := CapturedMatch.collection_pauses_and_resumes
  obtain ⟨cut, firstPath, paused, exactPrefix⟩ :=
    he_world_source_lifts_cuts project env.arguments represented child
  obtain ⟨last, suffix, completed, exactSuffix⟩ :=
    he_world_source_lifts_cuts project env.arguments paused (source_to_finished resumed)
  have firstRead := FramedMachine.worldCut_readouts project exactPrefix
  have following := FramedMachine.worldCut_readouts project exactSuffix
  have empty : project CapturedMatch.finalWorld = [] :=
    CapturedMatch.requery_after_first_loses_the_later_selection.2.1
  have contents :
      (observePath (worldPublication M project) firstPath).foldl (fun _ item => item.1)
        (project CapturedMatch.initialWorld) = [] := firstRead.1.trans empty
  have nonempty : project CapturedMatch.initialWorld ≠ [] := by decide +kernel
  refine ⟨cut, last, firstPath, suffix, a, b, paused, waiting, ?_, ?_, contents, ?_, completed⟩
  · intro noChanges
    rw [noChanges, List.foldl_nil] at contents
    exact nonempty contents
  · exact firstRead.2.symm
  · exact following.2.symm

/-- A real effectful match returns through its own collector, saving
both bindings in the already modified world. Its packed answer has
the original caller's activation and the retired frame cannot return
again. -/
theorem captured_match_collects_with_receipt :
    let env := CapturedMatch.environment
    ∃ (first : Store CapturedMatch.World (Control Bool) Continuation Result)
      (last : CustodyStore CapturedMatch.World (Control Bool) Continuation Result CollectorCustody.Phase)
      (ticket : Ticket (CollectorCustody.ReceiptId Bool CapturedMatch.World))
      (receiver : CollectorCustody.ReceiptId Bool CapturedMatch.World) (a b : Frame),
      Represents first (toWorldConfig CapturedMatch.collectionStart) ∧
      Relation.ReflTransGen (CustodyStep (CollectorCustody.machine env .unmarked true))
        (first, Ledger.root first.present) last ∧
      Represents last.1 (toWorldConfig ⟨(CapturedMatch.finalWorld.1, [a, b]), true,
        .returning [(CapturedMatch.pairs (number 11) (number 20), Frame.empty)], [], []⟩) ∧
      last.2.mark receiver = some (.control ticket .completed) ∧
      ticket.key ∈ last.2.issued ∧ ticket.key ∉ last.1.present := by
  intro env
  obtain ⟨first, represented⟩ := exists_represents (toWorldConfig CapturedMatch.collectionStart)
  obtain ⟨operand, a, b, form, child, capture⟩ := CapturedMatch.collection_plan
  have starts : Represents first ⟨CapturedMatch.initialWorld,
      .work (.minimal [] [] none (.expression .active [.symbol "collapse-bind", operand]) Frame.empty), [], []⟩ := by
    simpa only [toWorldConfig, CapturedMatch.collectionStart, form] using represented
  have service : env.services.snapshots = some (SnapshotServices.appendModel Bool CapturedMatch.StoreWorld) := rfl
  obtain ⟨last, ticket, receiver, path, reached, _, _, stamp, _, issued, retired, _⟩ :=
    CollectorCustody.collector_completed_return env .unmarked true service child capture starts
      (Ledger.root_covers first.present) (.localReturn [])
  exact ⟨first, last, ticket, receiver, a, b, represented, path, reached, stamp, issued, retired⟩

/-- Starting from an authored nested collapse, a legitimate outer
opening makes a physical frame. The unqualified inner rule can take
that very occurrence, despite producing the correct pair of frames
as a bag of labels. -/
theorem nested_collapse_raw_step_can_retire_outer_ticket :
    let env := CapturedMatch.environment
    let authored : Value := .expression .active [.symbol "collapse-bind", CapturedMatch.collectMatch]
    ∃ (first opened reached : Store CapturedMatch.World (Control Bool) Continuation Result)
      (outer : CollectorCustody.ReceiptId Bool CapturedMatch.World),
      Represents first ⟨CapturedMatch.initialWorld, .work (.minimal [] [] none authored Frame.empty), [], []⟩ ∧
      StoreStep (CollectorCustody.machine env .unmarked true) first opened ∧
      outer ∈ opened.present ∧
      StoreStep (CollectorCustody.machine env .unmarked true) opened reached ∧
      outer ∉ reached.present ∧
      ∃ operand : Value,
        CapturedMatch.collectMatch = .expression .active [.symbol "collapse-bind", operand] ∧
        Represents reached ⟨CapturedMatch.initialWorld, .work (.minimal [] [] none operand Frame.empty),
          [.collect Frame.empty, .collect Frame.empty], []⟩ := by
  intro env authored
  obtain ⟨first, represented⟩ := exists_represents
    (W := CapturedMatch.World) (C := Control Bool) (F := Continuation) (A := Result)
    ⟨CapturedMatch.initialWorld, .work (.minimal [] [] none authored Frame.empty), [], []⟩
  have service : env.services.snapshots = some (SnapshotServices.appendModel Bool CapturedMatch.StoreWorld) := rfl
  obtain ⟨opening, _, _, outer, _, _, slot, stamp, afterOpen, _, _⟩ :=
    CollectorCustody.open_collector env .unmarked true service represented (Ledger.root_covers first.present)
      (.localReturn [])
  have outerLive : outer ∈ opening.result.present :=
    ((opening.covered (Ledger.root_covers first.present)).2 _).mpr (by rw [stamp]; rfl)
  obtain ⟨operand, _, _, form, _, _⟩ := CapturedMatch.collection_plan
  have next : Represents opening.result ⟨CapturedMatch.initialWorld,
      .work (.minimal [] [] none (.expression .active [.symbol "collapse-bind", operand]) Frame.empty),
      [.collect Frame.empty], []⟩ := by
    simpa only [form] using afterOpen
  obtain ⟨reached, raw, gone, final⟩ :=
    CollectorCustody.raw_padded_open_can_replace_collector env .unmarked true service next outerLive slot
  exact ⟨first, opening.result, reached, outer, represented, opening.raw_step, outerLive, raw, gone,
    operand, form, final⟩

/-- Three authored collectors share the same activation. The innermost
reply goes to the immediately enclosing collector, not the equal older
one. The older frame keeps its physical key and mark through both
template writes and both layers of capture. -/
theorem nested_collectors_refuse_equal_older_frame :
    let env := CapturedMatch.environment
    let wrap : Value → Value := fun child => .expression .active [.symbol "collapse-bind", child]
    let packed := CapturedMatch.pairs (number 11) (number 20)
    let twice : Value := .expression .active [.expression .active [packed, .grounded (.int 2)]]
    let start : WorldConfiguration Bool CapturedMatch.World := ⟨CapturedMatch.initialWorld, true,
      .work (.minimal [] [] none (wrap (wrap CapturedMatch.collectMatch)) Frame.empty), [], []⟩
    ∃ (first : Store CapturedMatch.World (Control Bool) Continuation Result)
      (ready last : CustodyStore CapturedMatch.World (Control Bool) Continuation Result CollectorCustody.Phase)
      (older child parent : Ticket (CollectorCustody.ReceiptId Bool CapturedMatch.World))
      (reply receiver : CollectorCustody.ReceiptId Bool CapturedMatch.World) (a b : Frame),
      Represents first (toWorldConfig start) ∧
      Relation.ReflTransGen (CustodyStep (CollectorCustody.machine env .unmarked true))
        (first, Ledger.root first.present) ready ∧
      Represents ready.1 ⟨(CapturedMatch.finalWorld.1, [a, b]), .returning [(packed, Frame.empty)],
        [.collect Frame.empty, .collect Frame.empty], []⟩ ∧
      ready.2.mark older.key = some (.control older .onStack) ∧
      parent.parent = some older.key ∧
      ∃ landing : CustodyFiring (CollectorCustody.machine env .unmarked true) ready.1 ready.2,
        CollectorCustody.admitsHandoff ready.2 landing.selected reply child parent ∧
        (∀ selected claimed, ¬ CollectorCustody.admitsHandoff ready.2 selected reply claimed older) ∧
        Relation.ReflTransGen (CustodyStep (CollectorCustody.machine env .unmarked true))
          (landing.result, landing.after) last ∧
        Represents last.1 ⟨(CapturedMatch.finalWorld.1, [a, b, Frame.empty]),
          .returning [(twice, Frame.empty)], [.collect Frame.empty], []⟩ ∧
        last.2.mark older.key = some (.control older .onStack) ∧
        last.2.mark receiver = some (.control parent .completed) ∧
        last.2.mark reply = none ∧
        ∃ y, WorldSteps (admission := env.arguments) env.view env.services env.dispatch env.lookup .unmarked start y ∧
          Represents last.1 (toWorldConfig y) := by
  intro env wrap packed twice start
  obtain ⟨first, represented⟩ := exists_represents (toWorldConfig start)
  have service : env.services.snapshots = some (SnapshotServices.appendModel Bool CapturedMatch.StoreWorld) := rfl
  have initially := Ledger.root_covers (Phase := CollectorCustody.Phase) first.present
  obtain ⟨opening, owner, _, oldest, _, _, oldestSlot, oldestStamp, innerRaw, _, _⟩ :=
    CollectorCustody.open_collector env .unmarked true service represented initially (.localReturn [])
  let older : Ticket (CollectorCustody.ReceiptId Bool CapturedMatch.World) := ⟨oldest, owner, none⟩
  have openCover := opening.covered initially
  have oldestLive : oldest ∈ opening.result.present := (openCover.2 _).mpr (by rw [oldestStamp]; rfl)
  obtain ⟨operand, a, b, form, body, capture⟩ := CapturedMatch.collection_plan
  have starts : Represents opening.result ⟨CapturedMatch.initialWorld,
      .work (.minimal [] [] none
        (.expression .active [.symbol "collapse-bind", .expression .active [.symbol "collapse-bind", operand]])
        Frame.empty), [.collect Frame.empty], []⟩ := by
    simpa only [wrap, form] using innerRaw
  have advance : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.CaptureRowsRel
      (SnapshotServices.appendModel Bool CapturedMatch.StoreWorld) true
      (CapturedMatch.finalWorld.1, [a, b]) [(packed, Frame.empty)] []
      twice (CapturedMatch.finalWorld.1, [a, b, Frame.empty]) :=
    .cons (by simp [packed, CapturedMatch.pairs, Value.erase, Atom.empty]) ⟨rfl, rfl⟩ .nil
  obtain ⟨ready, child, parent, reply, trail, atReturn, parentSlot, up, keepsReady,
    landing, licensed, last, receiver, finish, reached, lastCover, completed, _, _, replyGone, keepsLast⟩ :=
    CollectorCustody.nested_collector_completed_return env .unmarked true service body capture advance
      starts openCover (.owned (parent := older) oldestStamp oldestSlot)
  have kept := (keepsReady oldestLive oldestSlot (by decide)).2.trans oldestStamp
  have retained := (keepsLast oldestLive oldestSlot (by decide)).2.trans oldestStamp
  have forgotten : last.2.mark reply = none := by
    have absent : ¬ (last.2.mark reply).isSome := fun marked => replyGone ((lastCover.2 _).mpr marked)
    cases tag : last.2.mark reply with
    | none => rfl
    | some mark => simp [tag] at absent
  have opened : CustodyStep (CollectorCustody.machine env .unmarked true)
      (first, Ledger.root first.present) (opening.result, opening.after) := ⟨opening, rfl⟩
  have toReady := Relation.ReflTransGen.head opened trail
  have toLast := (CustodyStep.raw_path toReady).trans ((Relation.ReflTransGen.single landing.raw_step).trans
    (CustodyStep.raw_path finish))
  obtain ⟨y, executes, _, representedLast⟩ := he_world_target_prefix env.arguments represented toLast
  refine ⟨first, ready, last, older, child, parent, reply, receiver, a, b, represented,
    toReady, atReturn, kept, up, landing, licensed, ?_, finish,
    reached, retained, completed, forgotten, y, executes, representedLast⟩
  intro selected claimed wrong
  have same := CollectorCustody.handoff_parent_unique licensed wrong
  have sameSlot := congrArg (fun ticket : Ticket (CollectorCustody.ReceiptId Bool CapturedMatch.World) =>
    ticket.key.1) same
  rw [parentSlot, oldestSlot] at sameSlot
  cases sameSlot

end CapturedMatch

namespace SyntaxSize

open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls (World)
open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.ExpressionSize
  (environment size counted expression_size_counts DataOnly)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame Result)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry (Value)
open Mettapedia.Machines.ProgressObservation (observePath)
open MeTTaCalculus.OccurrenceCommits (labels)

def seen (value : Atom) : Atom := app "seen" [value]
def collectSeen : Atom := app "collapse" [app "match" [.symbol "&self", seen (.var "z"), .var "z"]]
def rawSize : Atom := size collectSeen

private def heEntry (world : World) (label : Bool) : WorldConfiguration Bool World :=
  ⟨world, label, .work (.atom [] [] (Value.ofAtom rawSize) Atom.undefinedType Frame.empty), [], []⟩

/-- HE completes the authored expression-demand application on the
step. Its semantic result is the length of the held syntax; the space
world is unchanged, and a terminal control is required. -/
theorem held_size_on_the_step (world : World) (label : Bool) (data : DataOnly world label) :
    let M := heWorldMachine environment.view environment.services environment.dispatch environment.lookup
      .unmarked label environment.arguments
    ∃ (first last : Fired M) (path : Quiver.Path first last),
      Represents first (toWorldConfig (heEntry world label)) ∧
      Cell.control (.returning []) 0 ∈ labels Prod.fst last.present ∧
      observePath (publication M) path = [(counted 2, Frame.empty)] ∧
      worldsOf (labels Prod.fst last.present) = {world} := by
  intro M
  obtain ⟨first, represented⟩ := exists_represents (toWorldConfig (heEntry world label))
  have derived : (heEntry world label).SourceRel environment .unmarked [(counted 2, Frame.empty)] world := by
    refine ⟨_, _, _, .work ?_, .nil _, rfl⟩
    exact expression_size_counts world label [.symbol "collapse", app "match" [.symbol "&self", seen (.var "z"), .var "z"]] data
  obtain ⟨last, path, terminal, word, reached⟩ :=
    (he_world_completed_ordered_iff (policy := .unmarked) environment represented _ _).mp derived
  exact ⟨first, last, path, represented, terminal, word, reached⟩

open Mettapedia.Languages.MeTTa.PeTTa.StreamingOnTheStep

def copies (three : Bool) : List Atom :=
  if three then List.replicate 3 (seen (.symbol "same")) else []

def pettaEntry (three : Bool) (source : Atom) : Streaming.State :=
  Streaming.enter { state := NamedSpaces.Store.new (copies three) [] } source

private def readWorld (world : Streaming.World) : List Atom := world.state.core
private def cutValues (cut : List Atom × Option Unifying.Answer) : List Atom × Option Atom :=
  (cut.1, cut.2.map (fun answer => Unifying.resolve answer.bindings answer.value))

private def sizeBudget (three : Bool) : Nat := if three then 18 else 12

/-- PeTTa actually evaluates the same caller operand, including its
collection boundary. Duplicates are counted as separate occurrences. -/
theorem source_petta_size (three : Bool) :
    let final := Streaming.advance noProgram (sizeBudget three) (pettaEntry three rawSize)
    final.agenda = [] ∧ final.world.state.core = copies three ∧
      Streaming.values final = [(counted (copies three).length).erase] := by
  cases three <;> cbv

theorem petta_size_world_word (three : Bool) :
    (cutWord noProgram readWorld (sizeBudget three) (pettaEntry three rawSize)).map cutValues =
      [(copies three, some (counted (copies three).length).erase)] := by
  cases three <;> cbv

/-- Lift the actual PeTTa entry through the query, collection and
strict size call. The journal emits one count, not the quoted syntax
and not a deduplicated answer count. -/
theorem eager_size_on_the_step (three : Bool) :
    ∃ (first last : Fired (machine noProgram)) (path : Quiver.Path first last),
      Represents first (configOf (pettaEntry three rawSize)) ∧
      Represents last (configOf (Streaming.advance noProgram (sizeBudget three) (pettaEntry three rawSize))) ∧
      (observePath (streamedWorld noProgram readWorld) path).map cutValues =
        [(copies three, some (counted (copies three).length).erase)] := by
  obtain ⟨first, represented⟩ := exists_represents (configOf (pettaEntry three rawSize))
  obtain ⟨last, path, _, reached, observed⟩ :=
    advance_world_stream_lifts noProgram readWorld (sizeBudget three) represented
  exact ⟨first, last, path, represented, reached, by rw [observed, petta_size_world_word]⟩

private def item (n : Nat) : Atom := app "item" [.grounded (.int n)]
private def mark (n : Nat) : Atom := seen (.grounded (.int n))
private def inputs : List Atom := [item 1, item 2]
private def effectful : Atom :=
  app "collapse" [app "match" [.symbol "&self", app "item" [.var "x"],
    app "let" [.var "ack", app "add-atom" [.symbol "&self", seen (.var "x")], rawSize]]]
private def effectEntry : Streaming.State :=
  Streaming.enter { state := NamedSpaces.Store.new inputs [] } effectful
private def collectedCounts : Atom := .expression [.grounded (.int 1), .grounded (.int 2)]

/-- In the PeTTa source each template writes and then really counts
the current view. The outer collector finishes with both counts and
keeps both writes in its shared world. -/
theorem source_effectful_size :
    let last := Streaming.advance noProgram 61 effectEntry
    last.agenda = [] ∧ last.world.state.core = inputs ++ [mark 1, mark 2] ∧
      Streaming.values last = [collectedCounts] := by cbv

private theorem effectful_word :
    (cutWord noProgram readWorld 61 effectEntry).map cutValues =
      [(inputs ++ [mark 1], none), (inputs ++ [mark 1, mark 2], none),
        (inputs ++ [mark 1, mark 2], some collectedCounts)] := by cbv

theorem effectful_size_on_the_step :
    ∃ (first last : Fired (machine noProgram)) (path : Quiver.Path first last),
      Represents first (configOf effectEntry) ∧
      Represents last (configOf (Streaming.advance noProgram 61 effectEntry)) ∧
      (observePath (streamedWorld noProgram readWorld) path).map cutValues =
        [(inputs ++ [mark 1], none), (inputs ++ [mark 1, mark 2], none),
          (inputs ++ [mark 1, mark 2], some collectedCounts)] := by
  obtain ⟨first, represented⟩ := exists_represents (configOf effectEntry)
  obtain ⟨last, path, _, reached, observed⟩ :=
    advance_world_stream_lifts noProgram readWorld 61 represented
  exact ⟨first, last, path, represented, reached, by rw [observed, effectful_word]⟩

end SyntaxSize

namespace EffectfulLet

open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls (World environment)
open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.Quotation
  (letEntry letArgumentCut letReached letWorld authored_effectful_let)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame Result)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry (Value)
open Mettapedia.Machines.ProgressObservation (observePath)
open MeTTaCalculus.OccurrenceCommits (labels)

private def heDone (label : Bool) (frame : Frame) : WorldConfiguration Bool World :=
  ⟨letWorld, label, .returning [], [], [(.expression .active [], frame)]⟩

/-- Both parts of the actual effectful execution lift, for any
declared view. The argument cut separates the written store from a
not-yet-entered body; only the suffix publishes the bound value. -/
theorem he_effectful_let_on_the_step {View : Type} [DecidableEq View]
    (view : World → View) (label : Bool) :
    let M := heWorldMachine environment.view environment.services environment.dispatch environment.lookup
      .unmarked label environment.arguments
    ∃ (frame : Frame) (first cut last : Fired M)
        (prepare : Quiver.Path first cut) (resume : Quiver.Path cut last),
      Represents first (toWorldConfig (letEntry label)) ∧
      Represents cut (toWorldConfig (letArgumentCut label)) ∧
      Represents last (toWorldConfig (heDone label frame)) ∧
      M.CutTrace (FramedMachine.worldCut view) prepare.length (toWorldConfig (letEntry label))
        (toWorldConfig (letArgumentCut label)) (observePath (worldPublication M view) prepare) ∧
      M.CutTrace (FramedMachine.worldCut view) resume.length (toWorldConfig (letArgumentCut label))
        (toWorldConfig (heDone label frame)) (observePath (worldPublication M view) resume) ∧
      frame.read .unmarked (.var "picked") = .expression .active [] := by
  intro M
  obtain ⟨frame, prepared, resumed, retained⟩ := authored_effectful_let label
  obtain ⟨first, represented⟩ := exists_represents (toWorldConfig (letEntry label))
  obtain ⟨cut, prepare, atCut, firstTrace⟩ :=
    he_world_source_lifts_cuts view environment.arguments represented prepared
  obtain ⟨last, resume, atEnd, lastTrace⟩ :=
    he_world_source_lifts_cuts view environment.arguments atCut
      (Mettapedia.Languages.MeTTa.HE.RecursiveExecution.Contextual.Stateful.source_to_finished resumed)
  exact ⟨frame, first, cut, last, prepare, resume, represented, atCut, atEnd, firstTrace, lastTrace, retained⟩

private def unitVisible (label : Bool) (world : World) : Bool :=
  decide (Atom.unit ∈ world label)

private theorem unit_not_initial (label : Bool) : unitVisible label letWorld = false := by
  cases label <;> decide +kernel

private theorem unit_reached (label : Bool) : unitVisible label (letReached label) = true := by
  simp [unitVisible, letReached]

/-- A world-sensitive reader distinguishes the real put/take interval
from its endpoint cut. The very same firing path under the answer-only
observer has exactly one event. This gives an observation criterion,
not permission to move a guard or erase a physical dependency. -/
theorem he_let_observer_boundary (label : Bool) :
    let M := heWorldMachine environment.view environment.services environment.dispatch environment.lookup
      .unmarked label environment.arguments
    let view := unitVisible label
    ∃ (frame : Frame) (first last : Fired M) (path : Quiver.Path first last),
      Represents first (toWorldConfig (letEntry label)) ∧
      Represents last (toWorldConfig (heDone label frame)) ∧
      let detailed := observePath (worldPublication M view) path
      detailed ≠ (reportCut (view letWorld) (view letWorld) (detailed.filterMap Prod.snd).head?).toList ∧
      observePath (worldPublication M (fun _ => ())) path = [((), some (.expression .active [], frame))] := by
  intro M view
  obtain ⟨frame, first, cut, last, prepare, resume, represented, _atCut, atEnd, front, tail, _⟩ :=
    he_effectful_let_on_the_step view label
  let path := prepare.comp resume
  let detailed := observePath (worldPublication M view) path
  have together : M.CutTrace (FramedMachine.worldCut view) (prepare.length + resume.length)
      (toWorldConfig (letEntry label)) (toWorldConfig (heDone label frame)) detailed := by
    unfold detailed path
    rw [Mettapedia.Machines.ProgressObservation.observePath_comp]
    exact Mettapedia.GSLT.Ultrainfinite.Route.ObservedTrace.comp _ front tail
  have headSeen : observePath (worldPublication M view) prepare ≠ [] := by
    intro none
    have reached := (M.worldCut_readouts view front).1
    rw [none, List.foldl_nil] at reached
    exact Bool.false_ne_true ((unit_not_initial label).symm.trans (reached.trans (unit_reached label)))
  have tailSeen : observePath (worldPublication M view) resume ≠ [] := by
    intro none
    have reached := (M.worldCut_readouts view tail).1
    rw [none, List.foldl_nil] at reached
    exact (show true ≠ false by decide)
      ((unit_reached label).symm.trans (reached.trans (unit_not_initial label)))
  have long : 1 < detailed.length := by
    have a := List.length_pos_iff.mpr headSeen
    have b := List.length_pos_iff.mpr tailSeen
    simp only [detailed, path, Mettapedia.Machines.ProgressObservation.observePath_comp, List.length_append]
    omega
  have packets : detailed.filterMap Prod.snd = [(.expression .active [], frame)] :=
    (M.worldCut_readouts view together).2.symm
  have erased := coarsen_worldPublication_path view (fun _ => ()) represented path
  change coarsenCuts (fun _ => ()) (view letWorld) detailed =
    observePath (worldPublication M (fun _ => ())) path at erased
  rw [coarsenCuts_unit, packets] at erased
  exact ⟨frame, first, last, path, represented, atEnd,
    fun single => (Nat.not_le_of_lt long) ((M.worldCut_endpoint_iff view together).mp single), erased.symm⟩

open Mettapedia.Languages.MeTTa.PeTTa.StreamingOnTheStep

private def marker : Atom := app "let-marker" [.symbol "seen"]
private def pettaWritten : Atom :=
  app "let" [.var "picked", app "add-atom" [.symbol "&self", marker],
    app "match" [.symbol "&self", app "let-marker" [.var "tag"], app "reached" [.var "picked", .var "tag"]]]
private def pettaNoAnswer : Atom :=
  app "let" [.var "none", app "match" [.symbol "&self", app "let-marker" [.symbol "absent"], .symbol "ignored"],
    app "add-atom" [.symbol "&self", .symbol "wrong-body"]]
private def pettaAckAsKey : Atom :=
  app "let" [.var "picked", app "add-atom" [.symbol "&self", Atom.unit],
    app "match" [.symbol "&self", .var "picked", app "let" [.var "released",
      app "remove-atom" [.symbol "&self", .var "picked"], .var "picked"]]]
private def pettaAcknowledgment : Atom := app "reached" [Effects.boolean true, .symbol "seen"]

inductive LetProbe where
  | observeWrite | noAnswer | ackAsKey

private def pettaEntry : LetProbe → Streaming.State
  | .observeWrite => Streaming.enter {state := NamedSpaces.Store.new [] []} pettaWritten
  | .noAnswer => Streaming.enter {state := NamedSpaces.Store.new [marker] []} pettaNoAnswer
  | .ackAsKey => Streaming.enter {state := NamedSpaces.Store.new [] []} pettaAckAsKey

private def letSteps : LetProbe → Nat
  | .observeWrite => 31
  | .noAnswer => 5
  | .ackAsKey => 16

private def viewCore (world : Streaming.World) : List Atom := world.state.core
private def visibleCut (row : List Atom × Option Unifying.Answer) : List Atom × Option Atom :=
  (row.1, row.2.map (fun answer => Unifying.resolve answer.bindings answer.value))

private def letWord : LetProbe → List (List Atom × Option Atom)
  | .observeWrite => [([marker], none), ([marker], some pettaAcknowledgment)]
  | .noAnswer => []
  | .ackAsKey => [([Atom.unit], none)]

private def letVisible : LetProbe → List Atom × List Atom
  | .observeWrite => ([marker], [pettaAcknowledgment])
  | .noAnswer => ([marker], [])
  | .ackAsKey => ([Atom.unit], [])

set_option maxHeartbeats 1000000 in
private theorem petta_completed (probe : LetProbe) :
    let last := Streaming.advance noProgram (letSteps probe) (pettaEntry probe)
    last.agenda = [] ∧ (last.world.state.core, Streaming.values last) = letVisible probe := by
  cases probe <;> cbv

set_option maxHeartbeats 1000000 in
private theorem petta_effect_word (probe : LetProbe) :
    (cutWord noProgram viewCore (letSteps probe) (pettaEntry probe)).map visibleCut = letWord probe := by
  cases probe <;> cbv

/-- The PeTTa reader observes the new row and binds the Boolean
acknowledgment. A completed no-answer operand never executes its body.
Using the Boolean acknowledgment as a key finds no unit, so the write
survives. All three runs have checked terminal and world observations. -/
theorem petta_effectful_let_on_the_step (probe : LetProbe) :
    let finished := Streaming.advance noProgram (letSteps probe) (pettaEntry probe)
    ∃ (first last : Fired (machine noProgram)) (path : Quiver.Path first last),
      Represents first (configOf (pettaEntry probe)) ∧
      Represents last (configOf finished) ∧
      finished.agenda = [] ∧ (finished.world.state.core, Streaming.values finished) = letVisible probe ∧
      (observePath (streamedWorld noProgram viewCore) path).map visibleCut = letWord probe ∧
      (observePath (streamedWorld noProgram (fun _ => ())) path).filterMap
        (fun cut => cut.2.map (fun answer => Unifying.resolve answer.bindings answer.value)) = (letVisible probe).2 := by
  intro finished
  obtain ⟨first, represented⟩ := exists_represents (configOf (pettaEntry probe))
  obtain ⟨last, path, _, reached, word⟩ :=
    advance_world_stream_lifts noProgram viewCore (letSteps probe) represented
  obtain ⟨terminal, visible⟩ := petta_completed probe
  have cuts : (observePath (streamedWorld noProgram viewCore) path).map visibleCut = letWord probe := by
    rw [word, petta_effect_word]
  refine ⟨first, last, path, represented, reached, terminal, visible, cuts, ?_⟩
  have projected := coarsen_streamedWorld_path noProgram viewCore (fun _ => ()) represented path
  have packets := coarsenCuts_answers (fun _ : List Atom => ()) (viewCore (pettaEntry probe).world)
    (observePath (streamedWorld noProgram viewCore) path)
  rw [projected] at packets
  have readPackets := congrArg (List.map (fun answer : Unifying.Answer =>
    Unifying.resolve answer.bindings answer.value)) packets
  have cutPackets := congrArg (List.filterMap Prod.snd) cuts
  simp only [List.filterMap_map, visibleCut, Function.comp_apply] at cutPackets
  simp only [List.map_filterMap] at readPackets
  exact readPackets.trans (cutPackets.trans (by cases probe <;> rfl))

end EffectfulLet

end NamedDifferences

#print axioms NamedDifferences.removal
#print axioms NamedDifferences.return_type_reevaluation
#print axioms NamedDifferences.held_argument_under_undefined
#print axioms NamedDifferences.unquote_context_on_the_step
#print axioms NamedDifferences.quote_context_on_the_step
#print axioms NamedDifferences.open_quote_on_the_step
#print axioms NamedDifferences.open_unquote_on_the_step
#print axioms NamedDifferences.marker_dialects_separate
#print axioms NamedDifferences.captured_match_publishes_on_the_step
#print axioms NamedDifferences.captured_match_reports_in_firing_order
#print axioms NamedDifferences.firing_path_does_not_order_the_prior_bag
#print axioms NamedDifferences.captured_order_distinguished_on_the_step
#print axioms NamedDifferences.captured_match_collects_on_the_step
#print axioms NamedDifferences.captured_match_collects_with_receipt
#print axioms NamedDifferences.nested_collapse_raw_step_can_retire_outer_ticket
#print axioms NamedDifferences.nested_collectors_refuse_equal_older_frame
#print axioms NamedDifferences.SyntaxSize.held_size_on_the_step
#print axioms NamedDifferences.SyntaxSize.eager_size_on_the_step
#print axioms NamedDifferences.SyntaxSize.effectful_size_on_the_step
#print axioms NamedDifferences.EffectfulLet.he_effectful_let_on_the_step
#print axioms NamedDifferences.EffectfulLet.he_let_observer_boundary
#print axioms NamedDifferences.EffectfulLet.petta_effectful_let_on_the_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep
