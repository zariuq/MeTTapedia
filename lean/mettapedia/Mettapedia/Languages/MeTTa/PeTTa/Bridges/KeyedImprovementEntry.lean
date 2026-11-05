import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio

/-!
# Checked authored entry for a keyed-improvement block

Preparation inspects actual selected clauses for captured arguments. Function
and local-variable names are parameters. The completed observation contains
the full state and exact answer list. Exact pages decline, and failed private
validation selects reference execution without publishing a partial edit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open Eval SpaceSemantics NamedSpaces KeyedImprovementSource
open DeclarativeSpec (Runs)

def call (function : String) (names : Names) : Atom :=
  .expression [.symbol function, .var names.space, .var names.vertex, .var names.candidate]

structure Certificate (program : Program) (function : String) (names : Names) (head : String)
    (target : Handle) (key candidate : Nat) : Type where
  notIO : ioHead function = false
  notNative : StdLib.known function = false
  notControl : function ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]
  registered : program.equations.any (·.head == function) = true
  selected : clauses program function [Effects.handleValue target, number key, number candidate] =
    [.evaluate (bindings names target key candidate) (source names head)]

def prepare (program : Program) (function : String) (names : Names) (head : String)
    (target : Handle) (key candidate : Nat) : Option (Certificate program function names head target key candidate) :=
  if noIO : ioHead function = false then
    if noNative : StdLib.known function = false then
      if ordinary : function ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"] then
        if registered : program.equations.any (·.head == function) = true then
          match chosen : clauses program function [Effects.handleValue target, number key, number candidate] with
          | [.evaluate bound body] =>
              if sameBindings : bound = bindings names target key candidate then
                if sameBody : body = source names head then
                  some ⟨noIO, noNative, ordinary, registered, by simpa only [sameBindings, sameBody] using chosen⟩
                else none
              else none
          | _ => none
        else none
      else none
    else none
  else none

theorem Certificate.prepared {program : Program} {function : String} {names : Names} {head : String}
    {target : Handle} {key candidate : Nat}
    (certificate : Certificate program function names head target key candidate) :
    (prepare program function names head target key candidate).isSome = true := by
  unfold prepare
  simp only [dif_pos certificate.notIO, dif_pos certificate.notNative,
    dif_pos certificate.notControl, dif_pos certificate.registered]
  have selected := certificate.selected
  split <;> simp_all

theorem Certificate.call_returns {program : Program} {function : String} {names : Names} {head : String}
    {target : Handle} {key candidate : Nat}
    (certificate : Certificate program function names head target key candidate)
    (caller : Subst) (arguments : [names.space, names.vertex, names.candidate].map (fun name => applySubst caller (.var name)) =
      [Effects.handleValue target, number key, number candidate])
    (before after : Effects.State) (answers : List Atom)
    (completed : KeyedImprovementSource.run names head target key candidate before = some (after, answers)) :
    Returns program caller before (call function names) after answers := by
  have body := returns names head program target key candidate before after answers completed
  have invoked : (theory program).MultiStep
      {state := before, control := .arguments caller (.function function) []
        [Effects.handleValue target, number key, number candidate] 3}
      (finished after answers [] []) := by
    refine .step ?_ (single_sequence_answers program before after _ answers body)
    apply step_transition
    simp [step, certificate.notIO, certificate.notNative, certificate.selected]
  apply call_answers program caller before after function _ answers (by simp [certificate.registered]) _ certificate.notControl
  exact variable_arguments_answers program caller before after (.function function)
    [names.space, names.vertex, names.candidate] [] 0 answers
    (by simpa only [List.nil_append, arguments, List.length_cons, List.length_nil, Nat.zero_add] using invoked)

def complete (after : Effects.State) (answers : List Atom) : PureCallPortfolio.Completed := ⟨after, answers, [], []⟩

theorem source_meaning {program : Program} {function : String} {names : Names} {head : String}
    {target : Handle} {key candidate : Nat}
    (certificate : Certificate program function names head target key candidate)
    (caller : Subst) (arguments : [names.space, names.vertex, names.candidate].map (fun name => applySubst caller (.var name)) =
      [Effects.handleValue target, number key, number candidate])
    (before after : Effects.State) (answers : List Atom)
    (completed : KeyedImprovementSource.run names head target key candidate before = some (after, answers)) :
    PureCallPortfolio.sourceMeaning program caller (call function names) before = {complete after answers} := by
  have returned := certificate.call_returns caller arguments before after answers completed
  ext observed
  change Runs program {state := before, control := .evaluate caller (call function names)}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [← completed_run_iff_derivation, path_completed_iff program _ after answers [] [] returned]
  cases observed
  simp [complete, PureCallPortfolio.Completed.mk.injEq]

def region {Regime : Type} {program : Program} {function : String} {names : Names} {head : String}
    {target : Handle} {key candidate : Nat} (regime : Regime)
    (certificate : Certificate program function names head target key candidate)
    (caller : Subst) (arguments : [names.space, names.vertex, names.candidate].map (fun name => applySubst caller (.var name)) =
      [Effects.handleValue target, number key, number candidate]) :
    CertifiedRegion (PureCallPortfolio.boundary program caller (call function names)) Regime where
  regime := regime
  Artifact := PureCallPortfolio.Completed
  attempt before := match KeyedImprovementSource.run names head target key candidate before with
    | none => .declined before
    | some receipt => .committed (complete receipt.1 receipt.2)
  decode receipt := {receipt}
  restores before restored declined := by
    dsimp only at declined
    split at declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
    · cases declined
  exact before receipt committed := by
    split at committed
    · cases committed
    next result computed =>
      cases PartialRegionPlan.Attempt.committed.inj committed
      exact (source_meaning certificate caller arguments before result.1 result.2 computed).symm

def classify {Regime : Type} (observation : PureCallExtraction.Observation) (regime : Regime)
    (program : Program) (function : String) (names : Names) (head : String) (target : Handle) (key candidate : Nat)
    (caller : Subst) (arguments : [names.space, names.vertex, names.candidate].map (fun name => applySubst caller (.var name)) =
      [Effects.handleValue target, number key, number candidate]) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program caller (call function names)) Regime) :=
  match observation with
  | .exactPage => none
  | .completedResult => (prepare program function names head target key candidate).map
      (fun certificate => region regime certificate caller arguments)

theorem execute_exact {Regime : Type} {program : Program} {function : String} {names : Names} {head : String}
    {target : Handle} {key candidate : Nat} (regime : Regime)
    (certificate : Certificate program function names head target key candidate)
    (caller : Subst) (arguments : [names.space, names.vertex, names.candidate].map (fun name => applySubst caller (.var name)) =
      [Effects.handleValue target, number key, number candidate]) (before : Effects.State) :
    (region regime certificate caller arguments).execute before =
      PureCallPortfolio.sourceMeaning program caller (call function names) before :=
  congrFun (region regime certificate caller arguments).execute_eq_reference before

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementEntry
