import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierCollectionSource
import Mettapedia.Machines.WeightedPathRelaxation

/-!
# Weighted source calls and current-state nested relaxation

The source evaluates its actual addition operand before entering an authored
improvement function. A raw candidate argument is not an addition operation
and refuses this adapter. Captures, selected clauses and each current distance
fibre are checked. Nested matching retains source order and reads; no frontier
deduplication, round-count equality or native publication law is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces KeyedImprovementSource EffectfulQuerySource

def sum (distance weight : String) : Atom := .expression [.symbol "+", .var distance, .var weight]

def call (function : String) (names : Names) (distance weight : String) : Atom :=
  .expression [.symbol function, .var names.space, .var names.vertex, sum distance weight]

theorem sum_returns (program : Program) (caller : Subst) (state : Effects.State) (distance weight : String)
    (base cost : Nat) (readBase : Subst.lookup caller distance = some (number base))
    (readCost : Subst.lookup caller weight = some (number cost)) :
    PureReturns program caller state (sum distance weight) state (number (base + cost)) := by
  apply native_binary_call_returns program caller state state state state "+" _ _ _ _ _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simpa [applySubst, readBase] using variable_returns program caller state distance)
    (by simpa [applySubst, readCost] using variable_returns program caller state weight) _ (by decide)
  change Except.ok (state, [Atom.grounded (.int ((base : Int) + (cost : Int)))]) = _
  simp [number]

theorem call_returns {program : Program} {function : String} {names : Names} {head : String}
    {target : Handle} {key base cost : Nat}
    (certificate : KeyedImprovementEntry.Certificate program function names head target key (base + cost))
    (demanded : argumentIsRaw program function 2 = false) (caller : Subst) (distance weight : String)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (readKey : Subst.lookup caller names.vertex = some (number key))
    (readBase : Subst.lookup caller distance = some (number base))
    (readCost : Subst.lookup caller weight = some (number cost))
    (before after : Effects.State) (answers : List Atom)
    (completed : KeyedImprovementSource.run names head target key (base + cost) before = some (after, answers)) :
    Returns program caller before (call function names distance weight) after answers := by
  have body := returns names head program target key (base + cost) before after answers completed
  have invoked : (theory program).MultiStep
      {state := before, control := .arguments caller (.function function) []
        [Effects.handleValue target, number key, number (base + cost)] 3}
      (finished after answers [] []) := by
    refine .step ?_ (single_sequence_answers program before after _ answers body)
    apply step_transition
    simp [step, certificate.notIO, certificate.notNative, certificate.selected]
  have argument := evaluated_argument_answers program caller before before after (.function function)
    (sum distance weight) (number (base + cost)) answers [] [Effects.handleValue target, number key] 2 demanded
    (sum_returns program caller before distance weight base cost readBase readCost) invoked
  apply call_answers program caller before after function _ answers (by simp [certificate.registered]) _ certificate.notControl
  exact variable_prefix_arguments_answers program caller before after (.function function) [names.space, names.vertex]
    [sum distance weight] [] 0 answers (by simpa [applySubst, location, readKey] using argument)

def body (program : Program) (function : String) (names : Names) (head distance weight : String) (target : Handle) : Body :=
  fun caller before =>
    if Subst.lookup caller names.space = some (Effects.handleValue target) then
      if argumentIsRaw program function 2 = false then
        match Subst.lookup caller names.vertex, Subst.lookup caller distance, Subst.lookup caller weight with
        | some (.grounded (.int (.ofNat key))), some (.grounded (.int (.ofNat base))), some (.grounded (.int (.ofNat cost))) =>
            match KeyedImprovementEntry.prepare program function names head target key (base + cost) with
            | none => none
            | some _ => KeyedImprovementSource.run names head target key (base + cost) before
        | _, _, _ => none
      else none
    else none

theorem body_eq_run {program : Program} {function : String} {names : Names} {head : String}
    {target : Handle} {key base cost : Nat}
    (certificate : KeyedImprovementEntry.Certificate program function names head target key (base + cost))
    (demanded : argumentIsRaw program function 2 = false) (caller : Subst) (distance weight : String)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (readKey : Subst.lookup caller names.vertex = some (number key))
    (readBase : Subst.lookup caller distance = some (number base))
    (readCost : Subst.lookup caller weight = some (number cost)) (before : Effects.State) :
    body program function names head distance weight target caller before =
      KeyedImprovementSource.run names head target key (base + cost) before := by
  have prepared := certificate.prepared
  cases ready : KeyedImprovementEntry.prepare program function names head target key (base + cost) with
  | none => simp [ready] at prepared
  | some checked => simp [body, location, demanded, readKey, readBase, readCost, number, ready]

theorem body_returns (program : Program) (function : String) (names : Names) (head distance weight : String) (target : Handle)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (completed : body program function names head distance weight target caller before = some (after, answers)) :
    Returns program caller before (call function names distance weight) after answers := by
  unfold body at completed
  split at completed
  next location =>
    split at completed
    next demanded =>
      split at completed
      next key base cost readKey readBase readCost =>
        split at completed
        · cases completed
        next certificate prepared =>
          exact call_returns certificate demanded caller distance weight location readKey readBase readCost before after answers completed
      next => cases completed
    next => cases completed
  next => cases completed

theorem nested_returns (program : Program) (function : String) (names : Names) (head distance weight : String) (target : Handle)
    (legs : List NestedQuerySource.Leg) (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (completed : NestedQuerySource.run (body program function names head distance weight target) legs caller before = some (after, answers)) :
    Returns program caller before (NestedQuerySource.source legs (call function names distance weight)) after answers := by
  apply NestedQuerySource.run_returns program (call function names distance weight)
    (body program function names head distance weight target) (fun bound => bound.lookupExtends caller)
    (fun bindings before after answers _ computed => body_returns program function names head distance weight target bindings before after answers computed)
    legs _ caller before after answers (Subst.lookupExtends_refl caller) completed
  intro leg _ bindings rows bound extended member
  exact Subst.lookupExtends_trans extended (choices_extend bindings leg.2 rows bound member)

/-- Collect a next frontier only after all ordered, current-state relaxations
have completed. This does not deduplicate the producer's writes. -/
def frontierBody (function : String) (names : Names) (distance weight frontier itemName : String)
    (legs : List NestedQuerySource.Leg) : Atom :=
  FrontierCollectionSource.source frontier itemName (NestedQuerySource.source legs (call function names distance weight))

def frontierRun (program : Program) (function : String) (names : Names)
    (head distance weight frontier itemName : String) (target : Handle) (legs : List NestedQuerySource.Leg) : Body :=
  FrontierCollectionSource.run (NestedQuerySource.run (body program function names head distance weight target) legs) frontier itemName

theorem frontier_returns (program : Program) (function : String) (names : Names)
    (head distance weight frontier itemName : String) (target : Handle) (legs : List NestedQuerySource.Leg)
    (caller : Subst) (before after : Effects.State) (next : List Atom)
    (completed : frontierRun program function names head distance weight frontier itemName target legs caller before = some (after, next)) :
    PureReturns program caller before (frontierBody function names distance weight frontier itemName legs) after (.expression next) :=
  FrontierCollectionSource.source_returns program _ _
    (nested_returns program function names head distance weight target legs)
    frontier itemName caller before after next completed

theorem write_silent (before after : Effects.State) (target : Handle) (head : String)
    (key candidate : Nat) (old : Option Nat)
    (completed : write before target head key candidate old = some (after, [])) : before = after := by
  cases old with
  | none =>
      obtain ⟨_, _, impossible⟩ := Option.bind_eq_some_iff.mp completed
      cases impossible
  | some previous =>
      by_cases better : candidate < previous
      · rw [write, if_pos better] at completed
        obtain ⟨_, _, tail⟩ := Option.bind_eq_some_iff.mp completed
        obtain ⟨_, _, impossible⟩ := Option.bind_eq_some_iff.mp tail
        cases impossible
      · exact (Prod.mk.inj (Option.some.inj (by simpa only [write, if_neg better] using completed))).1

theorem run_silent (names : Names) (head : String) (target : Handle) (key candidate : Nat)
    (before after : Effects.State)
    (completed : KeyedImprovementSource.run names head target key candidate before = some (after, [])) : before = after := by
  unfold KeyedImprovementSource.run at completed
  split at completed
  · cases completed
  · obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp completed
    split at rest
    · obtain ⟨old, _, written⟩ := Option.bind_eq_some_iff.mp rest
      exact write_silent before after target head key candidate old written
    · cases rest

theorem body_silent (program : Program) (function : String) (names : Names) (head distance weight : String) (target : Handle) :
    NestedQuerySource.silent (body program function names head distance weight target) := by
  intro caller before after completed
  unfold body at completed
  split at completed
  · split at completed
    · split at completed
      next key base cost _ _ _ =>
        split at completed
        · cases completed
        · exact run_silent names head target key (base + cost) before after completed
      next => cases completed
    · cases completed
  · cases completed

/-- A completed empty source phase certifies no update, not merely a dropped
frontier. The exact nested read coverage remains part of the conclusion. -/
theorem nested_quiet_iff (program : Program) (function : String) (names : Names) (head distance weight : String) (target : Handle)
    (legs : List NestedQuerySource.Leg) (caller : Subst) (state : Effects.State) :
    NestedQuerySource.run (body program function names head distance weight target) legs caller state = some (state, []) ↔
      NestedQuerySource.QuietAt (body program function names head distance weight target) state legs caller :=
  NestedQuerySource.run_empty_iff _ (body_silent program function names head distance weight target) state legs caller

theorem improvement_denotes_relaxation (store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat)
    (edge : Mettapedia.Machines.WeightedRelaxation.Arc Nat) (base : Nat) (held : store edge.source = some base) :
    Mettapedia.Machines.KeyedImprovement.denote
      (Mettapedia.Machines.KeyedImprovement.improve store edge.target (base + edge.weight)).1 =
      Mettapedia.Machines.WeightedRelaxation.relax (Mettapedia.Machines.KeyedImprovement.denote store) edge := by
  rw [Mettapedia.Machines.KeyedImprovement.denote_improve]
  simp [Mettapedia.Machines.WeightedRelaxation.relax, Mettapedia.Machines.WeightedRelaxation.proposal,
    Mettapedia.Machines.KeyedImprovement.denote, held]

/-- A captured source distance stays current while relaxing its outgoing
edges, including self-loops, because weights are nonnegative. -/
theorem improvement_preserves_source (store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat)
    (edge : Mettapedia.Machines.WeightedRelaxation.Arc Nat) (base : Nat) (held : store edge.source = some base) :
    (Mettapedia.Machines.KeyedImprovement.improve store edge.target (base + edge.weight)).1 edge.source = some base := by
  by_cases loop : edge.target = edge.source
  · have notBetter : ¬ base + edge.weight < base := by omega
    simp [Mettapedia.Machines.KeyedImprovement.improve, loop, held, notBetter]
  · rw [Mettapedia.Machines.KeyedImprovement.other_key_unchanged store edge.target edge.source _ (Ne.symm loop), held]

theorem source_update_is_relaxation (names : Names) (head : String) (ordinary : head ∉ ["=", ":", ",", "cons"])
    (program : Program) (target : Handle) (before : Effects.State)
    (store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat)
    (represented : KeyedImprovementRows.Represents head before target store)
    (edge : Mettapedia.Machines.WeightedRelaxation.Arc Nat) (base : Nat) (held : store edge.source = some base) :
    ∃ after answers nextStore,
      Returns program (bindings names target edge.target (base + edge.weight)) before (source names head) after answers ∧
      KeyedImprovementRows.Represents head after target nextStore ∧
      Mettapedia.Machines.KeyedImprovement.denote nextStore =
        Mettapedia.Machines.WeightedRelaxation.relax (Mettapedia.Machines.KeyedImprovement.denote store) edge ∧
      answers = (if (Mettapedia.Machines.KeyedImprovement.improve store edge.target (base + edge.weight)).2 then [number edge.target] else []) := by
  obtain ⟨after, answers, returned, preserved, flags⟩ :=
    KeyedImprovementRows.source_update_refines names head ordinary program target edge.target (base + edge.weight) before store represented
  exact ⟨after, answers, _, returned, preserved, improvement_denotes_relaxation store edge base held, flags⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementSource
