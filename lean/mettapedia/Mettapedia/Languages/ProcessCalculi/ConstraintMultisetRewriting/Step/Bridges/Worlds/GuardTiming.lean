import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.Refinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingInstances

/-!
# Guard timing through actual world runs

The before-tells local family is the existing restricted step, with actual
admitted firings as its choices. Its local events and world moves refine the
after-tells family. Neither timing is selected as a language default.
This instantiates one-match firings, not the separate reading that recomputes
the quantifiers of every, maximal or unique at each guard timing.

Where each visible rule tells nothing or asks nothing, both timings agree.
This rule property survives firing, fork, publication and merge: published
snapshots ask nothing. Consequently the complete world-move relations agree
on finite runs from that region, including runs that publish new shared rules.

At a fixed quiet program the stronger local comparison is an event-fibre
bijection. It preserves exact finite execution length, action word and result.
The world reachability comparison does not assert counted world-event fibres.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.GuardTiming

open RuleSyntax RuleSyntax.Worlds RuleSyntax.StepWeb
open RuleSyntax.Equivalence (System)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
  (E : Extensions.{uO,uH,uE} Hom)

/-- The supplied local event family with guards checked before the firing's
own tells. Its events retain the actual firing and restricted admission. -/
def beforeEvents (program : Program Tm) :=
  (beforeTells (step X O E program).toStep (oneMatch X O E program)).eventSystem
    (Action := Rule Tm) (fun {_} firing => firing.rule)

theorem before_advances_iff (program : Program Tm) (before after : State Tm O) :
    Advances (beforeEvents X O E) program before after ↔
      ∃ firing : Firing O E program before.frame,
        firing.AdmitsBeforeTells X before ∧ firing.result X before = after := by
  constructor
  · rintro ⟨⟨firing, admitted⟩, result⟩
    exact ⟨firing, (oneMatch_admits_iff firing).mp admitted, result⟩
  · rintro ⟨firing, admitted, result⟩
    exact ⟨⟨firing, (oneMatch_admits_iff firing).mpr admitted⟩, result⟩

theorem before_advances (program : Program Tm) (before after : State Tm O)
    (advanced : Advances (beforeEvents X O E) program before after) :
    Advances (events X O E) program before after := by
  obtain ⟨firing, admitted, result⟩ := (before_advances_iff X O E program before after).mp advanced
  exact (events_advances_iff X E program before after).mpr
    ⟨firing, oneMatch_admits_of_beforeTells admitted, result⟩

theorem before_program_monotone : ProgramMonotone (beforeEvents X O E) := by
  intro first second inside before after advanced
  obtain ⟨firing, admitted, result⟩ := (before_advances_iff X O E first before after).mp advanced
  exact (before_advances_iff X O E second before after).mpr
    ⟨widen inside firing, admitted, result⟩

theorem before_no_events_at_inconsistent : NoEventsAtInconsistent X (beforeEvents X O E) := by
  intro program state dead
  refine ⟨fun choice => ?_⟩
  exact (events_no_events_at_inconsistent X E program state dead).elim
    ⟨choice.val, choice.property.1⟩

/-- This connects the supplied family to the already proved H-ASK world
relation, instead of introducing a separate world semantics. -/
theorem before_fires_iff (W W' : RuleSyntax.Worlds.Bag Tm O) :
    Fires (beforeEvents X O E) W W' ↔ FiresBeforeTells X E W W' := by
  constructor
  · rintro ⟨rest, shared, S, ⟨firing, admitted⟩⟩
    exact ⟨rest, shared, S, firing.result X S.state,
      ⟨firing, admitted, rfl⟩, rfl, rfl⟩
  · rintro ⟨rest, shared, S, after, ⟨firing, admitted, rfl⟩, rfl, rfl⟩
    exact Fires.fire (family := beforeEvents X O E) rest shared S ⟨firing, admitted⟩

theorem before_world_runs (J : Joining X O) {W W' : RuleSyntax.Worlds.Bag Tm O}
    (run : Relation.ReflTransGen (Move X J (beforeEvents X O E)) W W') :
    Relation.ReflTransGen (Move X J (events X O E)) W W' :=
  moves_runs_mono X J (before_advances X O E) run

/-- A rule tells nothing, or has neither checks nor collect queries. -/
def Quiet (rule : Rule Tm) : Prop :=
  rule.body.tell = [] ∨ (rule.body.checks = [] ∧ rule.collect = [])

omit [DecidableEq O] in
theorem snapshot_quiet_rule (state : State Tm O) (atom : Tm state.frame) :
    Quiet (Hosting.Alternatives.Worlds.snapshot state atom) :=
  Or.inr (snapshot_quiet state atom)

theorem quiet_admission (program : Program Tm) (quiet : ∀ rule ∈ program, Quiet rule)
    {state : State Tm O} (firing : Firing O E program state.frame) :
    (beforeTells (step X O E program).toStep (oneMatch X O E program)).Admits firing ↔
      firing.Admits X state := by
  rw [oneMatch_admits_iff]
  rcases quiet firing.rule firing.member with silent | ⟨noChecks, noCollect⟩
  · exact oneMatch_beforeTells_iff_of_no_tells firing (opened_tell_nil X firing silent)
  · exact oneMatch_beforeTells_iff_of_no_checks firing noChecks noCollect

theorem quiet_advances_iff (program : Program Tm) (quiet : ∀ rule ∈ program, Quiet rule)
    (before after : State Tm O) :
    Advances (beforeEvents X O E) program before after ↔
      Advances (events X O E) program before after := by
  refine ⟨before_advances X O E program before after, ?_⟩
  rintro ⟨⟨firing, admitted⟩, result⟩
  exact ⟨⟨firing, (quiet_admission X O E program quiet firing).mpr admitted⟩, result⟩

/-- The actual admitted-firing fibres, without identifying distinct firings. -/
def quietChoiceEquiv (program : Program Tm) (quiet : ∀ rule ∈ program, Quiet rule)
    (state : State Tm O) :
    (beforeEvents X O E program).Choice state ≃ (events X O E program).Choice state :=
  Equiv.subtypeEquivRight (quiet_admission X O E program quiet)

def quietBisimulation (program : Program Tm) (quiet : ∀ rule ∈ program, Quiet rule) :
    EventMultiplicity.Bisimulation (beforeEvents X O E program) (events X O E program) Eq where
  choices same := by
    cases same
    exact quietChoiceEquiv X O E program quiet _
  actions same choice := by cases same; rfl
  successors same choice := by cases same; rfl

def quietExecutionEquiv (program : Program Tm) (quiet : ∀ rule ∈ program, Quiet rule)
    (count : Nat) (state : State Tm O) :
    (beforeEvents X O E program).Execution count state ≃
      (events X O E program).Execution count state :=
  (quietBisimulation X O E program quiet).executions count rfl

theorem quietExecution_word (program : Program Tm) (quiet : ∀ rule ∈ program, Quiet rule)
    {count : Nat} {state : State Tm O} (run : (beforeEvents X O E program).Execution count state) :
    (events X O E program).word (quietExecutionEquiv X O E program quiet count state run) =
      (beforeEvents X O E program).word run :=
  (quietBisimulation X O E program quiet).execution_word rfl run

theorem quietExecution_last (program : Program Tm) (quiet : ∀ rule ∈ program, Quiet rule)
    {count : Nat} {state : State Tm O} (run : (beforeEvents X O E program).Execution count state) :
    (beforeEvents X O E program).last run =
      (events X O E program).last (quietExecutionEquiv X O E program quiet count state run) :=
  (quietBisimulation X O E program quiet).execution_last rfl run

/-- Guard timing agrees throughout a world computation, including after new
closed snapshots are published and after worlds are forked or merged. -/
theorem quiet_world_runs_iff (J : Joining X O) {W W' : RuleSyntax.Worlds.Bag Tm O}
    (quiet : RulesSatisfy Quiet W) :
    Relation.ReflTransGen (Move X J (beforeEvents X O E)) W W' ↔
      Relation.ReflTransGen (Move X J (events X O E)) W W' :=
  moves_runs_congr_of_rules X J Quiet (snapshot_quiet_rule O)
    (quiet_advances_iff X O E) quiet

theorem quiet_world_success_iff (J : Joining X O) (barb : State Tm O → Prop)
    {W : RuleSyntax.Worlds.Bag Tm O} (quiet : RulesSatisfy Quiet W) :
    (bagParallel X J (beforeEvents X O E) barb).Succeeds W ↔
      (bagParallel X J (events X O E) barb).Succeeds W := by
  constructor
  · rintro ⟨last, run, observed⟩
    exact ⟨last, (quiet_world_runs_iff X O E J quiet).mp run, observed⟩
  · rintro ⟨last, run, observed⟩
    exact ⟨last, (quiet_world_runs_iff X O E J quiet).mpr run, observed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.GuardTiming
