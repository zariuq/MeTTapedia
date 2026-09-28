import Mettapedia.GSLT.LanguageDef.HostGoalCorrespondence

/-!
# Host goals evaluated by the machines meet the host specification

**The instance.**  `machinesCorrect`: for programs related by
`ProgramBindsAhead` whose host goals are moded (`GoalsModed`), the reference
host and the output-first host of `HostGoalMachine` meet `HostCorrect`.  The
witness `MachinesCorr Q goalDest r h` says that the reference frontier `r`
embeds the output-first frontier `h` over the goal's destination and context
(`GoalRelated`, `GoalDoomed`), and that the reference run from `r` is moded
(`ModedFrom`).  `start` is `goal_activations_embed` at the goal's base.
`pull` is `machines_matches`, derived from the expansion laws of
`HostGoalCorrespondence`: both frontiers empty, `done` on both sides; both
first tasks silent, a host suspension and then a reference suspension; both
deliver, corresponding answers; the reference delivers an omitted answer where
the output-first task fails, a host suspension and then `prune`; a doomed
reference task, a reference suspension or `prune`.  A pull is one step on each
side, so the host passes at most one step before the next event.

`machinesRefine`: the reference host meets `RefinesStore`.  A state lies within
`W` when its tasks are doomed for the goal with no destination and the context
`Wᶜ`: an answer omitted there is one whose solutions lie in `W`.

**The side conditions** are conditions on the program, not on hosts.
`ProgramBindsAhead PA PF`, as in `outputFirst_simulates`.  `GoalsModed`: the
output-at-return run of every host goal, from every well-formed store,
evaluates only stable tests and primitives, which is what
`outputFirst_simulates` asks of a run.  It follows when every task is moded
(`goalsModed_of_moded`), for instance when no test or primitive reads the
bindings (`moded_of_stable`).  It is needed:
`HostGoalControls.prim_goals_not_moded`.

**Corollaries.**  `machines_query_answers` and `machines_query_terminates` are
`hosted_query_answers` and `hosted_query_terminates` with every host goal
evaluated by the machines.  No hypothesis about hosts is left: only
`ProgramBindsAhead`, the modes of the tier's run and of the host goals' runs,
and a well-formed start.  `machines_query_answers_of_moded` discharges both
mode conditions when every task is moded.

**Not covered.**  The enclosing machine is modelled by the two equation
machines on the program's equations; operations of the enclosing machine that
are not equations of the program (`match` against a space, `case`, a
primitive `superpose`) are not modelled, and a relation with one equation per
value stands for `superpose` over a fixed list.  Host relations called inside a
host goal's run are run inline by that machine, not handed to a host again.
Whether a given program meets `GoalsModed` is not decided here, beyond
`goalsModed_of_moded`.  Step bounds: the stuttering simulation of
`HostCallRefinement` does not bound the output-first steps by the reference's.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## The side condition -/

section Conditions

variable {Term Store Rel Op : Type}
variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op) (X : ExactStore S)
variable [Inhabited Term] [DecidableEq Rel]

/-- **Host goals are moded**: the output-at-return run of every host goal,
started in a well-formed store, evaluates only stable tests and primitives
(`Moded`), as `outputFirst_simulates` asks of a run. -/
def GoalsModed (isHost : Rel → Bool) (PA : EqProgram L Rel Op) : Prop :=
  ∀ {rel : Rel} {args : List Term} {σ : Store}, isHost rel = true → X.WellFormed σ →
    ∀ m, ∀ t ∈ (repeats (step (compiled L S PA)) m (initial L S PA (rel, args, σ))).frontier,
      Moded L X t

/-- The output-at-return run from a frontier is moded. -/
def ModedFrom (PA : EqProgram L Rel Op)
    (r : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))) : Prop :=
  ∀ m, ∀ t ∈ (repeats (step (compiled L S PA)) m ⟨r, []⟩).frontier, Moded L X t

variable {L S X}

/-- When every task is moded, so is every host goal's run. -/
theorem goalsModed_of_moded {isHost : Rel → Bool} {PA : EqProgram L Rel Op}
    (moded : ∀ t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op), Moded L X t) :
    GoalsModed L S X isHost PA :=
  fun _ _ _ t _ => moded t

theorem ModedFrom.head {PA : EqProgram L Rel Op}
    {t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    {rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
    (moded : ModedFrom L S X PA (t :: rest)) : Moded L X t :=
  moded 0 t List.mem_cons_self

/-- A moded run stays moded after its first step. -/
theorem ModedFrom.next {PA : EqProgram L Rel Op}
    {t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    {rest : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
    (moded : ModedFrom L S X PA (t :: rest)) :
    ModedFrom L S X PA ((expand (compiled L S PA) t).1 ++ rest) := by
  intro m task member
  apply moded (m + 1) task
  simp only [repeats]
  rw [step_cons, repeats_emitted]
  exact member

end Conditions

/-! ## The specification -/

section Specification

variable {Term Store Rel Op : Type}
variable {L : TemplateLanguage Term} {S : StoreAlgebra Term Store Op} {X : ExactStore S}
variable [Inhabited Term] [DecidableEq Rel] {PA PF : EqProgram L Rel Op}

/-- The witness relating the two hosts' states for a goal with destination
`goalDest` in the context `Q`: the reference frontier embeds the output-first
frontier (`GoalRelated`, `GoalDoomed`), and the reference run from it is
moded. -/
def MachinesCorr (PA : EqProgram L Rel Op) (Q : Set X.Valuation) (goalDest : Option Term)
    (r : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
    (h : List (Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))) : Prop :=
  Embeds (GoalRelated L X goalDest Q) (GoalDoomed L X goalDest Q) r h ∧ ModedFrom L S X PA r

/-- **Each pull corresponds.**  Pulling related states of the two hosts is
matched as `HostCorrect` asks: both goals exhausted; both deliver corresponding
answers; the output-first host passes a step (a silent step, or a failure where
the reference delivers an omitted answer); or the reference passes a step, or
delivers an answer that is omitted. -/
theorem machines_matches (aligned : ProgramBindsAhead L PA PF) {Q : Set X.Valuation}
    {goalDest : Option Term} {r : List (Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))}
    {h : List (Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))}
    (corr : MachinesCorr PA Q goalDest r h) :
    Matches X (referenceHost L S PA) (outputFirstHost L S PF) (MachinesCorr PA Q goalDest) Q
      goalDest r h := by
  obtain ⟨embeds, moded⟩ := corr
  cases embeds with
  | nil => exact .pulls rfl rfl .done
  | @keep a b ra rb related rest =>
      obtain ⟨tasks, answers⟩ := goal_expand_related aligned related moded.head
      have next := moded.next
      rcases expand_delivers (compiled L S PA) a with silentA | ⟨x, deliversA⟩
      · rw [silentA] at answers
        have silentB := answers.eq_nil
        exact .hostDelay (machinePull_silent _ rb silentB)
          (.refDelay (machinePull_silent _ ra silentA) ⟨tasks.append rest, next⟩)
      · rw [deliversA] at answers tasks next
        rcases x with ⟨⟨⟩, v, σA⟩
        rcases expand_delivers (outputFirst L S PF) b with silentB | ⟨y, deliversB⟩
        · rw [silentB] at answers
          cases answers with
          | drop omitted _ =>
              have noneB : (expand (outputFirst L S PF) b).1 = [] := tasks.eq_nil
              refine .hostDelay (machinePull_silent _ rb silentB) ?_
              rw [noneB, List.nil_append]
              exact .prune (machinePull_delivers _ ra deliversA) omitted.1 omitted.2
                ⟨rest, next⟩
        · rw [deliversB] at answers
          rcases y with ⟨⟨⟩, w, σF⟩
          cases answers with
          | keep same _ =>
              obtain ⟨goodA, goodF, sameValue, sols, keys⟩ := same
              change v = w at sameValue
              subst sameValue
              exact .pulls (machinePull_delivers _ ra deliversA)
                (machinePull_delivers _ rb deliversB) (.yield goodA goodF sols keys ⟨rest, next⟩)
          | drop _ impossible => cases impossible
  | @drop a ra _ doomed rest =>
      obtain ⟨all, omitted⟩ := goal_expand_doomed aligned doomed
      have next := moded.next
      rcases expand_delivers (compiled L S PA) a with silentA | ⟨x, deliversA⟩
      · exact .refDelay (machinePull_silent _ ra silentA) ⟨Embeds.prepend all rest, next⟩
      · rw [deliversA] at omitted next
        rcases x with ⟨⟨⟩, v, σA⟩
        obtain ⟨good, empty⟩ := omitted _ (List.mem_singleton_self _)
        exact .prune (machinePull_delivers _ ra deliversA) good empty ⟨rest, next⟩

variable (L S X)

/-- **The two hosts meet the host specification.**  For programs related by
`ProgramBindsAhead` whose host goals are moded, the output-first machine's
evaluation of a host goal against its destination corresponds, pull by pull,
to the output-at-return machine's evaluation of the goal. -/
def machinesCorrect {isHost : Rel → Bool} (aligned : ProgramBindsAhead L PA PF)
    (moded : GoalsModed L S X isHost PA) :
    HostCorrect X isHost (referenceHost L S PA) (outputFirstHost L S PF) where
  Corr Q goalDest := MachinesCorr PA Q goalDest
  start {rel args σA σF dest _} hit goodA goodF sols keys :=
    ⟨goal_activations_embed aligned rel args σA σF goodA goodF keys dest .base sols,
      moded hit goodA⟩
  pull corr := machines_matches aligned corr

/-- **The reference host refines stores**: every answer of a host goal started
in `σ` is well formed and its solutions are among `σ`'s.  A state's tasks are
doomed for the goal with no destination whose context is the complement of the
solutions allowed. -/
def machinesRefine (isHost : Rel → Bool) (PA : EqProgram L Rel Op) :
    RefinesStore X isHost (referenceHost L S PA) where
  Within within r := ∀ t ∈ r, GoalDoomed L X none withinᶜ t
  start {rel args σ} _ good :=
    goal_activations_doomed (programBindsAhead_refl L PA) rel args σ good none .base
      (Set.inter_compl_self _)
  pull {within r} inside := by
    cases r with
    | nil => exact .done
    | cons t rest =>
        obtain ⟨all, omitted⟩ :=
          goal_expand_doomed (programBindsAhead_refl L PA) (inside t List.mem_cons_self)
        have below : ∀ t' ∈ rest, GoalDoomed L X none withinᶜ t' :=
          fun t' member => inside t' (List.mem_cons_of_mem _ member)
        rcases expand_delivers (compiled L S PA) t with silent | ⟨x, delivers⟩
        · change PullWithin X _ within (machinePull (compiled L S PA) (t :: rest))
          rw [machinePull_silent _ rest silent]
          refine .suspend fun t' member => ?_
          rcases List.mem_append.mp member with member | member
          · exact all t' member
          · exact below t' member
        · change PullWithin X _ within (machinePull (compiled L S PA) (t :: rest))
          rw [machinePull_delivers _ rest delivers]
          rw [delivers] at omitted
          rcases x with ⟨⟨⟩, v, σ⟩
          obtain ⟨good, empty⟩ := omitted _ (List.mem_singleton_self _)
          refine .yield good (fun w inSol => ?_) below
          by_contra outside
          have inside' : w ∈ X.solutions σ ∩ meets X (some v) none ∩ withinᶜ :=
            ⟨⟨inSol, by simp [meets_none_right]⟩, outside⟩
          rw [empty] at inside'
          exact inside'

end Specification

/-! ## Runs whose host goals the machines evaluate -/

section Runs

variable {Term Store Rel Op : Type}
variable {L : TemplateLanguage Term} {S : StoreAlgebra Term Store Op} {X : ExactStore S}
variable [Inhabited Term] [DecidableEq Rel] {PA PF : EqProgram L Rel Op} {isHost : Rel → Bool}

/-- **The prefix law, with every host goal evaluated by the machines.**  From a
query control, every answer list the reference with host calls has delivered,
the output-first machine with host calls has delivered after some number of
steps, answer for answer.  No hypothesis about hosts is left: the host goals
are evaluated by the output-at-return and output-first machines themselves. -/
theorem machines_query_answers (aligned : ProgramBindsAhead L PA PF)
    (goalsModed : GoalsModed L S X isHost PA) {k : ℕ} {late early : Code L Rel Op k}
    (ahead : BindsAhead L [] late early) (frame : Fin k → Term) (σ : Store)
    (good : X.WellFormed σ)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA (referenceHost L S PA)))
      m (liftState (queryState L late frame σ))).frontier, HModed L X t) (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer X)
      (repeats (step (hostedAtReturn L S isHost PA (referenceHost L S PA))) n
        (liftState (queryState L late frame σ))).emitted
      (repeats (step (hostedFirst L S isHost PF (outputFirstHost L S PF))) n'
        (liftState (queryStateOut L early frame σ))).emitted :=
  hosted_query_answers aligned (machinesCorrect L S X aligned goalsModed)
    (machinesRefine L S X isHost PA) ahead frame σ good moded n

/-- **Termination, with every host goal evaluated by the machines.**  When the
reference with host calls exhausts its frontier within `n` steps, so does the
output-first machine with host calls after some number of steps, with the same
ordered answers. -/
theorem machines_query_terminates (aligned : ProgramBindsAhead L PA PF)
    (goalsModed : GoalsModed L S X isHost PA) {k : ℕ} {late early : Code L Rel Op k}
    (ahead : BindsAhead L [] late early) (frame : Fin k → Term) (σ : Store)
    (good : X.WellFormed σ)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA (referenceHost L S PA)))
      m (liftState (queryState L late frame σ))).frontier, HModed L X t) (n : ℕ)
    (done : (repeats (step (hostedAtReturn L S isHost PA (referenceHost L S PA))) n
      (liftState (queryState L late frame σ))).frontier = []) :
    ∃ n', (repeats (step (hostedFirst L S isHost PF (outputFirstHost L S PF))) n'
        (liftState (queryStateOut L early frame σ))).frontier = [] ∧
      List.Forall₂ (SameAnswer X)
        (repeats (step (hostedAtReturn L S isHost PA (referenceHost L S PA))) n
          (liftState (queryState L late frame σ))).emitted
        (repeats (step (hostedFirst L S isHost PF (outputFirstHost L S PF))) n'
          (liftState (queryStateOut L early frame σ))).emitted :=
  hosted_query_terminates aligned (machinesCorrect L S X aligned goalsModed)
    (machinesRefine L S X isHost PA) ahead frame σ good moded n done

/-- The prefix law when every task is moded, for example when no test or
primitive reads the bindings (`moded_of_stable`): both side conditions on
modes follow. -/
theorem machines_query_answers_of_moded (aligned : ProgramBindsAhead L PA PF)
    (moded : ∀ t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op), Moded L X t)
    {k : ℕ} {late early : Code L Rel Op k} (ahead : BindsAhead L [] late early)
    (frame : Fin k → Term) (σ : Store) (good : X.WellFormed σ) (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer X)
      (repeats (step (hostedAtReturn L S isHost PA (referenceHost L S PA))) n
        (liftState (queryState L late frame σ))).emitted
      (repeats (step (hostedFirst L S isHost PF (outputFirstHost L S PF))) n'
        (liftState (queryStateOut L early frame σ))).emitted :=
  machines_query_answers aligned (goalsModed_of_moded moded) ahead frame σ good
    (fun _ t _ => hmoded_of L X moded t) n

end Runs

end Mettapedia.GSLT.LanguageDef.HostGoals
