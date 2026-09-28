import Mettapedia.GSLT.LanguageDef.HostGoalRefinement

/-!
# Eager elimination of exhausted host nodes

When a host goal's answer arrives and the goal has no choice left, its stream
would next pull `done`.  The C then drops the host frame at once, and the
answer's resumption joins the tasks below it, instead of leaving the host node
beneath the resumption until the search backtracks into it.  This module
proves that the drop is unobservable.

**Inert tasks.**  A task is inert when its expansion leaves no successor and
no answer (`Inert`); a host node whose next pull is `done` is inert
(`host_done_inert`).  `AgreeUpToInert P₁ P₂`: `P₂` expands every task as `P₁`
does, except that it may leave out successors inert for `P₁`.  For states whose
frontiers differ by inert tasks (`Simulates (· = ·) (Inert P₁) (· = ·)`):
`inert_forward` (from `simulates_repeats`) matches every step of `P₁` by at
most one step of `P₂`, and `inert_backward` every step of `P₂` by finitely many
steps of `P₁`, one per inert task passed and one for the task itself.  Hence
`inert_answers`: every answer prefix either run delivers, the other delivers,
the second run within no more steps; and `inert_terminates`: either run
exhausts its frontier exactly when the other does, with the same answers.

**Dropping one host node.**  `drop_exhausted_host` and
`drop_exhausted_host_terminates`: in `withHost`, the frontiers
`segment ++ hostNode :: rest` and `segment ++ rest` deliver the same answers
and exhaust together when the host node's next pull is `done`.
`hostedAtReturn_drop_exhausted` and `hostedFirst_drop_exhausted` state it for
the two machines with host calls.

**The eager machine.**  `withHostEager P goal? H exhausted` is `withHost`,
except that a pull whose answer leaves the host in a state `exhausted`
recognizes places the answer alone, dropping the host node
(`eagerPullBranches`).  With a sound test (`exhausted h = true → H.pull h =
.done`), `agree_eager` makes it agree with `withHost` up to inert tasks, so
`eager_answers` and `eager_terminates` hold from every state.  For the machines
as hosts the test is an empty frontier (`machinePull_done_of_isEmpty`).
`machines_eager_query_answers`: when the reference and the output-first
machine both drop eagerly (`hostedAtReturnEager`, `hostedFirstEager`), the
prefix law of `machines_query_answers` still holds, answer for answer.

**The test must be sound.**  A host node whose next pull yields is not inert,
and dropping it loses the answers it would yield
(`HostGoalOrderControls.rash_runs`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Inert tasks -/

section Inert

variable {C K Call' F A : Type}

/-- A task that leaves nothing when expanded: no successor and no answer. -/
def Inert (P : Program C K Call' F A) (t : Task C K F) : Prop := expand P t = ([], [])

/-- Every list embeds in itself. -/
theorem embeds_refl {α : Type} {D : α → Prop} : ∀ l : List α, Embeds (· = ·) D l l
  | [] => .nil
  | _ :: rest => .keep rfl (embeds_refl rest)

/-- `P₂` expands every task as `P₁` does, except that it may leave out
successors that are inert for `P₁`. -/
def AgreeUpToInert (P₁ P₂ : Program C K Call' F A) : Prop :=
  ∀ t, Embeds (· = ·) (Inert P₁) (expand P₁ t).1 (expand P₂ t).1 ∧
    (expand P₁ t).2 = (expand P₂ t).2

theorem agreeUpToInert_refl (P : Program C K Call' F A) : AgreeUpToInert P P :=
  fun _ => ⟨embeds_refl _, rfl⟩

variable {P₁ P₂ : Program C K Call' F A}

/-- **Forward.**  From states whose frontiers differ by inert tasks, every step
of `P₁` is matched by at most one step of `P₂`. -/
theorem inert_forward (agree : AgreeUpToInert P₁ P₂) {s₁ s₂ : State C K F A}
    (sim : Simulates (· = ·) (Inert P₁) (· = ·) s₁ s₂) (n : ℕ) :
    ∃ n' ≤ n, Simulates (· = ·) (Inert P₁) (· = ·) (repeats (step P₁) n s₁)
      (repeats (step P₂) n' s₂) :=
  simulates_repeats P₁ P₂ (fun _ => True)
    (fun a b same _ => by
      subst same
      exact ⟨(agree a).1, by rw [(agree a).2]; exact List.forall₂_refl _⟩)
    (fun a inert => by
      unfold Inert at inert
      rw [inert]
      exact ⟨fun _ member => by simp at member, rfl⟩)
    n s₁ s₂ sim (fun _ _ _ _ => trivial)

/-- One step of `P₂` is matched by finitely many steps of `P₁`: the inert tasks
above the next task of `P₂`, one step each, and then that task. -/
theorem inert_backward_step (agree : AgreeUpToInert P₁ P₂) :
    ∀ (frontier : List (Task C K F)) (emitted : List (C × A)) (s₂ : State C K F A),
      Simulates (· = ·) (Inert P₁) (· = ·) ⟨frontier, emitted⟩ s₂ →
      ∃ k, Simulates (· = ·) (Inert P₁) (· = ·) (repeats (step P₁) k ⟨frontier, emitted⟩)
        (step P₂ s₂)
  | _, _, ⟨[], _⟩, sim => ⟨0, sim⟩
  | [], _, ⟨_ :: _, _⟩, ⟨embeds, _⟩ => by cases embeds
  | a :: frontier, emitted, ⟨b :: rest₂, e₂⟩, ⟨embeds, answers⟩ => by
      cases embeds with
      | keep same rest =>
          subst same
          refine ⟨1, ?_⟩
          change Simulates _ _ _ (step P₁ ⟨a :: frontier, emitted⟩) (step P₂ ⟨a :: rest₂, e₂⟩)
          rw [step_cons, step_cons, ← (agree a).2]
          exact ⟨(agree a).1.append rest, List.rel_append answers (List.forall₂_refl _)⟩
      | drop inert rest =>
          obtain ⟨k, sim'⟩ :=
            inert_backward_step agree frontier emitted ⟨b :: rest₂, e₂⟩ ⟨rest, answers⟩
          refine ⟨k + 1, ?_⟩
          have silent : step P₁ ⟨a :: frontier, emitted⟩ = ⟨frontier, emitted⟩ := by
            unfold Inert at inert
            rw [step_cons, inert]
            simp
          simp only [repeats]
          rw [silent]
          exact sim'

/-- **Backward.**  Every run of `P₂` is matched by a run of `P₁`. -/
theorem inert_backward (agree : AgreeUpToInert P₁ P₂) :
    ∀ (n : ℕ) (s₁ s₂ : State C K F A), Simulates (· = ·) (Inert P₁) (· = ·) s₁ s₂ →
      ∃ n', Simulates (· = ·) (Inert P₁) (· = ·) (repeats (step P₁) n' s₁)
        (repeats (step P₂) n s₂)
  | 0, _, _, sim => ⟨0, sim⟩
  | n + 1, ⟨frontier, emitted⟩, s₂, sim => by
      obtain ⟨k, sim'⟩ := inert_backward_step agree frontier emitted s₂ sim
      obtain ⟨n', sim''⟩ := inert_backward agree n _ _ sim'
      refine ⟨k + n', ?_⟩
      rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add (step P₁) k n']
      exact sim''

/-- A frontier of inert tasks is exhausted after one step per task, delivering
nothing. -/
theorem inert_clear (P : Program C K Call' F A) (emitted : List (C × A)) :
    ∀ frontier : List (Task C K F), (∀ t ∈ frontier, Inert P t) →
      repeats (step P) frontier.length ⟨frontier, emitted⟩ = ⟨[], emitted⟩
  | [], _ => rfl
  | t :: rest, inert => by
      have silent : step P ⟨t :: rest, emitted⟩ = ⟨rest, emitted⟩ := by
        have := inert t List.mem_cons_self
        unfold Inert at this
        rw [step_cons, this]
        simp
      simp only [List.length_cons, repeats]
      rw [silent]
      exact inert_clear P emitted rest fun t' member => inert t' (List.mem_cons_of_mem _ member)

theorem Embeds.forall_of_nil {α β : Type} {R : α → β → Prop} {D : α → Prop} :
    ∀ {as : List α}, Embeds R D as [] → ∀ a ∈ as, D a
  | [], _, _, member => absurd member List.not_mem_nil
  | _ :: _, .drop d rest, a, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact d
      · exact Embeds.forall_of_nil rest a member

theorem emitted_eq_of_simulates {D : Task C K F → Prop} {s₁ s₂ : State C K F A}
    (sim : Simulates (· = ·) D (· = ·) s₁ s₂) : s₁.emitted = s₂.emitted := by
  have same := sim.2
  rwa [List.forall₂_eq_eq_eq] at same

/-- **The same answers.**  Runs from states whose frontiers differ by inert
tasks deliver the same answers: every prefix one run has delivered, the other
delivers too, the second within no more steps. -/
theorem inert_answers (agree : AgreeUpToInert P₁ P₂) {s₁ s₂ : State C K F A}
    (sim : Simulates (· = ·) (Inert P₁) (· = ·) s₁ s₂) :
    (∀ n, ∃ n' ≤ n, (repeats (step P₁) n s₁).emitted = (repeats (step P₂) n' s₂).emitted) ∧
      ∀ n, ∃ n', (repeats (step P₂) n s₂).emitted = (repeats (step P₁) n' s₁).emitted :=
  ⟨fun n =>
      let ⟨n', le, sim'⟩ := inert_forward agree sim n
      ⟨n', le, emitted_eq_of_simulates sim'⟩,
    fun n =>
      let ⟨n', sim'⟩ := inert_backward agree n s₁ s₂ sim
      ⟨n', (emitted_eq_of_simulates sim').symm⟩⟩

/-- **The same termination.**  Either run exhausts its frontier exactly when the
other does, having delivered the same answers. -/
theorem inert_terminates (agree : AgreeUpToInert P₁ P₂) {s₁ s₂ : State C K F A}
    (sim : Simulates (· = ·) (Inert P₁) (· = ·) s₁ s₂) :
    (∀ n, (repeats (step P₁) n s₁).frontier = [] →
        ∃ n' ≤ n, (repeats (step P₂) n' s₂).frontier = [] ∧
          (repeats (step P₁) n s₁).emitted = (repeats (step P₂) n' s₂).emitted) ∧
      ∀ n, (repeats (step P₂) n s₂).frontier = [] →
        ∃ n', (repeats (step P₁) n' s₁).frontier = [] ∧
          (repeats (step P₂) n s₂).emitted = (repeats (step P₁) n' s₁).emitted := by
  refine ⟨fun n done => ?_, fun n done => ?_⟩
  · obtain ⟨n', le, embeds, answers⟩ := inert_forward agree sim n
    rw [done] at embeds
    rw [List.forall₂_eq_eq_eq] at answers
    exact ⟨n', le, embeds.eq_nil, answers⟩
  · obtain ⟨n', embeds, answers⟩ := inert_backward agree n s₁ s₂ sim
    rw [done] at embeds
    have cleared := inert_clear P₁ (repeats (step P₁) n' s₁).emitted _
      (Embeds.forall_of_nil embeds)
    refine ⟨n' + (repeats (step P₁) n' s₁).frontier.length, ?_, ?_⟩
    · rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add, cleared]
    · rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add, cleared]
      rw [List.forall₂_eq_eq_eq] at answers
      exact answers.symm

end Inert

/-! ## Exhausted host nodes -/

section HostDrop

variable {Context Control Call Frame Answer Goal HState : Type}
variable (P : Program Context Control Call Frame Answer) (goal? : Call → Option Goal)
  (H : Host Goal HState Answer)

/-- A host node whose next pull is `done` is inert. -/
theorem host_done_inert (context : Context) {h : HState} (returns : List Frame)
    (exhausted : H.pull h = .done) :
    Inert (withHost P goal? H) ⟨context, .host h, returns⟩ := by
  unfold Inert
  rw [expand_host, exhausted]
  rfl

/-- A frontier with an exhausted host node below a segment corresponds to the
same frontier without it. -/
theorem drop_host_simulates (context : Context) {h : HState} (returns : List Frame)
    (exhausted : H.pull h = .done)
    (segment rest : List (Task Context (Node Control HState Answer) Frame))
    (emitted : List (Context × Answer)) :
    Simulates (· = ·) (Inert (withHost P goal? H)) (· = ·)
      ⟨segment ++ ⟨context, .host h, returns⟩ :: rest, emitted⟩ ⟨segment ++ rest, emitted⟩ :=
  ⟨(embeds_refl segment).append
      (.drop (host_done_inert P goal? H context returns exhausted) (embeds_refl rest)),
    List.forall₂_refl _⟩

/-- **Dropping an exhausted host node is unobservable.**  The frontiers
`segment ++ hostNode :: rest` and `segment ++ rest`, for a host node whose next
pull is `done`, deliver the same answers: every prefix the first has
delivered, the second delivers within no more steps, and conversely. -/
theorem drop_exhausted_host (context : Context) {h : HState} (returns : List Frame)
    (exhausted : H.pull h = .done)
    (segment rest : List (Task Context (Node Control HState Answer) Frame))
    (emitted : List (Context × Answer)) :
    (∀ n, ∃ n' ≤ n,
      (repeats (step (withHost P goal? H)) n
        ⟨segment ++ ⟨context, .host h, returns⟩ :: rest, emitted⟩).emitted =
      (repeats (step (withHost P goal? H)) n' ⟨segment ++ rest, emitted⟩).emitted) ∧
    ∀ n, ∃ n',
      (repeats (step (withHost P goal? H)) n ⟨segment ++ rest, emitted⟩).emitted =
      (repeats (step (withHost P goal? H)) n'
        ⟨segment ++ ⟨context, .host h, returns⟩ :: rest, emitted⟩).emitted :=
  inert_answers (agreeUpToInert_refl _)
    (drop_host_simulates P goal? H context returns exhausted segment rest emitted)

/-- The same frontiers exhaust together, with the same answers. -/
theorem drop_exhausted_host_terminates (context : Context) {h : HState} (returns : List Frame)
    (exhausted : H.pull h = .done)
    (segment rest : List (Task Context (Node Control HState Answer) Frame))
    (emitted : List (Context × Answer)) :
    (∀ n, (repeats (step (withHost P goal? H)) n
        ⟨segment ++ ⟨context, .host h, returns⟩ :: rest, emitted⟩).frontier = [] →
      ∃ n' ≤ n, (repeats (step (withHost P goal? H)) n' ⟨segment ++ rest, emitted⟩).frontier = [] ∧
        (repeats (step (withHost P goal? H)) n
          ⟨segment ++ ⟨context, .host h, returns⟩ :: rest, emitted⟩).emitted =
        (repeats (step (withHost P goal? H)) n' ⟨segment ++ rest, emitted⟩).emitted) ∧
    ∀ n, (repeats (step (withHost P goal? H)) n ⟨segment ++ rest, emitted⟩).frontier = [] →
      ∃ n', (repeats (step (withHost P goal? H)) n'
          ⟨segment ++ ⟨context, .host h, returns⟩ :: rest, emitted⟩).frontier = [] ∧
        (repeats (step (withHost P goal? H)) n ⟨segment ++ rest, emitted⟩).emitted =
        (repeats (step (withHost P goal? H)) n'
          ⟨segment ++ ⟨context, .host h, returns⟩ :: rest, emitted⟩).emitted :=
  inert_terminates (agreeUpToInert_refl _)
    (drop_host_simulates P goal? H context returns exhausted segment rest emitted)

/-! ## The machine that drops exhausted host frames -/

/-- The alternatives of a pull when a host node whose state `exhausted`
recognizes is dropped with the answer that leaves it so. -/
def eagerPullBranches (exhausted : HState → Bool) (context : Context) :
    Pull HState Answer → List (Context × Node Control HState Answer)
  | .done => []
  | .yield a rest =>
      if exhausted rest then [(context, .answer a)]
      else [(context, .answer a), (context, .host rest)]
  | .suspend rest => [(context, .host rest)]

/-- **Eager host frames**: `withHost`, except that a pull whose answer leaves
the host in a state `exhausted` recognizes drops the host node at once, so the
answer's resumption joins the tasks below. -/
def withHostEager (exhausted : HState → Bool) :
    Program Context (Node Control HState Answer) (HCall Call HState) Frame Answer where
  inspect := (withHost P goal? H).inspect
  branches context
    | .base c => (withHost P goal? H).branches context (.base c)
    | .pull h => eagerPullBranches exhausted context (H.pull h)
  resume := (withHost P goal? H).resume

theorem expand_eager_host (exhausted : HState → Bool) (context : Context) (h : HState)
    (returns : List Frame) :
    expand (withHostEager P goal? H exhausted) ⟨context, .host h, returns⟩ =
      ((eagerPullBranches exhausted context (H.pull h)).map fun next =>
        ⟨next.1, next.2, returns⟩, []) :=
  rfl

/-- The eager machine expands every task as `withHost` does, except that it
leaves out the host node an answer exhausts, which is inert. -/
theorem agree_eager {exhausted : HState → Bool}
    (sound : ∀ h, exhausted h = true → H.pull h = .done) :
    AgreeUpToInert (withHost P goal? H) (withHostEager P goal? H exhausted) := by
  rintro ⟨context, node, returns⟩
  cases node with
  | run c =>
      have same : expand (withHostEager P goal? H exhausted) ⟨context, .run c, returns⟩ =
          expand (withHost P goal? H) ⟨context, .run c, returns⟩ := by
        change expandWith _ context returns (liftInstruction (P.inspect c)) =
          expandWith _ context returns (liftInstruction (P.inspect c))
        cases P.inspect c <;> rfl
      rw [same]
      exact ⟨embeds_refl _, rfl⟩
  | answer a => exact ⟨embeds_refl _, rfl⟩
  | host h =>
      rw [expand_host, expand_eager_host]
      refine ⟨?_, rfl⟩
      cases pulled : H.pull h with
      | done => exact .nil
      | suspend h' => exact embeds_refl _
      | yield a h' =>
          cases exhaustedAfter : exhausted h' with
          | false => simpa [pullBranches, eagerPullBranches, exhaustedAfter] using embeds_refl _
          | true =>
              simp only [pullBranches, eagerPullBranches, exhaustedAfter, if_true, List.map_cons,
                List.map_nil]
              exact .keep rfl
                (.drop (host_done_inert P goal? H context returns (sound h' exhaustedAfter)) .nil)

/-- **Eager host frames are unobservable.**  From any state, the machine that
drops exhausted host frames delivers the answers of the machine that keeps
them, within no more steps, and conversely. -/
theorem eager_answers {exhausted : HState → Bool}
    (sound : ∀ h, exhausted h = true → H.pull h = .done)
    (s : State Context (Node Control HState Answer) Frame Answer) :
    (∀ n, ∃ n' ≤ n, (repeats (step (withHost P goal? H)) n s).emitted =
        (repeats (step (withHostEager P goal? H exhausted)) n' s).emitted) ∧
      ∀ n, ∃ n', (repeats (step (withHostEager P goal? H exhausted)) n s).emitted =
        (repeats (step (withHost P goal? H)) n' s).emitted :=
  inert_answers (agree_eager P goal? H sound) ⟨embeds_refl _, List.forall₂_refl _⟩

/-- Both machines exhaust their frontiers together, with the same answers. -/
theorem eager_terminates {exhausted : HState → Bool}
    (sound : ∀ h, exhausted h = true → H.pull h = .done)
    (s : State Context (Node Control HState Answer) Frame Answer) :
    (∀ n, (repeats (step (withHost P goal? H)) n s).frontier = [] →
        ∃ n' ≤ n, (repeats (step (withHostEager P goal? H exhausted)) n' s).frontier = [] ∧
          (repeats (step (withHost P goal? H)) n s).emitted =
            (repeats (step (withHostEager P goal? H exhausted)) n' s).emitted) ∧
      ∀ n, (repeats (step (withHostEager P goal? H exhausted)) n s).frontier = [] →
        ∃ n', (repeats (step (withHost P goal? H)) n' s).frontier = [] ∧
          (repeats (step (withHostEager P goal? H exhausted)) n s).emitted =
            (repeats (step (withHost P goal? H)) n' s).emitted :=
  inert_terminates (agree_eager P goal? H sound) ⟨embeds_refl _, List.forall₂_refl _⟩

end HostDrop

/-! ## The hosted machines -/

/-- A run used as a host is exhausted when its frontier is empty. -/
theorem machinePull_done_of_isEmpty {C K Call' F A : Type} (P : Program C K Call' F A)
    {frontier : List (Task C K F)} (empty : frontier.isEmpty = true) :
    machinePull P frontier = .done := by
  rw [List.isEmpty_iff.mp empty]
  rfl

section Hosted

variable {Term Store Rel Op RState HState : Type}
variable (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)
variable [Inhabited Term] [DecidableEq Rel]

/-- The reference with host calls and eager host frames. -/
def hostedAtReturnEager (isHost : Rel → Bool) (PA : EqProgram L Rel Op)
    (R : Host (Call Term Store Rel) RState (Answer Term Store)) (exhausted : RState → Bool) :=
  withHostEager (compiled L S PA) (hostGoal isHost) R exhausted

/-- The output-first machine with host calls and eager host frames. -/
def hostedFirstEager (isHost : Rel → Bool) (PF : EqProgram L Rel Op)
    (H : Host (DestCall Term Store Rel) HState (Answer Term Store)) (exhausted : HState → Bool) :=
  withHostEager (outputFirst L S PF) (hostGoal isHost) H exhausted

/-- The reference with host calls: an exhausted host node below a segment can be
dropped without changing the answers. -/
theorem hostedAtReturn_drop_exhausted (isHost : Rel → Bool) (PA : EqProgram L Rel Op)
    (R : Host (Call Term Store Rel) RState (Answer Term Store)) {h : RState}
    (returns : List (ReturnFrame L Rel Op)) (exhausted : R.pull h = .done)
    (segment rest : List (RTask L Rel Op Store RState))
    (emitted : List (Unit × Answer Term Store)) :
    (∀ n, ∃ n' ≤ n,
      (repeats (step (hostedAtReturn L S isHost PA R)) n
        ⟨segment ++ ⟨(), .host h, returns⟩ :: rest, emitted⟩).emitted =
      (repeats (step (hostedAtReturn L S isHost PA R)) n' ⟨segment ++ rest, emitted⟩).emitted) ∧
    ∀ n, ∃ n',
      (repeats (step (hostedAtReturn L S isHost PA R)) n ⟨segment ++ rest, emitted⟩).emitted =
      (repeats (step (hostedAtReturn L S isHost PA R)) n'
        ⟨segment ++ ⟨(), .host h, returns⟩ :: rest, emitted⟩).emitted :=
  drop_exhausted_host _ _ R () returns exhausted segment rest emitted

/-- The same for the output-first machine with host calls. -/
theorem hostedFirst_drop_exhausted (isHost : Rel → Bool) (PF : EqProgram L Rel Op)
    (H : Host (DestCall Term Store Rel) HState (Answer Term Store)) {h : HState}
    (returns : List (DestFrame L Rel Op)) (exhausted : H.pull h = .done)
    (segment rest : List (FTask L Rel Op Store HState))
    (emitted : List (Unit × Answer Term Store)) :
    (∀ n, ∃ n' ≤ n,
      (repeats (step (hostedFirst L S isHost PF H)) n
        ⟨segment ++ ⟨(), .host h, returns⟩ :: rest, emitted⟩).emitted =
      (repeats (step (hostedFirst L S isHost PF H)) n' ⟨segment ++ rest, emitted⟩).emitted) ∧
    ∀ n, ∃ n',
      (repeats (step (hostedFirst L S isHost PF H)) n ⟨segment ++ rest, emitted⟩).emitted =
      (repeats (step (hostedFirst L S isHost PF H)) n'
        ⟨segment ++ ⟨(), .host h, returns⟩ :: rest, emitted⟩).emitted :=
  drop_exhausted_host _ _ H () returns exhausted segment rest emitted

variable {L S}
variable {X : ExactStore S} {PA PF : EqProgram L Rel Op} {isHost : Rel → Bool}

/-- **The prefix law with eager host frames on both sides.**  When the host
goals are evaluated by the machines and each machine drops a host node as soon
as the answer that exhausts it arrives, every answer list the reference has
delivered, the output-first machine has delivered after some number of steps,
answer for answer.  The conditions are those of `machines_query_answers`. -/
theorem machines_eager_query_answers (aligned : ProgramBindsAhead L PA PF)
    (goalsModed : GoalsModed L S X isHost PA) {k : ℕ} {late early : Code L Rel Op k}
    (ahead : BindsAhead L [] late early) (frame : Fin k → Term) (σ : Store)
    (good : X.WellFormed σ)
    (moded : ∀ m, ∀ t ∈ (repeats (step (hostedAtReturn L S isHost PA (referenceHost L S PA)))
      m (liftState (queryState L late frame σ))).frontier, HModed L X t) (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer X)
      (repeats (step (hostedAtReturnEager L S isHost PA (referenceHost L S PA) List.isEmpty)) n
        (liftState (queryState L late frame σ))).emitted
      (repeats (step (hostedFirstEager L S isHost PF (outputFirstHost L S PF) List.isEmpty)) n'
        (liftState (queryStateOut L early frame σ))).emitted := by
  obtain ⟨n₁, same₁⟩ := (eager_answers (compiled L S PA) (hostGoal isHost) (referenceHost L S PA)
    (fun _ empty => machinePull_done_of_isEmpty _ empty) _).2 n
  obtain ⟨n₂, same₂⟩ := machines_query_answers aligned goalsModed ahead frame σ good moded n₁
  obtain ⟨n₃, -, same₃⟩ := (eager_answers (outputFirst L S PF) (hostGoal isHost)
    (outputFirstHost L S PF) (fun _ empty => machinePull_done_of_isEmpty _ empty) _).1 n₂
  refine ⟨n₃, ?_⟩
  unfold hostedAtReturn hostedFirst at same₂
  unfold hostedAtReturnEager hostedFirstEager
  rw [same₁, ← same₃]
  exact same₂

end Hosted

end Mettapedia.GSLT.LanguageDef.HostGoals
