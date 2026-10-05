import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Module publication as an effect-aware productive block

Importing a module runs its initialization, exports its bindings, and links
the importer.  Initialization is a productive block (`ProductiveBlocks`): a
deterministic machine publishing ordered events, already closed under its
foreign callbacks (`Machine.close`), so a foreign callback's own effects are
events of the run.  An exported binding is an answer occurrence, a foreign
(for example Python) effect is a committed effect, and a failure is a fault
(`OrderedDemand.Event`).

* **The registry** (`Registry`).  What importers see: each name's binding
  (exporting module and token), the importer links, the published modules in
  order, and the reservation capacity.  A reservation succeeds when the
  exported names are distinct, unbound and fit the capacity (`Reservable`).
  Installing binds exactly the exported names (`binding_install_of_mem`,
  `binding_install_of_not_mem`); linking is idempotent (`link_link`).
* **One import attempt** (`importStep`).  A published module is only linked:
  its initialization never runs again.  Otherwise the initialization runs from
  its start or from its saved residual; its events join the visible trace;
  a finished run commits all its exports and the link atomically, or keeps
  them staged when the reservation fails; a fault makes the publication
  failed; exhausting the allowance keeps the exact residual and the exports
  published so far.  A staged publication retries only the reservation.
* **No partial links or tokens** (`registry_cases`).  After any attempt the
  registry is unchanged, or extended by the link alone (a repeated import), or
  by the atomic installation of every export together with the link.  A failed
  initialization or reservation leaves it unchanged
  (`failed_registry_unchanged`, `refused_registry_unchanged`).
* **Completed effects are never replayed** (`importStep_add`,
  `importSteps_eq`).  Splitting the fuel of an import over several attempts is
  the same as one attempt with the total fuel: retries after exhaustion resume
  the residual, retries after a refused reservation do not run the
  initialization, and repeated imports do nothing.  So the visible trace of
  any sequence of attempts is the trace of one uninterrupted run
  (`importSteps_visible`), and the trace only grows (`visible_prefix`): effects
  committed before a failure stay visible and are never undone or repeated.
* **The observation of a module** (`Session.observe`).  The visible trace
  with the module's publication status (finished when published, faulted when
  failed, otherwise incomplete) is an `OrderedDemand.Observation`; an import
  attempt extends it as a prefix (`observe_prefix`, of which `visible_prefix`
  is the event part), more fuel extends it (`observe_prefix_add`), and attempts
  are prefix-faithful to any final observation (`prefixFaithful_of_final`).
  The scope is the attempts at that module: importing another module extends
  the session's trace too (the controls).
* **Retained callback identity** (`CallbackTable`, `tableEnvironment`).  A
  callback is identified by its session and serial and keeps its owning
  module.  Closing a session makes every identity of that session resolve to
  nothing (`resolve_closeSession_self`), so a retained stale handle is refused
  with a visible fault reply and runs none of its own events
  (`stale_call_refused`); other sessions are unaffected
  (`resolve_closeSession_other`).  A resolved callback runs with its owner
  module, not with the module active at the call (`environment_owner`).

These are laws of the model.  Physical exactly-once execution of foreign
code, interpreter locks, finalizers, concurrent imports and the C realization
of the registry are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.PublicationBlocks

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics.OrderedDemand (Event answers answers_append Status Observation
  PrefixFaithful)

/-- The events of a module initialization: an exported binding is an answer, a
foreign effect is a committed effect, and a failure is a fault. -/
abbrev InitEvent (Name Token Effect Fault : Type) := Event (Name × Token) Effect Fault

/-! ## The registry -/

/-- **What importers see**: the binding of each name (exporting module and
token), the importer links, the published modules in order, and the
reservation capacity left. -/
structure Registry (Module Name Token : Type) where
  binding : Name → Option (Module × Token)
  links : List (Module × Module)
  published : List Module
  capacity : ℕ

namespace Registry

variable {Module Name Token : Type} [DecidableEq Module] [DecidableEq Name]

/-- The names of an export list. -/
def names (exports : List (Name × Token)) : List Name :=
  exports.map Prod.fst

/-- **A reservation succeeds** when the exported names are distinct, unbound,
and fit the capacity. -/
def Reservable (registry : Registry Module Name Token) (exports : List (Name × Token)) : Prop :=
  (names exports).Nodup ∧ (∀ name ∈ names exports, (registry.binding name).isNone = true) ∧
    exports.length ≤ registry.capacity

instance (registry : Registry Module Name Token) (exports : List (Name × Token)) :
    Decidable (registry.Reservable exports) := by
  unfold Reservable
  infer_instance

/-- Bind every export to its module, newest first. -/
def bindExports (module : Module) (binding : Name → Option (Module × Token)) :
    List (Name × Token) → Name → Option (Module × Token)
  | [] => binding
  | (name, token) :: rest => fun query =>
      if query = name then some (module, token) else bindExports module binding rest query

/-- **Install every export at once**, record the publication and consume the
reservation. -/
def install (registry : Registry Module Name Token) (module : Module)
    (exports : List (Name × Token)) : Registry Module Name Token where
  binding := bindExports module registry.binding exports
  links := registry.links
  published := registry.published ++ [module]
  capacity := registry.capacity - exports.length

/-- **Link an importer to a module**, once. -/
def link (registry : Registry Module Name Token) (importer module : Module) :
    Registry Module Name Token :=
  if (importer, module) ∈ registry.links then registry
  else { registry with links := registry.links ++ [(importer, module)] }

omit [DecidableEq Name] in
@[simp] theorem link_binding (registry : Registry Module Name Token) (importer module : Module) :
    (registry.link importer module).binding = registry.binding := by
  unfold link
  split <;> rfl

omit [DecidableEq Name] in
@[simp] theorem link_published (registry : Registry Module Name Token) (importer module : Module) :
    (registry.link importer module).published = registry.published := by
  unfold link
  split <;> rfl

omit [DecidableEq Name] in
@[simp] theorem link_capacity (registry : Registry Module Name Token) (importer module : Module) :
    (registry.link importer module).capacity = registry.capacity := by
  unfold link
  split <;> rfl

omit [DecidableEq Name] in
theorem mem_links_link (registry : Registry Module Name Token) (importer module : Module) :
    (importer, module) ∈ (registry.link importer module).links := by
  unfold link
  split
  · assumption
  · simp

omit [DecidableEq Name] in
/-- **Linking is idempotent.** -/
@[simp] theorem link_link (registry : Registry Module Name Token) (importer module : Module) :
    (registry.link importer module).link importer module = registry.link importer module := by
  exact if_pos (registry.mem_links_link importer module)

omit [DecidableEq Name] in
theorem links_link (registry : Registry Module Name Token) (importer module : Module) :
    (registry.link importer module).links =
      if (importer, module) ∈ registry.links then registry.links
      else registry.links ++ [(importer, module)] := by
  unfold link
  split <;> rfl

omit [DecidableEq Module] in
theorem bindExports_of_not_mem (module : Module) (binding : Name → Option (Module × Token))
    (exports : List (Name × Token)) {name : Name} (absent : name ∉ names exports) :
    bindExports module binding exports name = binding name := by
  induction exports with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨exported, token⟩ := head
      simp only [names, List.map_cons, List.mem_cons, not_or] at absent
      simp only [bindExports, if_neg absent.1]
      exact ih absent.2

omit [DecidableEq Module] in
theorem bindExports_of_mem (module : Module) (binding : Name → Option (Module × Token))
    {exports : List (Name × Token)} (distinct : (names exports).Nodup) {name : Name} {token : Token}
    (exported : (name, token) ∈ exports) :
    bindExports module binding exports name = some (module, token) := by
  induction exports with
  | nil => cases exported
  | cons head rest ih =>
      obtain ⟨first, firstToken⟩ := head
      simp only [names, List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp exported with same | later
      · cases same
        simp [bindExports]
      · have different : name ≠ first := by
          rintro rfl
          exact distinct.1 (List.mem_map.mpr ⟨(name, token), later, rfl⟩)
        simp only [bindExports, if_neg different]
        exact ih distinct.2 later

omit [DecidableEq Module] in
/-- **Installing binds exactly the exports**: a name that is not exported keeps
its binding. -/
theorem binding_install_of_not_mem (registry : Registry Module Name Token) (module : Module)
    (exports : List (Name × Token)) {name : Name} (absent : name ∉ names exports) :
    (registry.install module exports).binding name = registry.binding name :=
  bindExports_of_not_mem module registry.binding exports absent

omit [DecidableEq Module] in
/-- An exported name is bound to its module and token. -/
theorem binding_install_of_mem (registry : Registry Module Name Token) (module : Module)
    {exports : List (Name × Token)} (distinct : (names exports).Nodup) {name : Name}
    {token : Token} (exported : (name, token) ∈ exports) :
    (registry.install module exports).binding name = some (module, token) :=
  bindExports_of_mem module registry.binding distinct exported

end Registry

/-! ## Publication stages and import attempts -/

/-- The stage of a module's publication within a session. -/
inductive Stage (State Name Token : Type) where
  /-- Not started, or published. -/
  | idle
  /-- Initialization paused at an exact residual, with the exports published so far. -/
  | running (residual : State) (exported : List (Name × Token))
  /-- Initialization finished; its exports wait for a reservation. -/
  | staged (exports : List (Name × Token))
  /-- Initialization faulted; the publication failed. -/
  | failed

/-- **A session**: the registry, the visible trace of every initialization
event, and each module's stage. -/
structure Session (State Module Name Token Effect Fault : Type) where
  registry : Registry Module Name Token
  visible : List (InitEvent Name Token Effect Fault)
  stage : Module → Stage State Name Token

namespace Session

variable {State Module Name Token Effect Fault Verdict : Type}
  [DecidableEq Module] [DecidableEq Name]

/-- Change one module's stage. -/
def setStage (session : Session State Module Name Token Effect Fault) (module : Module)
    (stage : Stage State Name Token) : Session State Module Name Token Effect Fault :=
  { session with stage := Function.update session.stage module stage }

omit [DecidableEq Name] in
@[simp] theorem setStage_registry (session : Session State Module Name Token Effect Fault)
    (module : Module) (stage : Stage State Name Token) :
    (session.setStage module stage).registry = session.registry := rfl

omit [DecidableEq Name] in
@[simp] theorem setStage_visible (session : Session State Module Name Token Effect Fault)
    (module : Module) (stage : Stage State Name Token) :
    (session.setStage module stage).visible = session.visible := rfl

omit [DecidableEq Name] in
@[simp] theorem setStage_setStage (session : Session State Module Name Token Effect Fault)
    (module : Module) (first second : Stage State Name Token) :
    (session.setStage module first).setStage module second = session.setStage module second := by
  simp [setStage, Function.update_idem]

omit [DecidableEq Name] in
@[simp] theorem setStage_stage_self (session : Session State Module Name Token Effect Fault)
    (module : Module) (stage : Stage State Name Token) :
    (session.setStage module stage).stage module = stage := by
  simp [setStage]

/-- **Commit staged exports atomically**: install them all and link the
importer, or keep them staged when the reservation fails. -/
def commit (session : Session State Module Name Token Effect Fault) (importer module : Module)
    (exports : List (Name × Token)) : Session State Module Name Token Effect Fault :=
  if session.registry.Reservable exports then
    { session.setStage module .idle with
      registry := (session.registry.install module exports).link importer module }
  else session.setStage module (.staged exports)

variable (init : Machine State (InitEvent Name Token Effect Fault) Verdict Empty)

/-- Run the initialization from `state`, with `exported` already published,
and record what it did. -/
def continueFrom (fuel : ℕ) (session : Session State Module Name Token Effect Fault)
    (importer module : Module) (state : State) (exported : List (Name × Token)) :
    Session State Module Name Token Effect Fault :=
  let ran := { session with visible := session.visible ++ (init.run fuel state).1 }
  match (init.run fuel state).2 with
  | .finished _ => ran.commit importer module (exported ++ answers (init.run fuel state).1)
  | .faulted => ran.setStage module .failed
  | .suspended request _ => request.elim
  | .stuck residual => ran.setStage module (.running residual
      (exported ++ answers (init.run fuel state).1))
  | .exhausted residual => ran.setStage module (.running residual
      (exported ++ answers (init.run fuel state).1))

variable (start : Module → State)

/-- **One import attempt.**  A published module is only linked.  Otherwise the
initialization runs from its start or its residual, a staged publication
retries the reservation alone, and a failed one stays failed. -/
def importStep (fuel : ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    Session State Module Name Token Effect Fault :=
  if module ∈ session.registry.published then
    { session with registry := session.registry.link importer module }
  else
    match session.stage module with
    | .idle => continueFrom init fuel session importer module (start module) []
    | .running residual exported => continueFrom init fuel session importer module residual exported
    | .staged exports => session.commit importer module exports
    | .failed => session

/-- Several attempts in order. -/
def importSteps (fuels : List ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    Session State Module Name Token Effect Fault :=
  fuels.foldl (fun current fuel => importStep init start fuel importer module current) session

/-! ### The registry changes atomically -/

theorem commit_cases (session : Session State Module Name Token Effect Fault)
    (importer module : Module) (exports : List (Name × Token)) :
    ((session.commit importer module exports).registry = session.registry ∧
        ¬ session.registry.Reservable exports) ∨
      ((session.commit importer module exports).registry =
          (session.registry.install module exports).link importer module ∧
        session.registry.Reservable exports) := by
  unfold commit
  by_cases reservable : session.registry.Reservable exports
  · exact Or.inr ⟨by rw [if_pos reservable], reservable⟩
  · exact Or.inl ⟨by rw [if_neg reservable]; rfl, reservable⟩

theorem continueFrom_registry_cases (fuel : ℕ)
    (session : Session State Module Name Token Effect Fault) (importer module : Module)
    (state : State) (exported : List (Name × Token)) :
    (continueFrom init fuel session importer module state exported).registry = session.registry ∨
      ∃ exports, session.registry.Reservable exports ∧
        (continueFrom init fuel session importer module state exported).registry =
          (session.registry.install module exports).link importer module := by
  unfold continueFrom
  cases (init.run fuel state).2 with
  | finished verdict =>
      rcases commit_cases { session with visible := session.visible ++ (init.run fuel state).1 }
          importer module (exported ++ answers (init.run fuel state).1) with
        ⟨same, _⟩ | ⟨installed, reservable⟩
      · exact Or.inl same
      · exact Or.inr ⟨_, reservable, installed⟩
  | faulted => exact Or.inl rfl
  | suspended request _ => exact request.elim
  | stuck residual => exact Or.inl rfl
  | exhausted residual => exact Or.inl rfl

/-- **No partial links or tokens.**  After any attempt the registry is
unchanged, or extended by the link alone (a repeated import of a published
module), or by the atomic installation of every export of a successful
reservation together with the link. -/
theorem registry_cases (fuel : ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    (importStep init start fuel importer module session).registry = session.registry ∨
      (module ∈ session.registry.published ∧
        (importStep init start fuel importer module session).registry =
          session.registry.link importer module) ∨
      ∃ exports, session.registry.Reservable exports ∧
        (importStep init start fuel importer module session).registry =
          (session.registry.install module exports).link importer module := by
  unfold importStep
  by_cases published : module ∈ session.registry.published
  · rw [if_pos published]
    exact Or.inr (Or.inl ⟨published, rfl⟩)
  · rw [if_neg published]
    cases session.stage module with
    | idle =>
        rcases continueFrom_registry_cases init fuel session importer module (start module) [] with
          same | installed
        · exact Or.inl same
        · exact Or.inr (Or.inr installed)
    | running residual exported =>
        rcases continueFrom_registry_cases init fuel session importer module residual exported with
          same | installed
        · exact Or.inl same
        · exact Or.inr (Or.inr installed)
    | staged exports =>
        rcases commit_cases session importer module exports with ⟨same, _⟩ | ⟨installed, reservable⟩
        · exact Or.inl same
        · exact Or.inr (Or.inr ⟨exports, reservable, installed⟩)
    | failed => exact Or.inl rfl

/-- **A refused reservation leaves the registry unchanged** and keeps the
exports staged. -/
theorem refused_registry_unchanged (session : Session State Module Name Token Effect Fault)
    (importer module : Module) (exports : List (Name × Token))
    (refused : ¬ session.registry.Reservable exports) :
    session.commit importer module exports = session.setStage module (.staged exports) := by
  unfold commit
  rw [if_neg refused]

/-- **A faulted initialization publishes nothing**: the registry is unchanged,
its events (the effects before the fault and the fault) are visible, and the
publication is failed. -/
theorem failed_registry_unchanged (fuel : ℕ)
    (session : Session State Module Name Token Effect Fault) (importer module : Module)
    (state : State) (exported : List (Name × Token))
    (faulted : (init.run fuel state).2 = .faulted) :
    continueFrom init fuel session importer module state exported =
      { session with visible := session.visible ++ (init.run fuel state).1 }.setStage module .failed := by
  unfold continueFrom
  rw [faulted]

/-! ### The visible trace only grows -/

theorem commit_visible (session : Session State Module Name Token Effect Fault)
    (importer module : Module) (exports : List (Name × Token)) :
    (session.commit importer module exports).visible = session.visible := by
  unfold commit
  split <;> rfl

theorem continueFrom_visible (fuel : ℕ) (session : Session State Module Name Token Effect Fault)
    (importer module : Module) (state : State) (exported : List (Name × Token)) :
    (continueFrom init fuel session importer module state exported).visible =
      session.visible ++ (init.run fuel state).1 := by
  unfold continueFrom
  cases (init.run fuel state).2 with
  | finished verdict => exact commit_visible _ _ _ _
  | faulted => rfl
  | suspended request _ => exact request.elim
  | stuck residual => rfl
  | exhausted residual => rfl

/-! ### Equations of one attempt -/

theorem importStep_published {fuel : ℕ} {importer module : Module}
    {session : Session State Module Name Token Effect Fault}
    (published : module ∈ session.registry.published) :
    importStep init start fuel importer module session =
      { session with registry := session.registry.link importer module } := by
  unfold importStep
  rw [if_pos published]

theorem importStep_idle {fuel : ℕ} {importer module : Module}
    {session : Session State Module Name Token Effect Fault}
    (unpublished : module ∉ session.registry.published) (idle : session.stage module = .idle) :
    importStep init start fuel importer module session =
      continueFrom init fuel session importer module (start module) [] := by
  unfold importStep
  rw [if_neg unpublished, idle]

theorem importStep_running {fuel : ℕ} {importer module : Module}
    {session : Session State Module Name Token Effect Fault} {residual : State}
    {exported : List (Name × Token)}
    (unpublished : module ∉ session.registry.published)
    (running : session.stage module = .running residual exported) :
    importStep init start fuel importer module session =
      continueFrom init fuel session importer module residual exported := by
  unfold importStep
  rw [if_neg unpublished, running]

theorem importStep_staged {fuel : ℕ} {importer module : Module}
    {session : Session State Module Name Token Effect Fault} {exports : List (Name × Token)}
    (unpublished : module ∉ session.registry.published)
    (staged : session.stage module = .staged exports) :
    importStep init start fuel importer module session = session.commit importer module exports := by
  unfold importStep
  rw [if_neg unpublished, staged]

theorem importStep_failed {fuel : ℕ} {importer module : Module}
    {session : Session State Module Name Token Effect Fault}
    (unpublished : module ∉ session.registry.published) (failed : session.stage module = .failed) :
    importStep init start fuel importer module session = session := by
  unfold importStep
  rw [if_neg unpublished, failed]

/-! ### The observation of a module: the visible trace only grows -/

/-- **The publication status of a module in a session**: a published module has
finished, a failed publication has faulted, and an idle, running or staged
publication is incomplete. -/
def status (session : Session State Module Name Token Effect Fault) (module : Module) :
    Status Unit :=
  if module ∈ session.registry.published then .finished ()
  else
    match session.stage module with
    | .failed => .faulted
    | _ => .incomplete

/-- **The observation of a module in a session**: the session's visible trace,
with the module's publication status. -/
def observe (session : Session State Module Name Token Effect Fault) (module : Module) :
    Observation (InitEvent Name Token Effect Fault) Unit :=
  ⟨session.visible, session.status module⟩

/-- **An import attempt extends the module's observation**: no attempt removes
or rewrites an event, and the observation of a published or failed module does
not change. -/
theorem observe_prefix (fuel : ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    (session.observe module).Prefix
      ((importStep init start fuel importer module session).observe module) := by
  refine ⟨?_, fun final => ?_⟩
  · change session.visible <+: (importStep init start fuel importer module session).visible
    unfold importStep
    split
    · exact List.prefix_refl _
    · split
      · rw [continueFrom_visible]
        exact List.prefix_append _ _
      · rw [continueFrom_visible]
        exact List.prefix_append _ _
      · rw [commit_visible]
      · exact List.prefix_refl _
  · by_cases published : module ∈ session.registry.published
    · rw [importStep_published init start published]
      show (⟨session.visible, session.status module⟩ : Observation _ _) =
        ⟨session.visible, if module ∈ (session.registry.link importer module).published then
          .finished () else
          match session.stage module with
          | .failed => .faulted
          | _ => .incomplete⟩
      rw [Registry.link_published]
      unfold status
      rw [if_pos published]
    · have failed : session.stage module = .failed := by
        change (if module ∈ session.registry.published then Status.finished ()
          else
            match session.stage module with
            | .failed => .faulted
            | _ => .incomplete).Final at final
        rw [if_neg published] at final
        cases staged : session.stage module with
        | failed => rfl
        | idle => rw [staged] at final; exact final.elim
        | running residual exported => rw [staged] at final; exact final.elim
        | staged exports => rw [staged] at final; exact final.elim
      rw [importStep_failed init start published failed]

/-- **The visible trace only grows**: no attempt removes or rewrites an event,
so effects committed before a failure stay visible.  This is the event part of
`observe_prefix`. -/
theorem visible_prefix (fuel : ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    session.visible <+: (importStep init start fuel importer module session).visible :=
  (observe_prefix init start fuel importer module session).1

/-! ### Exact resumption: completed effects are never replayed -/

/-- A run that ends stuck ends at a state without a transition. -/
theorem run_stuck_step {Ev Req : Type} (machine : Machine State Ev Verdict Req) :
    ∀ (fuel : ℕ) (state residual : State) (events : List Ev),
      machine.run fuel state = (events, .stuck residual) → machine.step residual = none
  | 0, _, _, _, ran => by simp [Machine.run] at ran
  | fuel + 1, state, residual, events, ran => by
      cases found : machine.step state with
      | none =>
          rw [machine.run_succ_stuck found] at ran
          simp only [Prod.mk.injEq, Outcome.stuck.injEq] at ran
          rw [← ran.2]
          exact found
      | some transition =>
          cases transition with
          | silent next =>
              rw [machine.run_succ_silent found] at ran
              exact run_stuck_step machine fuel next residual events ran
          | publish published next =>
              rw [machine.run_succ_publish found] at ran
              simp only [Prod.mk.injEq] at ran
              exact run_stuck_step machine fuel next residual _ (Prod.ext rfl ran.2)
          | finish verdict =>
              rw [machine.run_succ_finish found] at ran
              simp at ran
          | fail failed =>
              rw [machine.run_succ_fail found] at ran
              simp at ran
          | call request saved =>
              rw [machine.run_succ_call found] at ran
              simp at ran

/-- A run from a stuck state stays there. -/
theorem run_of_step_none {Ev Req : Type} (machine : Machine State Ev Verdict Req)
    {residual : State} (stuck : machine.step residual = none) (fuel : ℕ) :
    machine.run fuel residual = ([], .stuck residual) ∨
      machine.run fuel residual = ([], .exhausted residual) := by
  cases fuel with
  | zero => exact Or.inr rfl
  | succ fuel => exact Or.inl (machine.run_succ_stuck stuck)

/-- An attempt after a commit changes nothing more. -/
theorem importStep_commit (fuel : ℕ) (session : Session State Module Name Token Effect Fault)
    (importer module : Module) (exports : List (Name × Token))
    (unpublished : module ∉ session.registry.published) :
    importStep init start fuel importer module (session.commit importer module exports) =
      session.commit importer module exports := by
  by_cases reservable : session.registry.Reservable exports
  · have published : module ∈ (session.commit importer module exports).registry.published := by
      simp [commit, if_pos reservable, Registry.install]
    rw [importStep_published init start published]
    simp only [commit, if_pos reservable, Registry.link_link]
  · rw [refused_registry_unchanged session importer module exports reservable,
      importStep_staged init start (by exact unpublished) (setStage_stage_self _ _ _)]
    simp only [commit, setStage_registry, if_neg reservable, setStage_setStage]

/-- Running the initialization from a state, then attempting again, is one run
with the total fuel. -/
theorem continueFrom_add (first second : ℕ)
    (session : Session State Module Name Token Effect Fault) (importer module : Module)
    (state : State) (exported : List (Name × Token))
    (unpublished : module ∉ session.registry.published) :
    importStep init start second importer module
        (continueFrom init first session importer module state exported) =
      continueFrom init (first + second) session importer module state exported := by
  have whole := init.run_add first second state
  rcases ran : init.run first state with ⟨events, outcome⟩
  rw [ran] at whole
  cases outcome with
  | finished verdict =>
      have stable : init.run (first + second) state = (events, .finished verdict) := by
        rw [whole]; rfl
      have left : continueFrom init first session importer module state exported =
          ({ session with visible := session.visible ++ events } : Session State Module Name Token
            Effect Fault).commit importer module (exported ++ answers events) := by
        unfold continueFrom
        rw [ran]
      have right : continueFrom init (first + second) session importer module state exported =
          ({ session with visible := session.visible ++ events } : Session State Module Name Token
            Effect Fault).commit importer module (exported ++ answers events) := by
        unfold continueFrom
        rw [stable]
      rw [left, right]
      exact importStep_commit init start second _ importer module _ unpublished
  | faulted =>
      have stable : init.run (first + second) state = (events, .faulted) := by
        rw [whole]; rfl
      have left : continueFrom init first session importer module state exported =
          ({ session with visible := session.visible ++ events } : Session State Module Name Token
            Effect Fault).setStage module .failed := by
        unfold continueFrom
        rw [ran]
      have right : continueFrom init (first + second) session importer module state exported =
          ({ session with visible := session.visible ++ events } : Session State Module Name Token
            Effect Fault).setStage module .failed := by
        unfold continueFrom
        rw [stable]
      rw [left, right]
      exact importStep_failed init start (by exact unpublished) (setStage_stage_self _ _ _)
  | suspended request _ => exact request.elim
  | stuck residual =>
      have stable : init.run (first + second) state = (events, .stuck residual) := by
        rw [whole]; rfl
      have noStep := run_stuck_step init first state residual events ran
      have left : continueFrom init first session importer module state exported =
          ({ session with visible := session.visible ++ events } : Session State Module Name Token
            Effect Fault).setStage module (.running residual (exported ++ answers events)) := by
        unfold continueFrom
        rw [ran]
      have right : continueFrom init (first + second) session importer module state exported =
          ({ session with visible := session.visible ++ events } : Session State Module Name Token
            Effect Fault).setStage module (.running residual (exported ++ answers events)) := by
        unfold continueFrom
        rw [stable]
      rw [left, right, importStep_running init start (by exact unpublished) (setStage_stage_self _ _ _)]
      unfold continueFrom
      rcases run_of_step_none init noStep second with again | again <;>
        · rw [again]
          simp [setStage, answers]
  | exhausted residual =>
      have resumed : init.run (first + second) state =
          (events ++ (init.run second residual).1, (init.run second residual).2) := by
        rw [whole]; rfl
      have left : continueFrom init first session importer module state exported =
          ({ session with visible := session.visible ++ events } : Session State Module Name Token
            Effect Fault).setStage module (.running residual (exported ++ answers events)) := by
        unfold continueFrom
        rw [ran]
      rw [left, importStep_running init start (by exact unpublished) (setStage_stage_self _ _ _)]
      unfold continueFrom
      rw [resumed]
      simp only [answers_append, List.append_assoc]
      cases (init.run second residual).2 with
      | finished verdict => simp [commit, setStage]
      | faulted => simp [setStage]
      | suspended request _ => exact request.elim
      | stuck later => simp [setStage]
      | exhausted later => simp [setStage]

/-- **Exact resumption of imports.**  Splitting the fuel of an import over two
attempts is the same as one attempt with the total fuel: an exhausted
initialization resumes its residual, a refused reservation is retried without
running the initialization, and a published module is linked once.  Completed
effects are therefore never replayed. -/
theorem importStep_add (first second : ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    importStep init start second importer module (importStep init start first importer module session) =
      importStep init start (first + second) importer module session := by
  by_cases published : module ∈ session.registry.published
  · rw [importStep_published init start published, importStep_published init start published,
      importStep_published init start (session := { session with
        registry := session.registry.link importer module }) (by simpa using published)]
    simp only [Registry.link_link]
  · cases staged : session.stage module with
    | idle =>
        rw [importStep_idle init start published staged, importStep_idle init start published staged]
        exact continueFrom_add init start first second session importer module _ _ published
    | running residual exported =>
        rw [importStep_running init start published staged,
          importStep_running init start published staged]
        exact continueFrom_add init start first second session importer module _ _ published
    | staged exports =>
        rw [importStep_staged init start published staged, importStep_staged init start published staged]
        exact importStep_commit init start second session importer module exports published
    | failed =>
        rw [importStep_failed init start published staged, importStep_failed init start published staged,
          importStep_failed init start published staged]

/-- **Any nonempty sequence of attempts is one attempt with the total fuel.** -/
theorem importSteps_eq (fuel : ℕ) (fuels : List ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    importSteps init start (fuel :: fuels) importer module session =
      importStep init start (fuel + fuels.sum) importer module session := by
  induction fuels generalizing fuel session with
  | nil => simp [importSteps]
  | cons next rest ih =>
      have step : importSteps init start (fuel :: next :: rest) importer module session =
          importSteps init start ((fuel + next) :: rest) importer module session := by
        simp only [importSteps, List.foldl_cons]
        rw [importStep_add]
      rw [step, ih, List.sum_cons, Nat.add_assoc]

/-- **The visible trace of any attempts on an unstarted module is the trace of
one uninterrupted run**: every initialization event, effects included, appears
exactly once, in order. -/
theorem importSteps_visible (fuel : ℕ) (fuels : List ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault)
    (unpublished : module ∉ session.registry.published) (idle : session.stage module = .idle) :
    (importSteps init start (fuel :: fuels) importer module session).visible =
      session.visible ++ (init.run (fuel + fuels.sum) (start module)).1 := by
  rw [importSteps_eq]
  unfold importStep
  rw [if_neg unpublished, idle, continueFrom_visible]

/-- **More fuel extends a module's observation.** -/
theorem observe_prefix_add (first second : ℕ) (importer module : Module)
    (session : Session State Module Name Token Effect Fault) :
    ((importStep init start first importer module session).observe module).Prefix
      ((importStep init start (first + second) importer module session).observe module) := by
  rw [← importStep_add]
  exact observe_prefix init start second importer module _

/-- **Import attempts are prefix-faithful to a final observation**: once some
fuel ends the publication, published or failed, the attempt with any fuel
observes a prefix of that observation. -/
theorem prefixFaithful_of_final {fuel : ℕ} (importer module : Module)
    (session : Session State Module Name Token Effect Fault)
    (final : ((importStep init start fuel importer module session).observe module).status.Final) :
    PrefixFaithful (fun fuel' => (importStep init start fuel' importer module session).observe module)
      ((importStep init start fuel importer module session).observe module) := by
  intro fuel'
  rcases le_total fuel' fuel with le | le
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
    exact observe_prefix_add init start fuel' extra importer module session
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
    have grown := observe_prefix_add init start fuel extra importer module session
    show ((importStep init start (fuel + extra) importer module session).observe module).Prefix _
    rw [← grown.2 final]
    exact Observation.Prefix.refl _

end Session

/-! ## Retained callback identity -/

/-- **A callback's identity**: the session that registered it and its serial
there. -/
structure CallbackId (SessionId : Type) where
  session : SessionId
  serial : ℕ
  deriving DecidableEq

/-- Registered callbacks, each with its owning module, and the live sessions. -/
structure CallbackTable (SessionId Module Handler : Type) where
  live : List SessionId
  entries : List (CallbackId SessionId × (Module × Handler))

namespace CallbackTable

variable {SessionId Module Handler : Type} [DecidableEq SessionId]

/-- The newest entry registered under an identity. -/
def lookupId (id : CallbackId SessionId) :
    List (CallbackId SessionId × (Module × Handler)) → Option (Module × Handler)
  | [] => none
  | (key, entry) :: rest => if key = id then some entry else lookupId id rest

/-- **Resolve a retained identity**: only a live session's registered callback
resolves. -/
def resolve? (table : CallbackTable SessionId Module Handler) (id : CallbackId SessionId) :
    Option (Module × Handler) :=
  if id.session ∈ table.live then lookupId id table.entries else none

/-- Register a callback with its owning module. -/
def register (table : CallbackTable SessionId Module Handler) (id : CallbackId SessionId)
    (owner : Module) (handler : Handler) : CallbackTable SessionId Module Handler :=
  { table with entries := (id, owner, handler) :: table.entries }

/-- Open a session. -/
def openSession (table : CallbackTable SessionId Module Handler) (session : SessionId) :
    CallbackTable SessionId Module Handler :=
  { table with live := session :: table.live }

/-- Close a session: it is no longer live and its entries are dropped. -/
def closeSession (table : CallbackTable SessionId Module Handler) (session : SessionId) :
    CallbackTable SessionId Module Handler where
  live := table.live.filter fun live => live ≠ session
  entries := table.entries.filter fun entry => entry.1.session ≠ session

theorem lookupId_filter_other (id : CallbackId SessionId) (session : SessionId)
    (other : id.session ≠ session) (entries : List (CallbackId SessionId × (Module × Handler))) :
    lookupId id (entries.filter fun entry => entry.1.session ≠ session) = lookupId id entries := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨key, entry⟩ := head
      rw [List.filter_cons]
      by_cases kept : key.session = session
      · have different : key ≠ id := by
          rintro rfl
          exact other kept
        rw [if_neg (by simp [kept]), ih]
        simp [lookupId, different]
      · rw [if_pos (by simp [kept])]
        simp only [lookupId, ih]

/-- **After closing a session, its identities resolve to nothing.** -/
theorem resolve_closeSession_self (table : CallbackTable SessionId Module Handler)
    (session : SessionId) (serial : ℕ) :
    (table.closeSession session).resolve? ⟨session, serial⟩ = none := by
  simp [resolve?, closeSession]

/-- Closing a session leaves every other session's resolution unchanged. -/
theorem resolve_closeSession_other (table : CallbackTable SessionId Module Handler)
    (session : SessionId) (id : CallbackId SessionId) (other : id.session ≠ session) :
    (table.closeSession session).resolve? id = table.resolve? id := by
  unfold resolve?
  have live : id.session ∈ (table.closeSession session).live ↔ id.session ∈ table.live := by
    simp [closeSession, other]
  by_cases present : id.session ∈ table.live
  · rw [if_pos (live.mpr present), if_pos present]
    exact lookupId_filter_other id session other table.entries
  · rw [if_neg (fun inside => present (live.mp inside)), if_neg present]

/-- A callback registered in a live session resolves to itself with its owner. -/
theorem resolve_register_self (table : CallbackTable SessionId Module Handler)
    (id : CallbackId SessionId) (owner : Module) (handler : Handler)
    (live : id.session ∈ table.live) :
    (table.register id owner handler).resolve? id = some (owner, handler) := by
  simp [resolve?, register, live, lookupId]

/-- **A retained handle stays stale when its serial is reused**: after its
session is closed, a new session registering the same serial does not revive
it, provided session identities are not reused. -/
theorem stale_after_serial_reuse (table : CallbackTable SessionId Module Handler)
    (old new : SessionId) (fresh : new ≠ old) (serial : ℕ) (owner : Module) (handler : Handler) :
    (((table.closeSession old).openSession new).register ⟨new, serial⟩ owner handler).resolve?
      ⟨old, serial⟩ = none := by
  simp [resolve?, register, openSession, closeSession, Ne.symm fresh]

end CallbackTable

section CallbackProtocol

variable {SessionId Module Handler : Type} [DecidableEq SessionId]
  {State Event Verdict Value Failure : Type}

/-- **The environment a callback table gives the callback protocol**: a
resolved callback runs with its owning module; an identity that does not
resolve is refused with a fault reply and runs no events of its own. -/
def tableEnvironment (table : CallbackTable SessionId Module Handler)
    (runHandler : Module → Handler → List Event × Reply Value Failure) (stale : Failure) :
    Environment (CallbackId SessionId) Event Value Failure := fun id =>
  match table.resolve? id with
  | some (owner, handler) => runHandler owner handler
  | none => ([], .faulted stale)

/-- A resolved callback runs with its owner module, whatever module is active
when it is called. -/
theorem environment_owner (table : CallbackTable SessionId Module Handler)
    (runHandler : Module → Handler → List Event × Reply Value Failure) (stale : Failure)
    {id : CallbackId SessionId} {owner : Module} {handler : Handler}
    (resolved : table.resolve? id = some (owner, handler)) :
    tableEnvironment table runHandler stale id = runHandler owner handler := by
  simp [tableEnvironment, resolved]

/-- **A stale callback is refused visibly.**  A run suspended on a callback of
a closed session continues, under the protocol, with the call event and a fault
reply and none of the callback's own events, then resumes the saved
continuation with that fault. -/
theorem stale_call_refused (machine : Machine State Event Verdict (CallbackId SessionId))
    (protocol : Callback State Event (CallbackId SessionId) Value Failure)
    (table : CallbackTable SessionId Module Handler)
    (runHandler : Module → Handler → List Event × Reply Value Failure) (stale : Failure)
    (session : SessionId) (serial : ℕ) (fuel : ℕ) (state saved : State) (events : List Event)
    (suspended : machine.run fuel state = (events, .suspended ⟨session, serial⟩ saved)) :
    ∃ k ≤ fuel,
      (machine.close protocol (tableEnvironment (table.closeSession session) runHandler stale)).run
          k state =
        (events ++ [protocol.callEvent ⟨session, serial⟩, protocol.replyEvent (.faulted stale)],
          .exhausted (protocol.resume saved (.faulted stale))) := by
  obtain ⟨k, bound, ran⟩ := machine.close_run_of_suspended protocol
    (tableEnvironment (table.closeSession session) runHandler stale) fuel state events
    ⟨session, serial⟩ saved suspended
  refine ⟨k, bound, ?_⟩
  have refused : tableEnvironment (table.closeSession session) runHandler stale ⟨session, serial⟩ =
      ([], .faulted stale) := by
    simp [tableEnvironment, CallbackTable.resolve_closeSession_self]
  rw [ran]
  simp [Machine.callEvents, refused]

end CallbackProtocol

end Mettapedia.GSLT.Distinction.PublicationBlocks
