import Mettapedia.Machines.PortfolioReach.Need

/-!
# A witness portfolio wherever the `once` or `select k` sits

A host is any machine that runs with effects and, at some states, asks for up
to `demand` answers of a generator and resumes with them: `demand = 1` is
`once`, `demand = k` is `select k`. The state that asks may be a `let` value,
a function body, or an argument; `resume` is everything that follows, and the
host's own alternatives, pending effects and enclosing calls are its control
state. The log holds every event performed so far, in order.

A take is served by the portfolio when the generator is admitted, and by the
plain cursor otherwise (or as a fallback).

* `machine_refines_spec`: when admission implies `Quiet`, every step of the
  machine is a step of the specification, in which an admitted take leaves the
  store and the log as they were and resumes the host on a batch of the
  generator's answers (`BatchMeaning`). For `once` the batch is one answer of
  the generator, or empty only when the generator has none (`once_batch`).
* `embedded_take`: the same for one take: the continuation starts in exactly
  the world the take was reached in, so its effects come once, after every
  earlier effect, in its own order.
* `portfolio_publishes`: such a step exists whenever some bound settles the
  demand, in particular whenever the generator has an answer.
* `Controls.unsound_admission`: admitting a generator with an effect gives a
  step that the plain cursor does not have.

The goals between a call and the commit of its `once` are treated in the last
section: the witness of the call alone is a witness of the whole body exactly
when those goals are determinate on every answer of the call
(`hoist_witness`, `hoist_complete`); a goal that can fail is not
(`Controls.failing_goal_is_not_hoisted`), nor one that can answer twice
(`Controls.branching_goal_is_not_determinate`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness (Step Space Reaches IsAnswer bounded
  boundedWork idWork)
open Mettapedia.Machines.BoundedSearchPortfolio (Origin Task Cursor Status status ready
  expandOne children Iteration beginIteration nextIteration BatchMeaning)

universe u v w x h r t b

variable {σ : Type x} {S : Type u} {A : Type v} {E : Type w}

/-! ## What a batch is to `once`, and that one is published -/

/-- **A batch for a demand of one** is one answer of the search, or is empty
and the search has no answer. -/
theorem once_batch (space : Space S A) (root : S) (answers : List A)
    (meaning : BatchMeaning space root 1 answers) :
    (∃ value, answers = [value] ∧ IsAnswer space root value) ∨
      (answers = [] ∧ ∀ value, ¬ IsAnswer space root value) := by
  have sound := BoundedSearchPortfolio.batchMeaning_sound space root 1 answers meaning
  obtain ⟨depth, suffix, _, limited, complete⟩ := meaning
  cases answers with
  | nil =>
      right
      rcases complete with full | ⟨all, uncut⟩
      · simp at full
      · exact ⟨rfl, Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness.no_answer_of_uncut_empty
          space uncut all.symm⟩
  | cons value rest =>
      left
      have none : rest = [] := by
        cases rest with
        | nil => rfl
        | cons other more => simp at limited
      subst none
      exact ⟨value, rfl, sound.2 value (by simp)⟩

theorem batch_of_published (duo : Duo (World σ E) (Walk S A) (Iteration S A))
    (published : duo.published.isSome = true) : ∃ answers, batch duo = some answers := by
  unfold batch
  cases winner : duo.published with
  | none => simp [winner] at published
  | some origin => cases origin <;> exact ⟨_, rfl⟩

/-- **The portfolio publishes** on a quiet root whenever some bound settles
the demand: under doubling quanta from one unit some round hands over a
lawful batch, with the world as it was. -/
theorem portfolio_publishes (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) (demand target : Nat)
    (decides : Decides (sys.space store) root demand target) (log : List E) :
    ∃ count answers,
      batch (portfolio sys root demand (rounds (doubling 1) count) store log) = some answers ∧
        BatchMeaning (sys.space store) root demand answers ∧
        (portfolio sys root demand (rounds (doubling 1) count) store log).world =
          ⟨store, log, none⟩ := by
  obtain ⟨units, _, outcome⟩ := deepen_need (sys.space store) root demand target decides
  have published := race_publishes_second (walkResumable (sys.space store) demand)
    (deepenResumable (sys.space store) root demand) (doubling 1)
    (⟨store, log, none⟩ : World σ E) ⟨[root], []⟩ (beginIteration root 0)
    (fun round => doubling_pos Nat.one_pos round) outcome
  obtain ⟨equal, sameWorld, lawful⟩ :=
    portfolio_quiet sys quiet demand (rounds (doubling 1) (units + 1)) log
  have same : portfolio sys root demand (rounds (doubling 1) (units + 1)) store log =
      race (walkResumable (sys.space store) demand)
        (deepenResumable (sys.space store) root demand) (doubling 1)
        (⟨store, log, none⟩ : World σ E) ⟨[root], []⟩ (beginIteration root 0) (units + 1) :=
    equal
  rw [← same] at published
  obtain ⟨answers, handed⟩ := batch_of_published _ published
  exact ⟨units + 1, answers, handed, lawful answers handed, sameWorld⟩

/-- For `once`: a quiet generator with an answer is served one of its
answers. -/
theorem once_publishes (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) {value : A} (answer : IsAnswer (sys.space store) root value)
    (log : List E) :
    ∃ count witness,
      batch (portfolio sys root 1 (rounds (doubling 1) count) store log) = some [witness] ∧
        IsAnswer (sys.space store) root witness ∧
        (portfolio sys root 1 (rounds (doubling 1) count) store log).world =
          ⟨store, log, none⟩ := by
  obtain ⟨depth, reaches⟩ := answer
  obtain ⟨count, answers, handed, lawful, sameWorld⟩ :=
    portfolio_publishes sys quiet 1 depth (decides_of_reaches reaches) log
  rcases once_batch (sys.space store) root answers lawful with ⟨witness, one, isAnswer⟩ | ⟨_, none⟩
  · subst one
    exact ⟨count, witness, handed, isAnswer, sameWorld⟩
  · exact absurd ⟨depth, reaches⟩ (none value)

/-! ## The host -/

/-- What a host state does next. -/
inductive HostMove (H : Type h) (S : Type u) (A : Type v) (E : Type w) (R : Type r) where
  | done (result : R)
  | effect (event : E) (next : H)
  | step (next : H)
  | take (demand : Nat) (root : S) (resume : Except E (List A) → H)

/-- A host: any machine with effects that asks generators for answers. -/
structure Host (σ : Type x) (H : Type h) (S : Type u) (A : Type v) (E : Type w)
    (R : Type r) where
  move : σ → H → HostMove H S A E R

/-- The host with its world. -/
structure HostState (σ : Type x) (E : Type w) (H : Type h) where
  store : σ
  log : List E
  control : H

/-- How a take is served: from a store, a log, a demand and a root to a store,
a log and a reply. -/
abbrev Service (σ : Type x) (S : Type u) (A : Type v) (E : Type w) :=
  σ → List E → Nat → S → σ → List E → Except E (List A) → Prop

/-- One step of a host whose takes are served by `service`. -/
inductive HostStep {H : Type h} {R : Type r} (sys : System σ S A E)
    (host : Host σ H S A E R) (service : Service σ S A E) :
    HostState σ E H → HostState σ E H → Prop
  | effect {state : HostState σ E H} {event : E} {next : H} :
      host.move state.store state.control = .effect event next →
        HostStep sys host service state
          ⟨sys.apply event state.store, state.log ++ [event], next⟩
  | step {state : HostState σ E H} {next : H} :
      host.move state.store state.control = .step next →
        HostStep sys host service state ⟨state.store, state.log, next⟩
  | take {state : HostState σ E H} {demand : Nat} {root : S}
      {resume : Except E (List A) → H} {store : σ} {log : List E}
      {reply : Except E (List A)} :
      host.move state.store state.control = .take demand root resume →
        service state.store state.log demand root store log reply →
        HostStep sys host service state ⟨store, log, resume reply⟩

theorem HostStep.mono {H : Type h} {R : Type r} {sys : System σ S A E}
    {host : Host σ H S A E R} {service other : Service σ S A E}
    (weaker : ∀ store log demand root store' log' reply,
      service store log demand root store' log' reply →
        other store log demand root store' log' reply)
    {before after : HostState σ E H} (stepped : HostStep sys host service before after) :
    HostStep sys host other before after := by
  cases stepped with
  | effect move => exact .effect move
  | step move => exact .step move
  | take move served => exact .take move (weaker _ _ _ _ _ _ _ served)

/-- The plain cursor serves: depth-first, performing what it meets, until it
has `demand` answers, has finished, or a raise ends it. -/
def plainServes (sys : System σ S A E) : Service σ S A E :=
  fun store log demand root store' log' reply =>
    ∃ fuel,
      store' = (plain sys root demand fuel store log).2.1.store ∧
        log' = (plain sys root demand fuel store log).2.1.log ∧
        (((plain sys root demand fuel store log).2.1.raised = none ∧
            ready ((plain sys root demand fuel store log).2.2.status demand) = true ∧
            reply = .ok (plain sys root demand fuel store log).2.2.reversed.reverse) ∨
          ∃ event, (plain sys root demand fuel store log).2.1.raised = some event ∧
            reply = .error event)

/-- The portfolio serves: some sequence of slices publishes a batch. -/
def portfolioServes (sys : System σ S A E) : Service σ S A E :=
  fun store log demand root store' log' reply =>
    ∃ slices answers,
      batch (portfolio sys root demand slices store log) = some answers ∧
        store' = (portfolio sys root demand slices store log).world.store ∧
        log' = (portfolio sys root demand slices store log).world.log ∧
        reply = .ok answers

/-- The law of a pure generator: the store and the log are untouched, and
the reply is a batch of the generator read at that store. -/
def lawServes (sys : System σ S A E) : Service σ S A E :=
  fun store log demand root store' log' reply =>
    store' = store ∧ log' = log ∧
      ∃ answers, reply = .ok answers ∧ BatchMeaning (sys.space store) root demand answers

/-- The machine: an admitted take may be served by the portfolio; the plain
cursor may serve any take. -/
def machineServes (sys : System σ S A E) (admits : σ → Nat → S → Prop) : Service σ S A E :=
  fun store log demand root store' log' reply =>
    (admits store demand root ∧ portfolioServes sys store log demand root store' log' reply) ∨
      plainServes sys store log demand root store' log' reply

/-- The specification: an admitted take follows the law of a pure generator;
any other is the plain cursor's. -/
def specServes (sys : System σ S A E) (admits : σ → Nat → S → Prop) : Service σ S A E :=
  fun store log demand root store' log' reply =>
    (admits store demand root ∧ lawServes sys store log demand root store' log' reply) ∨
      (¬ admits store demand root ∧
        plainServes sys store log demand root store' log' reply)

theorem portfolioServes_law (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) {log : List E} {demand : Nat} {store' : σ} {log' : List E}
    {reply : Except E (List A)}
    (served : portfolioServes sys store log demand root store' log' reply) :
    lawServes sys store log demand root store' log' reply := by
  obtain ⟨slices, answers, handed, sameStore, sameLog, replied⟩ := served
  obtain ⟨_, sameWorld, lawful⟩ := portfolio_quiet sys quiet demand slices log
  rw [sameWorld] at sameStore sameLog
  exact ⟨sameStore, sameLog, answers, replied, lawful answers handed⟩

theorem plainServes_law (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) {log : List E} {demand : Nat} {store' : σ} {log' : List E}
    {reply : Except E (List A)}
    (served : plainServes sys store log demand root store' log' reply) :
    lawServes sys store log demand root store' log' reply := by
  obtain ⟨fuel, sameStore, sameLog, outcome⟩ := served
  obtain ⟨sameWorld, lawful⟩ := plain_quiet sys quiet demand fuel log
  rw [sameWorld] at sameStore sameLog
  rcases outcome with ⟨_, finished, replied⟩ | ⟨event, raised, _⟩
  · exact ⟨sameStore, sameLog, _, replied, lawful finished⟩
  · rw [sameWorld] at raised
    cases raised

/-- **Every service of the machine is a service of the specification** when
admission implies quietness. -/
theorem machineServes_spec (sys : System σ S A E) (admits : σ → Nat → S → Prop)
    (sound : ∀ store demand root, admits store demand root → Quiet sys store root)
    (store : σ) (log : List E) (demand : Nat) (root : S) (store' : σ) (log' : List E)
    (reply : Except E (List A))
    (served : machineServes sys admits store log demand root store' log' reply) :
    specServes sys admits store log demand root store' log' reply := by
  rcases served with ⟨admitted, byPortfolio⟩ | byPlain
  · exact Or.inl ⟨admitted, portfolioServes_law sys (sound _ _ _ admitted) byPortfolio⟩
  · by_cases admitted : admits store demand root
    · exact Or.inl ⟨admitted, plainServes_law sys (sound _ _ _ admitted) byPlain⟩
    · exact Or.inr ⟨admitted, byPlain⟩

/-- **Embedding.** For every host, every state and every log: when admission
implies quietness, a step of the machine is a step of the specification. -/
theorem machine_refines_spec {H : Type h} {R : Type r} (sys : System σ S A E)
    (host : Host σ H S A E R) (admits : σ → Nat → S → Prop)
    (sound : ∀ store demand root, admits store demand root → Quiet sys store root)
    {before after : HostState σ E H}
    (stepped : HostStep sys host (machineServes sys admits) before after) :
    HostStep sys host (specServes sys admits) before after :=
  stepped.mono (machineServes_spec sys admits sound)

/-- The same for whole runs. -/
theorem machine_runs_refine_spec {H : Type h} {R : Type r} (sys : System σ S A E)
    (host : Host σ H S A E R) (admits : σ → Nat → S → Prop)
    (sound : ∀ store demand root, admits store demand root → Quiet sys store root)
    {before after : HostState σ E H}
    (run : Relation.ReflTransGen (HostStep sys host (machineServes sys admits)) before after) :
    Relation.ReflTransGen (HostStep sys host (specServes sys admits)) before after := by
  induction run with
  | refl => exact .refl
  | tail _ stepped ih => exact .tail ih (machine_refines_spec sys host admits sound stepped)

/-- **One embedded take.** An admitted take, wherever the host is, leaves the
store and the log as they were and resumes the host once, on a batch of the
generator's answers. What the continuation then performs is appended to the
log it found. -/
theorem embedded_take {H : Type h} {R : Type r} (sys : System σ S A E)
    (host : Host σ H S A E R) (admits : σ → Nat → S → Prop)
    (sound : ∀ store demand root, admits store demand root → Quiet sys store root)
    {before after : HostState σ E H} {demand : Nat} {root : S}
    {resume : Except E (List A) → H}
    (asks : host.move before.store before.control = .take demand root resume)
    (admitted : admits before.store demand root)
    (stepped : HostStep sys host (machineServes sys admits) before after) :
    ∃ answers, after = ⟨before.store, before.log, resume (.ok answers)⟩ ∧
      BatchMeaning (sys.space before.store) root demand answers := by
  cases stepped with
  | effect move => rw [asks] at move; cases move
  | step move => rw [asks] at move; cases move
  | take move served =>
      rw [asks] at move
      cases move
      rcases machineServes_spec sys admits sound _ _ _ _ _ _ _ served with
        ⟨_, sameStore, sameLog, answers, replied, lawful⟩ | ⟨refused, _⟩
      · subst sameStore sameLog replied
        exact ⟨answers, rfl, lawful⟩
      · exact absurd admitted refused

/-- For `once`: the host resumes on one answer of the generator, or on the
empty batch when the generator has none. -/
theorem embedded_once {H : Type h} {R : Type r} (sys : System σ S A E)
    (host : Host σ H S A E R) (admits : σ → Nat → S → Prop)
    (sound : ∀ store demand root, admits store demand root → Quiet sys store root)
    {before after : HostState σ E H} {root : S} {resume : Except E (List A) → H}
    (asks : host.move before.store before.control = .take 1 root resume)
    (admitted : admits before.store 1 root)
    (stepped : HostStep sys host (machineServes sys admits) before after) :
    (∃ value, after = ⟨before.store, before.log, resume (.ok [value])⟩ ∧
        IsAnswer (sys.space before.store) root value) ∨
      (after = ⟨before.store, before.log, resume (.ok [])⟩ ∧
        ∀ value, ¬ IsAnswer (sys.space before.store) root value) := by
  obtain ⟨answers, landed, lawful⟩ := embedded_take sys host admits sound asks admitted stepped
  rcases once_batch (sys.space before.store) root answers lawful with
    ⟨value, one, isAnswer⟩ | ⟨none, noAnswer⟩
  · subst one
    exact Or.inl ⟨value, landed, isAnswer⟩
  · subst none
    exact Or.inr ⟨landed, noAnswer⟩

/-! ## The goals between a call and its commit -/

section Hoist

variable {T : Type t} {B : Type b}

/-- The body of a `once` whose call is followed by more goals before the
commit: every answer of the call enters those goals. -/
def chain (call : Space S A) (after : Space T B) (enter : A → T) : Space (S ⊕ T) B where
  expand
    | .inl state =>
        match call.expand state with
        | .answer value => .branch [.inr (enter value)]
        | .branch children => .branch (children.map .inl)
    | .inr state =>
        match after.expand state with
        | .answer value => .answer value
        | .branch children => .branch (children.map .inr)

theorem chain_after (call : Space S A) (after : Space T B) (enter : A → T) {state : T}
    {result : B} {depth : Nat} (reaches : Reaches after state result depth) :
    Reaches (chain call after enter) (.inr state) result depth := by
  induction reaches with
  | answer expands => exact .answer (by simp [chain, expands])
  | @branch state child result depth states expands member _ ih =>
      exact .branch (cs := states.map .inr) (by simp [chain, expands])
        (List.mem_map_of_mem member) ih

theorem chain_call (call : Space S A) (after : Space T B) (enter : A → T) {state : S}
    {value : A} {depth : Nat} (reaches : Reaches call state value depth) {result : B}
    (continues : IsAnswer after (enter value) result) :
    IsAnswer (chain call after enter) (.inl state) result := by
  induction reaches with
  | @answer state value expands =>
      obtain ⟨later, reachesAfter⟩ := continues
      exact ⟨later + 1, .branch (c := .inr (enter value)) (cs := [.inr (enter value)])
        (by simp [chain, expands]) (by simp) (chain_after call after enter reachesAfter)⟩
  | @branch state child value depth states expands member _ ih =>
      obtain ⟨later, reachesChild⟩ := ih continues
      exact ⟨later + 1, .branch (cs := states.map .inl) (by simp [chain, expands])
        (List.mem_map_of_mem member) reachesChild⟩

theorem chain_split (call : Space S A) (after : Space T B) (enter : A → T) {start : S ⊕ T}
    {result : B} {depth : Nat} (reaches : Reaches (chain call after enter) start result depth) :
    (∀ state, start = .inr state → IsAnswer after state result) ∧
      (∀ state, start = .inl state →
        ∃ value, IsAnswer call state value ∧ IsAnswer after (enter value) result) := by
  induction reaches with
  | @answer start result expands =>
      constructor
      · intro state here
        subst here
        cases expansion : after.expand state with
        | answer value =>
            simp only [chain, expansion, Step.answer.injEq] at expands
            subst expands
            exact ⟨0, .answer expansion⟩
        | branch states => simp [chain, expansion] at expands
      · intro state here
        subst here
        cases expansion : call.expand state <;> simp [chain, expansion] at expands
  | @branch start child result depth states expands member _ ih =>
      constructor
      · intro state here
        subst here
        cases expansion : after.expand state with
        | answer value => simp [chain, expansion] at expands
        | branch children =>
            simp only [chain, expansion, Step.branch.injEq] at expands
            subst expands
            obtain ⟨next, inChildren, rfl⟩ := List.mem_map.mp member
            exact Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness.isAnswer_of_child after
              expansion inChildren (ih.1 next rfl)
      · intro state here
        subst here
        cases expansion : call.expand state with
        | answer value =>
            simp only [chain, expansion, Step.branch.injEq] at expands
            subst expands
            simp only [List.mem_singleton] at member
            subst member
            exact ⟨value, ⟨0, .answer expansion⟩, ih.1 (enter value) rfl⟩
        | branch children =>
            simp only [chain, expansion, Step.branch.injEq] at expands
            subst expands
            obtain ⟨next, inChildren, rfl⟩ := List.mem_map.mp member
            obtain ⟨value, isAnswer, continues⟩ := ih.2 next rfl
            exact ⟨value,
              Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness.isAnswer_of_child call expansion
                inChildren isAnswer, continues⟩

/-- **The answers of the body** are the continuations of the call's answers. -/
theorem chain_answer_iff (call : Space S A) (after : Space T B) (enter : A → T) (root : S)
    (result : B) :
    IsAnswer (chain call after enter) (.inl root) result ↔
      ∃ value, IsAnswer call root value ∧ IsAnswer after (enter value) result := by
  constructor
  · rintro ⟨depth, reaches⟩
    exact (chain_split call after enter reaches).2 root rfl
  · rintro ⟨value, ⟨depth, reaches⟩, continues⟩
    exact chain_call call after enter reaches continues

/-- The goals after the call are determinate on the call's answers: each
answer of the call has exactly the one continuation `finish` names. They
cannot fail and cannot leave a choice. -/
def Determinate (call : Space S A) (root : S) (after : Space T B) (enter : A → T)
    (finish : A → B) : Prop :=
  ∀ value, IsAnswer call root value →
    ∀ result, IsAnswer after (enter value) result ↔ result = finish value

/-- **Hoisting the commit.** When the goals between the call and the commit
are determinate, a witness of the call alone, run once through those goals,
is a witness of the whole body. -/
theorem hoist_witness {call : Space S A} {root : S} {after : Space T B} {enter : A → T}
    {finish : A → B} (determinate : Determinate call root after enter finish) {value : A}
    (witness : IsAnswer call root value) :
    IsAnswer (chain call after enter) (.inl root) (finish value) :=
  (chain_answer_iff call after enter root (finish value)).mpr
    ⟨value, witness, (determinate value witness (finish value)).mpr rfl⟩

/-- Every witness of the body arises so. -/
theorem hoist_complete {call : Space S A} {root : S} {after : Space T B} {enter : A → T}
    {finish : A → B} (determinate : Determinate call root after enter finish) {result : B}
    (answer : IsAnswer (chain call after enter) (.inl root) result) :
    ∃ value, IsAnswer call root value ∧ result = finish value := by
  obtain ⟨value, witness, continues⟩ := (chain_answer_iff call after enter root result).mp answer
  exact ⟨value, witness, (determinate value witness result).mp continues⟩

/-- A call without an answer leaves the body without one, whatever follows. -/
theorem hoist_none {call : Space S A} {root : S} (after : Space T B) (enter : A → T)
    (none : ∀ value, ¬ IsAnswer call root value) (result : B) :
    ¬ IsAnswer (chain call after enter) (.inl root) result := by
  intro answer
  obtain ⟨value, witness, _⟩ := (chain_answer_iff call after enter root result).mp answer
  exact none value witness

end Hoist

namespace Controls

/-- A host that asks for one answer in the value of a `let`, and whose body
then performs an effect that names it. -/
inductive Stage where
  | ask
  | got (reply : Except Nat (List Nat))
  | finished

def letHost : Host Unit Stage Nat Nat Nat Unit where
  move _ stage :=
    match stage with
    | .ask => .take 1 0 .got
    | .got (.ok [value]) => .effect value .finished
    | .got _ => .done ()
    | .finished => .done ()

/-- The positive case. The generator's first alternative never ends, so the
plain cursor never answers (`sidetrack_plain_never`). Embedded in the `let`,
the portfolio hands `4` to the body, whose effect is performed once: the log
is `[4]`. -/
theorem let_value_is_served :
    Relation.ReflTransGen
      (HostStep (System.ofSpace (σ := Unit) (E := Nat) sidetrack) letHost
        (machineServes (System.ofSpace (σ := Unit) (E := Nat) sidetrack) (fun _ _ _ => True)))
      ⟨(), [], .ask⟩ ⟨(), [4], .finished⟩ := by
  refine Relation.ReflTransGen.trans (b := ⟨(), [], Stage.got (.ok [4])⟩) ?_ ?_
  · exact Relation.ReflTransGen.single
      (HostStep.take (state := ⟨(), [], Stage.ask⟩) (demand := 1) (root := 0)
        (resume := Stage.got) (store := ()) (log := []) (reply := .ok [4]) rfl
        (Or.inl ⟨trivial, rounds (doubling 1) 3, [4], by decide, rfl, by decide, rfl⟩))
  · exact Relation.ReflTransGen.single
      (HostStep.effect (state := ⟨(), [], Stage.got (.ok [4])⟩) (event := 4)
        (next := Stage.finished) rfl)

/-- The plain cursor has one way to serve the generator with the deep effect:
it performs the effect and answers `5`. -/
theorem effectDeep_plain {store' : Unit} {log' : List Nat} {reply : Except Nat (List Nat)}
    (served : plainServes effectDeep () [] 1 0 store' log' reply) :
    log' = [7] ∧ reply = .ok [5] := by
  obtain ⟨fuel, _, sameLog, outcome⟩ := served
  have settled : plain effectDeep 0 1 fuel () [] = plain effectDeep 0 1 20 () [] := by
    unfold plain
    rcases Nat.le_total fuel 20 with small | large
    · have stopped : ((walkActor effectDeep 1).ready
            ((walkActor effectDeep 1).work halted fuel ⟨(), [], none⟩ ⟨[0], []⟩).2.2 ||
          halted ((walkActor effectDeep 1).work halted fuel ⟨(), [], none⟩ ⟨[0], []⟩).2.1) =
            true := by
        rcases outcome with ⟨_, finished, _⟩ | ⟨event, raised, _⟩
        · have ready' : (walkActor effectDeep 1).ready
              ((walkActor effectDeep 1).work halted fuel ⟨(), [], none⟩ ⟨[0], []⟩).2.2 = true :=
            finished
          rw [ready', Bool.true_or]
        · have halt : halted
              ((walkActor effectDeep 1).work halted fuel ⟨(), [], none⟩ ⟨[0], []⟩).2.1 = true := by
            show ((plain effectDeep 0 1 fuel () []).2.1.raised).isSome = true
            rw [raised]
            rfl
          rw [halt, Bool.or_true]
      have stable := Actor.work_stable (walkActor effectDeep 1) halted fuel (20 - fuel)
        ⟨(), [], none⟩ ⟨[0], []⟩ stopped
      rw [show fuel + (20 - fuel) = 20 by omega] at stable
      exact stable.symm
    · have stable := Actor.work_stable (walkActor effectDeep 1) halted 20 (fuel - 20)
        ⟨(), [], none⟩ ⟨[0], []⟩ (by decide)
      rw [show 20 + (fuel - 20) = fuel by omega] at stable
      exact stable
  rw [settled] at sameLog outcome
  refine ⟨sameLog.trans (by decide), ?_⟩
  rcases outcome with ⟨_, _, replied⟩ | ⟨event, raised, _⟩
  · exact replied.trans (by decide)
  · have none : (plain effectDeep 0 1 20 () []).2.1.raised = none := by decide
    rw [none] at raised
    cases raised

/-- **Admitting a generator with an effect.** The portfolio serves it the
shallow `6` with nothing performed; the plain cursor never does that. -/
theorem unsound_admission :
    portfolioServes effectDeep () [] 1 0 () [] (.ok [6]) ∧
      ¬ plainServes effectDeep () [] 1 0 () [] (.ok [6]) := by
  refine ⟨⟨rounds (doubling 1) 3, [6], by decide, rfl, by decide, rfl⟩, ?_⟩
  intro served
  have log := (effectDeep_plain served).1
  cases log

/-- In the `let` host the difference is in the log: with the generator
admitted the body's effect is the only one, `[6]`; under the plain cursor the
log is the generator's effect and then the body's, `[7, 5]`. -/
theorem lost_effect_in_let :
    Relation.ReflTransGen
        (HostStep effectDeep letHost (machineServes effectDeep (fun _ _ _ => True)))
        ⟨(), [], .ask⟩ ⟨(), [6], .finished⟩ ∧
      Relation.ReflTransGen
        (HostStep effectDeep letHost (machineServes effectDeep (fun _ _ _ => False)))
        ⟨(), [], .ask⟩ ⟨(), [7, 5], .finished⟩ := by
  constructor
  · refine Relation.ReflTransGen.trans (b := ⟨(), [], Stage.got (.ok [6])⟩) ?_ ?_
    · exact Relation.ReflTransGen.single
        (HostStep.take (state := ⟨(), [], Stage.ask⟩) (demand := 1) (root := 0)
          (resume := Stage.got) (store := ()) (log := []) (reply := .ok [6]) rfl
          (Or.inl ⟨trivial, unsound_admission.1⟩))
    · exact Relation.ReflTransGen.single
        (HostStep.effect (state := ⟨(), [], Stage.got (.ok [6])⟩) (event := 6)
          (next := Stage.finished) rfl)
  · refine Relation.ReflTransGen.trans (b := ⟨(), [7], Stage.got (.ok [5])⟩) ?_ ?_
    · exact Relation.ReflTransGen.single
        (HostStep.take (state := ⟨(), [], Stage.ask⟩) (demand := 1) (root := 0)
          (resume := Stage.got) (store := ()) (log := [7]) (reply := .ok [5]) rfl
          (Or.inr ⟨20, rfl, by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩))
    · exact Relation.ReflTransGen.single
        (HostStep.effect (state := ⟨(), [7], Stage.got (.ok [5])⟩) (event := 5)
          (next := Stage.finished) rfl)

/-- A call with the answers `1` and `2`. -/
def two : Space Nat Nat where
  expand
    | 0 => .branch [1, 2]
    | 1 => .answer 1
    | 2 => .answer 2
    | _ => .branch []

/-- A goal that succeeds on `2` alone. -/
def onlyTwo : Space Nat Nat where
  expand state := if state = 2 then .answer 2 else .branch []

/-- A goal that can fail is not hoisted past the commit: `1` is a witness of
the call, the goal after it fails on `1`, and yet the body has the answer
`2`. Taking the call's witness alone and then running the goal would report
no answer. -/
theorem failing_goal_is_not_hoisted :
    IsAnswer two 0 1 ∧ (∀ result, ¬ IsAnswer onlyTwo 1 result) ∧
      IsAnswer (chain two onlyTwo id) (.inl 0) 2 := by
  refine ⟨⟨1, .branch (c := 1) (cs := [1, 2]) rfl (by simp) (.answer rfl)⟩, ?_, ?_⟩
  · exact Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness.no_answer_of_uncut_empty onlyTwo
      (d := 0) rfl rfl
  · exact (chain_answer_iff two onlyTwo id 0 2).mpr
      ⟨2, ⟨1, .branch (c := 2) (cs := [1, 2]) rfl (by simp) (.answer rfl)⟩, ⟨0, .answer rfl⟩⟩

/-- A goal with two answers for each value. -/
def twice : Space Nat Nat where
  expand state := if state < 100 then .branch [100 + state, 200 + state] else .answer state

/-- A goal that can answer twice is not determinate: the commit of the body
keeps one of its answers, and hoisting would let both through. -/
theorem branching_goal_is_not_determinate (finish : Nat → Nat) :
    ¬ Determinate two 0 twice id finish := by
  intro determinate
  have witness : IsAnswer two 0 1 :=
    ⟨1, .branch (c := 1) (cs := [1, 2]) rfl (by simp) (.answer rfl)⟩
  have first : IsAnswer twice (id 1) 101 :=
    ⟨1, .branch (c := 101) (cs := [101, 201]) rfl (by simp) (.answer rfl)⟩
  have second : IsAnswer twice (id 1) 201 :=
    ⟨1, .branch (c := 201) (cs := [101, 201]) rfl (by simp) (.answer rfl)⟩
  have one := (determinate 1 witness 101).mp first
  have other := (determinate 1 witness 201).mp second
  omega

end Controls

#print axioms once_batch
#print axioms portfolio_publishes
#print axioms once_publishes
#print axioms machine_refines_spec
#print axioms machine_runs_refine_spec
#print axioms embedded_take
#print axioms embedded_once
#print axioms chain_answer_iff
#print axioms hoist_witness
#print axioms hoist_complete
#print axioms Controls.let_value_is_served
#print axioms Controls.unsound_admission
#print axioms Controls.lost_effect_in_let
#print axioms Controls.failing_goal_is_not_hoisted
#print axioms Controls.branching_goal_is_not_determinate

end Mettapedia.Machines.PortfolioReach
