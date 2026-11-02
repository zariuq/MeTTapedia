import Mettapedia.GSLT.Coordination.ConsensusNumbers.Race

/-!
# Rho communication as a shared object

The tuple space of the rho calculus, with its two interactions:

* `send outs`: put messages in the space;
* `join cs outs`: **COMM** with a join: take one message on each channel of `cs`, and put the
  continuation's messages `outs`, built from what was received, in the same step. A message on a
  channel with nothing to receive keeps waiting: the operation **waits** while some channel of
  `cs` has no message (`Controls.empty_channel_waits`).

What a continuation sends is built by substitution only: payloads are terms of literals and
pairs (`Tm`), and an output is a template over the received payloads (`Tpl`). A continuation
cannot compute on what it received before sending it on; it can only put it inside a new term.
Example: `for (y <- cell) { cell!(pair(lit a, y)) | ... }` receives the payload `y` on `cell` and
sends `pair (lit a) y` on `cell`, in one step.

## Every deterministic object runs over one message

Keep the object's **history** (the list of operations applied, newest first) as the one message on
a channel `cell`. Applying `a` is one COMM: take the message, send it back with `a` put in front
(Herlihy's fetch-and-cons). The process then replays the history it received, locally, to learn
its answer. The message is always there, so nobody waits.

* **Simulation** (`rho_runs_every_object`): a wait-free consensus protocol over any deterministic
  object becomes one over rho with the same decisions.
* So **rho COMM has an infinite consensus number** (`rho_hasConsensusNumber_top`), already with
  single receives; joins are not needed.
* In particular rho runs the step-space, with its absence checks, wait-free; what it cannot do is
  run it **compositionally**, one space per space (`Absence`).

Herlihy (p. 128) considers only operations that always respond. Here a waiting process is a
process that does not finish, so waiting counts against wait-freedom; no protocol here ever
waits.

## Controls

* `Controls.empty_channel_waits`: a receive on an empty space waits.
* `Controls.cell_fires`: a receive on the cell fires, and the history grows by one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-- Payloads: literals and pairs. -/
inductive Tm (L : Type) where
  | lit (l : L)
  | pair (a b : Tm L)
  deriving DecidableEq

/-- Templates over received payloads `X`: what a continuation sends. -/
inductive Tpl (X L : Type) where
  | var (x : X)
  | lit (l : L)
  | pair (a b : Tpl X L)

/-- Substitute the received payloads into a template. -/
def Tpl.fill {X L : Type} (args : X → Tm L) : Tpl X L → Tm L
  | .var x => args x
  | .lit l => .lit l
  | .pair a b => .pair (a.fill args) (b.fill args)

/-- Rho interactions: send, or COMM with a join. -/
inductive RhoOp (Ch L : Type) where
  | send (outs : List (Ch × Tm L))
  | join (cs : List Ch) (outs : List (Ch × Tpl (Fin cs.length) L))

/-- What a join receives, as messages. -/
def received {Ch L : Type} (cs : List Ch) (args : Fin cs.length → Tm L) : Multiset (Ch × Tm L) :=
  ↑(List.ofFn fun j => (cs.get j, args j))

/-- What a join's continuation sends. -/
def sent {Ch L : Type} {cs : List Ch} (outs : List (Ch × Tpl (Fin cs.length) L))
    (args : Fin cs.length → Tm L) : Multiset (Ch × Tm L) :=
  ↑(outs.map fun o => (o.1, o.2.fill args))

/-- **The rho tuple space as a shared object.** A join fires on any choice of one message per
channel; it waits while there is none. -/
abbrev rhoObject (Ch L : Type) [DecidableEq Ch] [DecidableEq L] : ObjectType where
  State := Multiset (Ch × Tm L)
  Op := RhoOp Ch L
  Res := List (Tm L)
  Fires M op M' r := match op with
    | .send outs => M' = M + ↑outs ∧ r = []
    | .join cs outs => ∃ args : Fin cs.length → Tm L,
        received cs args ≤ M ∧ M' = M - received cs args + sent outs args ∧ r = List.ofFn args

section Simulation

variable {Ch L : Type} [DecidableEq Ch] [DecidableEq L]
variable {T : DetObject} {n : ℕ} {V : Type}
variable (c : Ch) (lit : Option T.Op → L)

/-- A history as a payload: newest operation first. -/
def hist : List T.Op → Tm L
  | [] => .lit (lit none)
  | a :: h => .pair (.lit (lit (some a))) (hist h)

open Classical in
/-- Read a history back. -/
noncomputable def unhist : Tm L → List T.Op
  | .pair (.lit l) rest => if h : ∃ a, lit (some a) = l then h.choose :: unhist rest else []
  | _ => []

omit [DecidableEq L] in
variable {lit} in
theorem unhist_hist (inj : Function.Injective lit) (h : List T.Op) : unhist lit (hist lit h) = h := by
  induction h with
  | nil => simp [hist, unhist]
  | cons a h ih =>
      simp only [hist, unhist]
      have ex : ∃ b, lit (some b) = lit (some a) := ⟨a, rfl⟩
      rw [dif_pos ex, ih]
      have := Exists.choose_spec ex
      rw [Option.some.inj (inj this)]

/-- The state after a history, from `s`. -/
def replay (s : T.State) : List T.Op → T.State
  | [] => s
  | a :: h => (T.apply (replay s h) a).1

/-- Apply `a` as one COMM on the cell: take the history, send it back with `a` in front. -/
def cellOp (a : T.Op) : RhoOp Ch L :=
  .join [c] [(c, .pair (.lit (lit (some a))) (.var ⟨0, by simp⟩))]

/-- A process's action over rho: decide as before, or apply its operation in the cell. -/
def toRho : Action T.Op V → Action (RhoOp Ch L) V
  | .decide v => .decide v
  | .invoke a => .invoke (cellOp c lit a)

/-- The answer of `a`, replayed from the history received. -/
noncomputable def answer (s : T.State) (a : T.Op) (r : List (Tm L)) : T.Res :=
  (T.apply (replay s (unhist lit (r.headD (.lit (lit none))))) a).2

/-- **The protocol over rho**: each process does what it did, applying its operation to the
history in the cell and replaying the history it received to learn the answer. -/
noncomputable abbrev overRho (P : Protocol T.toObject n V) : Protocol (rhoObject Ch L) n V where
  Local := P.Local
  start := P.start
  init := {(c, hist lit [])}
  action i l := toRho c lit (P.action i l)
  next i l r := match P.action i l with
    | .decide _ => l
    | .invoke a => P.next i l (answer lit P.init a r)

variable {c lit} (P : Protocol T.toObject n V)

/-- The rho configuration holds, in its cell, a history that replays to the object's state. -/
def Simulates (C' : (overRho c lit P).Config) (C : P.Config) : Prop :=
  C'.loc = C.loc ∧ ∃ h, C'.obj = {(c, hist lit h)} ∧ replay P.init h = C.obj

variable {P}

theorem simulates_decision {C' : (overRho c lit P).Config} {C : P.Config} (sim : Simulates P C' C)
    (i : Fin n) : (overRho c lit P).decision C' i = P.decision C i := by
  unfold Protocol.decision
  have act : (overRho c lit P).action i (C'.loc i) = toRho c lit (P.action i (C.loc i)) := by
    rw [sim.1]
  rw [act]
  cases P.action i (C.loc i) <;> rfl

theorem overRho_next {i : Fin n} {l : P.Local} {a : T.Op} (h : P.action i l = .invoke a)
    (r : List (Tm L)) : (overRho c lit P).next i l r = P.next i l (answer lit P.init a r) := by
  show (match P.action i l with
    | .decide _ => l
    | .invoke a => P.next i l (answer lit P.init a r)) = _
  rw [h]

omit [DecidableEq Ch] [DecidableEq L] in
theorem received_cell (args : Fin [c].length → Tm L) :
    received [c] args = {(c, args ⟨0, by simp⟩)} := by
  simp [received, List.ofFn_succ]

/-- **One rho step is one step of the object.** -/
theorem Simulates.step (inj : Function.Injective lit) {C' D' : (overRho c lit P).Config} {C : P.Config}
    (sim : Simulates P C' C) {i : Fin n} (step : (overRho c lit P).Step C' i D') :
    Simulates P D' (P.go C i) := by
  obtain ⟨locs, h, obj, replays⟩ := sim
  have act : (overRho c lit P).action i (C'.loc i) = toRho c lit (P.action i (C.loc i)) := by
    rw [locs]
  cases hP : P.action i (C.loc i) with
  | decide v =>
      rw [hP] at act
      rw [Protocol.go_of_decide hP, step.eq_of_decide act]
      exact ⟨locs, h, obj, replays⟩
  | invoke a =>
      rw [hP] at act
      rw [Protocol.go_of_invoke hP]
      cases step with
      | decided h' => rw [act] at h'; cases h'
      | waits h' never =>
          rw [act] at h'
          cases h'
          exact absurd ⟨fun _ => hist lit h, by rw [received_cell, obj], rfl, rfl⟩
            (never _ _)
      | fires h' fires =>
          rw [act] at h'
          cases h'
          obtain ⟨args, le, rfl, rfl⟩ := fires
          rw [received_cell, obj, Multiset.singleton_le, Multiset.mem_singleton] at le
          have arg : args ⟨0, by simp⟩ = hist lit h := (Prod.ext_iff.mp le).2
          have arg0 : args 0 = hist lit h := arg
          refine ⟨?_, a :: h, ?_, ?_⟩
          · funext k
            by_cases same : k = i
            · subst same
              simp only [Function.update_self, locs]
              rw [hP]
              simp [answer, List.ofFn_succ, arg0, unhist_hist inj, replays]
            · simp only [Function.update_of_ne same, locs]
          · rw [obj, received_cell, arg]
            simp [sent, Tpl.fill, arg0, hist]
          · simp [replay, replays]

theorem Simulates.run (inj : Function.Injective lit) {C' D' : (overRho c lit P).Config}
    {C : P.Config} (sim : Simulates P C' C) {σ : List (Fin n)} (run : (overRho c lit P).Run C' σ D') :
    Simulates P D' (P.run C σ) := by
  induction σ generalizing C' C with
  | nil => rw [run]; exact sim
  | cons i σ ih =>
      obtain ⟨E', step, rest⟩ := run
      exact ih (sim.step inj step) rest

theorem simulates_initial (x : Fin n → V) :
    Simulates P ((overRho c lit P).initial x) (P.initial x) :=
  ⟨rfl, [], rfl, rfl⟩

theorem Simulates.reach (inj : Function.Injective lit) {x : Fin n → V}
    {C' : (overRho c lit P).Config} (reach : (overRho c lit P).Reach x C') :
    ∃ C, P.Reach x C ∧ Simulates P C' C := by
  obtain ⟨σ, run⟩ := reach
  exact ⟨_, Protocol.reach_iff.mpr ⟨σ, rfl⟩, (simulates_initial x).run inj run⟩

/-- **Every wait-free consensus protocol over a deterministic object runs over rho**, keeping the
object's history in one message. -/
theorem rho_runs_every_object (inj : Function.Injective lit) (S : P.Solves) :
    (overRho c lit P).Solves := by
  refine ⟨?_, ?_, ?_⟩
  · intro x C' reach i j v w hv hw
    obtain ⟨C, reachC, sim⟩ := Simulates.reach inj reach
    rw [simulates_decision sim] at hv hw
    exact S.agreement x C reachC i j v w hv hw
  · intro x C' reach i v hv
    obtain ⟨C, reachC, sim⟩ := Simulates.reach inj reach
    rw [simulates_decision sim] at hv
    exact S.validity x C reachC i v hv
  · intro x σ c' start exec i often
    have sims : ∀ m, Simulates P (c' m) (P.runFrom (P.initial x) σ m) := by
      intro m
      induction m with
      | zero => rw [start]; exact simulates_initial x
      | succ m ih => exact ih.step inj (exec m)
    obtain ⟨m, hm⟩ := S.waitFree x σ _ rfl (Protocol.execution_runFrom _ σ) i often
    exact ⟨m, by rw [simulates_decision (sims m)]; exact hm⟩

end Simulation

/-- A code for the operations of a compare-and-swap register on booleans. -/
def casCode : CasOp Bool → ℕ
  | .cas e new => Encodable.encode (e, new) + 1
  | .read => 0

theorem casCode_injective : Function.Injective casCode := by
  rintro (⟨e, new⟩ | _) (⟨e', new'⟩ | _) h <;> simp_all [casCode]

/-- **Rho COMM has an infinite consensus number**, for any channels and any infinite supply of
literals. -/
theorem rho_hasConsensusNumber_top (Ch L : Type) [DecidableEq Ch] [DecidableEq L] [Nonempty Ch]
    [Infinite L] : HasConsensusNumber (rhoObject Ch L) ⊤ := by
  intro n
  refine ⟨fun _ => le_top, fun _ => ?_⟩
  obtain ⟨P, S⟩ := (casRegister_race Bool).solvable n
  let lit : Option (CasOp Bool) → L := fun o =>
    Infinite.natEmbedding L (Encodable.encode (o.map casCode))
  have inj : Function.Injective lit := by
    intro o o' h
    have := Encodable.encode_injective ((Infinite.natEmbedding L).injective h)
    exact Option.map_injective casCode_injective this
  exact ⟨_, rho_runs_every_object (c := Classical.arbitrary Ch) inj S⟩

namespace Controls

/-- **Negative control**: a receive on an empty space waits. -/
theorem empty_channel_waits (outs : List (Unit × Tpl (Fin [()].length) Bool)) (s : Multiset (Unit × Tm Bool))
    (r : List (Tm Bool)) : ¬ (rhoObject Unit Bool).Fires 0 (.join [()] outs) s r := by
  rintro ⟨args, le, -, -⟩
  rw [received_cell] at le
  simp at le

/-- **Positive control**: a receive on the cell fires, taking the history and sending it back
with the new operation in front. -/
theorem cell_fires :
    (rhoObject Unit Bool).Fires {((), Tm.lit false)}
      (.join [()] [((), .pair (.lit true) (.var ⟨0, by simp⟩))])
      {((), .pair (.lit true) (.lit false))} [Tm.lit false] :=
  ⟨fun _ => .lit false, by rw [received_cell], by rw [received_cell]; simp [sent, Tpl.fill], rfl⟩

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
