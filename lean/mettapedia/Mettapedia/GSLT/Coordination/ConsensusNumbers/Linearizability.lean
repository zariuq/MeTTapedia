import Mettapedia.GSLT.Coordination.ConsensusNumbers.Registers

/-!
# Implementations, linearizability and wait-freedom

Herlihy's notion of one object implementing another (*Wait-free synchronization*, TOPLAS 1991,
§2.3), with Herlihy and Wing's correctness condition (*Linearizability: a correctness condition for
concurrent objects*, TOPLAS 1990).

## Words

* **Target and base**: an implementation builds a *target* object, given by its sequential
  specification (a `DetObject`: each operation, applied at a state, gives a new state and an
  answer), out of *base* objects that really exist (an `ObjectType`). Example: a counter (target)
  built from registers (base).
* **History**: what the outside sees of a run: the calls of target operations and their returns,
  in order (`Event`). Example: `[invoke 0 (write 1), invoke 1 read, respond 0 ack, respond 1 1]`.
* **Front-end**: each process runs a small program for each target operation it is called with:
  it calls base operations one at a time and finally returns an answer (`Implementation`). Between
  operations it keeps a memory (`Mem`); during one it is in a working state (`Work`).
* **Atomic implementation** (`atomic`): the target itself, used directly: a call becomes one base
  operation applied at some instant, and the process returns its answer later.
* **Linearizable history** (`LinearizableHistory`): one that the atomic implementation can show.
  So each operation is given one instant between its call and its return at which it takes effect,
  and the answers are those of the sequential specification applied in the order of the instants.
  This is Herlihy and Wing's "each operation appears to take effect instantaneously at some point
  between its invocation and its response"; an operation still in progress may take effect or not.
* **Linearizable implementation** (`Implementation.Linearizable`): every history it shows is
  linearizable.
* **Wait-free implementation** (`Implementation.WaitFree`): in every execution, a process with an
  operation in progress that is moved infinitely often returns, whatever the other processes do,
  including stopping forever.
* `Implements X Y s₀ n`: some implementation of `Y`, started at the state `s₀`, over `X`, for `n`
  processes, is linearizable and wait-free.

## Runs

A configuration is the base state and each process's status: idle with its memory, or busy with
its working state. The scheduler makes a choice (`Choice`): call an idle process with a target
operation, or move a process. A moved busy process calls its next base operation (and waits,
changing nothing, if that operation cannot fire), or returns; a moved idle process does nothing.

## Tools

* `linearizable_of_simulation`: to prove an implementation linearizable, relate each of its
  configurations to one of the atomic implementation, so that each step is matched by steps of the
  atomic implementation showing the same events.
* `returns_of_measure`: a process returns if a measure of the configuration does not grow while it
  is busy and drops at each of its own moves.

## Controls

* `Controls.atomic_linearizable`, `Controls.atomic_waitFree`: the atomic implementation is
  linearizable and wait-free (positive).
* `Controls.unwritten_read_not_linearizable`: a register that was never written cannot be read as
  `true` (negative).
* `Controls.blind_not_linearizable`: a front-end that answers `true` to a read without looking is
  not linearizable (negative).
* `Controls.spin_linearizable`, `Controls.spin_not_waitFree`: a front-end that calls base
  operations forever is linearizable (it never answers anything wrong) and not wait-free.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

/-- A call of a target operation, or its return. -/
inductive Event (n : ℕ) (Op Res : Type) where
  | invoke (i : Fin n) (op : Op)
  | respond (i : Fin n) (r : Res)

/-- What a front-end does next within an operation: call a base operation, or return an answer
together with the memory to keep. -/
inductive Move (Op Res Mem : Type) where
  | call (a : Op)
  | ret (r : Res) (m : Mem)

/-- An implementation of the target `Y` over the base `X`, for `n` processes. -/
structure Implementation (X : ObjectType) (Y : DetObject) (n : ℕ) where
  /-- The base objects' initial state. -/
  init : X.State
  /-- What a process keeps between operations. -/
  Mem : Type
  /-- A process's working state during an operation. -/
  Work : Type
  /-- Each process's memory at the start. -/
  mem₀ : Fin n → Mem
  /-- Start an operation. -/
  begin : Fin n → Mem → Y.Op → Work
  /-- What to do next. -/
  move : Fin n → Work → Move X.Op Y.Res Mem
  /-- The working state after a base operation's answer. -/
  next : Fin n → Work → X.Res → Work

/-- What the scheduler does: call an idle process with an operation, or move a process. -/
inductive Choice (n : ℕ) (Op : Type) where
  | invoke (i : Fin n) (op : Op)
  | move (i : Fin n)

/-- The process a choice concerns. -/
def Choice.who {n : ℕ} {Op : Type} : Choice n Op → Fin n
  | .invoke i _ => i
  | .move i => i

namespace Implementation

variable {X : ObjectType} {Y : DetObject} {n : ℕ} (I : Implementation X Y n)

/-- A process is idle with its memory, or busy with its working state. -/
inductive Status where
  | idle (m : I.Mem)
  | busy (w : I.Work)

/-- A configuration: the base state and every process's status. -/
@[ext]
structure Config where
  obj : X.State
  loc : Fin n → I.Status

/-- Every process idle with its initial memory, the base at its initial state. -/
def initial : I.Config := ⟨I.init, fun i => .idle (I.mem₀ i)⟩

/-- One step, with the event it shows, if any. -/
inductive Step : I.Config → Choice n Y.Op → Option (Event n Y.Op Y.Res) → I.Config → Prop
  | invoke {C : I.Config} {i : Fin n} {m : I.Mem} (op : Y.Op) :
      C.loc i = .idle m →
      Step C (.invoke i op) (some (.invoke i op))
        ⟨C.obj, Function.update C.loc i (.busy (I.begin i m op))⟩
  | call {C : I.Config} {i : Fin n} {w : I.Work} {a : X.Op} {s : X.State} {r : X.Res} :
      C.loc i = .busy w → I.move i w = .call a → X.Fires C.obj a s r →
      Step C (.move i) none ⟨s, Function.update C.loc i (.busy (I.next i w r))⟩
  | wait {C : I.Config} {i : Fin n} {w : I.Work} {a : X.Op} :
      C.loc i = .busy w → I.move i w = .call a → (∀ s r, ¬ X.Fires C.obj a s r) →
      Step C (.move i) none C
  | ret {C : I.Config} {i : Fin n} {w : I.Work} {r : Y.Res} {m : I.Mem} :
      C.loc i = .busy w → I.move i w = .ret r m →
      Step C (.move i) (some (.respond i r)) ⟨C.obj, Function.update C.loc i (.idle m)⟩
  | rest {C : I.Config} {i : Fin n} {m : I.Mem} :
      C.loc i = .idle m → Step C (.move i) none C

/-- A run: the steps of a finite list of choices, and the history they show. -/
def Run : I.Config → List (Choice n Y.Op) → List (Event n Y.Op Y.Res) → I.Config → Prop
  | C, [], h, D => h = [] ∧ D = C
  | C, c :: cs, h, D => ∃ e E h', I.Step C c e E ∧ Run E cs h' D ∧ h = e.toList ++ h'

/-- A history the implementation can show. -/
def Trace (h : List (Event n Y.Op Y.Res)) : Prop := ∃ cs D, I.Run I.initial cs h D

/-- An execution: an infinite list of choices and the configurations they lead to. -/
def Execution (cs : ℕ → Choice n Y.Op) (c : ℕ → I.Config) : Prop :=
  ∀ m, ∃ e, I.Step (c m) (cs m) e (c (m + 1))

/-- Process `i` has an operation in progress. -/
def Busy (C : I.Config) (i : Fin n) : Prop := ∃ w, C.loc i = .busy w

/-- **Wait-free**: in every execution from the start, a process with an operation in progress
that is moved infinitely often returns. -/
def WaitFree : Prop :=
  ∀ cs c, c 0 = I.initial → I.Execution cs c → ∀ i m, I.Busy (c m) i →
    (∀ N, ∃ k, N ≤ k ∧ cs k = .move i) → ∃ k, m ≤ k ∧ ¬ I.Busy (c k) i

end Implementation

/-- The working state of the atomic implementation: the operation to apply, or its answer. -/
inductive AtomicWork (Op Res : Type) where
  | pending (op : Op)
  | done (r : Res)

/-- **The atomic implementation**: the target itself, each operation applied in one base step. -/
def atomic (Y : DetObject) (s₀ : Y.State) (n : ℕ) : Implementation Y.toObject Y n where
  init := s₀
  Mem := Unit
  Work := AtomicWork Y.Op Y.Res
  mem₀ _ := ()
  begin _ _ op := .pending op
  move _ w := match w with
    | .pending op => .call op
    | .done r => .ret r ()
  next _ w r := match w with
    | .pending _ => .done r
    | .done r' => .done r'

/-- **A linearizable history** of `Y` from `s₀`: one the atomic implementation can show. -/
def LinearizableHistory (Y : DetObject) (s₀ : Y.State) {n : ℕ}
    (h : List (Event n Y.Op Y.Res)) : Prop :=
  (atomic Y s₀ n).Trace h

/-- **A linearizable implementation**: every history it shows is a linearizable history of `Y`
from `s₀`. -/
def Implementation.Linearizable {X : ObjectType} {Y : DetObject} {n : ℕ}
    (I : Implementation X Y n) (s₀ : Y.State) : Prop :=
  ∀ h, I.Trace h → LinearizableHistory Y s₀ h

/-- **`X` implements `Y`** from `s₀` for `n` processes: some implementation over `X` is
linearizable and wait-free. -/
def Implements (X : ObjectType) (Y : DetObject) (s₀ : Y.State) (n : ℕ) : Prop :=
  ∃ I : Implementation X Y n, I.Linearizable s₀ ∧ I.WaitFree

namespace Implementation

variable {X X' : ObjectType} {Y : DetObject} {n : ℕ}

/-! ### Runs -/

section Runs

variable {J : Implementation X' Y n}

theorem run_nil (C : J.Config) : J.Run C [] [] C := ⟨rfl, rfl⟩

theorem run_single {C D : J.Config} {c : Choice n Y.Op} {e : Option (Event n Y.Op Y.Res)}
    (step : J.Step C c e D) : J.Run C [c] e.toList D :=
  ⟨e, D, [], step, ⟨rfl, rfl⟩, by simp⟩

theorem run_append {C D E : J.Config} {cs cs' : List (Choice n Y.Op)}
    {h h' : List (Event n Y.Op Y.Res)} (first : J.Run C cs h D) (second : J.Run D cs' h' E) :
    J.Run C (cs ++ cs') (h ++ h') E := by
  induction cs generalizing C h with
  | nil => obtain ⟨rfl, rfl⟩ := first; simpa using second
  | cons c cs ih =>
      obtain ⟨e, F, h₁, step, rest, rfl⟩ := first
      exact ⟨e, F, h₁ ++ h', step, ih rest, by simp⟩

/-- A step changes only the status of the process it concerns. -/
theorem Step.loc_of_ne {C D : J.Config} {c : Choice n Y.Op} {e : Option (Event n Y.Op Y.Res)}
    (step : J.Step C c e D) {j : Fin n} (ne : j ≠ c.who) : D.loc j = C.loc j := by
  cases step with
  | invoke op _ => exact Function.update_of_ne ne _ _
  | call _ _ _ => exact Function.update_of_ne ne _ _
  | wait _ _ _ => rfl
  | ret _ _ => exact Function.update_of_ne ne _ _
  | rest _ => rfl

/-- Only an idle process can be called. -/
theorem Step.idle_of_invoke {C D : J.Config} {i : Fin n} {op : Y.Op}
    {e : Option (Event n Y.Op Y.Res)} (step : J.Step C (.invoke i op) e D) :
    ∃ m, C.loc i = .idle m := by
  cases step with
  | invoke op h => exact ⟨_, h⟩

end Runs

/-! ### Linearizability by simulation -/

section Simulation

variable {I : Implementation X Y n} {J : Implementation X' Y n}

/-- **Histories by simulation**: if each step of `I` from related configurations is matched by a
run of `J` showing the same events, every history of `I` is one of `J`. -/
theorem traces_of_simulation (R : I.Config → J.Config → Prop) (init : R I.initial J.initial)
    (step : ∀ C D c e C', R C D → I.Step C c e C' → ∃ cs D', J.Run D cs e.toList D' ∧ R C' D') :
    ∀ h, I.Trace h → J.Trace h := by
  rintro h ⟨cs, E, run⟩
  suffices key : ∀ C D h E, R C D → I.Run C cs h E → ∃ cs' D', J.Run D cs' h D' by
    obtain ⟨cs', D', run'⟩ := key _ _ _ _ init run
    exact ⟨cs', D', run'⟩
  clear run
  induction cs with
  | nil => rintro C D h E rel ⟨rfl, rfl⟩; exact ⟨[], D, run_nil D⟩
  | cons c cs ih =>
      rintro C D h E rel ⟨e, F, h', step', rest, rfl⟩
      obtain ⟨cs₁, D₁, run₁, rel₁⟩ := step C D c e F rel step'
      obtain ⟨cs₂, D₂, run₂⟩ := ih F D₁ h' E rel₁ rest
      exact ⟨cs₁ ++ cs₂, D₂, run_append run₁ run₂⟩

/-- **Linearizability by simulation** of the atomic implementation. -/
theorem linearizable_of_simulation {s₀ : Y.State}
    (R : I.Config → (atomic Y s₀ n).Config → Prop) (init : R I.initial (atomic Y s₀ n).initial)
    (step : ∀ C D c e C', R C D → I.Step C c e C' →
      ∃ cs D', (atomic Y s₀ n).Run D cs e.toList D' ∧ R C' D') :
    I.Linearizable s₀ :=
  traces_of_simulation R init step

end Simulation

/-! ### Returning by a measure -/

section Measure

variable {I : Implementation X Y n}

/-- **A process returns** if, from some time on and while it stays busy, a property `P` of the
configuration is kept, a measure never grows, and each of its own moves makes the measure drop. -/
theorem returns_of_measure {cs : ℕ → Choice n Y.Op} {c : ℕ → I.Config} (exec : I.Execution cs c)
    {i : Fin n} {m : ℕ} (P : I.Config → Prop) (μ : I.Config → ℕ) (start : P (c m))
    (keep : ∀ C ch e D, P C → I.Step C ch e D → I.Busy D i → P D)
    (mono : ∀ C ch e D, P C → I.Step C ch e D → I.Busy D i → μ D ≤ μ C)
    (drops : ∀ C e D, P C → I.Step C (.move i) e D → I.Busy D i → μ D < μ C)
    (often : ∀ N, ∃ k, N ≤ k ∧ cs k = .move i) : ∃ k, m ≤ k ∧ ¬ I.Busy (c k) i := by
  by_contra never
  have busy : ∀ k, m ≤ k → I.Busy (c k) i := fun k hk => by
    by_contra h
    exact never ⟨k, hk, h⟩
  have holds : ∀ d, P (c (m + d)) := by
    intro d
    induction d with
    | zero => exact start
    | succ d ih =>
        obtain ⟨e, step⟩ := exec (m + d)
        exact keep _ _ _ _ ih step (busy _ (by omega))
  have stays : ∀ d d', μ (c (m + d + d')) ≤ μ (c (m + d)) := by
    intro d d'
    induction d' with
    | zero => exact le_rfl
    | succ d' ih =>
        obtain ⟨e, step⟩ := exec (m + d + d')
        have := mono _ _ _ _ (by simpa [add_assoc] using holds (d + d')) step
          (busy _ (by omega))
        exact this.trans ih
  have descends : ∀ K, ∃ d, μ (c (m + d)) + K ≤ μ (c m) := by
    intro K
    induction K with
    | zero => exact ⟨0, le_rfl⟩
    | succ K ih =>
        obtain ⟨d, hd⟩ := ih
        obtain ⟨k, hk, moved⟩ := often (m + d)
        obtain ⟨e, step⟩ := exec k
        rw [moved] at step
        obtain ⟨d', rfl⟩ : ∃ d', k = m + d + d' := ⟨k - (m + d), by omega⟩
        have fall := drops _ _ _ (by simpa [add_assoc] using holds (d + d')) step
          (busy _ (by omega))
        have kept := stays d d'
        exact ⟨d + d' + 1, by
          have : m + (d + d' + 1) = m + d + d' + 1 := by omega
          rw [this]
          omega⟩
  obtain ⟨d, hd⟩ := descends (μ (c m) + 1)
  omega

end Measure

end Implementation

/-! ## Controls -/

namespace Controls

open Implementation

variable {Y : DetObject} {n : ℕ}

/-- **Positive control**: the atomic implementation is linearizable. -/
theorem atomic_linearizable (s₀ : Y.State) : (atomic Y s₀ n).Linearizable s₀ :=
  fun _ h => h

theorem atomic_begin {s₀ : Y.State} (i : Fin n) (m : Unit) (op : Y.Op) :
    (atomic Y s₀ n).begin i m op = .pending op := rfl

theorem atomic_next_pending {s₀ : Y.State} (i : Fin n) (op : Y.Op) (r : Y.Res) :
    (atomic Y s₀ n).next i (.pending op) r = .done r := rfl

theorem atomic_move_pending {s₀ : Y.State} (i : Fin n) (op : Y.Op) :
    (atomic Y s₀ n).move i (.pending op) = .call op := rfl

theorem atomic_move_done {s₀ : Y.State} (i : Fin n) (r : Y.Res) :
    (atomic Y s₀ n).move i (.done r) = .ret r () := rfl

/-- How far a process of the atomic implementation is from returning. -/
def atomicRank {s₀ : Y.State} : (atomic Y s₀ n).Status → ℕ
  | .idle _ => 0
  | .busy (.pending _) => 2
  | .busy (.done _) => 1

/-- **Positive control**: the atomic implementation is wait-free. -/
theorem atomic_waitFree (s₀ : Y.State) : (atomic Y s₀ n).WaitFree := by
  intro cs c _ exec i m busy often
  refine returns_of_measure exec (fun C => (atomic Y s₀ n).Busy C i)
    (fun C => atomicRank (C.loc i)) busy (fun _ _ _ _ _ _ h => h) ?_ ?_ often
  · intro C ch e D busyC step busyD
    by_cases who : i = ch.who
    · cases step with
      | @invoke j m' op h =>
          simp only [Choice.who] at who
          subst who
          obtain ⟨w, hw⟩ := busyC
          rw [h] at hw; cases hw
      | @call j w a s r h hm hf =>
          simp only [Choice.who] at who
          subst who
          rw [h]
          cases w with
          | pending op => simp [atomic_next_pending, atomicRank]
          | done r' => rw [atomic_move_done] at hm; cases hm
      | wait _ _ _ => exact le_rfl
      | @ret j w r m' h hm =>
          simp only [Choice.who] at who
          subst who
          simp [atomicRank]
      | rest _ => exact le_rfl
    · rw [step.loc_of_ne who]
  · intro C e D busyC step busyD
    cases step with
    | @call _ w a s r h hm hf =>
        rw [h]
        cases w with
        | pending op => simp [atomic_next_pending, atomicRank]
        | done r' => rw [atomic_move_done] at hm; cases hm
    | @wait _ w a h hm never =>
        cases w with
        | pending op =>
            rw [atomic_move_pending] at hm
            cases hm
            exact absurd rfl (never _ _)
        | done r' => rw [atomic_move_done] at hm; cases hm
    | @ret _ w r m' h hm =>
        obtain ⟨w', hw'⟩ := busyD
        simp at hw'
    | @rest _ m' h =>
        obtain ⟨w', hw'⟩ := busyC
        rw [h] at hw'; cases hw'

/-- The register of the controls: one register holding a boolean. -/
abbrev boolRegister : DetObject := registers Unit Bool

/-- A status of the atomic register from `false` that reads only. -/
def ReadsFalse {k : ℕ} (st : (atomic boolRegister (fun _ => false) k).Status) : Prop :=
  st = .idle () ∨ st = .busy (.pending (.read ())) ∨ st = .busy (.done (some false))

/-- In a run of the atomic register from `false` that reads only, every read answers `false`. -/
theorem atomic_reads_false {C D : (atomic boolRegister (fun _ => false) n).Config}
    {cs : List (Choice n boolRegister.Op)} {h : List (Event n boolRegister.Op boolRegister.Res)}
    (run : (atomic boolRegister (fun _ => false) n).Run C cs h D)
    (obj : C.obj = fun _ => false) (locs : ∀ i, ReadsFalse (C.loc i))
    (reads : ∀ i op, Event.invoke i op ∈ h → op = .read ()) :
    ∀ i r, Event.respond i r ∈ h → r = some false := by
  induction cs generalizing C h with
  | nil => obtain ⟨rfl, -⟩ := run; simp
  | cons ch cs ih =>
      obtain ⟨e, E, h', step, rest, rfl⟩ := run
      have readsRest : ∀ i op, Event.invoke i op ∈ h' → op = .read () :=
        fun i op mem => reads i op (List.mem_append_right _ mem)
      have update : ∀ (j : Fin n) (st : (atomic boolRegister (fun _ => false) n).Status),
          ReadsFalse st → ∀ k, ReadsFalse (Function.update C.loc j st k) := by
        intro j st hst k
        by_cases same : k = j
        · subst same; simpa using hst
        · simp only [Function.update_of_ne same]; exact locs k
      cases step with
      | @invoke j m op hl =>
          have isRead : op = .read () := reads j op (by simp)
          subst isRead
          intro i r mem
          simp only [Option.toList_some, List.cons_append, List.nil_append, List.mem_cons,
            reduceCtorEq, false_or] at mem
          exact ih rest obj (update j _ (Or.inr (Or.inl rfl))) readsRest i r mem
      | @call j w a s r hl hm hf =>
          intro i r' mem
          simp only [Option.toList_none, List.nil_append] at mem
          rcases locs j with hj | hj | hj <;> rw [hl] at hj <;> cases hj
          · rw [atomic_move_pending] at hm
            cases hm
            have hf' : boolRegister.apply C.obj (.read ()) = (s, r) := hf
            rw [obj] at hf'
            simp only [Prod.mk.injEq] at hf'
            obtain ⟨rfl, rfl⟩ := hf'
            exact ih rest rfl (update j _ (Or.inr (Or.inr rfl))) readsRest i r' mem
          · rw [atomic_move_done] at hm; cases hm
      | wait _ _ _ =>
          intro i r mem
          simp only [Option.toList_none, List.nil_append] at mem
          exact ih rest obj locs readsRest i r mem
      | @ret j w r₀ m hl hm =>
          intro i r mem
          have answered : r₀ = some false := by
            rcases locs j with hj | hj | hj <;> rw [hl] at hj <;> cases hj
            · rw [atomic_move_pending] at hm; cases hm
            · rw [atomic_move_done] at hm; cases hm; rfl
          simp only [Option.toList_some, List.cons_append, List.nil_append,
            List.mem_cons, Event.respond.injEq] at mem
          rcases mem with ⟨rfl, rfl⟩ | mem
          · exact answered
          · exact ih rest obj (update j _ (Or.inl rfl)) readsRest i r mem
      | rest _ =>
          intro i r mem
          simp only [Option.toList_none, List.nil_append] at mem
          exact ih rest obj locs readsRest i r mem

/-- **Negative control**: a register that was never written, read as `true`, is not a linearizable
history. -/
theorem unwritten_read_not_linearizable :
    ¬ LinearizableHistory boolRegister (fun _ => false)
      [Event.invoke (0 : Fin 1) (.read ()), Event.respond 0 (some true)] := by
  rintro ⟨cs, D, run⟩
  have := atomic_reads_false run rfl (fun _ => Or.inl rfl)
    (fun i op mem => by simp at mem; exact mem.2) 0 (some true) (by simp)
  simp at this

/-- A front-end that answers `true` at once, without looking at any base object. -/
def blind (X : ObjectType) (s : X.State) : Implementation X boolRegister 1 where
  init := s
  Mem := Unit
  Work := Unit
  mem₀ _ := ()
  begin _ _ _ := ()
  move _ _ := .ret (some true) ()
  next _ _ _ := ()

/-- **Negative control**: the blind front-end is not linearizable. -/
theorem blind_not_linearizable (X : ObjectType) (s : X.State) :
    ¬ (blind X s).Linearizable (fun _ => false) := by
  intro lin
  have first := Step.invoke (I := blind X s) (C := (blind X s).initial) (i := 0) (m := ())
    (RegOp.read () : boolRegister.Op) rfl
  have second := Step.ret (I := blind X s)
    (C := ⟨(blind X s).initial.obj, Function.update (blind X s).initial.loc 0
      (.busy ((blind X s).begin 0 () (RegOp.read () : boolRegister.Op)))⟩)
    (i := 0) (w := ()) (r := some true) (m := ()) (by simp [blind]) rfl
  exact unwritten_read_not_linearizable
    (lin _ ⟨[.invoke 0 (RegOp.read () : boolRegister.Op), .move 0], _,
      ⟨_, _, _, first, ⟨_, _, _, second, ⟨rfl, rfl⟩, rfl⟩, rfl⟩⟩)

/-- A front-end that keeps reading a register forever. -/
def spin : Implementation boolRegister.toObject boolRegister 1 where
  init := fun _ => false
  Mem := Unit
  Work := Unit
  mem₀ _ := ()
  begin _ _ _ := ()
  move _ _ := .call (.read ())
  next _ _ _ := ()

/-- **Positive control**: the spinning front-end is linearizable: it never answers. -/
theorem spin_linearizable : spin.Linearizable (fun _ => false) := by
  refine linearizable_of_simulation
    (fun C D => ∀ i, (C.loc i = .idle () ∧ D.loc i = .idle ()) ∨
      (C.loc i = .busy () ∧ ∃ op, D.loc i = .busy (.pending op)))
    (fun _ => Or.inl ⟨rfl, rfl⟩) ?_
  intro C D ch e C' rel step
  cases step with
  | @invoke j m op h =>
      refine ⟨[.invoke j op], ⟨D.obj, Function.update D.loc j (.busy (.pending op))⟩,
        run_single (Step.invoke (m := ()) op ?_), fun k => ?_⟩
      · rcases rel j with ⟨-, hD⟩ | ⟨hC, -⟩
        · exact hD
        · rw [h] at hC; cases hC
      · by_cases same : k = j
        · subst same; exact Or.inr ⟨by simp [spin], op, by simp⟩
        · simp only [Function.update_of_ne same]; exact rel k
  | @call j w a s r h hm hf =>
      refine ⟨[], D, run_nil D, fun k => ?_⟩
      by_cases same : k = j
      · subst same
        rcases rel k with ⟨hC, -⟩ | ⟨-, op, hD⟩
        · rw [h] at hC; cases hC
        · exact Or.inr ⟨by simp [spin], op, hD⟩
      · simp only [Function.update_of_ne same]; exact rel k
  | wait _ _ _ => exact ⟨[], D, run_nil D, rel⟩
  | ret h hm => simp [spin] at hm
  | rest _ => exact ⟨[], D, run_nil D, rel⟩

/-- **Negative control**: the spinning front-end is not wait-free. -/
theorem spin_not_waitFree : ¬ spin.WaitFree := by
  intro wf
  let busyConfig : spin.Config := ⟨fun _ => false, fun _ => .busy ()⟩
  let cs : ℕ → Choice 1 boolRegister.Op := fun k =>
    if k = 0 then .invoke 0 (RegOp.read () : boolRegister.Op) else .move 0
  let c : ℕ → spin.Config := fun k => if k = 0 then spin.initial else busyConfig
  have first : spin.Step spin.initial (.invoke 0 (RegOp.read () : boolRegister.Op))
      (some (.invoke 0 (RegOp.read () : boolRegister.Op))) busyConfig := by
    have := Step.invoke (I := spin) (C := spin.initial) (i := 0) (m := ())
      (RegOp.read () : boolRegister.Op) rfl
    convert this using 1
    ext i
    · rfl
    · fin_cases i; rfl
  have later : spin.Step busyConfig (.move 0) none busyConfig := by
    have := Step.call (I := spin) (C := busyConfig) (i := 0) (w := ())
      (a := (RegOp.read () : boolRegister.Op)) (s := fun _ => false) (r := some false) rfl rfl rfl
    convert this using 1
    ext i
    · rfl
    · fin_cases i; rfl
  have exec : spin.Execution cs c := by
    intro k
    rcases k with _ | k
    · exact ⟨_, by simpa [cs, c] using first⟩
    · exact ⟨none, by simpa [cs, c] using later⟩
  obtain ⟨k, hk, idle⟩ := wf cs c (by simp [c]) exec 0 1 ⟨(), by simp [c, busyConfig]⟩
    (fun N => ⟨N + 1, by omega, by simp [cs]⟩)
  exact idle ⟨(), by simp [c, busyConfig, if_neg (by omega : k ≠ 0)]⟩

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
