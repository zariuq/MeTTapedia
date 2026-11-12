import Mettapedia.Machines.QueryState

/-!
# Immediate, read-your-writes and declarative effect profiles

All three profiles execute the existing adaptive query syntax. The immediate
service changes its actual world at every effect. The independently implemented
buffered service retains effect descriptions and reads either its latest pending
writes or its original pre-state. A separate publication applies that prepared
payload once when the result is admitted. Atomic publication alone therefore
does not select the internal read policy.

Effects here are store updates and recordable events. An event description is
not an already executed terminal/network operation. Irrevocable host effects
need an explicit preparation-effect channel or a post-publication phase; these
models do not forbid them or pretend they can be rolled back. Primitive store
publication, dependency admission, concurrency and packet lifetime remain the
separate contracts of PreparedStoreProtocol and its consumers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetEffectProfiles

open ReadOnlyQuery (Program)

variable {Key Value Event Answer Error : Type}

structure World (Key Value Event : Type) where
  store : Key → Value
  events : List Event

inductive Effect (Key Value Event : Type) where
  | put (key : Key) (value : Value)
  | record (event : Event)
  deriving DecidableEq, Repr

inductive Request (Key Value Event : Type) where
  | load (key : Key)
  | perform (effect : Effect Key Value Event)
  deriving DecidableEq, Repr

inductive Result (Answer Error : Type) where
  | answer (value : Answer)
  | refused
  | error (reason : Error)
  deriving DecidableEq, Repr

abbrev Code (Key Value Event Answer Error : Type) :=
  Program (Request Key Value Event) (Option Value) (Result Answer Error)

variable [DecidableEq Key]

def applyEffect (world : World Key Value Event) : Effect Key Value Event → World Key Value Event
  | .put key value => { world with store := Function.update world.store key value }
  | .record event => { world with events := world.events ++ [event] }

def applyAll (effects : List (Effect Key Value Event)) (world : World Key Value Event) :
    World Key Value Event := effects.foldl applyEffect world

theorem applyAll_append (left right : List (Effect Key Value Event)) (world : World Key Value Event) :
    applyAll (left ++ right) world = applyAll right (applyAll left world) := by
  simp [applyAll, List.foldl_append]

def immediateService (world : World Key Value Event) : Request Key Value Event →
    Option Value × World Key Value Event
  | .load key => (some (world.store key), world)
  | .perform effect => (none, applyEffect world effect)

def ambient (code : Code Key Value Event Answer Error) (world : World Key Value Event) :=
  QueryState.run immediateService code world

structure Transaction (Key Value Event : Type) where
  base : World Key Value Event
  pendingRev : List (Effect Key Value Event)

def begin (world : World Key Value Event) : Transaction Key Value Event := ⟨world, []⟩

def lookup (base : Key → Value) : List (Effect Key Value Event) → Key → Value
  | [], key => base key
  | .put written value :: later, key => if key = written then value else lookup base later key
  | .record _ :: later, key => lookup base later key

def materialize (state : Transaction Key Value Event) : World Key Value Event :=
  applyAll state.pendingRev.reverse state.base

inductive ReadPolicy where
  | overlay
  | preState
  deriving DecidableEq, Repr

def readView (policy : ReadPolicy) (state : Transaction Key Value Event) (key : Key) : Value :=
  match policy with
  | .overlay => lookup state.base.store state.pendingRev key
  | .preState => state.base.store key

def preparedService (policy : ReadPolicy) (state : Transaction Key Value Event) :
    Request Key Value Event → Option Value × Transaction Key Value Event
  | .load key => (some (readView policy state key), state)
  | .perform effect => (none, { state with pendingRev := effect :: state.pendingRev })

def prepared (policy : ReadPolicy) (code : Code Key Value Event Answer Error)
    (world : World Key Value Event) := QueryState.run (preparedService policy) code (begin world)

theorem prepared_keeps_base (policy : ReadPolicy) (code : Code Key Value Event Answer Error)
    (world : World Key Value Event) : (prepared policy code world).state.base = world := by
  apply QueryState.state_invariant (preparedService policy) (fun state => state.base = world)
  · intro state same request
    cases request <;> exact same
  · rfl

theorem lookup_applied (base : World Key Value Event) (pending : List (Effect Key Value Event))
    (key : Key) : (applyAll pending.reverse base).store key = lookup base.store pending key := by
  induction pending with
  | nil => rfl
  | cons effect later ih =>
      rw [List.reverse_cons, applyAll_append]
      cases effect with
      | put written value =>
          simp only [applyAll, List.foldl_cons, List.foldl_nil, applyEffect, lookup]
          change Function.update (applyAll later.reverse base).store written value key =
            if key = written then value else lookup base.store later key
          by_cases same : key = written
          · subst key; simp
          · rw [Function.update_of_ne same, if_neg same]
            exact ih
      | record event =>
          simpa only [applyAll, List.foldl_cons, List.foldl_nil, applyEffect, lookup] using ih

theorem materialize_push (state : Transaction Key Value Event) (effect : Effect Key Value Event) :
    materialize { state with pendingRev := effect :: state.pendingRev } =
      applyEffect (materialize state) effect := by
  simp [materialize, List.reverse_cons, applyAll]

theorem overlay_service_refines (state : Transaction Key Value Event) (request : Request Key Value Event) :
    immediateService (materialize state) request =
      ((preparedService .overlay state request).1, materialize (preparedService .overlay state request).2) := by
  cases request with
  | load key => simp [immediateService, preparedService, readView, materialize, lookup_applied]
  | perform effect => simp [immediateService, preparedService, materialize_push]

/-- The independently implemented buffered lookup earns equivalence with the
actual immediate service on its private overlay, for every adaptive program.
Public rollback on refusal is a subsequent, different observation. -/
theorem overlay_simulation (code : Code Key Value Event Answer Error)
    (state : Transaction Key Value Event) :
    let delayed := QueryState.run (preparedService .overlay) code state
    ambient code (materialize state) =
      ⟨delayed.answer, materialize delayed.state, delayed.reads⟩ := by
  induction code generalizing state with
  | pure answer => rfl
  | read request more ih =>
      have response := overlay_service_refines state request
      cases found : preparedService .overlay state request with
      | mk reply nextState =>
          rw [found] at response
          simp only [ambient, QueryState.run, response, found]
          exact congrArg (fun result =>
            (⟨result.answer, result.state, (request, reply) :: result.reads⟩ :
              QueryState.Observation _ _ _ _)) (ih reply nextState)

structure Receipt (Key Value Event Answer : Type) where
  answer : Answer
  effects : List (Effect Key Value Event)
  deriving DecidableEq, Repr

structure Publication (Key Value Event Answer Error : Type) where
  result : Result Answer Error
  world : World Key Value Event
  published : Bool
  receipt : Option (Receipt Key Value Event Answer)

/-- Publication applies the retained effects to the admitted current world;
it does not rerun code or overwrite that world with an old private snapshot.
What makes admission valid under other writers is a separate dependency law. -/
def publish (recording allowed : Bool) (current : World Key Value Event)
    (preparation : QueryState.Observation (Request Key Value Event) (Option Value)
      (Result Answer Error) (Transaction Key Value Event)) :
    Publication Key Value Event Answer Error :=
  match preparation.answer with
  | .answer value =>
      if allowed then
        ⟨.answer value, applyAll preparation.state.pendingRev.reverse current, true,
          if recording then some ⟨value, preparation.state.pendingRev.reverse⟩ else none⟩
      else ⟨.refused, current, false, none⟩
  | .refused => ⟨.refused, current, false, none⟩
  | .error reason => ⟨.error reason, current, false, none⟩

theorem admission_refusal_preserves_public (recording : Bool) (current : World Key Value Event)
    (preparation : QueryState.Observation (Request Key Value Event) (Option Value)
      (Result Answer Error) (Transaction Key Value Event)) :
    (publish recording false current preparation).world = current ∧
      (publish recording false current preparation).published = false ∧
      (publish recording false current preparation).receipt = none := by
  cases answer : preparation.answer <;> simp [publish, answer]

theorem code_refusal_preserves_public (recording allowed : Bool) (current : World Key Value Event)
    (preparation : QueryState.Observation (Request Key Value Event) (Option Value)
      (Result Answer Error) (Transaction Key Value Event))
    (refused : preparation.answer = .refused) :
    (publish recording allowed current preparation).world = current ∧
      (publish recording allowed current preparation).published = false ∧
      (publish recording allowed current preparation).receipt = none := by
  simp [publish, refused]

theorem admitted_publication (recording : Bool) (current : World Key Value Event)
    (preparation : QueryState.Observation (Request Key Value Event) (Option Value)
      (Result Answer Error) (Transaction Key Value Event)) (value : Answer)
    (answered : preparation.answer = .answer value) :
    (publish recording true current preparation).result = .answer value ∧
      (publish recording true current preparation).world =
        applyAll preparation.state.pendingRev.reverse current ∧
      (publish recording true current preparation).published = true := by
  simp [publish, answered]

theorem receipt_exact (allowed : Bool) (current : World Key Value Event)
    (preparation : QueryState.Observation (Request Key Value Event) (Option Value)
      (Result Answer Error) (Transaction Key Value Event)) (receipt : Receipt Key Value Event Answer)
    (recorded : (publish true allowed current preparation).receipt = some receipt) :
    preparation.answer = .answer receipt.answer ∧
      receipt.effects = preparation.state.pendingRev.reverse ∧
      (publish true allowed current preparation).published = true := by
  cases answer : preparation.answer with
  | refused => simp [publish, answer] at recorded
  | error reason => simp [publish, answer] at recorded
  | answer value =>
      cases allowed with
      | false => simp [publish, answer] at recorded
      | true =>
          simp [publish, answer] at recorded
          subst receipt
          simp [publish, answer]

theorem no_recording_no_receipt (allowed : Bool) (current : World Key Value Event)
    (preparation : QueryState.Observation (Request Key Value Event) (Option Value)
      (Result Answer Error) (Transaction Key Value Event)) :
    (publish false allowed current preparation).receipt = none := by
  cases answer : preparation.answer <;> cases allowed <;> simp [publish, answer]

theorem overlay_read_after_write (base : World Key Value Event)
    (pending : List (Effect Key Value Event)) (key : Key) (value : Value) :
    (preparedService .overlay ⟨base, .put key value :: pending⟩ (.load key)).1 = some value := by
  simp [preparedService, readView, lookup]

theorem snapshot_reads_original (base : World Key Value Event)
    (pending : List (Effect Key Value Event)) (key : Key) :
    (preparedService .preState ⟨base, pending⟩ (.load key)).1 = some (base.store key) := rfl

/-- On admitted completion, buffering with read-your-writes preserves the
answer and final effects of immediate execution. Refused prefixes remain a
separate observation and need not agree. -/
theorem admitted_overlay_agrees_ambient (recording : Bool) (code : Code Key Value Event Answer Error)
    (world : World Key Value Event) (value : Answer)
    (answered : (ambient code world).answer = .answer value) :
    (publish recording true world (prepared .overlay code world)).result = .answer value ∧
      (publish recording true world (prepared .overlay code world)).world = (ambient code world).state := by
  have simulation := overlay_simulation code (begin world)
  change ambient code world =
    (⟨(prepared .overlay code world).answer,
      materialize (prepared .overlay code world).state,
      (prepared .overlay code world).reads⟩ : QueryState.Observation _ _ _ _) at simulation
  have sameAnswer := congrArg (fun result => result.answer) simulation
  have sameWorld := congrArg (fun result => result.state) simulation
  have preparedAnswer : (prepared .overlay code world).answer = .answer value :=
    sameAnswer.symm.trans answered
  have stableBase := prepared_keeps_base .overlay code world
  simp only [publish, preparedAnswer, ↓reduceIte]
  simp only [true_and]
  rw [sameWorld]
  simp only [materialize, stableBase]

def writeRead (key : Key) (value : Value) : Code Key Value Event (Option Value) Error :=
  .read (.perform (.put key value)) fun _ =>
    .read (.load key) fun read => .pure (.answer read)

def writeRefuse (key : Key) (value : Value) : Code Key Value Event Answer Error :=
  .read (.perform (.put key value)) fun _ => .pure .refused

theorem ambient_late_refusal (key : Key) (value : Value) (world : World Key Value Event) :
    ambient (writeRefuse (Answer := Answer) (Error := Error) key value) world =
      ⟨.refused, applyEffect world (.put key value), [(.perform (.put key value), none)]⟩ := rfl

theorem overlay_write_read (key : Key) (value : Value) (world : World Key Value Event) :
    (prepared .overlay (writeRead (Error := Error) key value) world).answer = .answer (some value) := by
  simp [prepared, writeRead, preparedService, readView, lookup, begin, QueryState.run]

theorem declarative_write_read (key : Key) (value : Value) (world : World Key Value Event) :
    (prepared .preState (writeRead (Error := Error) key value) world).answer =
      .answer (some (world.store key)) := rfl

theorem write_read_payload (policy : ReadPolicy) (key : Key) (value : Value)
    (world : World Key Value Event) :
    (prepared policy (writeRead (Error := Error) key value) world).state.pendingRev = [.put key value] := rfl

/-- Both interpretations publish exactly one admitted payload with the same
public store effects, yet their internal read answers differ. Single atomic
publication therefore does not entail an all-pre-state read discipline. -/
theorem atomic_publication_does_not_force_snapshot_reads (key : Key) (value : Value)
    (world : World Key Value Event) (changed : value ≠ world.store key) :
    let overlay := publish false true world (prepared .overlay (writeRead (Error := Error) key value) world)
    let snapshot := publish false true world (prepared .preState (writeRead (Error := Error) key value) world)
    overlay.published = true ∧ snapshot.published = true ∧ overlay.world = snapshot.world ∧
      overlay.result ≠ snapshot.result := by
  have one := overlay_write_read (Error := Error) key value world
  have two := declarative_write_read (Error := Error) key value world
  simp only [publish, one, two, ↓reduceIte]
  simp only [write_read_payload]
  simp only [true_and]
  intro same
  exact changed (Option.some.inj (Result.answer.inj same))

end Mettapedia.Machines.Cursor.LetEffectProfiles
