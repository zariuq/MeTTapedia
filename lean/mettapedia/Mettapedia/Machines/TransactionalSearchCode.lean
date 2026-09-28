import Mettapedia.Machines.MarkedUndoLog
import Mettapedia.Machines.RegisterCode
import Mettapedia.Machines.ResourceOwnership
import Mathlib.Data.Finset.Sort

/-!
# Flat search code with logical rollback and persistent effects

The source uses immutable binding snapshots at alternatives. The compiler emits
one flat instruction list, explicit trail writes/restores, and counted guard
jumps. Alternatives are concatenated in authored order. The target has one
binding store, a newest-first undo trail, a world, and emitted observations.
`lower_exact` compares the independent interpreters: ordered occurrences and
world agree exactly, and the target restores the complete incoming store/trail.
Failed branches keep their performed effects. Values and observations are
arbitrary types, so open terms, closures and explanation-bearing answers are
not excluded by this control model.

This is a terminating *search region*, not a claim that arbitrary recursive
relations terminate. Recursive or foreign services and scheduler fairness need
the surrounding resumable protocol. This file also proves the root condition
at a suspended register-code call, including payloads retained only by undo,
and makes revision-pinned entry explicit. It does not verify C layout, pointer
lifetime, exception cleanup, compiled unification, or that a particular C
root walk implements this mathematical root family.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TransactionalSearchCode

universe u v w x y

abbrev Store (Slot : Type u) (Value : Type v) := Slot → Value

/-- The observer can retain an open term, its environment and evidence. -/
structure Semantics (Slot : Type u) (Value : Type v) (Test : Type w)
    (Effect : Type x) (World : Type y) (Observation : Type v) where
  test : Test → Store Slot Value → World → Bool
  effect : Effect → World → World
  observe : Store Slot Value → World → Observation

/-- Source evaluation uses store snapshots at `choice`. Writes bind already
computed payloads; the correctness of a unifier producing those writes is a
separate head-matching theorem. -/
inductive Region (Slot : Type u) (Value : Type v) (Test : Type w) (Effect : Type x) where
  | fail
  | answer
  | write (slot : Slot) (value : Value) (body : Region Slot Value Test Effect)
  | guard (test : Test) (body : Region Slot Value Test Effect)
  | perform (effect : Effect) (body : Region Slot Value Test Effect)
  | choice (left right : Region Slot Value Test Effect)

variable {Slot : Type u} {Value : Type v} {Test : Type w} {Effect : Type x}
variable {World : Type y} {Observation : Type v} [DecidableEq Slot]

/-- Snapshot semantics. Worlds, unlike bindings, flow from the exhausted left
branch into the right branch, including when the left branch has no answer. -/
def source (S : Semantics Slot Value Test Effect World Observation) :
    Region Slot Value Test Effect → Store Slot Value → World → List Observation × World
  | .fail, _, world => ([], world)
  | .answer, bindings, world => ([S.observe bindings world], world)
  | .write slot value body, bindings, world =>
      source S body (Function.update bindings slot value) world
  | .guard test body, bindings, world =>
      if S.test test bindings world then source S body bindings world else ([], world)
  | .perform effect body, bindings, world => source S body bindings (S.effect effect world)
  | .choice left right, bindings, world =>
      let first := source S left bindings world
      let second := source S right bindings first.2
      (first.1 ++ second.1, second.2)

/-- A flat code instruction. A failed guard skips exactly the following
`skip` instructions, including balanced trail instructions inside that body. -/
inductive Instr (Slot : Type u) (Value : Type v) (Test : Type w) (Effect : Type x) where
  | write (slot : Slot) (value : Value)
  | undo
  | guard (test : Test) (skip : Nat)
  | perform (effect : Effect)
  | answer

/-- Compilation erases source choices to concatenated code, while every write
is paired with a restore. Guard offsets are computed from compiled body size. -/
def lower : Region Slot Value Test Effect → List (Instr Slot Value Test Effect)
  | .fail => []
  | .answer => [.answer]
  | .write slot value body => .write slot value :: lower body ++ [.undo]
  | .guard test body => .guard test (lower body).length :: lower body
  | .perform effect body => .perform effect :: lower body
  | .choice left right => lower left ++ lower right

structure State (Slot : Type u) (Value : Type v) (World : Type y) (Observation : Type v) where
  bindings : Store Slot Value
  trail : List (Slot × Value)
  world : World
  emitted : List Observation
  skipping : Nat

/-- Undo one write, preserving effects and observations. An empty trail makes
malformed standalone `undo` a no-op; compiled programs are proved balanced. -/
def undo (state : State Slot Value World Observation) : State Slot Value World Observation :=
  match state.trail with
  | [] => state
  | (slot, old) :: rest =>
      { state with bindings := Function.update state.bindings slot old, trail := rest }

/-- The target has a single explicit mutable-store model. The skip counter is
an executable specification of a relative forward jump, not a runtime cost
claim about iterating over skipped instructions. -/
def step (S : Semantics Slot Value Test Effect World Observation)
    (instruction : Instr Slot Value Test Effect)
    (state : State Slot Value World Observation) : State Slot Value World Observation :=
  match state.skipping with
  | n + 1 => { state with skipping := n }
  | 0 => match instruction with
    | .write slot value =>
        { state with
          bindings := Function.update state.bindings slot value
          trail := (slot, state.bindings slot) :: state.trail }
    | .undo => undo state
    | .guard test count =>
        if S.test test state.bindings state.world then state else { state with skipping := count }
    | .perform effect => { state with world := S.effect effect state.world }
    | .answer => { state with emitted := state.emitted ++ [S.observe state.bindings state.world] }

def execute (S : Semantics Slot Value Test Effect World Observation) :
    List (Instr Slot Value Test Effect) → State Slot Value World Observation →
      State Slot Value World Observation
  | [], state => state
  | instruction :: rest, state => execute S rest (step S instruction state)

theorem execute_append (S : Semantics Slot Value Test Effect World Observation)
    (first second : List (Instr Slot Value Test Effect))
    (state : State Slot Value World Observation) :
    execute S (first ++ second) state = execute S second (execute S first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simp only [List.cons_append, execute, ih]

/-- Skipping an entire region executes none of its effects, observations or
writes. This establishes the guard jump's extent independently of the compiler. -/
theorem execute_skip (S : Semantics Slot Value Test Effect World Observation)
    (code : List (Instr Slot Value Test Effect)) (rest : Nat)
    (state : State Slot Value World Observation) :
    execute S code { state with skipping := code.length + rest } =
      { state with skipping := rest } := by
  induction code generalizing state with
  | nil => simp [execute]
  | cons instruction code ih =>
      simp only [List.length_cons, Nat.succ_add, execute, step]
      exact ih _

/-- Restore exactly the pre-write payload even when the same slot was written
before. No single-assignment condition is needed. -/
theorem undo_write (state : State Slot Value World Observation) (slot : Slot) (value : Value) :
    undo { state with
      bindings := Function.update state.bindings slot value
      trail := (slot, state.bindings slot) :: state.trail } = state := by
  simp only [undo, Function.update_idem, Function.update_eq_self]

/-- Exact compiler correctness. It includes answer order and multiplicity,
performed effects, and restoration of both the store and the outer undo log. -/
theorem lower_exact (S : Semantics Slot Value Test Effect World Observation)
    (region : Region Slot Value Test Effect) (state : State Slot Value World Observation)
    (ready : state.skipping = 0) :
    execute S (lower region) state =
      { state with
        world := (source S region state.bindings state.world).2
        emitted := state.emitted ++ (source S region state.bindings state.world).1 } := by
  induction region generalizing state with
  | fail => simp [lower, execute, source]
  | answer => simp [lower, execute, step, ready, source]
  | write slot value body ih =>
      simp only [lower, List.cons_append, execute, step, ready, execute_append]
      rw [ih _ rfl]
      simp only [undo, source, Function.update_idem, Function.update_eq_self]
  | guard test body ih =>
      simp only [lower, execute, step, ready, source]
      cases h : S.test test state.bindings state.world with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          simpa [ready] using execute_skip S (lower body) 0 state
      | true =>
          simp only [↓reduceIte]
          simpa only [ready] using ih state ready
  | perform effect body ih =>
      simp only [lower, execute, step, ready, source]
      exact ih _ rfl
  | choice left right il ir =>
      simp only [lower, execute_append]
      rw [il state ready, ir]
      · simp only [source, List.append_assoc]
      · exact ready

/-- Source and target occurrence membership coincide; the stronger equality
above also preserves repetitions, which membership by itself would forget. -/
theorem compiled_answer_iff (S : Semantics Slot Value Test Effect World Observation)
    (region : Region Slot Value Test Effect) (bindings : Store Slot Value)
    (world : World) (answer : Observation) :
    answer ∈ (execute S (lower region) ⟨bindings, [], world, [], 0⟩).emitted ↔
      answer ∈ (source S region bindings world).1 := by
  rw [lower_exact S region _ rfl]
  simp

theorem compiled_restores (S : Semantics Slot Value Test Effect World Observation)
    (region : Region Slot Value Test Effect) (state : State Slot Value World Observation)
    (ready : state.skipping = 0) :
    (execute S (lower region) state).bindings = state.bindings ∧
      (execute S (lower region) state).trail = state.trail := by
  rw [lower_exact S region state ready]
  exact ⟨rfl, rfl⟩

/-- In particular, source failure does not reset the world to the checkpoint. -/
theorem compiled_world (S : Semantics Slot Value Test Effect World Observation)
    (region : Region Slot Value Test Effect) (state : State Slot Value World Observation)
    (ready : state.skipping = 0) :
    (execute S (lower region) state).world =
      (source S region state.bindings state.world).2 := by
  rw [lower_exact S region state ready]

/-! ## Choice records carry restoration as well as alternatives -/

/-- A choice boundary's log is chronological, as in `MarkedUndoLog`; this is
separate from the target instruction state's newest-first local trail. -/
structure ChoiceRecord (Slot : Type u) (Value : Type v) (Alternative : Type w) where
  saved : List (Slot × Value)
  alternatives : List Alternative

/-- No write in the interval touched an observer's live slot. This is a
syntactic support condition, not an assumed rollback-equivalence theorem. -/
def Avoids (log : List (Slot × Value)) (live : Set Slot) : Prop :=
  ∀ entry ∈ log, entry.1 ∉ live

/-- Undo is invisible at every slot outside the interval's write footprint. -/
theorem rollback_unwritten (log : List (Slot × Value)) (live : Set Slot)
    (disjoint : Avoids log live) (bindings : Store Slot Value) (slot : Slot)
    (used : slot ∈ live) :
    MarkedUndoLog.rollback log bindings slot = bindings slot := by
  induction log with
  | nil => rfl
  | cons entry rest ih =>
      have different : slot ≠ entry.1 := by
        intro same
        exact disjoint entry (List.mem_cons_self ..) (same ▸ used)
      have tail : Avoids rest live :=
        fun e member => disjoint e (List.mem_cons_of_mem _ member)
      simpa only [MarkedUndoLog.rollback, List.foldr_cons, MarkedUndoLog.restore,
        different, ↓reduceIte] using ih tail

/-- The observation after removing a boundary includes pending work and world,
not just the current answer. -/
def resumeView {Alternative : Type w} {Result : Type x}
    (observe : Store Slot Value → Result) (record : ChoiceRecord Slot Value Alternative)
    (bindings : Store Slot Value) (world : World) : List Alternative × Result × World :=
  (record.alternatives, observe (MarkedUndoLog.rollback record.saved bindings), world)

def withoutFrame {Alternative : Type w} {Result : Type x}
    (observe : Store Slot Value → Result) (bindings : Store Slot Value) (world : World) :
    List Alternative × Result × World := ([], observe bindings, world)

/-- A frame can be omitted only after proving that no pending alternative is
lost and that its restoration cannot change the continuation's observation.
A unique selected equation alone establishes neither condition. -/
theorem elide_choice_of_dead_writes {Alternative : Type w} {Result : Type x}
    (observe : Store Slot Value → Result) (live : Set Slot)
    (observer_local : ∀ left right, (∀ slot ∈ live, left slot = right slot) →
      observe left = observe right)
    (record : ChoiceRecord Slot Value Alternative) (empty : record.alternatives = [])
    (dead : Avoids record.saved live) (bindings : Store Slot Value) (world : World) :
    resumeView observe record bindings world = withoutFrame observe bindings world := by
  have same := observer_local (MarkedUndoLog.rollback record.saved bindings) bindings
    (fun slot used => rollback_unwritten record.saved live dead bindings slot used)
  simp only [resumeView, withoutFrame, empty, same]

/-- Saved payloads may be coalesced *inside this boundary*. Their complete
rollback and all performed effects remain unchanged. -/
theorem coalesce_choice {Alternative : Type w} {Result : Type x}
    (observe : Store Slot Value → Result) (record : ChoiceRecord Slot Value Alternative)
    (bindings : Store Slot Value) (world : World) :
    resumeView observe { record with saved := MarkedUndoLog.coalesce record.saved }
        bindings world = resumeView observe record bindings world := by
  simp only [resumeView, MarkedUndoLog.rollback_coalesce]

/-! ## Revision-pinned entries retain their authority across suspension -/

section Revisions
variable {Revision : Type w} {Head : Type x} [DecidableEq Revision]

/-- The captured revision belongs to the activation, not to a mutable global
"current version" consulted afresh every time this activation resumes. -/
structure Entry (Revision : Type w) (Head : Type x) where
  revision : Revision
  head : Head

/-- No finite enumeration of heads or restriction on values is required. A
missing entry declines; it does not invent a source equation. -/
def load (image : Revision → Head → Option (Region Slot Value Test Effect))
    (entry : Entry Revision Head) : Option (List (Instr Slot Value Test Effect)) :=
  (image entry.revision entry.head).map lower

omit [DecidableEq Slot] in
/-- A new program revision does not change already pinned code. This states
one precise activation policy; a language requiring fresh lookup on every
resumption needs an explicit different source policy and invalidation rule. -/
theorem load_other_revision (image : Revision → Head → Option (Region Slot Value Test Effect))
    (changed : Revision) (definitions : Head → Option (Region Slot Value Test Effect))
    (entry : Entry Revision Head) (other : entry.revision ≠ changed) :
    load (Function.update image changed definitions) entry = load image entry := by
  simp only [load, Function.update_of_ne other]

omit [DecidableEq Revision] in
/-- At every captured revision, entry into compiled code computes the source
region at that same revision, including its absence and its resulting world. -/
theorem entry_exact (S : Semantics Slot Value Test Effect World Observation)
    (image : Revision → Head → Option (Region Slot Value Test Effect))
    (entry : Entry Revision Head) (state : State Slot Value World Observation)
    (ready : state.skipping = 0) :
    (load image entry).map (fun code => execute S code state) =
      (image entry.revision entry.head).map (fun body =>
        { state with
          world := (source S body state.bindings state.world).2
          emitted := state.emitted ++ (source S body state.bindings state.world).1 }) := by
  cases found : image entry.revision entry.head with
  | none => simp [load, found]
  | some body => simp only [load, found, Option.map_some, lower_exact S body state ready]

end Revisions

/-! ## Suspended register frames and roots retained only for rollback -/

section Suspension
variable {V L O P H : Type}

/-- Drop only registers that the suspended continuation does not read. The
saved undo payloads and already transferred host arguments live separately. -/
def trim (live : Finset Nat) (registers : RegisterCode.Regs V) : RegisterCode.Regs V :=
  fun i => if i ∈ live then registers i else none

theorem trim_agrees (live : Finset Nat) (registers : RegisterCode.Regs V) :
    ∀ i ∈ live, trim live registers i = registers i := by
  intro i member
  simp [trim, member]

/-- This uses the established register-code liveness calculation, including
call argument evaluation before suspension and the return destination after it.
`V` may contain a higher-order closure or open syntax with its environment. -/
theorem suspend_trim_sound (S : RegisterCode.Sem V L O P H)
    (answer : H → List V → Option V) (destination : Nat) (head : H)
    (arguments : List (RegisterCode.Operand L)) (rest : List (RegisterCode.Instr L O P H))
    (out : Finset Nat) (registers : RegisterCode.Regs V) :
    Option.Rel (RegisterCode.Outcome.Agree out)
      (RegisterCode.exec S answer (.call destination head arguments :: rest) registers)
      ((RegisterCode.readAll S registers arguments).bind fun values =>
        (answer head values).bind fun value =>
          RegisterCode.exec S answer rest
            (Function.update (trim ((RegisterCode.liveIn S.toPatterns rest out).erase destination)
              registers) destination (some value))) :=
  RegisterCode.call_collect S answer destination head arguments rest out registers _
    (trim_agrees _ registers)

/-- Register roots are enumerated by indices, without comparing values or
requiring decidable equality of higher-order closures. -/
def registerValues (live : Finset Nat) (registers : RegisterCode.Regs V) : List V :=
  (live.sort (· ≤ ·)).flatMap fun slot => (registers slot).toList

def savedValues (log : List (Nat × Option V)) : List V :=
  log.flatMap fun entry => entry.2.toList

/-- All three strong-root families survive while a call is suspended. A host
cursor owns its transferred arguments even when caller registers are dead. -/
def suspendedValues (live : Finset Nat) (registers : RegisterCode.Regs V)
    (log : List (Nat × Option V)) (host : List V) : List V :=
  registerValues live registers ++ savedValues log ++ host

theorem saved_payload_is_root (live : Finset Nat) (registers : RegisterCode.Regs V)
    (log : List (Nat × Option V)) (host : List V) (slot : Nat) (value : V)
    (saved : (slot, some value) ∈ log) :
    value ∈ suspendedValues live registers log host := by
  simp only [suspendedValues, List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.mpr
    ⟨(slot, some value), saved, by simp⟩))

theorem host_value_is_root (live : Finset Nat) (registers : RegisterCode.Regs V)
    (log : List (Nat × Option V)) (host : List V) (value : V) (held : value ∈ host) :
    value ∈ suspendedValues live registers log host := by
  exact List.mem_append_right _ held

theorem register_value_is_root (live : Finset Nat) (registers : RegisterCode.Regs V)
    (log : List (Nat × Option V)) (host : List V) (slot : Nat) (value : V)
    (used : slot ∈ live) (held : registers slot = some value) :
    value ∈ suspendedValues live registers log host := by
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨slot, (Finset.mem_sort (· ≤ ·)).mpr used, by simp [held]⟩

/-- Restore an old binding: its saved value remains a root independently of
whether the overwritten register is live in the current continuation. -/
theorem rollback_payload_is_root (live : Finset Nat) (registers : RegisterCode.Regs V)
    (log : List (Nat × Option V)) (host : List V) (slot : Nat) (value : V)
    (saved : (slot, some value) ∈ log) :
    value ∈ suspendedValues live (trim live registers) log host :=
  saved_payload_is_root live _ log host slot value saved

variable {Address Payload : Type} [DecidableEq Address]

/-- An implementation supplies the complete strong addresses of a value,
including the environment of a closure. No value equality is required. -/
def addresses (references : V → Finset Address) : List V → Finset Address
  | [] => ∅
  | value :: rest => references value ∪ addresses references rest

theorem reference_mem_addresses (references : V → Finset Address) (values : List V)
    (value : V) (present : value ∈ values) (address : Address)
    (held : address ∈ references value) : address ∈ addresses references values := by
  induction values with
  | nil => simp at present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with same | later
      · exact Finset.mem_union_left _ (same ▸ held)
      · exact Finset.mem_union_right _ (ih later)

def ownedRoots (references : V → Finset Address) (values : List V) :
    ResourceOwnership.Roots Unit Address :=
  (addresses references values).image fun address => ((), address)

/-- Closing over the combined root family preserves every cell directly
referenced by a suspended value; `ResourceOwnership` also preserves all of its
transitive descendants, shared cells and cycles. -/
theorem suspended_cell_survives (references : V → Finset Address)
    (heap : ResourceOwnership.Heap Address Payload) (values : List V)
    (valid : ResourceOwnership.ValidRoots heap (ownedRoots references values))
    (value : V) (present : value ∈ values) (address : Address)
    (held : address ∈ references value) :
    (ResourceOwnership.collect heap (ownedRoots references values)).lookup address =
      heap.lookup address := by
  have root : ((), address) ∈ ownedRoots references values :=
    Finset.mem_image.mpr ⟨address, reference_mem_addresses references values value
      present address held, rfl⟩
  exact ResourceOwnership.lookup_collect_of_live heap _
    (ResourceOwnership.live_of_root heap _ root (valid _ root))

/-- A cell referenced only by an old binding survives collection while the
host is suspended, even after current dead registers have been cleared. -/
theorem saved_cell_survives (references : V → Finset Address)
    (heap : ResourceOwnership.Heap Address Payload)
    (live : Finset Nat) (registers : RegisterCode.Regs V)
    (log : List (Nat × Option V)) (host : List V)
    (valid : ResourceOwnership.ValidRoots heap
      (ownedRoots references (suspendedValues live (trim live registers) log host)))
    (slot : Nat) (value : V) (saved : (slot, some value) ∈ log) (address : Address)
    (held : address ∈ references value) :
    (ResourceOwnership.collect heap
      (ownedRoots references (suspendedValues live (trim live registers) log host))).lookup address =
        heap.lookup address :=
  suspended_cell_survives references heap _ valid value
    (rollback_payload_is_root live registers log host slot value saved) address held

end Suspension

/-! ## Executable positive and negative controls -/

namespace Controls

def semantics : Semantics Nat Nat (Nat × Nat) Nat Nat Nat where
  test := fun (slot, expected) bindings _ => bindings slot == expected
  effect := Nat.add
  observe := fun bindings _ => bindings 0

def zero : Store Nat Nat := fun _ => 0

def entry : State Nat Nat Nat Nat := ⟨zero, [], 0, [], 0⟩

/-- Left branch fails after binding and an effect. Right branch sees the old
binding but the performed effect remains. -/
def failedEffect : Region Nat Nat (Nat × Nat) Nat :=
  .choice (.write 0 9 (.perform 7 .fail)) .answer

theorem failure_keeps_effect :
    (execute semantics (lower failedEffect) entry).emitted = [0] ∧
    (execute semantics (lower failedEffect) entry).world = 7 ∧
    (execute semantics (lower failedEffect) entry).bindings 0 = 0 := by decide

/-- Here world mutation changes later guard acceptance and the yielded value. -/
def worldSemantics : Semantics Nat Nat Nat Nat Nat Nat where
  test := fun expected _ world => world == expected
  effect := Nat.add
  observe := fun bindings world => bindings 0 + world

/-- A failed alternative performs a lasting mutation; its sibling can observe
that mutation in both its guard and answer, while seeing restored bindings. -/
theorem failed_mutation_enables_sibling :
    let program : Region Nat Nat Nat Nat :=
      .choice (.write 0 9 (.perform 7 .fail)) (.guard 7 .answer)
    (execute worldSemantics (lower program) entry).emitted = [7] ∧
    (execute worldSemantics (lower program) entry).world = 7 ∧
    (execute worldSemantics (lower program) entry).bindings 0 = 0 := by decide

/-- Nested overwrites restore the correct payload at each boundary. -/
def nested : Region Nat Nat (Nat × Nat) Nat :=
  .write 0 4 (.choice (.write 0 9 .answer) .answer)

theorem nested_restoration :
    (execute semantics (lower nested) entry).emitted = [9, 4] ∧
    (execute semantics (lower nested) entry).bindings 0 = 0 := by decide

theorem duplicate_occurrences_remain :
    (execute semantics (lower (.choice .answer .answer)) entry).emitted = [0, 0] := by decide

theorem guard_skips_effect_and_undo :
    (execute semantics (lower (.guard (0, 3) (.write 0 5 (.perform 8 .answer)))) entry).world = 0 ∧
    (execute semantics (lower (.guard (0, 3) (.write 0 5 (.perform 8 .answer)))) entry).emitted = [] := by
  decide

/-- No alternative remains, yet removing restoration changes the outer
continuation's observation. Singleton equation admission does not justify it. -/
def needsRestore : ChoiceRecord Nat Nat Nat := ⟨[(0, 0)], []⟩

theorem empty_alternatives_do_not_license_elision :
    resumeView (fun bindings => bindings 0) needsRestore (fun _ => 9) 7 ≠
      (withoutFrame (Alternative := Nat) (fun bindings => bindings 0) (fun _ => 9) 7) := by
  decide

theorem nonempty_alternative_cannot_be_discarded :
    resumeView (fun bindings => bindings 0) (⟨[], [42]⟩ : ChoiceRecord Nat Nat Nat) zero 7 ≠
      (withoutFrame (Alternative := Nat) (fun bindings => bindings 0) zero 7) := by decide

theorem dead_register_does_not_mean_dead_payload :
    suspendedValues ∅ (fun _ => (none : Option Nat)) [(0, some 8)] [12] = [8, 12] := by
  simp [suspendedValues, registerValues, savedValues]

/-- The two revisions deliberately compute different answers. -/
def image (revision : Nat) (_head : Unit) : Option (Region Nat Nat (Nat × Nat) Nat) :=
  some (.write 0 revision .answer)

theorem fresh_lookup_differs_from_pinning :
    ((load image ⟨1, ()⟩).map (fun code => (execute semantics code entry).emitted)) = some [1] ∧
    ((load image ⟨2, ()⟩).map (fun code => (execute semantics code entry).emitted)) = some [2] := by
  decide

end Controls

end Mettapedia.Machines.TransactionalSearchCode
