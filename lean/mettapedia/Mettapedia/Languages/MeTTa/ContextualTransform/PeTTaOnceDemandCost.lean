import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand

/-!
# The work of `once` over ordered alternatives, and the first-firing rule

Part A gives `once` over ordered alternatives, each with the work its run costs
from the store it starts in. An eager `once`, which runs every alternative
before keeping the first answer, costs the sum over all of them
(`eagerRun_work`); the lazy `once` costs the alternatives up to the first answer
(`lazyRun_work`), whatever follows them (`lazyRun_append`), and both keep the
same first answer (`lazyRun_answer`). For a first alternative of constant work
and a second of work linear in the argument, `n` calls cost `n * (n + 1)`
eagerly, between `n ^ 2` and `2 * n ^ 2`, and `n` lazily (`eager_pick_loop`,
`eager_pick_loop_quadratic`, `lazy_pick_loop`).

The slowdown measured in CeTTa had another mechanism, modelled next. A `once`
routed out of the compiled region makes the host re-enter that region for its
call, and each entry admits the call's terms again. A loop of `n` calls over an
argument of `n` cells then admits `n * (n + 1)` nodes, where the compiled route
admits none (`every_once_delegated_loop`, `firing_once_delegated_loop`).
Delegating only the bodies that may run a transform still pays that admission
for them (`firing_body_loop`). The compiled region therefore runs every `once`
itself and carries the first-firing demand on the continuation that receives a
transform's result, so no `once` call is delegated and the loop admits nothing,
whatever its body may run (`demand_carried_loop`).

Part B is the fixed machine under a `once`, as a small-step relation that pops
the alternatives in order. A transform opens with first-firing demand
(`PeTTaTransformDemand.firstFiring`, which `firstFiring_from_packet` identifies
with the authored packet selection of `tfs:run-first`). An alternative without
an answer leaves its store changes, and the next alternative runs from the
store it left. Every input has a complete run (`run_exists`), steps are
deterministic (`step_deterministic`), and every complete run ends at the
authored reference's first answer and store, at the work of the alternatives
up to that answer (`run_reference`; together `machine_agrees_with_reference`).
The reference is `Search.once` over the alternatives, with `firstFiring` for
each transform. Neither what a run observes nor its work depends on the
alternatives after the first answer (`reference_append`, `prefixWork_append`,
`run_ignores_later`). A rule that ends the `once` at the first firing even
without an answer differs from the reference
(`Controls.ending_at_the_firing_drops_fallback`).

The alternatives of Part B are those the `once`'s demand reaches, in the order
its search visits them; a transform whose result feeds other work belongs to an
`other` alternative under that work's own demand.

These are models. Agreement with the C implementation comes from fixtures and
probes, not from these proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOnceDemandCost

open Mettapedia.Languages.MeTTa.PeTTa (Answers)
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

/-! ## Part A: the work of `once` over ordered alternatives -/

/-- An alternative a `once` may try: its run from a store, of which `once`
reads the first answer or the end, and the work of that run from the store. -/
structure Alt (S A : Type) where
  run : Search S A
  work : S → Nat

section Work

variable {S A : Type}

/-- The store the alternative's run is at when `once` stops reading it. -/
def Alt.stop (alt : Alt S A) (store : S) : S :=
  match alt.run store with
  | .done final => final
  | .answer _ here _ => here

/-- The alternative's first answer, with the store it is produced at. -/
def Alt.first (alt : Alt S A) (store : S) : Option (A × S) :=
  (alt.run store).first?

/-- The work of every alternative, each run from the store the previous one
left. -/
def trail : List (Alt S A) → S → List Nat
  | [], _ => []
  | alt :: rest, store => alt.work store :: trail rest (alt.stop store)

/-- The work of the alternatives `once` reaches: up to and including the first
one with an answer. -/
def reached : List (Alt S A) → S → List Nat
  | [], _ => []
  | alt :: rest, store =>
    match alt.first store with
    | some _ => [alt.work store]
    | none => alt.work store :: reached rest (alt.stop store)

/-- Lazy `once`: run the alternatives in order, each from the store the
previous one left, and stop at the first answer. -/
def lazyRun : List (Alt S A) → S → Option (A × S) × Nat
  | [], _ => (none, 0)
  | alt :: rest, store =>
    match alt.first store with
    | some answer => (some answer, alt.work store)
    | none =>
      let later := lazyRun rest (alt.stop store)
      (later.1, alt.work store + later.2)

/-- Eager `once`: run every alternative, each from the store the previous one
left, and then keep the first answer. -/
def eagerRun : List (Alt S A) → S → Option (A × S) × Nat
  | [], _ => (none, 0)
  | alt :: rest, store =>
    let later := eagerRun rest (alt.stop store)
    ((alt.first store).or later.1, alt.work store + later.2)

/-- The eager `once` costs the sum over all alternatives. -/
theorem eagerRun_work (alts : List (Alt S A)) (store : S) :
    (eagerRun alts store).2 = (trail alts store).sum := by
  induction alts generalizing store with
  | nil => rfl
  | cons alt rest ih => simp [eagerRun, trail, ih]

/-- The lazy `once` costs the alternatives up to the first answer. -/
theorem lazyRun_work (alts : List (Alt S A)) (store : S) :
    (lazyRun alts store).2 = (reached alts store).sum := by
  induction alts generalizing store with
  | nil => rfl
  | cons alt rest ih =>
    cases h : alt.first store <;> simp [lazyRun, reached, h, ih]

/-- Both keep the same first answer, at the store it is produced at. -/
theorem lazyRun_answer (alts : List (Alt S A)) (store : S) :
    (lazyRun alts store).1 = (eagerRun alts store).1 := by
  induction alts generalizing store with
  | nil => rfl
  | cons alt rest ih =>
    cases h : alt.first store <;> simp [lazyRun, eagerRun, h, ih]

theorem lazyRun_work_le (alts : List (Alt S A)) (store : S) :
    (lazyRun alts store).2 ≤ (eagerRun alts store).2 := by
  induction alts generalizing store with
  | nil => exact Nat.le_refl 0
  | cons alt rest ih =>
    cases h : alt.first store with
    | some answer => simp [lazyRun, eagerRun, h]
    | none =>
      simp only [lazyRun, eagerRun, h]
      exact Nat.add_le_add_left (ih _) _

/-- The lazy `once` does not read the alternatives after its first answer. -/
theorem lazyRun_append (alts later : List (Alt S A)) (store : S)
    (answered : (lazyRun alts store).1.isSome) :
    lazyRun (alts ++ later) store = lazyRun alts store := by
  induction alts generalizing store with
  | nil => simp [lazyRun] at answered
  | cons alt rest ih =>
    cases h : alt.first store with
    | some answer => simp [lazyRun, h]
    | none =>
      simp only [lazyRun, h] at answered
      simp only [List.cons_append, lazyRun, h, ih _ answered]

end Work

/-! ### The measured shape: `(pick (cons h t))` and `(pick l)` as `(len l)` -/

/-- `(pick (cons h t))` answers `h` at constant work. -/
def headAlt : Alt Unit Nat := ⟨Search.superpose [1], fun _ => 1⟩

/-- `(pick l)` computes `(len l)`, whose work is the list's `n` cells. -/
def lenAlt (n : Nat) : Alt Unit Nat := ⟨Search.superpose [n], fun _ => n⟩

def pick (n : Nat) : List (Alt Unit Nat) := [headAlt, lenAlt n]

/-- `calls` once-calls over the alternatives for an argument of `n` cells. -/
def loop (run : List (Alt Unit Nat) → Unit → Option (Nat × Unit) × Nat)
    (calls n : Nat) : Nat :=
  calls * (run (pick n) ()).2

theorem pick_first_answer (n : Nat) :
    (lazyRun (pick n) ()).1 = some (1, ()) ∧ (eagerRun (pick n) ()).1 = some (1, ()) := by
  constructor <;> rfl

theorem eager_pick_loop (n : Nat) : loop eagerRun n n = n * (n + 1) := by
  simp [loop, eagerRun, pick, headAlt, lenAlt, Nat.add_comm]

theorem lazy_pick_loop (n : Nat) : loop lazyRun n n = n := by
  simp [loop, lazyRun, pick, headAlt, Alt.first, Search.superpose, Trace.first?]

/-- `n` eager calls cost between `n ^ 2` and `2 * n ^ 2`: quadratic. -/
theorem eager_pick_loop_quadratic (n : Nat) :
    n ^ 2 ≤ loop eagerRun n n ∧ loop eagerRun n n ≤ 2 * n ^ 2 := by
  rw [eager_pick_loop]
  constructor
  · rw [Nat.pow_two]
    exact Nat.mul_le_mul_left n (Nat.le_succ n)
  · cases n with
    | zero => simp
    | succ m =>
      rw [Nat.pow_two, Nat.two_mul]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos m)) _ |>.trans_eq'
        (Nat.mul_succ _ _)

/-! ### The mechanism measured in CeTTa: re-admitting a call's terms -/

/-- Where a `once` call runs: in the compiled region that already holds the
loop's values, or delegated to the host, which re-enters the compiled region
for the call and admits the call's terms again. -/
inductive Route where
  | compiled
  | delegated
  deriving DecidableEq, Repr

/-- The nodes admitted for one call `(pick big)` whose argument has `n` cells:
the call node and the cells on the delegated route, nothing on the compiled
one. -/
def admitted : Route → Nat → Nat
  | .compiled, _ => 0
  | .delegated, n => n + 1

/-- The rule the regression had: every PeTTa `once` is delegated. -/
def everyOnceDelegated (_mayRunTransform : Bool) : Route := .delegated

/-- Delegating exactly the bodies that may run a transform. -/
def firingOnceDelegated (mayRunTransform : Bool) : Route :=
  if mayRunTransform then .delegated else .compiled

/-- The rule the compiled region follows: it runs every `once` itself and
carries the first-firing demand on the continuation that receives a
transform's result, so no body is delegated. -/
def demandCarried (_mayRunTransform : Bool) : Route := .compiled

/-- The nodes a loop of `calls` once-calls admits. -/
def loopAdmitted (rule : Bool → Route) (mayRunTransform : Bool) (calls n : Nat) : Nat :=
  calls * admitted (rule mayRunTransform) n

theorem every_once_delegated_loop (n : Nat) :
    loopAdmitted everyOnceDelegated false n n = n * (n + 1) := rfl

theorem firing_once_delegated_loop (n : Nat) :
    loopAdmitted firingOnceDelegated false n n = 0 := by
  simp [loopAdmitted, firingOnceDelegated, admitted]

/-- Under that delegation, a body that may run a transform keeps the host's
delimiter, and with it the admission at each re-entry. -/
theorem firing_body_loop (n : Nat) :
    firingOnceDelegated true = .delegated ∧
      loopAdmitted firingOnceDelegated true n n = n * (n + 1) := ⟨rfl, rfl⟩

/-- Carrying the demand admits nothing, whether or not the body may run a
transform. -/
theorem demand_carried_loop (mayRunTransform : Bool) (n : Nat) :
    loopAdmitted demandCarried mayRunTransform n n = 0 := by
  simp [loopAdmitted, demandCarried, admitted]

/-- The closed forms at the sizes measured on the C implementation: a profile
of the regressed build over 4000 calls (16004000 admissions of a list cell or
call); the admission counter of a build that delegated the bodies that may run
a transform, on such a body (300 and 600 calls) and on a pure body (600 calls);
and the counter of a build that carries the demand, on the body that may run a
transform (300 and 600 calls). The equalities here are arithmetic; their
agreement with the C is by measurement. -/
theorem admitted_at_measured_sizes :
    loopAdmitted everyOnceDelegated false 4000 4000 = 16004000 ∧
      loopAdmitted firingOnceDelegated true 300 300 = 90300 ∧
      loopAdmitted firingOnceDelegated true 600 600 = 360600 ∧
      loopAdmitted firingOnceDelegated false 600 600 = 0 ∧
      loopAdmitted demandCarried true 300 300 = 0 ∧
      loopAdmitted demandCarried true 600 600 = 0 := by
  decide

/-! ## Part B: the fixed machine under a `once` -/

/-- An alternative on a `once`'s demand path: a transform with takes or a
destination, which the demand limits to its first firing, or any other
computation. -/
inductive Branch (A : Type) where
  | transform (route : Answers → Search Store A) (sources : Sources)
      (emit : Subst → Answers)
  | other (run : Search Store A)

section Machine

variable {A : Type}

/-- What the authored reference runs for an alternative: `tfs:run-first` for a
transform, whose meaning is `firstFiring`, and the computation otherwise. -/
def Branch.reference : Branch A → Search Store A
  | .transform route sources emit => PeTTaTransformDemand.firstFiring route sources emit
  | .other run => run

/-- The authored reference: `once` over the alternatives, in order. -/
def reference (branches : List (Branch A)) : Search Store A :=
  Search.once ((Search.superpose branches).bind Branch.reference)

/-- An alternative as the machine runs it under the `once`'s demand. A
transform opens with first-firing demand, so its cursor closes after that
firing's packet; any other alternative runs to its first answer. -/
def Branch.first : Branch A → Search Store A
  | .transform route sources emit => PeTTaTransformDemand.firstFiring route sources emit
  | .other run => Search.once run

/-- The machine's state under a `once`: searching from a store with the
alternatives still on its choice stack, or the `once`'s outcome. -/
inductive State (A : Type) where
  | search (store : Store) (pending : List (Branch A))
  | answered (value : A) (store : Store)
  | exhausted (store : Store)

/-- The outcomes, which have no step. -/
def State.Terminal : State A → Prop
  | .search _ _ => False
  | .answered _ _ => True
  | .exhausted _ => True

/-- What the `once`'s consumer observes at an outcome: its answers and the
store it leaves. -/
def State.observe : State A → List A × Store
  | .search store _ => ([], store)
  | .answered value store => ([value], store)
  | .exhausted store => ([], store)

/-- One step pops the next alternative and runs it to its first answer or its
end, at the work `work` charges for that alternative from that store. -/
inductive Step (work : Branch A → Store → Nat) : State A → Nat → State A → Prop where
  | empty (store : Store) : Step work (.search store []) 0 (.exhausted store)
  | answer {branch : Branch A} {rest : List (Branch A)} {store here : Store} {value : A}
      {later : Store → Trace Store A}
      (produced : branch.first store = .answer value here later) :
      Step work (.search store (branch :: rest)) (work branch store) (.answered value here)
  | next {branch : Branch A} {rest : List (Branch A)} {store final : Store}
      (ended : branch.first store = .done final) :
      Step work (.search store (branch :: rest)) (work branch store) (.search final rest)

/-- A run, with the work its steps accumulate. -/
inductive Run (work : Branch A → Store → Nat) : State A → Nat → State A → Prop where
  | refl (state : State A) : Run work state 0 state
  | step {first middle last : State A} {now later : Nat} :
      Step work first now middle → Run work middle later last →
      Run work first (now + later) last

/-- The work of the alternatives a `once` reaches: up to and including the
first with an answer, each from the store the previous one left. -/
def prefixWork (work : Branch A → Store → Nat) : List (Branch A) → Store → Nat
  | [], _ => 0
  | branch :: rest, store =>
    match branch.first store with
    | .answer _ _ _ => work branch store
    | .done final => work branch store + prefixWork work rest final

variable {work : Branch A → Store → Nat}

theorem step_deterministic {first one other : State A} {now now' : Nat}
    (left : Step work first now one) (right : Step work first now' other) :
    one = other ∧ now = now' := by
  cases left with
  | empty => cases right; exact ⟨rfl, rfl⟩
  | answer produced =>
    cases right with
    | answer produced' =>
      rw [produced] at produced'
      cases produced'
      exact ⟨rfl, rfl⟩
    | next ended => rw [produced] at ended; cases ended
  | next ended =>
    cases right with
    | answer produced => rw [ended] at produced; cases produced
    | next ended' =>
      rw [ended] at ended'
      cases ended'
      exact ⟨rfl, rfl⟩

theorem terminal_stays {first last : State A} {now : Nat}
    (run : Run work first now last) (terminal : first.Terminal) :
    last = first ∧ now = 0 := by
  cases run with
  | refl => exact ⟨rfl, rfl⟩
  | step step _ =>
    cases step <;> exact absurd terminal (by simp [State.Terminal])

private theorem once_once {S B : Type} (m : Search S B) (store : S) :
    Search.once (Search.once m) store = Search.once m store := by
  simp only [Search.once]
  cases m store <;> rfl

private theorem once_firstFiring (route : Answers → Search Store A) (sources : Sources)
    (emit : Subst → Answers) (store : Store) :
    Search.once (PeTTaTransformDemand.firstFiring route sources emit) store =
      PeTTaTransformDemand.firstFiring route sources emit store := by
  have unfolded : PeTTaTransformDemand.firstFiring route sources emit store =
      match fireFirst store sources emit with
      | none => .done store
      | some (fired, packet) => Search.once (route packet) fired := rfl
  simp only [Search.once, unfolded]
  cases fireFirst store sources emit with
  | none => rfl
  | some result =>
    obtain ⟨fired, packet⟩ := result
    dsimp only
    cases route packet fired <;> rfl

/-- The reference reads its alternatives one at a time, as the machine does. -/
theorem reference_cons (branch : Branch A) (rest : List (Branch A)) (store : Store) :
    reference (branch :: rest) store =
      match branch.first store with
      | .answer value here _ => .answer value here .done
      | .done final => reference rest final := by
  have ref_first : Search.once (Branch.reference branch) store = branch.first store := by
    cases branch with
    | transform route sources emit => exact once_firstFiring route sources emit store
    | other run => rfl
  rw [← ref_first]
  simp only [reference, Search.once, Search.bind, Search.superpose, Trace.bind]
  cases Branch.reference branch store with
  | done final => rfl
  | answer value here later => rfl

theorem reference_nil (store : Store) : reference ([] : List (Branch A)) store = .done store := rfl

/-- Every input has a complete run; its work is the work of the alternatives
up to the first answer. -/
theorem run_exists (work : Branch A → Store → Nat) (branches : List (Branch A)) (store : Store) :
    ∃ last, last.Terminal ∧ Run work (.search store branches) (prefixWork work branches store) last := by
  induction branches generalizing store with
  | nil => exact ⟨.exhausted store, trivial, Run.step (Step.empty store) (Run.refl _)⟩
  | cons branch rest ih =>
    cases produced : branch.first store with
    | answer value here later =>
      refine ⟨.answered value here, trivial, ?_⟩
      have run := Run.step (Step.answer (work := work) (rest := rest) produced) (Run.refl _)
      simpa [prefixWork, produced] using run
    | done final =>
      obtain ⟨last, terminal, run⟩ := ih final
      refine ⟨last, terminal, ?_⟩
      have run := Run.step (Step.next (work := work) (rest := rest) produced) run
      simpa [prefixWork, produced] using run

/-- Every complete run ends at the authored reference's first answer and store,
at the work of the alternatives up to that answer. -/
theorem run_reference {branches : List (Branch A)} {store : Store} {now : Nat} {last : State A}
    (run : Run work (.search store branches) now last) (terminal : last.Terminal) :
    last.observe = (reference branches store).drain ∧ now = prefixWork work branches store := by
  induction branches generalizing store now with
  | nil =>
    cases run with
    | refl => exact absurd terminal (by simp [State.Terminal])
    | step step rest =>
      cases step
      obtain ⟨same, zero⟩ := terminal_stays rest trivial
      subst same zero
      exact ⟨rfl, rfl⟩
  | cons branch others ih =>
    cases run with
    | refl => exact absurd terminal (by simp [State.Terminal])
    | step step rest =>
      cases step with
      | answer produced =>
        obtain ⟨same, zero⟩ := terminal_stays rest trivial
        subst same zero
        rw [reference_cons, produced]
        exact ⟨rfl, by simp [prefixWork, produced]⟩
      | next ended =>
        obtain ⟨observed, worked⟩ := ih rest
        rw [reference_cons, ended]
        exact ⟨observed, by simp [prefixWork, ended, worked]⟩

/-- Neither the answer nor the store depends on alternatives after the first
answer. -/
theorem reference_append (branches later : List (Branch A)) (store : Store)
    (answered : ((reference branches store).first?).isSome) :
    reference (branches ++ later) store = reference branches store := by
  induction branches generalizing store with
  | nil => simp [reference_nil, Trace.first?] at answered
  | cons branch rest ih =>
    rw [List.cons_append, reference_cons, reference_cons]
    rw [reference_cons] at answered
    cases produced : branch.first store with
    | answer value here _ => rfl
    | done final =>
      rw [produced] at answered
      exact ih final answered

/-- Nor does the work. -/
theorem prefixWork_append (work : Branch A → Store → Nat) (branches later : List (Branch A))
    (store : Store) (answered : ((reference branches store).first?).isSome) :
    prefixWork work (branches ++ later) store = prefixWork work branches store := by
  induction branches generalizing store with
  | nil => simp [reference_nil, Trace.first?] at answered
  | cons branch rest ih =>
    rw [reference_cons] at answered
    simp only [List.cons_append, prefixWork]
    cases produced : branch.first store with
    | answer value here _ => rfl
    | done final =>
      rw [produced] at answered
      dsimp only
      rw [ih final answered]

/-- The fixed machine against the authored reference: a complete run exists,
and every complete run observes the reference's first answer and store, at the
work of the alternatives up to that answer. -/
theorem machine_agrees_with_reference (work : Branch A → Store → Nat)
    (branches : List (Branch A)) (store : Store) :
    (∃ last, last.Terminal ∧
      Run work (.search store branches) (prefixWork work branches store) last) ∧
    ∀ now last, last.Terminal → Run work (.search store branches) now last →
      last.observe = (reference branches store).drain ∧
        now = prefixWork work branches store :=
  ⟨run_exists work branches store, fun _ _ terminal run => run_reference run terminal⟩

/-- Alternatives after the first answer change neither what a complete run
observes nor its work. -/
theorem run_ignores_later (branches later : List (Branch A)) (store : Store)
    (answered : ((reference branches store).first?).isSome)
    {now : Nat} {last : State A} (run : Run work (.search store (branches ++ later)) now last)
    (terminal : last.Terminal) :
    last.observe = (reference branches store).drain ∧ now = prefixWork work branches store := by
  obtain ⟨observed, worked⟩ := run_reference run terminal
  rw [reference_append branches later store answered] at observed
  rw [prefixWork_append work branches later store answered] at worked
  exact ⟨observed, worked⟩

/-- A rule that ends the `once` at the first firing, even when its packet has
no answer, and so never tries the alternatives after it. -/
def endingAtFiring : List (Branch A) → Search Store A
  | [], store => .done store
  | .transform route sources emit :: rest, store =>
    match fireFirst store sources emit with
    | none => endingAtFiring rest store
    | some (fired, packet) => Search.once (route packet) fired
  | .other run :: rest, store =>
    match Search.once run store with
    | .answer value here _ => .answer value here .done
    | .done final => endingAtFiring rest final

end Machine

namespace Controls

def item (name : String) : Atom := .expression [.symbol "item", .symbol name]
def start : Store := [item "a", item "b"]

/-- `(take (item $x))`, and `(take (item NAME))`. -/
def takeItem : Sources := ⟨[.pat .take (.expression [.symbol "item", .var "x"])], [], none⟩
def takeExactly (name : String) : Sources := ⟨[.pat .take (item name)], [], none⟩

/-- A template without instances, as `(empty)` or `(,)` leave the caller. -/
def noInstances (_ : Subst) : Answers := []
def got (bindings : Subst) : Answers := [.expression [.symbol "got", applySubst bindings (.var "x")]]

/-- `(transform $sp (take (item $x)) (empty))`. -/
def claim : Branch Atom := .transform toCaller takeItem noInstances
def claimGot : Branch Atom := .transform toCaller takeItem got
def value (name : String) : Branch Atom := .other (Search.superpose [.symbol name])

/-- One unit of work per alternative tried. -/
def unit : Branch Atom → Store → Nat := fun _ _ => 1

/-- `(= (act $sp) (transform ...))` before `(= (act $sp) fallback)`. -/
def answerlessThenFallback : List (Branch Atom) := [claim, value "fallback"]

theorem reference_answers_fallback_after_one_take :
    (reference answerlessThenFallback start).drain = ([.symbol "fallback"], [item "b"]) ∧
      prefixWork unit answerlessThenFallback start = 2 := by
  decide +kernel

theorem ending_at_the_firing_drops_fallback :
    (endingAtFiring answerlessThenFallback start).drain = ([], [item "b"]) := by
  decide +kernel

/-- The machine's run for that shape exists and ends with `fallback`, one take
made: its only possible end. -/
theorem machine_answers_fallback_after_one_take :
    ∃ last, last.Terminal ∧ Run unit (.search start answerlessThenFallback) 2 last ∧
      last.observe = ([.symbol "fallback"], [item "b"]) := by
  obtain ⟨last, terminal, run⟩ := run_exists unit answerlessThenFallback start
  have agrees := run_reference run terminal
  refine ⟨last, terminal, ?_, ?_⟩
  · rwa [reference_answers_fallback_after_one_take.2] at run
  · exact agrees.1.trans reference_answers_fallback_after_one_take.1

/-- With `fallback` first, the transform is never reached. -/
theorem fallback_first_takes_nothing :
    (reference [value "fallback", claim] start).drain = ([.symbol "fallback"], start) ∧
      prefixWork unit [value "fallback", claim] start = 1 := by
  decide +kernel

/-- `(superpose (TRANSFORM done))`. -/
theorem answerless_take_then_value :
    (reference [claim, value "done"] start).drain = ([.symbol "done"], [item "b"]) := by
  decide +kernel

/-- `(superpose (TAKE-a TAKE-b done))`: each transform fires once. -/
theorem two_takes_then_value :
    (reference [.transform toCaller (takeExactly "a") noInstances,
      .transform toCaller (takeExactly "b") noInstances, value "done"] start).drain =
        ([.symbol "done"], []) := by
  decide +kernel

/-- Two transform equations: the second answers from the store the first left. -/
theorem later_equation_answers :
    (reference [claim, claimGot] start).drain =
      ([.expression [.symbol "got", .symbol "b"]], []) := by
  decide +kernel

/-- The eager family at 1000 calls over 1000 cells, against the lazy one. -/
theorem pick_loop_at_1000 :
    loop eagerRun 1000 1000 = 1001000 ∧ loop lazyRun 1000 1000 = 1000 := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOnceDemandCost
