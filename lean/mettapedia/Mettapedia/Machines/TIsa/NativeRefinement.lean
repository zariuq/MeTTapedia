import Mettapedia.GSLT.Logic.WeakestPrecondition

/-!
# Existing GSLT program proofs transferred to native execution

A machine interface supplies finite execution, determinism and a transitive
frame. The source is the existing program/action semantics and weakest
precondition library. Representation is indexed by the remaining program,
so primitive contracts must retain the native continuation and code location.

A boundary certificate discharges one source primitive or return at a time.
Induction realizes every safe source run and transfers its weakest precondition
to a terminating native run. Explicit source progress prevents empty-outcome
vacuity. Determinism reflects other native results of the witnessed length.
Counted certificates also retain the exact native step total through composition.
This does not establish arbitrary-run decomposition or certify an emitter:
concrete templates, layouts, admission and boundary certificates are required.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.NativeRefinement

open Mettapedia.GSLT.Logic.AbstractSeparationLogic

universe u v s m

structure Machine (M : Type m) where
  executes : Nat → M → M → Prop
  zero : ∀ state, executes 0 state state
  append : ∀ {first second before middle after}, executes first before middle →
    executes second middle after → executes (first + second) before after
  deterministic : ∀ {count before left right}, executes count before left →
    executes count before right → left = right
  frame : M → M → Prop
  frame_refl : ∀ state, frame state state
  frame_trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after

variable {S : Type s} {M : Type m} {Op : Type u} {Reply : Op → Type v} {Result : Type v}

structure Boundary (actions : (op : Op) → Action S (Reply op)) (machine : Machine M)
    (represents : Prog Op Reply Result → S → M → Prop) (observes : Result → S → M → Prop) : Prop where
  returned : ∀ value source native, represents (.ret value) source native →
    ∃ count after, machine.executes count native after ∧ machine.frame native after ∧ observes value source after
  primitive : ∀ op next source result following native,
    (actions op).Safe source → represents (.call op next) source native →
    (actions op).Step source result following →
    ∃ count after, machine.executes count native after ∧ machine.frame native after ∧
      represents (next result) following after

variable {actions : (op : Op) → Action S (Reply op)} {machine : Machine M}
variable {represents : Prog Op Reply Result → S → M → Prop} {observes : Result → S → M → Prop}

theorem Boundary.realizes (boundary : Boundary actions machine represents observes)
    (program : Prog Op Reply Result) (source following : S) (native : M) (value : Result)
    (safe : program.Safe actions source) (represented : represents program source native)
    (run : program.Runs actions source value following) :
    ∃ count after, machine.executes count native after ∧ machine.frame native after ∧ observes value following after := by
  induction program generalizing source native with
  | ret answer =>
      obtain ⟨rfl, rfl⟩ := run
      exact boundary.returned answer source native represented
  | call op next ih =>
      obtain ⟨reply, middle, step, later⟩ := run
      obtain ⟨first, state, executed, framed, representedNext⟩ :=
        boundary.primitive op next source reply middle native safe.1 represented step
      obtain ⟨second, after, rest, frameRest, observed⟩ :=
        ih reply middle state (safe.2 reply middle step) representedNext later
      exact ⟨first + second, after, machine.append executed rest,
        machine.frame_trans framed frameRest, observed⟩

theorem Boundary.wp_native (boundary : Boundary actions machine represents observes)
    (progress : ∀ op, (actions op).Progress)
    (program : Prog Op Reply Result) (post : Result → S → Prop) (source : S) (native : M)
    (wp : program.wp actions post source) (represented : represents program source native) :
    ∃ value following count after, program.Runs actions source value following ∧ post value following ∧
      machine.executes count native after ∧ machine.frame native after ∧ observes value following after := by
  obtain ⟨value, following, run⟩ := program.exists_runs actions progress source wp.1
  obtain ⟨count, after, executed, framed, observed⟩ :=
    boundary.realizes program source following native value wp.1 represented run
  exact ⟨value, following, count, after, run, wp.2 value following run, executed, framed, observed⟩

theorem Boundary.wp_native_reflects (boundary : Boundary actions machine represents observes)
    (progress : ∀ op, (actions op).Progress)
    (program : Prog Op Reply Result) (post : Result → S → Prop) (source : S) (native : M)
    (wp : program.wp actions post source) (represented : represents program source native) :
    ∃ count, ∀ after, machine.executes count native after →
      ∃ value following, program.Runs actions source value following ∧ post value following ∧
        machine.frame native after ∧ observes value following after := by
  obtain ⟨value, following, count, proved, run, postHolds, executed, framed, observed⟩ :=
    boundary.wp_native progress program post source native wp represented
  refine ⟨count, ?_⟩
  intro after candidate
  have same := machine.deterministic executed candidate
  subst after
  exact ⟨value, following, run, postHolds, framed, observed⟩

structure CountedBoundary (actions : (op : Op) → Action S (Reply op)) (machine : Machine M)
    (represents : Prog Op Reply Result → S → M → Prop) (observes : Result → S → M → Prop)
    (steps : Prog Op Reply Result → S → Nat) : Prop where
  returned : ∀ value source native, represents (.ret value) source native →
    ∃ after, machine.executes (steps (.ret value) source) native after ∧
      machine.frame native after ∧ observes value source after
  primitive : ∀ op next source result following native,
    (actions op).Safe source → represents (.call op next) source native →
    (actions op).Step source result following →
    ∃ count after, machine.executes count native after ∧ machine.frame native after ∧
      represents (next result) following after ∧
      steps (.call op next) source = count + steps (next result) following

variable {steps : Prog Op Reply Result → S → Nat}

theorem CountedBoundary.forget (boundary : CountedBoundary actions machine represents observes steps) :
    Boundary actions machine represents observes where
  returned value source native represented := by
    obtain ⟨after, executed, framed, observed⟩ := boundary.returned value source native represented
    exact ⟨steps (.ret value) source, after, executed, framed, observed⟩
  primitive op next source result following native safe represented step := by
    obtain ⟨count, after, executed, framed, representedNext, _⟩ :=
      boundary.primitive op next source result following native safe represented step
    exact ⟨count, after, executed, framed, representedNext⟩

theorem CountedBoundary.realizes (boundary : CountedBoundary actions machine represents observes steps)
    (program : Prog Op Reply Result) (source following : S) (native : M) (value : Result)
    (safe : program.Safe actions source) (represented : represents program source native)
    (run : program.Runs actions source value following) :
    ∃ after, machine.executes (steps program source) native after ∧
      machine.frame native after ∧ observes value following after := by
  induction program generalizing source native with
  | ret answer =>
      obtain ⟨rfl, rfl⟩ := run
      exact boundary.returned answer source native represented
  | call op next ih =>
      obtain ⟨reply, middle, step, later⟩ := run
      obtain ⟨count, state, executed, framed, representedNext, exactSteps⟩ :=
        boundary.primitive op next source reply middle native safe.1 represented step
      obtain ⟨after, rest, frameRest, observed⟩ :=
        ih reply middle state (safe.2 reply middle step) representedNext later
      exact ⟨after, exactSteps ▸ machine.append executed rest,
        machine.frame_trans framed frameRest, observed⟩

theorem CountedBoundary.wp_native (boundary : CountedBoundary actions machine represents observes steps)
    (progress : ∀ op, (actions op).Progress)
    (program : Prog Op Reply Result) (post : Result → S → Prop) (source : S) (native : M)
    (wp : program.wp actions post source) (represented : represents program source native) :
    ∃ value following after, program.Runs actions source value following ∧ post value following ∧
      machine.executes (steps program source) native after ∧
      machine.frame native after ∧ observes value following after := by
  obtain ⟨value, following, run⟩ := program.exists_runs actions progress source wp.1
  obtain ⟨after, executed, framed, observed⟩ :=
    boundary.realizes program source following native value wp.1 represented run
  exact ⟨value, following, after, run, wp.2 value following run, executed, framed, observed⟩

theorem CountedBoundary.wp_native_reflects (boundary : CountedBoundary actions machine represents observes steps)
    (progress : ∀ op, (actions op).Progress)
    (program : Prog Op Reply Result) (post : Result → S → Prop) (source : S) (native : M)
    (wp : program.wp actions post source) (represented : represents program source native)
    (after : M) (run : machine.executes (steps program source) native after) :
    ∃ value following, program.Runs actions source value following ∧ post value following ∧
      machine.frame native after ∧ observes value following after := by
  obtain ⟨value, following, proved, sourceRun, holds, executed, framed, observed⟩ :=
    boundary.wp_native progress program post source native wp represented
  have same := machine.deterministic executed run
  subst after
  exact ⟨value, following, sourceRun, holds, framed, observed⟩

end Mettapedia.Machines.TIsa.NativeRefinement
