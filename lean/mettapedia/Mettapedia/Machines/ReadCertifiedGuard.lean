import Mettapedia.Machines.ReadCertifiedQueryReuse
import Mettapedia.Machines.OrderedGuardPipeline

/-!
# Read-certified facts at an ordered guard boundary

A cache retains immutable facts. Each invocation materializes its own ordered
binding refinements, then runs the existing success and failure continuations.
The comparison preserves arbitrary body effects and saved alternatives because
only the pure fact provider is replaced: for an entry with recorded provenance
the cached guard and the fresh guard are the same function (`cached_eq_fresh`),
and the statements about evaluation and pipelines are that equality under a
context.

This establishes the adapter law for an admitted pure query family. A source
typing service must separately factor through that family; an authored
classifier with effects cannot acquire that property merely from its outputs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadCertifiedGuard

open ReadOnlyQuery ReadCertifiedQueryReuse ScopedCommit

variable {Authority Query Key Value Fact Local World Result : Type}
variable [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]

namespace Supported

variable {State Answer : Type}

def fresh (family : ReadCertifiedQueryReuse.Supported.Family
    State Authority Query Key Value Answer) (snapshot : State)
    (queryOf : Local → Query) (materialize : Local → Answer → List Local) :
    OrderedGuardPipeline.Guard Local :=
  fun state => materialize state (family.observe snapshot (queryOf state)).answer

def cached (family : ReadCertifiedQueryReuse.Supported.Family
    State Authority Query Key Value Answer) (snapshot : State)
    (queryOf : Local → Query) (entry : Entry Authority Query Key Value Answer)
    (materialize : Local → Answer → List Local) : OrderedGuardPipeline.Guard Local :=
  fun state => materialize state
    (ReadCertifiedQueryReuse.Supported.reuse family snapshot (queryOf state) entry).1

/-- Each current caller materializes its own ordered refinements from the
certified immutable answer. The snapshot is chosen for this invocation. -/
theorem cached_eq_fresh (family : ReadCertifiedQueryReuse.Supported.Family
    State Authority Query Key Value Answer) (snapshot : State)
    (queryOf : Local → Query) (entry : Entry Authority Query Key Value Answer)
    (history : ReadCertifiedQueryReuse.Supported.Recorded family entry)
    (materialize : Local → Answer → List Local) :
    cached family snapshot queryOf entry materialize =
      fresh family snapshot queryOf materialize := by
  funext state
  exact ReadCertifiedQueryReuse.Supported.materialized_exact family snapshot
    (queryOf state) entry history materialize state

/-- Only the pure provider changes. Arbitrary consuming effects and saved
alternatives keep exactly their existing operational behavior. -/
theorem cached_guard_eval_exact (family : ReadCertifiedQueryReuse.Supported.Family
    State Authority Query Key Value Answer) (snapshot : State)
    (queryOf : Local → Query) (entry : Entry Authority Query Key Value Answer)
    (history : ReadCertifiedQueryReuse.Supported.Recorded family entry)
    (materialize : Local → Answer → List Local) (body : Body Local World)
    (state : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (OrderedGuardPipeline.guard
      (cached family snapshot queryOf entry materialize) body)
        state success failure saved world =
    eval (OrderedGuardPipeline.guard
      (fresh family snapshot queryOf materialize) body)
        state success failure saved world := by
  rw [cached_eq_fresh family snapshot queryOf entry history materialize]

theorem cached_in_pipeline_exact (family : ReadCertifiedQueryReuse.Supported.Family
    State Authority Query Key Value Answer) (snapshot : State)
    (queryOf : Local → Query) (entry : Entry Authority Query Key Value Answer)
    (history : ReadCertifiedQueryReuse.Supported.Recorded family entry)
    (materialize : Local → Answer → List Local)
    (before after : List (OrderedGuardPipeline.Guard Local)) (body : Body Local World) :
    OrderedGuardPipeline.pipeline
      (before ++ cached family snapshot queryOf entry materialize :: after) body =
    OrderedGuardPipeline.pipeline
      (before ++ fresh family snapshot queryOf materialize :: after) body := by
  rw [cached_eq_fresh family snapshot queryOf entry history materialize]

end Supported

/-- Adaptive query programs specialize the same supported guard adapter. -/
def fresh (family : Authority → Query → Program Key Value (List Fact))
    (authority : Authority) (queryOf : Local → Query) (store : Key → Value)
    (materialize : Local → List Fact → List Local) : OrderedGuardPipeline.Guard Local :=
  Supported.fresh (programObserver family) (authority, store) queryOf materialize

def cached (family : Authority → Query → Program Key Value (List Fact))
    (authority : Authority) (queryOf : Local → Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value (List Fact))
    (materialize : Local → List Fact → List Local) : OrderedGuardPipeline.Guard Local :=
  Supported.cached (programObserver family) (authority, store) queryOf entry materialize

/-- Caller state is supplied again to materialization on every invocation. -/
theorem cached_eq_fresh (family : Authority → Query → Program Key Value (List Fact))
    (authority : Authority) (queryOf : Local → Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value (List Fact)) (history : Recorded family entry)
    (materialize : Local → List Fact → List Local) :
    cached family authority queryOf store entry materialize =
      fresh family authority queryOf store materialize :=
  Supported.cached_eq_fresh (programObserver family) (authority, store) queryOf entry
    history materialize

/-- Replacing just the pure provider preserves all effectful continuations,
ordered refinements and the saved alternative. -/
theorem cached_guard_eval_exact
    (family : Authority → Query → Program Key Value (List Fact))
    (authority : Authority) (queryOf : Local → Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value (List Fact)) (history : Recorded family entry)
    (materialize : Local → List Fact → List Local) (body : Body Local World)
    (state : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (OrderedGuardPipeline.guard
      (cached family authority queryOf store entry materialize) body)
        state success failure saved world =
    eval (OrderedGuardPipeline.guard
      (fresh family authority queryOf store materialize) body)
        state success failure saved world :=
  Supported.cached_guard_eval_exact (programObserver family) (authority, store) queryOf
    entry history materialize body state success failure saved world

/-- The complete native guard pipeline may contain a cached provider while
keeping the same ordered refinement algebra. -/
theorem cached_in_pipeline_exact
    (family : Authority → Query → Program Key Value (List Fact))
    (authority : Authority) (queryOf : Local → Query) (store : Key → Value)
    (entry : Entry Authority Query Key Value (List Fact)) (history : Recorded family entry)
    (materialize : Local → List Fact → List Local)
    (before after : List (OrderedGuardPipeline.Guard Local)) (body : Body Local World) :
    OrderedGuardPipeline.pipeline
      (before ++ cached family authority queryOf store entry materialize :: after) body =
    OrderedGuardPipeline.pipeline
      (before ++ fresh family authority queryOf store materialize :: after) body :=
  Supported.cached_in_pipeline_exact (programObserver family) (authority, store) queryOf
    entry history materialize before after body

namespace Controls

inductive Mode where
  | infer
  | check (required : Nat)
  deriving DecidableEq, Repr

/-- Inference and checking use different query keys. The immutable facts keep
two equal occurrences instead of deduplicating successful declarations. -/
def family (_owner : Nat) (mode : Mode) : Program Nat Nat (List Nat) :=
  .read 0 fun fact => .pure <|
    match mode with
    | .infer => [fact, fact]
    | .check required => if fact = required then [fact, fact] else []

def store : Nat → Nat := fun _ => 7
def entry : Entry Nat Mode Nat Nat (List Nat) := populate family 1 .infer store
def materialize (caller : Nat) (facts : List Nat) : List Nat := facts.map (caller + ·)

def touching : Body Nat Nat := .effect (fun state world => (state, world + 1)) .done

/-- Reuse retains both proof occurrences; the consumer runs once for each. -/
theorem duplicate_consumers_keep_effects :
    ScopedCommit.run (OrderedGuardPipeline.guard
      (cached family 1 (fun _ => .infer) store entry materialize) touching) 10 0 =
        ([17, 17], 2) := rfl

/-- A new caller gets newly materialized refinements despite reusing facts. -/
theorem different_caller_refinements :
    cached family 1 (fun _ => .infer) store entry materialize 10 = [17, 17] ∧
      cached family 1 (fun _ => .infer) store entry materialize 20 = [27, 27] := by
  decide

/-- A bound checking requirement cannot reuse the inference outcome. -/
theorem bound_mode_does_not_reuse_inference :
    reuse family 1 (.check 8) store entry = ([], 1) := by decide

/-- Returning the cached binding list itself would capture the previous
caller and disagree with fresh materialization. -/
theorem caching_refinements_is_not_caching_facts :
    materialize 10 entry.value.answer ≠
      cached family 1 (fun _ => .infer) store entry materialize 20 := by decide

/-- A classifier that records each classification in the world and then
offers the refinements of the fresh provider. -/
def countingClassifier (next : Body Nat Nat) : Body Nat Nat :=
  .effect (fun state world => (state, world + 100))
    (OrderedGuardPipeline.guard (fresh family 1 (fun _ => .infer) store materialize) next)

/-- The cached guard does not replace a classifier that performs an effect:
both offer the same refinements, and the worlds they leave differ. The
adapter law is about a pure provider only. -/
theorem same_answers_do_not_erase_classifier_effect :
    (ScopedCommit.run (countingClassifier .done) 10 0).1 =
        (ScopedCommit.run (OrderedGuardPipeline.guard
          (cached family 1 (fun _ => .infer) store entry materialize) .done) 10 0).1 ∧
      ScopedCommit.run (countingClassifier .done) 10 0 ≠
        ScopedCommit.run (OrderedGuardPipeline.guard
          (cached family 1 (fun _ => .infer) store entry materialize) .done) 10 0 := by
  decide

end Controls

end Mettapedia.Machines.ReadCertifiedGuard
