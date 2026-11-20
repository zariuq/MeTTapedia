import Mettapedia.Machines.ReadOnlySpecialization
import Mettapedia.Machines.OrderedGuardPipeline
import Mettapedia.GSLT.Distinction.OrderedSimulation

/-!
# Bounded driving and folding of read-certified configurations

Configuration descriptors are pure programs in the existing adaptive
read language. The compiler can describe host actions as data for the
host to execute at its original boundary. Driving follows a successor only when its
descriptor has become statically known, and folding shares a residual for
each equal configuration. A repeated successor remains a repeated edge.

The graph is private to a semantic authority (program, profile, and any
other non-memory parameters of its interpretation). An entry checks both
that authority and its actual ordered read footprint. An absent or stale
entry dispatches the current configuration to the source interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Supercompilation

open ReadOnlyQuery ReadOnlySpecialization
open Mettapedia.GSLT.Distinction

universe u v w x y

/-- One public boundary and its ordered successor occurrences. `View` can
expose replies, designated suspension reasons or action descriptors. -/
structure Boundary (Config : Type u) (View : Type v) where
  halted : Bool
  successors : List Config
  view : View
  deriving DecidableEq, Repr

abbrev Description (Config : Type u) (Key : Type v) (Value : Type w) (View : Type x) :=
  Config → Program Key Value (Boundary Config View)

variable {Config : Type u} {Key : Type v} {Value : Type w} {View : Type x}

structure Block (describe : Description Config Key Value View) where
  config : Config
  residual : Residual (describe config)

abbrev Graph (describe : Description Config Key Value View) := List (Block describe)

namespace Graph

variable {describe : Description Config Key Value View} [DecidableEq Config]

def lookup : Graph describe → (config : Config) → Option (Residual (describe config))
  | [], _ => none
  | block :: rest, config =>
    if same : block.config = config then some (same ▸ block.residual)
    else lookup rest config

theorem lookup_none_iff (blocks : Graph describe) (config : Config) :
    lookup blocks config = none ↔ config ∉ blocks.map Block.config := by
  induction blocks with
  | nil => simp [lookup]
  | cons block rest ih =>
    by_cases same : block.config = config
    · simp [lookup, same]
    · have different := Ne.symm same
      simp [lookup, same, different, ih]

/-- Only a completely driven descriptor supplies more configurations at
specialization time. Reading a live value is left to the residual. -/
def discovered (block : Block describe) : List Config :=
  match block.residual.suffix with
  | .pure boundary => if boundary.halted then [] else boundary.successors
  | .read _ _ => []

/-- Charge one visit per pending configuration, including those that fold
to an existing block. -/
def drive (static : Key → Bool) (memory : Key → Value) (reads : Nat) :
    Nat → List Config → Graph describe → Graph describe
  | 0, _, blocks => blocks
  | _ + 1, [], blocks => blocks
  | visits + 1, config :: pending, blocks =>
    match lookup blocks config with
    | some _ => drive static memory reads visits pending blocks
    | none =>
      let block : Block describe :=
        ⟨config, ReadOnlySpecialization.drive static memory reads (describe config)⟩
      drive static memory reads visits (discovered block ++ pending) (block :: blocks)

def compile (describe : Description Config Key Value View) (static : Key → Bool)
    (memory : Key → Value) (reads visits : Nat) (roots : List Config) : Graph describe :=
  drive static memory reads visits roots []

theorem drive_size_le (static : Key → Bool) (memory : Key → Value) (reads visits : Nat)
    (pending : List Config) (blocks : Graph describe) :
    (drive static memory reads visits pending blocks).length ≤ blocks.length + visits := by
  induction visits generalizing pending blocks with
  | zero => simp [drive]
  | succ visits ih =>
    cases pending with
    | nil => simp [drive]
    | cons config pending =>
      cases found : lookup blocks config with
      | some residual =>
        simp only [drive, found]
        exact (ih pending blocks).trans (by omega)
      | none =>
        simp only [drive, found]
        exact (ih _ _).trans (by simp; omega)

theorem drive_nodup (static : Key → Bool) (memory : Key → Value) (reads visits : Nat)
    (pending : List Config) (blocks : Graph describe) (distinct : (blocks.map Block.config).Nodup) :
    ((drive static memory reads visits pending blocks).map Block.config).Nodup := by
  induction visits generalizing pending blocks with
  | zero => exact distinct
  | succ visits ih =>
    cases pending with
    | nil => exact distinct
    | cons config pending =>
      cases found : lookup blocks config with
      | some residual =>
        simp only [drive, found]
        exact ih pending blocks distinct
      | none =>
        simp only [drive, found]
        exact ih _ _ (List.nodup_cons.mpr ⟨(lookup_none_iff _ _).mp found, distinct⟩)

theorem compile_size_le (describe : Description Config Key Value View)
    (static : Key → Bool) (memory : Key → Value) (reads visits : Nat) (roots : List Config) :
    (compile describe static memory reads visits roots).length ≤ visits := by
  simpa [compile] using drive_size_le (describe := describe) static memory reads visits roots []

theorem compile_nodup (describe : Description Config Key Value View)
    (static : Key → Bool) (memory : Key → Value) (reads visits : Nat) (roots : List Config) :
    ((compile describe static memory reads visits roots).map Block.config).Nodup :=
  drive_nodup static memory reads visits roots [] List.nodup_nil

end Graph

variable {Authority : Type y} [DecidableEq Config] [DecidableEq Value] [DecidableEq Authority]

/-- The read check validates the prefix at the current boundary. The
remaining live reads operate under that same selected memory. -/
def enter? (describe : Authority → Description Config Key Value View)
    (compiled : Authority) (blocks : Graph (describe compiled))
    (current : Authority) (memory : Key → Value) (config : Config) :
    Option (Observation Key Value (Boundary Config View)) :=
  if compiled = current then
    match blocks.lookup config with
    | some residual => residual.tryRun memory
    | none => none
  else none

theorem enter_sound (describe : Authority → Description Config Key Value View)
    (compiled : Authority) (blocks : Graph (describe compiled))
    (current : Authority) (memory : Key → Value) (config : Config)
    {result : Observation Key Value (Boundary Config View)}
    (entered : enter? describe compiled blocks current memory config = some result) :
    result = run memory (describe current config) := by
  unfold enter? at entered
  split at entered
  · rename_i same
    subst current
    split at entered
    · exact Residual.tryRun_sound _ _ entered
    · cases entered
  · cases entered

def dispatch (describe : Authority → Description Config Key Value View)
    (compiled : Authority) (blocks : Graph (describe compiled))
    (current : Authority) (memory : Key → Value) (config : Config) :
    Observation Key Value (Boundary Config View) :=
  match enter? describe compiled blocks current memory config with
  | some result => result
  | none => run memory (describe current config)

theorem dispatch_exact (describe : Authority → Description Config Key Value View)
    (compiled : Authority) (blocks : Graph (describe compiled))
    (current : Authority) (memory : Key → Value) (config : Config) :
    dispatch describe compiled blocks current memory config = run memory (describe current config) := by
  unfold dispatch
  split
  · exact enter_sound _ _ _ _ _ _ ‹_›
  · rfl

def ordered (readBoundary : Config → Boundary Config View) : OrderedSystem Config where
  step := fun config => (readBoundary config).successors
  halted := fun config => (readBoundary config).halted

/-- Ordered scheduler clients can consume the residual descriptors at every
boundary, including at a frontier left by an earlier partial run. -/
theorem ordered_dispatch_eq (describe : Authority → Description Config Key Value View)
    (compiled : Authority) (blocks : Graph (describe compiled))
    (current : Config → Authority) (memory : Config → Key → Value) :
    ordered (fun config =>
      (dispatch describe compiled blocks (current config) (memory config) config).answer) =
    ordered (fun config => (run (memory config) (describe (current config) config)).answer) := by
  congr 1
  funext config
  rw [dispatch_exact]

/-- Install the residual at the retained frontier after source execution.
The budgets count semantic advances of the same scheduler. -/
theorem resume_exact (describe : Authority → Description Config Key Value View)
    (compiled : Authority) (blocks : Graph (describe compiled))
    (current : Config → Authority) (memory : Config → Key → Value)
    (before after : Nat) (roots : List Config) :
    let source := ordered (fun config => (run (memory config) (describe (current config) config)).answer)
    let selected := ordered (fun config =>
      (dispatch describe compiled blocks (current config) (memory config) config).answer)
    selected.runFrontier after (source.runFrontier before roots) =
      source.runFrontier (before + after) roots := by
  dsimp only
  rw [ordered_dispatch_eq]
  exact (OrderedSystem.runFrontier_add _ before after roots).symm

/-- Reuse in an existing pure-guard position cannot duplicate a body effect,
discard a saved alternative, or change a binding supplied to the body. -/
theorem dispatch_guard_eval {Local World Result : Type}
    (describe : Authority → Description Config Key Value View)
    (compiled : Authority) (blocks : Graph (describe compiled))
    (current : Authority) (memory : Key → Value) (configOf : Local → Config)
    (materialize : Local → View → List Local) (next : ScopedCommit.Body Local World)
    (state : Local) (success : ScopedCommit.Success Local World Result)
    (failure saved : ScopedCommit.Failure World Result) (world : World) :
    ScopedCommit.eval (OrderedGuardPipeline.guard (fun localState =>
      materialize localState (dispatch describe compiled blocks current memory
        (configOf localState)).answer.view) next) state success failure saved world =
    ScopedCommit.eval (OrderedGuardPipeline.guard (fun localState =>
      materialize localState (run memory (describe current (configOf localState))).answer.view)
        next) state success failure saved world := by
  apply OrderedGuardPipeline.guard_congr
  rw [dispatch_exact]

end Mettapedia.Machines.Supercompilation
