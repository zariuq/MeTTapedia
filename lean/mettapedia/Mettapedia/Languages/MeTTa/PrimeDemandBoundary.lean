import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

/-!
# Prime demand boundary: rights, suspension observations, and contexts

This module specifies the small boundary shared by Prime's explicit
suspensions and first-class contexts.  It deliberately does not claim to be a
complete evaluator.

* Public suspension rights are `force` and `inspect`.  Restriction either
  returns the requested subset or rejects it; it cannot add authority.
* Suspension identity, origin equality, and result equivalence are three
  different relations.  The first implies the second and the second implies
  the third.  Concrete witnesses show both inclusions can be strict.
* A context is an immutable parent-linked chain.  Lookup uses the newest
  binding; absence is data.  Its public window contains names and immutable
  origins, never cells.
* The primary dynamics is a small-step relation.  Context binding allocates an
  unevaluated cell, lookup demands the referenced cell, and evaluation caches
  one branch result before it is returned.  A second demand therefore returns
  that same cached result.

The native correspondence still has to map runtime cells, snapshots, and
receipts into these mathematical objects.  Causal publication remains in
`PrimeNeedWorlds`; no identification between the two representations is made
here by definition.
-/

namespace Mettapedia.Languages.MeTTa.PrimeDemandBoundary

/-! ## Rights form a fail-closed attenuation boundary -/

inductive Right where
  | force
  | inspect
deriving DecidableEq, Repr

abbrev Rights := Finset Right

/-- Restriction succeeds exactly when all requested rights were already held. -/
def restrict? (current requested : Rights) : Option Rights :=
  if requested ⊆ current then some requested else none

theorem restrict_some_subset {current requested granted : Rights}
    (h : restrict? current requested = some granted) :
    granted ⊆ current := by
  unfold restrict? at h
  split at h <;> simp_all

theorem restrict_some_eq_requested {current requested granted : Rights}
    (h : restrict? current requested = some granted) :
    granted = requested := by
  unfold restrict? at h
  split at h <;> simp_all

theorem restrict_escalation_fails {current requested : Rights}
    (h : ¬ requested ⊆ current) :
    restrict? current requested = none := by
  simp [restrict?, h]

theorem restrict_same (rights : Rights) :
    restrict? rights rights = some rights := by
  simp [restrict?]

/-! ## Three observation relations -/

/-- An abstract pure-fragment account of immutable origins and their possible
observable results.  `observations` is set-valued so the model does not erase
nondeterminism.  This deliberately does not assert that origin equality is a
congruence for effects, authority, or open terms; those require a separate
runtime correspondence theorem. -/
structure SuspensionModel (Cell Origin Result : Type*) where
  origin : Cell → Origin
  observations : Origin → Set Result

def sameSuspension {Cell : Type*} (left right : Cell) : Prop :=
  left = right

def sameOrigin {Cell Origin Result : Type*}
    (model : SuspensionModel Cell Origin Result)
    (left right : Cell) : Prop :=
  model.origin left = model.origin right

def resultEquivalent {Cell Origin Result : Type*}
    (model : SuspensionModel Cell Origin Result)
    (left right : Cell) : Prop :=
  model.observations (model.origin left) =
    model.observations (model.origin right)

def RelationIncluded {α : Type*}
    (finer coarser : α → α → Prop) : Prop :=
  ∀ ⦃left right⦄, finer left right → coarser left right

def StrictlyFiner {α : Type*}
    (finer coarser : α → α → Prop) : Prop :=
  RelationIncluded finer coarser ∧
    ∃ left right, coarser left right ∧ ¬ finer left right

theorem sameSuspension_in_sameOrigin
    {Cell Origin Result : Type*}
    (model : SuspensionModel Cell Origin Result) :
    RelationIncluded sameSuspension (sameOrigin model) := by
  intro left right h
  subst right
  rfl

theorem sameOrigin_in_resultEquivalent
    {Cell Origin Result : Type*}
    (model : SuspensionModel Cell Origin Result) :
    RelationIncluded (sameOrigin model) (resultEquivalent model) := by
  intro left right h
  simp only [resultEquivalent]
  rw [h]

inductive DemoCell where
  | first
  | second
  | third
deriving DecidableEq

inductive DemoOrigin where
  | shared
  | other
deriving DecidableEq

inductive DemoResult where
  | done
deriving DecidableEq

def demoModel : SuspensionModel DemoCell DemoOrigin DemoResult where
  origin
    | .first => .shared
    | .second => .shared
    | .third => .other
  observations _ := {.done}

/-- Distinct cells can carry the same immutable origin. -/
theorem demo_sameSuspension_strictly_finer :
    StrictlyFiner sameSuspension (sameOrigin demoModel) := by
  constructor
  · exact sameSuspension_in_sameOrigin demoModel
  · refine ⟨DemoCell.first, DemoCell.second, ?_, ?_⟩
    · rfl
    · simp [sameSuspension]

/-- Different origins can nevertheless have equivalent observable results. -/
theorem demo_sameOrigin_strictly_finer :
    StrictlyFiner (sameOrigin demoModel) (resultEquivalent demoModel) := by
  constructor
  · exact sameOrigin_in_resultEquivalent demoModel
  · refine ⟨DemoCell.first, DemoCell.third, ?_, ?_⟩
    · rfl
    · simp [sameOrigin, demoModel]

/-! ## Persistent first-class contexts -/

inductive Lookup (Name Ref : Type*) where
  | missing (key : Name)
  | found (ref : Ref)
deriving DecidableEq, Repr

/-- The semantic representation is a persistent parent-linked chain. -/
inductive Context (Name Ref : Type*) where
  | empty
  | bind (parent : Context Name Ref) (key : Name) (ref : Ref)
deriving DecidableEq, Repr

namespace Context

variable {Name Ref Origin : Type*} [DecidableEq Name]

def lookup : Context Name Ref → Name → Lookup Name Ref
  | .empty, key => .missing key
  | .bind parent bound ref, key =>
      if key = bound then .found ref else lookup parent key

def entries : Context Name Ref → List (Name × Ref)
  | .empty => []
  | .bind parent key ref => (key, ref) :: entries parent

def depth : Context Name Ref → Nat
  | .empty => 0
  | .bind parent _ _ => parent.depth + 1

structure ViewEntry (Name Origin : Type*) where
  key : Name
  origin : Origin
deriving DecidableEq, Repr

structure Window (Name Origin : Type*) where
  shown : Nat
  total : Nat
  entries : List (ViewEntry Name Origin)
deriving DecidableEq, Repr

/-- A bounded public projection.  Its result type has no place for a cell. -/
def window (origin : Ref → Origin) (context : Context Name Ref)
    (limit : Nat) : Window Name Origin :=
  let visible := context.entries.take limit
  { shown := visible.length
    total := context.depth
    entries := visible.map fun entry =>
      { key := entry.1, origin := origin entry.2 } }

@[simp] theorem lookup_empty (key : Name) :
    lookup (Context.empty : Context Name Ref) key = .missing key :=
  rfl

@[simp] theorem lookup_bind_same (parent : Context Name Ref)
    (key : Name) (ref : Ref) :
    lookup (.bind parent key ref) key = .found ref := by
  simp [lookup]

@[simp] theorem lookup_bind_other (parent : Context Name Ref)
    {bound key : Name} (ref : Ref) (h : key ≠ bound) :
    lookup (.bind parent bound ref) key = lookup parent key := by
  simp [lookup, h]

/-- Newest binding wins, independently of older occurrences. -/
theorem newest_shadows (parent : Context Name Ref)
    (key : Name) (oldRef newRef : Ref) :
    lookup (.bind (.bind parent key oldRef) key newRef) key =
      .found newRef := by
  simp

omit [DecidableEq Name] in
@[simp] theorem window_zero (origin : Ref → Origin)
    (context : Context Name Ref) :
    window origin context 0 =
      { shown := 0, total := context.depth, entries := [] } := by
  simp [window]

omit [DecidableEq Name] in
theorem window_entries_length (origin : Ref → Origin)
    (context : Context Name Ref) (limit : Nat) :
    (window origin context limit).entries.length =
      (window origin context limit).shown := by
  simp [window]

omit [DecidableEq Name] in
theorem window_shown_le_limit (origin : Ref → Origin)
    (context : Context Name Ref) (limit : Nat) :
    (window origin context limit).shown ≤ limit := by
  simp [window]

omit [DecidableEq Name] in
@[simp] theorem window_bind_succ (origin : Ref → Origin)
    (parent : Context Name Ref) (key : Name) (ref : Ref) (limit : Nat) :
    window origin (.bind parent key ref) (limit + 1) =
      { shown := (parent.entries.take limit).length + 1
        total := parent.depth + 1
        entries :=
          { key := key, origin := origin ref } ::
            (parent.entries.take limit).map fun entry =>
              { key := entry.1, origin := origin entry.2 } } := by
  simp [window, entries, depth, Nat.add_comm]

end Context

/-! ## Small-step demand machine -/

/-- Internal context bindings retain cell identity and immutable origin.  The
public `Context.window` projection uses only `origin`. -/
structure BindingRef (Cell Term : Type*) where
  cell : Cell
  origin : Term
deriving DecidableEq, Repr

inductive Outcome (Value Fault : Type*) where
  | value (value : Value)
  | fault (fault : Fault)
deriving DecidableEq, Repr

inductive Cache (Value Fault : Type*) where
  | unevaluated
  | blackhole
  | done (outcome : Outcome Value Fault)
deriving DecidableEq, Repr

structure CellRecord (Term Value Fault : Type*) where
  origin : Term
  cache : Cache Value Fault
deriving DecidableEq, Repr

abbrev Heap (Cell Term Value Fault : Type*) :=
  Cell → Option (CellRecord Term Value Fault)

namespace Heap

variable {Cell Term Value Fault : Type*} [DecidableEq Cell]

def write (heap : Heap Cell Term Value Fault) (cell : Cell)
    (record : CellRecord Term Value Fault) : Heap Cell Term Value Fault :=
  Function.update heap cell (some record)

@[simp] theorem write_same (heap : Heap Cell Term Value Fault)
    (cell : Cell) (record : CellRecord Term Value Fault) :
    write heap cell record cell = some record := by
  simp [write]

theorem write_other (heap : Heap Cell Term Value Fault)
    {cell other : Cell} (record : CellRecord Term Value Fault)
    (h : other ≠ cell) :
    write heap cell record other = heap other := by
  simp [write, h]

end Heap

structure Suspension (Cell : Type*) where
  cell : Cell
  rights : Rights
deriving DecidableEq

inductive Control (Name Cell Term Value Fault : Type*) where
  | bind (context : Context Name (BindingRef Cell Term))
      (key : Name) (term : Term)
  | get (context : Context Name (BindingRef Cell Term)) (key : Name)
  | view (context : Context Name (BindingRef Cell Term)) (limit : Nat)
  | contextValue (context : Context Name (BindingRef Cell Term))
  | demand (cell : Cell)
  | force (suspension : Suspension Cell)
  | observe (suspension : Suspension Cell)
  | evaluate (cell : Cell) (origin : Term)
  | returned (outcome : Outcome Value Fault)
  | missing (key : Name)
  | window (window : Context.Window Name Term)
  | originView (origin : Term)
  | denied (right : Right)
  | outOfScope (cell : Cell)
  | cycle (cell : Cell)
deriving DecidableEq

structure Config (Name Cell Term Value Fault : Type*) where
  heap : Heap Cell Term Value Fault
  control : Control Name Cell Term Value Fault

/-- One boundary step.  `eval origin outcome` may be nondeterministic; each
chosen outcome is cached in its own successor heap. -/
inductive Step
    {Name Cell Term Value Fault : Type*}
    [DecidableEq Name] [DecidableEq Cell]
    (eval : Term → Outcome Value Fault → Prop) :
    Config Name Cell Term Value Fault →
      Config Name Cell Term Value Fault → Prop where
  | bind {heap context key term fresh}
      (freshCell : heap fresh = none) :
      Step eval
        ⟨heap, .bind context key term⟩
        ⟨Heap.write heap fresh
            { origin := term, cache := .unevaluated },
          .contextValue
            (.bind context key { cell := fresh, origin := term })⟩
  | getFound {heap context key ref}
      (found : context.lookup key = .found ref) :
      Step eval ⟨heap, .get context key⟩ ⟨heap, .demand ref.cell⟩
  | getMissing {heap context key}
      (missing : context.lookup key = .missing key) :
      Step eval ⟨heap, .get context key⟩ ⟨heap, .missing key⟩
  | view {heap context limit} :
      Step eval ⟨heap, .view context limit⟩
        ⟨heap, .window (context.window BindingRef.origin limit)⟩
  | forceAllowed {heap suspension record}
      (allowed : Right.force ∈ suspension.rights)
      (present : heap suspension.cell = some record) :
      Step eval ⟨heap, .force suspension⟩
        ⟨heap, .demand suspension.cell⟩
  | forceDenied {heap suspension}
      (denied : Right.force ∉ suspension.rights) :
      Step eval ⟨heap, .force suspension⟩ ⟨heap, .denied .force⟩
  | forceOutOfScope {heap suspension}
      (allowed : Right.force ∈ suspension.rights)
      (missing : heap suspension.cell = none) :
      Step eval ⟨heap, .force suspension⟩
        ⟨heap, .outOfScope suspension.cell⟩
  | observeAllowed {heap suspension record}
      (allowed : Right.inspect ∈ suspension.rights)
      (present : heap suspension.cell = some record) :
      Step eval ⟨heap, .observe suspension⟩
        ⟨heap, .originView record.origin⟩
  | observeDenied {heap suspension}
      (denied : Right.inspect ∉ suspension.rights) :
      Step eval ⟨heap, .observe suspension⟩
        ⟨heap, .denied .inspect⟩
  | observeOutOfScope {heap suspension}
      (allowed : Right.inspect ∈ suspension.rights)
      (missing : heap suspension.cell = none) :
      Step eval ⟨heap, .observe suspension⟩
        ⟨heap, .outOfScope suspension.cell⟩
  | demandUnevaluated {heap cell record}
      (present : heap cell = some record)
      (unevaluated : record.cache = .unevaluated) :
      Step eval ⟨heap, .demand cell⟩
        ⟨Heap.write heap cell { record with cache := .blackhole },
          .evaluate cell record.origin⟩
  | demandCached {heap cell record outcome}
      (present : heap cell = some record)
      (cached : record.cache = .done outcome) :
      Step eval ⟨heap, .demand cell⟩ ⟨heap, .returned outcome⟩
  | demandBlackhole {heap cell record}
      (present : heap cell = some record)
      (blackhole : record.cache = .blackhole) :
      Step eval ⟨heap, .demand cell⟩ ⟨heap, .cycle cell⟩
  | evaluateDone {heap cell record outcome}
      (present : heap cell = some record)
      (blackhole : record.cache = .blackhole)
      (evaluates : eval record.origin outcome) :
      Step eval ⟨heap, .evaluate cell record.origin⟩
        ⟨Heap.write heap cell { record with cache := .done outcome },
          .returned outcome⟩

section StepLaws

variable {Name Cell Term Value Fault : Type*}
variable [DecidableEq Name] [DecidableEq Cell]
variable (eval : Term → Outcome Value Fault → Prop)

/-- Binding is lazy: the new cell contains the origin and no result. -/
theorem bind_allocates_unevaluated
    (heap : Heap Cell Term Value Fault)
    (context : Context Name (BindingRef Cell Term))
    (key : Name) (term : Term) (fresh : Cell)
    (hFresh : heap fresh = none) :
    let record : CellRecord Term Value Fault :=
      { origin := term, cache := .unevaluated }
    let nextHeap := Heap.write heap fresh record
    nextHeap fresh = some record ∧
      Step eval
        ⟨heap, .bind context key term⟩
        ⟨nextHeap,
          .contextValue
            (.bind context key { cell := fresh, origin := term })⟩ := by
  dsimp
  exact ⟨Heap.write_same _ _ _, Step.bind hFresh⟩

/-- Persistent extension does not alter any existing, different cell. -/
theorem bind_preserves_other_cell
    (heap : Heap Cell Term Value Fault)
    (term : Term) {fresh other : Cell} (h : other ≠ fresh) :
    Heap.write heap fresh { origin := term, cache := .unevaluated } other =
      heap other :=
  Heap.write_other _ _ h

/-- Lookup of a shadowed name demands the newest cell. -/
theorem get_newest_step
    (heap : Heap Cell Term Value Fault)
    (parent : Context Name (BindingRef Cell Term))
    (key : Name) (oldRef newRef : BindingRef Cell Term) :
    Step eval
      ⟨heap, .get (.bind (.bind parent key oldRef) key newRef) key⟩
      ⟨heap, .demand newRef.cell⟩ := by
  exact Step.getFound (by simp)

/-- Absence is an ordinary result constructor and leaves the heap untouched. -/
theorem get_empty_returns_missing
    (heap : Heap Cell Term Value Fault) (key : Name) :
    Step eval ⟨heap, .get .empty key⟩ ⟨heap, .missing key⟩ := by
  exact Step.getMissing rfl

/-- Context observation is non-forcing: a view step has the identical heap. -/
theorem view_preserves_heap
    (heap : Heap Cell Term Value Fault)
    (context : Context Name (BindingRef Cell Term)) (limit : Nat) :
    Step eval ⟨heap, .view context limit⟩
      ⟨heap, .window (context.window BindingRef.origin limit)⟩ :=
  Step.view

/-- Once evaluation chooses a branch outcome, the successor heap caches that
outcome and the next demand returns exactly it without changing the heap. -/
theorem evaluate_then_demand_same
    (heap : Heap Cell Term Value Fault) (cell : Cell)
    (record : CellRecord Term Value Fault)
    (outcome : Outcome Value Fault)
    (hPresent : heap cell = some record)
    (hBlackhole : record.cache = .blackhole)
    (hEval : eval record.origin outcome) :
    let cachedHeap :=
      Heap.write heap cell { record with cache := .done outcome }
    Step eval
        (⟨heap, .evaluate cell record.origin⟩ :
          Config Name Cell Term Value Fault)
        (⟨cachedHeap, .returned outcome⟩ :
          Config Name Cell Term Value Fault) ∧
      Step eval
        (⟨cachedHeap, .demand cell⟩ :
          Config Name Cell Term Value Fault)
        (⟨cachedHeap, .returned outcome⟩ :
          Config Name Cell Term Value Fault) := by
  dsimp
  constructor
  · exact Step.evaluateDone hPresent hBlackhole hEval
  · refine Step.demandCached
      (record := { record with cache := .done outcome }) ?_ rfl
    simp [Heap.write]

/-- Inspecting an allowed suspension reveals its immutable origin without
changing the cache or any other heap component. -/
theorem observe_preserves_heap
    (heap : Heap Cell Term Value Fault) (suspension : Suspension Cell)
    (record : CellRecord Term Value Fault)
    (hInspect : Right.inspect ∈ suspension.rights)
    (hPresent : heap suspension.cell = some record) :
    Step eval
      (⟨heap, .observe suspension⟩ :
        Config Name Cell Term Value Fault)
      (⟨heap, .originView record.origin⟩ :
        Config Name Cell Term Value Fault) :=
  Step.observeAllowed hInspect hPresent

end StepLaws

/-! ## Positive and negative boundary examples -/

example :
    restrict? ({Right.force, Right.inspect} : Rights) {Right.inspect} =
      some {Right.inspect} := by
  decide

/-- An inspect-only handle cannot acquire force authority. -/
example :
    restrict? ({Right.inspect} : Rights) {Right.force} = none := by
  decide

/-- A raw missing lookup cannot invent a cell reference. -/
example :
    Context.lookup
        (Context.empty : Context Nat (BindingRef Nat Nat)) 7 =
      .missing 7 := by
  rfl

end Mettapedia.Languages.MeTTa.PrimeDemandBoundary
