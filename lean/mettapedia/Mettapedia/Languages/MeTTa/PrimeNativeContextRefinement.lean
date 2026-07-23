import Mettapedia.Languages.MeTTa.PrimeDemandBoundary

/-!
# Prime native context refinement

This module gives the parent-linked runtime representation an independent
mathematical model and interprets it into `PrimeDemandBoundary.Context`.  The
native model includes the cached depth stored by each frame; correspondence of
bounded views therefore requires a real representation invariant.

The result is a structural runtime refinement only.  It does not identify a
runtime context with a typing context or establish Curry--Howard soundness.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNativeContextRefinement

open PrimeDemandBoundary

/-- A native-style immutable context spine.  `storedDepth` models the cached
depth field in a runtime frame rather than recomputing it by recursion. -/
inductive NativeContext (Name Ref : Type*) where
  | empty
  | frame (parent : NativeContext Name Ref) (key : Name) (ref : Ref)
      (storedDepth : Nat)
deriving DecidableEq, Repr

namespace NativeContext

variable {Name Ref Cell Origin Key Term : Type*}

def cachedDepth : NativeContext Name Ref → Nat
  | .empty => 0
  | .frame _ _ _ storedDepth => storedDepth

/-- Native extension computes, stores, and shares the parent frame. -/
def bind (parent : NativeContext Name Ref) (key : Name) (ref : Ref) :
    NativeContext Name Ref :=
  .frame parent key ref (parent.cachedDepth + 1)

/-- The cached depth is trustworthy exactly when every parent frame is also
trustworthy and the current cache extends it by one. -/
def WellFormed : NativeContext Name Ref → Prop
  | .empty => True
  | .frame parent _ _ storedDepth =>
      parent.WellFormed ∧ storedDepth = parent.cachedDepth + 1

def structuralDepth : NativeContext Name Ref → Nat
  | .empty => 0
  | .frame parent _ _ _ => parent.structuralDepth + 1

def entries : NativeContext Name Ref → List (Name × Ref)
  | .empty => []
  | .frame parent key ref _ => (key, ref) :: parent.entries

def get [DecidableEq Name] : NativeContext Name Ref → Name → Option Ref
  | .empty, _ => none
  | .frame parent bound ref _, key =>
      if key = bound then some ref else parent.get key

/-- A native reference is interpreted as a semantic binding reference by two
independent projections. -/
def interpretRef (cellOf : Ref → Cell) (originOf : Ref → Origin)
    (ref : Ref) : BindingRef Cell Origin :=
  { cell := cellOf ref, origin := originOf ref }

def translate (cellOf : Ref → Cell) (originOf : Ref → Origin) :
    NativeContext Name Ref → Context Name (BindingRef Cell Origin)
  | .empty => .empty
  | .frame parent key ref _ =>
      .bind (translate cellOf originOf parent) key
        (interpretRef cellOf originOf ref)

def translateLookup (cellOf : Ref → Cell) (originOf : Ref → Origin)
    (key : Name) : Option Ref → Lookup Name (BindingRef Cell Origin)
  | none => .missing key
  | some ref => .found (interpretRef cellOf originOf ref)

structure NativeViewEntry (Name Ref : Type*) where
  key : Name
  ref : Ref
deriving DecidableEq, Repr

structure NativeWindow (Name Ref : Type*) where
  shown : Nat
  total : Nat
  entries : List (NativeViewEntry Name Ref)
deriving DecidableEq, Repr

/-- The native bounded view enumerates newest frames and retains references
only until the explicit public interpretation below. -/
def view (context : NativeContext Name Ref) (limit : Nat) :
    NativeWindow Name Ref :=
  let visible := context.entries.take limit
  { shown := visible.length
    total := context.cachedDepth
    entries := visible.map fun entry =>
      { key := entry.1, ref := entry.2 } }

/-- Public observation forgets cell identity and exposes immutable origins. -/
def interpretWindow (originOf : Ref → Origin)
    (window : NativeWindow Name Ref) : Context.Window Name Origin :=
  { shown := window.shown
    total := window.total
    entries := window.entries.map fun entry =>
      { key := entry.key, origin := originOf entry.ref } }

@[simp] theorem bind_wellFormed_iff
    (parent : NativeContext Name Ref) (key : Name) (ref : Ref) :
    (bind parent key ref).WellFormed ↔ parent.WellFormed := by
  simp [bind, WellFormed]

theorem wellFormed_cachedDepth_eq_structuralDepth
    {context : NativeContext Name Ref} (wellFormed : context.WellFormed) :
    context.cachedDepth = context.structuralDepth := by
  induction context with
  | empty => rfl
  | frame parent key ref storedDepth ih =>
      rcases wellFormed with ⟨parentWellFormed, depthStep⟩
      simp only [cachedDepth, structuralDepth]
      rw [depthStep, ih parentWellFormed]

@[simp] theorem translate_bind
    (cellOf : Ref → Cell) (originOf : Ref → Origin)
    (parent : NativeContext Name Ref) (key : Name) (ref : Ref) :
    translate cellOf originOf (bind parent key ref) =
      .bind (translate cellOf originOf parent) key
        (interpretRef cellOf originOf ref) :=
  rfl

theorem translate_depth
    (cellOf : Ref → Cell) (originOf : Ref → Origin)
    (context : NativeContext Name Ref) :
    (translate cellOf originOf context).depth = context.structuralDepth := by
  induction context with
  | empty => rfl
  | frame parent key ref storedDepth ih =>
      simp [translate, Context.depth, structuralDepth, ih]

theorem translate_depth_eq_cached
    (cellOf : Ref → Cell) (originOf : Ref → Origin)
    {context : NativeContext Name Ref} (wellFormed : context.WellFormed) :
    (translate cellOf originOf context).depth = context.cachedDepth := by
  rw [translate_depth, ← wellFormed_cachedDepth_eq_structuralDepth wellFormed]

theorem translate_entries
    (cellOf : Ref → Cell) (originOf : Ref → Origin)
    (context : NativeContext Name Ref) :
    (translate cellOf originOf context).entries =
      context.entries.map fun entry =>
        (entry.1, interpretRef cellOf originOf entry.2) := by
  induction context with
  | empty => rfl
  | frame parent key ref storedDepth ih =>
      simp [translate, Context.entries, entries, ih]

/-- Native lookup and semantic lookup agree operation by operation. -/
theorem get_refines_lookup [DecidableEq Name]
    (cellOf : Ref → Cell) (originOf : Ref → Origin)
    (context : NativeContext Name Ref) (key : Name) :
    Context.lookup (translate cellOf originOf context) key =
      translateLookup cellOf originOf key (context.get key) := by
  induction context with
  | empty => rfl
  | frame parent bound ref storedDepth ih =>
      by_cases same : key = bound
      · subst key
        simp [translate, get, translateLookup]
      · simp [translate, get, same, ih]

/-- A valid cached spine produces exactly the semantic bounded origin view. -/
theorem view_refines_window
    (cellOf : Ref → Cell) (originOf : Ref → Origin)
    {context : NativeContext Name Ref} (wellFormed : context.WellFormed)
    (limit : Nat) :
    interpretWindow originOf (context.view limit) =
      Context.window BindingRef.origin
        (translate cellOf originOf context) limit := by
  have depthAgreement :=
    translate_depth_eq_cached cellOf originOf wellFormed
  have entriesAgreement := translate_entries cellOf originOf context
  simp [interpretWindow, view, Context.window, depthAgreement,
    entriesAgreement, interpretRef, Function.comp_def]

@[simp] theorem get_bind_same [DecidableEq Name]
    (parent : NativeContext Name Ref) (key : Name) (ref : Ref) :
    (bind parent key ref).get key = some ref := by
  simp [bind, get]

@[simp] theorem get_bind_other [DecidableEq Name]
    (parent : NativeContext Name Ref) {bound key : Name} (ref : Ref)
    (different : key ≠ bound) :
    (bind parent bound ref).get key = parent.get key := by
  simp [bind, get, different]

/-- Shadowing changes the child lookup without mutating the parent value. -/
theorem newest_shadows_parent_unchanged [DecidableEq Name]
    (parent : NativeContext Name Ref) (key : Name) (oldRef newRef : Ref) :
    let base := bind parent key oldRef
    let child := bind base key newRef
    base.get key = some oldRef ∧ child.get key = some newRef := by
  simp

/-- Missing lookup is translated to explicit missing data. -/
theorem empty_get_refines_missing [DecidableEq Name]
    (cellOf : Ref → Cell) (originOf : Ref → Origin) (key : Name) :
    Context.lookup
        (translate cellOf originOf (NativeContext.empty : NativeContext Name Ref))
        key = .missing key := by
  rfl

theorem view_shown_le_limit (context : NativeContext Name Ref) (limit : Nat) :
    (context.view limit).shown ≤ limit := by
  simp [view]

/-- Changing the private cell interpretation cannot change a public origin
window. -/
theorem translated_window_ignores_cell_identity
    (leftCell rightCell : Ref → Cell) (originOf : Ref → Origin)
    {context : NativeContext Name Ref} (wellFormed : context.WellFormed)
    (limit : Nat) :
    Context.window BindingRef.origin
        (translate leftCell originOf context) limit =
      Context.window BindingRef.origin
        (translate rightCell originOf context) limit := by
  rw [← view_refines_window leftCell originOf wellFormed]
  rw [← view_refines_window rightCell originOf wellFormed]

/-- Repeated lookup of one binding denotes exactly one hidden cell. -/
theorem repeated_get_preserves_cell [DecidableEq Name]
    (cellOf : Ref → Cell) (originOf : Ref → Origin)
    {context : NativeContext Name Ref} {key : Name} {ref : Ref}
    (found : context.get key = some ref) :
    Context.lookup (translate cellOf originOf context) key =
        .found (interpretRef cellOf originOf ref) ∧
      Context.lookup (translate cellOf originOf context) key =
        .found (interpretRef cellOf originOf ref) := by
  rw [get_refines_lookup, found]
  exact ⟨rfl, rfl⟩

structure Captured (Name Ref Term : Type*) where
  context : NativeContext Name Ref
  term : Term

def capture (context : NativeContext Name Ref) (term : Term) :
    Captured Name Ref Term :=
  { context := context, term := term }

/-- A suspension keeps the context present at allocation; a later shadowing
frame is a separate value. -/
theorem capture_before_shadow [DecidableEq Name]
    (parent : NativeContext Name Ref) (key : Name)
    (oldRef newRef : Ref) (term : Term) :
    let base := bind parent key oldRef
    let suspended := capture base term
    let child := bind base key newRef
    suspended.context.get key = some oldRef ∧
      child.get key = some newRef := by
  simp [capture]

/-! ## Persistence as an identity-preserving graph translation -/

def mapRefs (f : Ref → Key) : NativeContext Name Ref → NativeContext Name Key
  | .empty => .empty
  | .frame parent key ref storedDepth =>
      .frame (mapRefs f parent) key (f ref) storedDepth

theorem mapRefs_comp (first : Ref → Key) (second : Key → Cell)
    (context : NativeContext Name Ref) :
    mapRefs second (mapRefs first context) =
      mapRefs (fun ref => second (first ref)) context := by
  induction context with
  | empty => rfl
  | frame parent key ref storedDepth ih =>
      simp [mapRefs, ih]

theorem mapRefs_identity (context : NativeContext Name Ref) :
    mapRefs id context = context := by
  induction context with
  | empty => rfl
  | frame parent key ref storedDepth ih =>
      simp [mapRefs, ih]

/-- If persisted keys decode back to their source references, the entire spine
round-trips, including repeated aliases and cached depths. -/
theorem rehydrate_persist
    (encode : Ref → Key) (decode : Key → Ref)
    (leftInverse : ∀ ref, decode (encode ref) = ref)
    (context : NativeContext Name Ref) :
    mapRefs decode (mapRefs encode context) = context := by
  rw [mapRefs_comp]
  have pointwise : (fun ref => decode (encode ref)) = id := by
    funext ref
    exact leftInverse ref
  rw [pointwise, mapRefs_identity]

theorem persistence_roundtrip_get [DecidableEq Name]
    (encode : Ref → Key) (decode : Key → Ref)
    (leftInverse : ∀ ref, decode (encode ref) = ref)
    (context : NativeContext Name Ref) (key : Name) :
    (mapRefs decode (mapRefs encode context)).get key = context.get key := by
  rw [rehydrate_persist encode decode leftInverse]

/-! ## Executable positive and negative representation examples -/

def goodDemoContext : NativeContext Nat Nat :=
  bind (bind .empty 1 10) 1 20

example : goodDemoContext.WellFormed := by
  simp [goodDemoContext, bind, WellFormed, cachedDepth]

example : goodDemoContext.get 1 = some 20 := by decide

def corruptDepthContext : NativeContext Nat Nat :=
  .frame .empty 1 10 7

/-- Negative: an arbitrary cached depth is not a valid native context. -/
example : ¬ corruptDepthContext.WellFormed := by
  simp [corruptDepthContext, WellFormed, cachedDepth]

/-- The corrupted cache is observably different from semantic depth, showing
why view refinement requires `WellFormed`. -/
example :
    (corruptDepthContext.view 1).total ≠
      (translate id id corruptDepthContext).depth := by
  decide

/-- Equal origins in independently allocated bindings do not identify cells. -/
example :
    let left : NativeContext Nat (Nat × Nat) :=
      bind .empty 1 (10, 99)
    let right : NativeContext Nat (Nat × Nat) :=
      bind .empty 1 (20, 99)
    (left.get 1).map Prod.fst ≠ (right.get 1).map Prod.fst ∧
      (left.get 1).map Prod.snd = (right.get 1).map Prod.snd := by
  decide

end NativeContext

end Mettapedia.Languages.MeTTa.PrimeNativeContextRefinement
