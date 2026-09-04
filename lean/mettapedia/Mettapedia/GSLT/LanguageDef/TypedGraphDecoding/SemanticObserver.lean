import Mathlib.Tactic

/-!
# Composable semantic observers for typed graph decoding

The structural decoder owns graph transitions.  Language semantics observes
those same transitions and may reject an action when its source-derived
judgment cannot advance.  Product observers combine features without adding
language-mode switches: each observer sees the identical before/action/after
edge, and the product advances exactly when both do.

The final counterexample records an important boundary.  Separate
no-dead-end arguments for two masks do not imply that their intersection has
a completion; their witnesses may be incompatible.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.SemanticObserver

universe uBase uAction uObservation uOther

/-- One checker-owned graph edge exposed to semantic observation. -/
structure Edge (Base : Type uBase) (Action : Type uAction) where
  before : Base
  action : Action
  after : Base

/-- A deterministic partial observer of structural graph transitions. -/
structure Observer (Base : Type uBase) (Action : Type uAction) where
  Observation : Type uObservation
  initial : Base → Observation
  observe? : Observation → Edge Base Action → Option Observation
  terminal : Observation → Prop

namespace Observer

variable {Base : Type uBase} {Action : Type uAction}

/-- Run one observer over an already authenticated structural path. -/
def run (observer : Observer Base Action) :
    observer.Observation → List (Edge Base Action) →
      Option observer.Observation
  | observation, [] => some observation
  | observation, edge :: edges => do
      let next ← observer.observe? observation edge
      run observer next edges

/-- Conjunction of two semantic observation layers over exactly the same
structural edge stream. -/
def product (left : Observer Base Action)
    (right : Observer Base Action) : Observer Base Action where
  Observation := left.Observation × right.Observation
  initial := fun base => (left.initial base, right.initial base)
  observe? := fun observation edge => do
    let nextLeft ← left.observe? observation.1 edge
    let nextRight ← right.observe? observation.2 edge
    pure (nextLeft, nextRight)
  terminal := fun observation =>
    left.terminal observation.1 ∧ right.terminal observation.2

@[simp] theorem product_initial (left : Observer Base Action)
    (right : Observer Base Action) (base : Base) :
    (product left right).initial base =
      (left.initial base, right.initial base) := rfl

@[simp] theorem product_terminal_iff (left : Observer Base Action)
    (right : Observer Base Action)
    (observation : left.Observation × right.Observation) :
    (product left right).terminal observation ↔
      left.terminal observation.1 ∧ right.terminal observation.2 := by
  rfl

/-- Product admission is exact conjunction, not an order-dependent pipeline. -/
theorem product_observe?_eq_some_iff
    (left : Observer Base Action) (right : Observer Base Action)
    (observation : left.Observation × right.Observation)
    (edge : Edge Base Action)
    (next : left.Observation × right.Observation) :
    (product left right).observe? observation edge = some next ↔
      left.observe? observation.1 edge = some next.1 ∧
        right.observe? observation.2 edge = some next.2 := by
  cases leftStep : left.observe? observation.1 edge with
  | none => simp [product, leftStep]
  | some nextLeft =>
      cases rightStep : right.observe? observation.2 edge with
      | none => simp [product, leftStep, rightStep]
      | some nextRight =>
          simp only [product, leftStep, rightStep, Option.some.injEq]
          constructor
          · intro equality
            cases equality
            exact ⟨rfl, rfl⟩
          · rintro ⟨leftEquality, rightEquality⟩
            change some (nextLeft, nextRight) = some next
            apply congrArg some
            apply Prod.ext
            · exact leftEquality
            · exact rightEquality

/-- Running a product observer is equivalent to running both components on
the same edge list. -/
theorem product_run_eq_some_iff
    (left : Observer Base Action) (right : Observer Base Action) :
    ∀ (edges : List (Edge Base Action))
      (observation : left.Observation × right.Observation)
      (next : left.Observation × right.Observation),
      run (product left right) observation edges = some next ↔
        run left observation.1 edges = some next.1 ∧
          run right observation.2 edges = some next.2 := by
  intro edges
  induction edges with
  | nil =>
      intro observation next
      simp only [run, Option.some.injEq]
      constructor
      · intro equality
        cases equality
        exact ⟨rfl, rfl⟩
      · rintro ⟨leftEquality, rightEquality⟩
        apply congrArg some
        apply Prod.ext
        · exact leftEquality
        · exact rightEquality
  | cons edge edges inductionHypothesis =>
      intro observation next
      simp only [run]
      cases leftStep : left.observe? observation.1 edge with
      | none => simp [product, leftStep]
      | some nextLeft =>
          cases rightStep : right.observe? observation.2 edge with
          | none => simp [product, leftStep, rightStep]
          | some nextRight =>
              simp only [product, leftStep, rightStep]
              exact inductionHypothesis (nextLeft, nextRight) next

end Observer

/-! ## Completion compatibility is a separate composition obligation -/

/-- A trace predicate has a completion after this exact prefix. -/
def HasTraceCompletion {Action : Type uAction}
    (accepts : List Action → Prop) (pre : List Action) : Prop :=
  ∃ suffix, accepts (pre ++ suffix)

/-- The joint-witness condition needed to compose two completion layers. -/
def JointlyCompletable {Action : Type uAction}
    (left right : List Action → Prop) (pre : List Action) : Prop :=
  ∃ suffix, left (pre ++ suffix) ∧ right (pre ++ suffix)

theorem conjunction_hasCompletion_iff_jointlyCompletable
    {Action : Type uAction} (left right : List Action → Prop)
    (pre : List Action) :
    HasTraceCompletion (fun trace => left trace ∧ right trace) pre ↔
      JointlyCompletable left right pre := by
  rfl

private def acceptsFalse : List Bool → Prop
  | [false] => True
  | _ => False

private def acceptsTrue : List Bool → Prop
  | [true] => True
  | _ => False

/-- Two layers can each have a completion while their conjunction has none.
No-dead-end proofs therefore require joint witness compatibility. -/
theorem independent_completions_do_not_compose :
    HasTraceCompletion acceptsFalse [] ∧
      HasTraceCompletion acceptsTrue [] ∧
      ¬ HasTraceCompletion
        (fun trace => acceptsFalse trace ∧ acceptsTrue trace) [] := by
  refine ⟨⟨[false], trivial⟩, ⟨[true], trivial⟩, ?_⟩
  rintro ⟨suffix, left, right⟩
  cases suffix with
  | nil => exact left
  | cons head tail =>
      cases head with
      | false => exact right
      | true => exact left

#print axioms Observer.product_observe?_eq_some_iff
#print axioms Observer.product_run_eq_some_iff
#print axioms conjunction_hasCompletion_iff_jointlyCompletable
#print axioms independent_completions_do_not_compose

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.SemanticObserver
