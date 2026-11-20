import Mettapedia.Machines.OrderedDependencyProjection

/-!
# Classified publications of ordered dependency projections

A publisher may conservatively advance a clock without comparing the
projected segment. A skipped clock must account for its projected segment.
Notifications and raw contents use the existing dependency store.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyClassification

open OrderedDependencyStore OrderedDependencyProjection

universe u v w

variable {Entry : Type u} {Projection : Type v} {Value : Type w} {size : Nat}

def publish (s : State Entry Projection size) (writer : Fin size)
    (contents : List Entry) (rewrites : Bool) (bumps : Projection → Bool) :
    State Entry Projection size :=
  { store := contentUpdate s.store writer contents rewrites
    clocks := fun slot reader =>
      if (reader = writer ∨ reader ∈ s.store.observers writer) ∧ bumps slot = true
      then s.clocks slot reader + 1 else s.clocks slot reader }

def Covers (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (writer : Fin size)
    (contents : List Entry) (bumps : Projection → Bool) : Prop :=
  ∀ slot, bumps slot = false →
    contents.filterMap (project slot) = (s.store.members writer).own.filterMap (project slot)

theorem publish_observers (s : State Entry Projection size) (invariant : ObserverInvariant s.store)
    (writer : Fin size) (contents : List Entry) (rewrites : Bool) (bumps : Projection → Bool) :
    ObserverInvariant (publish s writer contents rewrites bumps).store :=
  contentUpdate_observers s.store invariant writer contents rewrites

theorem publish_clock_mono (s : State Entry Projection size) (writer reader : Fin size)
    (contents : List Entry) (rewrites : Bool) (bumps : Projection → Bool) (slot : Projection) :
    s.clocks slot reader ≤ (publish s writer contents rewrites bumps).clocks slot reader := by
  simp only [publish]
  split <;> omega

/-- The projection-aware reference update witnesses soundness of the cheaper
classification. Both operations use the same published rows and dependency
index. -/
theorem publish_view_of_clock_eq [DecidableEq Value] (project : Projection → Entry → Option Value)
    (s : State Entry Projection size) (invariant : ObserverInvariant s.store)
    (writer reader : Fin size) (contents : List Entry) (rewrites : Bool)
    (bumps : Projection → Bool) (covers : Covers project s writer contents bumps) (slot : Projection)
    (unchanged : (publish s writer contents rewrites bumps).clocks slot reader = s.clocks slot reader) :
    view project (publish s writer contents rewrites bumps) reader slot = view project s reader slot := by
  have referenceClock : (update project s writer contents rewrites).clocks slot reader =
      s.clocks slot reader := by
    by_cases notified : reader = writer ∨ reader ∈ s.store.observers writer
    · have skipped : bumps slot = false := by
        cases bit : bumps slot
        · rfl
        · simp [publish, notified, bit] at unchanged
      simp [update, covers slot skipped]
    · simp [update, notified]
  exact update_view_of_clock_eq project s invariant writer reader contents rewrites slot referenceClock

theorem append_covers (project : Projection → Entry → Option Value)
    (rowBump : Projection → Entry → Bool)
    (coversRow : ∀ slot row, rowBump slot row = false → project slot row = none)
    (s : State Entry Projection size) (writer : Fin size) (suffix : List Entry) :
    Covers project s writer ((s.store.members writer).own ++ suffix)
      (fun slot => suffix.any (rowBump slot)) := by
  intro slot skipped
  have invisible : suffix.filterMap (project slot) = [] := by
    induction suffix with
    | nil => rfl
    | cons first rest ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at skipped
      simp [coversRow slot first skipped.1, ih skipped.2]
  simp [List.filterMap_append, invisible]

end Mettapedia.Machines.OrderedDependencyClassification
