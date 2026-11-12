import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ScopedEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualDiamond

/-!
# Actual contextual-helper states realizing scoped coexistence

Two source contexts are placed by explicit assignments into a declared native
frame. Source roles retain their scope identities. The resulting native state
is the existing coexistence realization; its step admission reads combined
knowledge and resources, including guards newly enabled by the context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]

abbrev scopedHelperEffect := (helperStep (S := S) (O := O)).toStep.effectCore.withScopeKeys Bool

structure ContextPlacement (left right : State S O) where
  frame : Frames.Frame S
  leftMap : Assignment left.frame.arity frame.arity
  rightMap : Assignment right.frame.arity frame.arity

namespace ContextPlacement

variable {left right : State S O} (placed : ContextPlacement left right)

abbrev state : State S O :=
  ⟨placed.frame, (Frames.contextual S).applyStore placed.leftMap left.knowledge ++
    (Frames.contextual S).applyStore placed.rightMap right.knowledge, left.present ∪ right.present⟩

def placement : EffectCore.Systems.Placement scopedHelperEffect
    [(false, left), (true, right)] (false, placed.frame) := by
  rintro ⟨side, source⟩ member
  change (side, source) ∈ [(false, left.frame), (true, right.frame)] at member
  cases side with
  | false =>
      have same : source = left.frame := by
        rcases List.mem_cons.mp member with same | later
        · exact (Prod.mk.inj same).2
        · have wrong := (Prod.mk.inj (List.mem_singleton.mp later)).1
          cases wrong
      cases same
      exact placed.leftMap
  | true =>
      have same : source = right.frame := by
        rcases List.mem_cons.mp member with wrong | later
        · cases (Prod.mk.inj wrong).1
        · exact (Prod.mk.inj (List.mem_singleton.mp later)).2
      cases same
      exact placed.rightMap

theorem native_realization :
    (helperStep (S := S) (O := O)).toStep.effectCore.configuration placed.state =
      EffectCore.Systems.realize scopedHelperEffect [(false, left), (true, right)] placed.placement := by
  rw [EffectCore.Systems.realize, EffectCore.Systems.realize, EffectCore.Systems.realize]
  rw [Coexistence.tensor_unit]
  rfl

theorem models_left {target : Frames.Frame S} (σ : Assignment placed.frame.arity target.arity)
    (solved : (Frames.contextual S).Models σ placed.state.knowledge) :
    (Frames.contextual S).Models (Assignment.compose σ placed.leftMap) left.knowledge :=
  (Frames.models_applyStore (X := Frames.contextual S)
    (a := left.frame) (b := placed.frame) (c := target) placed.leftMap σ left.knowledge).mp
    ((Frames.models_append (X := Frames.contextual S) σ _ _).mp solved).1

theorem models_right {target : Frames.Frame S} (σ : Assignment placed.frame.arity target.arity)
    (solved : (Frames.contextual S).Models σ placed.state.knowledge) :
    (Frames.contextual S).Models (Assignment.compose σ placed.rightMap) right.knowledge :=
  (Frames.models_applyStore (X := Frames.contextual S)
    (a := right.frame) (b := placed.frame) (c := target) placed.rightMap σ right.knowledge).mp
    ((Frames.models_append (X := Frames.contextual S) σ _ _).mp solved).2

theorem inherits_left_guard (f : Firing left) (allowed : helperStep.Admits f) :
    (Frames.contextual S).Entails placed.state.knowledge
      (fun _ σ => (Frames.contextual S).Models σ ((Frames.contextual S).applyStore placed.leftMap f.guards)) := by
  intro target mapping solved
  have asked := ((admits_iff f).mp allowed).2.2
  exact (Frames.models_applyStore (X := Frames.contextual S)
    (a := left.frame) (b := placed.frame) (c := target) placed.leftMap mapping f.guards).mpr
    (asked target (Assignment.compose mapping placed.leftMap) (placed.models_left mapping solved))

theorem left_admission_iff (f : Firing left) :
    helperStep.Admits (s := placed.state) (f.move placed.leftMap) ↔
      (Frames.contextual S).Solvable placed.state.knowledge ∧
        f.made ∉ left.present ∧ f.made ∉ right.present ∧
        (Frames.contextual S).Entails placed.state.knowledge
          (fun _ σ => (Frames.contextual S).Models σ
            ((Frames.contextual S).applyStore placed.leftMap f.guards)) := by
  rw [admits_iff]
  change (_ ∧ f.made ∉ left.present ∪ right.present ∧ _) ↔ _
  simp only [Finset.mem_union, not_or]
  tauto

/-- For an already admitted local firing, the exact extra conditions contain no blindness. -/
theorem admitted_left_iff (f : Firing left) (allowed : helperStep.Admits f) :
    helperStep.Admits (s := placed.state) (f.move placed.leftMap) ↔
      (Frames.contextual S).Solvable placed.state.knowledge ∧ f.made ∉ right.present := by
  rw [placed.left_admission_iff]
  have oldFresh := ((admits_iff f).mp allowed).2.1
  have asked := placed.inherits_left_guard f allowed
  exact ⟨fun ⟨solved, _, fresh, _⟩ => ⟨solved, fresh⟩,
    fun ⟨solved, fresh⟩ => ⟨solved, oldFresh, fresh, asked⟩⟩

theorem inherits_right_guard (f : Firing right) (allowed : helperStep.Admits f) :
    (Frames.contextual S).Entails placed.state.knowledge
      (fun _ σ => (Frames.contextual S).Models σ ((Frames.contextual S).applyStore placed.rightMap f.guards)) := by
  intro target mapping solved
  have asked := ((admits_iff f).mp allowed).2.2
  exact (Frames.models_applyStore (X := Frames.contextual S)
    (a := right.frame) (b := placed.frame) (c := target) placed.rightMap mapping f.guards).mpr
    (asked target (Assignment.compose mapping placed.rightMap) (placed.models_right mapping solved))

theorem right_admission_iff (f : Firing right) :
    helperStep.Admits (s := placed.state) (f.move placed.rightMap) ↔
      (Frames.contextual S).Solvable placed.state.knowledge ∧
        f.made ∉ right.present ∧ f.made ∉ left.present ∧
        (Frames.contextual S).Entails placed.state.knowledge
          (fun _ σ => (Frames.contextual S).Models σ
            ((Frames.contextual S).applyStore placed.rightMap f.guards)) := by
  rw [admits_iff]
  change (_ ∧ f.made ∉ left.present ∪ right.present ∧ _) ↔ _
  simp only [Finset.mem_union, not_or]
  tauto

theorem admitted_right_iff (f : Firing right) (allowed : helperStep.Admits f) :
    helperStep.Admits (s := placed.state) (f.move placed.rightMap) ↔
      (Frames.contextual S).Solvable placed.state.knowledge ∧ f.made ∉ left.present := by
  rw [placed.right_admission_iff]
  have oldFresh := ((admits_iff f).mp allowed).2.1
  have asked := placed.inherits_right_guard f allowed
  exact ⟨fun ⟨solved, _, fresh, _⟩ => ⟨solved, fresh⟩,
    fun ⟨solved, fresh⟩ => ⟨solved, oldFresh, fresh, asked⟩⟩

end ContextPlacement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
