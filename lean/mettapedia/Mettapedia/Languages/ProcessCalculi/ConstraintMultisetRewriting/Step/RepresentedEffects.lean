import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory

/-!
# Represented states and candidates of an effect core

The semantic carrier may contain objects that finite syntax cannot encode.
A representation interprets its own states and candidates and supplies the
represented result of every prepared candidate. This closure obligation is
independent of admission: refused preparations and their payloads remain
available. Neither state injectivity nor coverage of all semantic candidates
is imposed on the general representation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore

universe uO uT uH uOcc uS uF uR uC

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing)

structure Representation (Represented : Type uR) (Candidate : Represented → Type uC) where
  state : Represented → State
  firing : {s : Represented} → Candidate s → Firing (state s)
  preparedResult : {s : Represented} → (f : Candidate s) → E.Prepares (firing f) → Represented
  result_eq : ∀ {s : Represented} (f : Candidate s) (prepared : E.Prepares (firing f)),
    state (preparedResult f prepared) = E.preparedResult (firing f) prepared

namespace Representation

variable {E} {Represented : Type uR} {Candidate : Represented → Type uC}
  (R : E.Representation Represented Candidate)

private def castTarget {left right : State} (same : left = right) {a : Obj}
    (arrow : Hom a (E.frame right)) : Hom a (E.frame left) := same.symm ▸ arrow

private theorem cast_refines {left right : State} (same : left = right) {a : Obj}
    (arrow : Hom a (E.frame right)) (information : EquationStore (Tm a))
    (law : ∀ {b : Obj} (later : Hom (E.frame right) b),
      X.Models later (E.knowledge right) → X.Models (X.comp later arrow) information) :
    ∀ {b : Obj} (later : Hom (E.frame left) b),
      X.Models later (E.knowledge left) →
        X.Models (X.comp later (castTarget same arrow)) information := by
  cases same
  exact law

private theorem cast_exact {left right : State} (same : left = right) {a : Obj}
    (arrow : Hom a (E.frame right)) (information : EquationStore (Tm a))
    (law : ∀ {b : Obj} (later : Hom (E.frame right) b),
      X.Models (X.comp later arrow) information → X.Models later (E.knowledge right)) :
    ∀ {b : Obj} (later : Hom (E.frame left) b),
      X.Models (X.comp later (castTarget same arrow)) information →
        X.Models later (E.knowledge left) := by
  cases same
  exact law

def effect : EffectCore X O Represented Candidate where
  frame s := E.frame (R.state s)
  knowledge s := E.knowledge (R.state s)
  present s := E.present (R.state s)
  selection f := E.selection (R.firing f)
  target f := E.target (R.firing f)
  extension f := E.extension (R.firing f)
  information f := E.information (R.firing f)
  information_refines f := E.information_refines (R.firing f)
  Shapes f := E.Shapes (R.firing f)
  preparedResult f := R.preparedResult f
  present_preparedResult f p := by
    rw [R.result_eq]
    exact E.present_preparedResult (R.firing f) p
  preparedSettle f p := castTarget (R.result_eq f p) (E.preparedSettle (R.firing f) p)
  result_refines f p := cast_refines (R.result_eq f p) _ _ (E.result_refines (R.firing f) p)

theorem prepares_iff {s : Represented} (f : Candidate s) :
    R.effect.Prepares f ↔ E.Prepares (R.firing f) := Iff.rfl

def admission (allow : E.Admission) : R.effect.Admission := fun f p => allow (R.firing f) p

theorem exact (exactness : E.ExactKnowledge) : R.effect.ExactKnowledge :=
  fun f p => cast_exact (R.result_eq f p) _ _ (exactness (R.firing f) p)

def mapEvent {allow : E.Admission} {s t : Represented}
    (event : R.effect.Event (R.admission allow) s t) : E.Event allow (R.state s) (R.state t) :=
  ⟨R.firing event.firing, event.prepared, event.permitted,
    (R.result_eq event.firing event.prepared).symm.trans (congrArg R.state event.target_eq)⟩

theorem event_reflects {allow : E.Admission} {s : Represented} {target : State}
    (f : Candidate s) (event : E.Event allow (R.state s) target)
    (selected : event.firing = R.firing f) :
    ∃ (representedTarget : Represented)
      (lifted : R.effect.Event (R.admission allow) s representedTarget),
      R.state representedTarget = target ∧ lifted.firing = f := by
  rcases event with ⟨firing, prepared, permitted, result⟩
  dsimp only at selected
  subst firing
  exact ⟨R.preparedResult f prepared, ⟨f, prepared, permitted, rfl⟩,
    (R.result_eq f prepared).trans result, rfl⟩

/-- Reflection at a specified represented endpoint needs faithful state
interpretation. General representations instead use `event_reflects`. -/
theorem event_iff {allow : E.Admission} (faithful : Function.Injective R.state)
    {s t : Represented} (f : Candidate s) :
    (∃ event : R.effect.Event (R.admission allow) s t, event.firing = f) ↔
      ∃ event : E.Event allow (R.state s) (R.state t), event.firing = R.firing f := by
  constructor
  · rintro ⟨event, same⟩
    exact ⟨R.mapEvent event, congrArg R.firing same⟩
  · rintro ⟨event, same⟩
    obtain ⟨target, lifted, target_eq, selected⟩ := R.event_reflects f event same
    have equality : target = t := faithful target_eq
    subst target
    exact ⟨lifted, selected⟩

def mapEvents (allow : E.Admission) :
    (EventObject R.effect (R.admission allow)) ⥤q (EventObject E allow) where
  obj := R.state
  map := R.mapEvent

end Representation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

universe uO uT uH uOcc uS uF uR uC

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing) {Represented : Type uR} {Candidate : Represented → Type uC}
  (R : P.effectCore.Representation Represented Candidate)

def represent : Step X O Represented Candidate where
  toEffectCore := R.effect
  Admits f := P.Admits (R.firing f)
  admitted_prepares _ admitted := P.prepares admitted

theorem represent_admits_iff {s : Represented} (f : Candidate s) :
    (P.represent R).Admits f ↔ P.Admits (R.firing f) := Iff.rfl

theorem represent_prepares_iff {s : Represented} (f : Candidate s) :
    (P.represent R).Prepares f ↔ P.Prepares (R.firing f) := Iff.rfl

instance represent_guarded [P.Guarded] : (P.represent R).Guarded where
  holds f := P.Holds (R.firing f)
  admission f := P.admits_iff_prepares (R.firing f)

instance represent_exact [P.Exact] : (P.represent R).Exact :=
  ⟨R.exact P.effectCore_exact⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step
