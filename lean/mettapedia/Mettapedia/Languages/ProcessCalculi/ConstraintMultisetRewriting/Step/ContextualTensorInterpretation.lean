import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualRunInterpretation

/-!
# Two local runs through one shared contextual interpretation

Changing source roles supplies an actual transport isomorphism. Involution
and compatibility with both source frame maps are separate certificates.
The selected tensor is built from local admission checks. No ambient scheduling
policy or complete successful target run is assumed. Coherence of several
tensors is a further law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ContextualRunInterpretation

universe uO uT uH uOcc uS uF uI uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)

structure Flip where
  swap : {left right : State} → I.Place left right → I.Place right left
  stateIso : ∀ {left right : State} (place : I.Place left right),
    T.Iso (I.pair (swap place)).state (I.pair place).state

/-- Coherence certificates are separate from the data used by selected execution. -/
structure Flip.Lawful (flip : I.Flip) : Prop where
  swap_swap : ∀ {left right : State} (place : I.Place left right), flip.swap (flip.swap place) = place
  left_natural : ∀ {left right : State} (place : I.Place left right),
    X.Agree (X.comp (T.toStateIso (flip.stateIso place)).frame.hom (I.pair (flip.swap place)).leftMap)
      (I.pair place).rightMap
  right_natural : ∀ {left right : State} (place : I.Place left right),
    X.Agree (X.comp (T.toStateIso (flip.stateIso place)).frame.hom (I.pair (flip.swap place)).rightMap)
      (I.pair place).leftMap

variable (flip : I.Flip)

structure TensorPlan {left right : State} (place : I.Place left right) (first : P.Run left) (second : P.Run right) where
  leftPlan : I.Plan place first
  rightPlan : I.Plan (flip.swap (leftPlan.realize I place first).target) second

structure TensorResult {left right : State} (place : I.Place left right) (first : P.Run left) (second : P.Run right) where
  target : I.Place first.last second.last
  execution : P.Run (I.pair place).state
  resultIso : T.Iso execution.last (I.pair target).state
  length_preserved : execution.word.length = first.word.length + second.word.length

def TensorPlan.realize {left right : State} {place : I.Place left right} {first : P.Run left} {second : P.Run right}
    (plan : I.TensorPlan flip place first second) : I.TensorResult place first second := by
  let one := plan.leftPlan.realize I place first
  let two := plan.rightPlan.realize I (flip.swap one.target) second
  let bridge := T.trans (flip.stateIso one.target) (T.symm one.resultIso)
  let moved := T.moveRun bridge two.execution
  refine ⟨flip.swap two.target, one.execution.append moved, ?_, ?_⟩
  · have movedEnd := T.moveRunEndIso bridge two.execution
    have finalIso : T.Iso moved.last (I.pair (flip.swap two.target)).state :=
      T.trans (T.symm movedEnd) (T.trans two.resultIso (T.symm (flip.stateIso two.target)))
    exact Eq.mpr (congrArg (fun state => T.Iso state (I.pair (flip.swap two.target)).state)
      (one.execution.last_append moved)) finalIso
  · have unchanged := Transport.Similar.length_eq (Transport.Similar.moveRun bridge two.execution)
    rw [Step.Run.word_append, List.length_append, ← unchanged, one.length_preserved, two.length_preserved]

structure TensorChecks {left right : State} (place : I.Place left right) (first : P.Run left) (second : P.Run right) : Prop where
  leftChecks : I.Checks place first
  rightChecks : I.Checks (flip.swap ((Plan.ofChecks I place first leftChecks).realize I place first).target) second

def TensorChecks.plan {left right : State} {place : I.Place left right} {first : P.Run left} {second : P.Run right}
    (checked : I.TensorChecks flip place first second) : I.TensorPlan flip place first second :=
  ⟨Plan.ofChecks I place first checked.leftChecks, Plan.ofChecks I _ second checked.rightChecks⟩

theorem tensor_plan_iff_checks {left right : State} (place : I.Place left right) (first : P.Run left) (second : P.Run right) :
    Nonempty (I.TensorPlan flip place first second) ↔ I.TensorChecks flip place first second := by
  constructor
  · rintro ⟨plan⟩
    have one := (I.plan_iff_checks place first).mp ⟨plan.leftPlan⟩
    refine ⟨one, ?_⟩
    have same := Plan.unique I (Plan.ofChecks I place first one) plan.leftPlan
    rw [same]
    exact (I.plan_iff_checks _ second).mp ⟨plan.rightPlan⟩
  · intro checked
    exact ⟨checked.plan I flip⟩

theorem tensor_of_checks {left right : State} {place : I.Place left right} {first : P.Run left} {second : P.Run right}
    (checked : I.TensorChecks flip place first second) : Nonempty (I.TensorResult place first second) :=
  ⟨checked.plan.realize I flip⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ContextualRunInterpretation
