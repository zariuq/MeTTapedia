import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Prevalidated two-stage protocols with a protected internal phase

A plan supplies two actual admitted firings, not an assumed endpoint effect.
Public actions are permitted only at ready boundaries. Entering a protocol
performs its first real firing; the pending phase permits only its planned
completion. The logical label is emitted at completion, while the erased
execution retains both primitive events.

The public permission and label maps are parameters. This selects no engine
default and does not equate unrestricted intermediate-state observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ProtectedTwoStage

open Interface (Frames)

universe uO uT uH uOcc uS uF uPlan uL
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (P : Interface.Step X O State Firing)

structure Pair (source : State) where
  first : Firing source
  firstAdmitted : P.Admits first
  second : Firing (P.result first firstAdmitted)
  secondAdmitted : P.Admits second

def Pair.middle {source : State} (plan : Pair P source) : State :=
  P.result plan.first plan.firstAdmitted

def Pair.finishState {source : State} (plan : Pair P source) : State :=
  P.result plan.second plan.secondAdmitted

noncomputable def Pair.run {source : State} (plan : Pair P source) : P.Run source :=
  .cons plan.first plan.firstAdmitted (.cons plan.second plan.secondAdmitted (.nil _))

theorem Pair.run_last {source : State} (plan : Pair P source) : plan.run.last = plan.finishState := rfl
theorem Pair.run_length {source : State} (plan : Pair P source) : plan.run.word.length = 2 := rfl

variable {Plan : State → Type uPlan} {Label : Type uL}

structure Configuration (Plan : State → Type uPlan) (Label : Type uL) where
  realize : {source : State} → Plan source → Pair P source
  publicAllowed : {source : State} → Firing source → Prop
  externalLabel : {source : State} → Firing source → Label
  protocolLabel : {source : State} → Plan source → Label

inductive Phase (Plan : State → Type uPlan) : Type (max uS uPlan) where
  | ready (state : State)
  | pending {source : State} (plan : Plan source)

variable {P} (C : Configuration P Plan Label)

def physical : Phase Plan → State
  | .ready state => state
  | .pending plan => (C.realize plan).middle

inductive MacroMove : State → Label → State → Type (max uS uF uPlan uL) where
  | external {source : State} (firing : Firing source) (admitted : P.Admits firing)
      (permitted : C.publicAllowed firing) : MacroMove source (C.externalLabel firing) (P.result firing admitted)
  | protocol {source : State} (plan : Plan source) :
      MacroMove source (C.protocolLabel plan) (C.realize plan).finishState

inductive MicroMove : Phase Plan → Option Label → Phase Plan → Type (max uS uF uPlan uL) where
  | external {source : State} (firing : Firing source) (admitted : P.Admits firing)
      (permitted : C.publicAllowed firing) :
      MicroMove (.ready source) (some (C.externalLabel firing)) (.ready (P.result firing admitted))
  | enter {source : State} (plan : Plan source) : MicroMove (.ready source) none (.pending plan)
  | finish {source : State} (plan : Plan source) :
      MicroMove (.pending plan) (some (C.protocolLabel plan)) (.ready (C.realize plan).finishState)

inductive MacroTrace : State → List Label → State → Type (max uS uF uPlan uL) where
  | nil (source : State) : MacroTrace source [] source
  | cons {source middle target : State} {label : Label} {rest : List Label}
      (move : MacroMove C source label middle) (later : MacroTrace middle rest target) :
      MacroTrace source (label :: rest) target

inductive MicroTrace : Phase Plan → List Label → Phase Plan → Type (max uS uF uPlan uL) where
  | nil (source : Phase Plan) : MicroTrace source [] source
  | cons {source middle target : Phase Plan} {emitted : Option Label} {rest : List Label}
      (move : MicroMove C source emitted middle) (later : MicroTrace middle rest target) :
      MicroTrace source (emitted.toList ++ rest) target

noncomputable def expand : {source target : State} → {word : List Label} →
    MacroTrace C source word target → MicroTrace C (.ready source) word (.ready target)
  | _, _, _, .nil source => .nil (.ready source)
  | _, _, _, .cons (.external firing admitted permitted) later =>
      .cons (.external firing admitted permitted) (expand later)
  | _, _, _, .cons (.protocol plan) later =>
      .cons (.enter plan) (.cons (.finish plan) (expand later))

noncomputable def underlying : {source target : Phase Plan} → {word : List Label} →
    MicroTrace C source word target → P.Run (physical C source)
  | _, _, _, .nil source => .nil (physical C source)
  | _, _, _, .cons (.external firing admitted _) later => .cons firing admitted (underlying later)
  | _, _, _, .cons (.enter plan) later =>
      .cons (C.realize plan).first (C.realize plan).firstAdmitted (underlying later)
  | _, _, _, .cons (.finish plan) later =>
      .cons (C.realize plan).second (C.realize plan).secondAdmitted (underlying later)

def rawLength : {source target : Phase Plan} → {word : List Label} → MicroTrace C source word target → Nat
  | _, _, _, .nil _ => 0
  | _, _, _, .cons _ later => rawLength later + 1

theorem underlying_last {source target : Phase Plan} {word : List Label}
    (path : MicroTrace C source word target) : (underlying C path).last = physical C target := by
  induction path with
  | nil _ => rfl
  | cons move later ih => cases move <;> exact ih

theorem underlying_length {source target : Phase Plan} {word : List Label}
    (path : MicroTrace C source word target) : (underlying C path).word.length = rawLength C path := by
  induction path with
  | nil _ => rfl
  | cons move later ih => cases move <;> exact congrArg Nat.succ ih

theorem no_two_silent {first middle last : Phase Plan}
    (enter : MicroMove C first none middle) (later : MicroMove C middle none last) : False := by
  cases enter
  cases later

#print axioms expand
#print axioms underlying_last
#print axioms underlying_length
#print axioms no_two_silent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ProtectedTwoStage
