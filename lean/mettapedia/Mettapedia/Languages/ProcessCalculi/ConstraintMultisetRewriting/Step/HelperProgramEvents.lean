import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperScheduleDomain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicity

/-!
# Event origins in the admitted contextual schedule profile

The component programs here are complete admitted local runs. Their choices
are which pending component event to execute next. The exact tensor domain
constructs native admission for every such choice and remains true afterwards.
The choice retains its source role before primitive-firing projection.

This is a profile of selected local programs. It does not identify their
choices with every candidate that an unrestricted joint store might enable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open EventMultiplicity
variable {S : Signature} {O : Type} [DecidableEq O]

structure Program (S : Signature) (O : Type) [DecidableEq O] where
  source : State S O
  run : helperStep.Run source

namespace Program

inductive Head : Program S O → Type 1
  | cons {source : State S O} (f : Firing source) (allowed : helperStep.Admits f)
      (rest : helperStep.Run f.after) : Head ⟨source, .cons f allowed rest⟩

def Head.firing : {program : Program S O} → Head program → Firing program.source
  | _, .cons f _ _ => f

def Head.next : {program : Program S O} → Head program → Program S O
  | _, .cons f _ rest => ⟨f.after, rest⟩

def system : EventMultiplicity.System (Program S O) (MetaArity S) where
  Choice := Head
  next _ head := head.next
  action _ head := head.firing.helper

end Program

structure ContextProgram (S : Signature) (O : Type) [DecidableEq O] where
  left : Program S O
  right : Program S O
  place : ContextPlacement left.source right.source
  domain : TensorDomain place left.run right.run

namespace ContextProgram

def originFiring (pair : ContextProgram S O) :
    Program.Head pair.left ⊕ Program.Head pair.right → Firing pair.place.state
  | .inl head => pair.place.leftFiring head.firing
  | .inr head => pair.place.rightFiring head.firing

theorem left_allowed : ∀ (pair : ContextProgram S O) (head : Program.Head pair.left),
    helperStep.Admits (pair.place.leftFiring head.firing)
  | ⟨⟨_, .cons f allowed rest⟩, right, place, domain⟩, .cons _ _ _ =>
      ((place.domain_left_iff f allowed rest right.run).mp domain).1

theorem right_allowed : ∀ (pair : ContextProgram S O) (head : Program.Head pair.right),
    helperStep.Admits (pair.place.rightFiring head.firing)
  | ⟨left, ⟨_, .cons g allowed rest⟩, place, domain⟩, .cons _ _ _ =>
      ((place.domain_right_iff g allowed left.run rest).mp domain).1

def advanceLeft : (pair : ContextProgram S O) → Program.Head pair.left → ContextProgram S O
  | ⟨⟨_, .cons f allowed rest⟩, right, place, domain⟩, .cons _ _ _ =>
      ⟨⟨f.after, rest⟩, right, place.afterLeft f, ((place.domain_left_iff f allowed rest right.run).mp domain).2⟩

def advanceRight : (pair : ContextProgram S O) → Program.Head pair.right → ContextProgram S O
  | ⟨left, ⟨_, .cons g allowed rest⟩, place, domain⟩, .cons _ _ _ =>
      ⟨left, ⟨g.after, rest⟩, place.afterRight g, ((place.domain_right_iff g allowed left.run rest).mp domain).2⟩

def Choice (pair : ContextProgram S O) :=
  {origin : Program.Head pair.left ⊕ Program.Head pair.right // helperStep.Admits (pair.originFiring origin)}

def choiceEquiv (pair : ContextProgram S O) :
    Program.Head pair.left ⊕ Program.Head pair.right ≃ pair.Choice where
  toFun origin := ⟨origin, by cases origin with
    | inl head => exact pair.left_allowed head
    | inr head => exact pair.right_allowed head⟩
  invFun choice := choice.val
  left_inv _ := rfl
  right_inv _ := rfl

def next (pair : ContextProgram S O) (choice : pair.Choice) : ContextProgram S O :=
  match choice.val with
  | .inl head => pair.advanceLeft head
  | .inr head => pair.advanceRight head

def system : EventMultiplicity.System (ContextProgram S O) (MetaArity S) where
  Choice := Choice
  next := next
  action pair choice := (pair.originFiring choice.val).helper

def nativeRun (pair : ContextProgram S O) (choice : pair.Choice) : helperStep.Run pair.place.state :=
  .cons (pair.originFiring choice.val) choice.property (.nil _)

def resultIso : ∀ (pair : ContextProgram S O) (choice : pair.Choice),
    helperTransport.Iso (pair.nativeRun choice).last (pair.next choice).place.state
  | ⟨⟨_, .cons f _allowed _rest⟩, _right, place, _domain⟩, ⟨.inl (.cons _ _ _), _native⟩ => place.left_result_iso f
  | ⟨_left, ⟨_, .cons g _allowed _rest⟩, place, _domain⟩, ⟨.inr (.cons _ _ _), _native⟩ => place.right_result_iso g

def project (pair : ContextProgram S O) : Program S O × Program S O := (pair.left, pair.right)

theorem project_next : ∀ (pair : ContextProgram S O) (choice : pair.Choice),
    (pair.next choice).project = (asynchronous Program.system Program.system).next pair.project choice.val
  | ⟨⟨_, .cons _f _allowed _rest⟩, _right, _place, _domain⟩, ⟨.inl (.cons _ _ _), _native⟩ => rfl
  | ⟨_left, ⟨_, .cons _g _allowed _rest⟩, _place, _domain⟩, ⟨.inr (.cons _ _ _), _native⟩ => rfl

def projection : Bisimulation (system (S := S) (O := O))
    (asynchronous Program.system Program.system) (fun pair programs => pair.project = programs) where
  choices same := same ▸ (choiceEquiv _).symm
  actions same choice := by
    cases same
    cases choice with
    | mk origin native =>
      cases origin with
      | inl head => rfl
      | inr head => rfl
  successors same choice := by
    cases same
    exact project_next _ choice

theorem project_bisimilar (pair : ContextProgram S O) :
    Bisimilar system pair (asynchronous Program.system Program.system) pair.project :=
  ⟨_, ⟨projection⟩, rfl⟩

theorem parallel_congruence (first second : ContextProgram S O)
    (left : Bisimilar Program.system first.left Program.system second.left)
    (right : Bisimilar Program.system first.right Program.system second.right) :
    Bisimilar system first system second :=
  (first.project_bisimilar).trans ((left.asynchronous right).trans second.project_bisimilar.symm)

end ContextProgram

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
