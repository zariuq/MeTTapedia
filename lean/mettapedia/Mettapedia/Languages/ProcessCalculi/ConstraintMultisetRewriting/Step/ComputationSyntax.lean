import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicParallel

/-!
# Scoped redex descriptions for a declared computation presentation

The descriptor records a constructor path, primitive operation or selected
open equation, and the actual substitution. Its endpoints are computed from
those data. Soundness and coverage refer to the existing package reduction.
The inner arity changes at binders; it is not an unscoped list of offsets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSyntax

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open AlgebraicSchema AlgebraicParallel

variable {Head : Type}

inductive Context (Head : Type) : Nat → Nat → Type
  | hole {n : Nat} : Context Head n n
  | piDom {n m : Nat} (inner : Context Head n m) (codomain : Tm Head (n + 1)) : Context Head n m
  | piCod {n m : Nat} (domain : Tm Head n) (inner : Context Head (n + 1) m) : Context Head n m
  | sigmaDom {n m : Nat} (inner : Context Head n m) (codomain : Tm Head (n + 1)) : Context Head n m
  | sigmaCod {n m : Nat} (domain : Tm Head n) (inner : Context Head (n + 1) m) : Context Head n m
  | idType {n m : Nat} (inner : Context Head n m) (left right : Tm Head n) : Context Head n m
  | idLeft {n m : Nat} (type : Tm Head n) (inner : Context Head n m) (right : Tm Head n) : Context Head n m
  | idRight {n m : Nat} (type left : Tm Head n) (inner : Context Head n m) : Context Head n m
  | lam {n m : Nat} (inner : Context Head (n + 1) m) : Context Head n m
  | appFun {n m : Nat} (inner : Context Head n m) (argument : Tm Head n) : Context Head n m
  | appArg {n m : Nat} (function : Tm Head n) (inner : Context Head n m) : Context Head n m
  | pairFst {n m : Nat} (inner : Context Head n m) (second : Tm Head n) : Context Head n m
  | pairSnd {n m : Nat} (first : Tm Head n) (inner : Context Head n m) : Context Head n m
  | fst {n m : Nat} (inner : Context Head n m) : Context Head n m
  | snd {n m : Nat} (inner : Context Head n m) : Context Head n m
  | refl {n m : Nat} (inner : Context Head n m) : Context Head n m

def Context.plug : {n m : Nat} → Context Head n m → Tm Head m → Tm Head n
  | _, _, .hole, term => term
  | _, _, .piDom inner codomain, term => .pi (inner.plug term) codomain
  | _, _, .piCod domain inner, term => .pi domain (inner.plug term)
  | _, _, .sigmaDom inner codomain, term => .sigma (inner.plug term) codomain
  | _, _, .sigmaCod domain inner, term => .sigma domain (inner.plug term)
  | _, _, .idType inner left right, term => .id (inner.plug term) left right
  | _, _, .idLeft type inner right, term => .id type (inner.plug term) right
  | _, _, .idRight type left inner, term => .id type left (inner.plug term)
  | _, _, .lam inner, term => .lam (inner.plug term)
  | _, _, .appFun inner argument, term => .app (inner.plug term) argument
  | _, _, .appArg function inner, term => .app function (inner.plug term)
  | _, _, .pairFst inner second, term => .pair (inner.plug term) second
  | _, _, .pairSnd first inner, term => .pair first (inner.plug term)
  | _, _, .fst inner, term => .fst (inner.plug term)
  | _, _, .snd inner, term => .snd (inner.plug term)
  | _, _, .refl inner, term => .refl (inner.plug term)

theorem Context.step {rules : Rules Head} {n m : Nat} (context : Context Head n m)
    {before after : Tm Head m} (reduction : StepCore rules.computation rules.headEq before after) :
    StepCore rules.computation rules.headEq (context.plug before) (context.plug after) := by
  induction context with
  | hole => exact reduction
  | piDom _ _ ih => exact .congPiDom (ih reduction)
  | piCod _ _ ih => exact .congPiCod (ih reduction)
  | sigmaDom _ _ ih => exact .congSigmaDom (ih reduction)
  | sigmaCod _ _ ih => exact .congSigmaCod (ih reduction)
  | idType _ _ _ ih => exact .congIdTy (ih reduction)
  | idLeft _ _ _ ih => exact .congIdLeft (ih reduction)
  | idRight _ _ _ ih => exact .congIdRight (ih reduction)
  | lam _ ih => exact .congLam (ih reduction)
  | appFun _ _ ih => exact .congAppFun (ih reduction)
  | appArg _ _ ih => exact .congAppArg (ih reduction)
  | pairFst _ _ ih => exact .congPairFst (ih reduction)
  | pairSnd _ _ ih => exact .congPairSnd (ih reduction)
  | fst _ ih => exact .congFst (ih reduction)
  | snd _ ih => exact .congSnd (ih reduction)
  | refl _ ih => exact .congRefl (ih reduction)

variable {rules : Rules Head}

inductive Action (presentation : SchemaPresentation rules) (n : Nat) : Type
  | beta (body : Tm Head (n + 1)) (argument : Tm Head n)
  | first (left right : Tm Head n)
  | second (left right : Tm Head n)
  | head (left right : Head) (same : rules.headEq left right)
  | declared {arity : Nat} (left right : Tm Head arity)
      (selected : presentation.schema left right) (arguments : Sub Head arity n)

def Action.source {presentation : SchemaPresentation rules} {n : Nat} : Action presentation n → Tm Head n
  | .beta body argument => .app (.lam body) argument
  | .first left right => .fst (.pair left right)
  | .second left right => .snd (.pair left right)
  | .head left _ _ => .head left
  | .declared left _ _ arguments => subst arguments left

def Action.target {presentation : SchemaPresentation rules} {n : Nat} : Action presentation n → Tm Head n
  | .beta body argument => inst0 argument body
  | .first left _ => left
  | .second _ right => right
  | .head _ right _ => .head right
  | .declared _ right _ arguments => subst arguments right

theorem Action.sound {presentation : SchemaPresentation rules} {n : Nat} (action : Action presentation n) :
    StepCore rules.computation rules.headEq action.source action.target := by
  cases action with
  | beta body argument => exact .betaPi body argument
  | first left right => exact .betaSigmaFst left right
  | second left right => exact .betaSigmaSnd left right
  | head _ _ same => exact .head same
  | declared _ _ selected arguments => exact .root (presentation.sound selected arguments)

structure Event (presentation : SchemaPresentation rules) (n : Nat) where
  innerArity : Nat
  context : Context Head n innerArity
  action : Action presentation innerArity

def Event.source {presentation : SchemaPresentation rules} {n : Nat} (event : Event presentation n) : Tm Head n :=
  event.context.plug event.action.source

def Event.target {presentation : SchemaPresentation rules} {n : Nat} (event : Event presentation n) : Tm Head n :=
  event.context.plug event.action.target

theorem Event.sound {presentation : SchemaPresentation rules} {n : Nat} (event : Event presentation n) :
    StepCore rules.computation rules.headEq event.source event.target :=
  event.context.step event.action.sound

theorem complete (presentation : SchemaPresentation rules) {n : Nat} {before after : Tm Head n}
    (reduction : StepCore rules.computation rules.headEq before after) :
    ∃ event : Event presentation n, event.source = before ∧ event.target = after := by
  induction reduction with
  | betaPi body argument => exact ⟨⟨_, .hole, .beta body argument⟩, rfl, rfl⟩
  | betaSigmaFst left right => exact ⟨⟨_, .hole, .first left right⟩, rfl, rfl⟩
  | betaSigmaSnd left right => exact ⟨⟨_, .hole, .second left right⟩, rfl, rfl⟩
  | head same => exact ⟨⟨_, .hole, .head _ _ same⟩, rfl, rfl⟩
  | root computation =>
      obtain ⟨arity, left, right, arguments, selected, source, target⟩ := presentation.cover computation
      exact ⟨⟨_, .hole, .declared left right selected arguments⟩, source, target⟩
  | @congPiDom n A Anew B reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .piDom event.context B, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congPiCod n A B Bnew reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .piCod A event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congSigmaDom n A Anew B reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .sigmaDom event.context B, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congSigmaCod n A B Bnew reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .sigmaCod A event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congIdTy n A Anew a b reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .idType event.context a b, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congIdLeft n A a anew b reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .idLeft A event.context b, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congIdRight n A a b bnew reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .idRight A a event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | congLam _ ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .lam event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congAppFun n g gnew a reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .appFun event.context a, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congAppArg n g a anew reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .appArg g event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congPairFst n a anew b reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .pairFst event.context b, event.action⟩, ?_, ?_⟩ <;> rfl
  | @congPairSnd n a b bnew reduction ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .pairSnd a event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | congFst _ ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .fst event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | congSnd _ ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .snd event.context, event.action⟩, ?_, ?_⟩ <;> rfl
  | congRefl _ ih =>
      obtain ⟨event, rfl, rfl⟩ := ih
      refine ⟨⟨_, .refl event.context, event.action⟩, ?_, ?_⟩ <;> rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSyntax

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSyntax.complete
