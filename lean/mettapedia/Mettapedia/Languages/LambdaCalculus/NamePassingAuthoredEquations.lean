import Mettapedia.Languages.LambdaCalculus.NamePassingPresentationEquations
import Mettapedia.OSLF.Syntax.EquationalQuotient
import Mettapedia.OSLF.Syntax.BindingEquationQuotientModel

/-!
# Exact authored scope schemas for the open name-passing presentation

The two application scope equations are independent contextual schemas.
The definition body is a metavariable with one reference dependency; its
stored value is outside that binder. Their generated equation closure is
proved equal to the existing static relation at every open context and
inside every constructor. No recursive-definition equation is added.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredEquations

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualAssignment
open Presentation

abbrev metas : List (MetaArity signature) := [([Srt.nm], Srt.tm)]
abbrev schemaSig : Signature := withMetas signature metas

def boundBody {Γ : Ctx schemaSig} (argument : Term schemaSig Γ .nm) : Term schemaSig Γ .tm :=
  .op (.inr (MetaOp.mk (M := metas) 0)) (.cons argument .nil)

def schemaApplication {Γ : Ctx schemaSig} (function : Term schemaSig Γ .tm)
    (argument : Term schemaSig Γ .nm) : Term schemaSig Γ .tm :=
  .op (.inl .application) (.cons function (.cons argument .nil))

def schemaDefinition {Γ : Ctx schemaSig} (value : Term schemaSig Γ .tm)
    (body : Term schemaSig (.nm :: Γ) .tm) : Term schemaSig Γ .tm :=
  .op (.inl .definition) (.cons value (.cons body .nil))

def schemaCarrier {Γ : Ctx schemaSig} (name : Term schemaSig Γ .nm)
    (value body : Term schemaSig Γ .tm) : Term schemaSig Γ .tm :=
  .op (.inl .carrier) (.cons name (.cons value (.cons body .nil)))

def appDefinition : EqAxiom signature metas where
  ctx := [.tm, .nm]
  sort := .tm
  lhs := schemaApplication (schemaDefinition (.var .zero) (boundBody (.var .zero))) (.var (.succ .zero))
  rhs := schemaDefinition (.var .zero)
    (schemaApplication (boundBody (.var .zero)) (.var (.succ (.succ .zero))))

def appCarrier : EqAxiom signature metas where
  ctx := [.nm, .tm, .tm, .nm]
  sort := .tm
  lhs := schemaApplication (schemaCarrier (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ .zero))))
  rhs := schemaCarrier (.var .zero) (.var (.succ .zero))
    (schemaApplication (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero)))))

def equations : List (EqAxiom signature metas) := [appDefinition, appCarrier]

def supply {Γ : Ctx signature} (body : Program (.nm :: Γ)) : ContextualAssignment signature metas Γ
  | ⟨0, _⟩ => body
  | ⟨n + 1, impossible⟩ => by simp [metas] at impossible

def Same {Γ : Ctx signature} : {sort : Srt} → Term signature Γ sort → Term signature Γ sort → Prop
  | .nm, first, last => first = last
  | .tm, first, last => StaticEq first last

private theorem unary_lift {Θ Γ : Ctx signature} (ambient : Sub signature Θ Γ) :
    joinSub (dependencies := [Srt.nm])
      (argsToSub (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
      (weakenSub [Srt.nm] ambient) = liftSub ambient [Srt.nm] := by
  funext sort position
  cases position <;> rfl

theorem axiom_sound : ∀ (index : Fin equations.length) {Θ Γ : Ctx signature}
    (body : ContextualAssignment signature metas Θ) (ambient : Sub signature Θ Γ)
    (ordinary : Sub signature (equations.get index).ctx Γ),
    Same (ContextualAssignment.instantiate body ambient ordinary (equations.get index).lhs)
      (ContextualAssignment.instantiate body ambient ordinary (equations.get index).rhs)
  | ⟨0, _⟩, _, _, body, ambient, ordinary => by
      dsimp only [equations, List.get, appDefinition, schemaApplication, schemaDefinition,
        boundBody, Same, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        ContextualAssignment.apply]
      rw [ContextualAssignment.weakenSub_nil ambient,
        ContextualAssignment.weakenSub_nil (weakenSub [Srt.nm] ambient)]
      change StaticEq
        (application (definition (ordinary _ .zero)
          (bind (joinSub (argsToSub (.cons (Term.var .zero : Name (.nm :: _)) .nil))
            (weakenSub [Srt.nm] ambient)) (body 0))) (ordinary _ (.succ .zero)))
        (definition (ordinary _ .zero)
          (application
            (bind (joinSub (argsToSub (.cons (Term.var .zero : Name (.nm :: _)) .nil))
              (weakenSub [Srt.nm] ambient)) (body 0))
            (Mettapedia.OSLF.Binding.weaken (ordinary _ (.succ .zero)))))
      exact .appDefinition _ _ _
  | ⟨1, _⟩, _, _, _, _, ordinary => by
      change StaticEq
        (application (carrier (ordinary _ .zero) (ordinary _ (.succ .zero))
          (ordinary _ (.succ (.succ .zero)))) (ordinary _ (.succ (.succ (.succ .zero)))))
        (carrier (ordinary _ .zero) (ordinary _ (.succ .zero))
          (application (ordinary _ (.succ (.succ .zero))) (ordinary _ (.succ (.succ (.succ .zero))))))
      exact .appCarrier _ _ _ _
  | ⟨n + 2, impossible⟩, _, _, _, _, _ => by
      simp [equations] at impossible
      omega

private theorem same_refl {Γ : Ctx signature} {sort : Srt} (term : Term signature Γ sort) :
    Same term term := by cases sort <;> first | rfl | exact .refl _

private theorem same_symm {Γ : Ctx signature} {sort : Srt} {first last : Term signature Γ sort}
    (equal : Same first last) : Same last first := by
  cases sort with
  | nm => exact equal.symm
  | tm => exact .symm equal

private theorem same_trans {Γ : Ctx signature} {sort : Srt}
    {first middle last : Term signature Γ sort} (before : Same first middle) (after : Same middle last) :
    Same first last := by
  cases sort with
  | nm => exact before.trans after
  | tm => exact .trans before after

inductive SameArgs : {arity : List (List Srt × Srt)} → {Γ : Ctx signature} →
    Args signature arity Γ → Args signature arity Γ → Prop where
  | nil {Γ} : SameArgs (Args.nil (S := signature) (Γ := Γ)) .nil
  | cons {Γ binders sort rest} {first last : Term signature (binders ++ Γ) sort}
      {tail tail' : Args signature rest Γ} :
      Same first last → SameArgs tail tail' → SameArgs (.cons first tail) (.cons last tail')

private theorem same_cong {Γ : Ctx signature} {sort : Srt} (operator : Operator sort)
    {first last : Args signature (signature.arity operator) Γ} (equal : SameArgs first last) :
    Same (.op operator first) (.op operator last) := by
  cases operator with
  | reference =>
      cases equal with
      | cons names tail =>
          cases tail
          change _ = _ at names
          cases names
          exact .refl _
  | abstraction =>
      cases equal with
      | cons bodies tail => cases tail; exact .abstraction bodies
  | application =>
      cases equal with
      | cons functions tail =>
          cases tail with
          | cons arguments tail =>
              cases tail
              change _ = _ at arguments
              cases arguments
              exact .application _ functions
  | definition =>
      cases equal with
      | cons values tail =>
          cases tail with
          | cons bodies tail => cases tail; exact .definition values bodies
  | carrier =>
      cases equal with
      | cons names tail =>
          cases tail with
          | cons values tail =>
              cases tail with
              | cons bodies tail =>
                  cases tail
                  change _ = _ at names
                  cases names
                  exact .carrier _ values bodies

mutual

theorem eqClosure_sound : ∀ {Γ : Ctx signature} {sort : Srt} {first last : Term signature Γ sort},
    EqClosure equations first last → Same first last
  | _, _, _, _, .ax index body ambient ordinary => axiom_sound index body ambient ordinary
  | _, _, _, _, .refl term => same_refl term
  | _, _, _, _, .symm equal => same_symm (eqClosure_sound equal)
  | _, _, _, _, .trans before after => same_trans (eqClosure_sound before) (eqClosure_sound after)
  | _, _, _, _, .cong operator args => same_cong operator (eqArgs_sound args)

theorem eqArgs_sound : ∀ {Γ : Ctx signature} {arity : List (List Srt × Srt)}
    {first last : Args signature arity Γ}, EqArgs equations first last → SameArgs first last
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons before after => .cons (eqClosure_sound before) (eqArgs_sound after)

end

theorem declared_appDefinition {Γ : Ctx signature} (value : Program Γ)
    (body : Program (.nm :: Γ)) (argument : Name Γ) :
    EqClosure equations (application (definition value body) argument)
      (definition value (application body (Mettapedia.OSLF.Binding.weaken argument))) := by
  have declared := EqClosure.ax (E := equations) ⟨0, by decide⟩ (supply body)
    (fun _ position => .var position)
    (argsToSub (S := signature) (bs := [Srt.tm, Srt.nm]) (.cons value (.cons argument .nil)))
  dsimp only [equations, List.get, appDefinition, schemaApplication, schemaDefinition,
    boundBody, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, supply] at declared
  rw [ContextualAssignment.weakenSub_nil, ContextualAssignment.weakenSub_nil] at declared
  change EqClosure equations
    (application (definition value
      (Mettapedia.OSLF.Binding.bind (joinSub (dependencies := [Srt.nm])
        (argsToSub (S := signature) (bs := [Srt.nm])
          (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
        (weakenSub [Srt.nm] (fun _ position => .var position : Sub signature Γ Γ))) body)) argument)
    (definition value (application
      (Mettapedia.OSLF.Binding.bind (joinSub (dependencies := [Srt.nm])
        (argsToSub (S := signature) (bs := [Srt.nm])
          (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
        (weakenSub [Srt.nm] (fun _ position => .var position : Sub signature Γ Γ))) body)
      (Mettapedia.OSLF.Binding.weaken argument))) at declared
  rw [unary_lift, liftSub_var, bind_id] at declared
  exact declared

theorem declared_appCarrier {Γ : Ctx signature} (name : Name Γ) (value body : Program Γ)
    (argument : Name Γ) :
    EqClosure equations (application (carrier name value body) argument)
      (carrier name value (application body argument)) := by
  have declared := EqClosure.ax (E := equations) ⟨1, by decide⟩ (supply (reference (.var .zero)))
    (fun _ position => .var position)
    (argsToSub (S := signature) (bs := [Srt.nm, Srt.tm, Srt.tm, Srt.nm])
      (.cons name (.cons value (.cons body (.cons argument .nil)))))
  dsimp only [equations, List.get, appCarrier, schemaApplication, schemaCarrier,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs] at declared
  simp only [liftSub] at declared
  exact declared

theorem staticEq_complete {Γ : Ctx signature} {first last : Program Γ}
    (equal : StaticEq first last) : EqClosure equations first last := by
  induction equal with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ before after => exact .trans before after
  | appDefinition value body argument => exact declared_appDefinition value body argument
  | appCarrier name value body argument => exact declared_appCarrier name value body argument
  | abstraction _ ih => exact EqClosure.cong (E := equations) Operator.abstraction (.cons ih .nil)
  | application argument _ ih =>
      exact EqClosure.cong (E := equations) Operator.application (.cons ih (.cons (.refl argument) .nil))
  | definition _ _ values bodies =>
      exact EqClosure.cong (E := equations) Operator.definition (.cons values (.cons bodies .nil))
  | carrier name _ _ values bodies =>
      exact EqClosure.cong (E := equations) Operator.carrier (.cons (.refl name) (.cons values (.cons bodies .nil)))

theorem eqClosure_iff_staticEq {Γ : Ctx signature} (first last : Program Γ) :
    EqClosure equations first last ↔ StaticEq first last := ⟨eqClosure_sound, staticEq_complete⟩

theorem name_eqClosure_iff {Γ : Ctx signature} (first last : Name Γ) :
    EqClosure equations first last ↔ first = last :=
  ⟨eqClosure_sound, fun same => same ▸ .refl first⟩

noncomputable abbrev algebra := BindingEquationQuotientModel.algebra equations
noncomputable abbrev projection := BindingEquationQuotientModel.projection equations

end Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredEquations
