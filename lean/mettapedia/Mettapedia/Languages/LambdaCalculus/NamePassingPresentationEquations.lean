import Mettapedia.Languages.LambdaCalculus.NamePassingPresentation

/-!
# Application scope equations for the open name-passing presentation

The two independently authored application scope laws extend to ordinary
term variables in every stored and binding position. Definitions bind their
reference only in the body. This presentation records these two scope laws;
it does not attribute additional recursive-definition axioms to the abridged
constructor signature.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation

open Mettapedia.OSLF.Binding

inductive StaticEq : {Γ : Ctx signature} → Program Γ → Program Γ → Prop where
  | refl {Γ} (term : Program Γ) : StaticEq term term
  | symm {Γ} {first second : Program Γ} : StaticEq first second → StaticEq second first
  | trans {Γ} {first middle last : Program Γ} :
      StaticEq first middle → StaticEq middle last → StaticEq first last
  | appDefinition {Γ} (value : Program Γ) (body : Program (.nm :: Γ)) (argument : Name Γ) :
      StaticEq (application (definition value body) argument)
        (definition value (application body (Mettapedia.OSLF.Binding.weaken argument)))
  | appCarrier {Γ} (name : Name Γ) (value body : Program Γ) (argument : Name Γ) :
      StaticEq (application (carrier name value body) argument)
        (carrier name value (application body argument))
  | abstraction {Γ} {first second : Program (.nm :: Γ)} :
      StaticEq first second → StaticEq (abstraction first) (abstraction second)
  | application {Γ} (argument : Name Γ) {first second : Program Γ} :
      StaticEq first second → StaticEq (application first argument) (application second argument)
  | definition {Γ} {firstValue secondValue : Program Γ} {firstBody secondBody : Program (.nm :: Γ)} :
      StaticEq firstValue secondValue → StaticEq firstBody secondBody →
        StaticEq (definition firstValue firstBody) (definition secondValue secondBody)
  | carrier {Γ} (name : Name Γ) {firstValue secondValue firstBody secondBody : Program Γ} :
      StaticEq firstValue secondValue → StaticEq firstBody secondBody →
        StaticEq (carrier name firstValue firstBody) (carrier name secondValue secondBody)

theorem StaticEq.substitution {Γ Δ : Ctx signature} {first second : Program Γ}
    (equal : StaticEq first second) (substitution : Sub signature Γ Δ) :
    StaticEq (Mettapedia.OSLF.Binding.bind substitution first)
      (Mettapedia.OSLF.Binding.bind substitution second) := by
  induction equal generalizing Δ with
  | refl => exact .refl _
  | symm _ inductionHypothesis => exact .symm (inductionHypothesis substitution)
  | trans _ _ firstHypothesis secondHypothesis =>
      exact .trans (firstHypothesis substitution) (secondHypothesis substitution)
  | appDefinition value body argument =>
      simp only [Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.definition,
        Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.application, Mettapedia.OSLF.Binding.bind, bindArgs]
      have boundArgument : Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) (Mettapedia.OSLF.Binding.weaken argument) =
          Mettapedia.OSLF.Binding.weaken (Mettapedia.OSLF.Binding.bind substitution argument) := by
        simp only [Mettapedia.OSLF.Binding.weaken, bind_rename, rename_bind]
        apply congrArg (fun assigned => Mettapedia.OSLF.Binding.bind assigned argument)
        funext s position
        rfl
      change StaticEq
        (Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.application
          (Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.definition
            (Mettapedia.OSLF.Binding.bind substitution value)
            (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) body))
          (Mettapedia.OSLF.Binding.bind substitution argument))
        (Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.definition
          (Mettapedia.OSLF.Binding.bind substitution value)
          (Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.application
            (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) body)
            (Mettapedia.OSLF.Binding.bind (liftSub substitution [.nm]) (Mettapedia.OSLF.Binding.weaken argument))))
      rw [boundArgument]
      exact .appDefinition _ _ _
  | appCarrier name value body argument =>
      exact .appCarrier _ _ _ _
  | abstraction _ inductionHypothesis => exact .abstraction (inductionHypothesis (liftSub substitution [.nm]))
  | application argument _ inductionHypothesis => exact .application _ (inductionHypothesis substitution)
  | definition _ _ valueHypothesis bodyHypothesis =>
      exact .definition (valueHypothesis substitution) (bodyHypothesis (liftSub substitution [.nm]))
  | carrier name _ _ valueHypothesis bodyHypothesis =>
      exact .carrier _ (valueHypothesis substitution) (bodyHypothesis substitution)

/-- A root edge is a supplied occurrence, rather than a Boolean assertion of
reachability. Its contextual closure follows the active operational positions. -/
inductive ActiveEdge : {Γ : Ctx signature} → Program Γ → Program Γ → Type where
  | root {Γ} {first second : Program Γ} : RootEdge first second → ActiveEdge first second
  | application {Γ} (argument : Name Γ) {first second : Program Γ} :
      ActiveEdge first second → ActiveEdge (application first argument) (application second argument)
  | definition {Γ} (value : Program Γ) {first second : Program (.nm :: Γ)} :
      ActiveEdge first second → ActiveEdge (definition value first) (definition value second)
  | carrier {Γ} (name : Name Γ) (value : Program Γ) {first second : Program Γ} :
      ActiveEdge first second → ActiveEdge (carrier name value first) (carrier name value second)

end Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation
