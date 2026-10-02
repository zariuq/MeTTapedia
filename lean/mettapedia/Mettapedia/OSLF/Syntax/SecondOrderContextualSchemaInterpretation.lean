import Mettapedia.OSLF.Syntax.SecondOrderSchemaInterpretation
import Mettapedia.OSLF.Syntax.BindingContextualEquationInterpretation

/-!
# Contextual authored schemas in an extended term algebra

The original operators of an authored schema and the free metavariables of
its ambient second-order context remain separate. The shared contextual
semantic fold in that extended term algebra is exactly the established
syntactic instantiator on the lifted schema.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open FreeBindingTerms
open BindingEquationalModels

variable {S : Signature} {schema : List (MetaArity S)}

private theorem weakenVar_extension (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (v : Var Γ s) : ∀ (bs : Ctx S),
    @weakenVar S Γ s bs v = @weakenVar (withMetas S X.arities) Γ s bs v
  | [] => rfl
  | _ :: bs => congrArg Var.succ (weakenVar_extension X v bs)

private theorem joinEnvironment_extension (X : Object S) {Γ Δ : Ctx S} :
    ∀ (dependencies : Ctx S) (arguments : Sub (withMetas S X.arities) dependencies Δ)
      (ambient : Sub (withMetas S X.arities) Γ Δ),
      SemanticContextualMetavariables.joinEnvironment
        (S := S) (F := fun Γ s => Term (withMetas S X.arities) Γ s) arguments ambient =
        ContextualAssignment.joinSub arguments ambient
  | [], _, _ => rfl
  | _ :: dependencies, arguments, ambient => by
    funext s v
    cases v with
    | zero => rfl
    | succ old => exact congrFun (congrFun
        (joinEnvironment_extension X dependencies (fun s v => arguments s (.succ v)) ambient) s) old

theorem termAlgebra_weakenEnvironment (X : Object S) {Γ Δ : Ctx S}
    (ambient : Sub (withMetas S X.arities) Γ Δ) (bs : Ctx S) :
    SemanticContextualMetavariables.weakenEnvironment (termAlgebra X) bs ambient =
      ContextualAssignment.weakenSub (S := withMetas S X.arities) bs ambient := by
  funext s v
  dsimp only [SemanticContextualMetavariables.weakenEnvironment, termAlgebra,
    restrictedSubstitution, ContextualAssignment.weakenSub]
  refine (bind_var_eq_rename (S := withMetas S X.arities)
    (fun s v => @weakenVar S Δ s bs v) (ambient s v)).trans ?_
  congr 1
  funext s v
  exact weakenVar_extension X v bs

mutual

/-- The semantic contextual fold over the original operators equals
instantiation of their authored schema in the extended signature. -/
theorem interpretContextualSchema_liftSchema (X : Object S) {Γ Ξ Δ : Ctx S}
    (body : ContextualAssignment (withMetas S X.arities) schema Γ)
    (ambient : Sub (withMetas S X.arities) Γ Δ)
    (ordinary : Sub (withMetas S X.arities) Ξ Δ) :
    ∀ {s : S.Srt} (term : Term (withMetas S schema) Ξ s),
      SemanticContextualMetavariables.interpretSchema (termAlgebra X)
        body ambient ordinary term =
      ContextualAssignment.instantiate body ambient ordinary (liftSchema X term)
  | _, .var _ => rfl
  | _, .op (.inl op) args => by
    change Term.op (S := withMetas S X.arities) (.inl op)
        (toSyntax X (SemanticContextualMetavariables.interpretArgs (termAlgebra X)
          body ambient ordinary args)) =
      Term.op (S := withMetas S X.arities) (.inl op)
        (ContextualAssignment.instantiateArgs body ambient ordinary (liftSchemaArgs X args))
    exact congrArg (Term.op (S := withMetas S X.arities) (.inl op))
      (interpretContextualSchemaArgs_liftSchema X body ambient ordinary args)
  | _, .op (.inr (.mk k)) args => by
    simp only [SemanticContextualMetavariables.interpretSchema, SemanticContextualMetavariables.apply,
      liftSchema, ContextualAssignment.instantiate, ContextualAssignment.apply]
    dsimp only [termAlgebra, restrictedSubstitution]
    change bind (S := withMetas S X.arities) (SemanticContextualMetavariables.joinEnvironment
        (S := S) (F := fun Γ s => Term (withMetas S X.arities) Γ s)
        (argsEnvironment (termAlgebra X)
          (SemanticContextualMetavariables.interpretArgs (termAlgebra X)
            body ambient ordinary args)) ambient) (body k) =
      bind (S := withMetas S X.arities) (ContextualAssignment.joinSub (S := withMetas S X.arities)
        (argsToSub (S := withMetas S X.arities) (ContextualAssignment.instantiateArgs body ambient ordinary (liftSchemaArgs X args)))
        ambient) (body k)
    have arguments : argsEnvironment (termAlgebra X)
        (SemanticContextualMetavariables.interpretArgs (termAlgebra X) body ambient ordinary args) =
        argsToSub (S := withMetas S X.arities) (ContextualAssignment.instantiateArgs body ambient ordinary (liftSchemaArgs X args)) :=
      (argsEnvironment_toSyntax X _).trans (congrArg argsToSub
        (interpretContextualSchemaArgs_liftSchema X body ambient ordinary args))
    rw [arguments, joinEnvironment_extension]
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize]
  all_goals omega

/-- The schema comparison preserves the whole ordered argument list and
the separate lift of ordinary variables and weakening of captured values. -/
theorem interpretContextualSchemaArgs_liftSchema (X : Object S) {Γ Ξ Δ : Ctx S}
    (body : ContextualAssignment (withMetas S X.arities) schema Γ)
    (ambient : Sub (withMetas S X.arities) Γ Δ)
    (ordinary : Sub (withMetas S X.arities) Ξ Δ) :
    ∀ {L : List (MetaArity S)} (args : Args (withMetas S schema) L Ξ),
      toSyntax X (SemanticContextualMetavariables.interpretArgs (termAlgebra X)
        body ambient ordinary args) =
      ContextualAssignment.instantiateArgs body ambient ordinary (liftSchemaArgs X args)
  | _, .nil => rfl
  | _, .cons (bs := bs) head tail => by
    change Args.cons (SemanticContextualMetavariables.interpretSchema (termAlgebra X) body
        (SemanticContextualMetavariables.weakenEnvironment (termAlgebra X) bs ambient)
        ((restrictedSubstitution X).liftEnvironment ordinary bs) head)
        (toSyntax X (SemanticContextualMetavariables.interpretArgs (termAlgebra X)
          body ambient ordinary tail)) =
      Args.cons (ContextualAssignment.instantiate body (ContextualAssignment.weakenSub (S := withMetas S X.arities) bs ambient)
        (liftSub ordinary bs) (liftSchema X head))
        (ContextualAssignment.instantiateArgs body ambient ordinary (liftSchemaArgs X tail))
    rw [termAlgebra_weakenEnvironment, restricted_liftEnvironment]
    exact congrArg₂ Args.cons
      (interpretContextualSchema_liftSchema X body _ _ head)
      (interpretContextualSchemaArgs_liftSchema X body ambient ordinary tail)
termination_by _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

/-- Changing the second-order program base transports every contextual
body and both independent environments in an authored equation instance. -/
theorem instInto_contextual_liftSchema_instance {X Y : Object S}
    (assignment : X ⟶ Y) {Θ Ξ Γ : Ctx S}
    (body : ContextualAssignment (withMetas S Y.arities) schema Θ)
    (ambient : Sub (withMetas S Y.arities) Θ Γ)
    (ordinary : Sub (withMetas S Y.arities) Ξ Γ) {s : S.Srt}
    (term : Term (withMetas S schema) Ξ s) :
    instInto assignment
        (ContextualAssignment.instantiate body ambient ordinary (liftSchema Y term)) =
      ContextualAssignment.instantiate (fun i => instInto assignment (body i))
        (fun s v => instInto assignment (ambient s v))
        (fun s v => instInto assignment (ordinary s v)) (liftSchema X term) := by
  rw [← interpretContextualSchema_liftSchema Y body ambient ordinary term,
    ← interpretContextualSchema_liftSchema X
      (fun i => instInto assignment (body i))
      (fun s v => instInto assignment (ambient s v))
      (fun s v => instInto assignment (ordinary s v)) term]
  exact SemanticContextualMetavariables.interpretSchema_map
    (instIntoHom assignment) body ambient ordinary term

end Mettapedia.OSLF.Binding.SecondOrderContext
