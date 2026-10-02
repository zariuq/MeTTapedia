import Mettapedia.OSLF.Syntax.CategoricalBindingStageOperations
import Mettapedia.OSLF.Syntax.CategoricalBindingEquationSatisfaction
import Mettapedia.OSLF.Syntax.SecondOrderAuthoredEquationPresentation
import Mettapedia.OSLF.Syntax.SecondOrderContextualSchemaInterpretation
import Mettapedia.OSLF.Syntax.BindingContextualEquationInterpretation
import Mettapedia.OSLF.Syntax.BindingEquationInterpretation

/-!
# Ambient equation instances in categorical binding models

Selected function objects represent arbitrary natural metavariable bodies.
Global satisfaction of authored equations therefore supplies equation laws
in every generalized-element binding clone, including bodies parameterized
by a stage object.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open _root_.CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open FreeBindingTerms
open SecondOrderContext
open BindingEquationalModels

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable {S : Signature} (M : Model S D)

private theorem toSyntax_ambient (X : Object S) :
    ∀ {L : List (MetaArity S)} {Γ : Ctx S}
      (args : FamilyArgs S (restrictedSubstitution X).Carrier L Γ),
      toSyntax X args = terms.familyToSyntax (withMetas S X.arities)
        (toAmbientArgs X args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (Args.cons head) (toSyntax_ambient X tail)

private def restrictedTermsHom (X : Object S) :
    FreeBindingClone.Hom (termAlgebra X)
      (restrictAlgebra X (BindingCloneAlgebra.terms (withMetas S X.arities))) where
  raw :=
    { map := fun t => t
      map_variable := fun _ => rfl
      map_operation := by
        intro Γ s o args
        change Term.op (S := withMetas S X.arities) (Sum.inl o) (toSyntax X args) =
          Term.op (S := withMetas S X.arities) (Sum.inl o) (terms.familyToSyntax _
            (toAmbientArgs X (FamilyArgs.map (fun t => t) args)))
        have same : FamilyArgs.map (fun t => t) args = args := FamilyArgs.map_id args
        exact congrArg (Term.op (S := withMetas S X.arities) (Sum.inl o))
          ((toSyntax_ambient X args).trans (congrArg
            (fun a => terms.familyToSyntax (withMetas S X.arities) (toAmbientArgs X a))
              same.symm)) }
  map_substitute := by intro Γ Δ s env t; rfl

/-- Interpreting extended syntax at a family point is a binding-clone map
over the original signature. -/
def termPointHom (X : Object S) {Z : D} (p : Z ⟶ M.family X.arities) :
    FreeBindingClone.Hom (termAlgebra X) (M.stage Z) :=
  FreeBindingClone.Hom.comp
    (FreeBindingClone.Hom.comp (restrictedTermsHom X)
      (restrictHom X (FreeBindingClone.interpretHom (M.kripke X.arities))))
    (M.restageHom X p)

theorem termPointHom_map (X : Object S) {Z : D} (p : Z ⟶ M.family X.arities)
    {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S X.arities) Γ s) :
    (M.termPointHom X p).raw.map t = M.restageElem p (M.interp X.arities t) := rfl

/-- A selected family point realizes every semantic schema-body valuation. -/
def schemaPoint {schema : List (MetaArity S)} {Z : D}
    (body : MetaValuation (M.stage Z) schema) : Z ⟶ M.family schema :=
  M.familyLift schema (fun i => M.elemEquiv (body i))

theorem schemaPoint_body {schema : List (MetaArity S)} {Z : D}
    (body : MetaValuation (M.stage Z) schema) (i : Fin schema.length) :
    (M.termPointHom ⟨schema⟩ (M.schemaPoint body)).raw.map (metaVar i) = body i := by
  rw [M.termPointHom_map, M.restageElem_interp_metaVar]
  unfold schemaPoint
  rw [M.familyLift_proj]
  exact M.elemEquiv.left_inv (body i)

/-- Global categorical satisfaction entails equality at every semantic
schema-body valuation in each generalized-element stage. -/
theorem stage_schema_sound {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema))
    (sat : M.DependencySatisfies (authoredEquationPresentation S equations))
    (Z : D) (i : Fin equations.length) (body : MetaValuation (M.stage Z) schema) :
    BindingEquationInterpretation.interpretSchema (M.stage Z) body (equations.get i).lhs =
      BindingEquationInterpretation.interpretSchema (M.stage Z) body (equations.get i).rhs := by
  let X : Object S := ⟨schema⟩
  let genericBody : MetaValuation (termAlgebra X) schema := fun k => metaVar k
  let h := M.termPointHom X (M.schemaPoint body)
  have bodyEq : BindingEquationInterpretation.mapMetaValuation h genericBody = body := by
    funext k
    exact M.schemaPoint_body body k
  rw [← bodyEq, ← BindingEquationInterpretation.interpretSchema_map,
    ← BindingEquationInterpretation.interpretSchema_map]
  rw [interpretSchema_liftSchema, interpretSchema_liftSchema]
  let liftedIndex : Fin (equations.map (liftEquation X)).length :=
    ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩
  have equationAt : (equations.map (liftEquation X)).get liftedIndex =
      liftEquation X (equations.get i) := by
    change (equations.map (liftEquation X))[i.val] = liftEquation X (equations[i.val])
    simp
  have equality := sat X liftedIndex genericBody
  change M.interp X.arities
      (instantiate genericBody ((equations.map (liftEquation X)).get liftedIndex).lhs) =
    M.interp X.arities
      (instantiate genericBody ((equations.map (liftEquation X)).get liftedIndex).rhs) at equality
  rw [equationAt] at equality
  exact congrArg (M.restageElem (M.schemaPoint body)) equality

/-- Each stage clone satisfies the authored equations under arbitrary
semantic bodies and ordinary environments. -/
theorem stage_dependencySatisfies {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema))
    (sat : M.DependencySatisfies (authoredEquationPresentation S equations)) (Z : D) :
    BindingEquationInterpretation.DependencySatisfies (M.stage Z) equations := by
  intro i body Γ env
  exact congrArg ((M.stage Z).substitution.substitute env)
    (M.stage_schema_sound equations sat Z i body)

private def joinEnv {W : D} {Γ Δ : Ctx S} (arguments : M.Env W Γ)
    (ambient : M.Env W Δ) : M.Env W (Γ ++ Δ) :=
  SemanticContextualMetavariables.joinEnvironment
    (F := fun _ s => W ⟶ M.sort s) (Δ := []) arguments ambient

private theorem joinEnv_restage {W V : D} (h : V ⟶ W) {Γ Δ : Ctx S}
    (arguments : M.Env W Γ) (ambient : M.Env W Δ) :
    M.joinEnv (M.restage h arguments) (M.restage h ambient) =
      M.restage h (M.joinEnv arguments ambient) := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih =>
    funext sort index
    cases index with
    | zero => rfl
    | succ old => exact congrFun (congrFun
        (ih (fun s v => arguments s (.succ v))) sort) old

/-- Fix the ambient values of a contextual body while retaining its declared
dependency variables. The fixed values live in the stage parameter. -/
def captureBody {Z W : D} {dependencies Γ : Ctx S} {s : S.Srt}
    (body : M.ElemOver Z (dependencies ++ Γ) s) (w : W ⟶ Z)
    (ambient : M.Env W Γ) : M.ElemOver W dependencies s where
  value U point arguments :=
    body.value U (point ≫ w) (M.joinEnv arguments (M.restage point ambient))
  natural h point arguments := by
    rw [Category.assoc, ← body.natural]
    congr 1
    rw [← M.joinEnv_restage]
    congr 1
    funext s v
    exact Category.assoc h point (ambient s v)

theorem captureBody_restage {Z W V : D} {dependencies Γ : Ctx S} {s : S.Srt}
    (body : M.ElemOver Z (dependencies ++ Γ) s) (w : W ⟶ Z)
    (ambient : M.Env W Γ) (h : V ⟶ W) :
    M.captureBody body (h ≫ w) (M.restage h ambient) =
      M.restageElem h (M.captureBody body w ambient) := by
  apply ElemOver.ext
  funext U point arguments
  change body.value U (point ≫ h ≫ w)
      (M.joinEnv arguments (M.restage point (M.restage h ambient))) =
    body.value U ((point ≫ h) ≫ w)
      (M.joinEnv arguments (M.restage (point ≫ h) ambient))
  rw [Category.assoc]
  congr 1
  congr 1
  funext s v
  exact (Category.assoc point h (ambient s v)).symm

private theorem envValue_join {Z W : D} {dependencies Γ Δ : Ctx S}
    (arguments : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier
      dependencies Δ)
    (ambient : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Δ)
    (w : W ⟶ Z) (ρ : M.Env W Δ) :
    envValue (SemanticContextualMetavariables.joinEnvironment arguments ambient) W w ρ =
      M.joinEnv (envValue arguments W w ρ) (envValue ambient W w ρ) := by
  induction dependencies with
  | nil => rfl
  | cons s dependencies ih =>
    funext sort index
    cases index with
    | zero => rfl
    | succ old => exact congrFun (congrFun
        (ih (fun s v => arguments s (.succ v))) sort) old

private theorem weakenEnvironment_value {Z W : D} {Γ Δ : Ctx S}
    (ambient : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Δ)
    (w : W ⟶ Z) (ρ : M.Env W Δ) (bs : Ctx S) :
    envValue (SemanticContextualMetavariables.weakenEnvironment (M.stage Z) bs ambient)
      (M.ctx bs ⊗ W) (snd _ _ ≫ w) (M.extendEnv bs ρ) =
      M.restage (snd _ _) (envValue ambient W w ρ) := by
  funext s index
  change (ambient s index).value _ (snd _ _ ≫ w)
    (fun s v => M.extendEnv bs ρ s (weakenVar bs v)) = _
  have envEq : (fun s v => M.extendEnv bs ρ s (weakenVar bs v)) =
      M.restage (snd _ _) ρ := by
    funext s v
    exact M.extendEnv_old bs ρ v
  rw [envEq, (ambient s index).natural]
  rfl

private theorem weakenEnvironment_nil {Z : D} {Γ Δ : Ctx S}
    (ambient : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Δ) :
    SemanticContextualMetavariables.weakenEnvironment (M.stage Z) [] ambient = ambient := by
  funext s v
  exact (M.stage Z).substitution.substitute_identity (ambient s v)

theorem captureBody_value_id {Z W : D} {dependencies Γ : Ctx S} {s : S.Srt}
    (body : M.ElemOver Z (dependencies ++ Γ) s) (w : W ⟶ Z)
    (ambient : M.Env W Γ) (arguments : M.Env W dependencies) :
    (M.captureBody body w ambient).value W (𝟙 W) arguments =
      body.value W w (M.joinEnv arguments ambient) := by
  change body.value W ((𝟙 W) ≫ w) (M.joinEnv arguments (M.restage (𝟙 W) ambient)) = _
  rw [Category.id_comp]
  congr 1
  congr 1
  funext s v
  exact Category.id_comp (ambient s v)

mutual

/-- Evaluating a contextual schema fixes its ambient values in the stage
parameter; the remaining interpretation is the ordinary schema fold. -/
theorem contextualSchema_value {schema : List (MetaArity S)} {Z W : D}
    {Γ Ξ Δ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := schema) (M.stage Z) Γ)
    (ambient : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Δ)
    (ordinary : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Ξ Δ)
    (w : W ⟶ Z) (ρ : M.Env W Δ) :
    ∀ {s : S.Srt} (term : Term (withMetas S schema) Ξ s),
      (SemanticContextualMetavariables.interpretSchema (M.stage Z) body ambient ordinary term).value
          W w ρ =
        (BindingEquationInterpretation.interpretSchema (M.stage W)
          (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) term).value
          W (𝟙 W) (envValue ordinary W w ρ)
  | _, .var _ => rfl
  | _, .op (.inl op) args => by
    change M.tupleArgs (toAmbientArgs ⟨[]⟩
        (SemanticContextualMetavariables.interpretArgs (M.stage Z) body ambient ordinary args))
        W w ρ ≫ M.op op =
      M.tupleArgs (toAmbientArgs ⟨[]⟩
        (BindingEquationInterpretation.interpretSchemaArgs (M.stage W)
          (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) args))
        W (𝟙 W) (envValue ordinary W w ρ) ≫ M.op op
    exact congrArg (· ≫ M.op op)
      (contextualSchemaArgs_tuple body ambient ordinary w ρ args)
  | _, .op (.inr (.mk k)) args => by
    change (body k).value W w
        (envValue (SemanticContextualMetavariables.joinEnvironment
          (argsEnvironment (M.stage Z)
            (SemanticContextualMetavariables.interpretArgs (M.stage Z) body ambient ordinary args))
          ambient) W w ρ) =
      (M.captureBody (body k) w (envValue ambient W w ρ)).value W (𝟙 W)
        (envValue (argsEnvironment (M.stage W)
          (BindingEquationInterpretation.interpretSchemaArgs (M.stage W)
            (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) args))
          W (𝟙 W) (envValue ordinary W w ρ))
    have envEq := M.envValue_join
      (argsEnvironment (M.stage Z)
        (SemanticContextualMetavariables.interpretArgs (M.stage Z) body ambient ordinary args))
      ambient w ρ
    have argsEq : envValue (argsEnvironment (M.stage Z)
        (SemanticContextualMetavariables.interpretArgs (M.stage Z) body ambient ordinary args))
        W w ρ = envValue (argsEnvironment (M.stage W)
        (BindingEquationInterpretation.interpretSchemaArgs (M.stage W)
          (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) args))
        W (𝟙 W) (envValue ordinary W w ρ) := by
      funext s v
      exact contextualSchemaArgs_environment body ambient ordinary w ρ args s v
    exact (congrArg ((body k).value W w) envEq).trans
      ((congrArg (fun a => (body k).value W w (M.joinEnv a (envValue ambient W w ρ)))
        argsEq).trans (M.captureBody_value_id (body k) w _ _).symm)
termination_by _ term => 3 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize]
  all_goals omega

/-- Ordered argument tuples agree under ambient specialization, including
the selected function object of every binder-local argument. -/
theorem contextualSchemaArgs_tuple {schema : List (MetaArity S)} {Z W : D}
    {Γ Ξ Δ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := schema) (M.stage Z) Γ)
    (ambient : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Δ)
    (ordinary : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Ξ Δ)
    (w : W ⟶ Z) (ρ : M.Env W Δ) :
    ∀ {L : List (MetaArity S)} (args : Args (withMetas S schema) L Ξ),
      M.tupleArgs (toAmbientArgs ⟨[]⟩
        (SemanticContextualMetavariables.interpretArgs (M.stage Z) body ambient ordinary args))
        W w ρ =
      M.tupleArgs (toAmbientArgs ⟨[]⟩
        (BindingEquationInterpretation.interpretSchemaArgs (M.stage W)
          (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) args))
        W (𝟙 W) (envValue ordinary W w ρ)
  | _, .nil => rfl
  | _, .cons (bs := bs) head tail => by
    change lift (M.curry _) _ = lift (M.curry _) _
    rw [contextualSchemaArgs_tuple body ambient ordinary w ρ tail]
    congr 2
    have value := contextualSchema_value body
      (SemanticContextualMetavariables.weakenEnvironment (M.stage Z) bs ambient)
      ((M.stage Z).substitution.liftEnvironment ordinary bs)
      (snd (M.ctx bs) W ≫ w) (M.extendEnv bs ρ) head
    have ordinaryValue : envValue ((M.stage Z).substitution.liftEnvironment ordinary bs)
        (M.ctx bs ⊗ W) (snd _ _ ≫ w) (M.extendEnv bs ρ) =
        M.extendEnv bs (envValue ordinary W w ρ) := by
      funext s v
      change envValue ((restrictSubstitution ⟨[]⟩ (M.stageKripke Z)).liftEnvironment ordinary bs)
        (M.ctx bs ⊗ W) (snd _ _ ≫ w) (M.extendEnv bs ρ) s v = _
      have eqLift := restrict_liftEnvironment ⟨[]⟩ (M.stageKripke Z) ordinary bs
      exact (congrArg
        (fun env : ∀ s, Var (bs ++ Ξ) s → M.ElemOver Z (bs ++ Δ) s =>
          (env s v).value (M.ctx bs ⊗ W) (snd _ _ ≫ w) (M.extendEnv bs ρ))
        eqLift).trans (M.liftEnvironment_value ordinary W w ρ bs v)
    rw [M.weakenEnvironment_value, ordinaryValue] at value
    have captured : (fun i => M.captureBody (body i) (snd (M.ctx bs) W ≫ w)
        (M.restage (snd _ _) (envValue ambient W w ρ))) =
        BindingEquationInterpretation.mapMetaValuation (M.stageRestage (snd _ _))
          (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) := by
      funext i
      exact M.captureBody_restage (body i) w _ _
    rw [captured] at value
    have mapped := BindingEquationInterpretation.interpretSchema_map
      (M.stageRestage (snd (M.ctx bs) W))
      (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) head
    have mappedValue := congrArg
      (fun e : M.ElemOver (M.ctx bs ⊗ W) (bs ++ Ξ) _ =>
        e.value (M.ctx bs ⊗ W) (𝟙 _) (M.extendEnv bs (envValue ordinary W w ρ))) mapped
    have final := value.trans mappedValue.symm
    simpa only [FreeBindingClone.Hom.raw, stageRestage, restageElem, Category.id_comp,
      Category.comp_id] using final
termination_by _ args => 3 * argsSize args + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

/-- Dependency arguments are read in their authored order after ambient
specialization. -/
theorem contextualSchemaArgs_environment {schema : List (MetaArity S)} {Z W : D}
    {Γ Ξ Δ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := schema) (M.stage Z) Γ)
    (ambient : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Γ Δ)
    (ordinary : BindingSubstitutionAlgebra.Environment S (M.stage Z).substitution.Carrier Ξ Δ)
    (w : W ⟶ Z) (ρ : M.Env W Δ) :
    ∀ {dependencies : Ctx S}
      (args : Args (withMetas S schema) (dependencies.map (fun s => ([], s))) Ξ)
      (s : S.Srt) (v : Var dependencies s),
      envValue (argsEnvironment (M.stage Z)
        (SemanticContextualMetavariables.interpretArgs (M.stage Z) body ambient ordinary args))
        W w ρ s v =
      envValue (argsEnvironment (M.stage W)
        (BindingEquationInterpretation.interpretSchemaArgs (M.stage W)
          (fun i => M.captureBody (body i) w (envValue ambient W w ρ)) args))
        W (𝟙 W) (envValue ordinary W w ρ) s v
  | [], .nil, _, v => nomatch v
  | _ :: _, .cons head _tail, _, .zero => by
    change (SemanticContextualMetavariables.interpretSchema (M.stage Z) body
      (SemanticContextualMetavariables.weakenEnvironment (M.stage Z) [] ambient) ordinary head).value
        W w ρ = _
    rw [M.weakenEnvironment_nil]
    exact contextualSchema_value body ambient ordinary w ρ head
  | _ :: _, .cons _head tail, s, .succ v =>
    contextualSchemaArgs_environment body ambient ordinary w ρ tail s v
termination_by _ args _ _ => 3 * argsSize args + 2
decreasing_by
  all_goals simp_wf
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos _head; omega

end

/-- The existing global categorical model contract supplies contextual
equation satisfaction at every stage, including captured ambient values. -/
theorem stage_contextualSatisfies {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema))
    (sat : M.DependencySatisfies (authoredEquationPresentation S equations)) (Z : D) :
    BindingContextualEquationInterpretation.Satisfies (M.stage Z) equations := by
  intro i Γ Δ body ambient ordinary
  apply ElemOver.ext
  funext W w ρ
  have equality := M.stage_schema_sound equations sat W i
    (fun k => M.captureBody (body k) w (envValue ambient W w ρ))
  exact (M.contextualSchema_value body ambient ordinary w ρ (equations.get i).lhs).trans
    ((congrArg (fun e : M.ElemOver W (equations.get i).ctx (equations.get i).sort =>
      e.value W (𝟙 W) (envValue ordinary W w ρ)) equality).trans
        (M.contextualSchema_value body ambient ordinary w ρ (equations.get i).rhs).symm)

/-- Canonical categorical satisfaction supplies the full contextual
semantic equation contract in every generalized-element stage. -/
theorem stage_satisfies {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema))
    (sat : M.Satisfies (authoredEquationPresentation S equations)) (Z : D) :
    BindingEquationInterpretation.Satisfies (M.stage Z) equations :=
  M.stage_contextualSatisfies equations (Satisfies.toDependencySatisfies M sat) Z

/-- Actual contextual equation instances have equal interpretations in
every generalized-element stage. -/
theorem stage_contextual_instance {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema))
    (sat : M.DependencySatisfies (authoredEquationPresentation S equations)) (Z : D)
    (i : Fin equations.length) {Γ Δ : Ctx S} (body : ContextualAssignment S schema Γ)
    (ambient : Sub S Γ Δ) (ordinary : Sub S (equations.get i).ctx Δ) :
    BindingCloneFoldSubstitution.interpret (M.stage Z)
        (ContextualAssignment.instantiate body ambient ordinary (equations.get i).lhs) =
      BindingCloneFoldSubstitution.interpret (M.stage Z)
        (ContextualAssignment.instantiate body ambient ordinary (equations.get i).rhs) :=
  (M.stage_contextualSatisfies equations sat Z).interpret_instance i body ambient ordinary

/-- A family point interprets every contextual instance of a lifted
authored equation, using the existing global satisfaction contract. -/
theorem termPoint_contextual_instance {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema))
    (sat : M.DependencySatisfies (authoredEquationPresentation S equations))
    (X : Object S) {Z : D} (p : Z ⟶ M.family X.arities)
    (i : Fin equations.length) {Γ Δ : Ctx S}
    (body : ContextualAssignment (withMetas S X.arities) schema Γ)
    (ambient : Sub (withMetas S X.arities) Γ Δ)
    (ordinary : Sub (withMetas S X.arities) (equations.get i).ctx Δ) :
    (M.termPointHom X p).raw.map
        (ContextualAssignment.instantiate body ambient ordinary (liftSchema X (equations.get i).lhs)) =
      (M.termPointHom X p).raw.map
        (ContextualAssignment.instantiate body ambient ordinary (liftSchema X (equations.get i).rhs)) := by
  let h := M.termPointHom X p
  have lhs := SemanticContextualMetavariables.interpretSchema_map h body ambient ordinary
    (equations.get i).lhs
  have rhs := SemanticContextualMetavariables.interpretSchema_map h body ambient ordinary
    (equations.get i).rhs
  rw [interpretContextualSchema_liftSchema] at lhs rhs
  exact lhs.trans ((M.stage_contextualSatisfies equations sat Z i
    (SemanticContextualMetavariables.mapValuation h body)
    (fun s v => h.raw.map (ambient s v))
    (fun s v => h.raw.map (ordinary s v))).trans rhs.symm)

/-- The interpretation of actual extended syntax identifies every contextual
instance of an authored equation, including arbitrary ambient parameters. -/
theorem interp_contextual_instance {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema))
    (sat : M.DependencySatisfies (authoredEquationPresentation S equations))
    (X : Object S) (i : Fin equations.length) {Γ Δ : Ctx S}
    (body : ContextualAssignment (withMetas S X.arities) schema Γ)
    (ambient : Sub (withMetas S X.arities) Γ Δ)
    (ordinary : Sub (withMetas S X.arities) (equations.get i).ctx Δ) :
    M.interp X.arities
        (ContextualAssignment.instantiate body ambient ordinary (liftSchema X (equations.get i).lhs)) =
      M.interp X.arities
        (ContextualAssignment.instantiate body ambient ordinary (liftSchema X (equations.get i).rhs)) := by
  have equality := M.termPoint_contextual_instance equations sat X (𝟙 _) i body ambient ordinary
  apply ElemOver.ext
  funext W w ρ
  have value := congrArg
    (fun e : M.ElemOver (M.family X.arities) Δ (equations.get i).sort => e.value W w ρ) equality
  change (M.interp X.arities _).value W (w ≫ 𝟙 _) ρ =
    (M.interp X.arities _).value W (w ≫ 𝟙 _) ρ at value
  simpa only [restrictedTermsHom, Category.comp_id] using value

/-- For an authored equation list, contextual satisfaction follows from the
original global contract. No additional equation law is imposed on its models. -/
theorem authored_contextualSatisfies_iff {schema : List (MetaArity S)}
    (equations : List (EqAxiom S schema)) :
    M.ContextualSatisfies (authoredEquationPresentation S equations) ↔
      M.DependencySatisfies (authoredEquationPresentation S equations) := by
  constructor
  · exact Satisfies.toDependencySatisfies M
  · intro sat X
    change M.ContextualSatisfiesAxioms X.arities (equations.map (liftEquation X))
    intro i
    let sourceIndex : Fin equations.length :=
      ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    have equationAt :
        (equations.map (liftEquation X)).get i = liftEquation X (equations.get sourceIndex) := by
      change (equations.map (liftEquation X))[i.val] = liftEquation X (equations[i.val])
      simp
    rw [equationAt]
    intro Θ Δ body ambient ordinary
    exact M.interp_contextual_instance equations sat X sourceIndex body ambient ordinary

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
