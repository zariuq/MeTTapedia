import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafReadback
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonPrograms

/-!
# Contextual equation interpretation in operational presheaves

Authored schema interpretation at a presheaf point uses the original clone's
contextual metavariable values and its independent ordinary environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEquations

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf
open MultiBinderPresheaf BindingFunctionArgumentComparison
open IntrinsicScopedOperationalPresheafPrograms IntrinsicScopedOperationalPresheafReadback
open BindingEquationalModels (argsEnvironment)
open FreeBindingTerms (FamilyArgs)

universe u
variable {S : Signature}

/-- A family point retains each metavariable's complete contextual body. -/
def metaValuation (A : BindingCloneAlgebra.Algebra.{u} S)
    (N : List (MetaArity S)) (X : Base A) (p : ((model A).family N).obj X) :
    SemanticContextualMetavariables.Valuation (M := N) A X.unop.context :=
  fun k => (powerBodiesIso A (N.get k).1 (N.get k).2).hom.app X
    (((model A).familyProj N k).app X p)

/-- Every change of ambient stage substitutes inside all captured bodies,
under precisely their own declared dependency lists. -/
theorem metaValuation_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    (N : List (MetaArity S)) {X Y : Base A} (f : X ⟶ Y)
    (p : ((model A).family N).obj X) :
    metaValuation A N Y (((model A).family N).map f p) =
      IntrinsicScopedConditionalSubstitution.substValuation A
        (fromPositions X.unop.context f.unop) (metaValuation A N X p) := by
  funext k
  have naturality := ((model A).familyProj N k).naturality_apply f p
  have body := (congrArg
    ((powerBodiesIso A (N.get k).1 (N.get k).2).hom.app Y) naturality).trans
    (scopedBodyEquiv_reindex A (N.get k).1 (N.get k).2 f
      (((model A).familyProj N k).app X p))
  change metaValuation A N Y (((model A).family N).map f p) k =
    A.substitution.substitute
      (fromPositions ((N.get k).1 ++ X.unop.context)
        (extendScope A (N.get k).1 f.unop)) (metaValuation A N X p k) at body
  exact body.trans (congrArg
    (fun env => A.substitution.substitute env (metaValuation A N X p k))
    (fromPositions_extendScope A (N.get k).1 f.unop))

/-- Reindexing the captured bodies is exactly post-composing their ambient
environment, without changing the independently supplied ordinary values. -/
theorem schema_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    (N : List (MetaArity S)) {X Y : Base A} (f : X ⟶ Y)
    (p : ((model A).family N).obj X) {Γ : Ctx S} {s : S.Srt}
    (ordinary : Environment S A.substitution.Carrier Γ Y.unop.context)
    (term : Term (withMetas S N) Γ s) :
    SemanticContextualMetavariables.interpretSchema A
        (metaValuation A N Y (((model A).family N).map f p))
        (fun _ v => A.substitution.injectVar v) ordinary term =
      SemanticContextualMetavariables.interpretSchema A (metaValuation A N X p)
        (fromPositions X.unop.context f.unop) ordinary term := by
  rw [metaValuation_reindex]
  simpa only [A.substitution.substitute_identity] using
    (IntrinsicScopedConditionalSubstitution.interpretSchema_postAmbient A
      (fun _ v => A.substitution.injectVar v) (fromPositions X.unop.context f.unop)
      (metaValuation A N X p) ordinary term).symm

private theorem weaken_identity (A : BindingCloneAlgebra.Algebra.{u} S)
    (bs Γ : Ctx S) :
    SemanticContextualMetavariables.weakenEnvironment A bs
        (fun _ v => A.substitution.injectVar v : Environment S A.substitution.Carrier Γ Γ) =
      (fun _ v => A.substitution.injectVar (weakenVar bs v)) := by
  funext s v
  exact A.substitution.substitute_var _ v

private theorem weaken_empty (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Environment S A.substitution.Carrier Γ Δ) :
    SemanticContextualMetavariables.weakenEnvironment A [] env = env := by
  funext s v
  exact A.substitution.substitute_identity (env s v)

mutual

/-- Categorical term interpretation at an arbitrary point is the original
contextual schema interpretation with independent ordinary values. -/
theorem interp_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    (N : List (MetaArity S)) :
    ∀ {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S N) Γ s)
      {W : target A} (m : W ⟶ (model A).family N) (ρ : (model A).Env W Γ)
      (X : Base A) (w : W.obj X),
      programsAtEquiv A s X ((((model A).interp N term).value W m ρ).app X w) =
        SemanticContextualMetavariables.interpretSchema A
          (metaValuation A N X (m.app X w))
          (fun _ v => A.substitution.injectVar v) (readEnv A ρ X w) term
  | _, _, .var _, _, _, _, _, _ => rfl
  | _, _, .op (Sum.inl o) args, W, m, ρ, X, w => by
      have operation := op_body A o X
        (((model A).tupleArgs
          (BindingCloneFoldSubstitution.interpretArgs ((model A).kripke N) args)
          W m ρ).app X w)
      exact operation.trans (congrArg (A.operation o)
        (tupleArgs_value_point A N args m ρ X w))
  | _, _, .op (Sum.inr (MetaOp.mk k)) args, W, m, ρ, X, w => by
      have evaluated := eval_body_substitute A (N.get k).1 (N.get k).2 X
        (((model A).tupleCtx (N.get k).1
          (BindingCloneFoldSubstitution.interpretArgs ((model A).kripke N) args)
          W m ρ).app X w)
        (((model A).familyProj N k).app X (m.app X w))
      exact evaluated.trans (congrArg
        (fun env => A.substitution.substitute
          (SemanticContextualMetavariables.joinEnvironment env
            (fun _ v => A.substitution.injectVar v))
          (metaValuation A N X (m.app X w) k))
        (tupleCtx_value_point A N (N.get k).1 args m ρ X w))
termination_by _ _ term _ _ _ _ _ => 2 * termSize term
decreasing_by all_goals simp only [termSize]; omega

/-- Every categorical argument tuple reads the original ordered semantic
arguments beneath their individually authored binder contexts. -/
theorem tupleArgs_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    (N : List (MetaArity S)) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S N) arities Γ)
      {W : target A} (m : W ⟶ (model A).family N) (ρ : (model A).Env W Γ)
      (X : Base A) (w : W.obj X),
      fromFunctions A (familyAtEquiv A arities X
          (((model A).tupleArgs
            (BindingCloneFoldSubstitution.interpretArgs ((model A).kripke N) args)
            W m ρ).app X w)) =
        SemanticContextualMetavariables.interpretArgs A
          (metaValuation A N X (m.app X w))
          (fun _ v => A.substitution.injectVar v) (readEnv A ρ X w) args
  | _, _, .nil, _, _, _, _, _ => rfl
  | _, _, .cons (bs := bs) (s := _s) head tail, W, m, ρ, X, w => by
      apply congrArg₂ FamilyArgs.cons
      · let E := extendedStage A bs X
        let f : X ⟶ E := Quiver.Hom.op (sndProjection A.substitution.toClone
          (ContextObject.ofList A.substitution.toClone bs) X.unop)
        let p := canonicalPoint A bs X w
        have body := curry_body A
          (((model A).interp N head).value ((model A).ctx bs ⊗ W)
            (snd _ _ ≫ m) ((model A).extendEnv bs ρ)) X w
        have interpreted := interp_value_point A N head (snd _ _ ≫ m)
          ((model A).extendEnv bs ρ) E p
        have parameter :
            metaValuation A N E ((snd ((model A).ctx bs) W ≫ m).app E p) =
              metaValuation A N E (((model A).family N).map f (m.app X w)) :=
          congrArg (metaValuation A N E) (m.naturality_apply f w)
        rw [parameter, readEnv_extend_canonical] at interpreted
        have reindexed := schema_reindex A N f (m.app X w)
          (A.substitution.liftEnvironment (readEnv A ρ X w) bs) head
        have ambient : fromPositions X.unop.context f.unop =
            SemanticContextualMetavariables.weakenEnvironment A bs
              (fun _ v => A.substitution.injectVar v) :=
          (fromPositions_snd A bs X).trans (weaken_identity A bs X.unop.context).symm
        exact body.trans (interpreted.trans (reindexed.trans
          (congrArg (fun env => SemanticContextualMetavariables.interpretSchema A
            (metaValuation A N X (m.app X w)) env
            (A.substitution.liftEnvironment (readEnv A ρ X w) bs) head) ambient)))
      · exact tupleArgs_value_point A N tail m ρ X w
termination_by _ _ args _ _ _ _ _ => 2 * argsSize args + 1
decreasing_by
  all_goals have positive := termSize_pos head
  all_goals simp only [argsSize]; omega

/-- The context tuple of metavariable arguments retains every ordered value. -/
theorem tupleCtx_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    (N : List (MetaArity S)) :
    ∀ (bs : Ctx S) {Γ : Ctx S}
      (args : Args (withMetas S N) (bs.map fun s => ([], s)) Γ)
      {W : target A} (m : W ⟶ (model A).family N) (ρ : (model A).Env W Γ)
      (X : Base A) (w : W.obj X),
      fromPositions bs (contextAtEquiv A bs X
          (((model A).tupleCtx bs
            (BindingCloneFoldSubstitution.interpretArgs ((model A).kripke N) args)
            W m ρ).app X w)) =
        argsEnvironment A (SemanticContextualMetavariables.interpretArgs A
          (metaValuation A N X (m.app X w))
          (fun _ v => A.substitution.injectVar v) (readEnv A ρ X w) args)
  | [], _, .nil, _, _, _, _, _ => by funext s v; exact nomatch v
  | s :: bs, _, .cons head tail, W, m, ρ, X, w => by
      funext result v
      cases v with
      | zero =>
          change programsAtEquiv A s X
            ((((model A).interp N head).value W m ρ).app X w) =
            SemanticContextualMetavariables.interpretSchema A
              (metaValuation A N X (m.app X w))
              (SemanticContextualMetavariables.weakenEnvironment A []
                (fun _ v => A.substitution.injectVar v)) (readEnv A ρ X w) head
          rw [weaken_empty]
          exact interp_value_point A N head m ρ X w
      | succ v =>
          exact congrFun (congrFun (tupleCtx_value_point A N bs tail m ρ X w) result) v
termination_by _ _ args _ _ _ _ _ => 2 * argsSize args + 1
decreasing_by
  all_goals have positive := termSize_pos head
  all_goals simp only [argsSize]; omega

end

open SecondOrderContext

private theorem schemaPoint_proj_app
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (M : CategoricalBindingModel.Model S (target A))
    {N : List (MetaArity S)} {Z : target A}
    (body : BindingEquationalModels.MetaValuation (M.stage Z) N)
    (X : Base A) (z : Z.obj X) (k : Fin N.length) :
    (M.familyProj N k).app X ((M.schemaPoint body).app X z) =
      (M.elemEquiv (body k)).app X z :=
  congrArg (fun (g : Z ⟶ M.power (N.get k).1 (N.get k).2) => g.app X z)
    (M.familyLift_proj N (fun k => M.elemEquiv (body k)) k)

/-- The chosen family point reads exactly the supplied generalized values. -/
theorem metaValuation_schemaPoint (A : BindingCloneAlgebra.Algebra.{u} S)
    {N : List (MetaArity S)} {Z : target A}
    (body : BindingEquationalModels.MetaValuation ((model A).stage Z) N)
    (X : Base A) (z : Z.obj X) :
    metaValuation A N X (((model A).schemaPoint body).app X z) =
      (fun k => read A (body k) X z) := by
  funext k
  exact congrArg ((powerBodiesIso A (N.get k).1 (N.get k).2).hom.app X)
    (schemaPoint_proj_app (model A) body X z k)

/-- Dependency values in a generalized stage are interpreted through their
actual selected family point. -/
theorem stage_schema_as_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {N : List (MetaArity S)} {Z : target A}
    (body : BindingEquationalModels.MetaValuation ((model A).stage Z) N)
    {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S N) Γ s) :
    BindingEquationInterpretation.interpretSchema ((model A).stage Z) body term =
      (model A).restageElem ((model A).schemaPoint body) ((model A).interp N term) := by
  let h := (model A).termPointHom ⟨N⟩ ((model A).schemaPoint body)
  let genericBody : BindingEquationalModels.MetaValuation (termAlgebra ⟨N⟩) N :=
    fun k => metaVar k
  have bodyEq : BindingEquationInterpretation.mapMetaValuation h genericBody = body := by
    funext k
    exact (model A).schemaPoint_body body k
  have mapped := BindingEquationInterpretation.interpretSchema_map h genericBody term
  rw [bodyEq, interpretSchema_liftSchema,
    IntrinsicScopedLocalActedTypeComparison.ProgramPoints.instantiate_generators] at mapped
  exact mapped.symm.trans
    ((model A).termPointHom_map ⟨N⟩ ((model A).schemaPoint body) term)

/-- The schema fold over generalized values is the full original contextual
fold at every point, with its ambient variables explicitly retained. -/
theorem stage_schema_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {N : List (MetaArity S)} {Z W : target A}
    (body : BindingEquationalModels.MetaValuation ((model A).stage Z) N)
    {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S N) Γ s)
    (m : W ⟶ Z) (ρ : (model A).Env W Γ) (X : Base A) (w : W.obj X) :
    programsAtEquiv A s X
        ((BindingEquationInterpretation.interpretSchema ((model A).stage Z)
          body term).value W m ρ |>.app X w) =
      SemanticContextualMetavariables.interpretSchema A
        (fun k => read A (body k) X (m.app X w))
        (fun _ v => A.substitution.injectVar v) (readEnv A ρ X w) term := by
  rw [stage_schema_as_point]
  have point := interp_value_point A N term (m ≫ (model A).schemaPoint body) ρ X w
  exact point.trans (congrArg
    (fun valuation => SemanticContextualMetavariables.interpretSchema A valuation
      (fun _ v => A.substitution.injectVar v) (readEnv A ρ X w) term)
    (metaValuation_schemaPoint A body X (m.app X w)))

/-- Captured generalized schemas read the original contextual fold at each
point, with arbitrary captured and ordinary environments retained. -/
theorem contextual_stage_value_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {N : List (MetaArity S)} {Z W : target A} {Θ Ξ Δ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := N) ((model A).stage Z) Θ)
    (ambient : Environment S ((model A).stage Z).substitution.Carrier Θ Δ)
    (ordinary : Environment S ((model A).stage Z).substitution.Carrier Ξ Δ)
    (m : W ⟶ Z) (ρ : (model A).Env W Δ)
    {s : S.Srt} (term : Term (withMetas S N) Ξ s)
    (X : Base A) (w : W.obj X) :
    programsAtEquiv A s X
        ((SemanticContextualMetavariables.interpretSchema ((model A).stage Z)
          body ambient ordinary term).value W m ρ |>.app X w) =
      SemanticContextualMetavariables.interpretSchema A
        (fun k => read A ((model A).captureBody (body k) m
          ((model A).envValue ambient W m ρ)) X w)
        (fun _ v => A.substitution.injectVar v)
        (readEnv A ((model A).envValue ordinary W m ρ) X w) term := by
  have contextual := (model A).contextualSchema_value body ambient ordinary m ρ term
  have point := congrArg
    (fun (f : W ⟶ programs A s) => programsAtEquiv A s X (f.app X w)) contextual
  exact point.trans
    (stage_schema_value_point A
      (fun k => (model A).captureBody (body k) m ((model A).envValue ambient W m ρ))
      term (𝟙 W) ((model A).envValue ordinary W m ρ) X w)

/-- The generalized stages satisfy every authored contextual equation whenever
the original binding clone satisfies that full contextual law. -/
theorem stage_contextualSatisfies (A : BindingCloneAlgebra.Algebra.{u} S)
    {N : List (MetaArity S)} (equations : List (EqAxiom S N))
    (sat : BindingEquationInterpretation.Satisfies A equations) (Z : target A) :
    BindingEquationInterpretation.Satisfies ((model A).stage Z) equations := by
  intro i Θ Δ body ambient ordinary
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext W m ρ
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro w
  have lhs := contextual_stage_value_point A body ambient ordinary m ρ
    (equations.get i).lhs X w
  have rhs := contextual_stage_value_point A body ambient ordinary m ρ
    (equations.get i).rhs X w
  have equation := sat i
    (fun k => read A ((model A).captureBody (body k) m
      ((model A).envValue ambient W m ρ)) X w)
    (fun _ v => A.substitution.injectVar v)
    (readEnv A ((model A).envValue ordinary W m ρ) X w)
  exact (programsAtEquiv A (equations.get i).sort X).injective
    (lhs.trans (equation.trans rhs.symm))

/-- Full contextual clone satisfaction constructs full categorical satisfaction
at every authored second-order context. -/
theorem model_satisfies (A : BindingCloneAlgebra.Algebra.{u} S)
    {N : List (MetaArity S)} (equations : List (EqAxiom S N))
    (sat : BindingEquationInterpretation.Satisfies A equations) :
    (model A).Satisfies (authoredEquationPresentation S equations) := by
  intro O j Θ Δ body ambient ordinary
  change Fin (equations.map (liftEquation O)).length at j
  let i : Fin equations.length := ⟨j.val, by
    have bound := j.isLt
    simpa only [List.length_map] using bound⟩
  have selected : (equations.map (liftEquation O)).get j = liftEquation O (equations.get i) := by
    simp only [List.get_eq_getElem, List.getElem_map]
    rfl
  revert ordinary
  change ∀ ordinary : Sub (withMetas S O.arities)
      ((equations.map (liftEquation O)).get j).ctx Δ,
    (model A).interp O.arities
      (ContextualAssignment.instantiate body ambient ordinary
        ((equations.map (liftEquation O)).get j).lhs) =
    (model A).interp O.arities
      (ContextualAssignment.instantiate body ambient ordinary
        ((equations.map (liftEquation O)).get j).rhs)
  rw [selected]
  intro ordinary
  change Sub (withMetas S O.arities) (equations.get i).ctx Δ at ordinary
  apply CategoricalBindingModel.Model.ElemOver.ext
  funext W m ρ
  let h := (model A).termPointHom O m
  have lhs := SemanticContextualMetavariables.interpretSchema_map h body ambient ordinary
    (equations.get i).lhs
  have rhs := SemanticContextualMetavariables.interpretSchema_map h body ambient ordinary
    (equations.get i).rhs
  rw [interpretContextualSchema_liftSchema O body ambient ordinary] at lhs rhs
  dsimp only [h] at lhs rhs
  rw [(model A).termPointHom_map] at lhs rhs
  have equation := stage_contextualSatisfies A equations sat W i
    (fun k => h.raw.map (body k))
    (fun s v => h.raw.map (ambient s v))
    (fun s v => h.raw.map (ordinary s v))
  have values := congrArg
    (fun (e : (model A).ElemOver W Δ (equations.get i).sort) => e.value W (𝟙 W) ρ)
    (lhs.trans (equation.trans rhs.symm))
  simpa only [liftEquation, CategoricalBindingModel.Model.restageElem,
    Category.id_comp] using values

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafEquations
