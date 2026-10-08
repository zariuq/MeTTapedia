import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalReadout

/-!
# Complete received-binder and fresh-name constructor readouts

The independently formed continuation arrows are evaluated through the
actual pi product and exponential objects. Received argument and return
positions, private allocation and the stored definition value are read
through their whole contextual bodies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.Languages.LambdaCalculus
open NamePassingOpenInterpretation NamePassingConstructorInterpretation
open NamePassingContinuationOperations

theorem abstraction_current {Z X Y : Ambient} (body : Z ⊗ X ⟶ Y)
    (world : Base) (parameter : Z.obj world) (argument : X.obj world) :
    (((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction body).app
      world parameter).app world (𝟙 world)) argument = body.app world (parameter, argument) := by
  change body.app world (Z.map (𝟙 world) parameter, argument) = _
  rw [Functor.map_id_apply]

theorem call_current {Z X Y : Ambient} (function : Z ⟶ (X.functorHom Y))
    (argument : Z ⟶ X) (world : Base) (parameter : Z.obj world) :
    (call function argument).app world parameter =
      (function.app world parameter).app world (𝟙 world) (argument.app world parameter) := rfl

theorem binaryNames_points (target : Ctx sig) :
    (CategoricalOperations.binaryContextIso algebra).inv.app (stage (.nm :: .nm :: target))
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection algebra.substitution.toClone
        (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
          algebra.substitution.toClone [.nm, .nm]) (stage target).unop) =
      (rawPoint (.var .zero : Name (.nm :: .nm :: target)),
        rawPoint (.var (.succ .zero) : Name (.nm :: .nm :: target))) := by
  apply Prod.ext
  · apply (programsAtEquiv algebra .nm (stage (.nm :: .nm :: target))).injective
    rfl
  · apply (programsAtEquiv algebra .nm (stage (.nm :: .nm :: target))).injective
    exact MultiBinderPresheaf.leftProjection_as_var algebra [.nm, .nm] target (1 : Fin 2)

theorem rawPoint_weakening {target : Ctx sig} (name : Name target) :
    operations.names.map (rawChange weakening) (rawPoint name) = rawPoint (weaken name) := by
  rw [rawPoint_substitution]
  exact congrArg rawPoint (bind_var_eq_rename (fun _ position => Var.succ position) name)

theorem abstraction_shape {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (body : NamePassing.Presentation.Program (.nm :: context)) (environment : Environment context target)
    (result : Name target) :
    programsAtEquiv algebra .pr (stage target)
        ((((meaning operations (NamePassing.Presentation.abstraction body)).app
          (stage target) (contextPoint environment)).app (stage target) (𝟙 _)) (rawPoint result)) =
      algebra.operation Op.inp2
        (.cons (Quotient.mk _ result)
          (.cons (programsAtEquiv algebra .pr (stage (.nm :: .nm :: target))
            ((((meaning operations body).app (stage (.nm :: .nm :: target))
              (contextPoint ((environment.substitute weakening).lift))).app
                (stage (.nm :: .nm :: target)) (𝟙 _)) (rawPoint (.var (.succ .zero))))) .nil)) := by
  simp only [NamePassing.Presentation.abstraction, meaning]
  dsimp only [Operations.abstraction]
  simp only [NatTrans.comp_app_apply]
  rw [abstraction_current]
  let received : (operations.boundBodyObject ⊗ operations.names) ⊗
      (operations.names ⊗ operations.names) ⟶ operations.processes :=
    call (call
      (fst (operations.boundBodyObject ⊗ operations.names) (operations.names ⊗ operations.names) ≫
        fst operations.boundBodyObject operations.names)
      (snd (operations.boundBodyObject ⊗ operations.names) (operations.names ⊗ operations.names) ≫
        fst operations.names operations.names))
      (snd (operations.boundBodyObject ⊗ operations.names) (operations.names ⊗ operations.names) ≫
        snd operations.names operations.names)
  change programsAtEquiv algebra .pr (stage target)
    ((CategoricalOperations.receive algebra).app (stage target)
      (rawPoint result,
        (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction received).app
          (stage target) ((boundMeaning operations (meaning operations body)).app
            (stage target) (contextPoint environment), rawPoint result))) = _
  rw [CategoricalOperations.receive_readout, rawPoint_readout]
  rw [CategoricalOperations.binary_abstraction_body]
  rw [← rawChange_scopeWeakening target [.nm, .nm]]
  erw [binaryNames_points target]
  change algebra.operation Op.inp2 (.cons (Quotient.mk _ result)
    (.cons (programsAtEquiv algebra .pr (stage (.nm :: .nm :: target))
      (((((boundMeaning operations (meaning operations body)).app (stage target)
        (contextPoint environment)).app (stage (.nm :: .nm :: target))
          (rawChange (scopeWeakening [.nm, .nm]) ≫ 𝟙 _)) (rawPoint (.var .zero))).app
            (stage (.nm :: .nm :: target)) (𝟙 _)
              (rawPoint (.var (.succ .zero))))) .nil)) = _
  rw [Category.comp_id, boundMeaning_future]
  rw [← abstraction_environment]

theorem application_shape {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (function : NamePassing.Presentation.Program context) (argument : NamePassing.Presentation.Name context)
    (environment : Environment context target) (result : Name target) :
    programsAtEquiv algebra .pr (stage target)
        ((((meaning operations (NamePassing.Presentation.application function argument)).app
          (stage target) (contextPoint environment)).app (stage target) (𝟙 _)) (rawPoint result)) =
      algebra.operation Op.nu
        (.cons (algebra.operation Op.par
          (.cons (programsAtEquiv algebra .pr (stage (.nm :: target))
            ((((meaning operations function).app (stage (.nm :: target))
              (contextPoint (environment.substitute weakening))).app
                (stage (.nm :: target)) (𝟙 _)) (rawPoint (.var .zero))))
            (.cons (algebra.operation Op.out2
              (.cons (Quotient.mk _ (.var .zero : Name (.nm :: target)))
                (.cons (Quotient.mk _ (weaken (interpretName argument environment)))
                  (.cons (Quotient.mk _ (weaken result)) .nil)))) .nil))) .nil) := by
  let outer := (operations.termObject ⊗ operations.names) ⊗ operations.names
  let privateBody : outer ⊗ operations.names ⟶ operations.processes :=
    lift
      (call (fst outer operations.names ≫
        fst (operations.termObject ⊗ operations.names) operations.names ≫
          fst operations.termObject operations.names) (snd outer operations.names))
      (lift (snd outer operations.names)
        (lift (fst outer operations.names ≫
          fst (operations.termObject ⊗ operations.names) operations.names ≫
            snd operations.termObject operations.names)
          (fst outer operations.names ≫ snd (operations.termObject ⊗ operations.names) operations.names)) ≫
        operations.send) ≫ operations.parallel
  simp only [NamePassing.Presentation.application, meaning]
  dsimp only [Operations.application]
  simp only [NatTrans.comp_app_apply]
  rw [abstraction_current]
  change programsAtEquiv algebra .pr (stage target)
    ((CategoricalOperations.fresh algebra).app (stage target)
      ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction privateBody).app
        (stage target) (((meaning operations function).app (stage target) (contextPoint environment),
          (nameMeaning operations argument).app (stage target) (contextPoint environment)), rawPoint result))) = _
  rw [CategoricalOperations.fresh_readout, CategoricalOperations.abstraction_body]
  rw [← rawChange_scopeWeakening target [.nm]]
  erw [← freshName_point target]
  change algebra.operation Op.nu (.cons (programsAtEquiv algebra .pr (stage (.nm :: target))
    ((CategoricalOperations.parallel algebra).app (stage (.nm :: target))
      ((operations.termObject.map (rawChange weakening)
        ((meaning operations function).app (stage target) (contextPoint environment))).app
          (stage (.nm :: target)) (𝟙 _) (rawPoint (.var .zero)),
        (CategoricalOperations.send algebra).app (stage (.nm :: target))
          (rawPoint (.var .zero),
            operations.names.map (rawChange weakening)
              ((nameMeaning operations argument).app (stage target) (contextPoint environment)),
            operations.names.map (rawChange weakening) (rawPoint result))))) .nil) = _
  rw [CategoricalOperations.parallel_readout, CategoricalOperations.send_readout,
    meaning_substitution, nameMeaning_readout, rawPoint_weakening, rawPoint_weakening,
    rawPoint_readout, rawPoint_readout, rawPoint_readout]
  rfl

theorem definition_shape {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (value : NamePassing.Presentation.Program context)
    (body : NamePassing.Presentation.Program (.nm :: context)) (environment : Environment context target)
    (result : Name target) :
    programsAtEquiv algebra .pr (stage target)
        ((((meaning operations (NamePassing.Presentation.definition value body)).app
          (stage target) (contextPoint environment)).app (stage target) (𝟙 _)) (rawPoint result)) =
      algebra.operation Op.nu
        (.cons (algebra.operation Op.par
          (.cons
            (programsAtEquiv algebra .pr (stage (.nm :: target))
              ((((meaning operations body).app (stage (.nm :: target))
                (contextPoint environment.lift)).app (stage (.nm :: target)) (𝟙 _))
                  (rawPoint (weaken result))))
            (.cons
              (algebra.operation Op.rep
                (.cons
                  (algebra.operation Op.inp1
                    (.cons (Quotient.mk _ (.var .zero : Name (.nm :: target)))
                      (.cons
                        (scopedBodyEquiv algebra (stage (.nm :: target)).unop [.nm] .pr
                          ((meaning operations value).app (stage (.nm :: target))
                            (contextPoint (environment.substitute weakening))))
                        .nil)))
                  .nil))
              .nil)))
          .nil) := by
  let outer := (operations.termObject ⊗ operations.boundBodyObject) ⊗ operations.names
  let storedBody : outer ⊗ operations.names ⟶ operations.processes :=
    lift
      (call (call (fst outer operations.names ≫
        fst (operations.termObject ⊗ operations.boundBodyObject) operations.names ≫
          snd operations.termObject operations.boundBodyObject) (snd outer operations.names))
        (fst outer operations.names ≫ snd (operations.termObject ⊗ operations.boundBodyObject) operations.names))
      (lift (snd outer operations.names)
        (fst outer operations.names ≫
          fst (operations.termObject ⊗ operations.boundBodyObject) operations.names ≫
            fst operations.termObject operations.boundBodyObject) ≫
          operations.input ≫ operations.replication) ≫ operations.parallel
  simp only [NamePassing.Presentation.definition, meaning]
  dsimp only [Operations.definition]
  simp only [NatTrans.comp_app_apply]
  rw [abstraction_current]
  change programsAtEquiv algebra .pr (stage target)
    ((CategoricalOperations.fresh algebra).app (stage target)
      ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction storedBody).app
        (stage target) (((meaning operations value).app (stage target) (contextPoint environment),
          (boundMeaning operations (meaning operations body)).app (stage target) (contextPoint environment)),
            rawPoint result))) = _
  rw [CategoricalOperations.fresh_readout, CategoricalOperations.abstraction_body]
  rw [← rawChange_scopeWeakening target [.nm]]
  erw [← freshName_point target]
  let boundFunction : operations.boundBodyObject.obj (stage target) :=
    (boundMeaning operations (meaning operations body)).app (stage target) (contextPoint environment)
  let received : operations.termObject.obj (stage (.nm :: target)) :=
    boundFunction.app (stage (.nm :: target)) (rawChange weakening ≫ 𝟙 _) (rawPoint (.var .zero))
  let active : operations.processes.obj (stage (.nm :: target)) :=
    received.app (stage (.nm :: target)) (𝟙 _)
      (operations.names.map (rawChange weakening) (rawPoint result))
  let retained : operations.processes.obj (stage (.nm :: target)) :=
    (CategoricalOperations.replication algebra).app (stage (.nm :: target))
      ((CategoricalOperations.input algebra).app (stage (.nm :: target))
        (rawPoint (.var .zero), operations.termObject.map (rawChange weakening)
          ((meaning operations value).app (stage target) (contextPoint environment))))
  change algebra.operation Op.nu
    (.cons (programsAtEquiv algebra .pr (stage (.nm :: target))
      ((CategoricalOperations.parallel algebra).app (stage (.nm :: target)) (active, retained))) .nil) = _
  dsimp only [active, received, boundFunction, retained]
  rw [Category.comp_id, boundMeaning_future, ← lift_as_extendName, rawPoint_weakening,
    CategoricalOperations.parallel_readout, CategoricalOperations.replication_readout,
    CategoricalOperations.input_readout, meaning_substitution, rawPoint_readout]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler
