import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasBodies

/-!
# Continuation readouts on arbitrary schema inputs

The application, definition and carrier arrows are evaluated on independently
supplied complete function sections. In particular the definition body is
not required to be the compiler image of a source expression. Its reference
call and its retained value use different binding scopes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open NamePassingCategoricalCompiler NamePassingContinuationOperations
open NamePassingOpenInterpretation

attribute [local irreducible] Operations.application Operations.definition Operations.carrier

def applySection {context : Ctx sig} (function : operations.termObject.obj (stage context))
    (argument : operations.names.obj (stage context)) : operations.termObject.obj (stage context) :=
  operations.application.app (stage context) (function, argument)

def defineSection {context : Ctx sig} (value : operations.termObject.obj (stage context))
    (body : operations.boundBodyObject.obj (stage context)) : operations.termObject.obj (stage context) :=
  operations.definition.app (stage context) (value, body)

def carrySection {context : Ctx sig} (name : operations.names.obj (stage context))
    (value body : operations.termObject.obj (stage context)) : operations.termObject.obj (stage context) :=
  operations.carrier.app (stage context) (name, value, body)

/-- Application under a supplied reference binder, with the ordinary
argument kept outside that binder. -/
def applicationBody : operations.boundBodyObject ⊗ operations.names ⟶ operations.boundBodyObject :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
    (lift (call (fst (operations.boundBodyObject ⊗ operations.names) operations.names ≫
      fst operations.boundBodyObject operations.names)
      (snd (operations.boundBodyObject ⊗ operations.names) operations.names))
      (fst (operations.boundBodyObject ⊗ operations.names) operations.names ≫
        snd operations.boundBodyObject operations.names) ≫ operations.application)

theorem applicationBody_future (world future : Base) (change : world ⟶ future)
    (body : operations.boundBodyObject.obj world) (argument : operations.names.obj world)
    (reference : operations.names.obj future) :
    ((applicationBody.app world (body, argument)).app future change) reference =
      operations.application.app future
        ((body.app future change) reference, operations.names.map change argument) := by
  unfold applicationBody
  change operations.application.app future
    (((body.app future (change ≫ 𝟙 _)) reference), operations.names.map change argument) = _
  rw [Category.comp_id]

theorem applySection_substitution {context future : Ctx sig} (assigned : Sub sig context future)
    (function : operations.termObject.obj (stage context)) (argument : operations.names.obj (stage context)) :
    operations.termObject.map (rawChange assigned) (applySection function argument) =
      applySection (operations.termObject.map (rawChange assigned) function)
        (operations.names.map (rawChange assigned) argument) := by
  unfold applySection
  exact (operations.application.naturality_apply (rawChange assigned)
    (show (operations.termObject ⊗ operations.names).obj (stage context) from (function, argument))).symm

theorem defineSection_substitution {context future : Ctx sig} (assigned : Sub sig context future)
    (value : operations.termObject.obj (stage context)) (body : operations.boundBodyObject.obj (stage context)) :
    operations.termObject.map (rawChange assigned) (defineSection value body) =
      defineSection (operations.termObject.map (rawChange assigned) value)
        (operations.boundBodyObject.map (rawChange assigned) body) := by
  unfold defineSection
  exact (operations.definition.naturality_apply (rawChange assigned)
    (show (operations.termObject ⊗ operations.boundBodyObject).obj (stage context) from (value, body))).symm

theorem carrySection_substitution {context future : Ctx sig} (assigned : Sub sig context future)
    (name : operations.names.obj (stage context)) (value body : operations.termObject.obj (stage context)) :
    operations.termObject.map (rawChange assigned) (carrySection name value body) =
      carrySection (operations.names.map (rawChange assigned) name)
        (operations.termObject.map (rawChange assigned) value)
        (operations.termObject.map (rawChange assigned) body) := by
  unfold carrySection
  exact (operations.carrier.naturality_apply (rawChange assigned)
    (show (operations.names ⊗ (operations.termObject ⊗ operations.termObject)).obj (stage context) from
      (name, value, body))).symm

theorem application_readout {context : Ctx sig}
    (function : operations.termObject.obj (stage context)) (argument result : Name context) :
    programsAtEquiv algebra .pr (stage context)
      (((applySection function (rawPoint argument)).app (stage context) (𝟙 _)) (rawPoint result)) =
      algebra.operation Op.nu (.cons (algebra.operation Op.par
        (.cons (programsAtEquiv algebra .pr (stage (.nm :: context))
          ((function.app (stage (.nm :: context)) (rawChange weakening))
            (rawPoint (.var .zero : Name (.nm :: context)))))
          (.cons (Quotient.mk _ (out2 (.var .zero) (weaken argument) (weaken result))) .nil))) .nil) := by
  let outer := (operations.termObject ⊗ operations.names) ⊗ operations.names
  let privateBody : outer ⊗ operations.names ⟶ operations.processes :=
    lift (call (fst outer operations.names ≫
      fst (operations.termObject ⊗ operations.names) operations.names ≫
        fst operations.termObject operations.names) (snd outer operations.names))
      (lift (snd outer operations.names)
        (lift (fst outer operations.names ≫
          fst (operations.termObject ⊗ operations.names) operations.names ≫
            snd operations.termObject operations.names)
          (fst outer operations.names ≫ snd (operations.termObject ⊗ operations.names) operations.names)) ≫
        operations.send) ≫ operations.parallel
  unfold applySection
  unfold Operations.application
  rw [abstraction_current]
  change programsAtEquiv algebra .pr (stage context)
    ((CategoricalOperations.fresh algebra).app (stage context)
      ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction privateBody).app
        (stage context) ((function, rawPoint argument), rawPoint result))) = _
  rw [CategoricalOperations.fresh_readout, CategoricalOperations.abstraction_body]
  rw [← rawChange_scopeWeakening context [.nm]]
  erw [← freshName_point context]
  change algebra.operation Op.nu (.cons (programsAtEquiv algebra .pr (stage (.nm :: context))
    ((CategoricalOperations.parallel algebra).app (stage (.nm :: context))
      (((operations.termObject.map (rawChange weakening) function).app
        (stage (.nm :: context)) (𝟙 _)) (rawPoint (.var .zero)),
        (CategoricalOperations.send algebra).app (stage (.nm :: context))
          (rawPoint (.var .zero), operations.names.map (rawChange weakening) (rawPoint argument),
            operations.names.map (rawChange weakening) (rawPoint result))))) .nil) = _
  rw [CategoricalOperations.parallel_readout, rawPoint_weakening, rawPoint_weakening,
    CategoricalOperations.send_readout, rawPoint_readout, rawPoint_readout, rawPoint_readout]
  erw [send_classes]
  change algebra.operation Op.nu (.cons (algebra.operation Op.par
    (.cons (programsAtEquiv algebra .pr (stage (.nm :: context))
      ((function.app (stage (.nm :: context)) (rawChange weakening ≫ 𝟙 _)) (rawPoint (.var .zero))))
      (.cons _ .nil))) .nil) = _
  rw [Category.comp_id]
  rfl

theorem definition_readout {context : Ctx sig}
    (value : operations.termObject.obj (stage context)) (body : operations.boundBodyObject.obj (stage context))
    (result : Name context) :
    programsAtEquiv algebra .pr (stage context)
      (((defineSection value body).app (stage context) (𝟙 _)) (rawPoint result)) =
      algebra.operation Op.nu (.cons (algebra.operation Op.par
        (.cons (programsAtEquiv algebra .pr (stage (.nm :: context))
          (((body.app (stage (.nm :: context)) (rawChange weakening)
            (rawPoint (.var .zero : Name (.nm :: context)))).app (stage (.nm :: context)) (𝟙 _))
              (rawPoint (weaken result))))
          (.cons (algebra.operation Op.rep (.cons (algebra.operation Op.inp1
            (.cons (Quotient.mk _ (.var .zero : Name (.nm :: context)))
              (.cons (scopedBodyEquiv algebra (stage (.nm :: context)).unop [.nm] .pr
                (operations.termObject.map (rawChange weakening) value)) .nil))) .nil)) .nil))) .nil) := by
  let outer := (operations.termObject ⊗ operations.boundBodyObject) ⊗ operations.names
  let storedBody : outer ⊗ operations.names ⟶ operations.processes :=
    lift (call (call (fst outer operations.names ≫
      fst (operations.termObject ⊗ operations.boundBodyObject) operations.names ≫
        snd operations.termObject operations.boundBodyObject) (snd outer operations.names))
      (fst outer operations.names ≫ snd (operations.termObject ⊗ operations.boundBodyObject) operations.names))
      (lift (snd outer operations.names)
        (fst outer operations.names ≫
          fst (operations.termObject ⊗ operations.boundBodyObject) operations.names ≫
            fst operations.termObject operations.boundBodyObject) ≫ operations.input ≫ operations.replication) ≫
        operations.parallel
  unfold defineSection
  unfold Operations.definition
  rw [abstraction_current]
  change programsAtEquiv algebra .pr (stage context)
    ((CategoricalOperations.fresh algebra).app (stage context)
      ((Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction storedBody).app
        (stage context) ((value, body), rawPoint result))) = _
  rw [CategoricalOperations.fresh_readout, CategoricalOperations.abstraction_body]
  rw [← rawChange_scopeWeakening context [.nm]]
  erw [← freshName_point context]
  change algebra.operation Op.nu (.cons (programsAtEquiv algebra .pr (stage (.nm :: context))
    ((CategoricalOperations.parallel algebra).app (stage (.nm :: context))
      ((((body.app (stage (.nm :: context)) (rawChange weakening ≫ 𝟙 _))
        (rawPoint (.var .zero))).app (stage (.nm :: context)) (𝟙 _))
          (operations.names.map (rawChange weakening) (rawPoint result)),
        (CategoricalOperations.replication algebra).app (stage (.nm :: context))
          ((CategoricalOperations.input algebra).app (stage (.nm :: context))
            (rawPoint (.var .zero), operations.termObject.map (rawChange weakening) value))))) .nil) = _
  rw [Category.comp_id, rawPoint_weakening, CategoricalOperations.parallel_readout,
    CategoricalOperations.replication_readout, CategoricalOperations.input_readout, rawPoint_readout]
  rfl

theorem carrier_readout {context : Ctx sig} (name result : Name context)
    (value body : operations.termObject.obj (stage context)) :
    programsAtEquiv algebra .pr (stage context)
      (((carrySection (rawPoint name) value body).app (stage context) (𝟙 _)) (rawPoint result)) =
      algebra.operation Op.par (.cons
        (programsAtEquiv algebra .pr (stage context) ((body.app (stage context) (𝟙 _)) (rawPoint result)))
        (.cons (algebra.operation Op.inp1 (.cons (Quotient.mk _ name)
          (.cons (scopedBodyEquiv algebra (stage context).unop [.nm] .pr value) .nil))) .nil)) := by
  unfold carrySection
  unfold Operations.carrier
  rw [abstraction_current]
  change programsAtEquiv algebra .pr (stage context)
    ((CategoricalOperations.parallel algebra).app (stage context)
      (((body.app (stage context) (𝟙 _)) (rawPoint result)),
        (CategoricalOperations.input algebra).app (stage context) (rawPoint name, value))) = _
  rw [CategoricalOperations.parallel_readout, CategoricalOperations.input_readout, rawPoint_readout]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas
