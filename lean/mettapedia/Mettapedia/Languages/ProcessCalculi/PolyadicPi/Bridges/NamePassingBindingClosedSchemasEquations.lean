import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasPrimitives

/-!
# Scope equations for independently supplied continuation sections

The reference body can be any complete two-name function section. The scope
comparison retains its return and reference coordinates through the actual
fresh-name exchange. Stored values keep their own return binder and are
formed outside the reference binder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open NamePassingCategoricalCompiler NamePassingContinuationOperations NamePassingOpenInterpretation

attribute [local irreducible] Operations.application Operations.definition Operations.carrier

theorem rawChange_composition {context middle future : Ctx sig}
    (first : Sub sig context middle) (second : Sub sig middle future) :
    rawChange first ≫ rawChange second =
      rawChange (fun sort position => bind second (first sort position)) := by
  change Quiver.Hom.op ((rawChange second).unop ≫ (rawChange first).unop) =
    Quiver.Hom.op (rawChange (fun sort position => bind second (first sort position))).unop
  apply congrArg Quiver.Hom.op
  funext position
  change algebra.substitution.substitute
    (BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := future) middle
      (rawChange second).unop)
    (Quotient.mk _ (first _ (varOfIdx context position))) =
      (Quotient.mk _ (bind second (first _ (varOfIdx context position))) : TermQ equations future _)
  rw [rawChange_environment]
  exact (AuthoredClassified.projection.map_substitute second (first _ (varOfIdx context position))).symm

theorem rawChange_double_weakening (context : Ctx sig) :
    rawChange (weakening (Δ := context)) ≫ rawChange (weakening (Δ := .nm :: context)) =
      rawChange (scopeWeakening (context := context) [.nm, .nm]) := by
  rw [rawChange_composition]
  rfl

/-- Moving a supplied reference call under the next name binder restricts
the entire returned function. Naturality forces the older reference position
to become the second name coordinate. -/
theorem body_reference_weakening {context : Ctx sig}
    (body : operations.boundBodyObject.obj (stage context)) :
    operations.termObject.map (rawChange (weakening (Δ := .nm :: context)))
        ((body.app (stage (.nm :: context)) (rawChange weakening))
          (rawPoint (.var .zero : Name (.nm :: context)))) =
      (body.app (stage (.nm :: .nm :: context)) (rawChange (scopeWeakening [.nm, .nm])))
        (rawPoint (.var (.succ .zero) : Name (.nm :: .nm :: context))) := by
  have natural := ConcreteCategory.congr_hom
    (body.naturality (rawChange (weakening (Δ := .nm :: context))) (rawChange (weakening (Δ := context))))
    (rawPoint (.var .zero : Name (.nm :: context)))
  change (body.app (stage (.nm :: .nm :: context))
    (rawChange weakening ≫ rawChange weakening))
      (operations.names.map (rawChange weakening) (rawPoint (.var .zero))) = _ at natural
  rw [rawPoint_weakening, rawChange_double_weakening] at natural
  exact natural.symm

theorem raw_body_canonical {context : Ctx sig} (body : Proc (.nm :: .nm :: context)) :
    programsAtEquiv algebra .pr (stage (.nm :: .nm :: context))
      ((((rawSchemaBody body).app (stage (.nm :: .nm :: context))
        (rawChange (scopeWeakening [.nm, .nm])))
          (rawPoint (.var (.succ .zero) : Name (.nm :: .nm :: context)))).app
            (stage (.nm :: .nm :: context)) (𝟙 _) (rawPoint (.var .zero))) =
      (Quotient.mk _ body : TermQ equations (.nm :: .nm :: context) .pr) :=
  (bodyReadout_canonical (rawSchemaBody body)).symm.trans (rawSchemaBody_readout body)

theorem raw_body_exchanged {context : Ctx sig} (body : Proc (.nm :: .nm :: context)) :
    programsAtEquiv algebra .pr (stage (.nm :: .nm :: context))
      ((((rawSchemaBody body).app (stage (.nm :: .nm :: context))
        (rawChange (scopeWeakening [.nm, .nm])))
          (rawPoint (.var .zero : Name (.nm :: .nm :: context)))).app
            (stage (.nm :: .nm :: context)) (𝟙 _) (rawPoint (.var (.succ .zero)))) =
      (Quotient.mk _ (rename swapRen body) : TermQ equations (.nm :: .nm :: context) .pr) := by
  rw [rawSchemaBody_future]
  apply congrArg (Quotient.mk _)
  rw [bind_comp, ← bind_var_eq_rename swapRen]
  apply congrArg (fun assigned => bind assigned body)
  funext sort position
  cases position with
  | zero => rfl
  | succ position =>
    cases position with
    | zero => rfl
    | succ old => cases sort <;> rfl

def stored {context : Ctx sig} (value : Proc (.nm :: context)) (reference : Name context) : Proc context :=
  rep (inp1 reference value)

theorem stored_weakening {context : Ctx sig} (value : Proc (.nm :: context)) (reference : Name context) :
    stored (bind (liftSub (weakening (Δ := context)) [.nm]) value) (weaken reference) =
      weaken (stored value reference) := by
  unfold stored
  change _ = rename (fun _ position => Var.succ position) (rep (inp1 reference value))
  rw [← bind_var_eq_rename (fun _ position => Var.succ position) (rep (inp1 reference value))]
  rw [show weaken reference = bind (weakening (Δ := context)) reference from
    (bind_var_eq_rename (fun _ position => Var.succ position) reference).symm]
  rfl

theorem value_double_weakening {context : Ctx sig} (value : Proc (.nm :: context)) :
    bind (liftSub (weakening (Δ := .nm :: context)) [.nm])
        (bind (liftSub (weakening (Δ := context)) [.nm]) value) =
      bind (liftSub (scopeWeakening (context := context) [.nm, .nm]) [.nm]) value := by
  rw [bind_comp]
  apply congrArg (fun assigned => bind assigned value)
  funext sort position
  cases position with
  | zero => rfl
  | succ old => cases sort <;> rfl

/-- Exchange cannot capture the stored value: its return coordinate is
fixed and every old ambient coordinate remains beyond both fresh names. -/
theorem stored_exchange {context : Ctx sig} (value : Proc (.nm :: context)) :
    rename swapRen (stored
      (bind (liftSub (scopeWeakening (context := context) [.nm, .nm]) [.nm]) value)
      (.var .zero : Name (.nm :: .nm :: context))) =
      weaken (stored (bind (liftSub (weakening (Δ := context)) [.nm]) value)
        (.var .zero : Name (.nm :: context))) := by
  unfold stored
  simp only [rename_rep, rename_inp1, weaken, rename]
  apply congrArg rep
  apply congrArg (inp1 (.var (.succ .zero)))
  rw [rename_bind, rename_bind]
  apply congrArg (fun assigned => bind assigned value)
  funext sort position
  cases position with
  | zero => rfl
  | succ old => cases sort <;> rfl

private theorem frame_exchange {context : Ctx sig} (body declaration call : Proc context) :
    StructuralEq (par (par body declaration) call) (par (par body call) declaration) :=
  .trans (.parAssoc _ _ _) (.trans (.par (.refl _) (.parComm _ _)) (.symm (.parAssoc _ _ _)))

/-- The raw scope-extrusion comparison is independent of a source
expression or syntactically supplied metavariable instance. -/
theorem raw_definition_scope {context : Ctx sig} (value : Proc (.nm :: context))
    (body : Proc (.nm :: .nm :: context)) (argument result : Name context) :
    StructuralEq
      (nu (par (nu (par (rename swapRen body)
        (stored (bind (liftSub (scopeWeakening [.nm, .nm]) [.nm]) value) (.var .zero))))
        (out2 (.var .zero) (weaken argument) (weaken result))))
      (nu (par (nu (par body (out2 (.var .zero) (weaken (weaken argument)) (weaken (weaken result)))))
        (stored (bind (liftSub weakening [.nm]) value) (.var .zero)))) := by
  let inside := par (rename swapRen body)
    (stored (bind (liftSub (scopeWeakening [.nm, .nm]) [.nm]) value) (.var .zero))
  let call : Proc (.nm :: context) := out2 (.var .zero) (weaken argument) (weaken result)
  have aligned : rename swapRen (par inside (weaken call)) =
      par (par body (weaken (stored (bind (liftSub weakening [.nm]) value) (.var .zero))))
        (out2 (.var .zero) (weaken (weaken argument)) (weaken (weaken result))) := by
    dsimp only [inside, call]
    rw [rename_par, rename_par, stored_exchange]
    have swapTwice : rename swapRen (rename swapRen body) = body := by
      rw [rename_comp]
      have restored : (fun sort position => swapRen sort (swapRen sort position)) =
          (fun _ position => position : Ren sig (.nm :: .nm :: context) (.nm :: .nm :: context)) := by
        funext sort position
        cases position with
        | zero => rfl
        | succ position => cases position <;> rfl
      rw [restored, rename_id]
    rw [swapTwice]
    change par _ (out2 (.var .zero)
      (rename swapRen (weaken (weaken argument))) (rename swapRen (weaken (weaken result)))) = _
    rw [double_weakening_exchange, double_weakening_exchange]
  change StructuralEq (nu (par (nu inside) call)) _
  apply StructuralEq.trans (.nu (.nuPar inside call))
  apply StructuralEq.trans (.nuSwap (par inside (weaken call)))
  rw [aligned]
  exact .trans (.nu (.nu (frame_exchange _ _ _))) (.nu (.symm (.nuPar _ _)))

theorem function_future_current {context future : Ctx sig}
    (assigned : Sub sig context future) (function : operations.termObject.obj (stage context))
    (argument : operations.names.obj (stage future)) :
    (function.app (stage future) (rawChange assigned)) argument =
      ((operations.termObject.map (rawChange assigned) function).app (stage future) (𝟙 _)) argument := by
  change _ = (function.app (stage future) (rawChange assigned ≫ 𝟙 _)) argument
  rw [Category.comp_id]

theorem application_definition_readout {context : Ctx sig}
    (value : Proc (.nm :: context)) (body : Proc (.nm :: .nm :: context)) (argument result : Name context) :
    programsAtEquiv algebra .pr (stage context)
      (((applySection (defineSection (rawBody value) (rawSchemaBody body)) (rawPoint argument)).app
        (stage context) (𝟙 _)) (rawPoint result)) =
      (Quotient.mk _
        (nu (par (nu (par (rename swapRen body)
          (stored (bind (liftSub (scopeWeakening [.nm, .nm]) [.nm]) value) (.var .zero))))
          (out2 (.var .zero) (weaken argument) (weaken result)))) : TermQ equations context .pr) := by
  rw [application_readout, function_future_current, defineSection_substitution]
  erw [definition_readout]
  change algebra.operation Op.nu (.cons (algebra.operation Op.par
    (.cons (algebra.operation Op.nu (.cons (algebra.operation Op.par
      (.cons (programsAtEquiv algebra .pr (stage (.nm :: .nm :: context))
        ((((rawSchemaBody body).app (stage (.nm :: .nm :: context))
          (rawChange weakening ≫ rawChange weakening)) (rawPoint (.var .zero))).app
            (stage (.nm :: .nm :: context)) (𝟙 _) (rawPoint (.var (.succ .zero)))))
        (.cons (algebra.operation Op.rep (.cons (algebra.operation Op.inp1
          (.cons (Quotient.mk _ (.var .zero : Name (.nm :: .nm :: context)))
            (.cons (scopedBodyEquiv algebra (stage (.nm :: .nm :: context)).unop [.nm] .pr
              (operations.termObject.map (rawChange weakening)
                (operations.termObject.map (rawChange weakening) (rawBody value)))) .nil))) .nil)) .nil))) .nil))
      (.cons (Quotient.mk _ (out2 (.var .zero) (weaken argument) (weaken result))) .nil))) .nil) = _
  rw [rawChange_double_weakening, raw_body_exchanged, rawBody_substitution, rawBody_substitution,
    rawBody_readout, value_double_weakening]
  let retainedBody := bind (liftSub (scopeWeakening (context := context) [.nm, .nm]) [.nm]) value
  let retained : Proc (.nm :: .nm :: context) := inp1 (.var .zero) retainedBody
  let inside : Proc (.nm :: .nm :: context) := par (rename swapRen body) (rep retained)
  let continuation : Proc (.nm :: context) := out2 (.var .zero) (weaken argument) (weaken result)
  erw [input_classes (.var .zero) retainedBody, replication_classes retained,
    parallel_classes (rename swapRen body) (rep retained), fresh_classes inside,
    parallel_classes (nu inside) continuation, fresh_classes (par (nu inside) continuation)]
  rfl

theorem definition_application_readout {context : Ctx sig}
    (value : Proc (.nm :: context)) (body : Proc (.nm :: .nm :: context)) (argument result : Name context) :
    programsAtEquiv algebra .pr (stage context)
      (((defineSection (rawBody value) (applicationBody.app (stage context)
        (rawSchemaBody body, rawPoint argument))).app (stage context) (𝟙 _)) (rawPoint result)) =
      (Quotient.mk _
        (nu (par (nu (par body (out2 (.var .zero) (weaken (weaken argument)) (weaken (weaken result)))))
          (stored (bind (liftSub weakening [.nm]) value) (.var .zero)))) : TermQ equations context .pr) := by
  rw [definition_readout, applicationBody_future, rawPoint_weakening]
  change algebra.operation Op.nu (.cons (algebra.operation Op.par
    (.cons (programsAtEquiv algebra .pr (stage (.nm :: context))
      (((applySection
        (((rawSchemaBody body).app (stage (.nm :: context)) (rawChange weakening))
          (rawPoint (.var .zero : Name (.nm :: context)))) (rawPoint (weaken argument))).app
            (stage (.nm :: context)) (𝟙 _)) (rawPoint (weaken result))))
      (.cons (algebra.operation Op.rep (.cons (algebra.operation Op.inp1
        (.cons (Quotient.mk _ (.var .zero : Name (.nm :: context)))
          (.cons (scopedBodyEquiv algebra (stage (.nm :: context)).unop [.nm] .pr
            (operations.termObject.map (rawChange weakening) (rawBody value))) .nil))) .nil)) .nil))) .nil) = _
  erw [application_readout]
  rw [function_future_current, body_reference_weakening, raw_body_canonical,
    rawBody_substitution, rawBody_readout]
  let retainedBody := bind (liftSub (weakening (Δ := context)) [.nm]) value
  let retained : Proc (.nm :: context) := inp1 (.var .zero) retainedBody
  let continuation : Proc (.nm :: .nm :: context) :=
    out2 (.var .zero) (weaken (weaken argument)) (weaken (weaken result))
  let inside := par body continuation
  erw [parallel_classes body continuation, fresh_classes inside, input_classes (.var .zero) retainedBody,
    replication_classes retained, parallel_classes (nu inside) (rep retained),
    fresh_classes (par (nu inside) (rep retained))]
  rfl

theorem application_definition_current {context : Ctx sig}
    (value : operations.termObject.obj (stage context)) (body : operations.boundBodyObject.obj (stage context))
    (argument result : Name context) :
    programsAtEquiv algebra .pr (stage context)
      (((applySection (defineSection value body) (rawPoint argument)).app
        (stage context) (𝟙 _)) (rawPoint result)) =
      programsAtEquiv algebra .pr (stage context)
        (((defineSection value (applicationBody.app (stage context) (body, rawPoint argument))).app
          (stage context) (𝟙 _)) (rawPoint result)) := by
  obtain ⟨rawValue, representedValue⟩ := rawBody_surjective value
  obtain ⟨rawBody, representedBody⟩ := rawSchemaBody_surjective body
  rw [← representedValue, ← representedBody, application_definition_readout, definition_application_readout]
  exact Quotient.sound ((AuthoredEquations.eqClosure_iff_structuralEq _ _).mpr
    (raw_definition_scope rawValue rawBody argument result))

theorem function_body_current {context : Ctx sig} (function : operations.termObject.obj (stage context)) :
    scopedBodyEquiv algebra (stage context).unop [.nm] .pr function =
      programsAtEquiv algebra .pr (stage (.nm :: context))
        (((operations.termObject.map (rawChange weakening) function).app (stage (.nm :: context)) (𝟙 _))
          (rawPoint (.var .zero : Name (.nm :: context)))) := by
  rw [scopedBodyEquiv_apply, ← rawChange_scopeWeakening context [.nm], ← freshName_point context]
  change _ = programsAtEquiv algebra .pr (stage (.nm :: context))
    ((function.app (stage (.nm :: context)) (rawChange weakening ≫ 𝟙 _)) (rawPoint (.var .zero)))
  rw [Category.comp_id]
  rfl

attribute [local irreducible] applicationBody

theorem applicationBody_substitution {context future : Ctx sig} (assigned : Sub sig context future)
    (body : operations.boundBodyObject.obj (stage context)) (argument : operations.names.obj (stage context)) :
    operations.boundBodyObject.map (rawChange assigned) (applicationBody.app (stage context) (body, argument)) =
      applicationBody.app (stage future)
        (operations.boundBodyObject.map (rawChange assigned) body, operations.names.map (rawChange assigned) argument) :=
  (applicationBody.naturality_apply (rawChange assigned)
    (show (operations.boundBodyObject ⊗ operations.names).obj (stage context) from (body, argument))).symm

/-- The scope equation identifies complete return functions for every
supplied function-valued body and argument, before a call is selected. -/
theorem application_definition_section {context : Ctx sig}
    (value : operations.termObject.obj (stage context)) (body : operations.boundBodyObject.obj (stage context))
    (argument : operations.names.obj (stage context)) :
    applySection (defineSection value body) argument =
      defineSection value (applicationBody.app (stage context) (body, argument)) := by
  obtain ⟨rawArgument, represented⟩ := rawPoint_surjective argument
  rw [← represented]
  apply (scopedBodyEquiv algebra (stage context).unop [.nm] .pr).injective
  rw [function_body_current, function_body_current, applySection_substitution,
    defineSection_substitution, defineSection_substitution, applicationBody_substitution, rawPoint_weakening]
  exact application_definition_current (operations.termObject.map (rawChange weakening) value)
    (operations.boundBodyObject.map (rawChange weakening) body) (weaken rawArgument) (.var .zero)

/-- All carrier inputs are ordinary whole context sections; the existing
checked intrinsic equation therefore supplies this complete input law. -/
theorem application_carrier_section {context : Ctx sig}
    (name argument : operations.names.obj (stage context))
    (value body : operations.termObject.obj (stage context)) :
    applySection (carrySection name value body) argument = carrySection name value (applySection body argument) := by
  have same := NamePassingCategoricalCompiler.static_arrow
    (Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.StaticEq.appCarrier
      (.var .zero)
      (.var (.succ .zero))
      (.var (.succ (.succ .zero)))
      (.var (.succ (.succ (.succ .zero)))) :
        Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.StaticEq
          (Γ := [.nm, .tm, .tm, .nm]) _ _)
  simp only [Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.application,
    Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.carrier,
    NamePassingConstructorInterpretation.meaning,
    NamePassingConstructorInterpretation.nameMeaning,
    Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation.nameVariable] at same
  have values := ConcreteCategory.congr_hom (NatTrans.congr_app same (stage context))
    (show (NamePassingConstructorInterpretation.contextValue operations
      [.nm, .tm, .tm, .nm]).obj (stage context) from (name, value, body, argument, PUnit.unit))
  exact values

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas
