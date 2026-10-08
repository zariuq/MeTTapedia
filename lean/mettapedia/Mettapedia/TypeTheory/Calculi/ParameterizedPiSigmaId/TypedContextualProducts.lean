import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualDependentTypes

/-!
# Dependent products on the typed contextual quotient

Formation uses actual typed domain and codomain representatives. Lambda and
application are constructed in the typed calculus, after retyping the supplied
classes at those representatives. Beta is an equation of the complete term
classes, including the instantiated dependent annotation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual.Products

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization
open TypedContextual.DependentTypes TypedContextual.QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

noncomputable def rawLam {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (body : Term (extend context domain) codomain) : Term context (rawPi levels domain codomain) :=
  ⟨.lam body.code, .lamIntro (rawPi levels domain codomain).formed
    (rawPi levels domain codomain).universeWitness body.typed⟩

noncomputable def rawApp {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (function : Term context (rawPi levels domain codomain)) (argument : Term context domain) :
    Term context (codomain.reindex (nativeSection argument)) where
  code := .app function.code argument.code
  typed := by
    change Typed rules context.raw (.app function.code argument.code)
      (subst (nativeSection argument).substitution codomain.code)
    rw [nativeSection_substitution]
    exact .appElim function.typed argument.typed

theorem rawLam_congruent {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (first second : Term (extend context domain) codomain)
    (same : Equal rules (extend context domain).raw first.code second.code codomain.code) :
    QTerm.mk levels (rawLam levels first) = QTerm.mk levels (rawLam levels second) :=
  (QTerm.mk_eq_iff levels _ _).mpr ⟨(rawPi levels domain codomain).isType.refl,
    .lamCong (rawPi levels domain codomain).formed (rawPi levels domain codomain).universeWitness same⟩

theorem rawApp_function_congruent {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (first second : Term context (rawPi levels domain codomain)) (argument : Term context domain)
    (same : Equal rules context.raw first.code second.code (rawPi levels domain codomain).code) :
    QTerm.mk levels (rawApp levels first argument) = QTerm.mk levels (rawApp levels second argument) := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  constructor
  · exact (codomain.reindex (nativeSection argument)).isType.refl
  · change Equal rules context.raw (.app first.code argument.code) (.app second.code argument.code)
      (subst (nativeSection argument).substitution codomain.code)
    rw [nativeSection_substitution]
    exact .appCong same (.refl argument.typed)

theorem rawBeta {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (body : Term (extend context domain) codomain) (argument : Term context domain) :
    QTerm.mk levels (rawApp levels (rawLam levels body) argument) =
      QTerm.mk levels (body.reindex (nativeSection argument)) := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  constructor
  · exact (codomain.reindex (nativeSection argument)).isType.refl
  · change Equal rules context.raw (.app (.lam body.code) argument.code)
      (subst (nativeSection argument).substitution body.code)
      (subst (nativeSection argument).substitution codomain.code)
    rw [nativeSection_substitution]
    exact .betaPi (rawPi levels domain codomain).formed
      (rawPi levels domain codomain).universeWitness body.typed argument.typed

theorem rawInstantiation_reindex {source target : Context rules} (morphism : source ⟶ target)
    {domain : TypeOver target} (codomain : TypeOver (extend target domain)) (argument : Term target domain) :
    (codomain.reindex (nativeSection argument)).reindex morphism =
      (codomain.reindex (rawLift morphism domain)).reindex (nativeSection (argument.reindex morphism)) := by
  apply TypeOver.ext
  · change subst morphism.substitution (subst (nativeSection argument).substitution codomain.code) =
      subst (nativeSection (argument.reindex morphism)).substitution (subst (liftSub morphism.substitution) codomain.code)
    rw [nativeSection_substitution, nativeSection_substitution]
    exact subst_inst0 morphism.substitution argument.code codomain.code
  · rfl

theorem rawApp_reindex {source target : Context rules} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (function : Term target (rawPi levels domain codomain)) (argument : Term target domain) :
    ((rawApp levels function argument).reindex morphism).cast
      (rawInstantiation_reindex morphism codomain argument) =
      rawApp levels ((function.reindex morphism).cast (rawPi_reindex levels morphism domain codomain))
        (argument.reindex morphism) := by
  apply Term.ext
  rw [Term.cast_code]
  change Tm.app (subst morphism.substitution function.code) (subst morphism.substitution argument.code) =
    Tm.app ((function.reindex morphism).cast (rawPi_reindex levels morphism domain codomain)).code
      (argument.reindex morphism).code
  rw [Term.cast_code]
  rfl

theorem rawApp_compared {context : Context rules}
    (first second : TypeOver context) (sameDomain : TypeEq rules context.raw first.code second.code)
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : TypeEq rules (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)
    (leftFunction : Term context (rawPi levels first firstBody))
    (rightFunction : Term context (rawPi levels second secondBody))
    (left : Term context first) (right : Term context second)
    (sameFunction : Equal rules context.raw leftFunction.code rightFunction.code (rawPi levels first firstBody).code)
    (sameArgument : Equal rules context.raw left.code right.code first.code) :
    QTerm.mk levels (rawApp levels leftFunction left) = QTerm.mk levels (rawApp levels rightFunction right) := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  constructor
  · exact rawInstantiation_typeEquality levels first second sameDomain firstBody secondBody sameBody left right sameArgument
  · change Equal rules context.raw (.app leftFunction.code left.code) (.app rightFunction.code right.code)
      (subst (nativeSection left).substitution firstBody.code)
    rw [nativeSection_substitution]
    exact .appCong sameFunction sameArgument

noncomputable def pi {context : QuotientCwf.QContext rules}
    (domain : QuotientCwf.Ty levels context)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)) : QuotientCwf.Ty levels context :=
  QType.mk levels (rawPi levels (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative codomain))

noncomputable def lam {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm levels (QuotientCwf.ext context domain) codomain) :
    QuotientCwf.Tm levels context (pi levels domain codomain) :=
  ⟨QTerm.mk levels (rawLam levels (chosenTerm body)), rfl⟩

noncomputable def functionRepresentative {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm levels context (pi levels domain codomain)) :
    Term context.as (rawPi levels (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain)) :=
  QuotientCwf.termRepresentative _ function.val function.property

theorem functionRepresentative_class {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm levels context (pi levels domain codomain)) :
    QTerm.mk levels (functionRepresentative levels function) = function.val :=
  QuotientCwf.termRepresentative_class _ _ _

noncomputable def app {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm levels context (pi levels domain codomain))
    (argument : QuotientCwf.Tm levels context domain) :
    QuotientCwf.Tm levels context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) argument)) :=
  ⟨QTerm.mk levels (rawApp levels (functionRepresentative levels function) (chosenTerm argument)),
    type_at_argument codomain argument⟩

noncomputable def operations : PiOperations (QuotientCwf.cwf levels) where
  pi := pi levels
  lam := lam levels
  app := app levels

theorem beta : PiBeta (operations levels) := by
  intro context domain codomain body argument
  apply Subtype.ext
  have functionEquality := (QTerm.mk_eq_iff levels _ _).mp
    (functionRepresentative_class levels (lam levels body))
  exact (rawApp_function_congruent levels _ _ (chosenTerm argument) functionEquality.2).trans
    ((rawBeta levels (chosenTerm body) (chosenTerm argument)).trans (term_at_argument body argument))

theorem formation_substitution : StrictPiFormationSubstitution (operations levels) := by
  intro source target morphism domain codomain
  change QuotientCwf.tySub (pi levels domain codomain) morphism = _
  rw [← QuotientCwf.represented_type_reindex (pi levels domain codomain) morphism]
  have annotation : QType.mk levels (QuotientCwf.typeRepresentative (pi levels domain codomain)) =
      QType.mk levels (rawPi levels (QuotientCwf.typeRepresentative domain)
        (QuotientCwf.typeRepresentative codomain)) := QuotientCwf.typeRepresentative_class _
  have reindexed := congrArg (fun type => QType.reindex type (QuotientCwf.representative morphism)) annotation
  rw [QType.reindex_mk, QType.reindex_mk, rawPi_reindex] at reindexed
  apply reindexed.trans
  apply (QType.mk_eq_iff levels _ _).mpr
  exact rawPi_typeEquality levels _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison levels morphism domain codomain)

set_option backward.isDefEq.respectTransparency false in
theorem body_reindex_class {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)}
    (body : QuotientCwf.Tm levels (QuotientCwf.ext target domain) codomain) :
    QTerm.mk levels ((chosenTerm body).reindex (nativeLift morphism domain)) =
      (QuotientCwf.tmSub body (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism domain)).val := by
  calc
    _ = QuotientCwf.totalSub (QTerm.mk levels (chosenTerm body))
        (QuotientCwf.project (nativeLift morphism domain)) := rfl
    _ = _ := by rw [chosenTerm_class, nativeLift_projects]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem lambda_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)}
    (body : QuotientCwf.Tm levels (QuotientCwf.ext target domain) codomain) :
    HEq (QuotientCwf.tmSub (lam levels body) morphism)
      (lam levels (QuotientCwf.tmSub body
        (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))) := by
  apply heq_of_value
  change QuotientCwf.totalSub (QTerm.mk levels (rawLam levels (chosenTerm body))) morphism = _
  have actual : QuotientCwf.totalSub (QTerm.mk levels (rawLam levels (chosenTerm body))) morphism =
      QTerm.mk levels ((rawLam levels (chosenTerm body)).reindex (QuotientCwf.representative morphism)) := by
    calc
      _ = QuotientCwf.totalSub (QTerm.mk levels (rawLam levels (chosenTerm body)))
          (QuotientCwf.project (QuotientCwf.representative morphism)) := by
            rw [QuotientCwf.project_representative]
      _ = _ := rfl
  apply actual.trans
  apply (QTerm.mk_eq_iff levels _ _).mpr
  have domains := reindexed_domain_equality morphism domain
  let extended := (extensionComparison
    ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism)) domains).hom
  have bodies := (QTerm.mk_eq_iff levels _ _).mp ((body_reindex_class levels morphism body).trans
    (chosenTerm_class (QuotientCwf.tmSub body
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism domain))).symm)
  have moved := bodies.2.substitute extended.typed
  change Equal rules _
    (subst extended.substitution (subst (nativeLift morphism domain).substitution (chosenTerm body).code))
    (subst extended.substitution (chosenTerm (QuotientCwf.tmSub body
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism domain))).code)
    (subst extended.substitution (subst (nativeLift morphism domain).substitution
      (QuotientCwf.typeRepresentative codomain).code)) at moved
  rw [nativeLift_substitution, show extended.substitution = ids from extensionComparison_hom_substitution _ _ _,
    subst_ids, subst_ids, subst_ids] at moved
  constructor
  · have final := (QType.mk_eq_iff levels _ _).mp
      ((show QType.mk levels ((rawPi levels (QuotientCwf.typeRepresentative domain)
        (QuotientCwf.typeRepresentative codomain)).reindex (QuotientCwf.representative morphism)) =
        QuotientCwf.tySub (pi levels domain codomain) morphism from by
        exact (congrArg (QuotientCwf.tySub (pi levels domain codomain))
          (QuotientCwf.project_representative morphism))).trans
          (formation_substitution levels morphism domain codomain))
    exact final
  · change Equal rules source.as.raw
      (.lam (subst (liftSub (QuotientCwf.representative morphism).substitution) (chosenTerm body).code))
      (.lam (chosenTerm (QuotientCwf.tmSub body
        (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))).code)
      (subst (QuotientCwf.representative morphism).substitution
        (rawPi levels (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)).code)
    exact .lamCong ((rawPi levels (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain)).reindex (QuotientCwf.representative morphism)).formed
      (rawPi levels (QuotientCwf.typeRepresentative domain)
        (QuotientCwf.typeRepresentative codomain)).universeWitness moved

theorem supplied_reindex_class {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {type : QuotientCwf.Ty levels target}
    (term : QuotientCwf.Tm levels target type) {annotation : TypeOver target.as}
    (actual : Term target.as annotation) (same : QTerm.mk levels actual = term.val) :
    QTerm.mk levels (actual.reindex (QuotientCwf.representative morphism)) =
      (QuotientCwf.tmSub term morphism).val := by
  calc
    _ = QuotientCwf.totalSub (QTerm.mk levels actual)
        (QuotientCwf.project (QuotientCwf.representative morphism)) := rfl
    _ = _ := by rw [same, QuotientCwf.project_representative]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem application_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)}
    (function : QuotientCwf.Tm levels target (pi levels domain codomain))
    (argument : QuotientCwf.Tm levels target domain)
    (reindexedFunction : QuotientCwf.Tm levels source
      (pi levels (QuotientCwf.tySub domain morphism)
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))))
    (sameFunction : HEq (QuotientCwf.tmSub function morphism) reindexedFunction) :
    HEq (QuotientCwf.tmSub (app levels function argument) morphism)
      (app levels reindexedFunction (QuotientCwf.tmSub argument morphism)) := by
  apply heq_of_value
  let oldFunction := functionRepresentative levels function
  let oldArgument := chosenTerm argument
  let newFunction := (oldFunction.reindex (QuotientCwf.representative morphism)).cast
    (rawPi_reindex levels (QuotientCwf.representative morphism) _ _)
  let newArgument := oldArgument.reindex (QuotientCwf.representative morphism)
  have functions : QTerm.mk levels newFunction = QTerm.mk levels (functionRepresentative levels reindexedFunction) :=
    (QTerm.mk_cast _ _).trans ((supplied_reindex_class levels morphism function oldFunction
      (functionRepresentative_class levels function)).trans
        ((heq_value (formation_substitution levels morphism domain codomain) sameFunction).trans
          (functionRepresentative_class levels reindexedFunction).symm))
  have arguments : QTerm.mk levels newArgument = QTerm.mk levels (chosenTerm (QuotientCwf.tmSub argument morphism)) :=
    (supplied_reindex_class levels morphism argument oldArgument (chosenTerm_class argument)).trans
      (chosenTerm_class (QuotientCwf.tmSub argument morphism)).symm
  have compared := rawApp_compared levels _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison levels morphism domain codomain) newFunction
    (functionRepresentative levels reindexedFunction) newArgument
    (chosenTerm (QuotientCwf.tmSub argument morphism))
    ((QTerm.mk_eq_iff levels _ _).mp functions).2 ((QTerm.mk_eq_iff levels _ _).mp arguments).2
  have actual := supplied_reindex_class levels morphism (app levels function argument)
    (rawApp levels oldFunction oldArgument) rfl
  exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
    ((congrArg (QTerm.mk levels) (rawApp_reindex levels (QuotientCwf.representative morphism)
      oldFunction oldArgument)).trans compared))

theorem substitution : StrictPiSubstitution (operations levels) :=
  ⟨formation_substitution levels, lambda_substitution levels, application_substitution levels⟩

theorem fresh_instantiation {n : Nat} (body : Tm Head (n + 1)) :
    inst0 (.var 0) (Presentation.rename (liftRen wk) body) = body := by
  unfold inst0
  rw [subst_rename]
  conv => rhs; rw [← subst_ids body]
  apply subst_ext
  intro index
  exact Fin.cases rfl (fun _ => rfl) index

noncomputable def rawFreshApp {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (function : Term context (rawPi levels domain codomain)) : Term (extend context domain) codomain where
  code := .app (Presentation.rename wk function.code) (.var 0)
  typed := by
    have typed := Derivable.appElim (function.typed.rename (CtxRen.wk context.raw domain.code))
      (Derivable.var (R := rules) (Γ := (extend context domain).raw) 0)
    simpa only [Presentation.rename, Ctx.lookup, fresh_instantiation] using typed

theorem rawFreshApp_congruent {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (first second : Term context (rawPi levels domain codomain))
    (same : Equal rules context.raw first.code second.code (rawPi levels domain codomain).code) :
    QTerm.mk levels (rawFreshApp levels first) = QTerm.mk levels (rawFreshApp levels second) := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  refine ⟨codomain.isType.refl, ?_⟩
  have compared := Derivable.appCong (same.rename (CtxRen.wk context.raw domain.code))
    (Derivable.refl (Derivable.var (R := rules) (Γ := (extend context domain).raw) 0))
  simpa only [rawFreshApp, Presentation.rename, Ctx.lookup, fresh_instantiation] using compared

theorem rawFreshBeta {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (body : Term (extend context domain) codomain) :
    QTerm.mk levels (rawFreshApp levels (rawLam levels body)) = QTerm.mk levels body := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  refine ⟨codomain.isType.refl, ?_⟩
  have compared := Derivable.betaPi ((rawPi levels domain codomain).formed.rename
      (CtxRen.wk context.raw domain.code)) (rawPi levels domain codomain).universeWitness
    (body.typed.rename ((CtxRen.wk context.raw domain.code).snoc domain.code))
    (Derivable.var (R := rules) (Γ := (extend context domain).raw) 0)
  simpa only [rawFreshApp, rawLam, Presentation.rename, Ctx.lookup, fresh_instantiation] using compared

theorem rawEta {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (function : Term context (rawPi levels domain codomain)) :
    QTerm.mk levels (rawLam levels (rawFreshApp levels function)) = QTerm.mk levels function := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  refine ⟨(rawPi levels domain codomain).isType.refl, ?_⟩
  exact .etaPi (rawLam levels (rawFreshApp levels function)).typed function.typed
    ((QTerm.mk_eq_iff levels _ _).mp (rawFreshBeta levels (rawFreshApp levels function))).2

noncomputable def uncurry {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm levels context (pi levels domain codomain)) :
    QuotientCwf.Tm levels (QuotientCwf.ext context domain) codomain :=
  ⟨QTerm.mk levels (rawFreshApp levels (functionRepresentative levels function)),
    QuotientCwf.typeRepresentative_class codomain⟩

theorem uncurry_lam {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm levels (QuotientCwf.ext context domain) codomain) :
    uncurry levels (lam levels body) = body := by
  apply Subtype.ext
  have functions := (QTerm.mk_eq_iff levels _ _).mp (functionRepresentative_class levels (lam levels body))
  exact (rawFreshApp_congruent levels _ _ functions.2).trans
    ((rawFreshBeta levels (chosenTerm body)).trans (chosenTerm_class body))

theorem lam_uncurry {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm levels context (pi levels domain codomain)) :
    lam levels (uncurry levels function) = function := by
  apply Subtype.ext
  have bodies := chosenTerm_represents (uncurry levels function)
    (rawFreshApp levels (functionRepresentative levels function)) rfl
  exact (rawLam_congruent levels _ _ bodies).trans
    ((rawEta levels (functionRepresentative levels function)).trans (functionRepresentative_class levels function))

/-- The complete dependent function fibre is represented by body sections.
The inverse equations are earned by beta and typed function eta. -/
noncomputable def sectionEquiv {context : QuotientCwf.QContext rules}
    (domain : QuotientCwf.Ty levels context)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)) :
    QuotientCwf.Tm levels context (pi levels domain codomain) ≃
      QuotientCwf.Tm levels (QuotientCwf.ext context domain) codomain where
  toFun := uncurry levels
  invFun := lam levels
  left_inv := lam_uncurry levels
  right_inv := uncurry_lam levels

theorem uncurry_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)}
    (function : QuotientCwf.Tm levels target (pi levels domain codomain))
    (reindexedFunction : QuotientCwf.Tm levels source
      (pi levels (QuotientCwf.tySub domain morphism)
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))))
    (sameFunction : HEq (QuotientCwf.tmSub function morphism) reindexedFunction) :
    QuotientCwf.tmSub (uncurry levels function)
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism domain) = uncurry levels reindexedFunction := by
  let newBody := QuotientCwf.tmSub (uncurry levels function)
    (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
      (C := QuotientCwf.cwf levels) morphism domain)
  have lambdaEquality : lam levels newBody = reindexedFunction := by
    apply Subtype.ext
    calc
      _ = (QuotientCwf.tmSub (lam levels (uncurry levels function)) morphism).val :=
        (heq_value (formation_substitution levels morphism domain codomain)
          (lambda_substitution levels morphism (uncurry levels function))).symm
      _ = (QuotientCwf.tmSub function morphism).val := by rw [lam_uncurry]
      _ = reindexedFunction.val := heq_value (formation_substitution levels morphism domain codomain) sameFunction
  exact (uncurry_lam levels newBody).symm.trans (congrArg (uncurry levels) lambdaEquality)

noncomputable def qualified : Mettapedia.TypeTheory.ContextualProductComparison.DependentProductBeta
    (QuotientCwf.cwf levels) where
  pi := pi levels
  lam := lam levels
  app := app levels
  beta := beta levels

end TypedContextual.Products
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
