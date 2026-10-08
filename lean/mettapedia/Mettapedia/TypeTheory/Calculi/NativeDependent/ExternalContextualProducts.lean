import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualDependentTypes
import Mettapedia.TypeTheory.ContextualPiEta

/-!
# Generated external products on the contextual quotient

Formation, abstraction and application use actual generated admissions after
retyping complete supplied classes at selected annotations. Mixed annotation
congruence is used for substitution. Product beta and eta compare complete
term classes; the inverse body map retains every dependent argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Products

open _root_.CategoryTheory
open DependentTypes QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u
variable {S : Symbols.{u}} {D : Signature S}

def rawLam {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (body : Term (extend context domain) codomain) : Term context (rawPi domain codomain) :=
  ⟨.lam domain.code codomain.code body.code,
    conclude (.lambda context.raw domain.code codomain.code body.code)
      ⟨domain.formed, codomain.formed, body.typed, trivial⟩⟩

def rawApp {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (function : Term context (rawPi domain codomain)) (argument : Term context domain) :
    Term context (codomain.reindex (nativeSection argument)) where
  code := .app domain.code codomain.code function.code argument.code
  typed := by
    change Holds D (.term context.raw (.app domain.code codomain.code function.code argument.code)
      (codomain.code.substitute (nativeSection argument).substitution))
    rw [nativeSection_substitution]
    exact conclude (.application context.raw domain.code codomain.code function.code argument.code)
      ⟨domain.formed, codomain.formed, function.typed, argument.typed, trivial⟩

theorem rawLam_congruent {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first second : Term (extend context domain) codomain)
    (same : Holds D (.termEq (extend context domain).raw first.code second.code codomain.code)) :
    QTerm.mk (rawLam first) = QTerm.mk (rawLam second) :=
  (QTerm.mk_eq_iff _ _).mpr ⟨typeEquality_refl _,
    conclude (.lambdaCongruence context.raw domain.code codomain.code first.code second.code)
      ⟨domain.formed, codomain.formed, same, trivial⟩⟩

theorem rawLam_compared {context : Context D}
    (first second : TypeOver context) (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (left : Term (extend context first) firstBody) (right : Term (extend context second) secondBody)
    (same : Holds D (.termEq (extend context first).raw left.code
      (right.reindex (extensionComparison first second sameDomain).hom).code firstBody.code)) :
    QTerm.mk (rawLam left) = QTerm.mk (rawLam right) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨rawPi_typeEquality _ _ sameDomain _ _ sameBody, ?_⟩
  rw [extensionComparison_type_code] at sameBody
  rw [extensionComparison_term_code] at same
  exact conclude (.lambdaAnnotationCongruence context.raw first.code second.code firstBody.code
    secondBody.code left.code right.code) ⟨sameDomain, sameBody, secondBody.formed, same, right.typed, trivial⟩

theorem rawApp_function_congruent {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (first second : Term context (rawPi domain codomain)) (argument : Term context domain)
    (same : Holds D (.termEq context.raw first.code second.code (rawPi domain codomain).code)) :
    QTerm.mk (rawApp first argument) = QTerm.mk (rawApp second argument) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl _, ?_⟩
  change Holds D (.termEq context.raw _ _ (codomain.code.substitute (nativeSection argument).substitution))
  rw [nativeSection_substitution]
  exact conclude (.applicationCongruence context.raw domain.code codomain.code first.code second.code
    argument.code argument.code) ⟨domain.formed, codomain.formed, same, termEquality_refl argument, trivial⟩

theorem rawBeta {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (body : Term (extend context domain) codomain) (argument : Term context domain) :
    QTerm.mk (rawApp (rawLam body) argument) = QTerm.mk (body.reindex (nativeSection argument)) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl _, ?_⟩
  change Holds D (.termEq context.raw _ (body.code.substitute (nativeSection argument).substitution)
    (codomain.code.substitute (nativeSection argument).substitution))
  rw [nativeSection_substitution]
  exact conclude (.piBeta context.raw domain.code codomain.code body.code argument.code)
    ⟨domain.formed, codomain.formed, body.typed, argument.typed, trivial⟩

theorem rawLam_reindex {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (body : Term (extend target domain) codomain) :
    ((rawLam body).reindex morphism).cast (rawPi_reindex morphism domain codomain) =
      rawLam (body.reindex (rawLift morphism domain)) := by
  apply Term.ext
  rw [Term.cast_code]
  change (.lam domain.code codomain.code body.code : TermExpr S _).substitute morphism.substitution =
    .lam (domain.code.substitute morphism.substitution)
      (codomain.code.substitute (rawLift morphism domain).substitution)
      (body.code.substitute (rawLift morphism domain).substitution)
  rw [rawLift_substitution]
  rfl

theorem rawInstantiation_reindex {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} (codomain : TypeOver (extend target domain)) (argument : Term target domain) :
    (codomain.reindex (nativeSection argument)).reindex morphism =
      (codomain.reindex (rawLift morphism domain)).reindex (nativeSection (argument.reindex morphism)) := by
  apply TypeOver.ext
  change (codomain.code.substitute (nativeSection argument).substitution).substitute morphism.substitution =
    (codomain.code.substitute (rawLift morphism domain).substitution).substitute
      (nativeSection (argument.reindex morphism)).substitution
  rw [nativeSection_substitution, nativeSection_substitution, rawLift_substitution]
  exact TypeExpr.substitute_instantiate morphism.substitution codomain.code argument.code

theorem rawApp_reindex {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (function : Term target (rawPi domain codomain)) (argument : Term target domain) :
    ((rawApp function argument).reindex morphism).cast (rawInstantiation_reindex morphism codomain argument) =
      rawApp ((function.reindex morphism).cast (rawPi_reindex morphism domain codomain))
        (argument.reindex morphism) := by
  apply Term.ext
  rw [Term.cast_code]
  change (.app domain.code codomain.code function.code argument.code : TermExpr S _).substitute
    morphism.substitution = .app (domain.code.substitute morphism.substitution)
      (codomain.code.substitute (rawLift morphism domain).substitution)
      ((function.reindex morphism).cast (rawPi_reindex morphism domain codomain)).code
      (argument.code.substitute morphism.substitution)
  rw [Term.cast_code, rawLift_substitution]
  rfl

theorem rawApp_compared {context : Context D}
    (first second : TypeOver context) (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (leftFunction : Term context (rawPi first firstBody)) (rightFunction : Term context (rawPi second secondBody))
    (left : Term context first) (right : Term context second)
    (sameFunction : Holds D (.termEq context.raw leftFunction.code rightFunction.code (rawPi first firstBody).code))
    (sameArgument : Holds D (.termEq context.raw left.code right.code first.code)) :
    QTerm.mk (rawApp leftFunction left) = QTerm.mk (rawApp rightFunction right) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨rawInstantiation_typeEquality _ _ sameDomain _ _ sameBody _ _ sameArgument, ?_⟩
  rw [extensionComparison_type_code] at sameBody
  change Holds D (.termEq context.raw _ _ (firstBody.code.substitute (nativeSection left).substitution))
  rw [nativeSection_substitution]
  exact conclude (.applicationAnnotationCongruence context.raw first.code second.code firstBody.code
    secondBody.code leftFunction.code rightFunction.code left.code right.code)
    ⟨sameDomain, sameBody, secondBody.formed, sameFunction, sameArgument, rightFunction.typed, right.typed, trivial⟩

noncomputable def pi {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) : QuotientCwf.Ty context :=
  QType.mk (rawPi (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))

noncomputable def lam {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm (QuotientCwf.ext context domain) codomain) : QuotientCwf.Tm context (pi domain codomain) :=
  ⟨QTerm.mk (rawLam (chosenTerm body)), rfl⟩

noncomputable def functionRepresentative {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (function : QuotientCwf.Tm context (pi domain codomain)) :
    Term context.as (rawPi (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)) :=
  QuotientCwf.termRepresentative _ function.val function.property

theorem functionRepresentative_class {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)} (function : QuotientCwf.Tm context (pi domain codomain)) :
    QTerm.mk (functionRepresentative function) = function.val := QuotientCwf.termRepresentative_class _ _ _

noncomputable def app {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)} (function : QuotientCwf.Tm context (pi domain codomain))
    (argument : QuotientCwf.Tm context domain) :
    QuotientCwf.Tm context (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) argument)) :=
  ⟨QTerm.mk (rawApp (functionRepresentative function) (chosenTerm argument)), type_at_argument codomain argument⟩

noncomputable def operations (D : Signature S) : PiOperations (QuotientCwf.cwf D) where
  pi := pi
  lam := lam
  app := app

theorem beta : PiBeta (operations D) := by
  intro context domain codomain body argument
  apply Subtype.ext
  have functions := (QTerm.mk_eq_iff _ _).mp (functionRepresentative_class (lam body))
  exact (rawApp_function_congruent _ _ (chosenTerm argument) functions.2).trans
    ((rawBeta (chosenTerm body) (chosenTerm argument)).trans (term_at_argument body argument))

theorem formation_substitution : StrictPiFormationSubstitution (operations D) := by
  intro source target morphism domain codomain
  change QuotientCwf.tySub (pi domain codomain) morphism = _
  rw [← QuotientCwf.represented_type_reindex (pi domain codomain) morphism]
  have annotation : QType.mk (QuotientCwf.typeRepresentative (pi domain codomain)) =
      QType.mk (rawPi (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)) :=
    QuotientCwf.typeRepresentative_class _
  have reindexed := congrArg (fun type => QType.reindex type (QuotientCwf.representative morphism)) annotation
  rw [QType.reindex_mk, QType.reindex_mk, rawPi_reindex] at reindexed
  apply reindexed.trans
  apply (QType.mk_eq_iff _ _).mpr
  exact rawPi_typeEquality _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison morphism domain codomain)

theorem supplied_reindex_class {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) {type : QuotientCwf.Ty target} (term : QuotientCwf.Tm target type)
    {annotation : TypeOver target.as} (actual : Term target.as annotation) (same : QTerm.mk actual = term.val) :
    QTerm.mk (actual.reindex (QuotientCwf.representative morphism)) = (QuotientCwf.tmSub term morphism).val := by
  calc
    _ = QuotientCwf.totalSub (QTerm.mk actual) (QuotientCwf.project (QuotientCwf.representative morphism)) := rfl
    _ = _ := by rw [same, QuotientCwf.project_representative]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem body_reindex_class {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)} (body : QuotientCwf.Tm (QuotientCwf.ext target domain) codomain) :
    QTerm.mk ((chosenTerm body).reindex (nativeLift morphism domain)) =
      (QuotientCwf.tmSub body (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain)).val := by
  calc
    _ = QuotientCwf.totalSub (QTerm.mk (chosenTerm body)) (QuotientCwf.project (nativeLift morphism domain)) := rfl
    _ = _ := by rw [chosenTerm_class, nativeLift_projects]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem lambda_substitution {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)} (body : QuotientCwf.Tm (QuotientCwf.ext target domain) codomain) :
    HEq (QuotientCwf.tmSub (lam body) morphism)
      (lam (QuotientCwf.tmSub body (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain))) := by
  apply heq_of_value
  let newBody := QuotientCwf.tmSub body (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
    (C := QuotientCwf.cwf D) morphism domain)
  let comparison := (extensionComparison
    ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism))
    (reindexed_domain_equality morphism domain)).hom
  have bodies := (QTerm.mk_eq_iff _ _).mp ((body_reindex_class morphism body).trans (chosenTerm_class newBody).symm)
  have moved := reindex_termEquality bodies.2 comparison
  change Holds D (.termEq _
    (((chosenTerm body).code.substitute (nativeLift morphism domain).substitution).substitute comparison.substitution)
    ((chosenTerm newBody).code.substitute comparison.substitution)
    (((QuotientCwf.typeRepresentative codomain).code.substitute (nativeLift morphism domain).substitution).substitute
      comparison.substitution)) at moved
  rw [nativeLift_substitution, show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
    TermExpr.substitute_identity, TermExpr.substitute_identity, TypeExpr.substitute_identity] at moved
  have compared := rawLam_compared _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison morphism domain codomain)
    ((chosenTerm body).reindex (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain)))
    (chosenTerm newBody) (by
      change Holds D (.termEq _ _ ((chosenTerm newBody).code.substitute comparison.substitution) _)
      rw [show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
        TermExpr.substitute_identity]
      change Holds D (.termEq _ ((chosenTerm body).code.substitute
        (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain)).substitution) _
        ((QuotientCwf.typeRepresentative codomain).code.substitute
          (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain)).substitution))
      rw [rawLift_substitution]
      exact moved)
  have actual := supplied_reindex_class morphism (lam body) (rawLam (chosenTerm body)) rfl
  exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
    ((congrArg QTerm.mk (rawLam_reindex (QuotientCwf.representative morphism) (chosenTerm body))).trans compared))

set_option backward.isDefEq.respectTransparency false in
theorem application_substitution {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)} (function : QuotientCwf.Tm target (pi domain codomain))
    (argument : QuotientCwf.Tm target domain)
    (reindexedFunction : QuotientCwf.Tm source (pi (QuotientCwf.tySub domain morphism)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain))))
    (sameFunction : HEq (QuotientCwf.tmSub function morphism) reindexedFunction) :
    HEq (QuotientCwf.tmSub (app function argument) morphism)
      (app reindexedFunction (QuotientCwf.tmSub argument morphism)) := by
  apply heq_of_value
  let oldFunction := functionRepresentative function
  let oldArgument := chosenTerm argument
  let newFunction := (oldFunction.reindex (QuotientCwf.representative morphism)).cast
    (rawPi_reindex (QuotientCwf.representative morphism) _ _)
  let newArgument := oldArgument.reindex (QuotientCwf.representative morphism)
  have functions : QTerm.mk newFunction = QTerm.mk (functionRepresentative reindexedFunction) :=
    (QTerm.mk_cast _ _).trans ((supplied_reindex_class morphism function oldFunction
      (functionRepresentative_class function)).trans
        ((heq_value (formation_substitution morphism domain codomain) sameFunction).trans
          (functionRepresentative_class reindexedFunction).symm))
  have arguments : QTerm.mk newArgument = QTerm.mk (chosenTerm (QuotientCwf.tmSub argument morphism)) :=
    (supplied_reindex_class morphism argument oldArgument (chosenTerm_class argument)).trans
      (chosenTerm_class (QuotientCwf.tmSub argument morphism)).symm
  have compared := rawApp_compared _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison morphism domain codomain) newFunction (functionRepresentative reindexedFunction)
    newArgument (chosenTerm (QuotientCwf.tmSub argument morphism))
    ((QTerm.mk_eq_iff _ _).mp functions).2 ((QTerm.mk_eq_iff _ _).mp arguments).2
  have actual := supplied_reindex_class morphism (app function argument) (rawApp oldFunction oldArgument) rfl
  exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
    ((congrArg QTerm.mk (rawApp_reindex (QuotientCwf.representative morphism) oldFunction oldArgument)).trans compared))

theorem substitution : StrictPiSubstitution (operations D) :=
  ⟨formation_substitution, lambda_substitution, application_substitution⟩

theorem fresh_instantiation {n : Nat} (body : TermExpr S (n + 1)) :
    (body.rename (liftRenaming (Fin.succ : Renaming n (n + 1)))).substitute
      (instantiate (.var (0 : Fin (n + 1)))) = body := by
  rw [TermExpr.substitute_rename]
  have mappingSame : instantiate (S := S) (.var (0 : Fin (n + 1))) ∘
      liftRenaming (Fin.succ : Renaming n (n + 1)) = TermExpr.var := by
    funext index
    cases index using Fin.cases <;> rfl
  rw [mappingSame, TermExpr.substitute_identity]

theorem rawFreshAnnotation {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    (codomain.reindex (rawLift (projectionHom context domain) domain)).reindex
      (nativeSection (newest context domain)) = codomain := by
  apply TypeOver.ext
  change (codomain.code.substitute (rawLift (projectionHom context domain) domain).substitution).substitute
    (nativeSection (newest context domain)).substitution = codomain.code
  rw [nativeSection_substitution, rawLift_substitution]
  change (codomain.code.substitute (liftSubstitution (fun index => .var index.succ))).substitute
    (instantiate (.var (0 : Fin (context.arity + 1)))) = codomain.code
  rw [liftSubstitution_variables, TypeExpr.substitute_variables, TypeExpr.etaBody_instantiate]

def rawFreshApp {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (function : Term context (rawPi domain codomain)) :
    Term (extend context domain) codomain :=
  (rawApp ((function.reindex (projectionHom context domain)).cast
      (rawPi_reindex (projectionHom context domain) domain codomain)) (newest context domain)).cast
    (rawFreshAnnotation domain codomain)

theorem rawFreshApp_code {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (function : Term context (rawPi domain codomain)) :
    (rawFreshApp function).code = .app (domain.code.rename Fin.succ)
      (codomain.code.rename (liftRenaming Fin.succ)) (function.code.rename Fin.succ) (.var 0) := by
  rw [rawFreshApp, Term.cast_code]
  change (TermExpr.app (domain.code.substitute (fun index => .var index.succ))
    (codomain.code.substitute (rawLift (projectionHom context domain) domain).substitution)
    ((function.reindex (projectionHom context domain)).cast (rawPi_reindex _ _ _)).code (.var 0) : TermExpr S _) = _
  rw [Term.cast_code, rawLift_substitution]
  change (TermExpr.app _ (codomain.code.substitute (liftSubstitution (fun index => .var index.succ)))
    (function.code.substitute (fun index => .var index.succ)) (.var 0) : TermExpr S _) = _
  rw [liftSubstitution_variables, TypeExpr.substitute_variables, TypeExpr.substitute_variables,
    TermExpr.substitute_variables]

theorem rawFreshApp_congruent {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first second : Term context (rawPi domain codomain))
    (same : Holds D (.termEq context.raw first.code second.code (rawPi domain codomain).code)) :
    QTerm.mk (rawFreshApp first) = QTerm.mk (rawFreshApp second) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl codomain, ?_⟩
  let projection := projectionHom context domain
  let argument := newest context domain
  let body := codomain.reindex (rawLift projection domain)
  have reindexed : Holds D (.termEq (extend context domain).raw
      (first.reindex projection).code (second.reindex projection).code
      (.pi (domain.reindex projection).code body.code)) := by
    have compared := reindex_termEquality same projection
    change Holds D (.termEq _ _ _ ((rawPi domain codomain).reindex projection).code) at compared
    rw [rawPi_reindex] at compared
    exact compared
  have compared := conclude (.applicationCongruence (extend context domain).raw
    (domain.reindex projection).code body.code (first.reindex projection).code (second.reindex projection).code
    argument.code argument.code) ⟨(domain.reindex projection).formed, body.formed,
      reindexed, termEquality_refl argument, trivial⟩
  change Holds D (.termEq (extend context domain).raw
    (.app (domain.code.substitute projection.substitution) body.code (first.code.substitute projection.substitution) (.var 0))
    (.app (domain.code.substitute projection.substitution) body.code (second.code.substitute projection.substitution) (.var 0))
    (body.code.substitute (instantiate (.var (0 : Fin (context.arity + 1)))))) at compared
  change Holds D (.termEq _ (rawFreshApp first).code (rawFreshApp second).code codomain.code)
  rw [rawFreshApp_code, rawFreshApp_code]
  simpa only [body, TypeOver.reindex, projection, projectionHom, rawLift_substitution,
    liftSubstitution_variables, TypeExpr.substitute_variables, TermExpr.substitute_variables,
    TypeExpr.etaBody_instantiate] using compared

theorem rawFreshBeta {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (body : Term (extend context domain) codomain) :
    QTerm.mk (rawFreshApp (rawLam body)) = QTerm.mk body := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl codomain, ?_⟩
  let projection := projectionHom context domain
  let lifted := rawLift projection domain
  let argument := newest context domain
  have compared := conclude (.piBeta (extend context domain).raw (domain.reindex projection).code
    (codomain.reindex lifted).code (body.reindex lifted).code argument.code)
    ⟨(domain.reindex projection).formed, (codomain.reindex lifted).formed,
      (body.reindex lifted).typed, argument.typed, trivial⟩
  change Holds D (.termEq _ (rawFreshApp (rawLam body)).code body.code codomain.code)
  rw [rawFreshApp_code]
  simpa only [RuleCode.conclusion, lifted, projection, argument, rawLam, Term.reindex, TypeOver.reindex,
    projectionHom, rawLift_substitution, liftSubstitution_variables, TypeExpr.substitute_variables,
    TermExpr.substitute_variables, TypeExpr.etaBody_instantiate, fresh_instantiation, newest,
    TermExpr.rename] using compared

theorem rawEta {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (function : Term context (rawPi domain codomain)) :
    QTerm.mk (rawLam (rawFreshApp function)) = QTerm.mk function := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl _, ?_⟩
  change Holds D (.termEq context.raw (.lam domain.code codomain.code (rawFreshApp function).code)
    function.code (.pi domain.code codomain.code))
  rw [rawFreshApp_code]
  exact conclude (.piEta context.raw domain.code codomain.code function.code)
    ⟨domain.formed, codomain.formed, function.typed, trivial⟩

noncomputable def uncurry {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)} (function : QuotientCwf.Tm context (pi domain codomain)) :
    QuotientCwf.Tm (QuotientCwf.ext context domain) codomain :=
  ⟨QTerm.mk (rawFreshApp (functionRepresentative function)), QuotientCwf.typeRepresentative_class codomain⟩

theorem uncurry_lam {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)} (body : QuotientCwf.Tm (QuotientCwf.ext context domain) codomain) :
    uncurry (lam body) = body := by
  apply Subtype.ext
  have functions := (QTerm.mk_eq_iff _ _).mp (functionRepresentative_class (lam body))
  exact (rawFreshApp_congruent _ _ functions.2).trans ((rawFreshBeta (chosenTerm body)).trans (chosenTerm_class body))

theorem lam_uncurry {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)} (function : QuotientCwf.Tm context (pi domain codomain)) :
    lam (uncurry function) = function := by
  apply Subtype.ext
  have bodies := chosenTerm_represents (uncurry function) (rawFreshApp (functionRepresentative function)) rfl
  exact (rawLam_congruent _ _ bodies).trans ((rawEta (functionRepresentative function)).trans
    (functionRepresentative_class function))

noncomputable def sectionEquiv {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    QuotientCwf.Tm context (pi domain codomain) ≃ QuotientCwf.Tm (QuotientCwf.ext context domain) codomain where
  toFun := uncurry
  invFun := lam
  left_inv := lam_uncurry
  right_inv := uncurry_lam

theorem uncurry_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target)
    {domain : QuotientCwf.Ty target} {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)}
    (function : QuotientCwf.Tm target (pi domain codomain))
    (reindexedFunction : QuotientCwf.Tm source (pi (QuotientCwf.tySub domain morphism)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain))))
    (sameFunction : HEq (QuotientCwf.tmSub function morphism) reindexedFunction) :
    QuotientCwf.tmSub (uncurry function) (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
      (C := QuotientCwf.cwf D) morphism domain) = uncurry reindexedFunction := by
  let newBody := QuotientCwf.tmSub (uncurry function)
    (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution (C := QuotientCwf.cwf D) morphism domain)
  have lambdaEquality : lam newBody = reindexedFunction := by
    apply Subtype.ext
    calc
      _ = (QuotientCwf.tmSub (lam (uncurry function)) morphism).val :=
        (heq_value (formation_substitution morphism domain codomain) (lambda_substitution morphism (uncurry function))).symm
      _ = (QuotientCwf.tmSub function morphism).val := by rw [lam_uncurry]
      _ = reindexedFunction.val := heq_value (formation_substitution morphism domain codomain) sameFunction
  exact (uncurry_lam newBody).symm.trans (congrArg uncurry lambdaEquality)

set_option backward.isDefEq.respectTransparency false in
theorem genericSection_eq_uncurry {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)} (function : QuotientCwf.Tm context (pi domain codomain)) :
    Mettapedia.TypeTheory.ContextualPiEta.genericSection (operations D) formation_substitution function =
      uncurry function := by
  let C := QuotientCwf.cwf D
  let s := C.wk domain
  let lifted := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution (C := C) s domain
  let g := selfExtend C (C.vz domain)
  let weakened := reindexFunction (operations D) formation_substitution s function
  have functionRelated := (reindexFunction_heq (operations D) formation_substitution s function).symm
  have bodyRelated := uncurry_substitution s function weakened functionRelated
  have actualApplication : HEq (app weakened (C.vz domain)) (C.tmSub (uncurry weakened) g) := by
    have equation := beta (uncurry weakened) (C.vz domain)
    change app (lam (uncurry weakened)) (C.vz domain) = C.tmSub (uncurry weakened) g at equation
    rw [lam_uncurry] at equation
    exact heq_of_eq equation
  have substituted := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.tmSub_heq (C := C)
    rfl (heq_of_eq bodyRelated.symm) g
  have composed := (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.tmSub_comp_heq (C := C)
    (uncurry function) lifted g).symm
  have identity : C.compS lifted g = C.idS (C.ext context domain) :=
    Mettapedia.TypeTheory.ContextualPiEta.lifted_generic_identity (C := C) domain
  rw [identity] at composed
  apply eq_of_heq
  exact (Mettapedia.TypeTheory.ContextualPiEta.genericSection_heq (operations D) formation_substitution function).trans
    (actualApplication.trans (substituted.trans (composed.trans
      ((heq_of_eq (C.tmSub_id (uncurry function))).trans (cast_heq _ _)))))

theorem eta : Mettapedia.TypeTheory.ContextualPiEta.PiEta (operations D) formation_substitution := by
  intro context domain codomain function
  exact (congrArg lam (genericSection_eq_uncurry function)).trans (lam_uncurry function)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Products
