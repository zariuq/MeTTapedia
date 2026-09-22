import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf
import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Native syntax of quotient comprehension maps

These comparisons connect the already constructed quotient CwF to actual
admitted substitution and term representatives. The representative is not
a normal form and does not recover the original code of a quotient class.
Argument sections and lifted substitutions are checked on the independently
formed native telescopes; their categorical equations are proved using the
existing comprehension universal property.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientComprehensionSyntax

open _root_.CategoryTheory FormationSensitive
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

variable {Head : Type} {rules : Rules Head}

theorem mk_cast {context : Context rules} {first second : TypeOver context}
    (term : Term context first) (same : first = second) :
    QTerm.mk (term.cast same) = QTerm.mk term := by
  cases same
  rfl

theorem transport_value {context : QuotientCwf.QContext rules}
    {first second : QuotientCwf.Ty context} (same : first = second)
    (term : QuotientCwf.Tm context first) : (same ▸ term).val = term.val := by
  cases same
  rfl

theorem heq_value {context : QuotientCwf.QContext rules}
    {first second : QuotientCwf.Ty context}
    {left : QuotientCwf.Tm context first} {right : QuotientCwf.Tm context second}
    (sameType : first = second) (same : HEq left right) : left.val = right.val := by
  cases sameType
  exact congrArg Subtype.val (eq_of_heq same)

theorem heq_of_value {context : QuotientCwf.QContext rules}
    {first second : QuotientCwf.Ty context}
    {left : QuotientCwf.Tm context first} {right : QuotientCwf.Tm context second}
    (same : left.val = right.val) : HEq left right := by
  have types : first = second := left.property.symm.trans
    ((congrArg QTerm.type same).trans right.property)
  cases types
  exact heq_of_eq (Subtype.ext same)

/-- This is an admitted representative at the actual chosen annotation,
not a decoder that manufactures a source typing judgment. -/
noncomputable def chosenTerm {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type) :
    Term context.as (QuotientCwf.typeRepresentative type) :=
  QuotientCwf.termRepresentative _ term.val
    (term.property.trans (QuotientCwf.typeRepresentative_class type).symm)

theorem chosenTerm_class {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type) :
    QTerm.mk (chosenTerm term) = term.val := QuotientCwf.termRepresentative_class _ _ _

theorem chosenTerm_code_eq {context : QuotientCwf.QContext rules}
    {firstType secondType : QuotientCwf.Ty context}
    {first : QuotientCwf.Tm context firstType} {second : QuotientCwf.Tm context secondType}
    (same : first.val = second.val) : (chosenTerm first).code = (chosenTerm second).code :=
  congrArg (fun term : QTerm context.as => term.out.2.code) same

theorem chosenTerm_represents {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type)
    {annotation : TypeOver context.as} (actual : Term context.as annotation)
    (same : QTerm.mk actual = term.val) :
    Conv rules.headEq (chosenTerm term).code actual.code rules.computation :=
  ((QTerm.mk_eq_iff _ _).mp ((chosenTerm_class term).trans same.symm)).2

theorem eq_of_chosen_conversion {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (first second : QuotientCwf.Tm context type)
    (converted : Conv rules.headEq (chosenTerm first).code (chosenTerm second).code
      rules.computation) : first = second := by
  apply Subtype.ext
  rw [← chosenTerm_class first, ← chosenTerm_class second]
  exact Quotient.sound ⟨.refl _, converted⟩

theorem heq_of_chosen_conversion {context : QuotientCwf.QContext rules}
    {firstType secondType : QuotientCwf.Ty context}
    (first : QuotientCwf.Tm context firstType) (second : QuotientCwf.Tm context secondType)
    (sameType : firstType = secondType)
    (converted : Conv rules.headEq (chosenTerm first).code (chosenTerm second).code
      rules.computation) : HEq first second := by
  cases sameType
  exact heq_of_eq (eq_of_chosen_conversion first second converted)

def nativeSection {context : Context rules} {type : TypeOver context}
    (argument : Term context type) : context ⟶ extend context type :=
  FormationSensitiveContextual.pair (𝟙 context) (argument.cast type.reindex_id.symm)

theorem nativeSection_substitution {context : Context rules} {type : TypeOver context}
    (argument : Term context type) :
    (nativeSection argument).substitution = subst0 argument.code := by
  funext index
  refine Fin.cases ?_ ?_ index
  · exact Term.cast_code _ _
  · intro prior
    rfl

theorem nativeSection_projection {context : Context rules} {type : TypeOver context}
    (argument : Term context type) :
    nativeSection argument ≫ projectionHom context type = 𝟙 context :=
  FormationSensitiveContextual.pair_projection _ _

theorem selfExtend_value {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (argument : QuotientCwf.Tm context type) :
    (QuotientCwf.tmSub (QuotientCwf.vz type)
      (selfExtend (QuotientCwf.cwf rules) argument)).val = argument.val := by
  change (QuotientCwf.tmSub (QuotientCwf.vz type)
    (QuotientCwf.pair (𝟙 context) type ((QuotientCwf.tySub_id type).symm ▸ argument))).val = _
  rw [QuotientCwf.vz_pair_value]
  exact transport_value _ _

theorem nativeSection_projects {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (argument : QuotientCwf.Tm context type) :
    QuotientCwf.project (nativeSection (chosenTerm argument)) =
      selfExtend (QuotientCwf.cwf rules) argument := by
  apply QuotientCwf.pair_unique type
  · have rightBase : selfExtend (QuotientCwf.cwf rules) argument ≫
        QuotientCwf.wk type = 𝟙 context :=
        QuotientCwf.wk_pair (𝟙 context) type
          ((QuotientCwf.tySub_id type).symm ▸ argument)
    exact ((quotientProjection rules).map_comp _ _).symm.trans
      ((congrArg QuotientCwf.project (nativeSection_projection
        (chosenTerm argument))).trans
          (((quotientProjection rules).map_id context.as).trans rightBase.symm))
  · change (QuotientCwf.tmSub (QuotientCwf.vz type)
      (QuotientCwf.project (nativeSection (chosenTerm argument)) :
        context ⟶ QuotientCwf.ext context type)).val =
      (QuotientCwf.tmSub (QuotientCwf.vz type)
        (selfExtend (QuotientCwf.cwf rules) argument)).val
    rw [selfExtend_value]
    change QTerm.mk ((newest context.as (QuotientCwf.typeRepresentative type)).reindex
      (nativeSection (chosenTerm argument))) = argument.val
    rw [nativeSection, QuotientCwf.raw_newest_pair, mk_cast]
    exact chosenTerm_class argument

theorem type_at_argument {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty context}
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (argument : QuotientCwf.Tm context domain) :
    QType.mk ((QuotientCwf.typeRepresentative codomain).reindex
      (nativeSection (chosenTerm argument))) =
      QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf rules) argument) := by
  calc
    _ = QuotientCwf.tySub (QType.mk (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeSection (chosenTerm argument))) := rfl
    _ = _ := by rw [QuotientCwf.typeRepresentative_class, nativeSection_projects]; rfl

theorem term_at_argument {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm (QuotientCwf.ext context domain) codomain)
    (argument : QuotientCwf.Tm context domain) :
    QTerm.mk ((chosenTerm body).reindex (nativeSection (chosenTerm argument))) =
      (QuotientCwf.tmSub body (selfExtend (QuotientCwf.cwf rules) argument)).val := by
  calc
    _ = QuotientCwf.totalSub (QTerm.mk (chosenTerm body))
        (QuotientCwf.project (nativeSection (chosenTerm argument))) := rfl
    _ = _ := by rw [chosenTerm_class, nativeSection_projects]; rfl

theorem nativeSection_projects_of_class {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (argument : QuotientCwf.Tm context type)
    (actual : Term context.as (QuotientCwf.typeRepresentative type))
    (same : QTerm.mk actual = argument.val) :
    QuotientCwf.project (nativeSection actual) =
      selfExtend (QuotientCwf.cwf rules) argument := by
  have conversion := (chosenTerm_represents argument actual same).symm
  have sections : QuotientCwf.project (nativeSection actual) =
      QuotientCwf.project (nativeSection (chosenTerm argument)) := by
    apply quotientProjection_pair_eq (homConversion_refl _)
    simpa only [Term.cast_code] using conversion
  exact sections.trans (nativeSection_projects argument)

theorem type_at_argument_of_class {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty context}
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (argument : QuotientCwf.Tm context domain)
    (actual : Term context.as (QuotientCwf.typeRepresentative domain))
    (same : QTerm.mk actual = argument.val) :
    QType.mk ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection actual)) =
      QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf rules) argument) := by
  calc
    _ = QuotientCwf.tySub (QType.mk (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeSection actual)) := rfl
    _ = _ := by
      rw [QuotientCwf.typeRepresentative_class,
        nativeSection_projects_of_class argument actual same]
      rfl

/-- The source binder is independently formed. Native context conversion
checks the ordinary lifted substitution at that possibly different code. -/
def convertedLift {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) (sourceType : TypeOver source)
    (converted : Conv rules.headEq (subst morphism.substitution type.code)
      sourceType.code rules.computation) :
    extend source sourceType ⟶ extend target type where
  substitution := liftSub morphism.substitution
  typed := fun index => ((morphism.typed.lift type.code) index).convertNewest
    (type.reindex morphism).formed type.universeWitness converted

theorem convertedLift_substitution {source target : Context rules}
    (morphism : source ⟶ target) (type : TypeOver target) (sourceType : TypeOver source)
    (converted : Conv rules.headEq (subst morphism.substitution type.code)
      sourceType.code rules.computation) :
    (convertedLift morphism type sourceType converted).substitution =
      liftSub morphism.substitution := rfl

theorem reindexed_domain_conversion {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    Conv rules.headEq
      (subst (QuotientCwf.representative morphism).substitution
        (QuotientCwf.typeRepresentative type).code)
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)).code
      rules.computation :=
  (QType.mk_eq_iff _ _).mp ((QuotientCwf.represented_type_reindex type morphism).trans
    (QuotientCwf.typeRepresentative_class (QuotientCwf.tySub type morphism)).symm)

noncomputable def nativeLift {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    (QuotientCwf.ext source (QuotientCwf.tySub type morphism)).as ⟶
      (QuotientCwf.ext target type).as :=
  convertedLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative type)
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism))
    (reindexed_domain_conversion morphism type)

theorem nativeLift_projection {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    nativeLift morphism type ≫ projectionHom target.as (QuotientCwf.typeRepresentative type) =
      projectionHom source.as (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism))
        ≫ QuotientCwf.representative morphism := by
  apply Hom.ext
  funext index
  change rename wk ((QuotientCwf.representative morphism).substitution index) =
    subst projection ((QuotientCwf.representative morphism).substitution index)
  exact (subst_projection _).symm

theorem nativeLift_newest {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    QTerm.mk ((newest target.as (QuotientCwf.typeRepresentative type)).reindex
      (nativeLift morphism type)) =
    QTerm.mk (newest source.as
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism))) := by
  apply Quotient.sound
  constructor
  · change Conv rules.headEq
      (subst (liftSub (QuotientCwf.representative morphism).substitution)
        (subst projection (QuotientCwf.typeRepresentative type).code))
      (subst projection (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)).code) _
    rw [subst_projection, subst_projection, subst_liftSub_wk]
    exact (reindexed_domain_conversion morphism type).renameTerms wk
  · exact .refl _

theorem extensionSubstitution_value {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    (QuotientCwf.tmSub (QuotientCwf.vz type)
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf rules) morphism type)).val =
      (QuotientCwf.vz (QuotientCwf.tySub type morphism)).val := by
  let lifted := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
    (C := QuotientCwf.cwf rules) morphism type
  have bases : lifted ≫ QuotientCwf.wk type =
      QuotientCwf.wk (QuotientCwf.tySub type morphism) ≫ morphism :=
    Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution
      (C := QuotientCwf.cwf rules) morphism type
  apply heq_value
  · exact (QuotientCwf.tySub_comp type lifted (QuotientCwf.wk type)).symm.trans
      ((congrArg (QuotientCwf.tySub type) bases).trans
        (QuotientCwf.tySub_comp type (QuotientCwf.wk (QuotientCwf.tySub type morphism)) morphism))
  · exact Mettapedia.GSLT.Core.ContextualLadder.TypeOver.vz_extensionSubstitution
      (C := QuotientCwf.cwf rules) morphism type

theorem nativeLift_projects {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    QuotientCwf.project (nativeLift morphism type) =
      Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf rules) morphism type := by
  apply QuotientCwf.pair_unique type
  · have rightBase :=
      Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution
        (C := QuotientCwf.cwf rules) morphism type
    exact ((quotientProjection rules).map_comp _ _).symm.trans
      ((congrArg QuotientCwf.project (nativeLift_projection morphism type)).trans
        (((quotientProjection rules).map_comp _ _).trans
          ((congrArg (fun next => QuotientCwf.wk (QuotientCwf.tySub type morphism) ≫ next)
            (QuotientCwf.project_representative morphism)).trans rightBase.symm)))
  · exact (nativeLift_newest morphism type).trans
      (extensionSubstitution_value morphism type).symm

theorem chosenTerm_reindex_represents {source target : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty target} (term : QuotientCwf.Tm target type)
    (morphism : source ⟶ target) :
    Conv rules.headEq (chosenTerm (QuotientCwf.tmSub term morphism)).code
      (subst (QuotientCwf.representative morphism).substitution (chosenTerm term).code)
      rules.computation := by
  apply chosenTerm_represents (QuotientCwf.tmSub term morphism)
    ((chosenTerm term).reindex (QuotientCwf.representative morphism))
  calc
    _ = QuotientCwf.totalSub (QTerm.mk (chosenTerm term))
        (QuotientCwf.project (QuotientCwf.representative morphism)) := rfl
    _ = _ := by rw [chosenTerm_class, QuotientCwf.project_representative]; rfl

theorem reindexed_codomain_conversion {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)) :
    Conv rules.headEq
      (subst (liftSub (QuotientCwf.representative morphism).substitution)
        (QuotientCwf.typeRepresentative codomain).code)
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub codomain
        (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf rules) morphism domain))).code rules.computation := by
  apply (QType.mk_eq_iff
    ((QuotientCwf.typeRepresentative codomain).reindex (nativeLift morphism domain)) _).mp
  calc
    _ = QuotientCwf.tySub (QType.mk (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeLift morphism domain)) := rfl
    _ = _ := by
      exact (congrArg (fun type => QuotientCwf.tySub type
        (QuotientCwf.project (nativeLift morphism domain)))
          (QuotientCwf.typeRepresentative_class codomain)).trans
        ((congrArg (QuotientCwf.tySub codomain) (nativeLift_projects morphism domain)).trans
          (QuotientCwf.typeRepresentative_class _).symm)

theorem chosenTerm_lift_reindex_represents {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)}
    (body : QuotientCwf.Tm (QuotientCwf.ext target domain) codomain) :
    Conv rules.headEq (chosenTerm (QuotientCwf.tmSub body
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf rules) morphism domain))).code
      (subst (liftSub (QuotientCwf.representative morphism).substitution)
        (chosenTerm body).code) rules.computation := by
  apply chosenTerm_represents _ ((chosenTerm body).reindex (nativeLift morphism domain))
  calc
    _ = QuotientCwf.totalSub (QTerm.mk (chosenTerm body))
        (QuotientCwf.project (nativeLift morphism domain)) := rfl
    _ = _ := (congrArg (fun term => QuotientCwf.totalSub term
      (QuotientCwf.project (nativeLift morphism domain))) (chosenTerm_class body)).trans
        (congrArg (QuotientCwf.totalSub body.val) (nativeLift_projects morphism domain))

theorem argument_reindex_square {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    (argument : QuotientCwf.Tm target domain) :
    selfExtend (QuotientCwf.cwf rules) (QuotientCwf.tmSub argument morphism) ≫
        Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf rules) morphism domain =
      morphism ≫ selfExtend (QuotientCwf.cwf rules) argument := by
  let left := nativeSection (chosenTerm (QuotientCwf.tmSub argument morphism)) ≫
    nativeLift morphism domain
  let right := QuotientCwf.representative morphism ≫ nativeSection (chosenTerm argument)
  have converted : homConversion rules left right := by
    intro index
    refine Fin.cases ?_ ?_ index
    · change Conv rules.headEq
        (subst (nativeSection (chosenTerm (QuotientCwf.tmSub argument morphism))).substitution
          (.var 0))
        (subst (QuotientCwf.representative morphism).substitution
          ((nativeSection (chosenTerm argument)).substitution 0)) _
      rw [nativeSection_substitution, nativeSection_substitution]
      exact chosenTerm_reindex_represents argument morphism
    · intro prior
      change Conv rules.headEq
        (subst (nativeSection (chosenTerm (QuotientCwf.tmSub argument morphism))).substitution
          (rename wk ((QuotientCwf.representative morphism).substitution prior)))
        (subst (QuotientCwf.representative morphism).substitution
          ((nativeSection (chosenTerm argument)).substitution prior.succ)) _
      rw [nativeSection_substitution, nativeSection_substitution]
      change Conv rules.headEq
        (inst0 (chosenTerm (QuotientCwf.tmSub argument morphism)).code
          (rename wk ((QuotientCwf.representative morphism).substitution prior)))
        ((QuotientCwf.representative morphism).substitution prior) _
      rw [inst0_rename_wk]
      exact .refl _
  have projected := (quotientProjection_map_eq_iff left right).mpr converted
  have leftEquation : QuotientCwf.project left =
      selfExtend (QuotientCwf.cwf rules) (QuotientCwf.tmSub argument morphism) ≫
        Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf rules) morphism domain :=
    ((quotientProjection rules).map_comp _ _).trans
      (congrArg₂ (fun first second => first ≫ second)
        (nativeSection_projects (QuotientCwf.tmSub argument morphism))
        (nativeLift_projects morphism domain))
  have rightEquation : QuotientCwf.project right =
      morphism ≫ selfExtend (QuotientCwf.cwf rules) argument :=
    ((quotientProjection rules).map_comp _ _).trans
      (congrArg₂ (fun first second => first ≫ second)
        (QuotientCwf.project_representative morphism) (nativeSection_projects argument))
  exact leftEquation.symm.trans (projected.trans rightEquation)

theorem instantiatedType_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain))
    (argument : QuotientCwf.Tm target domain) :
    QuotientCwf.tySub (QuotientCwf.tySub codomain
      (selfExtend (QuotientCwf.cwf rules) argument)) morphism =
    QuotientCwf.tySub (QuotientCwf.tySub codomain
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf rules) morphism domain))
      (selfExtend (QuotientCwf.cwf rules) (QuotientCwf.tmSub argument morphism)) :=
  (QuotientCwf.tySub_comp codomain morphism (selfExtend (QuotientCwf.cwf rules) argument)).symm.trans
    ((congrArg (QuotientCwf.tySub codomain) (argument_reindex_square morphism argument).symm).trans
      (QuotientCwf.tySub_comp codomain _ _))

end FormationSensitiveContextual.QuotientComprehensionSyntax
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
