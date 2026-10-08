import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualComprehensionSyntax

/-!
# Mixed dependent formation and annotation transport

Products and sums are formed in the supplied domain extension. The actual
generated congruence rules compare different domain and body annotations.
Substitution uses the complete lifted authored substitution; instantiation
retains both the body comparison and the supplied argument equation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.DependentTypes

open _root_.CategoryTheory
open QuotientComprehensionSyntax

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem transport_heq {context : QuotientCwf.QContext D}
    {first second : QuotientCwf.Ty context} (same : first = second)
    (term : QuotientCwf.Tm context first) : HEq (same ▸ term) term := by
  cases same
  rfl

def rawPi {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : TypeOver context :=
  ⟨.pi domain.code codomain.code,
    conclude (.piFormation context.raw domain.code codomain.code)
      ⟨domain.formed, codomain.formed, trivial⟩⟩

def rawSigma {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : TypeOver context :=
  ⟨.sigma domain.code codomain.code,
    conclude (.sigmaFormation context.raw domain.code codomain.code)
      ⟨domain.formed, codomain.formed, trivial⟩⟩

theorem rawPi_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (codomain : TypeOver (extend target domain)) :
    (rawPi domain codomain).reindex morphism =
      rawPi (domain.reindex morphism) (codomain.reindex (rawLift morphism domain)) := by
  apply TypeOver.ext
  change (.pi domain.code codomain.code : TypeExpr S _).substitute morphism.substitution =
    .pi (domain.code.substitute morphism.substitution)
      (codomain.code.substitute (rawLift morphism domain).substitution)
  rw [rawLift_substitution]
  rfl

theorem rawSigma_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (codomain : TypeOver (extend target domain)) :
    (rawSigma domain codomain).reindex morphism =
      rawSigma (domain.reindex morphism) (codomain.reindex (rawLift morphism domain)) := by
  apply TypeOver.ext
  change (.sigma domain.code codomain.code : TypeExpr S _).substitute morphism.substitution =
    .sigma (domain.code.substitute morphism.substitution)
      (codomain.code.substitute (rawLift morphism domain).substitution)
  rw [rawLift_substitution]
  rfl

theorem rawPi_typeEquality {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    Holds D (.typeEq context.raw (rawPi first firstBody).code (rawPi second secondBody).code) := by
  rw [extensionComparison_type_code] at sameBody
  exact conclude (.piCongruence context.raw first.code second.code firstBody.code secondBody.code)
    ⟨sameDomain, sameBody, secondBody.formed, trivial⟩

theorem rawSigma_typeEquality {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    Holds D (.typeEq context.raw (rawSigma first firstBody).code (rawSigma second secondBody).code) := by
  rw [extensionComparison_type_code] at sameBody
  exact conclude (.sigmaCongruence context.raw first.code second.code firstBody.code secondBody.code)
    ⟨sameDomain, sameBody, secondBody.formed, trivial⟩

set_option backward.isDefEq.respectTransparency false in
theorem reindexed_body_class {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty target)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)) :
    QType.mk ((QuotientCwf.typeRepresentative codomain).reindex (nativeLift morphism domain)) =
      QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain) := by
  calc
    _ = QuotientCwf.tySub (QType.mk (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeLift morphism domain)) := rfl
    _ = _ := by rw [QuotientCwf.typeRepresentative_class, nativeLift_projects]

theorem reindexed_body_equality {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty target)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)) :
    Holds D (.typeEq (QuotientCwf.ext source (QuotientCwf.tySub domain morphism)).as.raw
      ((QuotientCwf.typeRepresentative codomain).code.substitute
        (liftSubstitution (QuotientCwf.representative morphism).substitution))
      (QuotientCwf.typeRepresentative
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf D) morphism domain))).code) := by
  have same := (QType.mk_eq_iff _ _).mp ((reindexed_body_class morphism domain codomain).trans
    (QuotientCwf.typeRepresentative_class _).symm)
  change Holds D (.typeEq _ ((QuotientCwf.typeRepresentative codomain).code.substitute
    (nativeLift morphism domain).substitution) _) at same
  rw [nativeLift_substitution] at same
  exact same

set_option backward.isDefEq.respectTransparency false in
theorem reindexed_body_comparison {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty target)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)) :
    Holds D (.typeEq (extend source.as
      ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))).raw
      ((QuotientCwf.typeRepresentative codomain).reindex
        (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain))).code
      ((QuotientCwf.typeRepresentative
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf D) morphism domain))).reindex
        (extensionComparison
          ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
          (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism))
          (reindexed_domain_equality morphism domain)).hom).code) := by
  let comparison := (extensionComparison
    ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism))
    (reindexed_domain_equality morphism domain)).hom
  have same := reindex_typeEquality (reindexed_body_equality morphism domain codomain) comparison
  rw [show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
    TypeExpr.substitute_identity, TypeExpr.substitute_identity] at same
  change Holds D (.typeEq _ _
    ((QuotientCwf.typeRepresentative
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain))).code.substitute comparison.substitution))
  rw [show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
    TypeExpr.substitute_identity]
  change Holds D (.typeEq _
    ((QuotientCwf.typeRepresentative codomain).code.substitute
      (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain)).substitution) _)
  rw [rawLift_substitution]
  exact same

theorem rawInstantiation_typeEquality {context : Context D}
    (first second : TypeOver context) (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (left : Term context first) (right : Term context second)
    (sameArgument : Holds D (.termEq context.raw left.code right.code first.code)) :
    Holds D (.typeEq context.raw (firstBody.reindex (nativeSection left)).code
      (secondBody.reindex (nativeSection right)).code) := by
  let converted := right.convertType first (typeEquality_symm sameDomain)
  have sections : homEquality D (nativeSection left) (nativeSection converted) := by
    apply homEquality_pair (homEquality_refl (𝟙 context))
    rw [Term.cast_code, Term.cast_code]
    change Holds D (.termEq context.raw left.code right.code (first.code.substitute TermExpr.var))
    rw [TypeExpr.substitute_identity]
    exact sameArgument
  have arguments := (QType.mk_eq_iff _ _).mp (QType.reindex_congruent (QType.mk firstBody) sections)
  rw [extensionComparison_type_code] at sameBody
  have bodies := reindex_typeEquality sameBody (nativeSection converted)
  change Holds D (.typeEq context.raw (firstBody.code.substitute (nativeSection converted).substitution)
    (secondBody.code.substitute (nativeSection converted).substitution)) at bodies
  rw [nativeSection_substitution] at bodies
  change Holds D (.typeEq context.raw (firstBody.reindex (nativeSection left)).code
    (firstBody.code.substitute (nativeSection converted).substitution)) at arguments
  rw [nativeSection_substitution] at arguments
  change Holds D (.typeEq context.raw (firstBody.code.substitute (instantiate right.code))
    (secondBody.code.substitute (instantiate right.code))) at bodies
  change Holds D (.typeEq context.raw _ (secondBody.code.substitute (nativeSection right).substitution))
  rw [nativeSection_substitution]
  exact typeEquality_trans arguments bodies

set_option backward.isDefEq.respectTransparency false in
theorem body_at_supplied_class {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (argument : QuotientCwf.Tm context domain)
    (actual : Term context.as (QuotientCwf.typeRepresentative domain))
    (same : QTerm.mk actual = argument.val) :
    QType.mk ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection actual)) =
      QuotientCwf.tySub codomain
        (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf D) argument) := by
  calc
    _ = QuotientCwf.tySub (QType.mk (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeSection actual)) := rfl
    _ = _ := by rw [QuotientCwf.typeRepresentative_class, nativeSection_projects_of_class argument actual same]

set_option backward.isDefEq.respectTransparency false in
theorem section_substitution {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    (argument : QuotientCwf.Tm target domain) :
    morphism ≫ Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf D) argument =
      Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf D)
        (QuotientCwf.tmSub argument morphism) ≫
        Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf D) morphism domain := by
  let oldSection := Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf D) argument
  let newSection := Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf D)
    (QuotientCwf.tmSub argument morphism)
  let lifted := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
    (C := QuotientCwf.cwf D) morphism domain
  have oldBase : oldSection ≫ QuotientCwf.wk domain = 𝟙 target := QuotientCwf.wk_pair _ _ _
  have newBase : newSection ≫ QuotientCwf.wk (QuotientCwf.tySub domain morphism) = 𝟙 source :=
    QuotientCwf.wk_pair _ _ _
  have liftedBase : lifted ≫ QuotientCwf.wk domain =
      QuotientCwf.wk (QuotientCwf.tySub domain morphism) ≫ morphism :=
    Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution
      (C := QuotientCwf.cwf D) morphism domain
  apply QuotientCwf.pair_unique domain
  · change (morphism ≫ oldSection) ≫ QuotientCwf.wk domain =
      (newSection ≫ lifted) ≫ QuotientCwf.wk domain
    rw [Category.assoc, oldBase, Category.comp_id, Category.assoc, liftedBase,
      ← Category.assoc, newBase, Category.id_comp]
  · change QuotientCwf.totalSub (QuotientCwf.vz domain).val (morphism ≫ oldSection) =
      QuotientCwf.totalSub (QuotientCwf.vz domain).val (newSection ≫ lifted)
    rw [QuotientCwf.totalSub_comp, QuotientCwf.totalSub_comp]
    have oldValue : QuotientCwf.totalSub (QuotientCwf.vz domain).val oldSection = argument.val :=
      selfExtend_value argument
    have liftedValue : QuotientCwf.totalSub (QuotientCwf.vz domain).val lifted =
        (QuotientCwf.vz (QuotientCwf.tySub domain morphism)).val :=
      extensionSubstitution_value morphism domain
    rw [oldValue, liftedValue]
    exact (selfExtend_value (QuotientCwf.tmSub argument morphism)).symm

set_option backward.isDefEq.respectTransparency false in
theorem instantiated_type_substitution {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty target}
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain))
    (argument : QuotientCwf.Tm target domain) :
    QuotientCwf.tySub (QuotientCwf.tySub codomain
      (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf D) argument)) morphism =
    QuotientCwf.tySub
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain))
      (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf D)
        (QuotientCwf.tmSub argument morphism)) := by
  rw [← QuotientCwf.tySub_comp, ← QuotientCwf.tySub_comp, section_substitution]

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.DependentTypes
