import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualComprehensionSyntax

/-!
# Actual dependent type formation with typed annotation comparison

Universe joins supply an admitted result universe for each product and sum.
The codomain is formed in the actual extension of its domain. Congruence
compares different domain annotations through their typed context isomorphism,
and raw substitution uses the actual lifted variable substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual.DependentTypes

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization
open TypedContextual.QuotientComprehensionSyntax

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

theorem transport_heq {context : QuotientCwf.QContext rules}
    {first second : QuotientCwf.Ty levels context} (same : first = second)
    (term : QuotientCwf.Tm levels context first) : HEq (same ▸ term) term := by
  cases same
  rfl

noncomputable def joinedLevel {context : Context rules} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : Head :=
  Classical.choose (levels.join_exists domain.universeWitness codomain.universeWitness)

theorem joinedLevel_rule {context : Context rules} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    rules.join domain.level codomain.level (joinedLevel levels domain codomain) :=
  Classical.choose_spec (levels.join_exists domain.universeWitness codomain.universeWitness)

theorem joinedLevel_universe {context : Context rules} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    rules.isUniverse (joinedLevel levels domain codomain) :=
  (levels.join_level (joinedLevel_rule levels domain codomain)).1

noncomputable def rawPi {context : Context rules} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : TypeOver context where
  code := .pi domain.code codomain.code
  level := joinedLevel levels domain codomain
  universeWitness := joinedLevel_universe levels domain codomain
  formed := .piForm domain.formed domain.universeWitness codomain.formed codomain.universeWitness
    (joinedLevel_rule levels domain codomain)

noncomputable def rawSigma {context : Context rules} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : TypeOver context where
  code := .sigma domain.code codomain.code
  level := joinedLevel levels domain codomain
  universeWitness := joinedLevel_universe levels domain codomain
  formed := .sigmaForm domain.formed domain.universeWitness codomain.formed codomain.universeWitness
    (joinedLevel_rule levels domain codomain)

theorem rawPi_reindex {source target : Context rules} (morphism : source ⟶ target)
    (domain : TypeOver target) (codomain : TypeOver (extend target domain)) :
    (rawPi levels domain codomain).reindex morphism =
      rawPi levels (domain.reindex morphism) (codomain.reindex (rawLift morphism domain)) := by
  apply TypeOver.ext
  · rfl
  · rfl

theorem rawSigma_reindex {source target : Context rules} (morphism : source ⟶ target)
    (domain : TypeOver target) (codomain : TypeOver (extend target domain)) :
    (rawSigma levels domain codomain).reindex morphism =
      rawSigma levels (domain.reindex morphism) (codomain.reindex (rawLift morphism domain)) := by
  apply TypeOver.ext
  · rfl
  · rfl

theorem rawPi_typeEquality {context : Context rules} (first second : TypeOver context)
    (sameDomain : TypeEq rules context.raw first.code second.code)
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : TypeEq rules (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code) :
    TypeEq rules context.raw (rawPi levels first firstBody).code (rawPi levels second secondBody).code := by
  rw [extensionComparison_type_code] at sameBody
  obtain ⟨domainLevel, domainUniverse, domainEquality⟩ := sameDomain
  obtain ⟨bodyLevel, bodyUniverse, bodyEquality⟩ := sameBody
  obtain ⟨resultLevel, joined⟩ := levels.join_exists domainUniverse bodyUniverse
  exact ⟨resultLevel, (levels.join_level joined).1,
    .piCong domainEquality domainUniverse bodyEquality bodyUniverse joined⟩

theorem rawSigma_typeEquality {context : Context rules} (first second : TypeOver context)
    (sameDomain : TypeEq rules context.raw first.code second.code)
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : TypeEq rules (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code) :
    TypeEq rules context.raw (rawSigma levels first firstBody).code (rawSigma levels second secondBody).code := by
  rw [extensionComparison_type_code] at sameBody
  obtain ⟨domainLevel, domainUniverse, domainEquality⟩ := sameDomain
  obtain ⟨bodyLevel, bodyUniverse, bodyEquality⟩ := sameBody
  obtain ⟨resultLevel, joined⟩ := levels.join_exists domainUniverse bodyUniverse
  exact ⟨resultLevel, (levels.join_level joined).1,
    .sigmaCong domainEquality domainUniverse bodyEquality bodyUniverse joined⟩

set_option backward.isDefEq.respectTransparency false in
theorem reindexed_body_class {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty levels target)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)) :
    QType.mk levels ((QuotientCwf.typeRepresentative codomain).reindex (nativeLift morphism domain)) =
      QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism domain) := by
  calc
    _ = QuotientCwf.tySub (QType.mk levels (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeLift morphism domain)) := rfl
    _ = _ := by rw [QuotientCwf.typeRepresentative_class, nativeLift_projects]

theorem reindexed_body_equality {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty levels target)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)) :
    TypeEq rules (QuotientCwf.ext source (QuotientCwf.tySub domain morphism)).as.raw
      (subst (liftSub (QuotientCwf.representative morphism).substitution)
        (QuotientCwf.typeRepresentative codomain).code)
      (QuotientCwf.typeRepresentative
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))).code := by
  have same := (QType.mk_eq_iff levels _ _).mp ((reindexed_body_class levels morphism domain codomain).trans
    (QuotientCwf.typeRepresentative_class _).symm)
  change TypeEq rules _ (subst (nativeLift morphism domain).substitution
    (QuotientCwf.typeRepresentative codomain).code) _ at same
  rw [nativeLift_substitution] at same
  exact same

set_option backward.isDefEq.respectTransparency false in
theorem reindexed_body_comparison {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty levels target)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)) :
    TypeEq rules (extend source.as
      ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))).raw
      ((QuotientCwf.typeRepresentative codomain).reindex
        (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain))).code
      ((QuotientCwf.typeRepresentative
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))).reindex
        (extensionComparison
          ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
          (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism))
          (reindexed_domain_equality morphism domain)).hom).code := by
  have same := reindex_typeEquality (reindexed_body_equality levels morphism domain codomain)
    (extensionComparison
      ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism))
      (reindexed_domain_equality morphism domain)).hom
  rw [extensionComparison_hom_substitution, subst_ids] at same
  change TypeEq rules _ _ (subst _ _)
  rw [extensionComparison_hom_substitution]
  exact same

include levels in
theorem rawInstantiation_typeEquality {context : Context rules}
    (first second : TypeOver context) (sameDomain : TypeEq rules context.raw first.code second.code)
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : TypeEq rules (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)
    (left : Term context first) (right : Term context second)
    (sameArgument : Equal rules context.raw left.code right.code first.code) :
    TypeEq rules context.raw (firstBody.reindex (nativeSection left)).code
      (secondBody.reindex (nativeSection right)).code := by
  let converted := right.convertType first sameDomain.symm
  have sections : homTypedEquality rules (nativeSection left) (nativeSection converted) := by
    apply homTypedEquality_pair (homTypedEquality_refl (𝟙 context))
    rw [Term.cast_code, Term.cast_code]
    change Equal rules context.raw left.code right.code (subst ids first.code)
    rw [subst_ids]
    exact sameArgument
  have arguments := (QType.mk_eq_iff levels _ _).mp
    (QType.reindex_congruent (QType.mk levels firstBody) sections)
  rw [extensionComparison_type_code] at sameBody
  have bodies := reindex_typeEquality sameBody (nativeSection converted)
  change TypeEq rules context.raw
    (subst (nativeSection converted).substitution firstBody.code)
    (subst (nativeSection converted).substitution secondBody.code) at bodies
  rw [nativeSection_substitution] at bodies
  change TypeEq rules context.raw (firstBody.reindex (nativeSection left)).code
    (subst (nativeSection converted).substitution firstBody.code) at arguments
  rw [nativeSection_substitution] at arguments
  change TypeEq rules context.raw (subst (subst0 right.code) firstBody.code)
    (subst (subst0 right.code) secondBody.code) at bodies
  change TypeEq rules context.raw _ (subst (nativeSection right).substitution secondBody.code)
  rw [nativeSection_substitution]
  exact arguments.trans levels bodies

set_option backward.isDefEq.respectTransparency false in
theorem body_at_supplied_class {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain))
    (argument : QuotientCwf.Tm levels context domain)
    (actual : Term context.as (QuotientCwf.typeRepresentative domain))
    (same : QTerm.mk levels actual = argument.val) :
    QType.mk levels ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection actual)) =
      QuotientCwf.tySub codomain
        (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels) argument) := by
  calc
    _ = QuotientCwf.tySub (QType.mk levels (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeSection actual)) := rfl
    _ = _ := by rw [QuotientCwf.typeRepresentative_class, nativeSection_projects_of_class argument actual same]

set_option backward.isDefEq.respectTransparency false in
theorem section_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    (argument : QuotientCwf.Tm levels target domain) :
    morphism ≫ Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels) argument =
      Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels)
        (QuotientCwf.tmSub argument morphism) ≫
        Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain := by
  let oldSection := Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels) argument
  let newSection := Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels)
    (QuotientCwf.tmSub argument morphism)
  let lifted := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
    (C := QuotientCwf.cwf levels) morphism domain
  have oldBase : oldSection ≫ QuotientCwf.wk domain = 𝟙 target := QuotientCwf.wk_pair _ _ _
  have newBase : newSection ≫ QuotientCwf.wk (QuotientCwf.tySub domain morphism) = 𝟙 source :=
    QuotientCwf.wk_pair _ _ _
  have liftedBase : lifted ≫ QuotientCwf.wk domain =
      QuotientCwf.wk (QuotientCwf.tySub domain morphism) ≫ morphism :=
    Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution
      (C := QuotientCwf.cwf levels) morphism domain
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
theorem instantiated_type_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain))
    (argument : QuotientCwf.Tm levels target domain) :
    QuotientCwf.tySub
      (QuotientCwf.tySub codomain
        (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels) argument)) morphism =
      QuotientCwf.tySub
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))
        (Mettapedia.TypeTheory.ContextualProductComparison.selfExtend (QuotientCwf.cwf levels)
          (QuotientCwf.tmSub argument morphism)) := by
  rw [← QuotientCwf.tySub_comp, ← QuotientCwf.tySub_comp, section_substitution]

end TypedContextual.DependentTypes
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
