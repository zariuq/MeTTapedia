import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualProducts

/-!
# Dependent pairs on the typed contextual quotient

Pairing and both projections use the actual typed pair rules. Supplied
components are retyped at the selected domain and its instantiated codomain.
The second projection retains its dependency on the first projection, and
beta and eta are equations of complete annotated term classes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual.Sums

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization
open TypedContextual.DependentTypes TypedContextual.QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

noncomputable def rawPair {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    Term context (rawSigma levels domain codomain) where
  code := .pair first.code second.code
  typed := by
    have typed := second.typed
    change Typed rules context.raw second.code (subst (nativeSection first).substitution codomain.code) at typed
    rw [nativeSection_substitution] at typed
    exact .pairIntro (rawSigma levels domain codomain).formed
      (rawSigma levels domain codomain).universeWitness first.typed typed

noncomputable def rawFst {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (value : Term context (rawSigma levels domain codomain)) : Term context domain :=
  ⟨.fst value.code, .fstElim value.typed⟩

noncomputable def rawSnd {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (value : Term context (rawSigma levels domain codomain)) :
    Term context (codomain.reindex (nativeSection (rawFst levels value))) where
  code := .snd value.code
  typed := by
    change Typed rules context.raw (.snd value.code)
      (subst (nativeSection (rawFst levels value)).substitution codomain.code)
    rw [nativeSection_substitution]
    exact .sndElim value.typed

theorem rawFst_congruent {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (first second : Term context (rawSigma levels domain codomain))
    (same : Equal rules context.raw first.code second.code (rawSigma levels domain codomain).code) :
    QTerm.mk levels (rawFst levels first) = QTerm.mk levels (rawFst levels second) :=
  (QTerm.mk_eq_iff levels _ _).mpr ⟨domain.isType.refl, .fstCong same⟩

theorem rawSnd_congruent {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (first second : Term context (rawSigma levels domain codomain))
    (same : Equal rules context.raw first.code second.code (rawSigma levels domain codomain).code) :
    QTerm.mk levels (rawSnd levels first) = QTerm.mk levels (rawSnd levels second) := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  constructor
  · apply rawInstantiation_typeEquality levels domain domain domain.isType.refl codomain codomain
    · rw [extensionComparison_type_code]
      exact codomain.isType.refl
    · exact .fstCong same
  · change Equal rules context.raw (.snd first.code) (.snd second.code)
      (subst (nativeSection (rawFst levels first)).substitution codomain.code)
    rw [nativeSection_substitution]
    exact .sndCong same

theorem rawFstBeta {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    QTerm.mk levels (rawFst levels (rawPair levels first second)) = QTerm.mk levels first := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  refine ⟨domain.isType.refl, ?_⟩
  have typed := second.typed
  change Typed rules context.raw second.code (subst (nativeSection first).substitution codomain.code) at typed
  rw [nativeSection_substitution] at typed
  exact .betaFst (rawSigma levels domain codomain).formed
    (rawSigma levels domain codomain).universeWitness first.typed typed

theorem rawSndBeta {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    QTerm.mk levels (rawSnd levels (rawPair levels first second)) = QTerm.mk levels second := by
  have firsts := ((QTerm.mk_eq_iff levels _ _).mp (rawFstBeta levels first second)).2
  have annotations := rawInstantiation_typeEquality levels domain domain domain.isType.refl codomain codomain
    (by rw [extensionComparison_type_code]; exact codomain.isType.refl)
    (rawFst levels (rawPair levels first second)) first firsts
  apply (QTerm.mk_eq_iff levels _ _).mpr
  refine ⟨annotations, ?_⟩
  have typed := second.typed
  change Typed rules context.raw second.code (subst (nativeSection first).substitution codomain.code) at typed
  rw [nativeSection_substitution] at typed
  have computed := Derivable.betaSnd (rawSigma levels domain codomain).formed
    (rawSigma levels domain codomain).universeWitness first.typed typed
  have retyped := annotations.symm
  change TypeEq rules context.raw (subst (nativeSection first).substitution codomain.code) _ at retyped
  rw [nativeSection_substitution] at retyped
  exact Equal.convType computed retyped

theorem rawEta {context : Context rules} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)}
    (value : Term context (rawSigma levels domain codomain)) :
    QTerm.mk levels (rawPair levels (rawFst levels value) (rawSnd levels value)) = QTerm.mk levels value := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  refine ⟨(rawSigma levels domain codomain).isType.refl, .symm ?_⟩
  apply Derivable.etaSigma value.typed (rawPair levels (rawFst levels value) (rawSnd levels value)).typed
  · exact .symm ((QTerm.mk_eq_iff levels _ _).mp (rawFstBeta levels (rawFst levels value) (rawSnd levels value))).2
  · have typed := (rawSnd levels value).typed
    change Typed rules context.raw (.snd value.code)
      (subst (nativeSection (rawFst levels value)).substitution codomain.code) at typed
    rw [nativeSection_substitution] at typed
    exact .symm (.betaSnd (rawSigma levels domain codomain).formed
      (rawSigma levels domain codomain).universeWitness (rawFst levels value).typed typed)

noncomputable def sigma {context : QuotientCwf.QContext rules}
    (domain : QuotientCwf.Ty levels context)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)) : QuotientCwf.Ty levels context :=
  QType.mk levels (rawSigma levels (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative codomain))

noncomputable def componentRepresentative {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm levels context domain)
    (second : QuotientCwf.Tm levels context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) first))) :
    Term context.as ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection (chosenTerm first))) :=
  QuotientCwf.termRepresentative _ second.val (second.property.trans (type_at_argument codomain first).symm)

theorem componentRepresentative_class {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm levels context domain)
    (second : QuotientCwf.Tm levels context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) first))) :
    QTerm.mk levels (componentRepresentative levels first second) = second.val :=
  QuotientCwf.termRepresentative_class _ _ _

noncomputable def pair {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm levels context domain)
    (second : QuotientCwf.Tm levels context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) first))) :
    QuotientCwf.Tm levels context (sigma levels domain codomain) :=
  ⟨QTerm.mk levels (rawPair levels (chosenTerm first) (componentRepresentative levels first second)), rfl⟩

noncomputable def pairRepresentative {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm levels context (sigma levels domain codomain)) :
    Term context.as (rawSigma levels (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain)) :=
  QuotientCwf.termRepresentative _ value.val value.property

theorem pairRepresentative_class {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm levels context (sigma levels domain codomain)) :
    QTerm.mk levels (pairRepresentative levels value) = value.val :=
  QuotientCwf.termRepresentative_class _ _ _

noncomputable def fst {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm levels context (sigma levels domain codomain)) : QuotientCwf.Tm levels context domain :=
  ⟨QTerm.mk levels (rawFst levels (pairRepresentative levels value)), QuotientCwf.typeRepresentative_class domain⟩

noncomputable def snd {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm levels context (sigma levels domain codomain)) : QuotientCwf.Tm levels context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) (fst levels value))) :=
  ⟨QTerm.mk levels (rawSnd levels (pairRepresentative levels value)),
    body_at_supplied_class levels codomain (fst levels value) (rawFst levels (pairRepresentative levels value)) rfl⟩

noncomputable def operations : SigmaOperations (QuotientCwf.cwf levels) where
  sigma := sigma levels
  pair := pair levels
  fst := fst levels
  snd := snd levels

theorem fst_pair {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm levels context domain)
    (second : QuotientCwf.Tm levels context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) first))) :
    fst levels (pair levels first second) = first := by
  apply Subtype.ext
  have values := (QTerm.mk_eq_iff levels _ _).mp (pairRepresentative_class levels (pair levels first second))
  exact (rawFst_congruent levels _ _ values.2).trans
    ((rawFstBeta levels (chosenTerm first) (componentRepresentative levels first second)).trans (chosenTerm_class first))

theorem snd_pair {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm levels context domain)
    (second : QuotientCwf.Tm levels context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) first))) :
    HEq (snd levels (pair levels first second)) second := by
  apply heq_of_value
  have values := (QTerm.mk_eq_iff levels _ _).mp (pairRepresentative_class levels (pair levels first second))
  exact (rawSnd_congruent levels _ _ values.2).trans
    ((rawSndBeta levels (chosenTerm first) (componentRepresentative levels first second)).trans
      (componentRepresentative_class levels first second))

theorem beta : SigmaBeta (operations levels) := ⟨fst_pair levels, snd_pair levels⟩

theorem eta {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm levels context (sigma levels domain codomain)) :
    pair levels (fst levels value) (snd levels value) = value := by
  apply Subtype.ext
  let original := pairRepresentative levels value
  let first := chosenTerm (fst levels value)
  let second := componentRepresentative levels (fst levels value) (snd levels value)
  have firsts := (QTerm.mk_eq_iff levels _ _).mp (chosenTerm_class (fst levels value))
  have seconds := (QTerm.mk_eq_iff levels _ _).mp
    (componentRepresentative_class levels (fst levels value) (snd levels value))
  have secondEquality := seconds.2
  change Equal rules context.as.raw second.code (rawSnd levels original).code
    (subst (nativeSection first).substitution (QuotientCwf.typeRepresentative codomain).code) at secondEquality
  rw [nativeSection_substitution] at secondEquality
  have pairs : QTerm.mk levels (rawPair levels first second) =
      QTerm.mk levels (rawPair levels (rawFst levels original) (rawSnd levels original)) := by
    apply (QTerm.mk_eq_iff levels _ _).mpr
    exact ⟨(rawSigma levels _ _).isType.refl,
      .pairCong (rawSigma levels _ _).formed (rawSigma levels _ _).universeWitness firsts.2 secondEquality⟩
  exact pairs.trans ((rawEta levels original).trans (pairRepresentative_class levels value))

theorem formation_substitution : StrictSigmaFormationSubstitution (operations levels) := by
  intro source target morphism domain codomain
  change QuotientCwf.tySub (sigma levels domain codomain) morphism = _
  rw [← QuotientCwf.represented_type_reindex (sigma levels domain codomain) morphism]
  have annotation : QType.mk levels (QuotientCwf.typeRepresentative (sigma levels domain codomain)) =
      QType.mk levels (rawSigma levels (QuotientCwf.typeRepresentative domain)
        (QuotientCwf.typeRepresentative codomain)) := QuotientCwf.typeRepresentative_class _
  have reindexed := congrArg (fun type => QType.reindex type (QuotientCwf.representative morphism)) annotation
  rw [QType.reindex_mk, QType.reindex_mk, rawSigma_reindex] at reindexed
  apply reindexed.trans
  apply (QType.mk_eq_iff levels _ _).mpr
  exact rawSigma_typeEquality levels _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison levels morphism domain codomain)

theorem rawPair_reindex {source target : Context rules} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (first : Term target domain) (second : Term target (codomain.reindex (nativeSection first))) :
    ((rawPair levels first second).reindex morphism).cast (rawSigma_reindex levels morphism domain codomain) =
      rawPair levels (first.reindex morphism)
        ((second.reindex morphism).cast (Products.rawInstantiation_reindex morphism codomain first)) := by
  apply Term.ext
  rw [Term.cast_code]
  change Tm.pair (subst morphism.substitution first.code) (subst morphism.substitution second.code) =
    Tm.pair (first.reindex morphism).code
      ((second.reindex morphism).cast (Products.rawInstantiation_reindex morphism codomain first)).code
  rw [Term.cast_code]
  rfl

theorem rawFst_reindex {source target : Context rules} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (value : Term target (rawSigma levels domain codomain)) :
    (rawFst levels value).reindex morphism =
      rawFst levels ((value.reindex morphism).cast (rawSigma_reindex levels morphism domain codomain)) := by
  apply Term.ext
  change Tm.fst (subst morphism.substitution value.code) =
    Tm.fst ((value.reindex morphism).cast (rawSigma_reindex levels morphism domain codomain)).code
  rw [Term.cast_code]
  rfl

theorem rawSnd_result_reindex {source target : Context rules} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (value : Term target (rawSigma levels domain codomain)) :
    (codomain.reindex (nativeSection (rawFst levels value))).reindex morphism =
      (codomain.reindex (rawLift morphism domain)).reindex
        (nativeSection (rawFst levels ((value.reindex morphism).cast (rawSigma_reindex levels morphism domain codomain)))) :=
  (Products.rawInstantiation_reindex morphism codomain (rawFst levels value)).trans
    (congrArg (fun argument => (codomain.reindex (rawLift morphism domain)).reindex (nativeSection argument))
      (rawFst_reindex levels morphism value))

theorem rawSnd_reindex {source target : Context rules} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (value : Term target (rawSigma levels domain codomain)) :
    ((rawSnd levels value).reindex morphism).cast (rawSnd_result_reindex levels morphism value) =
      rawSnd levels ((value.reindex morphism).cast (rawSigma_reindex levels morphism domain codomain)) := by
  apply Term.ext
  rw [Term.cast_code]
  change Tm.snd (subst morphism.substitution value.code) =
    Tm.snd ((value.reindex morphism).cast (rawSigma_reindex levels morphism domain codomain)).code
  rw [Term.cast_code]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pair_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)}
    (first : QuotientCwf.Tm levels target domain)
    (second : QuotientCwf.Tm levels target (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) first)))
    (reindexedSecond : QuotientCwf.Tm levels source
      (QuotientCwf.tySub (QuotientCwf.tySub codomain
        (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))
        (selfExtend (QuotientCwf.cwf levels) (QuotientCwf.tmSub first morphism))))
    (sameSecond : HEq (QuotientCwf.tmSub second morphism) reindexedSecond) :
    HEq (QuotientCwf.tmSub (pair levels first second) morphism)
      (pair levels (QuotientCwf.tmSub first morphism) reindexedSecond) := by
  apply heq_of_value
  let oldFirst := chosenTerm first
  let oldSecond := componentRepresentative levels first second
  let newFirst := oldFirst.reindex (QuotientCwf.representative morphism)
  let newSecond := (oldSecond.reindex (QuotientCwf.representative morphism)).cast
    (Products.rawInstantiation_reindex (QuotientCwf.representative morphism) _ oldFirst)
  have firsts := (QTerm.mk_eq_iff levels _ _).mp
    ((Products.supplied_reindex_class levels morphism first oldFirst (chosenTerm_class first)).trans
      (chosenTerm_class (QuotientCwf.tmSub first morphism)).symm)
  have seconds := (QTerm.mk_eq_iff levels newSecond
    (componentRepresentative levels (QuotientCwf.tmSub first morphism) reindexedSecond)).mp
    ((QTerm.mk_cast _ _).trans ((Products.supplied_reindex_class levels morphism second oldSecond
      (componentRepresentative_class levels first second)).trans
        ((heq_value (instantiated_type_substitution levels morphism codomain first) sameSecond).trans
          (componentRepresentative_class levels (QuotientCwf.tmSub first morphism) reindexedSecond).symm)))
  have secondEquality := seconds.2
  change Equal rules source.as.raw newSecond.code
    (componentRepresentative levels (QuotientCwf.tmSub first morphism) reindexedSecond).code
    (subst (nativeSection newFirst).substitution
      ((QuotientCwf.typeRepresentative codomain).reindex
        (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain))).code) at secondEquality
  rw [nativeSection_substitution] at secondEquality
  have compared : QTerm.mk levels (rawPair levels newFirst newSecond) =
      (pair levels (QuotientCwf.tmSub first morphism) reindexedSecond).val := by
    apply (QTerm.mk_eq_iff levels _ _).mpr
    constructor
    · exact rawSigma_typeEquality levels _ _ (reindexed_domain_equality morphism domain) _ _
        (reindexed_body_comparison levels morphism domain codomain)
    · exact .pairCong (rawSigma levels _ _).formed (rawSigma levels _ _).universeWitness firsts.2 secondEquality
  have actual := Products.supplied_reindex_class levels morphism (pair levels first second)
    (rawPair levels oldFirst oldSecond) rfl
  exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
    ((congrArg (QTerm.mk levels) (rawPair_reindex levels (QuotientCwf.representative morphism)
      oldFirst oldSecond)).trans compared))

set_option backward.isDefEq.respectTransparency false in
theorem projection_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) {domain : QuotientCwf.Ty levels target}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)}
    (value : QuotientCwf.Tm levels target (sigma levels domain codomain))
    (reindexedValue : QuotientCwf.Tm levels source
      (sigma levels (QuotientCwf.tySub domain morphism)
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))))
    (sameValue : HEq (QuotientCwf.tmSub value morphism) reindexedValue) :
    HEq (QuotientCwf.tmSub (fst levels value) morphism) (fst levels reindexedValue) ∧
      HEq (QuotientCwf.tmSub (snd levels value) morphism) (snd levels reindexedValue) := by
  let oldValue := pairRepresentative levels value
  let newValue := (oldValue.reindex (QuotientCwf.representative morphism)).cast
    (rawSigma_reindex levels (QuotientCwf.representative morphism) _ _)
  let actualValue := pairRepresentative levels reindexedValue
  have values := (QTerm.mk_eq_iff levels newValue actualValue).mp
    ((QTerm.mk_cast _ _).trans ((Products.supplied_reindex_class levels morphism value oldValue
      (pairRepresentative_class levels value)).trans
        ((heq_value (formation_substitution levels morphism domain codomain) sameValue).trans
          (pairRepresentative_class levels reindexedValue).symm)))
  have firsts : QTerm.mk levels (rawFst levels newValue) = QTerm.mk levels (rawFst levels actualValue) :=
    (QTerm.mk_eq_iff levels _ _).mpr ⟨reindexed_domain_equality morphism domain, .fstCong values.2⟩
  have seconds : QTerm.mk levels (rawSnd levels newValue) = QTerm.mk levels (rawSnd levels actualValue) := by
    apply (QTerm.mk_eq_iff levels _ _).mpr
    constructor
    · exact rawInstantiation_typeEquality levels _ _ (reindexed_domain_equality morphism domain) _ _
        (reindexed_body_comparison levels morphism domain codomain)
        (rawFst levels newValue) (rawFst levels actualValue) (.fstCong values.2)
    · change Equal rules source.as.raw (.snd newValue.code) (.snd actualValue.code)
        (subst (nativeSection (rawFst levels newValue)).substitution
          ((QuotientCwf.typeRepresentative codomain).reindex
            (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain))).code)
      rw [nativeSection_substitution]
      exact .sndCong values.2
  constructor
  · apply heq_of_value
    have actual := Products.supplied_reindex_class levels morphism (fst levels value)
      (rawFst levels oldValue) rfl
    exact actual.symm.trans ((congrArg (QTerm.mk levels)
      (rawFst_reindex levels (QuotientCwf.representative morphism) oldValue)).trans firsts)
  · apply heq_of_value
    have actual := Products.supplied_reindex_class levels morphism (snd levels value)
      (rawSnd levels oldValue) rfl
    exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
      ((congrArg (QTerm.mk levels) (rawSnd_reindex levels (QuotientCwf.representative morphism) oldValue)).trans seconds))

theorem substitution : StrictSigmaSubstitution (operations levels) :=
  ⟨formation_substitution levels, pair_substitution levels, projection_substitution levels⟩

noncomputable def qualified : Mettapedia.TypeTheory.ContextualSumComparison.DependentSumBeta
    (QuotientCwf.cwf levels) where
  sigma := sigma levels
  pair := pair levels
  fst := fst levels
  snd := snd levels
  fst_pair := fst_pair levels
  snd_pair := snd_pair levels

end TypedContextual.Sums
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
