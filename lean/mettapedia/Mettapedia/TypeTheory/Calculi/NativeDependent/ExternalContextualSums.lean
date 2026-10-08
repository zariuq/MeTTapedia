import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualProducts

/-!
# Generated external sums on the contextual quotient

Pairing and projections retain typed component admissions and their Church
annotations. The second projection is indexed by the actual first projection.
Mixed annotation congruence earns substitution across selected type codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Sums

open _root_.CategoryTheory
open DependentTypes QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u
variable {S : Symbols.{u}} {D : Signature S}

def rawPair {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) : Term context (rawSigma domain codomain) where
  code := .pair domain.code codomain.code first.code second.code
  typed := by
    have typed := second.typed
    change Holds D (.term context.raw second.code (codomain.code.substitute (nativeSection first).substitution)) at typed
    rw [nativeSection_substitution] at typed
    exact conclude (.pairIntroduction context.raw domain.code codomain.code first.code second.code)
      ⟨domain.formed, codomain.formed, first.typed, typed, trivial⟩

def rawFst {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (value : Term context (rawSigma domain codomain)) : Term context domain :=
  ⟨.fst domain.code codomain.code value.code,
    conclude (.firstProjection context.raw domain.code codomain.code value.code)
      ⟨domain.formed, codomain.formed, value.typed, trivial⟩⟩

def rawSnd {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (value : Term context (rawSigma domain codomain)) :
    Term context (codomain.reindex (nativeSection (rawFst value))) where
  code := .snd domain.code codomain.code value.code
  typed := by
    change Holds D (.term context.raw _ (codomain.code.substitute (nativeSection (rawFst value)).substitution))
    rw [nativeSection_substitution]
    exact conclude (.secondProjection context.raw domain.code codomain.code value.code)
      ⟨domain.formed, codomain.formed, value.typed, trivial⟩

theorem rawFst_congruent {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first second : Term context (rawSigma domain codomain))
    (same : Holds D (.termEq context.raw first.code second.code (rawSigma domain codomain).code)) :
    QTerm.mk (rawFst first) = QTerm.mk (rawFst second) :=
  (QTerm.mk_eq_iff _ _).mpr ⟨typeEquality_refl _,
    conclude (.firstCongruence context.raw domain.code codomain.code first.code second.code)
      ⟨domain.formed, codomain.formed, same, trivial⟩⟩

theorem rawSnd_congruent {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first second : Term context (rawSigma domain codomain))
    (same : Holds D (.termEq context.raw first.code second.code (rawSigma domain codomain).code)) :
    QTerm.mk (rawSnd first) = QTerm.mk (rawSnd second) := by
  have firsts := ((QTerm.mk_eq_iff _ _).mp (rawFst_congruent first second same)).2
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨rawInstantiation_typeEquality domain domain (typeEquality_refl domain) codomain codomain
    (by rw [extensionComparison_type_code]; exact typeEquality_refl _) _ _ firsts, ?_⟩
  change Holds D (.termEq context.raw _ _ (codomain.code.substitute (nativeSection (rawFst first)).substitution))
  rw [nativeSection_substitution]
  exact conclude (.secondCongruence context.raw domain.code codomain.code first.code second.code)
    ⟨domain.formed, codomain.formed, same, trivial⟩

theorem rawPair_congruent {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (left right : Term context domain)
    (leftSecond : Term context (codomain.reindex (nativeSection left)))
    (rightSecond : Term context (codomain.reindex (nativeSection right)))
    (firsts : Holds D (.termEq context.raw left.code right.code domain.code))
    (seconds : Holds D (.termEq context.raw leftSecond.code rightSecond.code
      (codomain.reindex (nativeSection left)).code)) :
    QTerm.mk (rawPair left leftSecond) = QTerm.mk (rawPair right rightSecond) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl _, ?_⟩
  have typed := rightSecond.typed
  change Holds D (.term context.raw _ (codomain.code.substitute (nativeSection right).substitution)) at typed
  change Holds D (.termEq context.raw _ _ (codomain.code.substitute (nativeSection left).substitution)) at seconds
  rw [nativeSection_substitution] at typed seconds
  exact conclude (.pairCongruence context.raw domain.code codomain.code left.code right.code
    leftSecond.code rightSecond.code) ⟨domain.formed, codomain.formed, firsts, seconds, typed, trivial⟩

theorem rawPair_compared {context : Context D}
    (first second : TypeOver context) (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (left : Term context first) (right : Term context second)
    (leftSecond : Term context (firstBody.reindex (nativeSection left)))
    (rightSecond : Term context (secondBody.reindex (nativeSection right)))
    (firsts : Holds D (.termEq context.raw left.code right.code first.code))
    (seconds : Holds D (.termEq context.raw leftSecond.code rightSecond.code
      (firstBody.reindex (nativeSection left)).code)) :
    QTerm.mk (rawPair left leftSecond) = QTerm.mk (rawPair right rightSecond) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨rawSigma_typeEquality _ _ sameDomain _ _ sameBody, ?_⟩
  rw [extensionComparison_type_code] at sameBody
  have typed := rightSecond.typed
  change Holds D (.term context.raw _ (secondBody.code.substitute (nativeSection right).substitution)) at typed
  change Holds D (.termEq context.raw _ _ (firstBody.code.substitute (nativeSection left).substitution)) at seconds
  rw [nativeSection_substitution] at typed seconds
  exact conclude (.pairAnnotationCongruence context.raw first.code second.code firstBody.code secondBody.code
    left.code right.code leftSecond.code rightSecond.code)
    ⟨sameDomain, sameBody, secondBody.formed, firsts, seconds, right.typed, typed, trivial⟩

theorem rawFst_compared {context : Context D}
    (first second : TypeOver context) (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (left : Term context (rawSigma first firstBody)) (right : Term context (rawSigma second secondBody))
    (values : Holds D (.termEq context.raw left.code right.code (rawSigma first firstBody).code)) :
    QTerm.mk (rawFst left) = QTerm.mk (rawFst right) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨sameDomain, ?_⟩
  rw [extensionComparison_type_code] at sameBody
  exact conclude (.firstAnnotationCongruence context.raw first.code second.code firstBody.code secondBody.code
    left.code right.code) ⟨sameDomain, sameBody, secondBody.formed, values, right.typed, trivial⟩

theorem rawSnd_compared {context : Context D}
    (first second : TypeOver context) (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (left : Term context (rawSigma first firstBody)) (right : Term context (rawSigma second secondBody))
    (values : Holds D (.termEq context.raw left.code right.code (rawSigma first firstBody).code)) :
    QTerm.mk (rawSnd left) = QTerm.mk (rawSnd right) := by
  have firsts := ((QTerm.mk_eq_iff _ _).mp (rawFst_compared _ _ sameDomain _ _ sameBody left right values)).2
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨rawInstantiation_typeEquality _ _ sameDomain _ _ sameBody _ _ firsts, ?_⟩
  rw [extensionComparison_type_code] at sameBody
  change Holds D (.termEq context.raw _ _ (firstBody.code.substitute (nativeSection (rawFst left)).substitution))
  rw [nativeSection_substitution]
  exact conclude (.secondAnnotationCongruence context.raw first.code second.code firstBody.code secondBody.code
    left.code right.code) ⟨sameDomain, sameBody, secondBody.formed, values, right.typed, trivial⟩

theorem rawFstBeta {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    QTerm.mk (rawFst (rawPair first second)) = QTerm.mk first := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl _, ?_⟩
  have typed := second.typed
  change Holds D (.term context.raw _ (codomain.code.substitute (nativeSection first).substitution)) at typed
  rw [nativeSection_substitution] at typed
  exact conclude (.sigmaFirstBeta context.raw domain.code codomain.code first.code second.code)
    ⟨domain.formed, codomain.formed, first.typed, typed, trivial⟩

theorem rawSndBeta {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    QTerm.mk (rawSnd (rawPair first second)) = QTerm.mk second := by
  have firsts := ((QTerm.mk_eq_iff _ _).mp (rawFstBeta first second)).2
  have annotations := rawInstantiation_typeEquality domain domain (typeEquality_refl domain) codomain codomain
    (by rw [extensionComparison_type_code]; exact typeEquality_refl _) _ _ firsts
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨annotations, ?_⟩
  have typed := second.typed
  change Holds D (.term context.raw _ (codomain.code.substitute (nativeSection first).substitution)) at typed
  rw [nativeSection_substitution] at typed
  have computed := conclude (.sigmaSecondBeta context.raw domain.code codomain.code first.code second.code)
    ⟨domain.formed, codomain.formed, first.typed, typed, trivial⟩
  have retyped := typeEquality_symm annotations
  change Holds D (.typeEq context.raw (codomain.code.substitute (nativeSection first).substitution) _) at retyped
  rw [nativeSection_substitution] at retyped
  exact termEquality_convert computed retyped

theorem rawEta {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (value : Term context (rawSigma domain codomain)) :
    QTerm.mk (rawPair (rawFst value) (rawSnd value)) = QTerm.mk value :=
  (QTerm.mk_eq_iff _ _).mpr ⟨typeEquality_refl _,
    conclude (.sigmaEta context.raw domain.code codomain.code value.code)
      ⟨domain.formed, codomain.formed, value.typed, trivial⟩⟩

noncomputable def sigma {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) : QuotientCwf.Ty context :=
  QType.mk (rawSigma (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative codomain))

noncomputable def componentRepresentative {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) first))) :
    Term context.as ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection (chosenTerm first))) :=
  QuotientCwf.termRepresentative _ second.val (second.property.trans (type_at_argument codomain first).symm)

theorem componentRepresentative_class {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) first))) :
    QTerm.mk (componentRepresentative first second) = second.val :=
  QuotientCwf.termRepresentative_class _ _ _

noncomputable def pair {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) first))) :
    QuotientCwf.Tm context (sigma domain codomain) :=
  ⟨QTerm.mk (rawPair (chosenTerm first) (componentRepresentative first second)), rfl⟩

noncomputable def pairRepresentative {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) :
    Term context.as (rawSigma (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain)) :=
  QuotientCwf.termRepresentative _ value.val value.property

theorem pairRepresentative_class {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) :
    QTerm.mk (pairRepresentative value) = value.val :=
  QuotientCwf.termRepresentative_class _ _ _

noncomputable def fst {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) : QuotientCwf.Tm context domain :=
  ⟨QTerm.mk (rawFst (pairRepresentative value)), QuotientCwf.typeRepresentative_class domain⟩

noncomputable def snd {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) : QuotientCwf.Tm context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) (fst value))) :=
  ⟨QTerm.mk (rawSnd (pairRepresentative value)),
    body_at_supplied_class codomain (fst value) (rawFst (pairRepresentative value)) rfl⟩

noncomputable def operations (D : Signature S) : SigmaOperations (QuotientCwf.cwf D) where
  sigma := sigma
  pair := pair
  fst := fst
  snd := snd

theorem fst_pair {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) first))) :
    fst (pair first second) = first := by
  apply Subtype.ext
  have values := (QTerm.mk_eq_iff _ _).mp (pairRepresentative_class (pair first second))
  exact (rawFst_congruent _ _ values.2).trans
    ((rawFstBeta (chosenTerm first) (componentRepresentative first second)).trans (chosenTerm_class first))

theorem snd_pair {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (first : QuotientCwf.Tm context domain)
    (second : QuotientCwf.Tm context
      (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) first))) :
    HEq (snd (pair first second)) second := by
  apply heq_of_value
  have values := (QTerm.mk_eq_iff _ _).mp (pairRepresentative_class (pair first second))
  exact (rawSnd_congruent _ _ values.2).trans
    ((rawSndBeta (chosenTerm first) (componentRepresentative first second)).trans
      (componentRepresentative_class first second))

theorem beta : SigmaBeta (operations D) := ⟨fst_pair, snd_pair⟩

theorem eta {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (value : QuotientCwf.Tm context (sigma domain codomain)) :
    pair (fst value) (snd value) = value := by
  apply Subtype.ext
  let original := pairRepresentative value
  let first := chosenTerm (fst value)
  let second := componentRepresentative (fst value) (snd value)
  have firsts := (QTerm.mk_eq_iff _ _).mp (chosenTerm_class (fst value))
  have seconds := (QTerm.mk_eq_iff _ _).mp
    (componentRepresentative_class (fst value) (snd value))
  have pairs : QTerm.mk (rawPair first second) =
      QTerm.mk (rawPair (rawFst original) (rawSnd original)) :=
    rawPair_congruent _ _ _ _ firsts.2 seconds.2
  exact pairs.trans ((rawEta original).trans (pairRepresentative_class value))

theorem formation_substitution : StrictSigmaFormationSubstitution (operations D) := by
  intro source target morphism domain codomain
  change QuotientCwf.tySub (sigma domain codomain) morphism = _
  rw [← QuotientCwf.represented_type_reindex (sigma domain codomain) morphism]
  have annotation : QType.mk (QuotientCwf.typeRepresentative (sigma domain codomain)) =
      QType.mk (rawSigma (QuotientCwf.typeRepresentative domain)
        (QuotientCwf.typeRepresentative codomain)) := QuotientCwf.typeRepresentative_class _
  have reindexed := congrArg (fun type => QType.reindex type (QuotientCwf.representative morphism)) annotation
  rw [QType.reindex_mk, QType.reindex_mk, rawSigma_reindex] at reindexed
  apply reindexed.trans
  apply (QType.mk_eq_iff _ _).mpr
  exact rawSigma_typeEquality _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison morphism domain codomain)

theorem rawPair_reindex {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)}
    (first : Term target domain) (second : Term target (codomain.reindex (nativeSection first))) :
    ((rawPair first second).reindex morphism).cast (rawSigma_reindex morphism domain codomain) =
      rawPair (first.reindex morphism)
        ((second.reindex morphism).cast (Products.rawInstantiation_reindex morphism codomain first)) := by
  apply Term.ext
  rw [Term.cast_code]
  change (.pair domain.code codomain.code first.code second.code : TermExpr S _).substitute morphism.substitution =
    .pair (domain.code.substitute morphism.substitution)
      (codomain.code.substitute (rawLift morphism domain).substitution) (first.code.substitute morphism.substitution)
      ((second.reindex morphism).cast (Products.rawInstantiation_reindex morphism codomain first)).code
  rw [Term.cast_code, rawLift_substitution]
  rfl

theorem rawFst_reindex {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)} (value : Term target (rawSigma domain codomain)) :
    (rawFst value).reindex morphism =
      rawFst ((value.reindex morphism).cast (rawSigma_reindex morphism domain codomain)) := by
  apply Term.ext
  change (.fst domain.code codomain.code value.code : TermExpr S _).substitute morphism.substitution =
    .fst (domain.code.substitute morphism.substitution)
      (codomain.code.substitute (rawLift morphism domain).substitution)
      ((value.reindex morphism).cast (rawSigma_reindex morphism domain codomain)).code
  rw [Term.cast_code, rawLift_substitution]
  rfl

theorem rawSnd_result_reindex {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)} (value : Term target (rawSigma domain codomain)) :
    (codomain.reindex (nativeSection (rawFst value))).reindex morphism =
      (codomain.reindex (rawLift morphism domain)).reindex
        (nativeSection (rawFst ((value.reindex morphism).cast (rawSigma_reindex morphism domain codomain)))) :=
  (Products.rawInstantiation_reindex morphism codomain (rawFst value)).trans
    (congrArg (fun argument => (codomain.reindex (rawLift morphism domain)).reindex (nativeSection argument))
      (rawFst_reindex morphism value))

theorem rawSnd_reindex {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} {codomain : TypeOver (extend target domain)} (value : Term target (rawSigma domain codomain)) :
    ((rawSnd value).reindex morphism).cast (rawSnd_result_reindex morphism value) =
      rawSnd ((value.reindex morphism).cast (rawSigma_reindex morphism domain codomain)) := by
  apply Term.ext
  rw [Term.cast_code]
  change (.snd domain.code codomain.code value.code : TermExpr S _).substitute morphism.substitution =
    .snd (domain.code.substitute morphism.substitution)
      (codomain.code.substitute (rawLift morphism domain).substitution)
      ((value.reindex morphism).cast (rawSigma_reindex morphism domain codomain)).code
  rw [Term.cast_code, rawLift_substitution]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pair_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target)
    {domain : QuotientCwf.Ty target} {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)}
    (first : QuotientCwf.Tm target domain)
    (second : QuotientCwf.Tm target (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) first)))
    (reindexedSecond : QuotientCwf.Tm source (QuotientCwf.tySub
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain)) (selfExtend (QuotientCwf.cwf D) (QuotientCwf.tmSub first morphism))))
    (sameSecond : HEq (QuotientCwf.tmSub second morphism) reindexedSecond) :
    HEq (QuotientCwf.tmSub (pair first second) morphism) (pair (QuotientCwf.tmSub first morphism) reindexedSecond) := by
  apply heq_of_value
  let oldFirst := chosenTerm first
  let oldSecond := componentRepresentative first second
  let newFirst := oldFirst.reindex (QuotientCwf.representative morphism)
  let newSecond := (oldSecond.reindex (QuotientCwf.representative morphism)).cast
    (Products.rawInstantiation_reindex (QuotientCwf.representative morphism) _ oldFirst)
  have firsts := (QTerm.mk_eq_iff _ _).mp
    ((Products.supplied_reindex_class morphism first oldFirst (chosenTerm_class first)).trans
      (chosenTerm_class (QuotientCwf.tmSub first morphism)).symm)
  have seconds := (QTerm.mk_eq_iff newSecond (componentRepresentative (QuotientCwf.tmSub first morphism) reindexedSecond)).mp
    ((QTerm.mk_cast _ _).trans ((Products.supplied_reindex_class morphism second oldSecond
      (componentRepresentative_class first second)).trans
        ((heq_value (instantiated_type_substitution morphism codomain first) sameSecond).trans
          (componentRepresentative_class (QuotientCwf.tmSub first morphism) reindexedSecond).symm)))
  have compared := rawPair_compared _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison morphism domain codomain) newFirst (chosenTerm (QuotientCwf.tmSub first morphism))
    newSecond (componentRepresentative (QuotientCwf.tmSub first morphism) reindexedSecond) firsts.2 seconds.2
  have actual := Products.supplied_reindex_class morphism (pair first second) (rawPair oldFirst oldSecond) rfl
  exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
    ((congrArg QTerm.mk (rawPair_reindex (QuotientCwf.representative morphism) oldFirst oldSecond)).trans compared))

set_option backward.isDefEq.respectTransparency false in
theorem projection_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target)
    {domain : QuotientCwf.Ty target} {codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)}
    (value : QuotientCwf.Tm target (sigma domain codomain))
    (reindexedValue : QuotientCwf.Tm source (sigma (QuotientCwf.tySub domain morphism)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain))))
    (sameValue : HEq (QuotientCwf.tmSub value morphism) reindexedValue) :
    HEq (QuotientCwf.tmSub (fst value) morphism) (fst reindexedValue) ∧
      HEq (QuotientCwf.tmSub (snd value) morphism) (snd reindexedValue) := by
  let oldValue := pairRepresentative value
  let newValue := (oldValue.reindex (QuotientCwf.representative morphism)).cast
    (rawSigma_reindex (QuotientCwf.representative morphism) _ _)
  let actualValue := pairRepresentative reindexedValue
  have values := (QTerm.mk_eq_iff newValue actualValue).mp
    ((QTerm.mk_cast _ _).trans ((Products.supplied_reindex_class morphism value oldValue
      (pairRepresentative_class value)).trans
        ((heq_value (formation_substitution morphism domain codomain) sameValue).trans
          (pairRepresentative_class reindexedValue).symm)))
  have firsts := rawFst_compared _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison morphism domain codomain) newValue actualValue values.2
  have seconds := rawSnd_compared _ _ (reindexed_domain_equality morphism domain) _ _
    (reindexed_body_comparison morphism domain codomain) newValue actualValue values.2
  constructor
  · apply heq_of_value
    have actual := Products.supplied_reindex_class morphism (fst value) (rawFst oldValue) rfl
    exact actual.symm.trans ((congrArg QTerm.mk (rawFst_reindex (QuotientCwf.representative morphism) oldValue)).trans firsts)
  · apply heq_of_value
    have actual := Products.supplied_reindex_class morphism (snd value) (rawSnd oldValue) rfl
    exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
      ((congrArg QTerm.mk (rawSnd_reindex (QuotientCwf.representative morphism) oldValue)).trans seconds))

theorem substitution : StrictSigmaSubstitution (operations D) :=
  ⟨formation_substitution, pair_substitution, projection_substitution⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Sums
