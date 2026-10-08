import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualSumElimination
import Mettapedia.TypeTheory.ContextualSumPairReadout

/-!
# Authored full-motive sum elimination and contextual comprehension

The component context is packed by the actual authored pair constructor. Its
substitution retains the two component positions and every older variable.
The comparison uses complete term classes, typed annotation transport and the
earned context isomorphism of the stable sum operations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SigmaEliminationComparison

open _root_.CategoryTheory
open DependentTypes QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u
variable {S : Symbols.{u}} {D : Signature S}

abbrev rawTuple {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : Context D :=
  extend (extend context domain) codomain

def rawTupleBase {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : rawTuple domain codomain ⟶ context :=
  projectionHom (extend context domain) codomain ≫ projectionHom context domain

theorem rawTupleBase_substitution {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    (rawTupleBase domain codomain).substitution = fun index => .var index.succ.succ := rfl

def rawFirst {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    Term (rawTuple domain codomain) (domain.reindex (rawTupleBase domain codomain)) :=
  ((newest context domain).reindex (projectionHom (extend context domain) codomain)).cast
    (domain.reindex_comp (projectionHom (extend context domain) codomain)
      (projectionHom context domain)).symm

set_option backward.isDefEq.respectTransparency false in
theorem rawFirst_code {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : (rawFirst domain codomain).code = .var 1 := by
  rw [rawFirst, Term.cast_code]
  rfl

theorem rawSecond_annotation {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    (codomain.reindex (rawLift (rawTupleBase domain codomain) domain)).reindex
      (nativeSection (rawFirst domain codomain)) =
        codomain.reindex (projectionHom (extend context domain) codomain) := by
  apply TypeOver.ext
  change (codomain.code.substitute (rawLift (rawTupleBase domain codomain) domain).substitution).substitute
    (nativeSection (rawFirst domain codomain)).substitution = codomain.code.substitute (fun index => .var index.succ)
  rw [rawLift_substitution, nativeSection_substitution, rawFirst_code, rawTupleBase_substitution,
    liftSubstitution_variables, TypeExpr.substitute_variables, TypeExpr.substitute_variables]
  exact genericPair_body codomain.code

def rawSecond {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    Term (rawTuple domain codomain)
      ((codomain.reindex (rawLift (rawTupleBase domain codomain) domain)).reindex
        (nativeSection (rawFirst domain codomain))) :=
  (newest (extend context domain) codomain).cast (rawSecond_annotation domain codomain).symm

theorem rawSecond_code {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : (rawSecond domain codomain).code = .var 0 := by
  rw [rawSecond, Term.cast_code]
  rfl

def rawGenericPair {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    Term (rawTuple domain codomain) ((rawSigma domain codomain).reindex (rawTupleBase domain codomain)) :=
  (Sums.rawPair (rawFirst domain codomain) (rawSecond domain codomain)).cast
    (rawSigma_reindex (rawTupleBase domain codomain) domain codomain).symm

set_option backward.isDefEq.respectTransparency false in
theorem rawGenericPair_code {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    (rawGenericPair domain codomain).code = genericPair domain.code codomain.code := by
  rw [rawGenericPair, Term.cast_code]
  change TermExpr.pair (domain.code.substitute (rawTupleBase domain codomain).substitution)
    (codomain.code.substitute (rawLift (rawTupleBase domain codomain) domain).substitution)
    (rawFirst domain codomain).code (rawSecond domain codomain).code = _
  rw [rawTupleBase_substitution, rawLift_substitution, rawTupleBase_substitution,
    liftSubstitution_variables, TypeExpr.substitute_variables, TypeExpr.substitute_variables,
    rawFirst_code, rawSecond_code]
  rfl

def rawPack {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    rawTuple domain codomain ⟶ extend context (rawSigma domain codomain) :=
  Contextual.pair (rawTupleBase domain codomain) (rawGenericPair domain codomain)

theorem rawPack_substitution {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    (rawPack domain codomain).substitution = packSubstitution domain.code codomain.code := by
  change extendSubstitution (rawTupleBase domain codomain).substitution
    (rawGenericPair domain codomain).code = _
  rw [rawTupleBase_substitution, rawGenericPair_code]
  rfl

theorem rawPack_projection {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    rawPack domain codomain ≫ projectionHom context (rawSigma domain codomain) =
      rawTupleBase domain codomain := Contextual.pair_projection _ _

def rawComponents {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) : context ⟶ rawTuple domain codomain :=
  Contextual.pair (nativeSection first) second

theorem rawComponents_substitution {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    (rawComponents first second).substitution = instantiateComponents first.code second.code := by
  change extendSubstitution (nativeSection first).substitution second.code = _
  rw [nativeSection_substitution]
  rfl

theorem rawComponents_packing {context : Context D} {domain : TypeOver context}
    {codomain : TypeOver (extend context domain)} (first : Term context domain)
    (second : Term context (codomain.reindex (nativeSection first))) :
    rawComponents first second ≫ rawPack domain codomain = nativeSection (Sums.rawPair first second) := by
  apply Hom.ext
  change composeSubstitution (rawPack domain codomain).substitution
    (rawComponents first second).substitution = (nativeSection (Sums.rawPair first second)).substitution
  rw [rawComponents_substitution, rawPack_substitution, nativeSection_substitution]
  exact packSubstitution_instantiate domain.code codomain.code first.code second.code

def rawEliminate {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain))
    (motive : TypeOver (extend context (rawSigma domain codomain)))
    (body : Term (rawTuple domain codomain) (motive.reindex (rawPack domain codomain)))
    (value : Term context (rawSigma domain codomain)) :
    Term context (motive.reindex (nativeSection value)) where
  code := .sigmaElim domain.code codomain.code motive.code body.code value.code
  typed := by
    have branch := body.typed
    change Holds D (.term (rawTuple domain codomain).raw body.code
      (motive.code.substitute (rawPack domain codomain).substitution)) at branch
    rw [rawPack_substitution] at branch
    change Holds D (.term context.raw _ (motive.code.substitute (nativeSection value).substitution))
    rw [nativeSection_substitution]
    exact conclude (.sigmaElimination context.raw domain.code codomain.code motive.code body.code value.code)
      ⟨domain.formed, codomain.formed, motive.formed, branch, value.typed, trivial⟩

theorem rawEliminate_beta {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain))
    (motive : TypeOver (extend context (rawSigma domain codomain)))
    (body : Term (rawTuple domain codomain) (motive.reindex (rawPack domain codomain)))
    (first : Term context domain) (second : Term context (codomain.reindex (nativeSection first))) :
    QTerm.mk (rawEliminate domain codomain motive body (Sums.rawPair first second)) =
      QTerm.mk (body.reindex (rawComponents first second)) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  constructor
  · rw [← TypeOver.reindex_comp, rawComponents_packing]
    exact typeEquality_refl _
  · have branch := body.typed
    change Holds D (.term (rawTuple domain codomain).raw body.code
      (motive.code.substitute (rawPack domain codomain).substitution)) at branch
    rw [rawPack_substitution] at branch
    have secondTyped := second.typed
    change Holds D (.term context.raw second.code (codomain.code.substitute (nativeSection first).substitution)) at secondTyped
    rw [nativeSection_substitution] at secondTyped
    change Holds D (.termEq context.raw _ (body.code.substitute (rawComponents first second).substitution)
      (motive.code.substitute (nativeSection (Sums.rawPair first second)).substitution))
    rw [nativeSection_substitution, rawComponents_substitution]
    exact conclude (.sigmaEliminationBeta context.raw domain.code codomain.code motive.code body.code
      first.code second.code) ⟨domain.formed, codomain.formed, motive.formed, branch, first.typed, secondTyped, trivial⟩

theorem rawEliminate_branch_congruence {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain))
    (motive : TypeOver (extend context (rawSigma domain codomain)))
    (first second : Term (rawTuple domain codomain) (motive.reindex (rawPack domain codomain)))
    (same : QTerm.mk first = QTerm.mk second) (value : Term context (rawSigma domain codomain)) :
    QTerm.mk (rawEliminate domain codomain motive first value) =
      QTerm.mk (rawEliminate domain codomain motive second value) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl _, ?_⟩
  have branch := ((QTerm.mk_eq_iff _ _).mp same).2
  change Holds D (.termEq (rawTuple domain codomain).raw first.code second.code
    (motive.code.substitute (rawPack domain codomain).substitution)) at branch
  rw [rawPack_substitution] at branch
  change Holds D (.termEq context.raw _ _ (motive.code.substitute (nativeSection value).substitution))
  rw [nativeSection_substitution]
  exact conclude (.sigmaEliminationCongruence context.raw domain.code codomain.code motive.code
    first.code second.code value.code value.code)
    ⟨domain.formed, codomain.formed, motive.formed, branch, termEquality_refl value, trivial⟩

theorem rawEliminate_section_eta {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain))
    (motive : TypeOver (extend context (rawSigma domain codomain)))
    (term : Term (extend context (rawSigma domain codomain)) motive)
    (value : Term context (rawSigma domain codomain)) :
    QTerm.mk (rawEliminate domain codomain motive (term.reindex (rawPack domain codomain)) value) =
      QTerm.mk (term.reindex (nativeSection value)) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨typeEquality_refl _, ?_⟩
  change Holds D (.termEq context.raw
    (.sigmaElim domain.code codomain.code motive.code
      (term.code.substitute (rawPack domain codomain).substitution) value.code)
    (term.code.substitute (nativeSection value).substitution)
    (motive.code.substitute (nativeSection value).substitution))
  rw [rawPack_substitution, nativeSection_substitution]
  exact conclude (.sigmaEliminationEta context.raw domain.code codomain.code motive.code term.code value.code)
    ⟨domain.formed, codomain.formed, motive.formed, term.typed, value.typed, trivial⟩

theorem supplied_domain_equality {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target) :
    Holds D (.typeEq source.as.raw
      ((QuotientCwf.typeRepresentative domain).reindex morphism).code
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism))).code) := by
  apply (QType.mk_eq_iff _ _).mp
  exact (congrArg (fun type => type.reindex morphism) (QuotientCwf.typeRepresentative_class domain)).trans
    (QuotientCwf.typeRepresentative_class _).symm

noncomputable def suppliedLift {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target) :
    (QuotientCwf.ext source (QuotientCwf.tySub domain (QuotientCwf.project morphism))).as ⟶
      (QuotientCwf.ext target domain).as :=
  convertedLift morphism (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism)))
    (supplied_domain_equality morphism domain)

theorem suppliedLift_substitution {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target) :
    (suppliedLift morphism domain).substitution = liftSubstitution morphism.substitution :=
  convertedLift_substitution _ _ _ _

theorem suppliedLift_projection {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target) :
    suppliedLift morphism domain ≫ projectionHom target.as (QuotientCwf.typeRepresentative domain) =
      projectionHom source.as
        (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism))) ≫ morphism := by
  apply Hom.ext
  change composeSubstitution (fun index => .var index.succ) (suppliedLift morphism domain).substitution =
    composeSubstitution morphism.substitution (fun index => .var index.succ)
  rw [suppliedLift_substitution]
  funext index
  exact (TermExpr.substitute_variables _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem suppliedLift_newest {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target) :
    QTerm.mk ((newest target.as (QuotientCwf.typeRepresentative domain)).reindex (suppliedLift morphism domain)) =
      QTerm.mk (newest source.as
        (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism)))) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  constructor
  · change Holds D (.typeEq _
      (((QuotientCwf.typeRepresentative domain).code.substitute (fun index => .var index.succ)).substitute
        (suppliedLift morphism domain).substitution)
      ((QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism))).code.substitute
        (fun index => .var index.succ)))
    rw [suppliedLift_substitution, TypeExpr.substitute_variables, TypeExpr.substitute_variables,
      TypeExpr.substitute_weaken]
    change Holds D (.typeEq (extend source.as
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism)))).raw _ _)
    simpa only [projectionHom, TypeOver.reindex, TypeExpr.substitute_variables] using
      reindex_typeEquality (supplied_domain_equality morphism domain)
        (projectionHom source.as
          (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism))))
  · let left := (newest target.as (QuotientCwf.typeRepresentative domain)).reindex (suppliedLift morphism domain)
    have sameCode : left.code = TermExpr.var (0 : Fin (source.as.arity + 1)) := by
      change (.var (0 : Fin (target.as.arity + 1)) : TermExpr S _).substitute
        (suppliedLift morphism domain).substitution = _
      rw [suppliedLift_substitution]
      rfl
    change Holds D (.termEq _ left.code (.var (0 : Fin (source.as.arity + 1))) _)
    rw [← sameCode]
    exact termEquality_refl left

theorem suppliedLift_projects {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target) :
    QuotientCwf.project (suppliedLift morphism domain) =
      Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain := by
  apply QuotientCwf.pair_unique domain
  · exact ((quotientProjection D).map_comp _ _).symm.trans
      ((congrArg QuotientCwf.project (suppliedLift_projection morphism domain)).trans
        (((quotientProjection D).map_comp _ _).trans
          (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution
            (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain).symm))
  · exact (suppliedLift_newest morphism domain).trans
      (extensionSubstitution_value (QuotientCwf.project morphism) domain).symm

set_option backward.isDefEq.respectTransparency false in
theorem supplied_body_comparison {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)) :
    Holds D (.typeEq (extend source.as ((QuotientCwf.typeRepresentative domain).reindex morphism)).raw
      ((QuotientCwf.typeRepresentative codomain).reindex
        (rawLift morphism (QuotientCwf.typeRepresentative domain))).code
      ((QuotientCwf.typeRepresentative
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain))).reindex
        (extensionComparison ((QuotientCwf.typeRepresentative domain).reindex morphism)
          (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism)))
          (supplied_domain_equality morphism domain)).hom).code) := by
  let comparison := (extensionComparison ((QuotientCwf.typeRepresentative domain).reindex morphism)
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain (QuotientCwf.project morphism)))
    (supplied_domain_equality morphism domain)).hom
  have actualClass : QType.mk ((QuotientCwf.typeRepresentative codomain).reindex (suppliedLift morphism domain)) =
      QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain) := by
    change QuotientCwf.tySub (QType.mk (QuotientCwf.typeRepresentative codomain))
      (QuotientCwf.project (suppliedLift morphism domain)) = _
    rw [QuotientCwf.typeRepresentative_class, suppliedLift_projects]
  have same := (QType.mk_eq_iff _ _).mp (actualClass.trans (QuotientCwf.typeRepresentative_class _).symm)
  have atRaw := reindex_typeEquality same comparison
  change Holds D (.typeEq _
    (((QuotientCwf.typeRepresentative codomain).code.substitute (suppliedLift morphism domain).substitution).substitute
      comparison.substitution) _ ) at atRaw
  rw [show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
    TypeExpr.substitute_identity, TypeExpr.substitute_identity, suppliedLift_substitution] at atRaw
  change Holds D (.typeEq _
    ((QuotientCwf.typeRepresentative codomain).code.substitute
      (rawLift morphism (QuotientCwf.typeRepresentative domain)).substitution)
    ((QuotientCwf.typeRepresentative
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain))).code.substitute comparison.substitution))
  rw [show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
    TypeExpr.substitute_identity, rawLift_substitution]
  exact atRaw

set_option backward.isDefEq.respectTransparency false in
theorem pairAt_class {source target : QuotientCwf.QContext D}
    (morphism : source.as ⟶ target.as) (domain : QuotientCwf.Ty target)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain))
    (first : QuotientCwf.Tm source (QuotientCwf.tySub domain (QuotientCwf.project morphism)))
    (second : QuotientCwf.Tm source
      (QuotientCwf.tySub codomain (QuotientCwf.pair (QuotientCwf.project morphism) domain first)))
    (actualFirst : Term source.as ((QuotientCwf.typeRepresentative domain).reindex morphism))
    (actualSecond : Term source.as
      (((QuotientCwf.typeRepresentative codomain).reindex
        (rawLift morphism (QuotientCwf.typeRepresentative domain))).reindex (nativeSection actualFirst)))
    (firsts : QTerm.mk actualFirst = first.val) (seconds : QTerm.mk actualSecond = second.val) :
    (pairAt (SumElimination.stable D) (QuotientCwf.project morphism) first second).val =
      QTerm.mk (Sums.rawPair actualFirst actualSecond) := by
  let laterBody := QuotientCwf.tySub codomain
    (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
      (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain)
  let localSecond := (secondEquiv (C := QuotientCwf.cwf D)
    (QuotientCwf.project morphism) domain codomain first).symm second
  have secondTypes :
      QuotientCwf.tySub laterBody (selfExtend (QuotientCwf.cwf D) first) =
        QuotientCwf.tySub codomain (QuotientCwf.pair (QuotientCwf.project morphism) domain first) := by
    change QuotientCwf.tySub
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain))
      (selfExtend (QuotientCwf.cwf D) first) = _
    rw [← QuotientCwf.tySub_comp]
    exact congrArg (QuotientCwf.tySub codomain)
      (lift_selfExtend (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain first)
  have localSecondClass : localSecond.val = second.val :=
    heq_value secondTypes (Mettapedia.TypeTheory.ContextualSumPairReadout.secondEquiv_symm_heq
      (C := QuotientCwf.cwf D) (QuotientCwf.project morphism) domain codomain first second)
  have firstEquations := (QTerm.mk_eq_iff _ _).mp (firsts.trans (chosenTerm_class first).symm)
  have secondEquations := (QTerm.mk_eq_iff _ _).mp
    (seconds.trans (localSecondClass.symm.trans (Sums.componentRepresentative_class first localSecond).symm))
  have pairs := Sums.rawPair_compared _ _ (supplied_domain_equality morphism domain) _ _
    (supplied_body_comparison morphism domain codomain)
    actualFirst (chosenTerm first) actualSecond (Sums.componentRepresentative first localSecond)
    firstEquations.2 secondEquations.2
  have readout := heq_value (Sums.formation_substitution (QuotientCwf.project morphism) domain codomain)
    (Mettapedia.TypeTheory.ContextualSumPairReadout.pairAt_heq
      (SumElimination.stable D) (QuotientCwf.project morphism) first second)
  exact readout.trans pairs.symm

noncomputable def correctedPack {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    QuotientCwf.ext (QuotientCwf.ext context domain) codomain ⟶
      QuotientCwf.ext context (Sums.sigma domain codomain) :=
  QuotientCwf.project (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)) ≫
    (QuotientCwf.extPresentation context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))).inv

set_option backward.isDefEq.respectTransparency false in
theorem correctedPack_base {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    correctedPack domain codomain ≫ QuotientCwf.wk (Sums.sigma domain codomain) =
      QuotientCwf.wk codomain ≫ QuotientCwf.wk domain := by
  let sum := rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)
  let presentation := QuotientCwf.extPresentation context.as sum
  have inverseProjection : presentation.inv ≫ QuotientCwf.wk (Sums.sigma domain codomain) =
      QuotientCwf.project (projectionHom context.as sum) := by
    have forward : presentation.hom ≫ QuotientCwf.project (projectionHom context.as sum) =
        QuotientCwf.wk (Sums.sigma domain codomain) := QuotientCwf.extPresentation_projection _ _
    rw [← forward, ← Category.assoc]
    exact (congrArg (fun first => first ≫ QuotientCwf.project (projectionHom context.as sum))
      presentation.inv_hom_id).trans (Category.id_comp _)
  change (QuotientCwf.project (rawPack _ _) ≫ presentation.inv) ≫ _ = _
  rw [Category.assoc, inverseProjection, ← (quotientProjection D).map_comp, rawPack_projection]
  exact (quotientProjection D).map_comp _ _

set_option backward.isDefEq.respectTransparency false in
theorem correctedPack_value {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    (QuotientCwf.tmSub (QuotientCwf.vz (Sums.sigma domain codomain)) (correctedPack domain codomain)).val =
      QTerm.mk (rawGenericPair (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)) := by
  let sum := rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)
  let selected := QuotientCwf.typeRepresentative (Sums.sigma domain codomain)
  have annotations : Holds D (.typeEq context.as.raw selected.code sum.code) :=
    (QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class (Sums.sigma domain codomain))
  let comparison := extensionComparison selected sum annotations
  let raw := rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)
  let map := raw ≫ comparison.inv
  have base : map ≫ projectionHom context.as selected = rawTupleBase _ _ := by
    apply Hom.ext
    change composeSubstitution (fun index => .var index.succ)
      (composeSubstitution comparison.inv.substitution raw.substitution) = _
    rw [show comparison.inv.substitution = TermExpr.var from extensionComparison_inv_substitution _ _ _,
      identity_composeSubstitution]
    exact congrArg Hom.substitution (rawPack_projection (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain))
  let term := (newest context.as selected).reindex map
  have code : term.code = (rawGenericPair (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain)).code := by
    change (.var (0 : Fin (context.as.arity + 1)) : TermExpr S _).substitute
      (composeSubstitution comparison.inv.substitution raw.substitution) = _
    rw [show comparison.inv.substitution = TermExpr.var from extensionComparison_inv_substitution _ _ _,
      identity_composeSubstitution]
    rfl
  change QTerm.mk term = _
  apply (QTerm.mk_eq_iff _ _).mpr
  constructor
  · change Holds D (.typeEq _ ((selected.reindex (projectionHom context.as selected)).reindex map).code
      (sum.reindex (rawTupleBase _ _)).code)
    rw [← TypeOver.reindex_comp, base]
    exact reindex_typeEquality annotations (rawTupleBase _ _)
  · rw [← code]
    exact termEquality_refl term

set_option backward.isDefEq.respectTransparency false in
theorem pack_comparison {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    correctedPack domain codomain = pack (SumElimination.stable D) domain codomain := by
  let tuple := QuotientCwf.ext (QuotientCwf.ext context domain) codomain
  let data := tupleArrowEquiv (C := QuotientCwf.cwf D) domain codomain (𝟙 tuple)
  let base := rawTupleBase (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)
  have dataBase : data.1 = QuotientCwf.project base := by
    change (𝟙 tuple ≫ QuotientCwf.wk codomain) ≫ QuotientCwf.wk domain = _
    rw [Category.id_comp]
    exact ((quotientProjection D).map_comp _ _).symm
  have firsts : QTerm.mk (rawFirst (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain)) = data.2.1.val := by
    have reading := heq_value
      (QuotientCwf.tySub_comp domain (𝟙 tuple ≫ QuotientCwf.wk codomain) (QuotientCwf.wk domain))
      (Mettapedia.TypeTheory.ContextualSumPairReadout.tupleArrow_first_heq
      (C := QuotientCwf.cwf D) domain codomain (𝟙 tuple))
    change data.2.1.val = (QuotientCwf.tmSub (QuotientCwf.vz domain) (𝟙 tuple ≫ QuotientCwf.wk codomain)).val at reading
    rw [Category.id_comp] at reading
    apply Eq.trans ?_ reading.symm
    rw [rawFirst, QTerm.mk_cast]
    rfl
  have seconds : QTerm.mk (rawSecond (QuotientCwf.typeRepresentative domain)
      (QuotientCwf.typeRepresentative codomain)) = data.2.2.val := by
    have types : QuotientCwf.tySub codomain (QuotientCwf.pair data.1 domain data.2.1) =
        QuotientCwf.tySub (QuotientCwf.tySub codomain (QuotientCwf.wk codomain)) (𝟙 tuple) := by
      exact (congrArg (QuotientCwf.tySub codomain)
        (Mettapedia.TypeTheory.ContextualSumPairReadout.tupleArrow_middle
          (C := QuotientCwf.cwf D) domain codomain (𝟙 tuple))).trans
        (QuotientCwf.tySub_comp codomain (𝟙 tuple) (QuotientCwf.wk codomain))
    have reading := heq_value types (Mettapedia.TypeTheory.ContextualSumPairReadout.tupleArrow_second_heq
      (C := QuotientCwf.cwf D) domain codomain (𝟙 tuple))
    change data.2.2.val = QuotientCwf.totalSub (QuotientCwf.vz codomain).val (𝟙 tuple) at reading
    rw [QuotientCwf.totalSub_id] at reading
    apply Eq.trans ?_ reading.symm
    rw [rawSecond, QTerm.mk_cast]
    rfl
  apply QuotientCwf.pair_unique (Sums.sigma domain codomain)
  · exact (correctedPack_base domain codomain).trans (pack_over (SumElimination.stable D) domain codomain).symm
  · rw [correctedPack_value]
    have classified := Mettapedia.TypeTheory.ContextualSumPairReadout.packArrow_pair_readout
      (SumElimination.stable D) domain codomain (𝟙 tuple)
    change pack (SumElimination.stable D) domain codomain =
      QuotientCwf.pair data.1 (Sums.sigma domain codomain)
        (pairAt (SumElimination.stable D) data.1 data.2.1 data.2.2) at classified
    rw [classified, QuotientCwf.vz_pair_value]
    have output := pairAt_class base domain codomain
    cases dataBase
    exact (QTerm.mk_cast _ _).trans (output data.2.1 data.2.2 _ _ firsts seconds).symm

noncomputable abbrev sumPresentation {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :=
  QuotientCwf.extPresentation context.as
    (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))

set_option backward.isDefEq.respectTransparency false in
theorem pack_presentation {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    pack (SumElimination.stable D) domain codomain ≫ (sumPresentation domain codomain).hom =
      QuotientCwf.project (rawPack (QuotientCwf.typeRepresentative domain)
        (QuotientCwf.typeRepresentative codomain)) := by
  rw [← pack_comparison]
  change (QuotientCwf.project (rawPack _ _) ≫ (sumPresentation domain codomain).inv) ≫
    (sumPresentation domain codomain).hom = _
  rw [Category.assoc, (sumPresentation domain codomain).inv_hom_id, Category.comp_id]

noncomputable def nativeMotive {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) :
    QuotientCwf.Ty (QuotientCwf.ext context (Sums.sigma domain codomain)) :=
  QuotientCwf.tySub (QType.mk motive) (sumPresentation domain codomain).hom

set_option backward.isDefEq.respectTransparency false in
theorem nativeMotive_at_pack {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) :
    QuotientCwf.tySub (nativeMotive domain codomain motive) (pack (SumElimination.stable D) domain codomain) =
      QType.mk (motive.reindex
        (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) := by
  unfold nativeMotive
  rw [← QuotientCwf.tySub_comp, pack_presentation]
  rfl

noncomputable def nativeBranch {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (body : Term (rawTuple (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))
      (motive.reindex (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) :
    QuotientCwf.Tm (QuotientCwf.ext (QuotientCwf.ext context domain) codomain)
      (QuotientCwf.tySub (nativeMotive domain codomain motive) (pack (SumElimination.stable D) domain codomain)) :=
  ⟨QTerm.mk body, (nativeMotive_at_pack domain codomain motive).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem nativeMotive_roundtrip {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) :
    QuotientCwf.tySub (nativeMotive domain codomain motive) (sumPresentation domain codomain).inv = QType.mk motive := by
  unfold nativeMotive
  rw [← QuotientCwf.tySub_comp, (sumPresentation domain codomain).inv_hom_id, QuotientCwf.tySub_id]

noncomputable def derivedSection {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (body : Term (rawTuple (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))
      (motive.reindex (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) :
    Term (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) motive :=
  let native := eliminate (SumElimination.stable D) domain codomain (nativeMotive domain codomain motive)
    (nativeBranch domain codomain motive body)
  let transported := QuotientCwf.tmSub native (sumPresentation domain codomain).inv
  QuotientCwf.termRepresentative motive transported.val
    (transported.property.trans (nativeMotive_roundtrip domain codomain motive))

theorem derivedSection_class {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (body : Term (rawTuple (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))
      (motive.reindex (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) :
    QTerm.mk (derivedSection domain codomain motive body) =
      (QuotientCwf.tmSub
        (eliminate (SumElimination.stable D) domain codomain (nativeMotive domain codomain motive)
          (nativeBranch domain codomain motive body)) (sumPresentation domain codomain).inv).val := by
  let native := eliminate (SumElimination.stable D) domain codomain (nativeMotive domain codomain motive)
    (nativeBranch domain codomain motive body)
  let transported := QuotientCwf.tmSub native (sumPresentation domain codomain).inv
  exact QuotientCwf.termRepresentative_class motive transported.val
    (transported.property.trans (nativeMotive_roundtrip domain codomain motive))

set_option backward.isDefEq.respectTransparency false in
theorem derivedSection_beta {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (body : Term (rawTuple (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))
      (motive.reindex (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) :
    QTerm.mk ((derivedSection domain codomain motive body).reindex
      (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) = QTerm.mk body := by
  let native := eliminate (SumElimination.stable D) domain codomain (nativeMotive domain codomain motive)
    (nativeBranch domain codomain motive body)
  change QuotientCwf.totalSub (QTerm.mk (derivedSection domain codomain motive body))
    (QuotientCwf.project (rawPack _ _)) = _
  rw [derivedSection_class]
  change QuotientCwf.totalSub (QuotientCwf.totalSub native.val (sumPresentation domain codomain).inv)
    (QuotientCwf.project (rawPack _ _)) = _
  rw [← QuotientCwf.totalSub_comp]
  change QuotientCwf.totalSub native.val (correctedPack domain codomain) = _
  rw [pack_comparison]
  exact congrArg Subtype.val (eliminate_beta (SumElimination.stable D) domain codomain
    (nativeMotive domain codomain motive) (nativeBranch domain codomain motive body))

set_option backward.isDefEq.respectTransparency false in
/-- Every supplied literal sum elimination is the actual contextual eliminator
read at the supplied pair, after correcting the chosen sum presentation. -/
theorem authored_elimination_is_contextual {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (body : Term (rawTuple (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))
      (motive.reindex (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (value : Term context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) :
    QTerm.mk (rawEliminate (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)
      motive body value) =
      QuotientCwf.totalSub
        (eliminate (SumElimination.stable D) domain codomain (nativeMotive domain codomain motive)
          (nativeBranch domain codomain motive body)).val
        (QuotientCwf.project (nativeSection value) ≫ (sumPresentation domain codomain).inv) := by
  have branch := derivedSection_beta domain codomain motive body
  have comparison := rawEliminate_branch_congruence (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative codomain) motive body
    ((derivedSection domain codomain motive body).reindex (rawPack _ _)) branch.symm value
  have eta := rawEliminate_section_eta (QuotientCwf.typeRepresentative domain)
    (QuotientCwf.typeRepresentative codomain) motive (derivedSection domain codomain motive body) value
  apply (comparison.trans eta).trans
  change QuotientCwf.totalSub (QTerm.mk (derivedSection domain codomain motive body))
    (QuotientCwf.project (nativeSection value)) = _
  rw [derivedSection_class]
  exact (QuotientCwf.totalSub_comp
    (eliminate (SumElimination.stable D) domain codomain (nativeMotive domain codomain motive)
      (nativeBranch domain codomain motive body)).val
    (QuotientCwf.project (nativeSection value)) (sumPresentation domain codomain).inv).symm

noncomputable def packPresentationIso {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    QuotientCwf.ext (QuotientCwf.ext context domain) codomain ≅
      (quotientProjection D).obj (extend context.as
        (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) where
  hom := pack (SumElimination.stable D) domain codomain ≫ (sumPresentation domain codomain).hom
  inv := (sumPresentation domain codomain).inv ≫ unpack (SumElimination.stable D) domain codomain
  hom_inv_id := by
    erw [Category.assoc, ← Category.assoc (sumPresentation domain codomain).hom,
      (sumPresentation domain codomain).hom_inv_id, Category.id_comp]
    exact unpack_pack (SumElimination.stable D) domain codomain
  inv_hom_id := by
    erw [Category.assoc, ← Category.assoc (unpack (SumElimination.stable D) domain codomain)]
    have middle : unpack (SumElimination.stable D) domain codomain ≫
        pack (SumElimination.stable D) domain codomain = 𝟙 _ :=
      pack_unpack (SumElimination.stable D) domain codomain
    erw [middle, Category.id_comp]
    exact (sumPresentation domain codomain).inv_hom_id

theorem packPresentationIso_hom {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    (packPresentationIso domain codomain).hom = QuotientCwf.project
      (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)) :=
  pack_presentation domain codomain

set_option backward.isDefEq.respectTransparency false in
theorem branch_readout_injective {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    Function.Injective (fun term : QTerm (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) =>
        QuotientCwf.totalSub term (QuotientCwf.project
          (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)))) := by
  intro first second same
  let comparison := packPresentationIso domain codomain
  have inverse := congrArg (fun term => QuotientCwf.totalSub term comparison.inv) same
  rw [← packPresentationIso_hom domain codomain, ← QuotientCwf.totalSub_comp,
    ← QuotientCwf.totalSub_comp, comparison.inv_hom_id,
    QuotientCwf.totalSub_id, QuotientCwf.totalSub_id] at inverse
  exact inverse

theorem derivedSection_unique {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (body : Term (rawTuple (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))
      (motive.reindex (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))))
    (candidate : Term (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) motive)
    (readout : QTerm.mk (candidate.reindex
      (rawPack (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) = QTerm.mk body) :
    QTerm.mk candidate = QTerm.mk (derivedSection domain codomain motive body) :=
  branch_readout_injective domain codomain (readout.trans (derivedSection_beta domain codomain motive body).symm)

theorem lifted_weaken_instantiate {n : Nat} (type : TypeExpr S (n + 1)) (value : TermExpr S n) :
    (type.rename (liftRenaming (Fin.succ : Renaming n (n + 1)))).substitute
      (liftSubstitution (instantiate value)) = type := by
  rw [TypeExpr.substitute_rename]
  have mapping : liftSubstitution (instantiate value) ∘ liftRenaming (Fin.succ : Renaming n (n + 1)) =
      (TermExpr.var : Substitution S (n + 1) (n + 1)) := by
    funext index
    cases index using Fin.cases <;> rfl
  rw [mapping, TypeExpr.substitute_identity]

def rawSumVariable {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    Term (extend context (rawSigma domain codomain))
      (rawSigma (domain.reindex (projectionHom context (rawSigma domain codomain)))
        (codomain.reindex (rawLift (projectionHom context (rawSigma domain codomain)) domain))) :=
  (newest context (rawSigma domain codomain)).cast
    (rawSigma_reindex (projectionHom context (rawSigma domain codomain)) domain codomain)

def rawFirstSection {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) := Sums.rawFst (rawSumVariable domain codomain)

def rawSecondMotive {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) : TypeOver (extend context (rawSigma domain codomain)) :=
  (codomain.reindex (rawLift (projectionHom context (rawSigma domain codomain)) domain)).reindex
    (nativeSection (rawFirstSection domain codomain))

def rawSecondSection {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    Term (extend context (rawSigma domain codomain)) (rawSecondMotive domain codomain) :=
  Sums.rawSnd (rawSumVariable domain codomain)

theorem rawFirstSection_code {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) :
    (rawFirstSection domain codomain).code =
      .fst (domain.code.rename Fin.succ) (codomain.code.rename (liftRenaming Fin.succ)) (.var 0) := by
  change TermExpr.fst (domain.code.substitute (fun index => .var index.succ))
    (codomain.code.substitute (rawLift (projectionHom context (rawSigma domain codomain)) domain).substitution)
    (rawSumVariable domain codomain).code = _
  rw [rawSumVariable, Term.cast_code, rawLift_substitution]
  change TermExpr.fst (domain.code.substitute (fun index => .var index.succ))
    (codomain.code.substitute (liftSubstitution (fun index => .var index.succ))) (.var 0) = _
  rw [liftSubstitution_variables, TypeExpr.substitute_variables, TypeExpr.substitute_variables]

theorem rawFirstSection_at_code {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) (value : Term context (rawSigma domain codomain)) :
    ((rawFirstSection domain codomain).reindex (nativeSection value)).code = (Sums.rawFst value).code := by
  change (rawFirstSection domain codomain).code.substitute (nativeSection value).substitution = _
  rw [rawFirstSection_code, nativeSection_substitution]
  change TermExpr.fst ((domain.code.rename Fin.succ).substitute (instantiate value.code))
    ((codomain.code.rename (liftRenaming Fin.succ)).substitute (liftSubstitution (instantiate value.code))) value.code = _
  rw [TypeExpr.instantiate_weaken, lifted_weaken_instantiate]
  rfl

theorem rawSecondMotive_at {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) (value : Term context (rawSigma domain codomain)) :
    (rawSecondMotive domain codomain).reindex (nativeSection value) =
      codomain.reindex (nativeSection (Sums.rawFst value)) := by
  apply TypeOver.ext
  change ((codomain.code.substitute (rawLift (projectionHom context (rawSigma domain codomain)) domain).substitution).substitute
    (nativeSection (rawFirstSection domain codomain)).substitution).substitute (nativeSection value).substitution = _
  rw [nativeSection_substitution, nativeSection_substitution, rawLift_substitution]
  change ((codomain.code.substitute (liftSubstitution (fun index => .var index.succ))).substitute
    (instantiate (rawFirstSection domain codomain).code)).substitute (instantiate value.code) = _
  rw [liftSubstitution_variables, TypeExpr.substitute_variables, TypeExpr.substitute_instantiate,
    lifted_weaken_instantiate]
  have first := rawFirstSection_at_code domain codomain value
  change (rawFirstSection domain codomain).code.substitute (nativeSection value).substitution =
    (Sums.rawFst value).code at first
  rw [nativeSection_substitution] at first
  rw [first]
  exact (congrArg (fun mapping => codomain.code.substitute mapping) (nativeSection_substitution (Sums.rawFst value))).symm

theorem rawSecondSection_at {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) (value : Term context (rawSigma domain codomain)) :
    QTerm.mk ((rawSecondSection domain codomain).reindex (nativeSection value)) = QTerm.mk (Sums.rawSnd value) := by
  have terms : ((rawSecondSection domain codomain).reindex (nativeSection value)).cast
      (rawSecondMotive_at domain codomain value) = Sums.rawSnd value := by
    apply Term.ext
    rw [Term.cast_code]
    change (TermExpr.snd (domain.code.substitute (fun index => .var index.succ))
      (codomain.code.substitute (rawLift (projectionHom context (rawSigma domain codomain)) domain).substitution)
      (rawSumVariable domain codomain).code).substitute (nativeSection value).substitution = _
    rw [rawSumVariable, Term.cast_code, rawLift_substitution, nativeSection_substitution]
    change (TermExpr.snd (domain.code.substitute (fun index => .var index.succ))
      (codomain.code.substitute (liftSubstitution (fun index => .var index.succ))) (.var 0)).substitute
        (instantiate value.code) = _
    rw [liftSubstitution_variables, TypeExpr.substitute_variables, TypeExpr.substitute_variables]
    change TermExpr.snd ((domain.code.rename Fin.succ).substitute (instantiate value.code))
      ((codomain.code.rename (liftRenaming Fin.succ)).substitute (liftSubstitution (instantiate value.code))) value.code = _
    rw [TypeExpr.instantiate_weaken, lifted_weaken_instantiate]
    rfl
  exact (QTerm.mk_cast _ _).symm.trans (congrArg QTerm.mk terms)

theorem full_motive_second_readout {context : Context D} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain))
    (first : Term context domain) (second : Term context (codomain.reindex (nativeSection first))) :
    QTerm.mk (rawEliminate domain codomain (rawSecondMotive domain codomain)
      ((rawSecondSection domain codomain).reindex (rawPack domain codomain)) (Sums.rawPair first second)) =
        QTerm.mk second :=
  (rawEliminate_section_eta domain codomain (rawSecondMotive domain codomain)
    (rawSecondSection domain codomain) (Sums.rawPair first second)).trans
      ((rawSecondSection_at domain codomain (Sums.rawPair first second)).trans (Sums.rawSndBeta first second))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SigmaEliminationComparison
