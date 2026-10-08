import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualRefinementValues
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualProducts

/-!
# Substitution of generated contextual refinement values

Predicate substitution follows the actual binder extension substitution.
The generated mixed annotation comparisons earn strict formation and the
heterogeneous introduction and forgetting equations for complete supplied
term classes. Guards are actual generated entailments and are transported
through the contextual section square.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementValues

open _root_.CategoryTheory
open QuotientComprehensionSyntax DependentTypes
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.GSLT.Core.ContextualLadder.TypeOver (extensionSubstitution)

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem reindexed_predicate_class {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) (domain : QuotientCwf.Ty target)
    (predicate : QPredicate (QuotientCwf.ext target domain).as) :
    QPredicate.mk ((predicateRepresentative predicate).reindex (nativeLift substitution domain)) =
      predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain) := by
  change predicateSub (QPredicate.mk (predicateRepresentative predicate))
    (QuotientCwf.project (nativeLift substitution domain)) = _
  rw [predicateRepresentative_class, nativeLift_projects]

theorem reindexed_predicate_equality {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) (domain : QuotientCwf.Ty target)
    (predicate : QPredicate (QuotientCwf.ext target domain).as) :
    Holds D (.predicateEq (QuotientCwf.ext source (QuotientCwf.tySub domain substitution)).as.raw
      ((predicateRepresentative predicate).code.substitute
        (liftSubstitution (QuotientCwf.representative substitution).substitution))
      (predicateRepresentative (predicateSub predicate
        (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))).code) := by
  have equality := (QPredicate.mk_eq_iff _ _).mp
    ((reindexed_predicate_class substitution domain predicate).trans
      (predicateRepresentative_class _).symm)
  change Holds D (.predicateEq _ ((predicateRepresentative predicate).code.substitute
    (nativeLift substitution domain).substitution) _) at equality
  rw [nativeLift_substitution] at equality
  exact equality

theorem reindexed_predicate_comparison {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) (domain : QuotientCwf.Ty target)
    (predicate : QPredicate (QuotientCwf.ext target domain).as) :
    Holds D (.predicateEq (extend source.as
      ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative substitution))).raw
      ((predicateRepresentative predicate).reindex
        (rawLift (QuotientCwf.representative substitution) (QuotientCwf.typeRepresentative domain))).code
      ((predicateRepresentative (predicateSub predicate
        (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))).reindex
        (extensionComparison
          ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative substitution))
          (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain substitution))
          (reindexed_domain_equality substitution domain)).hom).code) := by
  let comparison := (extensionComparison
    ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative substitution))
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain substitution))
    (reindexed_domain_equality substitution domain)).hom
  have equality := conclude (.substitutePredicateEquality
    (extend source.as ((QuotientCwf.typeRepresentative domain).reindex
      (QuotientCwf.representative substitution))).raw
    (QuotientCwf.ext source (QuotientCwf.tySub domain substitution)).as.raw comparison.substitution
    ((predicateRepresentative predicate).code.substitute
      (liftSubstitution (QuotientCwf.representative substitution).substitution))
    (predicateRepresentative (predicateSub predicate
      (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))).code)
      ⟨comparison.admitted, reindexed_predicate_equality substitution domain predicate, trivial⟩
  change Holds D (.predicateEq _
    (((predicateRepresentative predicate).code.substitute
      (liftSubstitution (QuotientCwf.representative substitution).substitution)).substitute
        comparison.substitution)
    ((predicateRepresentative (predicateSub predicate
      (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))).code.substitute
        comparison.substitution)) at equality
  rw [show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
    PropExpr.substitute_identity, PropExpr.substitute_identity] at equality
  change Holds D (.predicateEq _
    ((predicateRepresentative predicate).code.substitute
      (rawLift (QuotientCwf.representative substitution) (QuotientCwf.typeRepresentative domain)).substitution)
    ((predicateRepresentative (predicateSub predicate
      (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))).code.substitute
      comparison.substitution))
  rw [rawLift_substitution,
    show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _,
    PropExpr.substitute_identity]
  exact equality

/-- Choosing different generated annotation representatives does not
weaken strict formation substitution in the actual quotient CwF. -/
theorem formation_substitution {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) (domain : QuotientCwf.Ty target)
    (predicate : QPredicate (QuotientCwf.ext target domain).as) :
    QuotientCwf.tySub (Refinements.type domain predicate) substitution =
      Refinements.type (QuotientCwf.tySub domain substitution)
        (predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain)) := by
  let pulled := predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain)
  have annotated : QuotientCwf.tySub (QType.mk (typeRepresentative predicate)) substitution =
      QType.mk ((typeRepresentative predicate).reindex (QuotientCwf.representative substitution)) := by
    conv_lhs => rw [← QuotientCwf.project_representative substitution]
    rfl
  calc
    _ = QuotientCwf.tySub (QType.mk (typeRepresentative predicate)) substitution :=
      congrArg (fun type => QuotientCwf.tySub type substitution) (typeRepresentative_class predicate).symm
    _ = _ := annotated
    _ = QType.mk (Refinements.rawType
        ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative substitution))
        ((predicateRepresentative predicate).reindex
          (rawLift (QuotientCwf.representative substitution) (QuotientCwf.typeRepresentative domain)))) :=
      congrArg QType.mk (Refinements.rawType_reindex _ _ _)
    _ = QType.mk (typeRepresentative pulled) := _root_.Quotient.sound
      (Refinements.rawType_compared _ _ (reindexed_domain_equality substitution domain) _ _
        (reindexed_predicate_comparison substitution domain predicate))
    _ = _ := typeRepresentative_class pulled

theorem guard_substitution {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) {domain : QuotientCwf.Ty target}
    (predicate : QPredicate (QuotientCwf.ext target domain).as)
    (argument : QuotientCwf.Tm target domain) :
    predicateSub (guard predicate argument) substitution =
      guard (predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))
        (QuotientCwf.tmSub argument substitution) := by
  unfold guard
  rw [← predicateSub_comp, ← predicateSub_comp, section_substitution]

theorem guard_entails_substitution {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) {domain : QuotientCwf.Ty target}
    (predicate : QPredicate (QuotientCwf.ext target domain).as)
    (argument : QuotientCwf.Tm target domain) (evidence : (guard predicate argument).entails) :
    (guard (predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))
      (QuotientCwf.tmSub argument substitution)).entails := by
  rw [← guard_substitution]
  exact predicateSub_entails evidence substitution

theorem raw_guard_reindex {source target : Context D} (substitution : source ⟶ target)
    {domain : TypeOver target} (predicate : PredicateOver (extend target domain))
    (argument : Term target domain)
    (guard : Holds D (.entails target.raw (predicate.code.substitute (instantiate argument.code)))) :
    Holds D (.entails source.raw
      ((predicate.reindex (rawLift substitution domain)).code.substitute
        (instantiate (argument.reindex substitution).code))) := by
  have transported := conclude (.substituteEntailment source.raw target.raw substitution.substitution
    (predicate.code.substitute (instantiate argument.code))) ⟨substitution.admitted, guard, trivial⟩
  change Holds D (.entails source.raw
    ((predicate.code.substitute (instantiate argument.code)).substitute substitution.substitution))
    at transported
  rw [PropExpr.substitute_instantiate] at transported
  change Holds D (.entails source.raw
    ((predicate.code.substitute (rawLift substitution domain).substitution).substitute
      (instantiate (argument.code.substitute substitution.substitution))))
  rw [rawLift_substitution]
  exact transported

theorem raw_intro_reindex {source target : Context D} (substitution : source ⟶ target)
    {domain : TypeOver target} (predicate : PredicateOver (extend target domain))
    (argument : Term target domain)
    (guard : Holds D (.entails target.raw (predicate.code.substitute (instantiate argument.code)))) :
    ((Refinements.rawIntro predicate argument guard).reindex substitution).cast
        (Refinements.rawType_reindex substitution domain predicate) =
      Refinements.rawIntro (predicate.reindex (rawLift substitution domain))
        (argument.reindex substitution) (raw_guard_reindex substitution predicate argument guard) := by
  apply Term.ext
  rw [Term.cast_code]
  change (.refine domain.code predicate.code argument.code : TermExpr S _).substitute substitution.substitution =
    .refine (domain.code.substitute substitution.substitution)
      (predicate.code.substitute (rawLift substitution domain).substitution)
      (argument.code.substitute substitution.substitution)
  rw [rawLift_substitution]
  rfl

theorem raw_forget_reindex {source target : Context D} (substitution : source ⟶ target)
    {domain : TypeOver target} {predicate : PredicateOver (extend target domain)}
    (term : Term target (Refinements.rawType domain predicate)) :
    (Refinements.rawForget term).reindex substitution =
      Refinements.rawForget ((term.reindex substitution).cast
        (Refinements.rawType_reindex substitution domain predicate)) := by
  apply Term.ext
  change (.forget domain.code predicate.code term.code : TermExpr S _).substitute substitution.substitution =
    .forget (domain.code.substitute substitution.substitution)
      (predicate.code.substitute (rawLift substitution domain).substitution)
      ((term.reindex substitution).cast (Refinements.rawType_reindex substitution domain predicate)).code
  rw [Term.cast_code, rawLift_substitution]
  rfl

theorem intro_substitution {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) {domain : QuotientCwf.Ty target}
    (predicate : QPredicate (QuotientCwf.ext target domain).as)
    (argument : QuotientCwf.Tm target domain) (evidence : (guard predicate argument).entails)
    (transportedEvidence :
      (guard (predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))
        (QuotientCwf.tmSub argument substitution)).entails) :
    HEq (QuotientCwf.tmSub (intro predicate argument evidence) substitution)
      (intro (predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))
        (QuotientCwf.tmSub argument substitution) transportedEvidence) := by
  apply heq_of_value
  let pulled := predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain)
  let newArgument := QuotientCwf.tmSub argument substitution
  let rawSubstitution := QuotientCwf.representative substitution
  let oldPredicate := predicateRepresentative predicate
  let oldArgument := chosenTerm argument
  let oldGuard := raw_guard predicate argument evidence
  let newGuard := raw_guard pulled newArgument transportedEvidence
  have arguments := (QTerm.mk_eq_iff _ _).mp
    ((Products.supplied_reindex_class substitution argument oldArgument (chosenTerm_class argument)).trans
      (chosenTerm_class newArgument).symm)
  have compared : QTerm.mk (Refinements.rawIntro
      (oldPredicate.reindex (rawLift rawSubstitution (QuotientCwf.typeRepresentative domain)))
      (oldArgument.reindex rawSubstitution) (raw_guard_reindex rawSubstitution oldPredicate oldArgument oldGuard)) =
    QTerm.mk (Refinements.rawIntro (predicateRepresentative pulled) (chosenTerm newArgument) newGuard) :=
    (QTerm.mk_eq_iff _ _).mpr
      ⟨Refinements.rawType_compared _ _ (reindexed_domain_equality substitution domain) _ _
          (reindexed_predicate_comparison substitution domain predicate),
        Refinements.rawIntro_compared _ _ (reindexed_domain_equality substitution domain) _ _
          (reindexed_predicate_comparison substitution domain predicate) _ _ arguments.2 _ _⟩
  have actual := Products.supplied_reindex_class substitution (intro predicate argument evidence)
    (Refinements.rawIntro oldPredicate oldArgument oldGuard) rfl
  exact actual.symm.trans ((QTerm.mk_cast _ _).symm.trans
    ((congrArg QTerm.mk (raw_intro_reindex rawSubstitution oldPredicate oldArgument oldGuard)).trans compared))

theorem forget_substitution {source target : QuotientCwf.QContext D}
    (substitution : source ⟶ target) {domain : QuotientCwf.Ty target}
    (predicate : QPredicate (QuotientCwf.ext target domain).as)
    (term : QuotientCwf.Tm target (Refinements.type domain predicate))
    (transported : QuotientCwf.Tm source (Refinements.type (QuotientCwf.tySub domain substitution)
      (predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))))
    (same : HEq (QuotientCwf.tmSub term substitution) transported) :
    HEq (QuotientCwf.tmSub (forget predicate term) substitution)
      (forget (predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain))
        transported) := by
  apply heq_of_value
  let pulled := predicateSub predicate (extensionSubstitution (C := QuotientCwf.cwf D) substitution domain)
  let rawSubstitution := QuotientCwf.representative substitution
  let oldTerm := refinementTermRepresentative predicate term
  let pulledTerm := (oldTerm.reindex rawSubstitution).cast
    (Refinements.rawType_reindex rawSubstitution (QuotientCwf.typeRepresentative domain)
      (predicateRepresentative predicate))
  have castClass : QTerm.mk pulledTerm = QTerm.mk (oldTerm.reindex rawSubstitution) :=
    QTerm.mk_cast _ _
  have classes := (QTerm.mk_eq_iff pulledTerm (refinementTermRepresentative pulled transported)).mp
    ((castClass.trans
      (Products.supplied_reindex_class substitution term oldTerm (refinementTermRepresentative_class predicate term))).trans
        ((heq_value (formation_substitution substitution domain predicate) same).trans
          (refinementTermRepresentative_class pulled transported).symm))
  have compared : QTerm.mk (Refinements.rawForget pulledTerm) =
      QTerm.mk (Refinements.rawForget (refinementTermRepresentative pulled transported)) :=
    (QTerm.mk_eq_iff _ _).mpr
      ⟨reindexed_domain_equality substitution domain,
        Refinements.rawForget_compared _ _ (reindexed_domain_equality substitution domain) _ _
          (reindexed_predicate_comparison substitution domain predicate) _ _ classes.2⟩
  have actual := Products.supplied_reindex_class substitution (forget predicate term)
    (Refinements.rawForget oldTerm) rfl
  exact actual.symm.trans ((congrArg QTerm.mk (raw_forget_reindex rawSubstitution oldTerm)).trans compared)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementValues
