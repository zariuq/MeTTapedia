import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicates
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualComprehensionSyntax

/-!
# Generated refinement formation and retained inhabitants

Formation, introduction, forgetting and the guard use the actual generated
rules. Their beta and eta equations retain the supplied inhabitant. Predicate
and type representatives compare through the earned mixed annotation rules,
and complete binder substitution commutes with refinement formation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Refinements

open _root_.CategoryTheory
open QuotientComprehensionSyntax

universe u
variable {S : Symbols.{u}} {D : Signature S}

def rawType {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver (extend context domain)) : TypeOver context :=
  ⟨.comprehension domain.code predicate.code,
    conclude (.comprehensionFormation context.raw domain.code predicate.code)
      ⟨context.formed.judgment, domain.formed, predicate.formed, trivial⟩⟩

def rawIntro {context : Context D} {domain : TypeOver context}
    (predicate : PredicateOver (extend context domain)) (term : Term context domain)
    (guard : Holds D (.entails context.raw (predicate.code.substitute (instantiate term.code)))) :
    Term context (rawType domain predicate) :=
  ⟨.refine domain.code predicate.code term.code,
    conclude (.comprehensionIntroduction context.raw domain.code predicate.code term.code)
      ⟨domain.formed, predicate.formed, term.typed, guard, trivial⟩⟩

def rawForget {context : Context D} {domain : TypeOver context}
    {predicate : PredicateOver (extend context domain)} (term : Term context (rawType domain predicate)) :
    Term context domain :=
  ⟨.forget domain.code predicate.code term.code,
    conclude (.comprehensionElimination context.raw domain.code predicate.code term.code)
      ⟨domain.formed, predicate.formed, term.typed, trivial⟩⟩

theorem rawGuard {context : Context D} {domain : TypeOver context}
    {predicate : PredicateOver (extend context domain)} (term : Term context (rawType domain predicate)) :
    Holds D (.entails context.raw (predicate.code.substitute (instantiate (rawForget term).code))) :=
  conclude (.comprehensionGuard context.raw domain.code predicate.code term.code)
    ⟨domain.formed, predicate.formed, term.typed, trivial⟩

theorem rawBeta {context : Context D} {domain : TypeOver context}
    (predicate : PredicateOver (extend context domain)) (term : Term context domain)
    (guard : Holds D (.entails context.raw (predicate.code.substitute (instantiate term.code)))) :
    Holds D (.termEq context.raw (rawForget (rawIntro predicate term guard)).code term.code domain.code) :=
  conclude (.comprehensionBeta context.raw domain.code predicate.code term.code)
    ⟨domain.formed, predicate.formed, term.typed, guard, trivial⟩

theorem rawEta {context : Context D} {domain : TypeOver context}
    {predicate : PredicateOver (extend context domain)} (term : Term context (rawType domain predicate)) :
    Holds D (.termEq context.raw (rawIntro predicate (rawForget term) (rawGuard term)).code
      term.code (rawType domain predicate).code) :=
  conclude (.comprehensionEta context.raw domain.code predicate.code term.code)
    ⟨domain.formed, predicate.formed, term.typed, trivial⟩

theorem rawIntro_congruent {context : Context D} {domain : TypeOver context}
    (predicate : PredicateOver (extend context domain)) {first second : Term context domain}
    (same : Holds D (.termEq context.raw first.code second.code domain.code))
    (firstGuard : Holds D (.entails context.raw (predicate.code.substitute (instantiate first.code))))
    (secondGuard : Holds D (.entails context.raw (predicate.code.substitute (instantiate second.code)))) :
    Holds D (.termEq context.raw (rawIntro predicate first firstGuard).code
      (rawIntro predicate second secondGuard).code (rawType domain predicate).code) :=
  conclude (.refineCongruence context.raw domain.code predicate.code first.code second.code)
    ⟨domain.formed, predicate.formed, same, firstGuard, secondGuard, trivial⟩

theorem rawForget_congruent {context : Context D} {domain : TypeOver context}
    {predicate : PredicateOver (extend context domain)} {first second : Term context (rawType domain predicate)}
    (same : Holds D (.termEq context.raw first.code second.code (rawType domain predicate).code)) :
    Holds D (.termEq context.raw (rawForget first).code (rawForget second).code domain.code) :=
  conclude (.forgetCongruence context.raw domain.code predicate.code first.code second.code)
    ⟨domain.formed, predicate.formed, same, trivial⟩

theorem extensionComparison_predicate_code {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code))
    (predicate : PredicateOver (extend context second)) :
    (predicate.reindex (extensionComparison first second same).hom).code = predicate.code := by
  change predicate.code.substitute (extensionComparison first second same).hom.substitution = predicate.code
  rw [extensionComparison_hom_substitution, PropExpr.substitute_identity]

theorem rawType_compared {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstPredicate : PredicateOver (extend context first))
    (secondPredicate : PredicateOver (extend context second))
    (samePredicate : Holds D (.predicateEq (extend context first).raw firstPredicate.code
      (secondPredicate.reindex (extensionComparison first second sameDomain).hom).code)) :
    Holds D (.typeEq context.raw (rawType first firstPredicate).code (rawType second secondPredicate).code) := by
  rw [extensionComparison_predicate_code] at samePredicate
  exact conclude (.comprehensionCongruence context.raw first.code second.code
    firstPredicate.code secondPredicate.code) ⟨sameDomain, samePredicate, secondPredicate.formed, trivial⟩

theorem rawIntro_compared {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstPredicate : PredicateOver (extend context first))
    (secondPredicate : PredicateOver (extend context second))
    (samePredicate : Holds D (.predicateEq (extend context first).raw firstPredicate.code
      (secondPredicate.reindex (extensionComparison first second sameDomain).hom).code))
    (left : Term context first) (right : Term context second)
    (sameValue : Holds D (.termEq context.raw left.code right.code first.code))
    (leftGuard : Holds D (.entails context.raw (firstPredicate.code.substitute (instantiate left.code))))
    (rightGuard : Holds D (.entails context.raw (secondPredicate.code.substitute (instantiate right.code)))) :
    Holds D (.termEq context.raw (rawIntro firstPredicate left leftGuard).code
      (rawIntro secondPredicate right rightGuard).code (rawType first firstPredicate).code) := by
  rw [extensionComparison_predicate_code] at samePredicate
  exact conclude (.refineAnnotationCongruence context.raw first.code second.code
    firstPredicate.code secondPredicate.code left.code right.code)
      ⟨sameDomain, samePredicate, secondPredicate.formed, sameValue, right.typed,
        leftGuard, rightGuard, trivial⟩

theorem rawForget_compared {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstPredicate : PredicateOver (extend context first))
    (secondPredicate : PredicateOver (extend context second))
    (samePredicate : Holds D (.predicateEq (extend context first).raw firstPredicate.code
      (secondPredicate.reindex (extensionComparison first second sameDomain).hom).code))
    (left : Term context (rawType first firstPredicate))
    (right : Term context (rawType second secondPredicate))
    (sameValue : Holds D (.termEq context.raw left.code right.code (rawType first firstPredicate).code)) :
    Holds D (.termEq context.raw (rawForget left).code (rawForget right).code first.code) := by
  rw [extensionComparison_predicate_code] at samePredicate
  exact conclude (.forgetAnnotationCongruence context.raw first.code second.code
    firstPredicate.code secondPredicate.code left.code right.code)
      ⟨sameDomain, samePredicate, secondPredicate.formed, sameValue, right.typed, trivial⟩

theorem rawType_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (predicate : PredicateOver (extend target domain)) :
    (rawType domain predicate).reindex morphism =
      rawType (domain.reindex morphism) (predicate.reindex (rawLift morphism domain)) := by
  apply TypeOver.ext
  change TypeExpr.comprehension (domain.code.substitute morphism.substitution)
      (predicate.code.substitute (liftSubstitution morphism.substitution)) =
    TypeExpr.comprehension (domain.code.substitute morphism.substitution)
      (predicate.code.substitute (rawLift morphism domain).substitution)
  rw [rawLift_substitution]

def typeAt {context : Context D} (domain : TypeOver context)
    (predicate : QPredicate (extend context domain)) : QType context :=
  _root_.Quotient.lift (fun formed => QType.mk (rawType domain formed))
    (fun first second same => _root_.Quotient.sound
      (conclude (.comprehensionCongruence context.raw domain.code domain.code first.code second.code)
        ⟨typeEquality_refl domain, same, second.formed, trivial⟩)) predicate

@[simp] theorem typeAt_mk {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver (extend context domain)) :
    typeAt domain (QPredicate.mk predicate) = QType.mk (rawType domain predicate) := rfl

noncomputable def type {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (predicate : QPredicate (QuotientCwf.ext context domain).as) : QuotientCwf.Ty context :=
  typeAt (QuotientCwf.typeRepresentative domain) predicate

theorem typeAt_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (predicate : QPredicate (extend target domain)) :
    (typeAt domain predicate).reindex morphism =
      typeAt (domain.reindex morphism) (predicate.reindex (rawLift morphism domain)) := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact congrArg QType.mk (rawType_reindex morphism domain formed)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Refinements
