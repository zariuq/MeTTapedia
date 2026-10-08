import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualAssumptionModel

/-!
# Equal predicates compare their retained assumption contexts

Both comparison directions are guarded substitutions earned from the
generated predicate equation. They preserve every data variable and the
assumption inclusion. Their naturality, composition and uniqueness follow
from the complete typed substitution and monic inclusion laws. The raw
predicate presentations and their context objects remain retained.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

def assumptionArrow {context : Context D} (first second : PredicateOver context)
    (same : Holds D (.predicateEq context.raw first.code second.code)) :
    assumed context first ⟶ assumed context second :=
  select second (assumptionInclusion context first) (by
    have equation := conclude (.substitutePredicateEquality (assumed context first).raw context.raw
      TermExpr.var first.code second.code)
      ⟨(assumptionInclusion context first).admitted, same, trivial⟩
    change Holds D (.predicateEq (assumed context first).raw
      (first.code.substitute TermExpr.var) (second.code.substitute TermExpr.var)) at equation
    rw [PropExpr.substitute_identity, PropExpr.substitute_identity] at equation
    have guard := conclude (.entailmentConversion (assumed context first).raw first.code second.code)
      ⟨equation, Logic.hypothesis first, trivial⟩
    change Holds D (.entails (assumed context first).raw (second.code.substitute TermExpr.var))
    simpa only [PropExpr.substitute_identity] using guard)

theorem assumptionArrow_tuple {context : Context D} (first second : PredicateOver context)
    (same : Holds D (.predicateEq context.raw first.code second.code)) :
    (assumptionArrow first second same).substitution = TermExpr.var := rfl

theorem assumptionArrow_projection {context : Context D} (first second : PredicateOver context)
    (same : Holds D (.predicateEq context.raw first.code second.code)) :
    assumptionArrow first second same ≫ assumptionInclusion context second =
      assumptionInclusion context first := select_inclusion _ _ _

theorem assumptionArrow_unique {context : Context D} (first second : PredicateOver context)
    (same : Holds D (.predicateEq context.raw first.code second.code))
    (other : assumed context first ⟶ assumed context second)
    (projection : other ≫ assumptionInclusion context second = assumptionInclusion context first) :
    other = assumptionArrow first second same := by
  apply (cancel_mono (assumptionInclusion context second)).mp
  exact projection.trans (assumptionArrow_projection first second same).symm

def assumptionComparison {context : Context D} (first second : PredicateOver context)
    (same : Holds D (.predicateEq context.raw first.code second.code)) :
    assumed context first ≅ assumed context second where
  hom := assumptionArrow first second same
  inv := assumptionArrow second first (predicateEquality_symm same)
  hom_inv_id := Hom.ext (composeSubstitution_identity TermExpr.var)
  inv_hom_id := Hom.ext (composeSubstitution_identity TermExpr.var)

theorem assumptionArrow_comp {context : Context D} (first middle last : PredicateOver context)
    (earlier : Holds D (.predicateEq context.raw first.code middle.code))
    (later : Holds D (.predicateEq context.raw middle.code last.code)) :
    assumptionArrow first middle earlier ≫ assumptionArrow middle last later =
      assumptionArrow first last (predicateEquality_trans earlier later) :=
  Hom.ext (composeSubstitution_identity TermExpr.var)

def rawAssumptionLift {source target : Context D} (morphism : source ⟶ target)
    (predicate : PredicateOver target) :
    assumed source (predicate.reindex morphism) ⟶ assumed target predicate :=
  ⟨morphism.substitution,
    conclude (.substitutionAssumptionLift source.raw target.raw predicate.code morphism.substitution)
      ⟨morphism.admitted, predicate.formed, trivial⟩⟩

theorem assumptionEquation_reindex {source target : Context D} (morphism : source ⟶ target)
    {first second : PredicateOver target}
    (same : Holds D (.predicateEq target.raw first.code second.code)) :
    Holds D (.predicateEq source.raw (first.reindex morphism).code (second.reindex morphism).code) :=
  conclude (.substitutePredicateEquality source.raw target.raw morphism.substitution
    first.code second.code) ⟨morphism.admitted, same, trivial⟩

theorem assumptionArrow_natural {source target : Context D} (morphism : source ⟶ target)
    (first second : PredicateOver target)
    (same : Holds D (.predicateEq target.raw first.code second.code)) :
    rawAssumptionLift morphism first ≫ assumptionArrow first second same =
      assumptionArrow (first.reindex morphism) (second.reindex morphism)
        (assumptionEquation_reindex morphism same) ≫ rawAssumptionLift morphism second := by
  apply Hom.ext
  change composeSubstitution TermExpr.var morphism.substitution =
    composeSubstitution morphism.substitution TermExpr.var
  exact (identity_composeSubstitution morphism.substitution).trans
    (composeSubstitution_identity morphism.substitution).symm

namespace AssumptionModel

noncomputable def selectedPresentation (context : QuotientCwf.QContext D)
    (predicate : PredicateOver context.as) :
    selected context (QPredicate.mk predicate) ≅
      (quotientProjection D).obj (assumed context.as predicate) :=
  (quotientProjection D).mapIso (assumptionComparison (chosen (QPredicate.mk predicate)) predicate
    ((QPredicate.mk_eq_iff _ _).mp (chosen_class (QPredicate.mk predicate))))

theorem selectedPresentation_projection (context : QuotientCwf.QContext D)
    (predicate : PredicateOver context.as) :
    (selectedPresentation context predicate).hom ≫
      QuotientCwf.project (assumptionInclusion context.as predicate) =
        inclusion (QPredicate.mk predicate) := by
  let same := (QPredicate.mk_eq_iff _ _).mp (chosen_class (QPredicate.mk predicate))
  exact ((quotientProjection D).map_comp
    (assumptionArrow (chosen (QPredicate.mk predicate)) predicate same)
    (assumptionInclusion context.as predicate)).symm.trans
      (congrArg QuotientCwf.project (assumptionArrow_projection _ _ same))

end AssumptionModel
end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
