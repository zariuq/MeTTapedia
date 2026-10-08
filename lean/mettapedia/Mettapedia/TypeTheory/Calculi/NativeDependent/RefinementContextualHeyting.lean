import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualLogic
import Mathlib.Order.Heyting.Basic

/-!
# Heyting operations in the generated predicate doctrine

The lattice and implication laws are derived from the generated introduction,
elimination and extensionality rules. Entailment is exactly equality with the
top predicate. Substitution preserves these operations through the actual
simultaneous syntax substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Logic

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

def inAssumption {context : Context D} (first second : PredicateOver context) :
    PredicateOver (assumed context first) := ⟨second.code, predicate_weaken first second⟩

theorem entails_weaken {context : Context D} (assumption : PredicateOver context)
    {code : PropExpr S context.arity} (evidence : Holds D (.entails context.raw code)) :
    Holds D (.entails (assumed context assumption).raw code) := by
  have transported := conclude (.substituteEntailment (assumed context assumption).raw context.raw
    TermExpr.var code) ⟨(assumptionInclusion context assumption).admitted, evidence, trivial⟩
  change Holds D (.entails (assumed context assumption).raw (code.substitute TermExpr.var)) at transported
  simpa only [PropExpr.substitute_identity] using transported

theorem apply_order_identity {target : Context D} {first second : PredicateOver target}
    (consequence : RawOrder first second) (source : ContextExpr S target.arity)
    (admitted : Holds D (.substitution source target.raw TermExpr.var))
    (guard : Holds D (.entails source first.code)) :
    Holds D (.entails source second.code) := by
  have substitutedGuard : Holds D (.entails source (first.code.substitute TermExpr.var)) := by
    simpa only [PropExpr.substitute_identity] using guard
  have selected := conclude (.substitutionIntoAssumption source target.raw first.code TermExpr.var)
    ⟨admitted, first.formed, substitutedGuard, trivial⟩
  have transported := conclude (.substituteEntailment source (.assume target.raw first.code)
    TermExpr.var second.code) ⟨selected, consequence, trivial⟩
  change Holds D (.entails source (second.code.substitute TermExpr.var)) at transported
  simpa only [PropExpr.substitute_identity] using transported

theorem order_extra_assumption {context : Context D} {first second : PredicateOver context}
    (consequence : RawOrder first second) (extra : PredicateOver context) :
    RawOrder (inAssumption extra first) (inAssumption extra second) := by
  have lifted := conclude (.substitutionAssumptionLift (assumed context extra).raw context.raw
    first.code TermExpr.var) ⟨(assumptionInclusion context extra).admitted, first.formed, trivial⟩
  change Holds D (.substitution
    (.assume (assumed context extra).raw (first.code.substitute TermExpr.var))
    (.assume context.raw first.code) TermExpr.var) at lifted
  rw [PropExpr.substitute_identity] at lifted
  have transported := conclude (.substituteEntailment
    (.assume (assumed context extra).raw first.code) (.assume context.raw first.code)
    TermExpr.var second.code) ⟨lifted, consequence, trivial⟩
  change Holds D (.entails (.assume (assumed context extra).raw first.code)
    (second.code.substitute TermExpr.var)) at transported
  change Holds D (.entails (.assume (assumed context extra).raw first.code) second.code)
  simpa only [PropExpr.substitute_identity] using transported

theorem raw_meet_left {context : Context D} (first second : PredicateOver context) :
    RawOrder (conjunction first second) first :=
  conclude (.conjunctionFirst (assumed context (conjunction first second)).raw first.code second.code)
    ⟨predicate_weaken (conjunction first second) first,
      predicate_weaken (conjunction first second) second, hypothesis (conjunction first second), trivial⟩

theorem raw_meet_right {context : Context D} (first second : PredicateOver context) :
    RawOrder (conjunction first second) second :=
  conclude (.conjunctionSecond (assumed context (conjunction first second)).raw first.code second.code)
    ⟨predicate_weaken (conjunction first second) first,
      predicate_weaken (conjunction first second) second, hypothesis (conjunction first second), trivial⟩

theorem raw_le_meet {context : Context D} {first second third : PredicateOver context}
    (left : RawOrder first second) (right : RawOrder first third) :
    RawOrder first (conjunction second third) :=
  conclude (.conjunctionIntroduction (assumed context first).raw second.code third.code)
    ⟨left, right, trivial⟩

theorem raw_le_join_left {context : Context D} (first second : PredicateOver context) :
    RawOrder first (disjunction first second) :=
  conclude (.disjunctionFirst (assumed context first).raw first.code second.code)
    ⟨predicate_weaken first first, predicate_weaken first second, hypothesis first, trivial⟩

theorem raw_le_join_right {context : Context D} (first second : PredicateOver context) :
    RawOrder second (disjunction first second) :=
  conclude (.disjunctionSecond (assumed context second).raw first.code second.code)
    ⟨predicate_weaken second first, predicate_weaken second second, hypothesis second, trivial⟩

theorem raw_join_le {context : Context D} {first second third : PredicateOver context}
    (left : RawOrder first third) (right : RawOrder second third) :
    RawOrder (disjunction first second) third :=
  conclude (.disjunctionElimination (assumed context (disjunction first second)).raw
    first.code second.code third.code)
    ⟨predicate_weaken (disjunction first second) first,
      predicate_weaken (disjunction first second) second,
      predicate_weaken (disjunction first second) third,
      hypothesis (disjunction first second),
      order_extra_assumption left (disjunction first second),
      order_extra_assumption right (disjunction first second), trivial⟩

theorem raw_le_truth {context : Context D} (predicate : PredicateOver context) :
    RawOrder predicate (truth context) :=
  conclude (.truthIntroduction (assumed context predicate).raw)
    ⟨(assumed context predicate).formed.judgment, trivial⟩

theorem raw_falsehood_le {context : Context D} (predicate : PredicateOver context) :
    RawOrder (falsehood context) predicate :=
  conclude (.falsehoodElimination (assumed context (falsehood context)).raw predicate.code)
    ⟨predicate_weaken (falsehood context) predicate, hypothesis (falsehood context), trivial⟩

theorem raw_himp_adjoint {context : Context D} (first second third : PredicateOver context) :
    RawOrder first (implication second third) ↔ RawOrder (conjunction first second) third := by
  constructor
  · intro conditional
    have liftedConditional := apply_order_identity conditional
      (assumed context (conjunction first second)).raw
      (assumptionInclusion context (conjunction first second)).admitted (raw_meet_left first second)
    exact conclude (.implicationElimination (assumed context (conjunction first second)).raw
      second.code third.code)
      ⟨predicate_weaken (conjunction first second) second,
        predicate_weaken (conjunction first second) third,
        liftedConditional, raw_meet_right first second, trivial⟩
  · intro consequence
    let secondInFirst := inAssumption first second
    let nested := assumed (assumed context first) secondInFirst
    let base : nested ⟶ context :=
      assumptionInclusion (assumed context first) secondInFirst ≫ assumptionInclusion context first
    have baseTuple : base.substitution = TermExpr.var := by
      change (assumptionInclusion (assumed context first) secondInFirst ≫
        assumptionInclusion context first).substitution = TermExpr.var
      rw [assumptionInclusion_substitution]
      rfl
    have combined : Holds D (.entails nested.raw (.and first.code second.code)) :=
      conclude (.conjunctionIntroduction nested.raw first.code second.code)
        ⟨entails_weaken secondInFirst (hypothesis first), hypothesis secondInFirst, trivial⟩
    have baseAdmission := base.admitted
    rw [baseTuple] at baseAdmission
    have final := apply_order_identity consequence nested.raw baseAdmission combined
    exact conclude (.implicationIntroduction (assumed context first).raw second.code third.code)
      ⟨predicate_weaken first second, predicate_weaken first third, final, trivial⟩

instance predicateLattice (context : Context D) : Lattice (QPredicate context) where
  inf := meet
  inf_le_left first second := by
    refine _root_.Quotient.inductionOn₂ first second fun left right => ?_
    exact raw_meet_left left right
  inf_le_right first second := by
    refine _root_.Quotient.inductionOn₂ first second fun left right => ?_
    exact raw_meet_right left right
  le_inf first second third := by
    refine _root_.Quotient.inductionOn₃ first second third fun _ _ _ => ?_
    exact raw_le_meet
  sup := join
  le_sup_left first second := by
    refine _root_.Quotient.inductionOn₂ first second fun left right => ?_
    exact raw_le_join_left left right
  le_sup_right first second := by
    refine _root_.Quotient.inductionOn₂ first second fun left right => ?_
    exact raw_le_join_right left right
  sup_le first second third := by
    refine _root_.Quotient.inductionOn₃ first second third fun _ _ _ => ?_
    exact raw_join_le

instance predicateOrderTop (context : Context D) : OrderTop (QPredicate context) where
  top := QPredicate.mk (truth context)
  le_top predicate := by
    refine _root_.Quotient.inductionOn predicate fun formed => ?_
    exact raw_le_truth formed

instance predicateHeytingAlgebra (context : Context D) : HeytingAlgebra (QPredicate context) where
  himp := conditional
  le_himp_iff first second third := by
    refine _root_.Quotient.inductionOn₃ first second third fun left middle right => ?_
    exact raw_himp_adjoint left middle right
  bot := QPredicate.mk (falsehood context)
  bot_le predicate := by
    refine _root_.Quotient.inductionOn predicate fun formed => ?_
    exact raw_falsehood_le formed
  compl predicate := conditional predicate (QPredicate.mk (falsehood context))
  himp_bot _ := rfl

theorem raw_truth_le_iff {context : Context D} (predicate : PredicateOver context) :
    RawOrder (truth context) predicate ↔ Holds D (.entails context.raw predicate.code) := by
  constructor
  · intro conditional
    exact apply_order_identity conditional context.raw
      (conclude (.substitutionIdentity context.raw) ⟨context.formed.judgment, trivial⟩)
      (conclude (.truthIntroduction context.raw) ⟨context.formed.judgment, trivial⟩)
  · exact entails_weaken (truth context)

theorem entails_iff_top_le {context : Context D} (predicate : QPredicate context) :
    predicate.entails ↔ ⊤ ≤ predicate := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact (raw_truth_le_iff formed).symm

theorem entails_iff_eq_top {context : Context D} (predicate : QPredicate context) :
    predicate.entails ↔ predicate = ⊤ := by
  rw [entails_iff_top_le, top_le_iff]

theorem top_reindex {source target : Context D} (morphism : source ⟶ target) :
    (⊤ : QPredicate target).reindex morphism = ⊤ := rfl

theorem bot_reindex {source target : Context D} (morphism : source ⟶ target) :
    (⊥ : QPredicate target).reindex morphism = ⊥ := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Logic
