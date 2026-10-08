import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicates

/-!
# Logical consequence in the generated predicate doctrine

The order between predicate classes is actual generated entailment under the
antecedent assumption. Implication introduction and elimination give its
equivalent judgment in the original context. Predicate extensionality makes
this order antisymmetric. Reindexing uses the typed assumption lift, including
the complete substituted guard.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Logic

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

def truth (context : Context D) : PredicateOver context :=
  ⟨.truth, conclude (.truthFormation context.raw) ⟨context.formed.judgment, trivial⟩⟩

def falsehood (context : Context D) : PredicateOver context :=
  ⟨.falsehood, conclude (.falsehoodFormation context.raw) ⟨context.formed.judgment, trivial⟩⟩

def conjunction {context : Context D} (first second : PredicateOver context) : PredicateOver context :=
  ⟨.and first.code second.code,
    conclude (.conjunctionFormation context.raw first.code second.code) ⟨first.formed, second.formed, trivial⟩⟩

def disjunction {context : Context D} (first second : PredicateOver context) : PredicateOver context :=
  ⟨.or first.code second.code,
    conclude (.disjunctionFormation context.raw first.code second.code) ⟨first.formed, second.formed, trivial⟩⟩

def implication {context : Context D} (first second : PredicateOver context) : PredicateOver context :=
  ⟨.implies first.code second.code,
    conclude (.implicationFormation context.raw first.code second.code) ⟨first.formed, second.formed, trivial⟩⟩

abbrev RawOrder {context : Context D} (first second : PredicateOver context) : Prop :=
  Holds D (.entails (assumed context first).raw second.code)

theorem hypothesis {context : Context D} (predicate : PredicateOver context) :
    Holds D (.entails (assumed context predicate).raw predicate.code) := by
  have supplied := selectedGuard predicate (𝟙 (assumed context predicate))
  change Holds D (.entails (assumed context predicate).raw
    (predicate.code.substitute TermExpr.var)) at supplied
  simpa only [PropExpr.substitute_identity] using supplied

theorem predicate_weaken {context : Context D} (first second : PredicateOver context) :
    Holds D (.predicate (assumed context first).raw second.code) := by
  have supplied := (second.reindex (assumptionInclusion context first)).formed
  change Holds D (.predicate (assumed context first).raw
    (second.code.substitute TermExpr.var)) at supplied
  simpa only [PropExpr.substitute_identity] using supplied

theorem order_iff_implication {context : Context D} (first second : PredicateOver context) :
    RawOrder first second ↔ Holds D (.entails context.raw (implication first second).code) := by
  constructor
  · intro consequence
    exact conclude (.implicationIntroduction context.raw first.code second.code)
      ⟨first.formed, second.formed, consequence, trivial⟩
  · intro conditional
    have weakened : Holds D (.entails (assumed context first).raw (.implies first.code second.code)) := by
      simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
        conclude (.substituteEntailment (assumed context first).raw context.raw TermExpr.var
          (.implies first.code second.code))
          ⟨(assumptionInclusion context first).admitted, conditional, trivial⟩
    exact conclude (.implicationElimination (assumed context first).raw first.code second.code)
      ⟨predicate_weaken first first, predicate_weaken first second, weakened, hypothesis first, trivial⟩

theorem order_respects {context : Context D} {first first' second second' : PredicateOver context}
    (antecedents : Holds D (.predicateEq context.raw first.code first'.code))
    (consequents : Holds D (.predicateEq context.raw second.code second'.code)) :
    RawOrder first second ↔ RawOrder first' second' := by
  have equal := conclude (.implicationCongruence context.raw first.code first'.code second.code second'.code)
    ⟨antecedents, consequents, trivial⟩
  rw [order_iff_implication, order_iff_implication]
  constructor
  · intro evidence
    exact conclude (.entailmentConversion context.raw (implication first second).code
      (implication first' second').code) ⟨equal, evidence, trivial⟩
  · intro evidence
    exact conclude (.entailmentConversion context.raw (implication first' second').code
      (implication first second).code) ⟨predicateEquality_symm equal, evidence, trivial⟩

/-- Conditional evidence is applied along a supplied typed base substitution
and its actual pulled antecedent guard. -/
theorem apply_order {source target : Context D} {first second : PredicateOver target}
    (consequence : RawOrder first second) (morphism : source ⟶ target)
    (guard : Holds D (.entails source.raw (first.code.substitute morphism.substitution))) :
    Holds D (.entails source.raw (second.code.substitute morphism.substitution)) :=
  conclude (.substituteEntailment source.raw (assumed target first).raw
    (select first morphism guard).substitution second.code)
    ⟨(select first morphism guard).admitted, consequence, trivial⟩

theorem order_refl {context : Context D} (predicate : PredicateOver context) :
    RawOrder predicate predicate := hypothesis predicate

theorem order_trans {context : Context D} {first middle last : PredicateOver context}
    (earlier : RawOrder first middle) (later : RawOrder middle last) : RawOrder first last := by
  have guard : Holds D (.entails (assumed context first).raw
      (middle.code.substitute (assumptionInclusion context first).substitution)) := by
    simpa only [assumptionInclusion, PropExpr.substitute_identity] using earlier
  simpa only [assumptionInclusion, PropExpr.substitute_identity] using
    apply_order later (assumptionInclusion context first) guard

theorem order_antisymm {context : Context D} {first second : PredicateOver context}
    (forward : RawOrder first second) (backward : RawOrder second first) :
    Holds D (.predicateEq context.raw first.code second.code) :=
  conclude (.predicateExtensionality context.raw first.code second.code)
    ⟨first.formed, second.formed, forward, backward, trivial⟩

theorem order_reindex {source target : Context D} {first second : PredicateOver target}
    (consequence : RawOrder first second) (morphism : source ⟶ target) :
    RawOrder (first.reindex morphism) (second.reindex morphism) := by
  have lifted := conclude (.substitutionAssumptionLift source.raw target.raw first.code morphism.substitution)
    ⟨morphism.admitted, first.formed, trivial⟩
  exact conclude (.substituteEntailment (assumed source (first.reindex morphism)).raw
    (assumed target first).raw morphism.substitution second.code) ⟨lifted, consequence, trivial⟩

def order {context : Context D} (first second : QPredicate context) : Prop :=
  _root_.Quotient.liftOn₂ first second (fun left right => RawOrder left right)
    (fun _ _ _ _ antecedents consequents => propext (order_respects antecedents consequents))

instance predicatePartialOrder (context : Context D) : PartialOrder (QPredicate context) where
  le := order
  le_refl predicate := by
    refine _root_.Quotient.inductionOn predicate fun formed => ?_
    exact order_refl formed
  le_trans first middle last := by
    refine _root_.Quotient.inductionOn₃ first middle last fun _ _ _ => ?_
    exact order_trans
  le_antisymm first second := by
    refine _root_.Quotient.inductionOn₂ first second fun _ _ => ?_
    intro forward backward
    exact _root_.Quotient.sound (order_antisymm forward backward)

theorem mk_le_mk {context : Context D} (first second : PredicateOver context) :
    QPredicate.mk first ≤ QPredicate.mk second ↔ RawOrder first second := Iff.rfl

theorem reindex_monotone {source target : Context D} (morphism : source ⟶ target) :
    Monotone (fun predicate : QPredicate target => predicate.reindex morphism) := by
  intro first second
  refine _root_.Quotient.inductionOn₂ first second fun _ _ => ?_
  exact fun evidence => order_reindex evidence morphism

def meet {context : Context D} (first second : QPredicate context) : QPredicate context :=
  _root_.Quotient.liftOn₂ first second (fun left right => QPredicate.mk (conjunction left right))
    (fun _ _ _ _ left right => _root_.Quotient.sound
      (conclude (.conjunctionCongruence context.raw _ _ _ _) ⟨left, right, trivial⟩))

def join {context : Context D} (first second : QPredicate context) : QPredicate context :=
  _root_.Quotient.liftOn₂ first second (fun left right => QPredicate.mk (disjunction left right))
    (fun _ _ _ _ left right => _root_.Quotient.sound
      (conclude (.disjunctionCongruence context.raw _ _ _ _) ⟨left, right, trivial⟩))

def conditional {context : Context D} (first second : QPredicate context) : QPredicate context :=
  _root_.Quotient.liftOn₂ first second (fun left right => QPredicate.mk (implication left right))
    (fun _ _ _ _ left right => _root_.Quotient.sound
      (conclude (.implicationCongruence context.raw _ _ _ _) ⟨left, right, trivial⟩))

theorem meet_reindex {source target : Context D} (morphism : source ⟶ target)
    (first second : QPredicate target) :
    (meet first second).reindex morphism = meet (first.reindex morphism) (second.reindex morphism) := by
  refine _root_.Quotient.inductionOn₂ first second fun _ _ => rfl

theorem join_reindex {source target : Context D} (morphism : source ⟶ target)
    (first second : QPredicate target) :
    (join first second).reindex morphism = join (first.reindex morphism) (second.reindex morphism) := by
  refine _root_.Quotient.inductionOn₂ first second fun _ _ => rfl

theorem conditional_reindex {source target : Context D} (morphism : source ⟶ target)
    (first second : QPredicate target) :
    (conditional first second).reindex morphism =
      conditional (first.reindex morphism) (second.reindex morphism) := by
  refine _root_.Quotient.inductionOn₂ first second fun _ _ => rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Logic
