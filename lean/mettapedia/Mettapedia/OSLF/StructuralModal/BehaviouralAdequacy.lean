import Mettapedia.OSLF.StructuralModal.EquationInvariance
import Mettapedia.GSLT.Logic.HennessyMilnerDirections

/-!
# Adequacy of the behavioural structural-modal fragment

The behavioural fragment of the structural-modal language (no spatial former)
has a step-future diamond and a step-past box and no negation.  Over the
saturated span of a language it translates into the directional
Hennessy–Milner language with the same satisfaction, so bidirectionally
bisimilar terms satisfy the same behavioural formulas.  Its diamond-only part
is the negation-free forward language, whose logical preorder is the
simulation preorder under forward image-finiteness modulo the equations.
The fragment is not expressive enough for the converse of the first fact: it
has no forward box and no backward diamond, so it cannot separate every pair
of non-bisimilar terms, and no such claim is made.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.StructuralModal.BehaviouralAdequacy

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.StructuralModal
open Mettapedia.OSLF.StructuralModal.EquationInvariance

/-! ## The language span in relational form -/

theorem derivedDiamond_langSpanUsing_iff (relEnv : RelationEnv) (lang : LanguageDef)
    (predicate : Pattern → Prop) (term : Pattern) :
    derivedDiamond (langSpanUsing relEnv lang) predicate term ↔
      ∃ target, langSemanticReducesUsing relEnv lang term target ∧ predicate target := by
  constructor
  · rintro ⟨edge, sourceEq, holds⟩
    have sourceEq' : edge.val.1 = term := sourceEq
    refine ⟨edge.val.2, ?_, holds⟩
    rw [← sourceEq']
    exact edge.2
  · rintro ⟨target, step, holds⟩
    exact ⟨⟨(term, target), step⟩, rfl, holds⟩

theorem derivedBox_langSpanUsing_iff (relEnv : RelationEnv) (lang : LanguageDef)
    (predicate : Pattern → Prop) (term : Pattern) :
    derivedBox (langSpanUsing relEnv lang) predicate term ↔
      ∀ source, langSemanticReducesUsing relEnv lang source term → predicate source := by
  constructor
  · intro holds source step
    exact holds ⟨(source, term), step⟩ rfl
  · intro holds edge targetEq
    have targetEq' : edge.val.2 = term := targetEq
    apply holds
    rw [← targetEq']
    exact edge.2

/-! ## Translation of the behavioural fragment -/

/-- The empty observation set of a language. -/
def noObservations (relEnv : RelationEnv) (lang : LanguageDef) :
    ObservedGSLT.{0} (langGSLTUsing relEnv lang) :=
  ⟨PEmpty, fun atom _ => atom.elim⟩

/-- The directional system of a language with no atoms. -/
def languageDirectional (relEnv : RelationEnv) (lang : LanguageDef) :
    System.{0, 0} (langGSLTUsing relEnv lang) :=
  directional (noObservations relEnv lang) (fun atom => atom.elim)

/-- Behavioural structural-modal formulas as directional formulas. -/
def toDirectional : Formula → HennessyMilner.Formula PEmpty Direction
  | .top => .top
  | .bot => .neg .top
  | .and left right => .conj (toDirectional left) (toDirectional right)
  | .or left right => .neg (.conj (.neg (toDirectional left)) (.neg (toDirectional right)))
  | .headed _ _ => .top
  | .diamond inner => .dia .forward (toDirectional inner)
  | .box inner => .neg (.dia .backward (.neg (toDirectional inner)))

theorem sat_toDirectional (relEnv : RelationEnv) (lang : LanguageDef) {formula : Formula}
    (admissible : Admissible formula) (term : Pattern) :
    (languageDirectional relEnv lang).sat (toDirectional formula) term ↔
      satisfiesOver (langSpanUsing relEnv lang) formula term := by
  induction admissible generalizing term with
  | top => exact Iff.rfl
  | bot => simp [toDirectional, System.sat, satisfiesOver]
  | and _ _ leftIH rightIH =>
      exact and_congr (leftIH term) (rightIH term)
  | or _ _ leftIH rightIH =>
      show ¬ (¬ _ ∧ ¬ _) ↔ _ ∨ _
      rw [leftIH term, rightIH term]
      tauto
  | diamond _ innerIH =>
      show (∃ target, _ ∧ _) ↔ derivedDiamond _ _ _
      rw [derivedDiamond_langSpanUsing_iff]
      exact exists_congr fun target => and_congr Iff.rfl (innerIH target)
  | box _ innerIH =>
      show ¬ (∃ source, _ ∧ ¬ _) ↔ derivedBox _ _ _
      rw [derivedBox_langSpanUsing_iff]
      constructor
      · intro holds source step
        by_contra fails
        exact holds ⟨source, step, fun sat => fails ((innerIH source).mp sat)⟩
      · rintro holds ⟨source, step, fails⟩
        exact fails ((innerIH source).mpr (holds source step))

/-- Behavioural equivalence: the same admissible formulas hold. -/
def BehaviourallyEquivalent (relEnv : RelationEnv) (lang : LanguageDef) (left right : Pattern) :
    Prop :=
  ∀ formula : Formula, Admissible formula →
    (satisfiesOver (langSpanUsing relEnv lang) formula left ↔
      satisfiesOver (langSpanUsing relEnv lang) formula right)

/-- Soundness: bidirectionally bisimilar terms satisfy the same behavioural
formulas. -/
theorem behaviourallyEquivalent_of_bisimilar (relEnv : RelationEnv) (lang : LanguageDef)
    {left right : Pattern} (bisimilar : (languageDirectional relEnv lang).Bisimilar left right) :
    BehaviourallyEquivalent relEnv lang left right := by
  intro formula admissible
  rw [← sat_toDirectional relEnv lang admissible left, ← sat_toDirectional relEnv lang admissible right]
  exact System.logicallyEquivalent_of_bisimilar _ bisimilar _

/-! ## The diamond-only fragment and the simulation preorder -/

/-- Formulas built from truth, falsity, conjunction, disjunction, and the
step-future diamond. -/
inductive Positive : Formula → Prop
  | top : Positive .top
  | bot : Positive .bot
  | and {left right : Formula} : Positive left → Positive right → Positive (.and left right)
  | or {left right : Formula} : Positive left → Positive right → Positive (.or left right)
  | diamond {inner : Formula} : Positive inner → Positive (.diamond inner)

theorem admissible_of_positive {formula : Formula} (positive : Positive formula) :
    Admissible formula := by
  induction positive with
  | top => exact .top
  | bot => exact .bot
  | and _ _ leftIH rightIH => exact .and leftIH rightIH
  | or _ _ leftIH rightIH => exact .or leftIH rightIH
  | diamond _ innerIH => exact .diamond innerIH

/-- The forward system of a language with no atoms. -/
def languageForward (relEnv : RelationEnv) (lang : LanguageDef) :
    System.{0, 0} (langGSLTUsing relEnv lang) :=
  System.ofObserved (noObservations relEnv lang) (fun atom => atom.elim)

/-- Positive formulas as negation-free forward formulas. -/
def toPositive : Formula → PosFormula PEmpty Unit
  | .top => .top
  | .bot => .bot
  | .and left right => .conj (toPositive left) (toPositive right)
  | .or left right => .disj (toPositive left) (toPositive right)
  | .headed _ _ => .top
  | .diamond inner => .dia () (toPositive inner)
  | .box _ => .top

theorem psat_toPositive (relEnv : RelationEnv) (lang : LanguageDef) {formula : Formula}
    (positive : Positive formula) (term : Pattern) :
    (languageForward relEnv lang).psat (toPositive formula) term ↔
      satisfiesOver (langSpanUsing relEnv lang) formula term := by
  induction positive generalizing term with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | and _ _ leftIH rightIH => exact and_congr (leftIH term) (rightIH term)
  | or _ _ leftIH rightIH => exact or_congr (leftIH term) (rightIH term)
  | diamond _ innerIH =>
      show (∃ target, _ ∧ _) ↔ derivedDiamond _ _ _
      rw [derivedDiamond_langSpanUsing_iff]
      exact exists_congr fun target => and_congr Iff.rfl (innerIH target)

/-- Negation-free forward formulas as positive structural-modal formulas. -/
def ofPositive : PosFormula PEmpty Unit → Formula
  | .top => .top
  | .bot => .bot
  | .atom atom => atom.elim
  | .conj left right => .and (ofPositive left) (ofPositive right)
  | .disj left right => .or (ofPositive left) (ofPositive right)
  | .dia _ inner => .diamond (ofPositive inner)

theorem positive_ofPositive : ∀ formula : PosFormula PEmpty Unit, Positive (ofPositive formula)
  | .top => .top
  | .bot => .bot
  | .atom atom => atom.elim
  | .conj left right => .and (positive_ofPositive left) (positive_ofPositive right)
  | .disj left right => .or (positive_ofPositive left) (positive_ofPositive right)
  | .dia _ inner => .diamond (positive_ofPositive inner)

theorem satisfiesOver_ofPositive (relEnv : RelationEnv) (lang : LanguageDef) :
    ∀ (formula : PosFormula PEmpty Unit) (term : Pattern),
      satisfiesOver (langSpanUsing relEnv lang) (ofPositive formula) term ↔
        (languageForward relEnv lang).psat formula term
  | .top, _ => Iff.rfl
  | .bot, _ => Iff.rfl
  | .atom atom, _ => atom.elim
  | .conj left right, term =>
      and_congr (satisfiesOver_ofPositive relEnv lang left term)
        (satisfiesOver_ofPositive relEnv lang right term)
  | .disj left right, term =>
      or_congr (satisfiesOver_ofPositive relEnv lang left term)
        (satisfiesOver_ofPositive relEnv lang right term)
  | .dia _ inner, term => by
      show derivedDiamond _ _ _ ↔ ∃ target, _ ∧ _
      rw [derivedDiamond_langSpanUsing_iff]
      exact exists_congr fun target =>
        and_congr Iff.rfl (satisfiesOver_ofPositive relEnv lang inner target)

/-- The positive logical preorder: every positive formula true on the left
is true on the right. -/
def PositivePreorder (relEnv : RelationEnv) (lang : LanguageDef) (left right : Pattern) : Prop :=
  ∀ formula : Formula, Positive formula →
    satisfiesOver (langSpanUsing relEnv lang) formula left →
      satisfiesOver (langSpanUsing relEnv lang) formula right

theorem positivePreorder_iff_logicalPreorder (relEnv : RelationEnv) (lang : LanguageDef)
    (left right : Pattern) :
    PositivePreorder relEnv lang left right ↔
      (languageForward relEnv lang).LogicalPreorder left right := by
  constructor
  · intro ordered formula holds
    rw [← satisfiesOver_ofPositive relEnv lang formula right]
    exact ordered _ (positive_ofPositive formula)
      ((satisfiesOver_ofPositive relEnv lang formula left).mpr holds)
  · intro ordered formula positive holds
    rw [← psat_toPositive relEnv lang positive right]
    exact ordered _ ((psat_toPositive relEnv lang positive left).mpr holds)

/-- The diamond-only fragment characterizes the simulation preorder under
forward image-finiteness modulo the equations. -/
theorem positivePreorder_iff_similar (relEnv : RelationEnv) (lang : LanguageDef)
    (finite : (languageForward relEnv lang).ImageFiniteModulo) (left right : Pattern) :
    PositivePreorder relEnv lang left right ↔ (languageForward relEnv lang).Similar left right :=
  (positivePreorder_iff_logicalPreorder relEnv lang left right).trans
    (System.logicalPreorder_iff_similar _ finite left right)

end Mettapedia.OSLF.StructuralModal.BehaviouralAdequacy
