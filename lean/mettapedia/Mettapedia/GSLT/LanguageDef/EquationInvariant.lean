import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Quantities the static equivalence preserves

Two terms are shown inequivalent by a quantity that every equation step
preserves and that differs on them.  This module supplies the general
principle, and one family of quantities: the weight of a term, the sum of a
chosen weight over its constructor occurrences.

A weight is preserved by the equivalence of a presentation when

* each authored equation, under every substitution, has sides of equal
  weight;
* the presentation has no set collection, whose idempotence law deletes an
  element;
* every declared collection unit has weight zero.

Authored equations are reduced to their two sides under one substitution when
they carry no premise and their sides are matched exactly.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

open Mettapedia.OSLF.MeTTaIL.DerivedContexts

mutual
  /-- The sum of a weight over the constructor occurrences of a pattern. -/
  def weigh (weight : String → Nat) : Pattern → Nat
    | .bvar _ => 0
    | .fvar _ => 0
    | .apply label arguments => weight label + weighList weight arguments
    | .lambda _ body => weigh weight body
    | .multiLambda _ _ body => weigh weight body
    | .subst body replacement => weigh weight body + weigh weight replacement
    | .collection _ elements _ => weighList weight elements

  /-- The total weight of a list of patterns. -/
  def weighList (weight : String → Nat) : List Pattern → Nat
    | [] => 0
    | pattern :: patterns => weigh weight pattern + weighList weight patterns
end

@[simp] theorem weighList_append (weight : String → Nat) (first second : List Pattern) :
    weighList weight (first ++ second) = weighList weight first + weighList weight second := by
  induction first with
  | nil => simp [weighList]
  | cons head tail recurse => simp [weighList, recurse, Nat.add_assoc]

/-- Weight does not see the order of a list. -/
theorem weighList_perm (weight : String → Nat) {first second : List Pattern}
    (permutation : List.Perm first second) :
    weighList weight first = weighList weight second := by
  induction permutation with
  | nil => rfl
  | cons head _ recurse => simp [weighList, recurse]
  | swap first second tail => simp [weighList]; omega
  | trans _ _ firstStep secondStep => exact firstStep.trans secondStep

/-- Weight is compositional: a context sees only the weight of what fills
its hole. -/
theorem weigh_fill_congr (weight : String → Nat) :
    ∀ (context : OneHoleContext) {first second : Pattern},
      weigh weight first = weigh weight second →
        weigh weight (context.fill first) = weigh weight (context.fill second)
  | .hole, _, _, same => same
  | .apply label before inner after, _, _, same => by
      simp [OneHoleContext.fill, weigh, weighList, weigh_fill_congr weight inner same]
  | .lambda _ inner, _, _, same => by
      simp [OneHoleContext.fill, weigh, weigh_fill_congr weight inner same]
  | .multiLambda _ _ inner, _, _, same => by
      simp [OneHoleContext.fill, weigh, weigh_fill_congr weight inner same]
  | .substBody inner replacement, _, _, same => by
      simp [OneHoleContext.fill, weigh, weigh_fill_congr weight inner same]
  | .substReplacement body inner, _, _, same => by
      simp [OneHoleContext.fill, weigh, weigh_fill_congr weight inner same]
  | .collection _ before inner after _, _, _, same => by
      simp [OneHoleContext.fill, weigh, weighList, weigh_fill_congr weight inner same]

end Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

namespace Mettapedia.GSLT.LanguageDef.EquationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

variable {base : BasePremiseEvaluator} {language : LanguageDef}

/-- **Invariants.**  A quantity that contexts respect and every generator of
the equation theory preserves is equal on equivalent terms. -/
theorem equationEquiv_invariant {α : Type*} (measure : Pattern → α)
    (contexts : ∀ (context : OneHoleContext) (first second : Pattern),
      measure first = measure second →
        measure (context.fill first) = measure (context.fill second))
    (generators : ∀ source target, EquationGenerator base language source target →
      measure source = measure target)
    {left right : Pattern} (equivalent : EquationEquiv base language left right) :
    measure left = measure right := by
  induction equivalent with
  | rel left right step =>
      cases step with
      | inContext context generator =>
          exact contexts context _ _ (generators _ _ generator)
  | refl pattern => rfl
  | symm left right _ recurse => exact recurse.symm
  | trans left middle right _ _ first second => exact first.trans second

/-- The authored equations carry no premise and are matched exactly. -/
def PlainEquations (language : LanguageDef) : Prop :=
  ∀ equation : Equation, List.Mem equation language.equations →
    equation.premises = [] ∧ Pattern.isMatchCorrect equation.left = true ∧
      Pattern.isMatchCorrect equation.right = true

/-- An instance of a plain equation is its two sides under one substitution,
read in one of the two directions. -/
theorem equationInstance_sides (plain : PlainEquations language)
    {source target : Pattern}
    (authored : EquationInstance base language source target) :
    ∃ equation : Equation, List.Mem equation language.equations ∧
      ∃ bindings : Bindings,
        (source = applyBindings bindings equation.left ∧
            target = applyBindings bindings equation.right) ∨
          (source = applyBindings bindings equation.right ∧
            target = applyBindings bindings equation.left) := by
  obtain ⟨fuel, authored⟩ := authored
  cases authored with
  | @forward equation _ _ initial final membership matched premises applied =>
      obtain ⟨premiseFree, leftCorrect, -⟩ := plain equation membership
      rw [premiseFree] at premises
      cases premises
      exact ⟨equation, membership, initial,
        Or.inl ⟨(matchPattern_correct matched leftCorrect).symm, applied.symm⟩⟩
  | @reverse equation _ _ initial final membership matched premises applied =>
      obtain ⟨premiseFree, -, rightCorrect⟩ := plain equation membership
      rw [premiseFree] at premises
      cases premises
      exact ⟨equation, membership, initial,
        Or.inr ⟨(matchPattern_correct matched rightCorrect).symm, applied.symm⟩⟩

/-- A presentation-derived law preserves a weight when the presentation has
no set collection and its declared units weigh nothing. -/
theorem derivedInstance_weigh (weight : String → Nat)
    (noSets : language.usesCollection .hashSet = false)
    (units : ∀ rule ∈ language.terms, ∀ algebra, rule.algebra? = some algebra →
      ∀ unit, algebra.unit = some unit → weight unit = 0)
    {source target : Pattern} (derived : DerivedInstance language source target) :
    source.weigh weight = target.weigh weight := by
  cases derived with
  | bagPerm _ _ permutation =>
      simp [Pattern.weigh, Pattern.weighList_perm weight permutation]
  | setPerm declaration _ _ =>
      have uses := usesCollection_eq_true_of_collectionCarrierRule declaration
      rw [noSets] at uses
      cases uses
  | setDedup declaration _ =>
      have uses := usesCollection_eq_true_of_collectionCarrierRule declaration
      rw [noSets] at uses
      cases uses
  | flatten _ _ _ => simp [Pattern.weigh, Pattern.weighList]
  | singleton _ _ _ => simp [Pattern.weigh, Pattern.weighList]
  | unitElim algebraRule declaredUnit _ =>
      have weightless :=
        units _ algebraRule.authored _ algebraRule.declared _ declaredUnit
      simp [Pattern.weigh, Pattern.weighList, weightless]
  | emptyUnit algebraRule declaredUnit _ =>
      have weightless :=
        units _ algebraRule.authored _ algebraRule.declared _ declaredUnit
      simp [Pattern.weigh, Pattern.weighList, weightless]

/-- **A weight the equations preserve separates terms.**  Equivalent terms
have equal weight. -/
theorem equationEquiv_weigh (weight : String → Nat)
    (plain : PlainEquations language)
    (noSets : language.usesCollection .hashSet = false)
    (units : ∀ rule ∈ language.terms, ∀ algebra, rule.algebra? = some algebra →
      ∀ unit, algebra.unit = some unit → weight unit = 0)
    (laws : ∀ equation : Equation, List.Mem equation language.equations →
      ∀ bindings : Bindings,
        (applyBindings bindings equation.left).weigh weight =
          (applyBindings bindings equation.right).weigh weight)
    {left right : Pattern} (equivalent : EquationEquiv base language left right) :
    left.weigh weight = right.weigh weight := by
  apply equationEquiv_invariant (Pattern.weigh weight)
    (fun context _ _ same => Pattern.weigh_fill_congr weight context same) _ equivalent
  rintro source target (authored | derived)
  · obtain ⟨equation, membership, bindings, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
      equationInstance_sides plain authored
    · exact laws equation membership bindings
    · exact (laws equation membership bindings).symm
  · exact derivedInstance_weigh weight noSets units derived

end Mettapedia.GSLT.LanguageDef.EquationSemantics
