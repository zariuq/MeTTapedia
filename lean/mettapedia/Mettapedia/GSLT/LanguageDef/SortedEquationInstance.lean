import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Equation instances that respect the equation's own type context

An authored equation carries a type context: it declares, for each of its
schema variables, the sort the variable ranges over.  The instance relation that
generates a presentation's equation theory does not read that context.  It
matches a side of the equation against a term with the ordinary pattern matcher,
so a variable declared to range over one sort is instantiated by any pattern at
all, and the generated theory can relate terms of different sorts.

This module supplies the disciplined relation beside the permissive one: a
*sorted* instance is an instance whose substitution puts, at each variable the
equation declares, a pattern of the declared type.  Everything is stated so that
the two live side by side — the sorted theory is contained in the generated one
(`equationEquiv_of_sortedEquationEquiv`), so every negative proved about the
sorted theory is a statement about the discipline and not about a different
presentation.

The point of the discipline is that invariants survive it.  A predicate
respected by every sorted generator in every context is respected by the whole
sorted theory (`sortedEquationEquiv_invariant`), which is what a frame of
predicates needs and what the permissive theory does not give.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.EquationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- **The discipline.**  At every variable the equation's own type context
declares, the substitution puts a *term* of the declared type: an object
pattern, so neither a pending explicit substitution nor an open collection
tail, and sorted at the declared type by the presentation's own grammar. -/
def SortedBindings (language : LanguageDef)
    (typeContext : List (String × TypeExpr)) (bindings : Bindings) : Prop :=
  ∀ name type, (name, type) ∈ typeContext →
    WellSorted.isObjectPattern (applyBindings bindings (.fvar name)) = true ∧
      WellSorted.HasType language WellSorted.FreeTypeContext.empty []
        (applyBindings bindings (.fvar name)) type

/-- An authored equation instance that respects the equation's type context. -/
inductive SortedEquationInstanceAt
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Nat → Pattern → Pattern → Prop where
  | forward
      {fuel : Nat} {equation : Equation} {source target : Pattern}
      {initialBindings finalBindings : Bindings} :
      List.Mem equation language.equations →
      initialBindings ∈ matchPattern equation.left source →
      PremisesAt base language fuel initialBindings equation.premises
        finalBindings →
      SortedBindings language equation.typeContext finalBindings →
      applyBindings finalBindings equation.right = target →
      SortedEquationInstanceAt base language fuel source target
  | reverse
      {fuel : Nat} {equation : Equation} {source target : Pattern}
      {initialBindings finalBindings : Bindings} :
      List.Mem equation language.equations →
      initialBindings ∈ matchPattern equation.right source →
      PremisesAt base language fuel initialBindings equation.premises
        finalBindings →
      SortedBindings language equation.typeContext finalBindings →
      applyBindings finalBindings equation.left = target →
      SortedEquationInstanceAt base language fuel source target

/-- A sorted instance has some finite premise-derivation depth. -/
def SortedEquationInstance
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (source target : Pattern) : Prop :=
  ∃ fuel, SortedEquationInstanceAt base language fuel source target

/-- **The discipline only removes instances.** -/
theorem equationInstance_of_sortedEquationInstance
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (sorted : SortedEquationInstance base language source target) :
    EquationInstance base language source target := by
  obtain ⟨fuel, instance'⟩ := sorted
  refine ⟨fuel, ?_⟩
  cases instance' with
  | forward member matched premises _ applied =>
      exact EquationInstanceAt.forward member matched premises applied
  | reverse member matched premises _ applied =>
      exact EquationInstanceAt.reverse member matched premises applied

/-- One generator of the disciplined equation theory: a sorted authored
instance, or a presentation-derived law.  The derived laws already carry their
own sorting judgement, so they pass through unchanged. -/
def SortedEquationGenerator
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (source target : Pattern) : Prop :=
  SortedEquationInstance base language source target ∨
    DerivedInstance language source target

theorem equationGenerator_of_sorted
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (generator : SortedEquationGenerator base language source target) :
    EquationGenerator base language source target :=
  generator.imp equationInstance_of_sortedEquationInstance id

/-- One disciplined generator in one syntactic context. -/
inductive SortedEquationContextStep
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Prop where
  | inContext (context : OneHoleContext) {redex contractum : Pattern} :
      SortedEquationGenerator base language redex contractum →
      SortedEquationContextStep base language
        (context.fill redex) (context.fill contractum)

theorem equationContextStep_of_sorted
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (step : SortedEquationContextStep base language source target) :
    EquationContextStep base language source target := by
  cases step with
  | inContext context generator =>
      exact EquationContextStep.inContext context (equationGenerator_of_sorted generator)

/-- **The disciplined equation theory.** -/
def SortedEquationEquiv
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Prop :=
  Relation.EqvGen (SortedEquationContextStep base language)

/-- **It is contained in the generated one**, so a negative about it is a
statement about the discipline rather than about a different presentation. -/
theorem equationEquiv_of_sortedEquationEquiv
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern}
    (equivalent : SortedEquationEquiv base language left right) :
    EquationEquiv base language left right := by
  induction equivalent with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (equationContextStep_of_sorted step)
  | refl pattern => exact Relation.EqvGen.refl pattern
  | symm _ _ _ inductionHypothesis => exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans _ _ _ _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- **The invariance principle.**  A predicate respected by every disciplined
generator in every context is respected by the whole disciplined theory.  This
is what a frame of predicates needs, and what the permissive theory does not
supply. -/
theorem sortedEquationEquiv_invariant
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {predicate : Pattern → Prop}
    (respects : ∀ (context : OneHoleContext) (redex contractum : Pattern),
      SortedEquationGenerator base language redex contractum →
      (predicate (context.fill redex) ↔ predicate (context.fill contractum)))
    {left right : Pattern}
    (equivalent : SortedEquationEquiv base language left right) :
    predicate left ↔ predicate right := by
  induction equivalent with
  | rel _ _ step =>
      cases step with
      | inContext context generator => exact respects context _ _ generator
  | refl _ => exact Iff.rfl
  | symm _ _ _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- A generator's sides sit in a context, and a predicate that reads only the
context's own frame cannot tell them apart.  This is the half of `respects`
that every concrete invariant shares, so it is proved once here: outside the
hole, a predicate of the head former is independent of what is plugged in. -/
theorem headedBy_fill_congr (label : String) :
    ∀ (context : OneHoleContext) (left right : Pattern),
      context ≠ .hole →
      ((∃ inner, context.fill left = .apply label [inner]) ↔
        (∃ inner, context.fill right = .apply label [inner]))
  | .hole, _, _, notHole => absurd rfl notHole
  | .apply constructor before inner after, left, right, _ => by
      simp only [OneHoleContext.fill, Pattern.apply.injEq]
      constructor
      · rintro ⟨witness, sameLabel, shape⟩
        refine ⟨inner.fill right, sameLabel, ?_⟩
        cases before with
        | nil =>
            cases after with
            | nil => rfl
            | cons _ _ => simp at shape
        | cons _ _ => simp at shape
      · rintro ⟨witness, sameLabel, shape⟩
        refine ⟨inner.fill left, sameLabel, ?_⟩
        cases before with
        | nil =>
            cases after with
            | nil => rfl
            | cons _ _ => simp at shape
        | cons _ _ => simp at shape
  | .lambda _ _, _, _, _ => by
      simp only [OneHoleContext.fill]
      constructor <;> rintro ⟨witness, shape⟩ <;> exact Pattern.noConfusion shape
  | .multiLambda _ _ _, _, _, _ => by
      simp only [OneHoleContext.fill]
      constructor <;> rintro ⟨witness, shape⟩ <;> exact Pattern.noConfusion shape
  | .substBody _ _, _, _, _ => by
      simp only [OneHoleContext.fill]
      constructor <;> rintro ⟨witness, shape⟩ <;> exact Pattern.noConfusion shape
  | .substReplacement _ _, _, _, _ => by
      simp only [OneHoleContext.fill]
      constructor <;> rintro ⟨witness, shape⟩ <;> exact Pattern.noConfusion shape
  | .collection _ _ _ _ _, _, _, _ => by
      simp only [OneHoleContext.fill]
      constructor <;> rintro ⟨witness, shape⟩ <;> exact Pattern.noConfusion shape

/-- **A presentation-derived law is a law of the disciplined theory too.**  The
derived laws already carry their own sorting judgement, so the discipline does
not narrow them. -/
theorem sortedDerivedInstance_equivalent
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (derivedWitness : DerivedInstance language source target) :
    SortedEquationEquiv base language source target :=
  Relation.EqvGen.rel _ _
    (SortedEquationContextStep.inContext .hole (Or.inr derivedWitness))

/-! ## The disciplined operational theory

A presentation's operational theory is its authored step with a change of
representative at each end.  Everything below is the ordinary construction with
the disciplined equivalence in place of the permissive one, so the two theories
differ in exactly one thing, and the containment theorems say which.
-/

/-- The disciplined equivalence is an equivalence. -/
def sortedEquationSetoid
    (base : BasePremiseEvaluator) (language : LanguageDef) : Setoid Pattern where
  r := SortedEquationEquiv base language
  iseqv :=
    ⟨Relation.EqvGen.refl,
      fun relation => Relation.EqvGen.symm _ _ relation,
      fun first second => Relation.EqvGen.trans _ _ _ first second⟩

/-- One authored rewrite, with disciplined changes of representative at both
ends. -/
def StepModuloSortedEquations
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (source target : Pattern) : Prop :=
  ∃ redex contractum : Pattern,
    SortedEquationEquiv base language source redex ∧
      Step base language redex contractum ∧
        SortedEquationEquiv base language contractum target

theorem stepModuloSortedEquations_resp_left
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    ∀ {source source' target : Pattern},
      SortedEquationEquiv base language source source' →
      StepModuloSortedEquations base language source target →
      ∃ target', StepModuloSortedEquations base language source' target' ∧
        SortedEquationEquiv base language target target' := by
  intro source source' target sourceEquivalent
  rintro ⟨redex, contractum, redexEquivalent, primitive, targetEquivalent⟩
  refine ⟨target, ⟨redex, contractum, ?_, primitive, targetEquivalent⟩, ?_⟩
  · exact (sortedEquationSetoid base language).iseqv.trans
      ((sortedEquationSetoid base language).iseqv.symm sourceEquivalent)
      redexEquivalent
  · exact (sortedEquationSetoid base language).iseqv.refl target

theorem stepModuloSortedEquations_resp_right
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    ∀ {source target target' : Pattern},
      StepModuloSortedEquations base language source target →
      SortedEquationEquiv base language target target' →
      StepModuloSortedEquations base language source target' := by
  rintro source target target' ⟨redex, contractum, redexEquivalent, primitive,
    targetEquivalent⟩ targetsEquivalent
  exact ⟨redex, contractum, redexEquivalent, primitive,
    (sortedEquationSetoid base language).iseqv.trans targetEquivalent
      targetsEquivalent⟩

/-- **The disciplined generated theory.**  Same presentation, same authored
step; the equations are the ones that read their own type contexts. -/
def gsltModuloSortedEquations
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Mettapedia.GSLT.GSLT where
  Term := Pattern
  equations := sortedEquationSetoid base language
  rewrites := StepModuloSortedEquations base language
  rewrites_resp_left := stepModuloSortedEquations_resp_left base language
  rewrites_resp_right := stepModuloSortedEquations_resp_right base language

/-- The disciplined step is a step of the permissive theory. -/
theorem stepModuloEquations_of_sorted
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (step : StepModuloSortedEquations base language source target) :
    StepModuloEquations base language source target := by
  obtain ⟨redex, contractum, redexEquivalent, primitive, targetEquivalent⟩ := step
  exact ⟨redex, contractum, equationEquiv_of_sortedEquationEquiv redexEquivalent,
    primitive, equationEquiv_of_sortedEquationEquiv targetEquivalent⟩

/-- Every authored step is a disciplined step, so the theory is not empty for
want of equations. -/
theorem stepModuloSortedEquations_of_step
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern}
    (primitive : Step base language source target) :
    StepModuloSortedEquations base language source target :=
  ⟨source, target, (sortedEquationSetoid base language).iseqv.refl source,
    primitive, (sortedEquationSetoid base language).iseqv.refl target⟩

end Mettapedia.GSLT.LanguageDef.EquationSemantics
