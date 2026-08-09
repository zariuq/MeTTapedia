import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Proof-relevant occurrences above authored equation support

`EquationContextStep` deliberately lives in `Prop`: it says that an authored
step exists, and proof irrelevance hides which declaration occurrence produced
it.  Indexed decorations such as resource cost or provenance need the richer
object before that erasure.  This module retains equation identity,
orientation, bindings, reflective-declaration identity, and redex position in
`Type`, then proves that forgetting those data recovers exactly the ordinary
authored support relation.
-/

namespace Mettapedia.GSLT.LanguageDef.EquationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- Exact instantiation of an application-only schema context.

A literal application in a matcher-correct schema has a path consisting only
of application frames. Instantiating sibling patterns changes their contents
but preserves that path. -/
inductive InstantiatedApplicationContext (bindings : Bindings) :
    OneHoleContext → OneHoleContext → Prop where
  | hole : InstantiatedApplicationContext bindings .hole .hole
  | apply (constructor : String) (before after : List Pattern)
      {templateInner instantiatedInner : OneHoleContext}
      (inner : InstantiatedApplicationContext bindings templateInner
        instantiatedInner) :
      InstantiatedApplicationContext bindings
        (.apply constructor before templateInner after)
        (.apply constructor (before.map (applyBindings bindings))
          instantiatedInner (after.map (applyBindings bindings)))

namespace InstantiatedApplicationContext

/-- Instantiating an application-only context commutes exactly with filling
its hole. -/
theorem fill_applyBindings {bindings : Bindings}
    {template instantiated : OneHoleContext}
    (contexts : InstantiatedApplicationContext bindings template instantiated)
    (pattern : Pattern) :
    instantiated.fill (applyBindings bindings pattern) =
      applyBindings bindings (template.fill pattern) := by
  induction contexts with
  | hole => rfl
  | apply constructor before after inner inductionHypothesis =>
      simp [OneHoleContext.fill, applyBindings, List.map_append,
        inductionHypothesis]

end InstantiatedApplicationContext

/-- Orientation of one proof-relevant authored equation occurrence. -/
inductive EquationOrientation where
  | forward
  | reverse
deriving DecidableEq, Repr

/-- Proof-relevant occurrence of one authored equation instance.

Ordinary `EquationInstance` lives in `Prop`, so Lean correctly erases which
equation, orientation, bindings, and fuel produced it. This `Type`-valued
witness retains exactly those authored choices and has a forgetful map back to
the ordinary semantics. -/
inductive AuthoredEquationInstanceWitness
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Type where
  | forward {sourcePattern targetPattern : Pattern}
      (fuel : Nat)
      (equation : { equation : Equation // equation ∈ language.equations })
      (initialBindings finalBindings : Bindings)
      (matched : initialBindings ∈ matchPattern equation.1.left sourcePattern)
      (premises : PremisesAt base language fuel initialBindings
        equation.1.premises finalBindings)
      (target_eq : applyBindings finalBindings equation.1.right = targetPattern) :
      AuthoredEquationInstanceWitness base language sourcePattern targetPattern
  | reverse {sourcePattern targetPattern : Pattern}
      (fuel : Nat)
      (equation : { equation : Equation // equation ∈ language.equations })
      (initialBindings finalBindings : Bindings)
      (matched : initialBindings ∈ matchPattern equation.1.right sourcePattern)
      (premises : PremisesAt base language fuel initialBindings
        equation.1.premises finalBindings)
      (target_eq : applyBindings finalBindings equation.1.left = targetPattern) :
      AuthoredEquationInstanceWitness base language sourcePattern targetPattern

namespace AuthoredEquationInstanceWitness

/-- Forget occurrence identity and recover the ordinary proposition-valued
equation instance. -/
def erase {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    AuthoredEquationInstanceWitness base language sourcePattern targetPattern →
      EquationInstance base language sourcePattern targetPattern
  | .forward fuel equation _initialBindings _finalBindings matched premises
      target_eq =>
        ⟨fuel, .forward equation.2 matched premises target_eq⟩
  | .reverse fuel equation _initialBindings _finalBindings matched premises
      target_eq =>
        ⟨fuel, .reverse equation.2 matched premises target_eq⟩

/-- Every ordinary equation instance is supported by at least one
proof-relevant authored occurrence. The result proves support completeness
without choosing an occurrence from an erased proof. -/
theorem exists_erasing_to {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern}
    (instanceWitness : EquationInstance base language
      sourcePattern targetPattern) :
    ∃ occurrence : AuthoredEquationInstanceWitness base language sourcePattern
        targetPattern,
      occurrence.erase = instanceWitness := by
  rcases instanceWitness with ⟨fuel, instanceAt⟩
  cases instanceAt with
  | @forward equation sourcePattern targetPattern initialBindings finalBindings
      membership matched premises target_eq =>
      refine ⟨.forward fuel ⟨equation, membership⟩ initialBindings finalBindings
        matched premises target_eq, ?_⟩
      exact Subsingleton.elim _ _
  | @reverse equation sourcePattern targetPattern initialBindings finalBindings
      membership matched premises target_eq =>
      refine ⟨.reverse fuel ⟨equation, membership⟩ initialBindings finalBindings
        matched premises target_eq, ?_⟩
      exact Subsingleton.elim _ _

/-- Selected orientation, retained independently of proposition-valued
equation semantics. -/
def orientation {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    AuthoredEquationInstanceWitness base language sourcePattern targetPattern →
      EquationOrientation
  | .forward .. => .forward
  | .reverse .. => .reverse

/-- Final bindings used to instantiate the selected target schema. -/
def finalBindings {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    AuthoredEquationInstanceWitness base language sourcePattern targetPattern →
      Bindings
  | .forward _ _ _ finalBindings _ _ _ => finalBindings
  | .reverse _ _ _ finalBindings _ _ _ => finalBindings

/-- The authored schema instantiated to produce the target endpoint. -/
def targetSchema {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    AuthoredEquationInstanceWitness base language sourcePattern targetPattern →
      Pattern
  | .forward _ equation _ _ _ _ _ => equation.1.right
  | .reverse _ equation _ _ _ _ _ => equation.1.left

/-- The retained target schema and final bindings reconstruct the exact target
endpoint. -/
theorem applyBindings_targetSchema {base : BasePremiseEvaluator}
    {language : LanguageDef}
    {sourcePattern targetPattern : Pattern}
    (witness : AuthoredEquationInstanceWitness base language sourcePattern
      targetPattern) :
    applyBindings witness.finalBindings witness.targetSchema = targetPattern := by
  cases witness <;> assumption

/-- One target application is the instantiated image of a literal application
node in the selected equation orientation. An application inside a
metavariable binding is not a template occurrence. -/
def TargetApplicationTemplate {base : BasePremiseEvaluator}
    {language : LanguageDef}
    {sourcePattern targetPattern : Pattern}
    (witness : AuthoredEquationInstanceWitness base language sourcePattern
      targetPattern)
    (instantiatedContext : OneHoleContext) (sourceLabel : String)
    (arguments : List Pattern) : Prop :=
  ∃ templateContext templateArguments,
    Selects (.apply sourceLabel templateArguments) templateContext
        witness.targetSchema ∧
      InstantiatedApplicationContext witness.finalBindings templateContext
        instantiatedContext ∧
      templateArguments.map (applyBindings witness.finalBindings) = arguments

/-- A template application selects the exact instantiated target node. -/
theorem TargetApplicationTemplate.selects {base : BasePremiseEvaluator}
    {language : LanguageDef}
    {sourcePattern targetPattern : Pattern}
    {witness : AuthoredEquationInstanceWitness base language sourcePattern
      targetPattern}
    {context : OneHoleContext} {sourceLabel : String}
    {arguments : List Pattern}
    (template : witness.TargetApplicationTemplate context sourceLabel arguments) :
    Selects (.apply sourceLabel arguments) context targetPattern := by
  rcases template with ⟨templateContext, templateArguments, selected, contexts,
    arguments_eq⟩
  have filled : context.fill (.apply sourceLabel arguments) = targetPattern := by
    calc
      _ = context.fill
          (applyBindings witness.finalBindings
            (.apply sourceLabel templateArguments)) := by
              simp [applyBindings, arguments_eq]
      _ = applyBindings witness.finalBindings
          (templateContext.fill (.apply sourceLabel templateArguments)) :=
        contexts.fill_applyBindings _
      _ = applyBindings witness.finalBindings witness.targetSchema := by
        rw [selected.fill_eq]
      _ = targetPattern := witness.applyBindings_targetSchema
  rw [← filled]
  exact Selects.of_fill context (.apply sourceLabel arguments)

end AuthoredEquationInstanceWitness

/-- A proof-relevant authored contextual generator.

This is the occurrence layer above the five-field `EquationContextStep`:
equation identity, orientation, bindings, and redex context live in `Type`;
`erase` recovers the ordinary support relation in `Prop`.  Reflection has its
own indexed occurrence layer in `ReflectiveEquationOccurrence`. -/
inductive AuthoredGeneratorWitness
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Type where
  | equation (context : OneHoleContext) {redex contractum : Pattern}
      (instanceWitness : AuthoredEquationInstanceWitness base language redex
        contractum) :
      AuthoredGeneratorWitness base language (context.fill redex)
        (context.fill contractum)

namespace AuthoredGeneratorWitness

/-- Forget proof-relevant occurrence identity and recover the sole authored
equation generator relation. -/
def erase {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right →
      EquationContextStep base language left right
  | .equation context instanceWitness =>
      .inContext context instanceWitness.erase

/-- Support erasure is complete: every proposition-valued authored generator
has a proof-relevant occurrence above it. This does not choose an occurrence
from an erased proof. -/
theorem exists_erasing_to {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern}
    (step : EquationContextStep base language left right) :
    ∃ occurrence : AuthoredGeneratorWitness base language left right,
      occurrence.erase = step := by
  cases step with
  | inContext context instanceWitness =>
      obtain ⟨instanceOccurrence, erases⟩ :=
        AuthoredEquationInstanceWitness.exists_erasing_to instanceWitness
      refine ⟨.equation context instanceOccurrence, ?_⟩
      exact Subsingleton.elim _ _

/-- Exact redex context retained by either authored generator form. -/
def redexContext {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → OneHoleContext
  | .equation context _ => context

/-- Exact redex selected inside the retained one-hole context. -/
def redex {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → Pattern
  | .equation _ (redex := redex) _ => redex

/-- Exact contractum selected inside the retained one-hole context. -/
def contractum {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → Pattern
  | .equation _ (contractum := contractum) _ => contractum

/-- The retained context and redex reconstruct the indexed left endpoint. -/
@[simp]
theorem redexContext_fill_redex
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern}
    (witness : AuthoredGeneratorWitness base language left right) :
    witness.redexContext.fill witness.redex = left := by
  cases witness
  rfl

/-- The retained context and contractum reconstruct the indexed right
endpoint. -/
@[simp]
theorem redexContext_fill_contractum
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern}
    (witness : AuthoredGeneratorWitness base language left right) :
    witness.redexContext.fill witness.contractum = right := by
  cases witness
  rfl

/-- Executable constructor discriminator for the proof-relevant generator
witness. -/
def isEquation {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → Bool
  | .equation .. => true

end AuthoredGeneratorWitness

end Mettapedia.GSLT.LanguageDef.EquationSemantics
