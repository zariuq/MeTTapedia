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
inductive DeclaredEquationInstanceWitness
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
      DeclaredEquationInstanceWitness base language sourcePattern targetPattern
  | reverse {sourcePattern targetPattern : Pattern}
      (fuel : Nat)
      (equation : { equation : Equation // equation ∈ language.equations })
      (initialBindings finalBindings : Bindings)
      (matched : initialBindings ∈ matchPattern equation.1.right sourcePattern)
      (premises : PremisesAt base language fuel initialBindings
        equation.1.premises finalBindings)
      (target_eq : applyBindings finalBindings equation.1.left = targetPattern) :
      DeclaredEquationInstanceWitness base language sourcePattern targetPattern

namespace DeclaredEquationInstanceWitness

/-- Forget occurrence identity and recover the ordinary proposition-valued
equation instance. -/
def erase {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    DeclaredEquationInstanceWitness base language sourcePattern targetPattern →
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
    ∃ occurrence : DeclaredEquationInstanceWitness base language sourcePattern
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
    DeclaredEquationInstanceWitness base language sourcePattern targetPattern →
      EquationOrientation
  | .forward .. => .forward
  | .reverse .. => .reverse

/-- Final bindings used to instantiate the selected target schema. -/
def finalBindings {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    DeclaredEquationInstanceWitness base language sourcePattern targetPattern →
      Bindings
  | .forward _ _ _ finalBindings _ _ _ => finalBindings
  | .reverse _ _ _ finalBindings _ _ _ => finalBindings

/-- The authored schema instantiated to produce the target endpoint. -/
def targetSchema {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    DeclaredEquationInstanceWitness base language sourcePattern targetPattern →
      Pattern
  | .forward _ equation _ _ _ _ _ => equation.1.right
  | .reverse _ equation _ _ _ _ _ => equation.1.left

/-- The retained target schema and final bindings reconstruct the exact target
endpoint. -/
theorem applyBindings_targetSchema {base : BasePremiseEvaluator}
    {language : LanguageDef}
    {sourcePattern targetPattern : Pattern}
    (witness : DeclaredEquationInstanceWitness base language sourcePattern
      targetPattern) :
    applyBindings witness.finalBindings witness.targetSchema = targetPattern := by
  cases witness <;> assumption

/-- One target application is the instantiated image of a literal application
node in the selected equation orientation. An application inside a
metavariable binding is not a template occurrence. -/
def TargetApplicationTemplate {base : BasePremiseEvaluator}
    {language : LanguageDef}
    {sourcePattern targetPattern : Pattern}
    (witness : DeclaredEquationInstanceWitness base language sourcePattern
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
    {witness : DeclaredEquationInstanceWitness base language sourcePattern
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

end DeclaredEquationInstanceWitness

/-- A proof-relevant presentation-derived law.  Each constructor retains the
declaring rule and the exact collection data of the corresponding
`DerivedInstance`, so two derived steps with the same endpoints but different
declaring rules or different permutations remain distinct occurrences. -/
inductive DerivedGeneratorWitness (language : LanguageDef) :
    Pattern → Pattern → Type where
  | bagPerm (rule : GrammarRule) (elements elements' : List Pattern) :
      CollectionCarrierRule language rule .hashBag →
      SortedAt language (.collection .hashBag elements none) rule.category →
      List.Perm elements elements' →
      DerivedGeneratorWitness language
        (.collection .hashBag elements none) (.collection .hashBag elements' none)
  | setPerm (rule : GrammarRule) (elements elements' : List Pattern) :
      CollectionCarrierRule language rule .hashSet →
      SortedAt language (.collection .hashSet elements none) rule.category →
      List.Perm elements elements' →
      DerivedGeneratorWitness language
        (.collection .hashSet elements none) (.collection .hashSet elements' none)
  | setDedup (rule : GrammarRule) (element : Pattern) (elements : List Pattern) :
      CollectionCarrierRule language rule .hashSet →
      SortedAt language
        (.collection .hashSet (element :: element :: elements) none) rule.category →
      DerivedGeneratorWitness language
        (.collection .hashSet (element :: element :: elements) none)
        (.collection .hashSet (element :: elements) none)
  | flatten (rule : GrammarRule) (kind : CollType) (algebra : CollectionAlgebra)
      (pre inner post : List Pattern) :
      AlgebraRule language rule kind algebra →
      algebra.flatten = true →
      SortedAt language
        (.collection kind (pre ++ (.collection kind inner none) :: post) none)
        rule.category →
      DerivedGeneratorWitness language
        (.collection kind (pre ++ (.collection kind inner none) :: post) none)
        (.collection kind (pre ++ inner ++ post) none)
  | singleton (rule : GrammarRule) (kind : CollType) (algebra : CollectionAlgebra)
      (element : Pattern) :
      AlgebraRule language rule kind algebra →
      algebra.flatten = true →
      SortedAt language (.collection kind [element] none) rule.category →
      DerivedGeneratorWitness language (.collection kind [element] none) element
  | unitElim (rule : GrammarRule) (kind : CollType) (algebra : CollectionAlgebra)
      (unit : String) (pre post : List Pattern) :
      AlgebraRule language rule kind algebra →
      algebra.unit = some unit →
      SortedAt language
        (.collection kind (pre ++ (.apply unit []) :: post) none) rule.category →
      DerivedGeneratorWitness language
        (.collection kind (pre ++ (.apply unit []) :: post) none)
        (.collection kind (pre ++ post) none)
  | emptyUnit (rule : GrammarRule) (kind : CollType) (algebra : CollectionAlgebra)
      (unit : String) :
      AlgebraRule language rule kind algebra →
      algebra.unit = some unit →
      SortedAt language (.collection kind [] none) rule.category →
      DerivedGeneratorWitness language (.collection kind [] none) (.apply unit [])

namespace DerivedGeneratorWitness

/-- Forget the occurrence data and recover the derived law. -/
def erase {language : LanguageDef} {left right : Pattern} :
    DerivedGeneratorWitness language left right → DerivedInstance language left right
  | .bagPerm _ _ _ carrier sorted perm => .bagPerm carrier sorted perm
  | .setPerm _ _ _ carrier sorted perm => .setPerm carrier sorted perm
  | .setDedup _ _ _ carrier sorted => .setDedup carrier sorted
  | .flatten _ _ _ _ _ _ algebra flattens sorted => .flatten algebra flattens sorted
  | .singleton _ _ _ _ algebra flattens sorted => .singleton algebra flattens sorted
  | .unitElim _ _ _ _ _ _ algebra unit sorted => .unitElim algebra unit sorted
  | .emptyUnit _ _ _ _ algebra unit sorted => .emptyUnit algebra unit sorted

/-- Every derived law has an occurrence above it. -/
theorem exists_erasing_to {language : LanguageDef} {left right : Pattern}
    (derived : DerivedInstance language left right) :
    ∃ occurrence : DerivedGeneratorWitness language left right, occurrence.erase = derived := by
  cases derived with
  | bagPerm carrier sorted perm => exact ⟨.bagPerm _ _ _ carrier sorted perm, rfl⟩
  | setPerm carrier sorted perm => exact ⟨.setPerm _ _ _ carrier sorted perm, rfl⟩
  | setDedup carrier sorted => exact ⟨.setDedup _ _ _ carrier sorted, rfl⟩
  | flatten algebra flattens sorted => exact ⟨.flatten _ _ _ _ _ _ algebra flattens sorted, rfl⟩
  | singleton algebra flattens sorted => exact ⟨.singleton _ _ _ _ algebra flattens sorted, rfl⟩
  | unitElim algebra unit sorted => exact ⟨.unitElim _ _ _ _ _ _ algebra unit sorted, rfl⟩
  | emptyUnit algebra unit sorted => exact ⟨.emptyUnit _ _ _ _ algebra unit sorted, rfl⟩

end DerivedGeneratorWitness

/-- A proof-relevant contextual generator: an authored equation instance or a
presentation-derived law, placed in one retained one-hole context.

This is the occurrence layer above the five-field `EquationContextStep`:
equation or law identity, orientation, bindings, and redex context live in
`Type`; `erase` recovers the ordinary support relation in `Prop`.  The name
records the layer's origin in authored equations; since the equation theory
also contains the laws a presentation derives, those laws carry occurrences
here as well.  Reflection has its own indexed occurrence layer in
`ReflectiveEquationOccurrence`. -/
inductive AuthoredGeneratorWitness
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Pattern → Pattern → Type where
  | equation (context : OneHoleContext) {redex contractum : Pattern}
      (instanceWitness : DeclaredEquationInstanceWitness base language redex
        contractum) :
      AuthoredGeneratorWitness base language (context.fill redex)
        (context.fill contractum)
  | derived (context : OneHoleContext) {redex contractum : Pattern}
      (lawWitness : DerivedGeneratorWitness language redex contractum) :
      AuthoredGeneratorWitness base language (context.fill redex)
        (context.fill contractum)

namespace AuthoredGeneratorWitness

/-- Forget proof-relevant occurrence identity and recover the sole equation
generator relation. -/
def erase {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right →
      EquationContextStep base language left right
  | .equation context instanceWitness =>
      .inContext context (Or.inl instanceWitness.erase)
  | .derived context lawWitness =>
      .inContext context (Or.inr lawWitness.erase)

/-- Support erasure is complete: every proposition-valued generator, authored
or derived, has a proof-relevant occurrence above it.  This does not choose
an occurrence from an erased proof. -/
theorem exists_erasing_to {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern}
    (step : EquationContextStep base language left right) :
    ∃ occurrence : AuthoredGeneratorWitness base language left right,
      occurrence.erase = step := by
  cases step with
  | inContext context generator =>
      rcases generator with instanceWitness | lawWitness
      · obtain ⟨instanceOccurrence, _⟩ :=
          DeclaredEquationInstanceWitness.exists_erasing_to instanceWitness
        refine ⟨.equation context instanceOccurrence, ?_⟩
        exact Subsingleton.elim _ _
      · obtain ⟨lawOccurrence, _⟩ := DerivedGeneratorWitness.exists_erasing_to lawWitness
        refine ⟨.derived context lawOccurrence, ?_⟩
        exact Subsingleton.elim _ _

/-- Retained one-hole context around the generator's redex. -/
def redexContext {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → OneHoleContext
  | .equation context _ => context
  | .derived context _ => context

/-- Exact redex selected inside the retained one-hole context. -/
def redex {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → Pattern
  | .equation _ (redex := redex) _ => redex
  | .derived _ (redex := redex) _ => redex

/-- Exact contractum selected inside the retained one-hole context. -/
def contractum {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → Pattern
  | .equation _ (contractum := contractum) _ => contractum
  | .derived _ (contractum := contractum) _ => contractum

/-- The retained context and redex reconstruct the indexed left endpoint. -/
@[simp]
theorem redexContext_fill_redex
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern}
    (witness : AuthoredGeneratorWitness base language left right) :
    witness.redexContext.fill witness.redex = left := by
  cases witness <;> rfl

/-- The retained context and contractum reconstruct the indexed right
endpoint. -/
@[simp]
theorem redexContext_fill_contractum
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern}
    (witness : AuthoredGeneratorWitness base language left right) :
    witness.redexContext.fill witness.contractum = right := by
  cases witness <;> rfl

/-- Executable constructor discriminator: the occurrence comes from an
authored equation. -/
def isEquation {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → Bool
  | .equation .. => true
  | .derived .. => false

/-- Executable constructor discriminator: the occurrence comes from a
presentation-derived law. -/
def isDerived {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right → Bool
  | .equation .. => false
  | .derived .. => true

end AuthoredGeneratorWitness

end Mettapedia.GSLT.LanguageDef.EquationSemantics
