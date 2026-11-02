import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.LanguageDef.NamedFreeContext

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
      (raw : readsRaw equation.1 = true)
      (initialBindings finalBindings : Bindings)
      (matched : initialBindings ∈ matchPattern equation.1.left sourcePattern)
      (premises : PremisesAt base language fuel initialBindings
        equation.1.premises finalBindings)
      (target_eq : applyBindings finalBindings equation.1.right = targetPattern) :
      DeclaredEquationInstanceWitness base language sourcePattern targetPattern
  | reverse {sourcePattern targetPattern : Pattern}
      (fuel : Nat)
      (equation : { equation : Equation // equation ∈ language.equations })
      (raw : readsRaw equation.1 = true)
      (initialBindings finalBindings : Bindings)
      (matched : initialBindings ∈ matchPattern equation.1.right sourcePattern)
      (premises : PremisesAt base language fuel initialBindings
        equation.1.premises finalBindings)
      (target_eq : applyBindings finalBindings equation.1.left = targetPattern) :
      DeclaredEquationInstanceWitness base language sourcePattern targetPattern

namespace DeclaredEquationInstanceWitness

/-- Forget occurrence identity and recover the ordinary proposition-valued
equation instance. -/
theorem erase {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    DeclaredEquationInstanceWitness base language sourcePattern targetPattern →
      EquationInstance base language sourcePattern targetPattern
  | .forward fuel equation raw _initialBindings _finalBindings matched premises
      target_eq =>
        ⟨fuel, .forward equation.2 raw matched premises target_eq⟩
  | .reverse fuel equation raw _initialBindings _finalBindings matched premises
      target_eq =>
        ⟨fuel, .reverse equation.2 raw matched premises target_eq⟩

/-- Every ordinary equation instance is supported by at least one
proof-relevant authored occurrence, when the ordinary matcher reads every
authored equation. The result proves support completeness without choosing
an occurrence from an erased proof. -/
theorem exists_erasing_to {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern}
    (raw : ∀ equation ∈ language.equations, readsRaw equation = true)
    (instanceWitness : EquationInstance base language
      sourcePattern targetPattern) :
    ∃ occurrence : DeclaredEquationInstanceWitness base language sourcePattern
        targetPattern,
      occurrence.erase = instanceWitness := by
  rcases instanceWitness with ⟨fuel, instanceAt⟩
  cases instanceAt with
  | @forward equation sourcePattern targetPattern initialBindings finalBindings
      membership raw matched premises target_eq =>
      refine ⟨.forward fuel ⟨equation, membership⟩ raw initialBindings finalBindings
        matched premises target_eq, ?_⟩
      exact Subsingleton.elim _ _
  | @reverse equation sourcePattern targetPattern initialBindings finalBindings
      membership raw matched premises target_eq =>
      refine ⟨.reverse fuel ⟨equation, membership⟩ raw initialBindings finalBindings
        matched premises target_eq, ?_⟩
      exact Subsingleton.elim _ _
  | declared membership notRaw _ =>
      rw [raw _ membership] at notRaw
      cases notRaw

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
  | .forward _ _ _ _ finalBindings _ _ _ => finalBindings
  | .reverse _ _ _ _ finalBindings _ _ _ => finalBindings

/-- The authored schema instantiated to produce the target endpoint. -/
def targetSchema {base : BasePremiseEvaluator} {language : LanguageDef}
    {sourcePattern targetPattern : Pattern} :
    DeclaredEquationInstanceWitness base language sourcePattern targetPattern →
      Pattern
  | .forward _ equation _ _ _ _ _ _ => equation.1.right
  | .reverse _ equation _ _ _ _ _ _ => equation.1.left

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

/-- A finite route to the declared collection type inside one parameter. -/
inductive CollectionTypeEdge where
  | domain
  | codomain
  | binder
  | element
deriving DecidableEq,Repr

/-- Read one actual declared type occurrence. The empty route selects a
collection of the requested kind; every other step follows the type spine. -/
def collectionTypeAt? (kind : CollType) : List CollectionTypeEdge → TypeExpr → Option TypeExpr
  | [],.collection actual element => if kind == actual then some element else none
  | .domain::rest,.arrow domain _ => collectionTypeAt? kind rest domain
  | .codomain::rest,.arrow _ codomain => collectionTypeAt? kind rest codomain
  | .binder::rest,.multiBinder body => collectionTypeAt? kind rest body
  | .element::rest,.collection _ element => collectionTypeAt? kind rest element
  | _,_ => none

/-- A selected route proves exactly the original declared-type occurrence. -/
theorem collectionTypeAt?_sound {kind : CollType} {path : List CollectionTypeEdge}
    {type elementType : TypeExpr} (selected : collectionTypeAt? kind path type = some elementType) :
    WellSorted.CollectionTypeOccurs kind elementType type := by
  induction path generalizing type with
  | nil =>
      cases type <;> simp only [collectionTypeAt?,reduceCtorEq] at selected
      case collection actual element =>
        split at selected
        next same =>
          have kindSame : kind = actual := beq_iff_eq.mp same
          cases kindSame
          cases Option.some.inj selected
          exact .here
        next => cases selected
  | cons step rest ih =>
      cases step <;> cases type <;> simp only [collectionTypeAt?,reduceCtorEq] at selected
      case domain.arrow domain codomain => exact .domain (ih selected)
      case codomain.arrow domain codomain => exact .codomain (ih selected)
      case binder.multiBinder body => exact .binder (ih selected)
      case element.collection actual element => exact .element (ih selected)

/-- Every declared-type occurrence has a finite route, without extracting a
computational choice from the proposition at runtime. -/
theorem collectionTypeAt?_complete {kind : CollType} {type elementType : TypeExpr}
    (occurs : WellSorted.CollectionTypeOccurs kind elementType type) :
    ∃ path,collectionTypeAt? kind path type = some elementType := by
  induction occurs with
  | here => exact ⟨[],by simp only [collectionTypeAt?,beq_self_eq_true,ite_true]⟩
  | domain _ ih => obtain ⟨path,selected⟩ := ih; exact ⟨.domain::path,selected⟩
  | codomain _ ih => obtain ⟨path,selected⟩ := ih; exact ⟨.codomain::path,selected⟩
  | binder _ ih => obtain ⟨path,selected⟩ := ih; exact ⟨.binder::path,selected⟩
  | element _ ih => obtain ⟨path,selected⟩ := ih; exact ⟨.element::path,selected⟩

/-- Executable evidence for a source kind law retains the exact declaring
parameter, its type route, the bound context and checked raw data typing.
Alternative typing receipts are validation data, not derivation identities. -/
structure CollectionTypedReceipt (language : LanguageDef) (rule : GrammarRule)
    (kind : CollType) (elements : List Pattern) where
  parameterIndex : Fin rule.params.length
  path : List CollectionTypeEdge
  elementType : TypeExpr
  selected : collectionTypeAt? kind path (rule.params.get parameterIndex).typeExpr = some elementType
  bound : List TypeExpr
  data : NamedFreeContext.SourceReceiptData language bound (.collection kind elementType)
  accepted : data.accepts (.collection kind elements none) = true

namespace CollectionTypedReceipt

/-- Checked data reconstructs the existing independent source judgment. -/
theorem erase {language : LanguageDef} {rule : GrammarRule} {kind : CollType} {elements : List Pattern}
    (receipt : CollectionTypedReceipt language rule kind elements) :
    WellSorted.CollectionTypedAt language rule kind elements :=
  ⟨rule.params.get receipt.parameterIndex,List.get_mem _ _,receipt.elementType,
    collectionTypeAt?_sound receipt.selected,
    WellSorted.FreeTypeContext.ofList receipt.data.entries,receipt.bound,
    receipt.data.sound _ receipt.accepted⟩

/-- Every original source typing witness has honest finite receipt data.
This is an existence theorem, not a computational encoder from a Prop proof. -/
theorem exists_of_typed {language : LanguageDef} {rule : GrammarRule} {kind : CollType} {elements : List Pattern}
    (typed : WellSorted.CollectionTypedAt language rule kind elements) :
    ∃ receipt : CollectionTypedReceipt language rule kind elements,receipt.erase = typed := by
  obtain ⟨parameter,member,elementType,occurs,free,bound,sourceTyped⟩ := typed
  obtain ⟨index,atIndex⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨inBounds,entrySame⟩ := List.getElem?_eq_some_iff.mp atIndex
  let slot : Fin rule.params.length := ⟨index,inBounds⟩
  have parameterSame : rule.params.get slot = parameter := entrySame
  obtain ⟨path,selected⟩ := collectionTypeAt?_complete occurs
  obtain ⟨data,accepted,_⟩ := NamedFreeContext.SourceReceiptData.exists_of_typed sourceTyped
  have actualSelection : collectionTypeAt? kind path (rule.params.get slot).typeExpr = some elementType := by
    simpa only [parameterSame] using selected
  exact ⟨⟨slot,path,elementType,actualSelection,bound,data,accepted⟩,Subsingleton.elim _ _⟩

end CollectionTypedReceipt

#print axioms collectionTypeAt?_sound
#print axioms collectionTypeAt?_complete
#print axioms CollectionTypedReceipt.erase
#print axioms CollectionTypedReceipt.exists_of_typed

/-- A presentation-derived law retains its declaring rule, raw decomposition
and checked collection-typing receipt. These typing/path/header choices are
administrative validation evidence. A Prop-valued permutation proof does not
retain physical token identities or distinguish equal-endpoint permutations;
logical derivation identity is selected separately from this packet data. -/
inductive DerivedGeneratorWitness (language : LanguageDef) :
    Pattern → Pattern → Type where
  | bagPerm (rule : GrammarRule) (elements elements' : List Pattern) :
      rule ∈ language.terms →
      CollectionTypedReceipt language rule .hashBag elements →
      List.Perm elements elements' →
      DerivedGeneratorWitness language
        (.collection .hashBag elements none) (.collection .hashBag elements' none)
  | setPerm (rule : GrammarRule) (elements elements' : List Pattern) :
      rule ∈ language.terms →
      CollectionTypedReceipt language rule .hashSet elements →
      List.Perm elements elements' →
      DerivedGeneratorWitness language
        (.collection .hashSet elements none) (.collection .hashSet elements' none)
  | setDedup (rule : GrammarRule) (element : Pattern) (elements : List Pattern) :
      rule ∈ language.terms →
      CollectionTypedReceipt language rule .hashSet (element :: element :: elements) →
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
theorem erase {language : LanguageDef} {left right : Pattern} :
    DerivedGeneratorWitness language left right → DerivedInstance language left right
  | .bagPerm _ _ _ member receipt perm => .bagPerm member receipt.erase perm
  | .setPerm _ _ _ member receipt perm => .setPerm member receipt.erase perm
  | .setDedup _ _ _ member receipt => .setDedup member receipt.erase
  | .flatten _ _ _ _ _ _ algebra flattens sorted => .flatten algebra flattens sorted
  | .singleton _ _ _ _ algebra flattens sorted => .singleton algebra flattens sorted
  | .unitElim _ _ _ _ _ _ algebra unit sorted => .unitElim algebra unit sorted
  | .emptyUnit _ _ _ _ algebra unit sorted => .emptyUnit algebra unit sorted

/-- Every derived law has an occurrence above it. -/
theorem exists_erasing_to {language : LanguageDef} {left right : Pattern}
    (derived : DerivedInstance language left right) :
    ∃ occurrence : DerivedGeneratorWitness language left right, occurrence.erase = derived := by
  cases derived with
  | bagPerm member typed perm =>
      obtain ⟨receipt,_⟩ := CollectionTypedReceipt.exists_of_typed typed
      exact ⟨.bagPerm _ _ _ member receipt perm,Subsingleton.elim _ _⟩
  | setPerm member typed perm =>
      obtain ⟨receipt,_⟩ := CollectionTypedReceipt.exists_of_typed typed
      exact ⟨.setPerm _ _ _ member receipt perm,Subsingleton.elim _ _⟩
  | setDedup member typed =>
      obtain ⟨receipt,_⟩ := CollectionTypedReceipt.exists_of_typed typed
      exact ⟨.setDedup _ _ _ member receipt,Subsingleton.elim _ _⟩
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
theorem erase {base : BasePremiseEvaluator} {language : LanguageDef}
    {left right : Pattern} :
    AuthoredGeneratorWitness base language left right →
      EquationContextStep base language left right
  | .equation context instanceWitness =>
      .inContext context (Or.inl instanceWitness.erase)
  | .derived context lawWitness =>
      .inContext context (Or.inr lawWitness.erase)

/-- Support erasure is complete: when the ordinary matcher reads every
authored equation, every proposition-valued generator, authored or derived,
has a proof-relevant occurrence above it.  This does not choose an
occurrence from an erased proof. -/
theorem exists_erasing_to {base : BasePremiseEvaluator}
    {language : LanguageDef} {left right : Pattern}
    (raw : ∀ equation ∈ language.equations, readsRaw equation = true)
    (step : EquationContextStep base language left right) :
    ∃ occurrence : AuthoredGeneratorWitness base language left right,
      occurrence.erase = step := by
  cases step with
  | inContext context generator =>
      rcases generator with instanceWitness | lawWitness
      · obtain ⟨instanceOccurrence, _⟩ :=
          DeclaredEquationInstanceWitness.exists_erasing_to raw instanceWitness
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

#print axioms Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedGeneratorWitness.erase
#print axioms Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedGeneratorWitness.exists_erasing_to
#print axioms Mettapedia.GSLT.LanguageDef.EquationSemantics.AuthoredGeneratorWitness.erase
#print axioms Mettapedia.GSLT.LanguageDef.EquationSemantics.AuthoredGeneratorWitness.exists_erasing_to
