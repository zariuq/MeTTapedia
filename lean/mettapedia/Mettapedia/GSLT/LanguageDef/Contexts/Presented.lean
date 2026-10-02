import Mettapedia.GSLT.Contexts.ContextMorphism
import Mettapedia.GSLT.LanguageDef.Contexts.SymbolMaps
import Mettapedia.GSLT.LanguageDef.SemanticCategory

/-!
# The contexts of a presented language

A language definition presents a symmetric multicategory of contexts.

* An interface records the type of a hole or of a result and its binding
  stage: the types of the binders in scope there.
* The terms of an interface are the well-sorted object patterns of that type
  whose loose bound variables are typed by the stage.  A term of the
  interface with an empty stage is a closed term; a term at a stage with one
  name is a term parameterised by that name.
* A context is a linear pattern with holes that sends every well-sorted
  filling of its holes to a well-sorted term, in the language and in every
  language it maps into by a map of declarations.  The second clause makes
  a context well-sorted by its shape and not by the accident of which terms
  the language happens to have.  Filling is textual, so a hole beneath a
  binder captures: its interface carries the binder in its stage.
* Static equivalence and reduction are those of the language, each
  saturated within the terms of one interface.

At the interface of the interacting sort with an empty stage this is the
behavioural theory that the interactive presentation already has.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- An interface: the type of a hole or result and the types of the binders
in scope there. -/
structure Interface where
  type : TypeExpr
  stage : List TypeExpr

/-- The terms of an interface. -/
abbrev Term (language : LanguageDef) (interface : Interface) :=
  OpenPattern language FreeTypeContext.empty interface.stage interface.type

variable (base : BasePremiseEvaluator) (language : LanguageDef)

/-- Static equivalence generated within the terms of one interface. -/
def termSetoid (interface : Interface) : Setoid (Term language interface) where
  r := Relation.EqvGen fun left right => EquationContextStep base language left.1 right.1
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Reduction between terms of one interface, saturated by the static
equivalence at both ends. -/
def TermStep {interface : Interface} (source target : Term language interface) : Prop :=
  ∃ redex contractum : Term language interface,
    (termSetoid base language interface).r source redex ∧
      Step base language redex.1 contractum.1 ∧
        (termSetoid base language interface).r contractum target

theorem termStep_resp_left {interface : Interface}
    {source source' target : Term language interface}
    (equivalent : (termSetoid base language interface).r source source')
    (step : TermStep base language source target) :
    ∃ target', TermStep base language source' target' ∧
      (termSetoid base language interface).r target target' := by
  obtain ⟨redex, contractum, redexEquivalent, primitive, targetEquivalent⟩ := step
  exact ⟨target, ⟨redex, contractum,
    (termSetoid base language interface).iseqv.trans
      ((termSetoid base language interface).iseqv.symm equivalent) redexEquivalent,
    primitive, targetEquivalent⟩, (termSetoid base language interface).iseqv.refl target⟩

theorem termStep_resp_right {interface : Interface}
    {source target target' : Term language interface}
    (step : TermStep base language source target)
    (equivalent : (termSetoid base language interface).r target target') :
    TermStep base language source target' := by
  obtain ⟨redex, contractum, redexEquivalent, primitive, targetEquivalent⟩ := step
  exact ⟨redex, contractum, redexEquivalent, primitive,
    (termSetoid base language interface).iseqv.trans targetEquivalent equivalent⟩

/-- The action of a symbol map on an interface. -/
def Interface.map (symbols : LanguageDefSymbolMap) (interface : Interface) : Interface where
  type := mapTypeExpr symbols interface.type
  stage := interface.stage.map (mapTypeExpr symbols)

@[simp] theorem Interface.map_id (interface : Interface) :
    interface.map LanguageDefSymbolMap.id = interface := by
  cases interface with
  | mk type stage =>
      have stageFixed : stage.map (mapTypeExpr LanguageDefSymbolMap.id) = stage := by
        induction stage with
        | nil => rfl
        | cons head tail recurse => simp [recurse]
      simp [Interface.map, stageFixed]

@[simp] theorem Interface.map_comp (first second : LanguageDefSymbolMap)
    (interface : Interface) :
    interface.map (first.comp second) = (interface.map first).map second := by
  cases interface with
  | mk type stage =>
      have stageComposed : stage.map (mapTypeExpr (first.comp second)) =
          (stage.map (mapTypeExpr first)).map (mapTypeExpr second) := by
        induction stage with
        | nil => rfl
        | cons head tail recurse => simp [recurse]
      simp [Interface.map, stageComposed]

/-- A map of declarations carries the terms of an interface to terms of its
image. -/
theorem openPatternWellSorted_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {interface : Interface} {pattern : Pattern}
    (sorted : OpenPatternWellSorted source.language FreeTypeContext.empty interface.stage
      interface.type pattern) :
    OpenPatternWellSorted target.language FreeTypeContext.empty
      (interface.map morphism.symbols).stage (interface.map morphism.symbols).type
      (mapPattern morphism.symbols pattern) := by
  have mapped := sorted.1.map morphism
  rw [FreeTypeContext.map_empty] at mapped
  refine ⟨mapped, ?_, ?_, ?_⟩
  · simpa using sorted.2.1
  · simpa using sorted.2.2.1
  · simpa [ScopeSafeAt, Interface.map] using mapped.isWellScopedAt

/-- The image of a term under a map of declarations. -/
def Term.map {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    {interface : Interface} (term : Term source.language interface) :
    Term target.language (interface.map morphism.symbols) :=
  ⟨mapPattern morphism.symbols term.1, openPatternWellSorted_map morphism term.2⟩

/-- A context of a presentation: a linear pattern with holes that sends
well-sorted fillings to well-sorted terms, in the presentation and in every
presentation it maps into. -/
structure Context (presentation : ValidatedLanguageDef) {arity : Type}
    (holes : arity → Interface) (result : Interface) where
  shape : MultiHoleContext arity
  linear : shape.Linear
  sorted : ∀ {target : ValidatedLanguageDef} (morphism : StructuralMorphism presentation target)
    (filling : (index : arity) → Term target.language ((holes index).map morphism.symbols)),
    OpenPatternWellSorted target.language FreeTypeContext.empty
      (result.map morphism.symbols).stage (result.map morphism.symbols).type
      ((mapContextSymbols morphism.symbols shape).fill fun index => (filling index).1)

variable {presentation : ValidatedLanguageDef}

/-- A context sends well-sorted fillings in its own presentation to
well-sorted terms: the instance of its law at the identity map. -/
theorem Context.sortedHere {arity : Type} {holes : arity → Interface} {result : Interface}
    (context : Context presentation holes result)
    (filling : (index : arity) → Term presentation.language (holes index)) :
    OpenPatternWellSorted presentation.language FreeTypeContext.empty result.stage result.type
      (context.shape.fill fun index => (filling index).1) := by
  have here := context.sorted (StructuralMorphism.id presentation) fun index =>
    ⟨(filling index).1, by
      change OpenPatternWellSorted _ _ ((holes index).map LanguageDefSymbolMap.id).stage
        ((holes index).map LanguageDefSymbolMap.id).type _
      rw [Interface.map_id]
      exact (filling index).2⟩
  change OpenPatternWellSorted _ _ (result.map LanguageDefSymbolMap.id).stage
    (result.map LanguageDefSymbolMap.id).type
    ((mapContextSymbols LanguageDefSymbolMap.id context.shape).fill _) at here
  rwa [Interface.map_id, mapContextSymbols_id] at here

/-- Fill the holes of a context. -/
def Context.fill {arity : Type} {holes : arity → Interface} {result : Interface}
    (context : Context presentation holes result)
    (filling : (index : arity) → Term presentation.language (holes index)) :
    Term presentation.language result :=
  ⟨context.shape.fill fun index => (filling index).1, context.sortedHere filling⟩

/-- Changing the filling of one hole by one equation step changes the filled
context by one equation step. -/
theorem Context.fill_update_step {arity : Type} [DecidableEq arity]
    {holes : arity → Interface} {result : Interface} (context : Context presentation holes result)
    (filling : (index : arity) → Term presentation.language (holes index)) (index : arity)
    {first second : Term presentation.language (holes index)}
    (step : EquationContextStep base presentation.language first.1 second.1) :
    EquationContextStep base presentation.language
      (context.fill (Function.update filling index first)).1
      (context.fill (Function.update filling index second)).1 := by
  obtain ⟨focus, focused⟩ :=
    context.linear.exists_oneHole index fun other => (filling other).1
  have raw : ∀ term : Term presentation.language (holes index),
      (fun other => (Function.update filling index term other).1) =
        Function.update (fun other => (filling other).1) index term.1 := by
    intro term
    funext other
    by_cases same : other = index
    · subst same
      simp
    · simp [Function.update_of_ne same]
  have filled : ∀ term : Term presentation.language (holes index),
      (context.fill (Function.update filling index term)).1 = focus.fill term.1 := by
    intro term
    change context.shape.fill _ = _
    rw [raw term]
    exact focused term.1
  rw [filled first, filled second]
  exact equationContextStep_fill focus step

/-- Changing the filling of one hole within its equivalence class does not
change the class of the filled context. -/
theorem Context.fill_update_resp {arity : Type} [DecidableEq arity]
    {holes : arity → Interface} {result : Interface} (context : Context presentation holes result)
    (filling : (index : arity) → Term presentation.language (holes index)) (index : arity)
    {first second : Term presentation.language (holes index)}
    (equivalent : (termSetoid base presentation.language (holes index)).r first second) :
    (termSetoid base presentation.language result).r
      (context.fill (Function.update filling index first))
      (context.fill (Function.update filling index second)) := by
  induction equivalent with
  | rel first second step =>
      exact Relation.EqvGen.rel _ _ (context.fill_update_step base filling index step)
  | refl term => exact Relation.EqvGen.refl _
  | symm first second _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans first middle second _ _ firstStep secondStep =>
      exact Relation.EqvGen.trans _ _ _ firstStep secondStep

/-- **Filling respects the static equivalence**, in every hole at once. -/
theorem Context.fill_resp {arity : Type} {holes : arity → Interface} {result : Interface}
    (context : Context presentation holes result)
    {first second : (index : arity) → Term presentation.language (holes index)}
    (equivalent : ∀ index, (termSetoid base presentation.language (holes index)).r (first index)
      (second index)) :
    (termSetoid base presentation.language result).r (context.fill first) (context.fill second) := by
  classical
  have mixed : ∀ changed : List arity,
      (termSetoid base presentation.language result).r (context.fill first)
        (context.fill fun index => if index ∈ changed then second index else first index) := by
    intro changed
    induction changed with
    | nil => exact (termSetoid base presentation.language result).iseqv.refl _
    | cons index changed recurse =>
        refine (termSetoid base presentation.language result).iseqv.trans recurse ?_
        have before : (fun other => if other ∈ changed then second other else first other) =
            Function.update (fun other => if other ∈ changed then second other else first other)
              index (if index ∈ changed then second index else first index) := by
          rw [Function.update_eq_self]
        have after : (fun other => if other ∈ index :: changed then second other
            else first other) =
            Function.update (fun other => if other ∈ changed then second other else first other)
              index (second index) := by
          funext other
          by_cases same : other = index
          · subst same
            simp
          · simp [same]
        rw [before, after]
        apply context.fill_update_resp base
        by_cases present : index ∈ changed
        · simp only [present, if_true]
          exact (termSetoid base presentation.language _).iseqv.refl _
        · simp only [present, if_false]
          exact equivalent index
  have final := mixed context.shape.holes
  have same : context.fill (fun index =>
      if index ∈ context.shape.holes then second index else first index) =
        context.fill second := by
    apply Subtype.ext
    change context.shape.fill _ = context.shape.fill _
    apply MultiHoleContext.fill_congr
    intro index membership
    simp [membership]
  rwa [same] at final

/-- The context that is a hole. -/
def Context.identity (interface : Interface) :
    Context presentation (fun _ : Unit => interface) interface where
  shape := .hole ()
  linear := MultiHoleContext.linear_hole
  sorted := fun _ filling => (filling ()).2

/-- Plug a family of contexts into the holes of a context. -/
def Context.plug {arity : Type} {holes : arity → Interface} {result : Interface}
    {innerArity : arity → Type} {innerHoles : (index : arity) → innerArity index → Interface}
    (context : Context presentation holes result)
    (inner : (index : arity) → Context presentation (innerHoles index) (holes index)) :
    Context presentation
      (fun position : Σ index, innerArity index => innerHoles position.1 position.2) result where
  shape := context.shape.plug fun index => (inner index).shape
  linear := context.linear.plug fun index => (inner index).linear
  sorted := fun morphism filling => by
    rw [mapContextSymbols_plug, MultiHoleContext.fill_plug]
    exact context.sorted morphism fun index =>
      ⟨_, (inner index).sorted morphism fun position => filling ⟨index, position⟩⟩

/-- Rename the holes along a bijection. -/
def Context.relabel {arity newArity : Type} {holes : newArity → Interface} {result : Interface}
    (rename : arity → newArity) (bijective : Function.Bijective rename)
    (context : Context presentation (fun index => holes (rename index)) result) :
    Context presentation holes result where
  shape := context.shape.relabel rename
  linear := context.linear.relabel bijective
  sorted := fun morphism filling => by
    rw [mapContextSymbols_relabel, MultiHoleContext.fill_relabel]
    exact context.sorted morphism fun index => filling (rename index)

/-- A term as a context with no hole. -/
def Context.constant {holes : Empty → Interface} {result : Interface}
    (term : Term presentation.language result) : Context presentation holes result where
  shape := MultiHoleContext.ofPattern term.1
  linear := MultiHoleContext.linear_ofPattern term.1
  sorted := fun morphism _ => by
    rw [mapContextSymbols_ofPattern, MultiHoleContext.fill_ofPattern]
    exact openPatternWellSorted_map morphism term.2

variable (presentation)

/-- **The contexts of a presentation**, with its static equivalence and its
reduction. -/
def contextTheory : ContextTheory.{0} where
  Interface := Interface
  Term := Term presentation.language
  equations := termSetoid base presentation.language
  rewrites := TermStep base presentation.language
  rewrites_resp_left := termStep_resp_left base presentation.language
  rewrites_resp_right := termStep_resp_right base presentation.language
  Context := Context presentation
  fill := Context.fill
  fill_resp := fun context _ _ equivalent => context.fill_resp base equivalent
  identity := Context.identity
  fill_identity := fun _ _ => rfl
  plug := Context.plug
  fill_plug := fun context inner _ =>
    Subtype.ext (MultiHoleContext.fill_plug _ context.shape fun index => (inner index).shape)
  relabel := Context.relabel
  fill_relabel := fun rename _ context _ =>
    Subtype.ext (MultiHoleContext.fill_relabel _ rename context.shape)
  constant := Context.constant
  fill_constant := fun term _ => Subtype.ext (MultiHoleContext.fill_ofPattern _ term.1)

/-! ## One-hole contexts as labels -/

variable {presentation}

/-- A one-hole context that sends the terms of one interface to terms of
another, in the presentation and in every presentation it maps into, is a
label between them. -/
def labelOfOneHole {source target : Interface} (context : OneHoleContext)
    (sorted : ∀ {extension : ValidatedLanguageDef}
      (morphism : StructuralMorphism presentation extension)
      (term : Term extension.language (source.map morphism.symbols)),
      OpenPatternWellSorted extension.language FreeTypeContext.empty
        (target.map morphism.symbols).stage (target.map morphism.symbols).type
        ((CIGSLT.mapOneHoleContext morphism.symbols context).fill term.1)) :
    Context presentation (fun _ : Unit => source) target where
  shape := MultiHoleContext.ofOneHole context
  linear := MultiHoleContext.linear_ofOneHole context
  sorted := fun morphism filling => by
    rw [mapContextSymbols_ofOneHole, MultiHoleContext.fill_ofOneHole]
    exact sorted morphism (filling ())

/-- Placing a term in the label of a one-hole context plugs it. -/
theorem apply_labelOfOneHole {source target : Interface} (context : OneHoleContext)
    (sorted : ∀ {extension : ValidatedLanguageDef}
      (morphism : StructuralMorphism presentation extension)
      (term : Term extension.language (source.map morphism.symbols)),
      OpenPatternWellSorted extension.language FreeTypeContext.empty
        (target.map morphism.symbols).stage (target.map morphism.symbols).type
        ((CIGSLT.mapOneHoleContext morphism.symbols context).fill term.1))
    (term : Term presentation.language source) :
    ((contextTheory base presentation).apply (labelOfOneHole context sorted) term).1 =
      context.fill term.1 :=
  MultiHoleContext.fill_ofOneHole _ context

/-- **Every label is a one-hole context.**  The transitions labelled by the
contexts of a presentation are those of plugging into one-hole contexts. -/
theorem exists_oneHole_of_label {source target : Interface}
    (label : Context presentation (fun _ : Unit => source) target) :
    ∃ context : OneHoleContext, ∀ term : Term presentation.language source,
      ((contextTheory base presentation).apply label term).1 = context.fill term.1 := by
  obtain ⟨context, focused⟩ :=
    label.linear.exists_oneHole () fun _ => Pattern.bvar 0
  refine ⟨context, fun term => ?_⟩
  have same : (fun _ : Unit => term.1) =
      Function.update (fun _ : Unit => Pattern.bvar 0) () term.1 := by
    funext index
    cases index
    simp
  change label.shape.fill (fun _ => term.1) = _
  rw [same]
  exact focused term.1

/-! ## The interface of the closed terms of a sort -/

/-- The interface of the closed terms of a sort. -/
def closedInterface (sort : LangSort presentation.language) : Interface where
  type := .base sort.1
  stage := []

/-- A closed term of a sort is a term of its closed interface. -/
def ofClosed {sort : LangSort presentation.language}
    (term : ClosedTerm presentation.language sort) :
    Term presentation.language (closedInterface sort) :=
  ⟨term.1, term.2.1, term.2.2.2.1, term.2.2.2.2.1, term.2.2.2.2.2⟩

/-- A term of the closed interface of a sort is a closed term of the sort. -/
def toClosed {sort : LangSort presentation.language}
    (term : Term presentation.language (closedInterface sort)) :
    ClosedTerm presentation.language sort :=
  ⟨term.1, term.2.1, ground_of_closed_sorting (sort := sort) term.2.1 term.2.2.2.1 term.2.2.2.2,
    term.2.2.1, term.2.2.2.1, term.2.2.2.2⟩

/-- The closed terms of a sort are the terms of its closed interface. -/
def closedEquiv (sort : LangSort presentation.language) :
    ClosedTerm presentation.language sort ≃ Term presentation.language (closedInterface sort) where
  toFun := ofClosed
  invFun := toClosed
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end Mettapedia.GSLT.LanguageDef.Contexts
