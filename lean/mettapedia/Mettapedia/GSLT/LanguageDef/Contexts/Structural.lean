import Mettapedia.GSLT.LanguageDef.Contexts.Presented
import Mettapedia.GSLT.LanguageDef.EquationSimulation
import Mettapedia.GSLT.Contexts.TransitionProfile

/-!
# Maps of declarations as maps of theories

A map of declarations acts on terms and on contexts, and the two actions
commute with filling on the nose.  It is a map of theories as soon as it
preserves the static equivalence.  It is a morphism as soon as it also
preserves reductions and reflects the reductions of images: then what every
probe sees is preserved.

Preservation of bisimilarity for reduction alone does not make a map of
declarations a morphism; the reflection of reductions is what is used.  When
the two presentations carry no equation, the three conditions are conditions
on the raw reduction relation.

The first two conditions follow from complete declaration transport,
including algebraic unit references, under the evaluator's transport laws.
Constructor injectivity is unnecessary. Reflection of reductions remains a
separate condition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.EquationSimulation
open Mettapedia.GSLT.LanguageDef.StructuralSimulation
open Mettapedia.GSLT.LanguageDef.SymbolMapSimulation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

variable (base : BasePremiseEvaluator) {source target : ValidatedLanguageDef}

/-- The image of a context under a map of declarations. -/
def Context.map (morphism : StructuralMorphism source target) {arity : Type}
    {holes : arity → Interface} {result : Interface} (context : Context source holes result) :
    Context target (fun index => (holes index).map morphism.symbols)
      (result.map morphism.symbols) where
  shape := mapContextSymbols morphism.symbols context.shape
  linear := linear_mapContextSymbols context.linear morphism.symbols
  sorted := fun {final} next filling => by
    have composed := context.sorted (morphism.comp next) fun index =>
      ⟨(filling index).1, by
        change OpenPatternWellSorted _ _
          ((holes index).map (morphism.symbols.comp next.symbols)).stage
          ((holes index).map (morphism.symbols.comp next.symbols)).type _
        rw [Interface.map_comp]
        exact (filling index).2⟩
    change OpenPatternWellSorted _ _ (result.map (morphism.symbols.comp next.symbols)).stage
      (result.map (morphism.symbols.comp next.symbols)).type
      ((mapContextSymbols (morphism.symbols.comp next.symbols) context.shape).fill _) at composed
    rwa [Interface.map_comp, mapContextSymbols_comp] at composed

/-- **Filling commutes with the action of a map of declarations.** -/
theorem Term.map_fill (morphism : StructuralMorphism source target) {arity : Type}
    {holes : arity → Interface} {result : Interface} (context : Context source holes result)
    (filling : (index : arity) → Term source.language (holes index)) :
    Term.map morphism (context.fill filling) =
      (Context.map morphism context).fill fun index => Term.map morphism (filling index) :=
  Subtype.ext (fill_mapContextSymbols morphism.symbols _ context.shape).symm

/-- Filling commutes with the action up to the static equivalence, the
equality read in the setoid of the target. -/
theorem Term.map_fill_equiv (morphism : StructuralMorphism source target) {arity : Type}
    {holes : arity → Interface} {result : Interface} (context : Context source holes result)
    (filling : (index : arity) → Term source.language (holes index)) :
    (termSetoid base target.language (result.map morphism.symbols)).r
      (Term.map morphism (context.fill filling))
      ((Context.map morphism context).fill fun index => Term.map morphism (filling index)) := by
  rw [Term.map_fill]
  exact Relation.EqvGen.refl _

/-- Placing a term in the image of a label that is a one-hole context plugs
it into the image of that context. -/
theorem apply_map_label (morphism : StructuralMorphism source target)
    {origin result : Interface} (label : Context source (fun _ : Unit => origin) result)
    {context : OneHoleContext} (shape : label.shape = MultiHoleContext.ofOneHole context)
    (term : Term target.language (origin.map morphism.symbols)) :
    ((contextTheory base target).apply (Context.map morphism label) term).1 =
      (CIGSLT.mapOneHoleContext morphism.symbols context).fill term.1 := by
  change (mapContextSymbols morphism.symbols label.shape).fill (fun _ => term.1) = _
  rw [shape, mapContextSymbols_ofOneHole, MultiHoleContext.fill_ofOneHole]

/-- The image of the hole acts on every term of the target as the identity. -/
theorem apply_map_identity (morphism : StructuralMorphism source target) (origin : Interface)
    (term : Term target.language (origin.map morphism.symbols)) :
    (contextTheory base target).apply
      (Context.map morphism (Context.identity (presentation := source) origin)) term = term :=
  Subtype.ext rfl

/-- The map preserves the static equivalence of every interface. -/
def PreservesEquations (morphism : StructuralMorphism source target) : Prop :=
  ∀ {interface : Interface} {left right : Term source.language interface},
    (termSetoid base source.language interface).r left right →
      (termSetoid base target.language (interface.map morphism.symbols)).r
        (Term.map morphism left) (Term.map morphism right)

/-- A map that carries every equation step to an equation step preserves the
static equivalence. -/
theorem preservesEquations_of_contextSteps (morphism : StructuralMorphism source target)
    (steps : ∀ {left right : Pattern}, EquationContextStep base source.language left right →
      EquationContextStep base target.language (mapPattern morphism.symbols left)
        (mapPattern morphism.symbols right)) :
    PreservesEquations base morphism := by
  intro interface left right equivalent
  induction equivalent with
  | rel left right step => exact Relation.EqvGen.rel _ _ (steps step)
  | refl term => exact Relation.EqvGen.refl _
  | symm left right _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans left middle right _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- **A map of declarations that preserves the static equivalence is a map of
theories.** -/
def structuralContextMap (morphism : StructuralMorphism source target)
    (equations : PreservesEquations base morphism) :
    ContextMap (contextTheory base source) (contextTheory base target) where
  interface := fun interface => interface.map morphism.symbols
  term := Term.map morphism
  context := Context.map morphism
  term_resp := equations
  equivariant := fun context filling => Term.map_fill_equiv base morphism context filling

/-- The map preserves reduction at every interface. -/
def PreservesSteps (morphism : StructuralMorphism source target) : Prop :=
  ∀ {interface : Interface} {term next : Term source.language interface},
    TermStep base source.language term next →
      TermStep base target.language (Term.map morphism term) (Term.map morphism next)

/-- Reductions of images are images of reductions, up to the static
equivalence. -/
def ReflectsSteps (morphism : StructuralMorphism source target) : Prop :=
  ∀ {interface : Interface} {term : Term source.language interface}
    {next : Term target.language (interface.map morphism.symbols)},
    TermStep base target.language (Term.map morphism term) next →
      ∃ next' : Term source.language interface,
        TermStep base source.language term next' ∧
          (termSetoid base target.language (interface.map morphism.symbols)).r next
            (Term.map morphism next')

theorem structuralContextMap_preservesTransitions (morphism : StructuralMorphism source target)
    (equations : PreservesEquations base morphism) (steps : PreservesSteps base morphism) :
    (structuralContextMap base morphism equations).PreservesTransitions :=
  (structuralContextMap base morphism equations).preservesTransitions_of_rewrites steps

theorem structuralContextMap_reflectsTransitions (morphism : StructuralMorphism source target)
    (equations : PreservesEquations base morphism) (reflects : ReflectsSteps base morphism) :
    (structuralContextMap base morphism equations).ReflectsTransitions :=
  (structuralContextMap base morphism equations).reflectsTransitions_of_rewrites reflects

/-- **A map of declarations that preserves the static equivalence, preserves
reductions and reflects the reductions of images is a morphism of
theories.** -/
def structuralContextMorphism (morphism : StructuralMorphism source target)
    (equations : PreservesEquations base morphism) (steps : PreservesSteps base morphism)
    (reflects : ReflectsSteps base morphism) :
    ContextMorphism (contextTheory base source) (contextTheory base target) :=
  ContextMorphism.ofTransitions (structuralContextMap base morphism equations)
    (structuralContextMap_preservesTransitions base morphism equations steps)
    (structuralContextMap_reflectsTransitions base morphism equations reflects)

/-! ## Presentations without equations -/

/-- In a presentation without equations the static equivalence of an
interface is equality. -/
theorem termSetoid_iff_eq (language : LanguageDef) (free : language.isEquationFree = true)
    {interface : Interface} (left right : Term language interface) :
    (termSetoid base language interface).r left right ↔ left = right := by
  constructor
  · intro equivalent
    induction equivalent with
    | rel left right step =>
        exact Subtype.ext ((equationEquiv_iff_eq_of_no_generators free left.1 right.1).mp
          (Relation.EqvGen.rel _ _ step))
    | refl term => rfl
    | symm left right _ recurse => exact recurse.symm
    | trans left middle right _ _ first second => exact first.trans second
  · rintro rfl
    exact Relation.EqvGen.refl left

/-- In a presentation without equations a reduction between terms of an
interface is a reduction of the patterns. -/
theorem termStep_iff_step (language : LanguageDef) (free : language.isEquationFree = true)
    {interface : Interface} (term next : Term language interface) :
    TermStep base language term next ↔ Step base language term.1 next.1 := by
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    obtain rfl := (termSetoid_iff_eq base language free _ _).mp before
    obtain rfl := (termSetoid_iff_eq base language free _ _).mp after
    exact step
  · intro step
    exact ⟨term, next, Relation.EqvGen.refl _, step, Relation.EqvGen.refl _⟩

/-- A map out of a presentation without equations preserves the static
equivalence. -/
theorem preservesEquations_of_equationFree (morphism : StructuralMorphism source target)
    (free : source.language.isEquationFree = true) : PreservesEquations base morphism := by
  intro interface left right equivalent
  obtain rfl := (termSetoid_iff_eq base source.language free _ _).mp equivalent
  exact Relation.EqvGen.refl _

/-- Between presentations without equations, a map that preserves the
reductions of patterns preserves reduction at every interface. -/
theorem preservesSteps_of_equationFree (morphism : StructuralMorphism source target)
    (sourceFree : source.language.isEquationFree = true)
    (targetFree : target.language.isEquationFree = true)
    (steps : ∀ {pattern next : Pattern}, Step base source.language pattern next →
      Step base target.language (mapPattern morphism.symbols pattern)
        (mapPattern morphism.symbols next)) :
    PreservesSteps base morphism := by
  intro interface term next step
  rw [termStep_iff_step base _ sourceFree] at step
  rw [termStep_iff_step base _ targetFree]
  exact steps step

/-- Between presentations without equations, a map reflects reduction at
every interface when every reduction of the image of a term is the image of
a reduction to a term of the same interface. -/
theorem reflectsSteps_of_equationFree (morphism : StructuralMorphism source target)
    (sourceFree : source.language.isEquationFree = true)
    (targetFree : target.language.isEquationFree = true)
    (reflects : ∀ {interface : Interface} (term : Term source.language interface)
      {next : Pattern}, Step base target.language (mapPattern morphism.symbols term.1) next →
        ∃ next' : Term source.language interface,
          Step base source.language term.1 next'.1 ∧
            next = mapPattern morphism.symbols next'.1) :
    ReflectsSteps base morphism := by
  intro interface term next step
  rw [termStep_iff_step base _ targetFree] at step
  obtain ⟨next', sourceStep, same⟩ := reflects term step
  refine ⟨next', (termStep_iff_step base _ sourceFree _ _).mpr sourceStep, ?_⟩
  have equal : next = Term.map morphism next' := Subtype.ext same
  rw [equal]
  exact Relation.EqvGen.refl _

/-! ## Complete declaration transport -/

/-- Complete declaration transport preserves equivalence at every typed
interface; unit names are transported as algebra references. -/
theorem preservesEquations_transport (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base)
    (baseMono : ∀ bindings premise result,
      result ∈ base (mapLanguageDef morphism.symbols source.language) bindings premise →
        result ∈ base target.language bindings premise) :
    PreservesEquations base morphism :=
  preservesEquations_of_contextSteps base morphism fun step =>
    equationContextStep_transport_of_structuralMorphism morphism mapsBaseResults baseMono step

/-- Complete declaration transport preserves reduction at every interface. -/
theorem preservesSteps_transport (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base)
    (baseMono : ∀ bindings premise result,
      result ∈ base (mapLanguageDef morphism.symbols source.language) bindings premise →
        result ∈ base target.language bindings premise) :
    PreservesSteps base morphism := by
  intro interface term next step
  obtain ⟨redex, contractum, before, primitive, after⟩ := step
  have equations : PreservesEquations base morphism :=
    preservesEquations_transport base morphism mapsBaseResults baseMono
  exact ⟨Term.map morphism redex, Term.map morphism contractum, equations before,
    SymbolMapSimulation.step_map_of_structuralMorphism morphism mapsBaseResults baseMono
      primitive, equations after⟩

/-- With no external relation, a declaration map need only preserve the
built-in equality relation to transport static equivalence. -/
theorem preservesEquations_transport_default (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq") :
    PreservesEquations (engineBasePremises RelationEnv.empty) morphism :=
  preservesEquations_transport _ morphism
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols relationFixesEq)
    (engineBasePremises_empty_mono _ _)

/-- With no external relation, complete declaration transport also
preserves reductions modulo equations. -/
theorem preservesSteps_transport_default (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq") :
    PreservesSteps (engineBasePremises RelationEnv.empty) morphism :=
  preservesSteps_transport _ morphism
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols relationFixesEq)
    (engineBasePremises_empty_mono _ _)

/-! ## Maps that fix the declared units -/

/-- **A map of declarations that fixes the declared units preserves the
static equivalence of every interface.**  The evaluator hypotheses are those
under which reduction is carried along the map. -/
theorem preservesEquations_of_fixesUnits (morphism : StructuralMorphism source target)
    (units : FixesDeclaredUnits morphism.symbols source.language)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base)
    (baseMono : ∀ bindings premise result,
      result ∈ base (mapLanguageDef morphism.symbols source.language) bindings premise →
        result ∈ base target.language bindings premise) :
    PreservesEquations base morphism :=
  preservesEquations_of_contextSteps base morphism fun step =>
    equationContextStep_map_of_structuralMorphism morphism units mapsBaseResults baseMono step

/-- **Such a map preserves reduction at every interface.**  Reduction at an
interface is reduction of patterns between equivalent terms of the interface,
and the map carries both. -/
theorem preservesSteps_of_fixesUnits (morphism : StructuralMorphism source target)
    (units : FixesDeclaredUnits morphism.symbols source.language)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base)
    (baseMono : ∀ bindings premise result,
      result ∈ base (mapLanguageDef morphism.symbols source.language) bindings premise →
        result ∈ base target.language bindings premise) :
    PreservesSteps base morphism := by
  intro interface term next step
  obtain ⟨redex, contractum, before, primitive, after⟩ := step
  have equations : PreservesEquations base morphism :=
    preservesEquations_of_fixesUnits base morphism units mapsBaseResults baseMono
  exact ⟨Term.map morphism redex, Term.map morphism contractum, equations before,
    SymbolMapSimulation.step_map_of_structuralMorphism morphism mapsBaseResults baseMono
      primitive,
    equations after⟩

/-- For the evaluator with no external relation the evaluator hypotheses
reduce to one condition on names: the relation map fixes the built-in
relation `"eq"`. -/
theorem preservesEquations_default (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    (units : FixesDeclaredUnits morphism.symbols source.language) :
    PreservesEquations (engineBasePremises RelationEnv.empty) morphism :=
  preservesEquations_of_fixesUnits _ morphism units
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols
      relationFixesEq)
    (engineBasePremises_empty_mono _ _)

/-- Reduction at every interface is preserved, for the evaluator with no
external relation. -/
theorem preservesSteps_default (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    (units : FixesDeclaredUnits morphism.symbols source.language) :
    PreservesSteps (engineBasePremises RelationEnv.empty) morphism :=
  preservesSteps_of_fixesUnits _ morphism units
    (SymbolMapSimulation.engineBasePremises_empty_maps_results morphism.symbols
      relationFixesEq)
    (engineBasePremises_empty_mono _ _)

/-- **A map of declarations that reflects the reductions of images is a
morphism of theories.**  Preservation of the static equivalence and of
reductions is proved, not assumed; the two conditions on names are that the
built-in relation and the declared units keep theirs. -/
def structuralContextMorphism_of_reflects (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    (units : FixesDeclaredUnits morphism.symbols source.language)
    (reflects : ReflectsSteps (engineBasePremises RelationEnv.empty) morphism) :
    ContextMorphism (contextTheory (engineBasePremises RelationEnv.empty) source)
      (contextTheory (engineBasePremises RelationEnv.empty) target) :=
  structuralContextMorphism _ morphism
    (preservesEquations_default morphism relationFixesEq units)
    (preservesSteps_default morphism relationFixesEq units) reflects

end Mettapedia.GSLT.LanguageDef.Contexts
