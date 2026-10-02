import Mettapedia.GSLT.LanguageDef.Contexts.Structural
import Mettapedia.GSLT.Contexts.Traces

/-!
# Invertible maps of declarations

Two presentations related by a renaming of their declarations present one
theory.  An invertible map preserving equations is faithful and exhausting:
it reflects the static equivalence because its inverse preserves it, and
every context of the target between images of interfaces is the image of its
own image under the inverse.  When the map and its inverse preserve
reductions, the map is hosting and a morphism, and the two presentations lie in one degree of
the comparison of theories, by bisimilarity and by traces, and bisimilarity
over all contexts of one is bisimilarity over all contexts of the other.

This gives the two conditions an inhabitant other than the identity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## Equal interfaces -/

/-- A term of an interface is a term of an equal interface. -/
def Term.reindex {language : LanguageDef} {first second : Interface} (same : first = second)
    (term : Term language first) : Term language second :=
  ⟨term.1, by subst same; exact term.2⟩

@[simp] theorem Term.reindex_val {language : LanguageDef} {first second : Interface}
    (same : first = second) (term : Term language first) : (term.reindex same).1 = term.1 :=
  rfl

/-- A context between interfaces is a context between equal interfaces. -/
def Context.reindex {presentation : ValidatedLanguageDef} {arity : Type}
    {holes holes' : arity → Interface} {result result' : Interface}
    (holesSame : ∀ index, holes index = holes' index) (resultSame : result = result')
    (context : Context presentation holes result) : Context presentation holes' result' where
  shape := context.shape
  linear := context.linear
  sorted := fun next filling => by
    obtain rfl : holes = holes' := funext holesSame
    subst resultSame
    exact context.sorted next filling

@[simp] theorem Context.reindex_shape {presentation : ValidatedLanguageDef} {arity : Type}
    {holes holes' : arity → Interface} {result result' : Interface}
    (holesSame : ∀ index, holes index = holes' index) (resultSame : result = result')
    (context : Context presentation holes result) :
    (context.reindex holesSame resultSame).shape = context.shape :=
  rfl

variable (base : BasePremiseEvaluator)

/-- Equal terms are statically equivalent. -/
theorem termSetoid_of_eq {language : LanguageDef} {interface : Interface}
    {left right : Term language interface} (same : left = right) :
    (termSetoid base language interface).r left right := by
  subst same
  exact (termSetoid base language interface).iseqv.refl _

/-- The static equivalence of an interface is that of an equal interface, on
terms with the same patterns. -/
theorem termSetoid_of_interface_eq {language : LanguageDef} {first second : Interface}
    (same : first = second) {left right : Term language first}
    {left' right' : Term language second} (leftSame : left.1 = left'.1)
    (rightSame : right.1 = right'.1)
    (equivalent : (termSetoid base language first).r left right) :
    (termSetoid base language second).r left' right' := by
  subst same
  obtain rfl : left = left' := Subtype.ext leftSame
  obtain rfl : right = right' := Subtype.ext rightSame
  exact equivalent

/-- Reduction at an interface is reduction at an equal interface, on terms
with the same patterns. -/
theorem termStep_of_interface_eq {language : LanguageDef} {first second : Interface}
    (same : first = second) {term next : Term language first}
    {term' next' : Term language second} (termSame : term.1 = term'.1)
    (nextSame : next.1 = next'.1) (step : TermStep base language term next) :
    TermStep base language term' next' := by
  subst same
  obtain rfl : term = term' := Subtype.ext termSame
  obtain rfl : next = next' := Subtype.ext nextSame
  exact step

/-! ## Inverse maps of declarations -/

variable {source target : ValidatedLanguageDef}

/-- Two maps of declarations are inverse to each other when each composite
acts on symbols as the identity. -/
structure Inverse (forward : StructuralMorphism source target)
    (backward : StructuralMorphism target source) : Prop where
  /-- Going to the target and back returns every symbol of the source. -/
  sourceRoundTrip : forward.symbols.comp backward.symbols = LanguageDefSymbolMap.id
  /-- Going to the source and back returns every symbol of the target. -/
  targetRoundTrip : backward.symbols.comp forward.symbols = LanguageDefSymbolMap.id

namespace Inverse

variable {forward : StructuralMorphism source target}
  {backward : StructuralMorphism target source} (inverse : Inverse forward backward)

include inverse

/-- The inverse of the inverse. -/
theorem symm : Inverse backward forward :=
  ⟨inverse.targetRoundTrip, inverse.sourceRoundTrip⟩

theorem interface_roundTrip (interface : Interface) :
    (interface.map forward.symbols).map backward.symbols = interface := by
  rw [← Interface.map_comp, inverse.sourceRoundTrip, Interface.map_id]

theorem pattern_roundTrip (pattern : Pattern) :
    mapPattern backward.symbols (mapPattern forward.symbols pattern) = pattern := by
  rw [← mapPattern_comp, inverse.sourceRoundTrip, mapPattern_id]

theorem shape_roundTrip {ι : Type} (context : MultiHoleContext ι) :
    mapContextSymbols backward.symbols (mapContextSymbols forward.symbols context) = context := by
  rw [← mapContextSymbols_comp, inverse.sourceRoundTrip, mapContextSymbols_id]

/-- An invertible map preserving equations is faithful: its inverse preserves
the static equivalence, so it reflects it. -/
theorem faithful (equations : PreservesEquations base forward)
    (backEquations : PreservesEquations base backward) :
    (structuralContextMap base forward equations).Faithful := by
  rw [ContextMap.faithful_iff_reflectsEquations]
  intro origin first second equivalent
  exact termSetoid_of_interface_eq base (inverse.interface_roundTrip origin)
    (inverse.pattern_roundTrip first.1) (inverse.pattern_roundTrip second.1)
    (backEquations equivalent)

/-- **An invertible map of declarations is exhausting**: a context of the
target between images of interfaces is the image of its image under the
inverse. -/
theorem exhausting (equations : PreservesEquations base forward) :
    (structuralContextMap base forward equations).Exhausting := by
  intro arity holes result observer
  refine ⟨(Context.map backward observer).reindex
    (fun index => inverse.interface_roundTrip (holes index))
    (inverse.interface_roundTrip result), fun filling => ?_⟩
  exact termSetoid_of_eq base (Subtype.ext
    (congrArg (MultiHoleContext.fill fun index => (Term.map forward (filling index)).1)
      (inverse.symm.shape_roundTrip observer.shape)))

/-- The reductions of images are images of reductions, because the inverse
preserves reductions. -/
theorem reflectsSteps (backSteps : PreservesSteps base backward) :
    ReflectsSteps base forward := by
  intro interface term next step
  refine ⟨(Term.map backward next).reindex (inverse.interface_roundTrip interface), ?_, ?_⟩
  · exact termStep_of_interface_eq base (inverse.interface_roundTrip interface)
      (inverse.pattern_roundTrip term.1) rfl (backSteps step)
  · exact termSetoid_of_eq base (Subtype.ext (inverse.symm.pattern_roundTrip next.1).symm)

/-- An invertible map preserving equations and reductions in both directions
is hosting.  Its static and operational obligations are proved separately. -/
theorem hosting (equations : PreservesEquations base forward)
    (backEquations : PreservesEquations base backward) (steps : PreservesSteps base forward)
    (backSteps : PreservesSteps base backward) :
    (structuralContextMap base forward equations).Hosting :=
  ⟨inverse.faithful base equations backEquations,
    structuralContextMap_preservesTransitions base forward equations steps,
    structuralContextMap_reflectsTransitions base forward equations
      (inverse.reflectsSteps base backSteps)⟩

/-- **An invertible map of declarations that preserves reductions in both
directions is a morphism of theories.** -/
def morphism (equations : PreservesEquations base forward)
    (steps : PreservesSteps base forward) (backSteps : PreservesSteps base backward) :
    ContextMorphism (contextTheory base source) (contextTheory base target) :=
  structuralContextMorphism base forward equations steps (inverse.reflectsSteps base backSteps)

/-- **Presentations related by an invertible map of declarations lie in one
degree of the comparison of theories.** -/
theorem embeds (equations : PreservesEquations base forward)
    (backEquations : PreservesEquations base backward) (steps : PreservesSteps base forward)
    (backSteps : PreservesSteps base backward) :
    (contextTheory base source).Embeds (contextTheory base target) ∧
      (contextTheory base target).Embeds (contextTheory base source) :=
  ⟨⟨inverse.morphism base equations steps backSteps,
      inverse.hosting base equations backEquations steps backSteps, inverse.exhausting base equations⟩,
    ⟨inverse.symm.morphism base backEquations backSteps steps,
      inverse.symm.hosting base backEquations equations backSteps steps,
      inverse.symm.exhausting base backEquations⟩⟩

/-- The two presentations also lie in one degree of the comparison up to
traces. -/
theorem traceEmbeds (equations : PreservesEquations base forward)
    (backEquations : PreservesEquations base backward) (steps : PreservesSteps base forward)
    (backSteps : PreservesSteps base backward) :
    (contextTheory base source).TraceEmbeds (contextTheory base target) :=
  ⟨structuralContextMap base forward equations,
    (structuralContextMap base forward equations).preservesTraces_of_transitions
      (structuralContextMap_preservesTransitions base forward equations steps)
      (structuralContextMap_reflectsTransitions base forward equations
        (inverse.reflectsSteps base backSteps)),
    inverse.hosting base equations backEquations steps backSteps, inverse.exhausting base equations⟩

/-- **Bisimilarity over all contexts of one presentation is bisimilarity over
all contexts of the other**, between images of interfaces. -/
theorem bisimilar_targetProbe_iff (equations : PreservesEquations base forward)
    (steps : PreservesSteps base forward) (backSteps : PreservesSteps base backward)
    {origin : Interface} {left right : Term source.language origin} :
    (structuralContextMap base forward equations).targetProbe.Bisimilar (index := origin)
        (Term.map forward left) (Term.map forward right) ↔
      (contextTheory base source).fullProbe.Bisimilar (index := origin) left right :=
  ContextMap.Exhausting.bisimilar_targetProbe_iff_source _ (inverse.exhausting base equations)
    (structuralContextMap_preservesTransitions base forward equations steps)
    (structuralContextMap_reflectsTransitions base forward equations
      (inverse.reflectsSteps base backSteps))

end Inverse

end Mettapedia.GSLT.LanguageDef.Contexts
