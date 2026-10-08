import Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeExclusion

/-!
# Complete observers reconstruct source classes with admitted original rules

Actual combined-family ask steps recover every supplied source tuple. The
earned nonunit original-rule exclusion then makes each get successor the
complete selected child. Induction on the independently formed source term
reconstructs its AC1 class against any right-hand representative. The
bisimulation quantifies every literal categorical label, without a root
decoder or a chosen structural equality observation.

Receipt origins must be inhabited. Original declarations are independently
supplied and need only their local nonunit-redex admission. This does not
identify literal labels with the paper's payload-sensitive label classes,
admit arbitrary equations or binding, or price semantic matching.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

def combinedSourceRules
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (Origins : Type w) : ReactionRule (.origin : ContextCategory arity) → Prop :=
  fun rule => rules arity Origins rule ∨ Source.mappedRules sourceRules rule

variable (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
variable (nonunit : ∀ original, sourceRules original → Source.NonunitRedex original)

include nonunit

theorem combined_observer_constructor_arguments
    (origins : Nonempty Origins) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (right : Source.ValueClass arity)
    (related : IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode constructor arguments))))
      (RawArrow.value (Source.classEmbedding right))) :
    ∃ before : Fin (sourceArity arity constructor) → Source.Value arity,
      right = classOf (Source.sourceNode constructor before) ∧
      ∀ position, IPOBisimilar (combinedSourceRules sourceRules Origins)
        (RawArrow.value (Source.classEmbedding (classOf (arguments position))))
        (RawArrow.value (Source.classEmbedding (classOf (before position)))) := by
  obtain ⟨origin⟩ := origins
  have askStep : ActIPO (combinedSourceRules sourceRules Origins) (askLabel constructor)
      (RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode constructor arguments))))
      (RawArrow.value (sourceBundle constructor arguments)) :=
    (combined_ask_source_step_iff sourceRules constructor _ _).mpr ⟨origin, arguments, rfl, rfl⟩
  obtain ⟨matched, matchedStep, tupleRelated⟩ := ipoBisimilar_forward related askStep
  obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
    (combined_ask_source_step_iff sourceRules constructor right matched).mp matchedStep
  rw [wholeTarget] at tupleRelated
  refine ⟨before, rightRead, ?_⟩
  intro position
  have getStep : ActIPO (combinedSourceRules sourceRules Origins) (getLabel constructor position)
      (RawArrow.value (sourceBundle constructor arguments))
      (RawArrow.value (Source.classEmbedding (classOf (arguments position)))) :=
    (combined_nonunit_get_source_step_iff sourceRules nonunit constructor arguments position _).mpr
      ⟨⟨origin⟩, rfl⟩
  obtain ⟨after, afterStep, childRelated⟩ := ipoBisimilar_forward tupleRelated getStep
  have childRead := ((combined_nonunit_get_source_step_iff sourceRules nonunit
    constructor before position after).mp afterStep).2
  rw [childRead] at childRelated
  exact childRelated

private theorem raw_source_combined_observer_separation
    (origins : Nonempty Origins) {sort : (Source.signature arity).Srt}
    (left : Term (Source.signature arity) (Source.Parallel arity) sort) :
    ∀ right : Source.ValueClass arity, IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (Source.embed left)))
      (RawArrow.value (Source.classEmbedding right)) →
      classOf (Source.embed left) = Source.classEmbedding right := by
  apply @Term.rec (Source.signature arity) (Source.Parallel arity)
    (fun _ left => ∀ right : Source.ValueClass arity, IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (Source.embed left)))
      (RawArrow.value (Source.classEmbedding right)) →
      classOf (Source.embed left) = Source.classEmbedding right) (t := left)
  · intro sort parallel right related
    obtain ⟨before, rightRead, _children⟩ := combined_observer_constructor_arguments sourceRules nonunit
      origins .unit (fun position => Fin.elim0 position) right related
    exact congrArg Source.classEmbedding rightRead.symm
  · intro sort parallel first second firstInduction secondInduction right related
    change sort = ULift.up () at parallel
    subst sort
    let arguments : Fin 2 → Source.Value arity := Fin.cases first (fun _ => second)
    obtain ⟨before, rightRead, children⟩ :=
      combined_observer_constructor_arguments sourceRules nonunit origins .properCut arguments right related
    have firstRead : classOf first = classOf (before 0) :=
      Source.classEmbedding_injective (firstInduction _ (children 0))
    have secondRead : classOf second = classOf (before 1) :=
      Source.classEmbedding_injective (secondInduction _ (children 1))
    have constructorRead : classOf (.cut rfl first second : Source.Value arity) =
        classOf (Source.sourceNode .properCut before) :=
      Quotient.sound (Equation.cut rfl (Quotient.exact firstRead) (Quotient.exact secondRead))
    exact congrArg Source.classEmbedding (constructorRead.trans rightRead.symm)
  · intro constructor arguments inductionHypothesis right related
    obtain ⟨before, rightRead, children⟩ :=
      combined_observer_constructor_arguments sourceRules nonunit origins (.ordinary constructor) arguments right related
    have coordinates : ∀ position, classOf (arguments position) = classOf (before position) :=
      fun position => Source.classEmbedding_injective (inductionHypothesis position _ (children position))
    have constructorRead := (node_class_eq_iff (signature := Source.signature arity)
      (Parallel := Source.Parallel arity) constructor arguments before).mpr coordinates
    exact congrArg Source.classEmbedding (constructorRead.trans rightRead.symm)

theorem combined_observer_bisimilar_iff_source_equal (origins : Nonempty Origins)
    (first second : Source.ValueClass arity) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (Source.classEmbedding first))
      (RawArrow.value (Source.classEmbedding second)) ↔ first = second := by
  constructor
  · refine Quotient.inductionOn first ?_
    intro raw related
    exact Source.classEmbedding_injective
      (raw_source_combined_observer_separation sourceRules nonunit origins raw second related)
  · intro same
    subst second
    exact ipoBisimilar_refl _ _

theorem combined_observer_raw_bisimilar_iff_source_equation (origins : Nonempty Origins)
    (first second : Source.Value arity) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (Source.embed first)))
      (RawArrow.value (classOf (Source.embed second))) ↔ Equation first second :=
  (combined_observer_bisimilar_iff_source_equal sourceRules nonunit origins
    (classOf first) (classOf second)).trans
      ⟨fun same => Quotient.exact same, fun equation => Quotient.sound equation⟩

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
