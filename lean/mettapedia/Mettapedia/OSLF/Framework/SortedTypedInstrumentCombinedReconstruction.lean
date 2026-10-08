import Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalProbeTargetSupport

/-!
# Complete many-sorted reconstruction with arbitrary original reactions

Literal categorical IPO bisimulation uses every native interface and label.
An ask successor retains a whole heterogeneous tuple. Each matched get
successor is recursively reconstructed at its own original sort before its
earned zero support excludes a competing original-rule successor. Source
unit redexes are allowed and get targets need not be unique.

The right value is arbitrary native syntax. Administrative origins are
inhabited explicitly; no inhabitance of a source sort, total source erasure,
current-view characterization or binder/RUN behavior is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}
variable (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)

private theorem combined_constructor_reconstruction
    (origins : Nonempty Origins) (head : SourceHead source Parallel)
    (arguments : (position : Fin (headArity head)) → Term source Parallel (headInput head position))
    (childRecovery : ∀ position
      (right : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position))),
      IPOBisimilar (combinedSourceRules sourceRules Origins)
        (RawArrow.value (classOf (embed (arguments position)))) (RawArrow.value right) →
          classOf (embed (arguments position)) = right)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (related : IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (sourceNode head (fun position => embed (arguments position)))))
      (RawArrow.value right)) :
    classOf (sourceNode head (fun position => embed (arguments position))) = right := by
  obtain ⟨origin⟩ := origins
  let embedded : Arguments head := fun position => embed (arguments position)
  have askStep : ActIPO (combinedSourceRules sourceRules Origins) (probeLabel (.ask head))
      (RawArrow.value (classOf (sourceNode head embedded)))
      (RawArrow.value (classOf (bundle head embedded))) := by
    obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := (Occurrence.ask origin head embedded).direct_step
    exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩
  obtain ⟨matched, matchedStep, tupleRelated⟩ := ipoBisimilar_forward related askStep
  cases matched with
  | value matched =>
    obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
      (combined_ask_step_iff sourceRules head right matched).mp matchedStep
    rw [wholeTarget] at tupleRelated
    have coordinates : ∀ position, classOf (embedded position) = classOf (before position) := by
      intro position
      have getStep : ActIPO (combinedSourceRules sourceRules Origins) (probeLabel (.get head position))
          (RawArrow.value (classOf (bundle head embedded)))
          (RawArrow.value (classOf (embedded position))) := by
        obtain ⟨rule, admitted, reaction, square, minimal, output⟩ :=
          (Occurrence.get origin head embedded position).direct_step
        exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩
      obtain ⟨after, afterStep, childRelated⟩ := ipoBisimilar_forward tupleRelated getStep
      cases after with
      | value after =>
        have recovered : classOf (embedded position) = after := childRecovery position after childRelated
        have pureAfter : classObserverCount after = 0 := by
          rw [← recovered]
          exact classObserverCount_embedding (classOf (arguments position))
        have actualCoordinate := (combined_get_pure_result_readout sourceRules
          head before position after pureAfter afterStep).2
        exact recovered.trans actualCoordinate
    exact (sourceNode_class_congruence head embedded before coordinates).trans rightRead.symm

private theorem raw_source_combined_reconstruction
    (origins : Nonempty Origins) {sort : source.Srt} (left : Term source Parallel sort) :
    ∀ right : ValueClass (source := source) (Parallel := Parallel) (.original sort),
      IPOBisimilar (combinedSourceRules sourceRules Origins)
        (RawArrow.value (classOf (embed left))) (RawArrow.value right) → classOf (embed left) = right := by
  apply @Term.rec source Parallel
    (fun sort left => ∀ right : ValueClass (source := source) (Parallel := Parallel) (.original sort),
      IPOBisimilar (combinedSourceRules sourceRules Origins)
        (RawArrow.value (classOf (embed left))) (RawArrow.value right) → classOf (embed left) = right) (t := left)
  · intro sort parallel right related
    exact combined_constructor_reconstruction sourceRules origins (.unit sort parallel)
      (fun position => Fin.elim0 position) (fun position => Fin.elim0 position) right related
  · intro sort parallel first second firstInduction secondInduction right related
    let arguments : Fin 2 → Term source Parallel sort := Fin.cases first (fun _ => second)
    have recoveries : ∀ position (after : ValueClass (source := source) (Parallel := Parallel) (.original sort)),
        IPOBisimilar (combinedSourceRules sourceRules Origins)
          (RawArrow.value (classOf (embed (arguments position)))) (RawArrow.value after) →
            classOf (embed (arguments position)) = after := by
      intro position
      fin_cases position
      · exact firstInduction
      · exact secondInduction
    exact combined_constructor_reconstruction sourceRules origins (.properCut sort parallel)
      arguments recoveries right related
  · intro constructor arguments inductionHypothesis right related
    exact combined_constructor_reconstruction sourceRules origins (.ordinary constructor)
      arguments inductionHypothesis right related

theorem combined_observer_bisimilar_iff_embedded_equal (origins : Nonempty Origins)
    {sort : source.Srt} (left : Class source Parallel sort)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original sort)) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classEmbedding left)) (RawArrow.value right) ↔ classEmbedding left = right := by
  constructor
  · refine Quotient.inductionOn left ?_
    intro raw related
    exact raw_source_combined_reconstruction sourceRules origins raw right related
  · intro same
    rw [same]
    exact ipoBisimilar_refl _ _

theorem combined_observer_bisimilar_iff_source_equal_all_rules (origins : Nonempty Origins)
    {sort : source.Srt} (first second : Class source Parallel sort) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classEmbedding first)) (RawArrow.value (classEmbedding second)) ↔ first = second :=
  (combined_observer_bisimilar_iff_embedded_equal sourceRules origins first (classEmbedding second)).trans
    ⟨fun same => classEmbedding_injective same, fun same => congrArg classEmbedding same⟩

theorem combined_observer_raw_bisimilar_iff_source_equation_all_rules (origins : Nonempty Origins)
    {sort : source.Srt} (first second : Term source Parallel sort) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (embed first))) (RawArrow.value (classOf (embed second))) ↔ Equation first second :=
  (combined_observer_bisimilar_iff_source_equal_all_rules sourceRules origins (classOf first) (classOf second)).trans
    ⟨fun same => Quotient.exact same, fun equation => Quotient.sound equation⟩

theorem combined_source_context_congruence (origins : Nonempty Origins) {firstSort secondSort : source.Srt}
    (context : ContextClass source Parallel firstSort secondSort) {first second : Class source Parallel firstSort}
    (related : IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classEmbedding first)) (RawArrow.value (classEmbedding second))) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classEmbedding (context.fill first)))
      (RawArrow.value (classEmbedding (context.fill second))) := by
  have same := (combined_observer_bisimilar_iff_source_equal_all_rules sourceRules origins first second).mp related
  exact (combined_observer_bisimilar_iff_source_equal_all_rules sourceRules origins
    (context.fill first) (context.fill second)).mpr (congrArg context.fill same)

end Mettapedia.OSLF.Framework.SortedTypedInstruments
