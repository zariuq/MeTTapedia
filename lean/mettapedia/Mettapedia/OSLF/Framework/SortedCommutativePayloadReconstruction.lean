import Mettapedia.OSLF.Framework.SortedCommutativePayloadIPOSystem
import Mettapedia.OSLF.Framework.SortedCommutativeCombinedReconstruction

/-!
# Complete source reconstruction with process-bearing labels

Label shapes are compared literally, while their process positions use the
same greatest fixed point as successor states. Actual administrative probes
have independently proved empty process-position families, so their matched
labels recover the exact categorical probe. Structural induction then reads
every complete supplied child before excluding an original-rule successor.

Original rules are arbitrary and may have unit redexes. Their get successors
need not be unique. The right state is an arbitrary native value, including
observer-bearing values. Administrative origins are inhabited explicitly.
The source equation theory here is the closed one-sort AC1 theory.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Support

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}
variable (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)

private theorem constructor_reconstruction
    (origins : Nonempty Origins) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (childRecovery : ∀ position (right : ValueClass arity .base),
      (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
        (classOf (Source.embed (arguments position))) right →
          classOf (Source.embed (arguments position)) = right)
    (right : ValueClass arity .base)
    (related : (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
      (classOf (Source.embed (Source.sourceNode constructor arguments))) right) :
    classOf (Source.embed (Source.sourceNode constructor arguments)) = right := by
  obtain ⟨origin⟩ := origins
  let embedded := fun position => Source.embed (arguments position)
  have askStep : ActIPO (combinedSourceRules sourceRules Origins) (askLabel constructor)
      (RawArrow.value (classOf (Source.embed (Source.sourceNode constructor arguments))))
      (RawArrow.value (classOf (bundle arity constructor embedded))) :=
    (combined_ask_source_step_iff sourceRules constructor _ _).mpr ⟨origin, arguments, rfl, rfl⟩
  obtain ⟨matched, matchedStep, tupleRelated⟩ :=
    bisimilar_probe_forward (combinedSourceRules sourceRules Origins) (.ask constructor) related askStep
  have administrative := (combined_ask_step_iff_administrative
    sourceRules constructor right (RawArrow.value matched)).mp matchedStep
  obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
    (ask_native_step_iff constructor right matched).mp administrative
  rw [wholeTarget] at tupleRelated
  have coordinates : ∀ position, classOf (embedded position) = classOf (before position) := by
    intro position
    have getStep : ActIPO (combinedSourceRules sourceRules Origins) (getLabel constructor position)
        (RawArrow.value (classOf (bundle arity constructor embedded)))
        (RawArrow.value (classOf (embedded position))) := by
      obtain ⟨rule, admitted, reaction, square, minimal, output⟩ :=
        (Occurrence.get origin constructor embedded position).direct_step
      exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩
    obtain ⟨after, afterStep, childRelated⟩ :=
      bisimilar_probe_forward (combinedSourceRules sourceRules Origins)
        (.get constructor position) tupleRelated getStep
    have recovered : classOf (embedded position) = after := childRecovery position after childRelated
    have pureAfter : arrowObserverCount (RawArrow.value after :
        (.origin : ContextCategory arity) ⟶ .interface .base) = 0 := by
      rw [← recovered]
      exact classObserverCount_embedding (classOf (arguments position))
    have actualCoordinate := (combined_get_pure_result_readout sourceRules
      constructor before position after pureAfter afterStep).2
    exact recovered.trans actualCoordinate
  exact (congrArg classOf (Source.sourceNode_embed constructor arguments)).trans
    ((sourceNode_class_congruence constructor embedded before coordinates).trans rightRead.symm)

private theorem raw_source_reconstruction
    (origins : Nonempty Origins) {sort : (Source.signature arity).Srt}
    (left : Term (Source.signature arity) (Source.Parallel arity) sort) :
    ∀ right : ValueClass arity .base,
      (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
        (classOf (Source.embed left)) right → classOf (Source.embed left) = right := by
  apply @Term.rec (Source.signature arity) (Source.Parallel arity)
    (fun _ left => ∀ right : ValueClass arity .base,
      (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
        (classOf (Source.embed left)) right → classOf (Source.embed left) = right) (t := left)
  · intro sort parallel right related
    exact constructor_reconstruction sourceRules origins .unit
      (fun position => Fin.elim0 position) (fun position => Fin.elim0 position) right related
  · intro sort parallel first second firstInduction secondInduction right related
    change sort = ULift.up () at parallel
    subst sort
    let arguments : Fin 2 → Source.Value arity := Fin.cases first (fun _ => second)
    have recoveries : ∀ position (after : ValueClass arity .base),
        (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
          (classOf (Source.embed (arguments position))) after →
            classOf (Source.embed (arguments position)) = after := by
      intro position
      fin_cases position
      · exact firstInduction
      · exact secondInduction
    exact constructor_reconstruction sourceRules origins .properCut arguments recoveries right related
  · intro constructor arguments inductionHypothesis right related
    exact constructor_reconstruction sourceRules origins (.ordinary constructor)
      arguments inductionHypothesis right related

theorem bisimilar_iff_embedded_equal (origins : Nonempty Origins)
    (left : Source.ValueClass arity) (right : ValueClass arity .base) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
      (Source.classEmbedding left) right ↔ Source.classEmbedding left = right := by
  constructor
  · refine Quotient.inductionOn left ?_
    intro raw related
    exact raw_source_reconstruction sourceRules origins raw right related
  · intro same
    rw [same]
    exact (firingSystem (combinedSourceRules sourceRules Origins)).bisimilar_refl .base right

theorem bisimilar_iff_source_equal (origins : Nonempty Origins)
    (first second : Source.ValueClass arity) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
      (Source.classEmbedding first) (Source.classEmbedding second) ↔ first = second :=
  (bisimilar_iff_embedded_equal sourceRules origins first (Source.classEmbedding second)).trans
    ⟨fun same => Source.classEmbedding_injective same, fun same => congrArg Source.classEmbedding same⟩

theorem raw_bisimilar_iff_source_equation (origins : Nonempty Origins)
    (first second : Source.Value arity) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
      (classOf (Source.embed first)) (classOf (Source.embed second)) ↔ Equation first second :=
  (bisimilar_iff_source_equal sourceRules origins (classOf first) (classOf second)).trans
    ⟨fun same => Quotient.exact same, fun equation => Quotient.sound equation⟩

theorem source_context_congruence (origins : Nonempty Origins)
    (context : ContextClass (Source.signature arity) (Source.Parallel arity) (ULift.up ()) (ULift.up ()))
    {first second : Source.ValueClass arity}
    (related : (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
      (Source.classEmbedding first) (Source.classEmbedding second)) :
    (firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar .base
      (Source.classEmbedding (context.fill first)) (Source.classEmbedding (context.fill second)) := by
  have same := (bisimilar_iff_source_equal sourceRules origins first second).mp related
  exact (bisimilar_iff_source_equal sourceRules origins (context.fill first) (context.fill second)).mpr
    (congrArg context.fill same)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels
