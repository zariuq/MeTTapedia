import Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionInversion
import Mettapedia.OSLF.Framework.SortedCommutativeProbeConstructorReadout

/-!
# Full-family get/build inversion and complete source reconstruction

The actual labels act on complete independently supplied source bundles.
Whole-family inversion excludes every competing administrative declaration,
then reads the fresh instrument head and cancels its actual probe context.
Every tuple coordinate and the reconstructed source constructor class are
preserved. The equivalences require inhabited origins explicitly; arbitrary
source AC1 decompositions remain available when an ask produces the bundle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Support
open scoped BigOperators

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

def getLabel (constructor : SourceSymbol Symbols) (position : Fin (sourceArity arity constructor)) :
    (.interface (.arguments constructor) : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.context (contextClassOf (probeContext arity (.get constructor position)))

def buildLabel (constructor : SourceSymbol Symbols) :
    (.interface (.arguments constructor) : ContextCategory arity) ⟶ .interface .base :=
  RawArrow.context (contextClassOf (probeContext arity (.build constructor)))

def sourceBundle (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity) : ValueClass arity (.arguments constructor) :=
  classOf (bundle arity constructor (fun position => Source.embed (arguments position)))

theorem Source.sourceNode_class_congruence (constructor : SourceSymbol Symbols)
    (first second : Fin (sourceArity arity constructor) → Source.Value arity)
    (coordinates : ∀ position, classOf (first position) = classOf (second position)) :
    classOf (Source.sourceNode constructor first) = classOf (Source.sourceNode constructor second) := by
  cases constructor with
  | ordinary symbol =>
    exact (node_class_eq_iff (signature := Source.signature arity) (Parallel := Source.Parallel arity)
      symbol first second).mpr coordinates
  | properCut =>
    exact Quotient.sound (Equation.cut rfl (Quotient.exact (coordinates 0)) (Quotient.exact (coordinates 1)))
  | unit => rfl

private theorem probe_body_class_readout (instrument : Probe arity)
    (first second : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (same : classOf (cut arity instrument (probe arity instrument) first) =
      classOf (cut arity instrument (probe arity instrument) second)) :
    classOf first = classOf second := by
  let label : (.interface (InstrumentCutContexts.receiver (sourceArity arity) instrument) : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) instrument) :=
    RawArrow.context (contextClassOf (probeContext arity instrument))
  have firstSquare : (RawArrow.value (classOf first) : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫ label =
        RawArrow.value (classOf (cut arity instrument (probe arity instrument) first)) :=
    congrArg RawArrow.value (congrArg classOf (probeContext_fill arity instrument first))
  have secondSquare : (RawArrow.value (classOf second) : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫ label =
        RawArrow.value (classOf (cut arity instrument (probe arity instrument) second)) :=
    congrArg RawArrow.value (congrArg classOf (probeContext_fill arity instrument second))
  exact RawArrow.value.inj ((cancel_mono label).mp
    (firstSquare.trans ((congrArg RawArrow.value same).trans secondSquare.symm)))

private theorem source_bundle_coordinates (constructor : SourceSymbol Symbols)
    (first second : Fin (sourceArity arity constructor) → Source.Value arity)
    (same : sourceBundle constructor first = sourceBundle constructor second) :
    ∀ position, classOf (first position) = classOf (second position) := by
  have coordinates := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
    (Constructor.arguments constructor)
    (fun position => Source.embed (first position)) (fun position => Source.embed (second position))).mp same
  exact fun position => Source.classEmbedding_injective (coordinates position)

private theorem get_assay_support (constructor : SourceSymbol Symbols)
    (position : Fin (sourceArity arity constructor))
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity) :
    classObserverCount ((contextClassOf (probeContext arity (.get constructor position))).fill
      (sourceBundle constructor arguments)) = 3 := by
  exact (congrArg observerCount (probeContext_fill arity (.get constructor position)
    (bundle arity constructor (fun other => Source.embed (arguments other))))).trans
      ((observerCount_probeCut (.get constructor position) _).trans (by
        rw [observerCount_bundle]
        simp only [observerCount_embed, Finset.sum_const_zero]
        rfl))

private theorem build_assay_support (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity) :
    classObserverCount ((contextClassOf (probeContext arity (.build constructor))).fill
      (sourceBundle constructor arguments)) = 3 := by
  exact (congrArg observerCount (probeContext_fill arity (.build constructor)
    (bundle arity constructor (fun other => Source.embed (arguments other))))).trans
      ((observerCount_probeCut (.build constructor) _).trans (by
        rw [observerCount_bundle]
        simp only [observerCount_embed, Finset.sum_const_zero]
        rfl))

theorem get_source_step_iff (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor))
    (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ActIPO (rules arity Origins) (getLabel constructor position)
      (RawArrow.value (sourceBundle constructor arguments)) result ↔
        Nonempty Origins ∧ result = RawArrow.value (Source.classEmbedding (classOf (arguments position))) := by
  constructor
  · intro step
    have erased : Source.classRetraction
        ((contextClassOf (probeContext arity (.get constructor position))).fill
          (sourceBundle constructor arguments)) = classOf (.zero rfl : Source.Value arity) := by
      exact (congrArg (fun value => Source.classRetraction (classOf value))
        (probeContext_fill arity (.get constructor position)
          (bundle arity constructor (fun other => Source.embed (arguments other))))).trans
            (erasure_probeCut (.get constructor position) _)
    obtain ⟨origin, found, before, matched⟩ := three_head_assay_inversion
      (sourceBundle constructor arguments) (contextClassOf (probeContext arity (.get constructor position)))
      result (get_assay_support constructor position arguments) erased step
    have fillRead := congrArg classOf (probeContext_fill arity (.get constructor position)
      (bundle arity constructor (fun other => Source.embed (arguments other))))
    rcases matched with ⟨selected, inputRead, outputRead⟩ | ⟨inputRead, _outputRead⟩
    · have redexRead := fillRead.symm.trans inputRead
      have instrumentRead := get_get_head_readout constructor found position selected
        (bundle arity constructor (fun other => Source.embed (arguments other)))
        (bundle arity found (fun other => Source.embed (before other))) redexRead
      obtain ⟨same, selectedRead⟩ := InstrumentCutContexts.Probe.get.inj instrumentRead
      subst found
      have selectedSame : position = selected := eq_of_heq selectedRead
      subst selected
      have bundleRead := probe_body_class_readout (.get constructor position)
        (bundle arity constructor (fun other => Source.embed (arguments other)))
        (bundle arity constructor (fun other => Source.embed (before other))) redexRead
      have coordinates := source_bundle_coordinates constructor arguments before bundleRead
      exact ⟨⟨origin⟩, outputRead.trans
        (congrArg (fun value => (RawArrow.value (Source.classEmbedding value) :
          (.origin : ContextCategory arity) ⟶ .interface .base)) (coordinates position)).symm⟩
    · exact (get_build_head_separate constructor found position
        (bundle arity constructor (fun other => Source.embed (arguments other)))
        (bundle arity found (fun other => Source.embed (before other))) (fillRead.symm.trans inputRead)).elim
  · rintro ⟨⟨origin⟩, outputRead⟩
    rw [outputRead]
    exact (Occurrence.get origin constructor (fun other => Source.embed (arguments other)) position).direct_step

theorem build_source_step_iff (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ActIPO (rules arity Origins) (buildLabel constructor)
      (RawArrow.value (sourceBundle constructor arguments)) result ↔
        Nonempty Origins ∧ result = RawArrow.value
          (Source.classEmbedding (classOf (Source.sourceNode constructor arguments))) := by
  constructor
  · intro step
    have erased : Source.classRetraction
        ((contextClassOf (probeContext arity (.build constructor))).fill
          (sourceBundle constructor arguments)) = classOf (.zero rfl : Source.Value arity) := by
      exact (congrArg (fun value => Source.classRetraction (classOf value))
        (probeContext_fill arity (.build constructor)
          (bundle arity constructor (fun other => Source.embed (arguments other))))).trans
            (erasure_probeCut (.build constructor) _)
    obtain ⟨origin, found, before, matched⟩ := three_head_assay_inversion
      (sourceBundle constructor arguments) (contextClassOf (probeContext arity (.build constructor)))
      result (build_assay_support constructor arguments) erased step
    have fillRead := congrArg classOf (probeContext_fill arity (.build constructor)
      (bundle arity constructor (fun other => Source.embed (arguments other))))
    rcases matched with ⟨selected, inputRead, _outputRead⟩ | ⟨inputRead, outputRead⟩
    · exact (get_build_head_separate found constructor selected
        (bundle arity found (fun other => Source.embed (before other)))
        (bundle arity constructor (fun other => Source.embed (arguments other)))
          (fillRead.symm.trans inputRead).symm).elim
    · have redexRead := fillRead.symm.trans inputRead
      have foundSame := build_build_head_readout constructor found
        (bundle arity constructor (fun other => Source.embed (arguments other)))
        (bundle arity found (fun other => Source.embed (before other))) redexRead
      subst found
      have bundleRead := probe_body_class_readout (.build constructor)
        (bundle arity constructor (fun other => Source.embed (arguments other)))
        (bundle arity constructor (fun other => Source.embed (before other))) redexRead
      have coordinates := source_bundle_coordinates constructor arguments before bundleRead
      exact ⟨⟨origin⟩, outputRead.trans
        (congrArg (fun value => (RawArrow.value (Source.classEmbedding value) :
          (.origin : ContextCategory arity) ⟶ .interface .base))
          (Source.sourceNode_class_congruence constructor arguments before coordinates)).symm⟩
  · rintro ⟨⟨origin⟩, outputRead⟩
    have sourceRead := congrArg (fun value => (RawArrow.value (classOf value) :
      (.origin : ContextCategory arity) ⟶ .interface .base)) (Source.sourceNode_embed constructor arguments)
    rw [outputRead]
    apply Eq.mpr (congrArg (fun (target : (.origin : ContextCategory arity) ⟶ .interface .base) =>
      ActIPO (rules arity Origins) (buildLabel constructor)
        (RawArrow.value (sourceBundle constructor arguments)) target) sourceRead)
    exact (Occurrence.build origin constructor (fun other => Source.embed (arguments other))).direct_step

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
