import Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeFactorization
import Mettapedia.OSLF.Framework.SortedCommutativeOriginalAskExclusion
import Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionReadout

/-!
# Original nonunit rules cannot supply administrative probe IPOs

The independently earned complete reaction factorization constructs a smaller
commuting candidate at the actual probe receiver. IPO minimality would split
the probe label, contradicting its positive hereditary support. Rules at the
source origin have an independent smaller candidate as well.

Admission checks only that an original redex is not the source unit class.
It does not assume reaction exclusion, observer adequacy or faithful ground
action. With this local admission, combined-family get/build retain exactly
the administrative complete target and the explicit origin-inhabitation
condition. Unit rules remain outside the result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Support

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

def probeLabel (instrument : Probe arity) :
    (.interface (InstrumentCutContexts.receiver (sourceArity arity) instrument) : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) instrument) :=
  RawArrow.context (contextClassOf (probeContext arity instrument))

theorem probeLabel_support (instrument : Probe arity) : arrowObserverCount (probeLabel instrument) = 2 :=
  contextObserverCount_probeContext instrument

def Source.NonunitRedex (original : ReactionRule (.origin : Source.SourceCategory (arity := arity))) : Prop :=
  ¬HEq original.redex (RawArrow.value (classOf (.zero rfl : Source.Value arity)) :
    (.origin : Source.SourceCategory (arity := arity)) ⟶ .interface (ULift.up ()))

theorem nonunit_base_probe_square_not_ipo (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (redex : Source.ValueClass arity) (nonunit : redex ≠ classOf (.zero rfl : Source.Value arity))
    (reaction : ContextClass (signature arity) (Parallel arity) .base
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶
        .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫ probeLabel instrument =
      RawArrow.value (Source.classEmbedding redex) ≫ RawArrow.context reaction) :
    ¬ IsIdemPushout (C := ContextCategory arity) (RawArrow.value supplied)
      (RawArrow.value (Source.classEmbedding redex)) (probeLabel instrument)
      (RawArrow.context reaction) square := by
  have read : reaction.fill (Source.classEmbedding redex) =
      (contextClassOf (probeContext arity instrument)).fill supplied :=
    (RawArrow.value.inj square).symm
  obtain ⟨before, inputRead, reactionRead⟩ :=
    nonunit_probe_reaction_factorization instrument supplied redex nonunit reaction read
  let candidate : Candidate (C := ContextCategory arity) (RawArrow.value supplied)
      (RawArrow.value (Source.classEmbedding redex)) (probeLabel instrument) (RawArrow.context reaction) :=
    { apex := .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      inl := 𝟙 (.interface (InstrumentCutContexts.receiver (sourceArity arity) instrument) : ContextCategory arity)
      inr := RawArrow.context before
      down := probeLabel instrument
      comm := (Category.comp_id _).trans (congrArg RawArrow.value inputRead).symm
      fac_left := Category.id_comp _
      fac_right := congrArg RawArrow.context reactionRead.symm }
  intro minimal
  obtain ⟨section_, recovers⟩ := minimal.down_splits candidate
  have support := congrArg arrowObserverCount recovers
  change arrowObserverCount (section_ ≫ probeLabel instrument) = 0 at support
  rw [arrowCount_comp, probeLabel_support] at support
  omega

theorem origin_probe_square_not_ipo (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (reaction : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶
        .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫ probeLabel instrument =
      𝟙 (.origin : ContextCategory arity) ≫ reaction) :
    ¬ IsIdemPushout (C := ContextCategory arity) (RawArrow.value supplied)
      (𝟙 (.origin : ContextCategory arity)) (probeLabel instrument) reaction square := by
  let candidate : Candidate (C := ContextCategory arity) (RawArrow.value supplied)
      (𝟙 (.origin : ContextCategory arity)) (probeLabel instrument) reaction :=
    { apex := .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      inl := 𝟙 (.interface (InstrumentCutContexts.receiver (sourceArity arity) instrument) : ContextCategory arity)
      inr := RawArrow.value supplied
      down := probeLabel instrument
      comm := by simp only [Category.comp_id, Category.id_comp]
      fac_left := Category.id_comp _
      fac_right := square.trans (Category.id_comp reaction) }
  intro minimal
  obtain ⟨section_, recovers⟩ := minimal.down_splits candidate
  have support := congrArg arrowObserverCount recovers
  change arrowObserverCount (section_ ≫ probeLabel instrument) = 0 at support
  rw [arrowCount_comp, probeLabel_support] at support
  omega

theorem mapped_nonunit_original_probe_not_ipo (instrument : Probe arity)
    (original : ReactionRule (.origin : Source.SourceCategory (arity := arity)))
    (nonunit : Source.NonunitRedex original)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (reaction : (Source.mapReactionRule original).codomain ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶
        .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫ probeLabel instrument =
      (Source.mapReactionRule original).redex ≫ reaction) :
    ¬ IsIdemPushout (C := ContextCategory arity) (RawArrow.value supplied)
      (Source.mapReactionRule original).redex (probeLabel instrument) reaction square := by
  cases original with
  | mk codomain redex reactum =>
    cases codomain with
    | origin =>
      cases redex with
      | identity => exact origin_probe_square_not_ipo instrument supplied reaction square
    | interface sort =>
      cases sort with
      | up sort =>
        cases sort
        cases redex with
        | value redex =>
          have redexNonunit : redex ≠ classOf (.zero rfl : Source.Value arity) := by
            intro same
            exact nonunit (heq_of_eq (congrArg RawArrow.value same))
          cases reaction with
          | context reaction =>
            exact nonunit_base_probe_square_not_ipo instrument supplied redex redexNonunit reaction square

theorem nonunit_source_rules_do_not_fire_under_probe
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (nonunit : ∀ original, sourceRules original → Source.NonunitRedex original)
    (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (result : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) instrument)) :
    ¬ ActIPO (Source.mappedRules sourceRules) (probeLabel instrument) (RawArrow.value supplied) result := by
  rintro ⟨rule, ⟨original, admitted, rfl⟩, reaction, square, minimal, _output⟩
  exact mapped_nonunit_original_probe_not_ipo instrument original (nonunit original admitted)
    supplied reaction square minimal

theorem combined_nonunit_probe_step_iff_administrative
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (nonunit : ∀ original, sourceRules original → Source.NonunitRedex original)
    (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (result : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) instrument)) :
    ActIPO (fun rule => rules arity Origins rule ∨ Source.mappedRules sourceRules rule)
        (probeLabel instrument) (RawArrow.value supplied) result ↔
      ActIPO (rules arity Origins) (probeLabel instrument) (RawArrow.value supplied) result := by
  constructor
  · rintro ⟨rule, admitted, reaction, square, minimal, output⟩
    rcases admitted with administrative | original
    · exact ⟨rule, administrative, reaction, square, minimal, output⟩
    · exact (nonunit_source_rules_do_not_fire_under_probe sourceRules nonunit instrument supplied result
        ⟨rule, original, reaction, square, minimal, output⟩).elim
  · rintro ⟨rule, admitted, reaction, square, minimal, output⟩
    exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩

theorem combined_nonunit_get_source_step_iff
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (nonunit : ∀ original, sourceRules original → Source.NonunitRedex original)
    (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (position : Fin (sourceArity arity constructor))
    (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ActIPO (fun rule => rules arity Origins rule ∨ Source.mappedRules sourceRules rule)
        (getLabel constructor position) (RawArrow.value (sourceBundle constructor arguments)) result ↔
      Nonempty Origins ∧ result = RawArrow.value (Source.classEmbedding (classOf (arguments position))) :=
  (combined_nonunit_probe_step_iff_administrative (Origins := Origins) sourceRules nonunit
    (.get constructor position) _ result).trans (get_source_step_iff constructor arguments position result)

theorem combined_nonunit_build_source_step_iff
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)
    (nonunit : ∀ original, sourceRules original → Source.NonunitRedex original)
    (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ActIPO (fun rule => rules arity Origins rule ∨ Source.mappedRules sourceRules rule)
        (buildLabel constructor) (RawArrow.value (sourceBundle constructor arguments)) result ↔
      Nonempty Origins ∧ result =
        RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode constructor arguments))) :=
  (combined_nonunit_probe_step_iff_administrative (Origins := Origins) sourceRules nonunit
    (.build constructor) _ result).trans (build_source_step_iff constructor arguments result)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
