import Mettapedia.OSLF.Framework.SortedCommutativeProbeFactorization
import Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeExclusion

/-!
# Actual administrative probe inversion on arbitrary native values

Every administrative redex has a nonempty free-head inventory and starts
outside the nullary probe sorts. Complete identity-or-body factorization
therefore applies to an inspected probe IPO. The body alternative gives
an actual smaller commuting candidate; minimality rejects it. The remaining
identity retains the exact probe, whole supplied input, complete output and
authored occurrence. No source-purity hypothesis or root-view decoder is used.
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

theorem minimal_probe_reaction_identity {source : Srt arity}
    (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (redex : Value arity source) (nonempty : inventory redex ≠ 0)
    (nonprobe : ∀ other : Probe arity, source ≠ .probe other)
    (reaction : ContextClass (signature arity) (Parallel arity) source
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶
        .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫ probeLabel instrument =
      RawArrow.value (classOf redex) ≫ RawArrow.context reaction)
    (minimal : IsIdemPushout (C := ContextCategory arity) (RawArrow.value supplied)
      (RawArrow.value (classOf redex)) (probeLabel instrument) (RawArrow.context reaction) square) :
    InstrumentCutContexts.result (sourceArity arity) instrument = source ∧
      HEq reaction (ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) source) := by
  have read : reaction.fill (classOf redex) =
      (contextClassOf (probeContext arity instrument)).fill supplied := (RawArrow.value.inj square).symm
  rcases probe_reaction_identity_or_factor instrument supplied redex nonempty nonprobe reaction read
      with identityRead | ⟨before, inputRead, reactionRead⟩
  · exact identityRead
  · let candidate : Candidate (C := ContextCategory arity) (RawArrow.value supplied)
        (RawArrow.value (classOf redex)) (probeLabel instrument) (RawArrow.context reaction) :=
      { apex := .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)
        inl := 𝟙 (.interface (InstrumentCutContexts.receiver (sourceArity arity) instrument) : ContextCategory arity)
        inr := RawArrow.context before
        down := probeLabel instrument
        comm := (Category.comp_id _).trans (congrArg RawArrow.value inputRead).symm
        fac_left := Category.id_comp _
        fac_right := congrArg RawArrow.context reactionRead.symm }
    obtain ⟨section_, recovers⟩ := minimal.down_splits candidate
    have support := congrArg arrowObserverCount recovers
    change arrowObserverCount (section_ ≫ probeLabel instrument) = 0 at support
    rw [arrowCount_comp, probeLabel_support] at support
    omega

private theorem context_fill_heq {source first second : Srt arity}
    (before : ContextClass (signature arity) (Parallel arity) source first)
    (after : ContextClass (signature arity) (Parallel arity) source second)
    (sortRead : first = second) (same : HEq before after) (value : ValueClass arity source) :
    HEq (before.fill value) (after.fill value) := by
  subst second
  exact heq_of_eq (congrArg (fun context => context.fill value) (eq_of_heq same))

private theorem constructor_count_heq {first second : Srt arity}
    (before : ValueClass arity first) (after : ValueClass arity second)
    (sortRead : first = second) (same : HEq before after) :
    constructorInventory before = constructorInventory after := by
  subst second
  exact congrArg constructorInventory (eq_of_heq same)

private theorem probe_fill_constructor (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)) :
    constructorInventory ((contextClassOf (probeContext arity instrument)).fill supplied) =
      {Constructor.cut instrument} :=
  Quotient.inductionOn supplied (fun raw =>
    (congrArg constructorInventory (congrArg classOf (probeContext_fill arity instrument raw))).trans rfl)

theorem minimal_direct_probe_readout (selected instrument : Probe arity)
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) selected))
    (output : Value arity (InstrumentCutContexts.result (sourceArity arity) selected))
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (result : ValueClass arity (InstrumentCutContexts.result (sourceArity arity) instrument))
    (reaction : ContextClass (signature arity) (Parallel arity)
      (InstrumentCutContexts.result (sourceArity arity) selected)
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶
        .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫ probeLabel instrument =
      (directRule arity selected body output).redex ≫ RawArrow.context reaction)
    (minimal : IsIdemPushout (C := ContextCategory arity) (RawArrow.value supplied)
      (directRule arity selected body output).redex (probeLabel instrument) (RawArrow.context reaction) square)
    (outputRead : RawArrow.value result = (directRule arity selected body output).reactum ≫
      RawArrow.context reaction) :
    selected = instrument ∧ HEq (classOf body) supplied ∧ HEq (classOf output) result := by
  let redex := cut arity selected (probe arity selected) body
  have identityRead := minimal_probe_reaction_identity instrument supplied redex
    (Multiset.singleton_ne_zero _) (result_ne_probe selected) reaction square minimal
  have completeRead := context_fill_heq _ _ identityRead.1 identityRead.2 (classOf redex)
  have headRead := constructor_count_heq _ _ identityRead.1 completeRead
  have squareRead := (RawArrow.value.inj square).symm
  have requestedHead := (congrArg constructorInventory squareRead).trans (probe_fill_constructor instrument supplied)
  have sameHead := headRead.symm.trans requestedHead
  have same : selected = instrument :=
    Constructor.cut.inj (Multiset.singleton_inj.mp sameHead)
  subst instrument
  have reactionRead : reaction = ContextClass.identity
      (signature := signature arity) (Parallel := Parallel arity)
      (InstrumentCutContexts.result (sourceArity arity) selected) := eq_of_heq identityRead.2
  have reactionArrowRead : RawArrow.context reaction =
      𝟙 (.interface (InstrumentCutContexts.result (sourceArity arity) selected) : ContextCategory arity) :=
    congrArg RawArrow.context reactionRead
  change (RawArrow.value supplied : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.receiver (sourceArity arity) selected)) ≫ probeLabel selected =
    RawArrow.value (classOf (cut arity selected (probe arity selected) body)) ≫ RawArrow.context reaction at square
  have outputValueRead : result = reaction.fill (classOf output) := RawArrow.value.inj outputRead
  rw [reactionRead, ContextClass.fill_identity] at outputValueRead
  rw [reactionArrowRead, Category.comp_id] at square
  have suppliedRead : (RawArrow.value (classOf body) : (.origin : ContextCategory arity) ⟶
        .interface (InstrumentCutContexts.receiver (sourceArity arity) selected)) ≫ probeLabel selected =
      (directRule arity selected body output).redex :=
    congrArg RawArrow.value (congrArg classOf (probeContext_fill arity selected body))
  have inputRead := RawArrow.value.inj ((cancel_mono (probeLabel selected)).mp (square.trans suppliedRead.symm))
  exact ⟨rfl, heq_of_eq inputRead.symm, heq_of_eq outputValueRead.symm⟩

theorem administrative_probe_step_inversion (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (result : ValueClass arity (InstrumentCutContexts.result (sourceArity arity) instrument))
    (step : ActIPO (rules arity Origins) (probeLabel instrument) (RawArrow.value supplied) (RawArrow.value result)) :
    ∃ occurrence : Occurrence arity Origins,
      occurrence.instrument = instrument ∧ HEq (classOf occurrence.body) supplied ∧
        HEq (classOf occurrence.output) result := by
  obtain ⟨rule, ⟨occurrence, rfl⟩, reaction, square, minimal, outputRead⟩ := step
  cases occurrence with
  | ask origin constructor arguments =>
    cases reaction with
    | context reaction =>
      exact ⟨.ask origin constructor arguments,
        minimal_direct_probe_readout (.ask constructor) instrument (sourceNode arity constructor arguments)
          (bundle arity constructor arguments) supplied result reaction square minimal outputRead⟩
  | get origin constructor arguments position =>
    cases reaction with
    | context reaction =>
      exact ⟨.get origin constructor arguments position,
        minimal_direct_probe_readout (.get constructor position) instrument (bundle arity constructor arguments)
          (arguments position) supplied result reaction square minimal outputRead⟩
  | build origin constructor arguments =>
    cases reaction with
    | context reaction =>
      exact ⟨.build origin constructor arguments,
        minimal_direct_probe_readout (.build constructor) instrument (bundle arity constructor arguments)
          (sourceNode arity constructor arguments) supplied result reaction square minimal outputRead⟩

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
