import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeFactorization

/-!
# Full administrative probe IPO inversion at every native typed value

Whole-body factorization supplies an actual smaller commuting candidate.
The IPO splitting property rejects that candidate using complete probe
support. The remaining identity recovers the selected instrument, whole
input and output, and a retained authored occurrence. No source-purity or
source-sort inhabitance hypothesis is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}

theorem minimal_probe_reaction_identity {first : Srt source Parallel}
    (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (redex : Value (source := source) (Parallel := Parallel) first)
    (nonempty : inventory redex ≠ 0)
    (nonprobe : ∀ other : Probe source Parallel, first ≠ .probe other)
    (reaction : ContextClass (signature source Parallel) NativeParallel first (result instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory source Parallel) ⟶
        .interface (receiver instrument)) ≫ probeLabel instrument =
      RawArrow.value (classOf redex) ≫ RawArrow.context reaction)
    (minimal : IsIdemPushout (C := ContextCategory source Parallel) (RawArrow.value supplied)
      (RawArrow.value (classOf redex)) (probeLabel instrument) (RawArrow.context reaction) square) :
    result instrument = first ∧ HEq reaction
      (ContextClass.identity (signature := signature source Parallel) (Parallel := NativeParallel) first) := by
  have read : reaction.fill (classOf redex) =
      (contextClassOf (probeContext instrument)).fill supplied := (RawArrow.value.inj square).symm
  rcases probe_reaction_identity_or_factor instrument supplied redex nonempty nonprobe reaction read
      with identityRead | ⟨before, inputRead, reactionRead⟩
  · exact identityRead
  · let candidate : Candidate (C := ContextCategory source Parallel) (RawArrow.value supplied)
        (RawArrow.value (classOf redex)) (probeLabel instrument) (RawArrow.context reaction) :=
      { apex := .interface (receiver instrument)
        inl := 𝟙 (.interface (receiver instrument) : ContextCategory source Parallel)
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

private theorem context_fill_heq {first beforeSort afterSort : Srt source Parallel}
    (before : ContextClass (signature source Parallel) NativeParallel first beforeSort)
    (after : ContextClass (signature source Parallel) NativeParallel first afterSort)
    (sortRead : beforeSort = afterSort) (same : HEq before after)
    (value : ValueClass (source := source) (Parallel := Parallel) first) :
    HEq (before.fill value) (after.fill value) := by
  subst afterSort
  exact heq_of_eq (congrArg (fun context => context.fill value) (eq_of_heq same))

private theorem constructor_count_heq {first second : Srt source Parallel}
    (before : ValueClass (source := source) (Parallel := Parallel) first)
    (after : ValueClass (source := source) (Parallel := Parallel) second)
    (sortRead : first = second) (same : HEq before after) :
    constructorInventory before = constructorInventory after := by
  subst second
  exact congrArg constructorInventory (eq_of_heq same)

private theorem probe_fill_constructor (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)) :
    constructorInventory ((contextClassOf (probeContext instrument)).fill supplied) =
      {Constructor.cut instrument} :=
  Quotient.inductionOn supplied (fun raw =>
    (congrArg constructorInventory (congrArg classOf (probeContext_fill instrument raw))).trans rfl)

def directRule (instrument : Probe source Parallel)
    (body : Value (source := source) (Parallel := Parallel) (receiver instrument))
    (output : Value (source := source) (Parallel := Parallel) (result instrument)) :
    ReactionRule (.origin : ContextCategory source Parallel) where
  codomain := .interface (result instrument)
  redex := RawArrow.value (classOf (cut instrument (probe instrument) body))
  reactum := RawArrow.value (classOf output)

theorem minimal_direct_probe_readout (selected instrument : Probe source Parallel)
    (body : Value (source := source) (Parallel := Parallel) (receiver selected))
    (output : Value (source := source) (Parallel := Parallel) (result selected))
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (observed : ValueClass (source := source) (Parallel := Parallel) (result instrument))
    (reaction : ContextClass (signature source Parallel) NativeParallel
      (result selected) (result instrument))
    (square : (RawArrow.value supplied : (.origin : ContextCategory source Parallel) ⟶
        .interface (receiver instrument)) ≫ probeLabel instrument =
      (directRule selected body output).redex ≫ RawArrow.context reaction)
    (minimal : IsIdemPushout (C := ContextCategory source Parallel) (RawArrow.value supplied)
      (directRule selected body output).redex (probeLabel instrument) (RawArrow.context reaction) square)
    (outputRead : RawArrow.value observed = (directRule selected body output).reactum ≫
      RawArrow.context reaction) :
    selected = instrument ∧ HEq (classOf body) supplied ∧ HEq (classOf output) observed := by
  let redex := cut selected (probe selected) body
  have identityRead := minimal_probe_reaction_identity instrument supplied redex
    (Multiset.singleton_ne_zero _) (result_ne_probe selected) reaction square minimal
  have completeRead := context_fill_heq _ _ identityRead.1 identityRead.2 (classOf redex)
  have headRead := constructor_count_heq _ _ identityRead.1 completeRead
  have squareRead := (RawArrow.value.inj square).symm
  have requestedHead := (congrArg constructorInventory squareRead).trans (probe_fill_constructor instrument supplied)
  have sameHead := headRead.symm.trans requestedHead
  have same : selected = instrument := Constructor.cut.inj (Multiset.singleton_inj.mp sameHead)
  subst instrument
  have reactionRead : reaction = ContextClass.identity
      (signature := signature source Parallel) (Parallel := NativeParallel) (result selected) :=
    eq_of_heq identityRead.2
  have reactionArrowRead : RawArrow.context reaction =
      𝟙 (.interface (result selected) : ContextCategory source Parallel) :=
    congrArg RawArrow.context reactionRead
  change (RawArrow.value supplied : (.origin : ContextCategory source Parallel) ⟶
      .interface (receiver selected)) ≫ probeLabel selected =
    RawArrow.value (classOf (cut selected (probe selected) body)) ≫ RawArrow.context reaction at square
  have outputValueRead : observed = reaction.fill (classOf output) := RawArrow.value.inj outputRead
  rw [reactionRead, ContextClass.fill_identity] at outputValueRead
  rw [reactionArrowRead, Category.comp_id] at square
  have suppliedRead : (RawArrow.value (classOf body) : (.origin : ContextCategory source Parallel) ⟶
        .interface (receiver selected)) ≫ probeLabel selected = (directRule selected body output).redex :=
    congrArg RawArrow.value (congrArg classOf (probeContext_fill selected body))
  have inputRead := RawArrow.value.inj ((cancel_mono (probeLabel selected)).mp (square.trans suppliedRead.symm))
  exact ⟨rfl, heq_of_eq inputRead.symm, heq_of_eq outputValueRead.symm⟩

theorem administrative_probe_step_inversion (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (observed : ValueClass (source := source) (Parallel := Parallel) (result instrument))
    (step : ActIPO (rules source Parallel Origins) (probeLabel instrument)
      (RawArrow.value supplied) (RawArrow.value observed)) :
    ∃ occurrence : Occurrence source Parallel Origins,
      occurrence.instrument = instrument ∧ HEq (classOf occurrence.body) supplied ∧
        HEq (classOf occurrence.output) observed := by
  obtain ⟨rule, ⟨occurrence, rfl⟩, reaction, square, minimal, outputRead⟩ := step
  cases occurrence with
  | ask origin head arguments =>
    cases reaction with
    | context reaction =>
      exact ⟨.ask origin head arguments,
        minimal_direct_probe_readout (.ask head) instrument (sourceNode head arguments)
          (bundle head arguments) supplied observed reaction square minimal outputRead⟩
  | get origin head arguments position =>
    cases reaction with
    | context reaction =>
      exact ⟨.get origin head arguments position,
        minimal_direct_probe_readout (.get head position) instrument (bundle head arguments)
          (arguments position) supplied observed reaction square minimal outputRead⟩
  | build origin head arguments =>
    cases reaction with
    | context reaction =>
      exact ⟨.build origin head arguments,
        minimal_direct_probe_readout (.build head) instrument (bundle head arguments)
          (sourceNode head arguments) supplied observed reaction square minimal outputRead⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments
