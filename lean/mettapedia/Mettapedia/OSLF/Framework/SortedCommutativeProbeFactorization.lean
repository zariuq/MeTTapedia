import Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeFactorization

/-!
# Complete identity-or-body factorization for fresh probe assays

Every nonempty redex inventory that starts outside the fresh nullary probe
sorts can reach an assay head only through its body. Stripping actual outer
parallel units leaves the identity or an entire body frame. The result
retains the complete inner context and independent body equation, without
restricting the redex to source syntax or assuming faithful ground action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

theorem result_ne_probe (instrument other : Probe arity) :
    InstrumentCutContexts.result (sourceArity arity) instrument ≠ .probe other := by
  cases instrument <;> intro impossible <;> cases impossible

private theorem raw_nonprobe_context_cannot_end_at_probe {source target : Srt arity}
    (nonprobe : ∀ instrument : Probe arity, source ≠ .probe instrument)
    (context : RawContext (signature arity) (Parallel arity) source target) :
    ∀ instrument : Probe arity, target = .probe instrument → False := by
  apply @RawContext.rec (signature arity) (Parallel arity) source
    (fun target _ => ∀ instrument : Probe arity, target = .probe instrument → False) (t := context)
  · intro instrument impossible
    exact nonprobe instrument impossible
  · intro constructor position _siblings _inner _inductionHypothesis instrument impossible
    cases constructor with
    | original => cases impossible
    | arguments => cases impossible
    | probe => exact Fin.elim0 position
    | cut selected => cases selected <;> cases impossible
  · intro target parallel _inner _sibling _inductionHypothesis _instrument impossible
    change target = .base at parallel
    rw [parallel] at impossible
    cases impossible
  · intro target parallel _sibling _inner _inductionHypothesis _instrument impossible
    change target = .base at parallel
    rw [parallel] at impossible
    cases impossible

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

theorem raw_probe_reaction_identity_or_factor {source : Srt arity}
    (instrument : Probe arity)
    (supplied : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (redex : Value arity source) (nonempty : inventory redex ≠ 0)
    (nonprobe : ∀ other : Probe arity, source ≠ .probe other)
    (reaction : RawContext (signature arity) (Parallel arity) source
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (read : classOf (reaction.fill redex) =
      classOf (cut arity instrument (probe arity instrument) supplied)) :
    (InstrumentCutContexts.result (sourceArity arity) instrument = source ∧
      HEq (contextClassOf reaction)
        (ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) source)) ∨
    ∃ before : ContextClass (signature arity) (Parallel arity) source
        (InstrumentCutContexts.receiver (sourceArity arity) instrument),
      before.fill (classOf redex) = classOf supplied ∧
        contextClassOf reaction = before.comp (contextClassOf (probeContext arity instrument)) := by
  rcases reaction.singleton_inventory_frame_or_identity redex nonempty _
      (congrArg inventoryQ read) with identityRead | frame
  · exact Or.inl identityRead
  · obtain ⟨found, position, siblings, inner, outputRead, contextRead⟩ := frame
    have completeRead := (context_fill_heq _ _ outputRead contextRead (classOf redex)).trans (heq_of_eq read)
    have heads := constructor_count_heq _ _ outputRead completeRead
    have foundRead : found = Constructor.cut instrument := by
      change ({found} : Multiset (Constructor arity)) = {Constructor.cut instrument} at heads
      exact Multiset.singleton_inj.mp heads
    subst found
    have frameRead : contextClassOf (RawContext.frame (signature := signature arity)
        (Parallel := Parallel arity) (Constructor.cut instrument) position siblings inner) =
        contextClassOf reaction := eq_of_heq contextRead
    have filledRead := (congrArg (fun context => context.fill (classOf redex)) frameRead).trans read
    fin_cases position
    · exact (raw_nonprobe_context_cannot_end_at_probe nonprobe inner instrument rfl).elim
    · change RawContext (signature arity) (Parallel arity) source
        (InstrumentCutContexts.receiver (sourceArity arity) instrument) at inner
      change classOf (Term.node (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.cut instrument)
        (RawContext.insert (signature := signature arity) (Parallel := Parallel arity)
          (Constructor.cut instrument) 1 siblings (inner.fill redex))) =
        classOf (Term.node (signature := signature arity) (Parallel := Parallel arity)
          (Constructor.cut instrument) _) at filledRead
      have coordinates := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.cut instrument) _ _).mp filledRead
      refine Or.inr ⟨contextClassOf inner, ?_, frameRead.symm.trans ?_⟩
      · have bodyRead := coordinates (1 : Fin 2)
        change classOf (inner.fill redex) = classOf supplied at bodyRead
        exact bodyRead
      · apply Quotient.sound
        change ContextEquation (signature := signature arity) (Parallel := Parallel arity)
          (RawContext.frame (signature := signature arity) (Parallel := Parallel arity)
            (Constructor.cut instrument) 1 siblings inner)
          (RawContext.comp (signature := signature arity) (Parallel := Parallel arity)
            inner (probeContext arity instrument))
        unfold probeContext RawContext.comp
        apply ContextEquation.frame
        · intro other absent
          fin_cases other
          · change Equation (siblings 0 absent) (probe arity instrument)
            have probeRead := coordinates (0 : Fin 2)
            change classOf (siblings 0 absent) = classOf (probe arity instrument) at probeRead
            exact Quotient.exact probeRead
          · exact (absent rfl).elim
        · exact ContextEquation.refl inner

theorem probe_reaction_identity_or_factor {source : Srt arity}
    (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (redex : Value arity source) (nonempty : inventory redex ≠ 0)
    (nonprobe : ∀ other : Probe arity, source ≠ .probe other)
    (reaction : ContextClass (signature arity) (Parallel arity) source
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (read : reaction.fill (classOf redex) =
      (contextClassOf (probeContext arity instrument)).fill supplied) :
    (InstrumentCutContexts.result (sourceArity arity) instrument = source ∧
      HEq reaction (ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) source)) ∨
    ∃ before : ContextClass (signature arity) (Parallel arity) source
        (InstrumentCutContexts.receiver (sourceArity arity) instrument),
      before.fill (classOf redex) = supplied ∧
        reaction = before.comp (contextClassOf (probeContext arity instrument)) := by
  revert read
  refine Quotient.inductionOn₂ reaction supplied ?_
  intro rawReaction rawSupplied read
  exact raw_probe_reaction_identity_or_factor instrument rawSupplied redex nonempty nonprobe rawReaction
    (read.trans (congrArg classOf (probeContext_fill arity instrument rawSupplied)))

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
