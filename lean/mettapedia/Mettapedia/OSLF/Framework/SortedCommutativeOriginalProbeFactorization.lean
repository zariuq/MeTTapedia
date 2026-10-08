import Mettapedia.OSLF.Framework.SortedCommutativeOriginalAskFactorization
import Mettapedia.OSLF.Syntax.SortedCommutativeSingletonContexts

/-!
# Nonunit original redexes inside complete probe assays

A nonunit source redex has a nonempty inventory. When an actual reaction
produces one complete assay head, every outer parallel sibling is the unit
class. The remaining constructor frame must be the supplied probe Cut. Its
fresh nullary probe cannot contain the source hole, so the whole reaction
factors through the assay label, retaining its entire body and inner context.

The nonunit premise is essential: a source unit can be inserted beside an
entire assay, as the independently proved unit-rule competition demonstrates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open Mettapedia.OSLF.SortedCommutative
open Support

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

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

private theorem observer_count_heq {first second : Srt arity}
    (before : ValueClass arity first) (after : ValueClass arity second)
    (sortRead : first = second) (same : HEq before after) :
    classObserverCount before = classObserverCount after := by
  subst second
  exact congrArg classObserverCount (eq_of_heq same)

theorem source_nonunit_inventory (redex : Source.Value arity)
    (nonunit : classOf redex ≠ classOf (.zero rfl : Source.Value arity)) :
    inventory (Source.embed redex) ≠ 0 := by
  intro empty
  have same : classOf (Source.embed redex) = classOf (.zero rfl : Value arity .base) :=
    inventoryQ_injective empty
  exact nonunit (Source.classEmbedding_injective same)

theorem raw_nonunit_probe_reaction_factorization (instrument : Probe arity)
    (supplied : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (redex : Source.Value arity)
    (nonunit : classOf redex ≠ classOf (.zero rfl : Source.Value arity))
    (reaction : RawContext (signature arity) (Parallel arity) .base
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (read : classOf (reaction.fill (Source.embed redex)) =
      classOf (cut arity instrument (probe arity instrument) supplied)) :
    ∃ before : ContextClass (signature arity) (Parallel arity) .base
        (InstrumentCutContexts.receiver (sourceArity arity) instrument),
      before.fill (classOf (Source.embed redex)) = classOf supplied ∧
        contextClassOf reaction = before.comp (contextClassOf (probeContext arity instrument)) := by
  have headRead := congrArg inventoryQ read
  rcases reaction.singleton_inventory_frame_or_identity (Source.embed redex)
      (source_nonunit_inventory redex nonunit) _ headRead with identityRead | frame
  · obtain ⟨sameSort, sameContext⟩ := identityRead
    have sameValue := context_fill_heq _ _ sameSort sameContext (classOf (Source.embed redex))
    have pure : classObserverCount (classOf (reaction.fill (Source.embed redex))) = 0 :=
      (observer_count_heq _ _ sameSort sameValue).trans (observerCount_embed redex)
    have counts := congrArg classObserverCount read
    change observerCount (reaction.fill (Source.embed redex)) =
      observerCount (cut arity instrument (probe arity instrument) supplied) at counts
    rw [observerCount_probeCut] at counts
    change observerCount (reaction.fill (Source.embed redex)) = 0 at pure
    omega
  · obtain ⟨found, position, siblings, inner, outputRead, contextRead⟩ := frame
    have completeRead := (context_fill_heq _ _ outputRead contextRead
      (classOf (Source.embed redex))).trans (heq_of_eq read)
    have heads := constructor_count_heq _ _ outputRead completeRead
    have foundRead : found = Constructor.cut instrument := by
      change ({found} : Multiset (Constructor arity)) = {Constructor.cut instrument} at heads
      exact Multiset.singleton_inj.mp heads
    subst found
    have frameRead : contextClassOf (RawContext.frame (signature := signature arity)
        (Parallel := Parallel arity) (Constructor.cut instrument) position siblings inner) =
        contextClassOf reaction := eq_of_heq contextRead
    have filledRead := (congrArg (fun context => context.fill (classOf (Source.embed redex)))
      frameRead).trans read
    fin_cases position
    · exact (base_context_cannot_end_at_probe instrument inner).elim
    · change RawContext (signature arity) (Parallel arity) .base
        (InstrumentCutContexts.receiver (sourceArity arity) instrument) at inner
      change classOf (Term.node (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.cut instrument)
        (RawContext.insert (signature := signature arity) (Parallel := Parallel arity)
          (Constructor.cut instrument) 1 siblings (inner.fill (Source.embed redex)))) =
        classOf (Term.node (signature := signature arity) (Parallel := Parallel arity)
          (Constructor.cut instrument) _) at filledRead
      have coordinates := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.cut instrument) _ _).mp filledRead
      refine ⟨contextClassOf inner, ?_, frameRead.symm.trans ?_⟩
      · have bodyRead := coordinates (1 : Fin 2)
        change classOf (inner.fill (Source.embed redex)) = classOf supplied at bodyRead
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

theorem nonunit_probe_reaction_factorization (instrument : Probe arity)
    (supplied : ValueClass arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (redex : Source.ValueClass arity)
    (nonunit : redex ≠ classOf (.zero rfl : Source.Value arity))
    (reaction : ContextClass (signature arity) (Parallel arity) .base
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (read : reaction.fill (Source.classEmbedding redex) =
      (contextClassOf (probeContext arity instrument)).fill supplied) :
    ∃ before : ContextClass (signature arity) (Parallel arity) .base
        (InstrumentCutContexts.receiver (sourceArity arity) instrument),
      before.fill (Source.classEmbedding redex) = supplied ∧
        reaction = before.comp (contextClassOf (probeContext arity instrument)) := by
  revert nonunit read
  refine Quotient.inductionOn₃ reaction supplied redex ?_
  intro rawReaction rawSupplied rawRedex nonunit read
  change classOf (rawReaction.fill (Source.embed rawRedex)) =
    classOf ((probeContext arity instrument).fill rawSupplied) at read
  exact raw_nonunit_probe_reaction_factorization instrument rawSupplied rawRedex nonunit rawReaction
    (read.trans (congrArg classOf (probeContext_fill arity instrument rawSupplied)))

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
