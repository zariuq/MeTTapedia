import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeSupport
import Mettapedia.OSLF.Syntax.SortedCommutativeSingletonContexts
import Mettapedia.OSLF.Syntax.SortedCommutativeConstructorReadout

/-!
# Whole-body factorization of heterogeneous fresh probe contexts

The free-head inventory independently records the actual administrative
constructor. A nonempty redex starting outside all fresh probe sorts can
reach a probe assay only by the identity or its complete body frame. Actual
AC1 units are stripped by generated context equations; the factorization
retains the whole inner context, every sibling and the typed body equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open Mettapedia.OSLF.SortedCommutative

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

private def headConstructor {sort : Srt source Parallel}
    (head : Head (signature := signature source Parallel) (Parallel := NativeParallel) sort) :
    Constructor source Parallel :=
  match head with
  | .node constructor _arguments => constructor

def constructorInventory {sort : Srt source Parallel}
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort) :
    Multiset (Constructor source Parallel) :=
  (inventoryQ supplied).map headConstructor

theorem constructorInventory_probeCut (instrument : Probe source Parallel)
    (body : Value (source := source) (Parallel := Parallel) (receiver instrument)) :
    constructorInventory (classOf (cut instrument (probe instrument) body)) =
      {Constructor.cut instrument} := rfl

theorem result_ne_probe (instrument other : Probe source Parallel) :
    result instrument ≠ .probe other := by
  cases instrument <;> intro impossible <;> cases impossible

private theorem raw_nonprobe_context_cannot_end_at_probe {first second : Srt source Parallel}
    (nonprobe : ∀ instrument : Probe source Parallel, first ≠ .probe instrument)
    (context : RawContext (signature source Parallel) NativeParallel first second) :
    ∀ instrument : Probe source Parallel, second = .probe instrument → False := by
  apply @RawContext.rec (signature source Parallel) NativeParallel first
    (fun second _ => ∀ instrument : Probe source Parallel, second = .probe instrument → False)
    (t := context)
  · intro instrument impossible
    exact nonprobe instrument impossible
  · intro constructor position _siblings _inner _inductionHypothesis instrument impossible
    cases constructor with
    | original => cases impossible
    | arguments => cases impossible
    | probe => exact Fin.elim0 position
    | cut selected => cases selected <;> cases impossible
  · intro second parallel _inner _sibling _inductionHypothesis _instrument impossible
    cases second with
    | original => cases impossible
    | arguments => exact parallel.elim
    | probe => exact parallel.elim
  · intro second parallel _sibling _inner _inductionHypothesis _instrument impossible
    cases second with
    | original => cases impossible
    | arguments => exact parallel.elim
    | probe => exact parallel.elim

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

theorem raw_probe_reaction_identity_or_factor {first : Srt source Parallel}
    (instrument : Probe source Parallel)
    (supplied : Value (source := source) (Parallel := Parallel) (receiver instrument))
    (redex : Value (source := source) (Parallel := Parallel) first)
    (nonempty : inventory redex ≠ 0)
    (nonprobe : ∀ other : Probe source Parallel, first ≠ .probe other)
    (reaction : RawContext (signature source Parallel) NativeParallel first (result instrument))
    (read : classOf (reaction.fill redex) = classOf (cut instrument (probe instrument) supplied)) :
    (result instrument = first ∧ HEq (contextClassOf reaction)
      (ContextClass.identity (signature := signature source Parallel) (Parallel := NativeParallel) first)) ∨
    ∃ before : ContextClass (signature source Parallel) NativeParallel first (receiver instrument),
      before.fill (classOf redex) = classOf supplied ∧
        contextClassOf reaction = before.comp (contextClassOf (probeContext instrument)) := by
  rcases reaction.singleton_inventory_frame_or_identity redex nonempty _
      (congrArg inventoryQ read) with identityRead | frame
  · exact Or.inl identityRead
  · obtain ⟨found, position, siblings, inner, outputRead, contextRead⟩ := frame
    have completeRead := (context_fill_heq _ _ outputRead contextRead (classOf redex)).trans (heq_of_eq read)
    have heads := constructor_count_heq _ _ outputRead completeRead
    have foundRead : found = Constructor.cut instrument := by
      change ({found} : Multiset (Constructor source Parallel)) = {Constructor.cut instrument} at heads
      exact Multiset.singleton_inj.mp heads
    subst found
    have frameRead : contextClassOf (RawContext.frame (signature := signature source Parallel)
        (Parallel := NativeParallel) (Constructor.cut instrument) position siblings inner) =
        contextClassOf reaction := eq_of_heq contextRead
    have filledRead := (congrArg (fun context => context.fill (classOf redex)) frameRead).trans read
    fin_cases position
    · exact (raw_nonprobe_context_cannot_end_at_probe nonprobe inner instrument rfl).elim
    · change RawContext (signature source Parallel) NativeParallel first (receiver instrument) at inner
      change classOf (Term.node (signature := signature source Parallel) (Parallel := NativeParallel)
        (Constructor.cut instrument)
        (RawContext.insert (signature := signature source Parallel) (Parallel := NativeParallel)
          (Constructor.cut instrument) 1 siblings (inner.fill redex))) =
        classOf (Term.node (signature := signature source Parallel) (Parallel := NativeParallel)
          (Constructor.cut instrument) _) at filledRead
      have coordinates := (node_class_eq_iff (signature := signature source Parallel) (Parallel := NativeParallel)
        (Constructor.cut instrument) _ _).mp filledRead
      refine Or.inr ⟨contextClassOf inner, ?_, frameRead.symm.trans ?_⟩
      · have bodyRead := coordinates (1 : Fin 2)
        change classOf (inner.fill redex) = classOf supplied at bodyRead
        exact bodyRead
      · apply Quotient.sound
        change ContextEquation (signature := signature source Parallel) (Parallel := NativeParallel)
          (RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
            (Constructor.cut instrument) 1 siblings inner)
          (RawContext.comp (signature := signature source Parallel) (Parallel := NativeParallel)
            inner (probeContext instrument))
        unfold probeContext RawContext.comp
        apply ContextEquation.frame
        · intro other absent
          fin_cases other
          · change Equation (siblings 0 absent) (probe instrument)
            have probeRead := coordinates (0 : Fin 2)
            change classOf (siblings 0 absent) = classOf (probe instrument) at probeRead
            exact Quotient.exact probeRead
          · exact (absent rfl).elim
        · exact ContextEquation.refl inner

theorem probe_reaction_identity_or_factor {first : Srt source Parallel}
    (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (redex : Value (source := source) (Parallel := Parallel) first)
    (nonempty : inventory redex ≠ 0)
    (nonprobe : ∀ other : Probe source Parallel, first ≠ .probe other)
    (reaction : ContextClass (signature source Parallel) NativeParallel first (result instrument))
    (read : reaction.fill (classOf redex) = (contextClassOf (probeContext instrument)).fill supplied) :
    (result instrument = first ∧ HEq reaction
      (ContextClass.identity (signature := signature source Parallel) (Parallel := NativeParallel) first)) ∨
    ∃ before : ContextClass (signature source Parallel) NativeParallel first (receiver instrument),
      before.fill (classOf redex) = supplied ∧
        reaction = before.comp (contextClassOf (probeContext instrument)) := by
  revert read
  refine Quotient.inductionOn₂ reaction supplied ?_
  intro rawReaction rawSupplied read
  exact raw_probe_reaction_identity_or_factor instrument rawSupplied redex nonempty nonprobe rawReaction
    (read.trans (congrArg classOf (probeContext_fill instrument rawSupplied)))

end Mettapedia.OSLF.Framework.SortedTypedInstruments
