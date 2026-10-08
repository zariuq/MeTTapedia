import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeReadout
import Mettapedia.OSLF.Syntax.SortedCommutativeContextOuterFrame

/-!
# Whole original-reaction factorization at a heterogeneous ask label

An original-sort context cannot enter a fresh nullary probe sort. Its
complete output at the nonparallel ask result therefore has the exact ask
head and places the entire original redex in the body position. The inner
context may change original sorts. Its complete typed filling equation and
every sibling are retained, including when the redex is an AC1 unit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open Mettapedia.OSLF.SortedCommutative

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

private theorem raw_original_context_cannot_end_at_probe {original : source.Srt}
    {target : Srt source Parallel}
    (context : RawContext (signature source Parallel) NativeParallel (.original original) target) :
    ∀ instrument : Probe source Parallel, target = .probe instrument → False := by
  apply @RawContext.rec (signature source Parallel) NativeParallel (.original original)
    (fun target _ => ∀ instrument : Probe source Parallel, target = .probe instrument → False) (t := context)
  · intro _instrument impossible
    cases impossible
  · intro constructor position _siblings _inner _inductionHypothesis instrument impossible
    cases constructor with
    | original => cases impossible
    | arguments => cases impossible
    | probe => exact Fin.elim0 position
    | cut selected => cases selected <;> cases impossible
  · intro target parallel _inner _sibling _inductionHypothesis _instrument impossible
    cases target with
    | original => cases impossible
    | arguments => exact parallel.elim
    | probe => exact parallel.elim
  · intro target parallel _sibling _inner _inductionHypothesis _instrument impossible
    cases target with
    | original => cases impossible
    | arguments => exact parallel.elim
    | probe => exact parallel.elim

theorem original_context_cannot_end_at_probe {original : source.Srt}
    (instrument : Probe source Parallel)
    (context : RawContext (signature source Parallel) NativeParallel (.original original) (.probe instrument)) : False :=
  raw_original_context_cannot_end_at_probe context instrument rfl

private theorem constructor_inventory_heq {first second : Srt source Parallel}
    (before : ValueClass (source := source) (Parallel := Parallel) first)
    (after : ValueClass (source := source) (Parallel := Parallel) second)
    (sortRead : first = second) (same : HEq before after) :
    constructorInventory before = constructorInventory after := by
  subst second
  exact congrArg constructorInventory (eq_of_heq same)

theorem raw_ask_reaction_factorization {original : source.Srt}
    (head : SourceHead source Parallel)
    (supplied : Value (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (redex : Value (source := source) (Parallel := Parallel) (.original original))
    (reaction : RawContext (signature source Parallel) NativeParallel (.original original) (.arguments head))
    (read : classOf (reaction.fill redex) = classOf (cut (.ask head) (probe (.ask head)) supplied)) :
    ∃ before : ContextClass (signature source Parallel) NativeParallel
        (.original original) (.original (headOutput head)),
      before.fill (classOf redex) = classOf supplied ∧
        contextClassOf reaction = before.comp (contextClassOf (probeContext (.ask head))) := by
  obtain ⟨found, position, siblings, inner, outputRead, contextRead⟩ :=
    reaction.outer_frame_of_nonparallel (by intro impossible; cases impossible) (arguments_not_parallel head)
  have completeRead := (RawContext.fill_class_heq _ _ outputRead contextRead redex).trans (heq_of_eq read)
  have heads : constructorInventory (classOf ((RawContext.frame found position siblings inner).fill redex)) =
      constructorInventory (classOf (cut (.ask head) (probe (.ask head)) supplied)) :=
    constructor_inventory_heq _ _ outputRead completeRead
  have foundRead : found = Constructor.cut (.ask head) := by
    change ({found} : Multiset (Constructor source Parallel)) = {Constructor.cut (.ask head)} at heads
    exact Multiset.singleton_inj.mp heads
  subst found
  have reactionRead :
      (RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
        (Constructor.cut (.ask head)) position siblings inner :
        RawContext (signature source Parallel) NativeParallel (.original original) (.arguments head)) = reaction :=
    eq_of_heq contextRead
  subst reaction
  fin_cases position
  · exact (original_context_cannot_end_at_probe (.ask head) inner).elim
  · change RawContext (signature source Parallel) NativeParallel
      (.original original) (.original (headOutput head)) at inner
    change classOf (Term.node (signature := signature source Parallel) (Parallel := NativeParallel)
      (Constructor.cut (.ask head))
      (RawContext.insert (signature := signature source Parallel) (Parallel := NativeParallel)
        (Constructor.cut (.ask head)) 1 siblings (inner.fill redex))) =
      classOf (Term.node (signature := signature source Parallel) (Parallel := NativeParallel)
        (Constructor.cut (.ask head)) _) at read
    have coordinates := (node_class_eq_iff (signature := signature source Parallel) (Parallel := NativeParallel)
      (Constructor.cut (.ask head)) _ _).mp read
    refine ⟨contextClassOf inner, ?_, ?_⟩
    · change classOf (inner.fill redex) = classOf supplied
      have bodyRead := coordinates (1 : Fin 2)
      change classOf (inner.fill redex) = classOf supplied at bodyRead
      exact bodyRead
    · apply Quotient.sound
      change ContextEquation (signature := signature source Parallel) (Parallel := NativeParallel)
        (RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
          (Constructor.cut (.ask head)) 1 siblings inner)
        (RawContext.comp (signature := signature source Parallel) (Parallel := NativeParallel)
          inner (probeContext (.ask head)))
      unfold probeContext RawContext.comp
      apply ContextEquation.frame
      · intro other absent
        fin_cases other
        · change Equation (siblings 0 absent) (probe (.ask head))
          have probeRead := coordinates (0 : Fin 2)
          change classOf (siblings 0 absent) = classOf (probe (.ask head)) at probeRead
          exact Quotient.exact probeRead
        · exact (absent rfl).elim
      · exact ContextEquation.refl inner

theorem ask_reaction_factorization {original : source.Srt}
    (head : SourceHead source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)))
    (redex : ValueClass (source := source) (Parallel := Parallel) (.original original))
    (reaction : ContextClass (signature source Parallel) NativeParallel (.original original) (.arguments head))
    (read : reaction.fill redex = (contextClassOf (probeContext (.ask head))).fill supplied) :
    ∃ before : ContextClass (signature source Parallel) NativeParallel
        (.original original) (.original (headOutput head)),
      before.fill redex = supplied ∧ reaction = before.comp (contextClassOf (probeContext (.ask head))) := by
  revert read
  refine Quotient.inductionOn₃ reaction supplied redex ?_
  intro rawReaction rawSupplied rawRedex read
  change classOf (rawReaction.fill rawRedex) = classOf ((probeContext (.ask head)).fill rawSupplied) at read
  exact raw_ask_reaction_factorization head rawSupplied rawRedex rawReaction
    (read.trans (congrArg classOf (probeContext_fill (.ask head) rawSupplied)))

end Mettapedia.OSLF.Framework.SortedTypedInstruments
