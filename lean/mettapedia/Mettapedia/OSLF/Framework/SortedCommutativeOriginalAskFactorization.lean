import Mettapedia.OSLF.Framework.SortedCommutativeProbeConstructorReadout
import Mettapedia.OSLF.Framework.SortedCommutativeProbeSourceReadout
import Mettapedia.OSLF.Syntax.SortedCommutativeContextOuterFrame

/-!
# Complete factorization of an original reaction under an ask assay

The reaction starts at the original base sort. It cannot enter a fresh
nullary probe sort. Its complete output under an ask assay consequently
places the original redex in the body slot of that exact ask frame. The
whole reaction factors through the ask label, with its entire prefix and
the independent body equation retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

private theorem raw_base_context_cannot_end_at_probe {target : Srt arity}
    (context : RawContext (signature arity) (Parallel arity) .base target) :
    ∀ instrument : Probe arity, target = .probe instrument → False := by
  apply @RawContext.rec (signature arity) (Parallel arity) .base
    (fun target _ => ∀ instrument : Probe arity, target = .probe instrument → False) (t := context)
  · intro _instrument impossible
    cases impossible
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

theorem base_context_cannot_end_at_probe (instrument : Probe arity)
    (context : RawContext (signature arity) (Parallel arity) .base (.probe instrument)) : False :=
  raw_base_context_cannot_end_at_probe context instrument rfl

private theorem constructor_inventory_heq {first second : Srt arity}
    (before : ValueClass arity first) (after : ValueClass arity second)
    (sortRead : first = second) (same : HEq before after) :
    constructorInventory before = constructorInventory after := by
  subst second
  exact congrArg constructorInventory (eq_of_heq same)

theorem raw_ask_reaction_factorization (constructor : SourceSymbol Symbols)
    (supplied redex : Value arity .base)
    (reaction : RawContext (signature arity) (Parallel arity) .base (.arguments constructor))
    (read : classOf (reaction.fill redex) =
      classOf (cut arity (.ask constructor) (probe arity (.ask constructor)) supplied)) :
    ∃ before : ContextClass (signature arity) (Parallel arity) .base .base,
      before.fill (classOf redex) = classOf supplied ∧
        contextClassOf reaction = before.comp (contextClassOf (probeContext arity (.ask constructor))) := by
  obtain ⟨found, position, siblings, inner, outputRead, contextRead⟩ :=
    reaction.outer_frame_of_nonparallel (by intro impossible; cases impossible)
      (arguments_not_parallel arity constructor)
  have completeRead := (RawContext.fill_class_heq _ _ outputRead contextRead redex).trans (heq_of_eq read)
  have heads : constructorInventory (classOf ((RawContext.frame found position siblings inner).fill redex)) =
      constructorInventory (classOf (cut arity (.ask constructor) (probe arity (.ask constructor)) supplied)) :=
    constructor_inventory_heq _ _ outputRead completeRead
  have foundRead : found = Constructor.cut (.ask constructor) := by
    change ({found} : Multiset (Constructor arity)) = {Constructor.cut (.ask constructor)} at heads
    exact Multiset.singleton_inj.mp heads
  subst found
  have reactionRead :
      (RawContext.frame (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.cut (.ask constructor)) position siblings inner :
        RawContext (signature arity) (Parallel arity) .base (.arguments constructor)) = reaction :=
    eq_of_heq contextRead
  subst reaction
  fin_cases position
  · exact (base_context_cannot_end_at_probe (.ask constructor) inner).elim
  · change RawContext (signature arity) (Parallel arity) .base .base at inner
    change classOf (Term.node (signature := signature arity) (Parallel := Parallel arity)
      (Constructor.cut (.ask constructor))
      (RawContext.insert (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.cut (.ask constructor)) 1 siblings (inner.fill redex))) =
      classOf (Term.node (signature := signature arity) (Parallel := Parallel arity)
        (Constructor.cut (.ask constructor)) _) at read
    have coordinates := (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
      (Constructor.cut (.ask constructor)) _ _).mp read
    refine ⟨contextClassOf inner, ?_, ?_⟩
    · change classOf (inner.fill redex) = classOf supplied
      have bodyRead := coordinates (1 : Fin 2)
      change classOf (inner.fill redex) = classOf supplied at bodyRead
      exact bodyRead
    · apply Quotient.sound
      change ContextEquation (signature := signature arity) (Parallel := Parallel arity)
        (RawContext.frame (signature := signature arity) (Parallel := Parallel arity)
          (Constructor.cut (.ask constructor)) 1 siblings inner)
        (RawContext.comp (signature := signature arity) (Parallel := Parallel arity)
          inner (probeContext arity (.ask constructor)))
      unfold probeContext RawContext.comp
      apply ContextEquation.frame
      · intro other absent
        fin_cases other
        · change Equation (siblings 0 absent) (probe arity (.ask constructor))
          have probeRead := coordinates (0 : Fin 2)
          change classOf (siblings 0 absent) = classOf (probe arity (.ask constructor)) at probeRead
          exact Quotient.exact probeRead
        · exact (absent rfl).elim
      · exact ContextEquation.refl inner

theorem ask_reaction_factorization (constructor : SourceSymbol Symbols)
    (supplied redex : ValueClass arity .base)
    (reaction : ContextClass (signature arity) (Parallel arity) .base (.arguments constructor))
    (read : reaction.fill redex =
      (contextClassOf (probeContext arity (.ask constructor))).fill supplied) :
    ∃ before : ContextClass (signature arity) (Parallel arity) .base .base,
      before.fill redex = supplied ∧
        reaction = before.comp (contextClassOf (probeContext arity (.ask constructor))) := by
  revert read
  refine Quotient.inductionOn₃ reaction supplied redex ?_
  intro rawReaction rawSupplied rawRedex read
  change classOf (rawReaction.fill rawRedex) =
    classOf ((probeContext arity (.ask constructor)).fill rawSupplied) at read
  exact raw_ask_reaction_factorization constructor rawSupplied rawRedex rawReaction
    (read.trans (congrArg classOf (probeContext_fill arity (.ask constructor) rawSupplied)))

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
