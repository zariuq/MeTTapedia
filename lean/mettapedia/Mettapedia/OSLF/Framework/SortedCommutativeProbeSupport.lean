import Mettapedia.OSLF.Syntax.SortedCommutativeSourceSupport
import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentFiring

/-!
# Complete probe support and identity of pure nonbase contexts

A context with nonbase input and zero hereditary observer support is the
literal hole. This property is proved on raw typed contexts and then on
their independently generated classes. Complete administrative redex
support counts retain every argument; ask has two auxiliary heads, while
get and build have three. No firing inversion or observer adequacy is an
assumption of these calculations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat}

theorem contextObserverCount_zero_nonbase_identity {source target : Srt arity}
    (nonbase : source ≠ .base)
    (context : RawContext (signature arity) (Parallel arity) source target)
    (pure : contextObserverCount context = 0) :
    target = source ∧ HEq context (.hole : RawContext (signature arity) (Parallel arity) source source) := by
  revert pure
  apply @RawContext.rec (signature arity) (Parallel arity) source
    (fun target context => contextObserverCount context = 0 →
      target = source ∧ HEq context (.hole : RawContext (signature arity) (Parallel arity) source source))
    (t := context)
  · intro _pure
    exact ⟨rfl, HEq.rfl⟩
  · intro constructor position siblings inner inductionHypothesis pure
    cases constructor with
    | original symbol =>
      change 0 + siblingCount (.original symbol) position siblings + contextObserverCount inner = 0 at pure
      have innerPure : contextObserverCount inner = 0 := by omega
      exact (nonbase (inductionHypothesis innerPure).1.symm).elim
    | arguments constructor =>
      change 1 + siblingCount (.arguments constructor) position siblings + contextObserverCount inner = 0 at pure
      omega
    | probe instrument =>
      change 1 + siblingCount (.probe instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
    | cut instrument =>
      change 1 + siblingCount (.cut instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
  · intro target parallel inner sibling inductionHypothesis pure
    change target = .base at parallel
    subst target
    change contextObserverCount inner + observerCount sibling = 0 at pure
    have innerPure : contextObserverCount inner = 0 := by omega
    exact (nonbase (inductionHypothesis innerPure).1.symm).elim
  · intro target parallel sibling inner inductionHypothesis pure
    change target = .base at parallel
    subst target
    change observerCount sibling + contextObserverCount inner = 0 at pure
    have innerPure : contextObserverCount inner = 0 := by omega
    exact (nonbase (inductionHypothesis innerPure).1.symm).elim

theorem classContextObserverCount_zero_nonbase_identity {source target : Srt arity}
    (nonbase : source ≠ .base)
    (context : ContextClass (signature arity) (Parallel arity) source target)
    (pure : classContextObserverCount context = 0) :
    target = source ∧ HEq context (ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) source) := by
  revert pure
  refine Quotient.inductionOn context ?_
  intro raw pure
  obtain ⟨same, read⟩ := contextObserverCount_zero_nonbase_identity nonbase raw pure
  subst target
  exact ⟨rfl, heq_of_eq (congrArg contextClassOf (eq_of_heq read))⟩

theorem observerCount_sourceNode (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) :
    observerCount (sourceNode arity constructor arguments) = ∑ position, observerCount (arguments position) := by
  cases constructor with
  | ordinary symbol =>
    change 0 + (∑ position, observerCount (arguments position)) = _
    exact Nat.zero_add _
  | properCut =>
    change observerCount (arguments 0) + observerCount (arguments 1) = ∑ position : Fin 2, observerCount (arguments position)
    rw [Fin.sum_univ_two]
  | unit =>
    change 0 = ∑ position : Fin 0, observerCount (arguments position)
    rw [Fin.sum_univ_zero]

theorem observerCount_bundle (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) :
    observerCount (bundle arity constructor arguments) = 1 + ∑ position, observerCount (arguments position) := rfl

theorem observerCount_probeCut (instrument : Probe arity)
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)) :
    observerCount (cut arity instrument (probe arity instrument) body) = 2 + observerCount body := by
  rw [← probeContext_fill, contextObserverCount_fill, contextObserverCount_probeContext]

theorem ask_redex_support (origin : Type w) (suppliedOrigin : origin) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) :
    arrowObserverCount (Occurrence.rule (Occurrence.ask suppliedOrigin constructor arguments)).redex =
      2 + ∑ position, observerCount (arguments position) := by
  change observerCount (cut arity (.ask constructor) (probe arity (.ask constructor))
    (sourceNode arity constructor arguments)) = _
  rw [observerCount_probeCut, observerCount_sourceNode]

theorem get_redex_support (origin : Type w) (suppliedOrigin : origin) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base)
    (position : Fin (sourceArity arity constructor)) :
    arrowObserverCount (Occurrence.rule (Occurrence.get suppliedOrigin constructor arguments position)).redex =
      3 + ∑ position, observerCount (arguments position) := by
  change observerCount (cut arity (.get constructor position) (probe arity (.get constructor position))
    (bundle arity constructor arguments)) = _
  rw [observerCount_probeCut, observerCount_bundle]
  omega

theorem build_redex_support (origin : Type w) (suppliedOrigin : origin) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base) :
    arrowObserverCount (Occurrence.rule (Occurrence.build suppliedOrigin constructor arguments)).redex =
      3 + ∑ position, observerCount (arguments position) := by
  change observerCount (cut arity (.build constructor) (probe arity (.build constructor))
    (bundle arity constructor arguments)) = _
  rw [observerCount_probeCut, observerCount_bundle]
  omega

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support
