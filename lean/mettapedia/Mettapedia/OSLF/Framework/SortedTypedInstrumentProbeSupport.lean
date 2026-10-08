import Mettapedia.OSLF.Framework.SortedTypedInstrumentContextSupport
import Mettapedia.OSLF.Framework.SortedTypedInstrumentFiring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Complete heterogeneous probe support and fresh-context rigidity

A context with a fresh input sort and zero hereditary observer support is
the actual hole. The proof retains every declared sibling sort and uses no
inhabitant of an original sort. Probe labels have two auxiliary heads;
complete administrative redex counts include every supplied coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

theorem contextObserverCount_zero_nonoriginal_identity {first second : Srt source Parallel}
    (nonoriginal : ∀ original : source.Srt, first ≠ .original original)
    (context : RawContext (signature source Parallel) NativeParallel first second)
    (pure : contextObserverCount context = 0) :
    second = first ∧
      HEq context (.hole : RawContext (signature source Parallel) NativeParallel first first) := by
  revert pure
  apply @RawContext.rec (signature source Parallel) NativeParallel first
    (fun second context => contextObserverCount context = 0 → second = first ∧
      HEq context (.hole : RawContext (signature source Parallel) NativeParallel first first))
    (t := context)
  · intro _pure
    exact ⟨rfl, HEq.rfl⟩
  · intro constructor position siblings inner inductionHypothesis pure
    cases constructor with
    | original constructor =>
      change 0 + siblingCount (.original constructor) position siblings + contextObserverCount inner = 0 at pure
      have innerPure : contextObserverCount inner = 0 := by omega
      exact (nonoriginal (source.input constructor position) (inductionHypothesis innerPure).1.symm).elim
    | arguments head =>
      change 1 + siblingCount (.arguments head) position siblings + contextObserverCount inner = 0 at pure
      omega
    | probe instrument =>
      change 1 + siblingCount (.probe instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
    | cut instrument =>
      change 1 + siblingCount (.cut instrument) position siblings + contextObserverCount inner = 0 at pure
      omega
  · intro second parallel inner sibling inductionHypothesis pure
    cases second with
    | original original =>
      change contextObserverCount inner + observerCount sibling = 0 at pure
      have innerPure : contextObserverCount inner = 0 := by omega
      exact (nonoriginal original (inductionHypothesis innerPure).1.symm).elim
    | arguments => exact parallel.elim
    | probe => exact parallel.elim
  · intro second parallel sibling inner inductionHypothesis pure
    cases second with
    | original original =>
      change observerCount sibling + contextObserverCount inner = 0 at pure
      have innerPure : contextObserverCount inner = 0 := by omega
      exact (nonoriginal original (inductionHypothesis innerPure).1.symm).elim
    | arguments => exact parallel.elim
    | probe => exact parallel.elim

theorem classContextObserverCount_zero_nonoriginal_identity {first second : Srt source Parallel}
    (nonoriginal : ∀ original : source.Srt, first ≠ .original original)
    (context : ContextClass (signature source Parallel) NativeParallel first second)
    (pure : classContextObserverCount context = 0) :
    second = first ∧ HEq context
      (ContextClass.identity (signature := signature source Parallel) (Parallel := NativeParallel) first) := by
  revert pure
  refine Quotient.inductionOn context ?_
  intro raw pure
  obtain ⟨same, read⟩ := contextObserverCount_zero_nonoriginal_identity nonoriginal raw pure
  subst second
  exact ⟨rfl, heq_of_eq (congrArg contextClassOf (eq_of_heq read))⟩

theorem observerCount_sourceNode (head : SourceHead source Parallel) (arguments : Arguments head) :
    observerCount (sourceNode head arguments) = ∑ position, observerCount (arguments position) := by
  cases head with
  | ordinary constructor =>
    change 0 + (∑ position, observerCount (arguments position)) = _
    exact Nat.zero_add _
  | properCut sort parallel =>
    change observerCount (arguments 0) + observerCount (arguments 1) =
      ∑ position : Fin 2, observerCount (arguments position)
    rw [Fin.sum_univ_two]
  | unit sort parallel =>
    change 0 = ∑ position : Fin 0, observerCount (arguments position)
    rw [Fin.sum_univ_zero]

theorem observerCount_bundle (head : SourceHead source Parallel) (arguments : Arguments head) :
    observerCount (bundle head arguments) = 1 + ∑ position, observerCount (arguments position) := rfl

theorem observerCount_probe (instrument : Probe source Parallel) :
    observerCount (probe instrument) = 1 := by
  change 1 + (∑ position : Fin 0, observerCount (Fin.elim0 position)) = 1
  simp only [Fin.sum_univ_zero, Nat.add_zero]

theorem contextObserverCount_probeContext (instrument : Probe source Parallel) :
    contextObserverCount (probeContext instrument) = 2 := by
  unfold probeContext
  change 1 + siblingCount (.cut instrument) 1 _ + 0 = 2
  unfold siblingCount
  change 1 + (∑ other : Fin 2, _) + 0 = 2
  rw [Fin.sum_univ_two]
  norm_num [Fin.cases]
  change 1 + observerCount (probe instrument) = 2
  rw [observerCount_probe]

theorem observerCount_probeCut (instrument : Probe source Parallel)
    (body : Value (source := source) (Parallel := Parallel) (receiver instrument)) :
    observerCount (cut instrument (probe instrument) body) = 2 + observerCount body := by
  rw [← probeContext_fill, contextObserverCount_fill, contextObserverCount_probeContext]

def probeLabel (instrument : Probe source Parallel) :
    (.interface (receiver instrument) : ContextCategory source Parallel) ⟶ .interface (result instrument) :=
  RawArrow.context (contextClassOf (probeContext instrument))

theorem probeLabel_support (instrument : Probe source Parallel) :
    arrowObserverCount (probeLabel instrument) = 2 := contextObserverCount_probeContext instrument

theorem ask_redex_support (Origins : Type w) (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) :
    arrowObserverCount (Occurrence.rule (Occurrence.ask origin head arguments)).redex =
      2 + ∑ position, observerCount (arguments position) := by
  change observerCount (cut (.ask head) (probe (.ask head)) (sourceNode head arguments)) = _
  rw [observerCount_probeCut, observerCount_sourceNode]

theorem get_redex_support (Origins : Type w) (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) (position : Fin (headArity head)) :
    arrowObserverCount (Occurrence.rule (Occurrence.get origin head arguments position)).redex =
      3 + ∑ other, observerCount (arguments other) := by
  change observerCount (cut (.get head position) (probe (.get head position)) (bundle head arguments)) = _
  rw [observerCount_probeCut, observerCount_bundle]
  omega

theorem build_redex_support (Origins : Type w) (origin : Origins) (head : SourceHead source Parallel)
    (arguments : Arguments head) :
    arrowObserverCount (Occurrence.rule (Occurrence.build origin head arguments)).redex =
      3 + ∑ position, observerCount (arguments position) := by
  change observerCount (cut (.build head) (probe (.build head)) (bundle head arguments)) = _
  rw [observerCount_probeCut, observerCount_bundle]
  omega

end Mettapedia.OSLF.Framework.SortedTypedInstruments
