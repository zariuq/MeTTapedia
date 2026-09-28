import Mettapedia.OSLF.Syntax.RhoPayloadResources
import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison
import Mettapedia.GSLT.Causality.ResourceReads

/-!
# The authored rho executor fires on bags of atoms

The authored executor steps a process by communication inside parallel bags.
Translated into the payload presentation, each executor step is one firing on
the bag of atom classes: an output and an input on one channel class are
consumed, and the atoms of the continuation are produced. Conversely, every
firing on the atom bag of an admitted closed process is an executor step from
a structurally congruent rearrangement, and it reaches a process whose atoms
are the fired bag. The profile with Drop behaves the same way.

The conflicts and commuting squares of the resource system are therefore
properties of the executor. Two communications whose atoms fit together are
executor steps in either order, meeting in one bag of atoms. An output wanted
by two inputs is taken by one of them: after either communication, the other
is not enabled.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoPayloadPresentation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)
open Mettapedia.OSLF.Binding.RhoCombinedInterpretedStep (RhoStepWithDrop)
open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.ResourceInteraction

attribute [local instance] Classical.propDecidable

/-- Firing a communication keeps a bag of atoms a bag of atoms. -/
theorem atomBag_of_strict_step {M N : Multiset (Cls [] Srt.pr)} (bag : AtomBag M)
    (step : (strictSystem []).theory.Step M N) : AtomBag N := by
  obtain ⟨_, _, _, rfl⟩ := step
  exact atomBag_add (atomBag_of_le bag tsub_le_self) (atomBag_atoms _)

/-- Firing a communication or a drop keeps a bag of atoms a bag of atoms. -/
theorem atomBag_of_book_step {M N : Multiset (Cls [] Srt.pr)} (bag : AtomBag M)
    (step : (bookSystem []).theory.Step M N) : AtomBag N := by
  obtain ⟨site, _, _, rfl⟩ := step
  cases site <;> exact atomBag_add (atomBag_of_le bag tsub_le_self) (atomBag_atoms _)

/-- **Every executor step is one communication on the bags of atoms.** -/
theorem executor_step_fires {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoStep source target) {s₀ : Term sig [] Srt.pr}
    (hs : tProc (Env.empty []) source = some s₀) :
    ∃ t₀, tProc (Env.empty []) target = some t₀ ∧
      (strictSystem []).theory.Step (atoms s₀) (atoms t₀) := by
  obtain ⟨t₀, ht, steps⟩ := rhoStep_simulation sourceTyped step hs
  exact ⟨t₀, ht, (strict_step_iff s₀ t₀).mp steps⟩

/-- **Every step of the executor with Drop is one communication or one drop on
the bags of atoms.** -/
theorem executorWithDrop_step_fires {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoStepWithDrop source target) {s₀ : Term sig [] Srt.pr}
    (hs : tProc (Env.empty []) source = some s₀) :
    ∃ t₀, tProc (Env.empty []) target = some t₀ ∧
      (bookSystem []).theory.Step (atoms s₀) (atoms t₀) := by
  obtain ⟨t₀, ht, steps⟩ := rhoStepWithDrop_simulation sourceTyped step hs
  exact ⟨t₀, ht, (book_step_iff s₀ t₀).mp steps⟩

/-- **Every communication on the atom bag of an admitted closed process is an
executor step** from a structurally congruent rearrangement, reaching a process
whose atoms are the fired bag. -/
theorem firing_realized {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    {N : Multiset (Cls [] Srt.pr)} (step : (strictSystem []).theory.Step (atoms s₀) N) :
    ∃ P₁ P', StructuralCongruence P P₁ ∧ RhoStep P₁ P' ∧
      ∃ t, tProc (Env.empty []) P' = some t ∧ atoms t = N := by
  have bag := atomBag_of_strict_step (atomBag_atoms s₀) step
  have steps : Steps strictRules s₀ (realize N) :=
    (strict_step_iff s₀ (realize N)).mpr (by rw [atoms_realize bag]; exact step)
  obtain ⟨P₁, P', congruent, executes, t, ht, same⟩ := strict_reflection typed hs steps
  exact ⟨P₁, P', congruent, executes, t, ht,
    by rw [atoms_invariant (cls_eq_iff.mp same), atoms_realize bag]⟩

/-- **Every communication or drop on the atom bag of an admitted closed process
is a step of the executor with Drop**, from a structurally congruent
rearrangement. -/
theorem bookFiring_realized {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    {N : Multiset (Cls [] Srt.pr)} (step : (bookSystem []).theory.Step (atoms s₀) N) :
    ∃ P₁ P', StructuralCongruence P P₁ ∧ RhoStepWithDrop P₁ P' ∧
      ∃ t, tProc (Env.empty []) P' = some t ∧ atoms t = N := by
  have bag := atomBag_of_book_step (atomBag_atoms s₀) step
  have steps : Steps bookRules s₀ (realize N) :=
    (book_step_iff s₀ (realize N)).mpr (by rw [atoms_realize bag]; exact step)
  obtain ⟨P₁, P', congruent, executes, t, ht, same⟩ := book_reflection typed hs steps
  exact ⟨P₁, P', congruent, executes, t, ht,
    by rw [atoms_invariant (cls_eq_iff.mp same), atoms_realize bag]⟩

/-- **Concurrent communications are executor steps in either order.** From an
admitted closed process, two communications whose atoms fit together are each
an executor step, each is again an executor step after the other, and both
orders reach one bag of atoms. -/
theorem executor_square {free : FreeSortContext} {P : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] P)
    {s₀ : Term sig [] Srt.pr} (hs : tProc (Env.empty []) P = some s₀)
    (i j : CommInstance [])
    (concurrent : (strictSystem []).Concurrent (atoms s₀) (site₁ := ()) (site₂ := ()) i j) :
    (∃ P₁ P', StructuralCongruence P P₁ ∧ RhoStep P₁ P' ∧ ∃ t, tProc (Env.empty []) P' = some t ∧
        atoms t = (strictSystem []).fire (atoms s₀) (site := ()) i) ∧
      (∃ P₁ P', StructuralCongruence P P₁ ∧ RhoStep P₁ P' ∧ ∃ t, tProc (Env.empty []) P' = some t ∧
        atoms t = (strictSystem []).fire (atoms s₀) (site := ()) j) ∧
      (strictSystem []).fire ((strictSystem []).fire (atoms s₀) (site := ()) i) (site := ()) j =
        (strictSystem []).fire ((strictSystem []).fire (atoms s₀) (site := ()) j) (site := ()) i := by
  have square := (strictSystem []).square_of_concurrent concurrent
  exact ⟨firing_realized typed hs ⟨(), i, square.first, rfl⟩,
    firing_realized typed hs ⟨(), j, square.second, rfl⟩, square.meet⟩

end Mettapedia.OSLF.Binding.RhoPayloadPresentation

#print axioms Mettapedia.OSLF.Binding.RhoPayloadPresentation.executor_step_fires
#print axioms Mettapedia.OSLF.Binding.RhoPayloadPresentation.executorWithDrop_step_fires
#print axioms Mettapedia.OSLF.Binding.RhoPayloadPresentation.firing_realized
#print axioms Mettapedia.OSLF.Binding.RhoPayloadPresentation.bookFiring_realized
#print axioms Mettapedia.OSLF.Binding.RhoPayloadPresentation.executor_square
