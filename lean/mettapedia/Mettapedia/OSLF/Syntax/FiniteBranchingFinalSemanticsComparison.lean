import Mettapedia.CategoryTheory.FiniteActionTreeFinalSemantics
import Mettapedia.OSLF.Syntax.FiniteBranchingFinalSemantics

/-!
# Canonical comparison with general indexed final observations

The general indexed final coalgebra specializes to the existing finite
syntax observation functor. The comparison is the unique isomorphism between
the two earned final objects; every actual observation arrow commutes with
it. This comparison introduces no signature requirement on generic indexed
coalgebras.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.FinalSemanticsComparison

open _root_.CategoryTheory
open Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

abbrev Base := PUnit.{u + 1}
abbrev Index (_ : Base.{u}) := S.Srt
abbrev labels (_ : Base.{u}) (sort : S.Srt) := Actions sort

def promotedObject : Endofunctor.Coalgebra (behaviourFunctor S Actions) :=
  FiniteActionTreeFinalSemantics.finalObject Base (Index S) (labels S Actions)

def promotedFinal : Limits.IsTerminal (promotedObject S Actions) :=
  FiniteActionTreeFinalSemantics.isFinal Base (Index S) (labels S Actions)

/-- The unique comparison is earned by the two actual final universal properties. -/
def comparison : promotedObject S Actions ≅ FinalSemantics.finalObject S Actions :=
  (promotedFinal S Actions).uniqueUpToIso (FinalSemantics.isFinal S Actions)

def promotedObserve (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    object ⟶ promotedObject S Actions :=
  FiniteActionTreeFinalSemantics.observe Base (Index S) (labels S Actions) object

theorem comparison_observe (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    promotedObserve S Actions object ≫ (comparison S Actions).hom =
      FinalSemantics.observe S Actions object :=
  FinalSemantics.observe_unique S Actions object _

theorem inverse_comparison_observe
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    FinalSemantics.observe S Actions object ≫ (comparison S Actions).inv =
      promotedObserve S Actions object :=
  FiniteActionTreeFinalSemantics.observe_unique Base (Index S) (labels S Actions) object _

theorem comparison_natural
    {first second : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (mapping : first ⟶ second) :
    mapping ≫ promotedObserve S Actions second ≫ (comparison S Actions).hom =
      FinalSemantics.observe S Actions first := by
  rw [comparison_observe]
  exact FinalSemantics.observe_natural S Actions mapping

end Mettapedia.OSLF.FiniteBranching.FinalSemanticsComparison
