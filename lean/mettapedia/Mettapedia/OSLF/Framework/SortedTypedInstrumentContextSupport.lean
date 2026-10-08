import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceCategory

/-!+# Hereditary support under complete context action and composition

The selected input appears exactly once in a genuine one-hole context.
Filling adds its observer measure to that of every sibling and path frame;
composition adds the complete context measures. These actual readouts descend
through the generated equations and apply to every native typed arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open scoped BigOperators

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

theorem insert_count (constructor : Constructor source Parallel)
    (position : Fin ((signature source Parallel).arity constructor))
    (siblings : (other : Fin ((signature source Parallel).arity constructor)) → other ≠ position →
      Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor other))
    (supplied : Value (source := source) (Parallel := Parallel) ((signature source Parallel).input constructor position)) :
    (∑ other, observerCount (RawContext.insert constructor position siblings supplied other)) =
      observerCount supplied + siblingCount constructor position siblings := by
  classical
  calc
    _ = ∑ other, ((if other = position then observerCount supplied else 0) +
        (if absent : other ≠ position then observerCount (siblings other absent) else 0)) := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases same : other = position
      · subst other
        simp only [RawContext.insert, dite_true, if_true, ne_eq, not_true_eq_false, dite_false, Nat.add_zero]
      · simp only [RawContext.insert, dif_neg same, if_neg same, dif_pos same, Nat.zero_add]
    _ = observerCount supplied + siblingCount constructor position siblings := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, siblingCount]

theorem contextObserverCount_fill {first second : Srt source Parallel}
    (context : RawContext (signature source Parallel) NativeParallel first second)
    (supplied : Value (source := source) (Parallel := Parallel) first) :
    observerCount (context.fill supplied) = contextObserverCount context + observerCount supplied := by
  apply @RawContext.rec (signature source Parallel) NativeParallel first
    (fun _ context => observerCount (context.fill supplied) = contextObserverCount context + observerCount supplied)
    (t := context)
  · exact (Nat.zero_add _).symm
  · intro constructor position siblings inner inductionHypothesis
    change constructorWeight constructor +
      (∑ other, observerCount (RawContext.insert constructor position siblings (inner.fill supplied) other)) = _
    rw [insert_count, inductionHypothesis]
    change _ = (constructorWeight constructor + siblingCount constructor position siblings + contextObserverCount inner) + observerCount supplied
    omega
  · intro target parallel inner sibling inductionHypothesis
    change observerCount (inner.fill supplied) + observerCount sibling = _
    rw [inductionHypothesis]
    change _ = (contextObserverCount inner + observerCount sibling) + observerCount supplied
    omega
  · intro target parallel sibling inner inductionHypothesis
    change observerCount sibling + observerCount (inner.fill supplied) = _
    rw [inductionHypothesis]
    change _ = (observerCount sibling + contextObserverCount inner) + observerCount supplied
    omega

theorem contextObserverCount_comp {first second third : Srt source Parallel}
    (before : RawContext (signature source Parallel) NativeParallel first second)
    (after : RawContext (signature source Parallel) NativeParallel second third) :
    contextObserverCount (before.comp after) = contextObserverCount before + contextObserverCount after := by
  apply @RawContext.rec (signature source Parallel) NativeParallel second
    (fun _ after => contextObserverCount (before.comp after) = contextObserverCount before + contextObserverCount after)
    (t := after)
  · exact (Nat.add_zero _).symm
  · intro constructor position siblings outer inductionHypothesis
    change constructorWeight constructor + siblingCount constructor position siblings + contextObserverCount (before.comp outer) = _
    rw [inductionHypothesis]
    change _ = contextObserverCount before + (constructorWeight constructor + siblingCount constructor position siblings + contextObserverCount outer)
    omega
  · intro target parallel outer sibling inductionHypothesis
    change contextObserverCount (before.comp outer) + observerCount sibling = _
    rw [inductionHypothesis]
    exact Nat.add_assoc _ _ _
  · intro target parallel sibling outer inductionHypothesis
    change observerCount sibling + contextObserverCount (before.comp outer) = _
    rw [inductionHypothesis]
    change _ = contextObserverCount before + (observerCount sibling + contextObserverCount outer)
    omega

theorem classCount_fill {first second : Srt source Parallel}
    (context : ContextClass (signature source Parallel) NativeParallel first second)
    (supplied : ValueClass (source := source) (Parallel := Parallel) first) :
    classObserverCount (context.fill supplied) = classContextObserverCount context + classObserverCount supplied :=
  Quotient.inductionOn₂ context supplied contextObserverCount_fill

theorem classCount_comp {first second third : Srt source Parallel}
    (before : ContextClass (signature source Parallel) NativeParallel first second)
    (after : ContextClass (signature source Parallel) NativeParallel second third) :
    classContextObserverCount (before.comp after) = classContextObserverCount before + classContextObserverCount after :=
  Quotient.inductionOn₂ before after contextObserverCount_comp

def arrowObserverCount : {first second : ContextCategory source Parallel} → (first ⟶ second) → Nat
  | _, _, .identity => 0
  | _, _, .value supplied => classObserverCount supplied
  | _, _, .context supplied => classContextObserverCount supplied

theorem arrowCount_comp {first second third : ContextCategory source Parallel}
    (before : first ⟶ second) (after : second ⟶ third) :
    arrowObserverCount (before ≫ after) = arrowObserverCount before + arrowObserverCount after := by
  cases before with
  | identity => exact (Nat.zero_add _).symm
  | value supplied =>
    cases after with
    | context context => exact (classCount_fill context supplied).trans (Nat.add_comm _ _)
  | context before =>
    cases after with
    | context after => exact classCount_comp before after

theorem composite_zero_support {first second third : ContextCategory source Parallel}
    (before : first ⟶ second) (after : second ⟶ third)
    (pure : arrowObserverCount (before ≫ after) = 0) :
    arrowObserverCount before = 0 ∧ arrowObserverCount after = 0 := by
  rw [arrowCount_comp] at pure
  exact Nat.add_eq_zero_iff.mp pure

end Mettapedia.OSLF.Framework.SortedTypedInstruments
