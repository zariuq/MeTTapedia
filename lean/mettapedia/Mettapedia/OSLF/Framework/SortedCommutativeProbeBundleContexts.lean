import Mettapedia.OSLF.Framework.SortedCommutativeProbeSupport

/-!
# Complete support required to leave an argument-bundle sort

An argument-bundle context with fewer than two auxiliary heads is the
literal hole. An administrative Cut requires its separate probe sibling;
counting only the selected path would miss that obligation. The result
descends through the actual context equations and excludes ask rules from
get/build assays without assuming a chosen root or a deterministic match.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

theorem contextObserverCount_lt_two_bundle_identity (constructor : SourceSymbol Symbols)
    {target : Srt arity}
    (context : RawContext (signature arity) (Parallel arity) (.arguments constructor) target)
    (small : contextObserverCount context < 2) :
    target = .arguments constructor ∧ HEq context
      (.hole : RawContext (signature arity) (Parallel arity)
        (.arguments constructor) (.arguments constructor)) := by
  revert small
  apply @RawContext.rec (signature arity) (Parallel arity) (.arguments constructor)
    (fun target context => contextObserverCount context < 2 →
      target = .arguments constructor ∧ HEq context
        (.hole : RawContext (signature arity) (Parallel arity)
          (.arguments constructor) (.arguments constructor))) (t := context)
  · intro _small
    exact ⟨rfl, HEq.rfl⟩
  · intro frame position siblings inner inductionHypothesis small
    cases frame with
    | original symbol =>
      change 0 + siblingCount (.original symbol) position siblings + contextObserverCount inner < 2 at small
      have innerSmall : contextObserverCount inner < 2 := by omega
      have impossible := (inductionHypothesis innerSmall).1
      cases impossible
    | arguments found =>
      change 1 + siblingCount (.arguments found) position siblings + contextObserverCount inner < 2 at small
      have innerPure : contextObserverCount inner = 0 := by omega
      have impossible := (contextObserverCount_zero_nonbase_identity
        (show (.arguments constructor : Srt arity) ≠ .base from by intro same; cases same)
        inner innerPure).1
      cases impossible
    | probe instrument =>
      exact Fin.elim0 position
    | cut instrument =>
      change 1 + siblingCount (.cut instrument) position siblings + contextObserverCount inner < 2 at small
      have innerPure : contextObserverCount inner = 0 := by omega
      have siblingsPure : siblingCount (.cut instrument) position siblings = 0 := by omega
      by_cases first : position = 0
      · subst position
        have impossible := (contextObserverCount_zero_nonbase_identity
          (show (.arguments constructor : Srt arity) ≠ .base from by intro same; cases same)
          inner innerPure).1
        change (.probe instrument : Srt arity) = .arguments constructor at impossible
        cases impossible
      · have absent : (0 : Fin 2) ≠ position := Ne.symm first
        have siblingPure := siblingCount_zero siblings siblingsPure 0 absent
        have impossible := observerCount_zero_sort (siblings 0 absent) siblingPure
        change (.probe instrument : Srt arity) = .base at impossible
        cases impossible
  · intro target parallel inner sibling inductionHypothesis small
    change target = .base at parallel
    subst target
    change contextObserverCount inner + observerCount sibling < 2 at small
    have innerSmall : contextObserverCount inner < 2 := by omega
    have impossible := (inductionHypothesis innerSmall).1
    cases impossible
  · intro target parallel sibling inner inductionHypothesis small
    change target = .base at parallel
    subst target
    change observerCount sibling + contextObserverCount inner < 2 at small
    have innerSmall : contextObserverCount inner < 2 := by omega
    have impossible := (inductionHypothesis innerSmall).1
    cases impossible

theorem classContextObserverCount_lt_two_bundle_identity (constructor : SourceSymbol Symbols)
    {target : Srt arity}
    (context : ContextClass (signature arity) (Parallel arity) (.arguments constructor) target)
    (small : classContextObserverCount context < 2) :
    target = .arguments constructor ∧ HEq context
      (ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) (.arguments constructor)) := by
  revert small
  refine Quotient.inductionOn context ?_
  intro raw small
  obtain ⟨same, read⟩ := contextObserverCount_lt_two_bundle_identity constructor raw small
  subst target
  exact ⟨rfl, heq_of_eq (congrArg contextClassOf (eq_of_heq read))⟩

theorem classContextObserverCount_bundle_to_base (constructor : SourceSymbol Symbols)
    (context : ContextClass (signature arity) (Parallel arity) (.arguments constructor) .base) :
    2 ≤ classContextObserverCount context := by
  by_contra small
  have impossible := (classContextObserverCount_lt_two_bundle_identity constructor context (by omega)).1
  cases impossible

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support
