import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesOccursEdge

/-!
# Two arguments of different types, both held at bound variables

Over `A : U0, B : U0, Q : A → B → U0` (`reboundStore`):

  `λ x y. Q x y ≐ λ x y. Π (z : A). Π (w : B). Q z w`  at  `Π (x : A) (y : B). U0`.

The right side holds the unknown `Q` of the pattern at the two variables it binds: `z` has to go to `x` and `w` to
`y`, two abstractions of different types. The rule reads the equation with both abstractions in scope
(`rebound_read`).

The store is in the fragment (`rebound_in_fragment`) and has no solution (`rebound_unsolvable`, proved apart from
the rule: the renaming that sends `z` to `x` and `w` to `y` carries `Q z w` back to `Q x y`,
`ContextualDependentOccursRenamed.renamed_occurrence_not_typeEq`). The family below is stuck on it wherever its
compiled run reads `stuck` (`rebound_stuck_below_of_ending`) and the family with the rule refutes it wherever its
compiled run reads `refuted` (`rebound_refuted_of_ending`). Those readings are evaluations, not theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls ContextualDependentRigidFormers ContextualDependentOccursRenamed
open ContextualDependentOccursBound

/-- `A → B → U0`, over `A B`. -/
def familyOverAB : TypeOver ctxAX := formIn ctxAX (.pi (.var 1) (.pi (.var 1) u0)) (by decide +kernel)

/-- `A : U0, B : U0, Q : A → B → U0`. -/
abbrev ctxABQ := extend ctxAX familyOverAB

/-- `Π (x : A) (y : B). U0`, over `A B Q`. -/
def reboundType : TypeOver ctxABQ := formIn ctxABQ (.pi (.var 2) (.pi (.var 2) u0)) (by decide +kernel)

theorem reboundType_code : reboundType.code = .pi (.var (2 : Fin 3)) (.pi (.var 2) u0) := by decide +kernel

/-- `λ x y. Q x y ≐ λ x y. Π (z : A). Π (w : B). Q z w`. -/
def reboundEquation : Equation (TotalTerm ctxABQ) :=
  (termIn ctxABQ reboundType (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxABQ reboundType
      (.lam (.lam (.pi (.var 4) (.pi (.var 4) (.app (.app (.var 4) (.var 1)) (.var 0)))))) (by decide +kernel))
def reboundStore : EquationStore (TotalTerm ctxABQ) := [reboundEquation]

/-- The raw problem. -/
def reboundProblem : Problem :=
  { unknowns := [.u0, .u0, .pi (.var 1) (.pi (.var 1) .u0)],
    equations := [(.pi (.var 2) (.pi (.var 2) .u0), .lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0))),
      .lam (.lam (.pi (.var 4) (.pi (.var 4) (.app (.app (.var 4) (.var 1)) (.var 0))))))] }

theorem rebound_in_fragment : InFragmentStore reboundStore := storeInside_sound (by decide +kernel)

/-- The rule reads the equation, with both abstractions in scope: `z` goes to `x` and `w` to `y`. -/
theorem rebound_read : (boundShape (S := setting) reboundEquation).isSome = true := by decide +kernel

/-- **The store has no solution.** Under the two abstractions a solution would make `Q x y` equal to
`Π (z : A). Π (w : B). Q z w`; sending `z` to `x` and `w` to `y` carries `Q z w` back to `Q x y`. -/
theorem rebound_unsolvable : ¬ (frames setting.levels).Solvable reboundStore := by
  rintro ⟨Δ, σ, solved⟩
  have equal := ((solves_raw (S := setting) σ reboundEquation).mp (solved reboundEquation List.mem_cons_self)).2
  have typeCode : reboundEquation.1.1.code = .pi (.var (2 : Fin 3)) (.pi (.var 2) u0) := reboundType_code
  rw [typeCode] at equal
  have equal' : Equal setting.R Δ.raw
      (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0)))
        (.var (Fin.succ 0))) (.var 0))))
      (.lam (.lam (.pi (Presentation.rename wk (Presentation.rename wk (σ.substitution 2)))
        (.pi (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1))))
          (.app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
            (Presentation.rename wk (σ.substitution 0))))) (.var (Fin.succ 0))) (.var 0))))))
      (.pi (σ.substitution 2) (.pi (Presentation.rename wk (σ.substitution 1)) u0)) := equal
  have formed := Δ.formed
  obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed equal' formed).1 formed)
  have formed1 : CtxFormed setting.R (.snoc Δ.raw (σ.substitution 2)) := formed.snoc ⟨u, hu, tA⟩
  have inner := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed equal'
  obtain ⟨⟨v, hv, tB⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed inner formed1).1 formed1)
  have formed2 : CtxFormed setting.R
      (.snoc (.snoc Δ.raw (σ.substitution 2)) (Presentation.rename wk (σ.substitution 1))) :=
    formed1.snoc ⟨v, hv, tB⟩
  have bodies := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed1 inner
  have first : CtxRen
      (.snoc (.snoc (.snoc (.snoc Δ.raw (σ.substitution 2)) (Presentation.rename wk (σ.substitution 1)))
        (Presentation.rename wk (Presentation.rename wk (σ.substitution 2))))
        (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))))
      (.snoc (.snoc (.snoc Δ.raw (σ.substitution 2)) (Presentation.rename wk (σ.substitution 1)))
        (Presentation.rename wk (Presentation.rename wk (σ.substitution 1))))
      (liftRen (mergeAt (Fin.succ 0))) := by
    have lifted := CtxRen.snoc
      (mergeAt_ctxRen (.snoc (.snoc Δ.raw (σ.substitution 2)) (Presentation.rename wk (σ.substitution 1)))
        (Fin.succ 0))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1))))
    rw [rename_mergeAt_wk] at lifted
    exact lifted
  have compatible := CtxRen.comp first
    (mergeAt_ctxRen (.snoc (.snoc Δ.raw (σ.substitution 2)) (Presentation.rename wk (σ.substitution 1))) 0)
  refine renamed_occurrence_not_typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (T := binder true (Presentation.rename wk (Presentation.rename wk (σ.substitution 2)))
      (binder true (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1))))
        (.app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
          (Presentation.rename wk (σ.substitution 0))))) (.var (Fin.succ 0))) (.var 0))))
    (.codomain true (.codomain true (.here _ _))) compatible ?back formed2
    ⟨_, .sort _, (Equal.typed bodies formed2).2⟩ ⟨_, .sort _, bodies⟩
  rw [← rename_comp]
  show Presentation.rename (mergeAt 0)
      (Tm.app (Tm.app (Presentation.rename (liftRen (mergeAt (Fin.succ 0)))
          (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
            (σ.substitution 0))))))
        (.var (liftRen (mergeAt (Fin.succ 0)) (Fin.succ 0)))) (.var (liftRen (mergeAt (Fin.succ 0)) 0))) =
    Tm.app (Tm.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var (Fin.succ 0)))
      (.var 0)
  rw [rename_liftRen_wk, rename_mergeAt_wk]
  show Tm.app (Tm.app (Presentation.rename (mergeAt 0)
        (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 0)))))
      (.var (mergeAt 0 (liftRen (mergeAt (Fin.succ 0)) (Fin.succ 0)))))
      (.var (mergeAt 0 (liftRen (mergeAt (Fin.succ 0)) 0))) = _
  rw [rename_mergeAt_wk]
  rfl

/-- **The family below is stuck on the store** at every budget and number of rounds at which its compiled run reads
`stuck`. -/
theorem rebound_stuck_below_of_ending {fuel rounds : Nat}
    (read : endingTop fuel rounds ctxABQ reboundStore = .stuck) :
    InFragmentStore reboundStore ∧ ¬ (frames setting.levels).Solvable reboundStore ∧
      isStuck (run (elimSigmaTower.solver fuel) reboundStore rounds) = true :=
  ⟨rebound_in_fragment, rebound_unsolvable, stuck_of_endingTop read⟩

/-- **The family with the occurs rule at a bound variable refutes the store** wherever its compiled run reads
`refuted`. -/
theorem rebound_refuted_of_ending {fuel rounds : Nat}
    (read : endingBound fuel rounds ctxABQ reboundStore = .refuted) :
    InFragmentStore reboundStore ∧ ¬ (frames setting.levels).Solvable reboundStore ∧
      endingOf (run (boundTower.solver fuel) reboundStore rounds) = .refuted :=
  ⟨rebound_in_fragment, rebound_unsolvable, (endingBound_run fuel rounds reboundStore).trans read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
