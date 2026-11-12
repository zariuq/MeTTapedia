import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesOccurs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepBound

/-!
# The occurs rule at a bound variable on the witnesses of the fourth stuck family

**The witness.** On `λ x. Q x ≐ λ x. Π (y : A). Q y` the family with the occurs rule at a bound variable refutes
wherever its compiled run reads `refuted` (`boundOccurs_refuted_of_ending`); the compiled run reads `refuted` at
budgets 16, 64 and 256.

**The unknown at another outer variable** (`otherOuterStore`):

  `λ x y. Q y ≐ λ x y. Π (z : A). Q x`  at  `Π (x : A) (y : A). U0`.

The store is in the fragment (`otherOuter_in_fragment`) and has no solution (`otherOuter_unsolvable`): both `Q y` and
`Q x` are images of `Q w` over one variable `w` (`ContextualDependentOccursRenamed.instances_not_typeEq`). The family
below is stuck on it wherever its compiled run reads `stuck` (`otherOuter_stuck_below_of_ending`), and the family
with the occurs rule at a bound variable refutes it wherever its compiled run reads `refuted`
(`otherOuter_refuted_of_ending`): the rule merges `x` and `y`. The compiled runs read `stuck` and `refuted` at
budgets 16 and 64. Those readings are evaluations, not theorems.

**Controls of the reader.** The rule reads both equations (`boundOccurs_read`, `otherOuter_read`) and does not read
`λ x. Q x ≐ λ x. Π (y : A). A`, which the solver commits (`constant_not_read`).
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

/-! ## The witness -/

/-- **The family with the occurs rule at a bound variable refutes the witness** wherever its compiled run reads
`refuted`: the store is in the fragment and has no solution, and the run ends refuted. -/
theorem boundOccurs_refuted_of_ending {fuel rounds : Nat}
    (read : endingBound fuel rounds ctxAQ boundOccursStore = .refuted) :
    InFragmentStore boundOccursStore ∧ ¬ (frames setting.levels).Solvable boundOccursStore ∧
      endingOf (run (boundTower.solver fuel) boundOccursStore rounds) = .refuted :=
  ⟨boundOccurs_in_fragment, boundOccurs_unsolvable, (endingBound_run fuel rounds boundOccursStore).trans read⟩

/-- The rule reads the equation of the witness. -/
theorem boundOccurs_read : (boundShape (S := setting) boundOccursEquation).isSome = true := by decide +kernel

/-! ## The unknown at another outer variable -/

/-- `Π (x : A) (y : A). U0`, over `A Q`. -/
def otherOuterType : TypeOver ctxAQ := formIn ctxAQ (.pi (.var 1) (.pi (.var 2) u0)) (by decide +kernel)

theorem otherOuterType_code : otherOuterType.code = .pi (.var (1 : Fin 2)) (.pi (.var 2) u0) := by decide +kernel

/-- `λ x y. Q y ≐ λ x y. Π (z : A). Q x`. -/
def otherOuterEquation : Equation (TotalTerm ctxAQ) :=
  (termIn ctxAQ otherOuterType (.lam (.lam (.app (.var 2) (.var 0)))) (by decide +kernel),
    termIn ctxAQ otherOuterType (.lam (.lam (.pi (.var 3) (.app (.var 3) (.var 2))))) (by decide +kernel))
def otherOuterStore : EquationStore (TotalTerm ctxAQ) := [otherOuterEquation]

/-- The raw problem of the sweep. -/
def otherOuterProblem : Problem :=
  { unknowns := [.u0, .pi (.var 0) .u0],
    equations := [(.pi (.var 1) (.pi (.var 2) .u0), .lam (.lam (.app (.var 2) (.var 0))),
      .lam (.lam (.pi (.var 3) (.app (.var 3) (.var 2)))))] }

theorem otherOuter_in_fragment : InFragmentStore otherOuterStore := storeInside_sound (by decide +kernel)

/-- Weakening twice, through a lifted weakening. -/
theorem liftRen_wk_wk {n : Nat} : (fun index : Fin n => liftRen wk (wk index)) = fun index => wk (wk index) := by
  funext index
  simp [liftRen, wk]

/-- **The store has no solution.** Under the two abstractions a solution would make `Q y` equal to
`Π (z : A). Q x`; both `Q y` and `Q x` are images of `Q w` over one variable. -/
theorem otherOuter_unsolvable : ¬ (frames setting.levels).Solvable otherOuterStore := by
  rintro ⟨Δ, σ, solved⟩
  have equal :=
    ((solves_raw (S := setting) σ otherOuterEquation).mp (solved otherOuterEquation List.mem_cons_self)).2
  have typeCode : otherOuterEquation.1.1.code = .pi (.var (1 : Fin 2)) (.pi (.var 2) u0) := otherOuterType_code
  rw [typeCode] at equal
  have equal' : Equal setting.R Δ.raw
      (.lam (.lam (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var 0))))
      (.lam (.lam (.pi (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))))
          (.var (Fin.succ (Fin.succ 0)))))))
      (.pi (σ.substitution 1) (.pi (Presentation.rename wk (σ.substitution 1)) u0)) := equal
  have formed := Δ.formed
  obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed equal' formed).1 formed)
  have formed1 : CtxFormed setting.R (.snoc Δ.raw (σ.substitution 1)) := formed.snoc ⟨u, hu, tA⟩
  have inner := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed equal'
  obtain ⟨⟨v, hv, tA1⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed inner formed1).1 formed1)
  have formed2 : CtxFormed setting.R
      (.snoc (.snoc Δ.raw (σ.substitution 1)) (Presentation.rename wk (σ.substitution 1))) :=
    formed1.snoc ⟨v, hv, tA1⟩
  have bodies := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed1 inner
  obtain ⟨typedV, typedT⟩ := Equal.typed bodies formed2
  have isV : IsType setting.R
      (.snoc (.snoc Δ.raw (σ.substitution 1)) (Ctx.lookup (.snoc Δ.raw (σ.substitution 1)) 0))
      (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var 0)) :=
    ⟨_, .sort _, typedV⟩
  have isP : IsType setting.R (.snoc Δ.raw (σ.substitution 1))
      (.app (Presentation.rename wk (σ.substitution 0)) (.var 0)) := by
    have renamed := isV.rename (mergeAt_ctxRen (.snoc Δ.raw (σ.substitution 1)) 0)
    have same : Presentation.rename (mergeAt (0 : Fin (Δ.arity + 1)))
        (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var 0)) =
        .app (Presentation.rename wk (σ.substitution 0)) (.var 0) := by
      show Tm.app (Presentation.rename (mergeAt 0) (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))))
        (.var (mergeAt 0 0)) = _
      rw [rename_mergeAt_wk, mergeAt_zero]
    rw [same] at renamed
    exact renamed
  refine instances_not_typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (T := binder true (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))))
        (.var (Fin.succ (Fin.succ 0)))))
    (.codomain true (.here _ _))
    (P := .app (Presentation.rename wk (σ.substitution 0)) (.var 0))
    (CtxRen.snoc (CtxRen.wk Δ.raw (σ.substitution 1)) (σ.substitution 1))
    (CtxRen.comp (CtxRen.wk (.snoc Δ.raw (σ.substitution 1)) (Presentation.rename wk (σ.substitution 1)))
      (CtxRen.wk _ (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))))
    ?first ?second formed1 isP formed2 ⟨_, .sort _, typedT⟩ ⟨_, .sort _, bodies⟩
  case first =>
    show Tm.app (Presentation.rename (liftRen wk) (Presentation.rename wk (σ.substitution 0))) (.var (liftRen wk 0)) =
      Tm.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var 0)
    rw [rename_comp, rename_comp, liftRen_wk_wk]
    rfl
  case second =>
    show Tm.app (Presentation.rename (fun index => wk (wk index)) (Presentation.rename wk (σ.substitution 0)))
        (.var (wk (wk 0))) =
      Tm.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))))
        (.var (Fin.succ (Fin.succ 0)))
    rw [rename_comp, rename_comp, rename_comp]
    rfl

/-- **The family below is stuck on the store** at every budget and number of rounds at which its compiled run reads
`stuck`: a store of the fragment without solution that it neither commits nor refutes. -/
theorem otherOuter_stuck_below_of_ending {fuel rounds : Nat}
    (read : endingTop fuel rounds ctxAQ otherOuterStore = .stuck) :
    InFragmentStore otherOuterStore ∧ ¬ (frames setting.levels).Solvable otherOuterStore ∧
      isStuck (run (elimSigmaTower.solver fuel) otherOuterStore rounds) = true :=
  ⟨otherOuter_in_fragment, otherOuter_unsolvable, stuck_of_endingTop read⟩

/-- **The family with the occurs rule at a bound variable refutes the store** wherever its compiled run reads
`refuted`. -/
theorem otherOuter_refuted_of_ending {fuel rounds : Nat}
    (read : endingBound fuel rounds ctxAQ otherOuterStore = .refuted) :
    InFragmentStore otherOuterStore ∧ ¬ (frames setting.levels).Solvable otherOuterStore ∧
      endingOf (run (boundTower.solver fuel) otherOuterStore rounds) = .refuted :=
  ⟨otherOuter_in_fragment, otherOuter_unsolvable, (endingBound_run fuel rounds otherOuterStore).trans read⟩

/-- The rule reads the equation, after merging the two abstractions. -/
theorem otherOuter_read : (boundShape (S := setting) otherOuterEquation).isSome = true := by decide +kernel

/-! ## Control: an equation with a solution is not read -/

/-- `λ x. Q x ≐ λ x. Π (y : A). A`: solved by `Q := λ x. A → A`. -/
def constantEquation : Equation (TotalTerm ctxAQ) :=
  (termIn ctxAQ boundOccursType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxAQ boundOccursType (.lam (.pi (.var 2) (.var 3))) (by decide +kernel))

/-- The rule does not read it, in either orientation. -/
theorem constant_not_read : (boundShape (S := setting) constantEquation).isSome = false ∧
    (boundShape (S := setting) (ContextualDependentEtaExpansion.swap (S := setting) constantEquation)).isSome =
      false :=
  ⟨by decide +kernel, by decide +kernel⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
