import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnesses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepElimSigma
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursRenamed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFullUnder

/-!
# A stuck family that asks for a refutation: the unknown of a pattern under a binder of the other side

The sweep over `A : U0, Q : A → U0` finds stores of the dynamic pattern fragment on which the family above the mixed family is stuck
and which have **no solution**. The witness (`boundOccursStore`):

  `λ x. Q x ≐ λ x. Π (y : A). Q y`  at  `Π (x : A). U0`.

The right side holds the unknown `Q` of the pattern `Q x` at the variable `y` that its own Π binds. The occurs
checks of the tower look for the weakened left side `Q x` in the right side; `Q y` is not it, so no reader fires.

* `boundOccurs_in_fragment`: the store is in the fragment (the decided membership test).
* `boundOccurs_unsolvable`: the store has no solution, by the occurs check for a renamed occurrence
  (`ContextualDependentOccursRenamed.codomain_pattern_not_typeEq`): sending `y` to `x` carries `Q y` back to `Q x`.
* `boundOccurs_gap_of_ending`: at every budget and number of rounds at which the compiled run of the family above the mixed family reads
  `stuck`, the store is in the fragment, has no solution, and the family above the mixed family is stuck on it. The compiled run reads
  `stuck` at budgets 16 and 64; that reading is an evaluation, not a theorem.

**Controls.** With the unknown at the outer variable, `λ x. Q x ≐ λ x. Π (y : A). Q x`, the store is in the
fragment and the tower's occurs check reads it: the compiled run reads `refuted`, and then the store has no solution
(`outer_unsolvable_of_ending`).
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

/-- `A → U0`, over `A`. -/
def familyOverA : TypeOver ctxA := formIn ctxA (.pi (.var 0) u0) (by decide +kernel)

/-- `A : U0, Q : A → U0`. -/
abbrev ctxAQ := extend ctxA familyOverA

/-- `Π (x : A). U0`, over `A Q`. -/
def boundOccursType : TypeOver ctxAQ := formIn ctxAQ (.pi (.var 1) u0) (by decide +kernel)

theorem boundOccursType_code : boundOccursType.code = .pi (.var (1 : Fin 2)) u0 := by decide +kernel

/-- `λ x. Q x ≐ λ x. Π (y : A). Q y`. -/
def boundOccursEquation : Equation (TotalTerm ctxAQ) :=
  (termIn ctxAQ boundOccursType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxAQ boundOccursType (.lam (.pi (.var 2) (.app (.var 2) (.var 0)))) (by decide +kernel))
def boundOccursStore : EquationStore (TotalTerm ctxAQ) := [boundOccursEquation]

/-- The raw problem of the sweep. -/
def boundOccursProblem : Problem :=
  { unknowns := [.u0, .pi (.var 0) .u0],
    equations := [(.pi (.var 1) .u0, .lam (.app (.var 1) (.var 0)), .lam (.pi (.var 2) (.app (.var 2) (.var 0))))] }

theorem boundOccurs_in_fragment : InFragmentStore boundOccursStore := storeInside_sound (by decide +kernel)

/-- **The store has no solution.** Under the abstraction a solution would make `Q x` equal to `Π (y : A). Q y`,
whose codomain is carried back to `Q x` by sending `y` to `x`. -/
theorem boundOccurs_unsolvable : ¬ (frames setting.levels).Solvable boundOccursStore := by
  rintro ⟨Δ, σ, solved⟩
  have equal := ((solves_raw (S := setting) σ boundOccursEquation).mp (solved boundOccursEquation List.mem_cons_self)).2
  have typeCode : boundOccursEquation.1.1.code = .pi (.var (1 : Fin 2)) u0 := boundOccursType_code
  rw [typeCode] at equal
  have equal' : Equal setting.R Δ.raw (.lam (.app (Presentation.rename wk (σ.substitution 0)) (.var 0)))
      (.lam (.pi (Presentation.rename wk (σ.substitution 1))
        (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var 0))))
      (.pi (σ.substitution 1) u0) := equal
  have formed := Δ.formed
  obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed equal' formed).1 formed)
  have formed1 : CtxFormed setting.R (.snoc Δ.raw (σ.substitution 1)) := formed.snoc ⟨u, hu, tA⟩
  have bodies := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed equal'
  have typedRight := (Equal.typed bodies formed1).2
  refine codomain_pattern_not_typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete true formed1
    (0 : Fin (Δ.arity + 1)) (D := Presentation.rename wk (σ.substitution 1))
    (V := .app (Presentation.rename wk (σ.substitution 0)) (.var 0))
    (B := .app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var 0)) rfl ?_
    ⟨_, .sort _, typedRight⟩ ⟨_, .sort _, bodies⟩
  show Tm.app (Presentation.rename (mergeAt 0) (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))))
    (.var (mergeAt 0 0)) = _
  rw [rename_mergeAt_wk, mergeAt_zero]

/-- **The unknown of a pattern under a binder of the other side**: the store is in the fragment and has no solution,
and the family above the mixed family is stuck on it at every budget and number of rounds at which the compiled run reads `stuck`. -/
theorem boundOccurs_gap_of_ending {fuel rounds : Nat} (read : endingTop fuel rounds ctxAQ boundOccursStore = .stuck) :
    InFragmentStore boundOccursStore ∧ ¬ (frames setting.levels).Solvable boundOccursStore ∧
      isStuck (run (elimSigmaTower.solver fuel) boundOccursStore rounds) = true :=
  ⟨boundOccurs_in_fragment, boundOccurs_unsolvable, stuck_of_endingTop read⟩

/-! ## Control: the unknown at the outer variable is read by the tower's occurs check -/

/-- `λ x. Q x ≐ λ x. Π (y : A). Q x`. -/
def outerEquation : Equation (TotalTerm ctxAQ) :=
  (termIn ctxAQ boundOccursType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxAQ boundOccursType (.lam (.pi (.var 2) (.app (.var 2) (.var 1)))) (by decide +kernel))
def outerStore : EquationStore (TotalTerm ctxAQ) := [outerEquation]

theorem outer_in_fragment : InFragmentStore outerStore := storeInside_sound (by decide +kernel)

/-- A run of the family above the mixed family that the compiled run reads as refuted certifies that the store has no solution. -/
theorem unsolvable_of_endingTop {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : endingTop fuel rounds Γ store = .refuted) : ¬ (frames setting.levels).Solvable store := by
  rw [← endingTop_run] at read
  cases outcome : run (elimSigmaTower.solver fuel) store rounds with
  | refuted absent => exact absent
  | solved _ _ => rw [outcome] at read; cases read
  | stuck _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- **The unknown at the outer variable**: the store is in the fragment, and has no solution wherever the compiled
run of the family above the mixed family reads `refuted`. -/
theorem outer_unsolvable_of_ending {fuel rounds : Nat} (read : endingTop fuel rounds ctxAQ outerStore = .refuted) :
    InFragmentStore outerStore ∧ ¬ (frames setting.levels).Solvable outerStore :=
  ⟨outer_in_fragment, unsolvable_of_endingTop read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
