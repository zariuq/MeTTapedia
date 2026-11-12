import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesOccursOuter

/-!
# The edge of the occurs rule at a bound variable

**A codomain passed without merging** (`edgeStore`), over `A : U0, Q : A → U0, R : A → U0`:

  `λ x. Q x ≐ λ x. Π (w : R x). Π (y : A). Q y`  at  `Π (x : A). U0`.

The right side holds the unknown `Q` of the pattern at its bound variable `y`, below a codomain whose domain `R x`
is the type of no variable. The rule passes that codomain with the pattern weakened, and reads the equation
(`edge_read`). The store is in the fragment (`edge_in_fragment`) and has no solution (`edge_unsolvable`, proved
apart from the rule: `Q x` and `Q y` are images of one type under two renamings of contexts). The family below is
stuck on it wherever its compiled run reads `stuck` (`edge_stuck_below_of_ending`) and the family with the rule
refutes it wherever its compiled run reads `refuted` (`edge_refuted_of_ending`); the compiled runs read so at budgets
16 and 64.

**Two abstractions of one type that are not consecutive** (`apartStore`), over `A : U0, Q : A → U0`:

  `λ x w y. Q y ≐ λ x w y. Π (z : A). Q x`  at  `Π (x : A) (w : U0) (y : A). U0`.

The rule merges `y` into `x` past `w`, and reads the equation (`apart_read`). The store is in the fragment
(`apart_in_fragment`) and has no solution (`apart_unsolvable`, proved apart from the rule: with `y` sent to `x` the
right side holds the left side weakened). The family below is stuck on it wherever its compiled run reads `stuck`
(`apart_stuck_below_of_ending`) and the family with the rule refutes it wherever its compiled run reads `refuted`
(`apart_refuted_of_ending`).

The readings of the compiled runs are evaluations, not theorems.
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

/-! ## A codomain passed without merging -/

/-- `A → U0`, over `A Q`. -/
def familyOverAQ : TypeOver ctxAQ := formIn ctxAQ (.pi (.var 1) u0) (by decide +kernel)

/-- `A : U0, Q : A → U0, R : A → U0`. -/
abbrev ctxAQR := extend ctxAQ familyOverAQ

/-- `Π (x : A). U0`, over `A Q R`. -/
def edgeType : TypeOver ctxAQR := formIn ctxAQR (.pi (.var 2) u0) (by decide +kernel)

theorem edgeType_code : edgeType.code = .pi (.var (2 : Fin 3)) u0 := by decide +kernel

/-- `λ x. Q x ≐ λ x. Π (w : R x). Π (y : A). Q y`. -/
def edgeEquation : Equation (TotalTerm ctxAQR) :=
  (termIn ctxAQR edgeType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxAQR edgeType
      (.lam (.pi (.app (.var 1) (.var 0)) (.pi (.var 4) (.app (.var 4) (.var 0))))) (by decide +kernel))
def edgeStore : EquationStore (TotalTerm ctxAQR) := [edgeEquation]

/-- The raw problem. -/
def edgeProblem : Problem :=
  { unknowns := [.u0, .pi (.var 0) .u0, .pi (.var 1) .u0],
    equations := [(.pi (.var 2) .u0, .lam (.app (.var 2) (.var 0)),
      .lam (.pi (.app (.var 1) (.var 0)) (.pi (.var 4) (.app (.var 4) (.var 0)))))] }

theorem edge_in_fragment : InFragmentStore edgeStore := storeInside_sound (by decide +kernel)

/-- The rule reads the equation: it passes the first codomain with the pattern weakened. -/
theorem edge_read : (boundShape (S := setting) edgeEquation).isSome = true := by decide +kernel

/-- Weakening three times, through a lifted double weakening. -/
theorem liftRen_wk_wk_wk {n : Nat} :
    (fun index : Fin n => liftRen (fun prior : Fin n => wk (wk prior)) (wk index)) =
      fun index => wk (wk (wk index)) := by
  funext index
  simp [liftRen, wk]

/-- **The store has no solution.** Under the abstraction a solution would make `Q x` equal to
`Π (w : R x). Π (y : A). Q y`; `Q y` is the image of `Q x` under the renaming that sends `x` to `y`. -/
theorem edge_unsolvable : ¬ (frames setting.levels).Solvable edgeStore := by
  rintro ⟨Δ, σ, solved⟩
  have equal := ((solves_raw (S := setting) σ edgeEquation).mp (solved edgeEquation List.mem_cons_self)).2
  have typeCode : edgeEquation.1.1.code = .pi (.var (2 : Fin 3)) u0 := edgeType_code
  rw [typeCode] at equal
  have equal' : Equal setting.R Δ.raw
      (.lam (.app (Presentation.rename wk (σ.substitution 1)) (.var 0)))
      (.lam (.pi (.app (Presentation.rename wk (σ.substitution 0)) (.var 0))
        (.pi (Presentation.rename wk (Presentation.rename wk (σ.substitution 2)))
          (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1))))
            (.var 0)))))
      (.pi (σ.substitution 2) u0) := equal
  have formed := Δ.formed
  obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed equal' formed).1 formed)
  have formed1 : CtxFormed setting.R (.snoc Δ.raw (σ.substitution 2)) := formed.snoc ⟨u, hu, tA⟩
  have bodies := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed equal'
  obtain ⟨typedV, typedT⟩ := Equal.typed bodies formed1
  have compatible' : CtxRen (.snoc Δ.raw (σ.substitution 2))
      (.snoc (.snoc (.snoc Δ.raw (σ.substitution 2)) (.app (Presentation.rename wk (σ.substitution 0)) (.var 0)))
        (Presentation.rename wk (Presentation.rename wk (σ.substitution 2))))
      (liftRen fun prior => wk (wk prior)) := by
    rw [rename_comp]
    exact CtxRen.snoc (CtxRen.comp (CtxRen.wk Δ.raw (σ.substitution 2)) (CtxRen.wk _ _)) (σ.substitution 2)
  refine instances_not_typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (T := binder true (.app (Presentation.rename wk (σ.substitution 0)) (.var 0))
      (binder true (Presentation.rename wk (Presentation.rename wk (σ.substitution 2)))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1))))
          (.var 0))))
    (.codomain true (.codomain true (.here _ _)))
    (P := .app (Presentation.rename wk (σ.substitution 1)) (.var 0))
    (CtxRen.id _) compatible' (rename_id _) ?second formed1 ⟨_, .sort _, typedV⟩ formed1
    ⟨_, .sort _, typedT⟩ ⟨_, .sort _, bodies⟩
  show Tm.app (Presentation.rename (liftRen fun prior => wk (wk prior)) (Presentation.rename wk (σ.substitution 1)))
      (.var (liftRen (fun prior => wk (wk prior)) 0)) =
    Tm.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))) (.var 0)
  rw [rename_comp, rename_comp, rename_comp, liftRen_wk_wk_wk]
  rfl

/-- **The family below is stuck on the store** at every budget and number of rounds at which its compiled run reads
`stuck`. -/
theorem edge_stuck_below_of_ending {fuel rounds : Nat} (read : endingTop fuel rounds ctxAQR edgeStore = .stuck) :
    InFragmentStore edgeStore ∧ ¬ (frames setting.levels).Solvable edgeStore ∧
      isStuck (run (elimSigmaTower.solver fuel) edgeStore rounds) = true :=
  ⟨edge_in_fragment, edge_unsolvable, stuck_of_endingTop read⟩

/-- **The family with the occurs rule at a bound variable refutes the store** wherever its compiled run reads
`refuted`. -/
theorem edge_refuted_of_ending {fuel rounds : Nat} (read : endingBound fuel rounds ctxAQR edgeStore = .refuted) :
    InFragmentStore edgeStore ∧ ¬ (frames setting.levels).Solvable edgeStore ∧
      endingOf (run (boundTower.solver fuel) edgeStore rounds) = .refuted :=
  ⟨edge_in_fragment, edge_unsolvable, (endingBound_run fuel rounds edgeStore).trans read⟩

/-! ## Two abstractions of one type that are not consecutive -/

/-- `Π (x : A) (w : U0) (y : A). U0`, over `A Q`. -/
def apartType : TypeOver ctxAQ := formIn ctxAQ (.pi (.var 1) (.pi u0 (.pi (.var 3) u0))) (by decide +kernel)

theorem apartType_code : apartType.code = .pi (.var (1 : Fin 2)) (.pi u0 (.pi (.var 3) u0)) := by decide +kernel

/-- `λ x w y. Q y ≐ λ x w y. Π (z : A). Q x`. -/
def apartEquation : Equation (TotalTerm ctxAQ) :=
  (termIn ctxAQ apartType (.lam (.lam (.lam (.app (.var 3) (.var 0))))) (by decide +kernel),
    termIn ctxAQ apartType (.lam (.lam (.lam (.pi (.var 4) (.app (.var 4) (.var 3)))))) (by decide +kernel))
def apartStore : EquationStore (TotalTerm ctxAQ) := [apartEquation]

/-- The raw problem. -/
def apartProblem : Problem :=
  { unknowns := [.u0, .pi (.var 0) .u0],
    equations := [(.pi (.var 1) (.pi .u0 (.pi (.var 3) .u0)), .lam (.lam (.lam (.app (.var 3) (.var 0)))),
      .lam (.lam (.lam (.pi (.var 4) (.app (.var 4) (.var 3))))))] }

theorem apart_in_fragment : InFragmentStore apartStore := storeInside_sound (by decide +kernel)

/-- The rule reads the equation: it merges `y` into `x` past `w`. -/
theorem apart_read : (boundShape (S := setting) apartEquation).isSome = true := by decide +kernel

/-- A lifted renaming after a weakening is the weakening after the renaming. -/
theorem rename_liftRen_wk {n m : Nat} (ρ : Ren n m) (term : Tower.Tm n) :
    Presentation.rename (liftRen ρ) (Presentation.rename wk term) =
      Presentation.rename wk (Presentation.rename ρ term) := by
  rw [rename_comp, rename_comp]
  rfl

/-- **The store has no solution.** Under the three abstractions a solution would make `Q y` equal to
`Π (z : A). Q x`; sending `y` to `x` makes it `Q x ≐ Π (z : A). Q x`, whose right side holds the left side
weakened. -/
theorem apart_unsolvable : ¬ (frames setting.levels).Solvable apartStore := by
  rintro ⟨Δ, σ, solved⟩
  have equal := ((solves_raw (S := setting) σ apartEquation).mp (solved apartEquation List.mem_cons_self)).2
  have typeCode : apartEquation.1.1.code = .pi (.var (1 : Fin 2)) (.pi u0 (.pi (.var 3) u0)) := apartType_code
  rw [typeCode] at equal
  have equal' : Equal setting.R Δ.raw
      (.lam (.lam (.lam (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (σ.substitution 0)))) (.var 0)))))
      (.lam (.lam (.lam (.pi (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
          (σ.substitution 1))))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
          (σ.substitution 0))))) (.var (Fin.succ (Fin.succ (Fin.succ 0)))))))))
      (.pi (σ.substitution 1) (.pi u0 (.pi (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))
        u0))) := equal
  have formed := Δ.formed
  obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed equal' formed).1 formed)
  have formed1 : CtxFormed setting.R (.snoc Δ.raw (σ.substitution 1)) := formed.snoc ⟨u, hu, tA⟩
  have inner1 := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed equal'
  obtain ⟨⟨v, hv, tU⟩, _⟩ := IsType.pi_parts (Typed.isType (Equal.typed inner1 formed1).1 formed1)
  have formed2 : CtxFormed setting.R (.snoc (.snoc Δ.raw (σ.substitution 1)) u0) := formed1.snoc ⟨v, hv, tU⟩
  have inner2 := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed1 inner1
  have bodies := ContextualDependentOccursFull.lam_equal_inv (S := setting) TowerModel.facts formed2 inner2
  have renamed := Equal.rename bodies
    (mergeAt_ctxRen (.snoc (.snoc Δ.raw (σ.substitution 1)) u0) (Fin.succ 0))
  have leftEq : Presentation.rename (mergeAt (Fin.succ (0 : Fin (Δ.arity + 1))))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 0)))) (.var 0)) =
      .app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var (Fin.succ 0)) := by
    show Tm.app (Presentation.rename (mergeAt (Fin.succ 0))
        (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 0)))))
      (.var (mergeAt (Fin.succ 0) 0)) = _
    rw [rename_mergeAt_wk, mergeAt_zero]
  have rightEq : Presentation.rename (mergeAt (Fin.succ (0 : Fin (Δ.arity + 1))))
      (.pi (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1))))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
          (σ.substitution 0))))) (.var (Fin.succ (Fin.succ (Fin.succ 0)))))) =
      .pi (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))
        (Presentation.rename wk
          (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))) (.var (Fin.succ 0)))) := by
    show Tm.pi (Presentation.rename (mergeAt (Fin.succ 0))
          (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))))
        (Tm.app (Presentation.rename (liftRen (mergeAt (Fin.succ 0)))
            (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
              (σ.substitution 0))))))
          (.var (liftRen (mergeAt (Fin.succ 0)) (Fin.succ (Fin.succ (Fin.succ 0)))))) =
      Tm.pi (Presentation.rename wk (Presentation.rename wk (σ.substitution 1)))
        (Tm.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (σ.substitution 0))))
          (.var (wk (Fin.succ 0))))
    rw [rename_mergeAt_wk, rename_liftRen_wk, rename_mergeAt_wk]
    rfl
  rw [leftEq, rightEq] at renamed
  exact codomain_pattern_not_typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete true formed2
    (Fin.succ 0) rfl (rename_mergeAt_wk _ _) ⟨_, .sort _, (Equal.typed renamed formed2).2⟩
    ⟨_, .sort _, renamed⟩

/-- **The family below is stuck on the store** at every budget and number of rounds at which its compiled run reads
`stuck`. -/
theorem apart_stuck_below_of_ending {fuel rounds : Nat} (read : endingTop fuel rounds ctxAQ apartStore = .stuck) :
    InFragmentStore apartStore ∧ ¬ (frames setting.levels).Solvable apartStore ∧
      isStuck (run (elimSigmaTower.solver fuel) apartStore rounds) = true :=
  ⟨apart_in_fragment, apart_unsolvable, stuck_of_endingTop read⟩

/-- **The family with the occurs rule at a bound variable refutes the store** wherever its compiled run reads
`refuted`. -/
theorem apart_refuted_of_ending {fuel rounds : Nat} (read : endingBound fuel rounds ctxAQ apartStore = .refuted) :
    InFragmentStore apartStore ∧ ¬ (frames setting.levels).Solvable apartStore ∧
      endingOf (run (boundTower.solver fuel) apartStore rounds) = .refuted :=
  ⟨apart_in_fragment, apart_unsolvable, (endingBound_run fuel rounds apartStore).trans read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
