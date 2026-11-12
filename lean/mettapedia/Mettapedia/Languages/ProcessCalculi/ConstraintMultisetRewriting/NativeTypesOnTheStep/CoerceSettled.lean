import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.MatchAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.Refinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjective

/-!
# The coerce firing: typed after its match, and settled

`ProgrammingOnTheStep.Refinement.coerceFiring` makes the helpers `x : X` and `g : Ground` over
`X : U0`, tells `(x : X) ≐ (g : Ground)`, and makes the row `8 : x` at `Ground`. The present step
refuses it (`coerce_refused`): in the frame `x` has the variable type `X`.

* **Typed after its match** (`coerce_typedAfterMatch`), and not in its frame
  (`coerce_not_typedInFrame`). The firing is admitted after the match (`coerce_admitsAfterMatch`).
* **Its information has an initial solution**: `toGround` (`X ↦ Ground, x ↦ p, g ↦ p` into
  `p : Ground`) is principal (`toGround_principal`): every solution `τ` agrees with its factor
  `p ↦ τ g` (`toGround_agrees`), by the told equation and the equality of the two codes of `X` at
  `U0` (`ContextualDependentUniverseInjective.equal_at_universe`). It is an epimorphism on terms
  (`toGround_epi`), hence initial (`toGround_initial`).
* **The settling step admits it** with the semantic settler (`coerce_settled`), where the present
  step refuses it (`coerce_separation`); the made row of the result has its declared type `Ground`
  (`coerce_result_type`).

**Controls.**
* Without its tell the same row is not typed after the match (`untold_not_typedAfterMatch`), and the
  firing is not admitted after the match (`untold_not_admittedAfterMatch`).
* The settler that never settles is the present step and refuses the coerce firing
  (`never_refuses_coerce`).
* A store with no solution types even `U0` at `Ground` after its match, vacuously
  (`vacuous_typedAfterMatch`), and admission after the match still refuses it, by solvability
  (`vacuous_refused`).
* A firing whose made row is typed in its frame (`refinedFiring`) is admitted by every settling step
  with the present step's result (`refined_settled`, `refined_settled_result`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Coerce

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.Refinement
open UnificationWithLevels (Agree InitialSolution EpiOnTerms)

/-! ## Typed after the match -/

/-- The made row of the coerce firing: `x` at `Ground`. -/
def coerceRow : Make triple := ⟨groundType _, (.var 1 : Tower.Tm 3)⟩

theorem coerceFiring_makes : coerceFiring.makes = [(8, coerceRow)] := rfl

/-- **The coerce row is typed after its match**: at every solution of the firing's information. -/
theorem coerce_typedAfterMatch : TypedAfterMatch setting.levels coerceFiring.information coerceRow :=
  (typedAfterMatch_iff setting.levels _ coerceRow).mpr fun _ τ solved => coerce_typed_at_solutions τ solved

/-- **It is not typed in its frame.** -/
theorem coerce_not_typedInFrame : ¬ TypedInFrame coerceRow :=
  fun typed => x_not_ground ((typedInFrame_iff coerceRow).mp typed)

/-- **The coerce firing is admitted after the match.** -/
theorem coerce_admitsAfterMatch : AdmitsAfterMatch setting.levels coerceFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff coerceFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => Finset.notMem_empty o inside⟩, coerce_solvable, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact coerce_typedAfterMatch
  · intro _ _ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-! ## The initial solution `toGround` -/

/-- The factor of a solution through `toGround`: `p` goes to the solution's value of `g`. -/
def throughGround {Θ : Context Tower.rules} (τ : Θ ⟶ triple) : Θ ⟶ point :=
  pair (toEmpty Θ) ⟨τ.substitution 0, τ.typed 0⟩

/-- **Every solution agrees with its factor through `toGround`.** -/
theorem toGround_agrees {Θ : Context Tower.rules} (τ : Θ ⟶ triple)
    (solved : (frames setting.levels).Models τ coerceFiring.information) :
    Agree (frames setting.levels) τ (throughGround τ ≫ toGround) := by
  obtain ⟨types, terms⟩ := (ContextualDependentTwins.solves_iff setting.levels τ (xRow, gRow)).mp
    (solved _ (List.mem_singleton_self _))
  have same : homTypedEquality Tower.rules τ (throughGround τ ≫ toGround) := by
    refine ⟨τ.typed, fun index => ?_⟩
    fin_cases index
    · exact .refl (τ.typed 0)
    · exact terms
    · exact ContextualDependentUniverseInjective.equal_at_universe (S := setting) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra rigid TowerModel.complete Θ.formed
        (groundType (empty Tower.rules)).universeWitness (τ.typed 2) (ground_typed Θ.raw) types
  exact fun t => act_equal_of_substEq setting.levels same t

/-- **`toGround` is a principal answer of the coerce firing's information.** -/
theorem toGround_principal : (frames setting.levels).Principal coerceFiring.information toGround :=
  ⟨toGround_solves, fun _ τ solved => ⟨throughGround τ, toGround_agrees τ solved⟩⟩

/-- **`toGround` is an epimorphism on terms**: two substitutions out of `p : Ground` that agree on
its image agree on `p`. -/
theorem toGround_epi : EpiOnTerms (frames setting.levels) toGround := by
  intro Θ g h agree
  have e := (agree gRow).2
  have same : homTypedEquality Tower.rules g h := by
    refine ⟨g.typed, fun index => ?_⟩
    fin_cases index
    exact e
  exact fun t => act_equal_of_substEq setting.levels same t

/-- **`toGround` is the initial solution.** -/
theorem toGround_initial : InitialSolution (frames setting.levels) coerceFiring.information toGround :=
  UnificationWithLevels.Principal.initial toGround_principal toGround_epi

/-! ## The settling step admits the coerce firing -/

/-- The coerce firing's made row is not typed in its frame. -/
theorem coerce_not_frameTyped : ¬ FrameTyped setting.levels coerceFiring :=
  fun typed => x_not_ground (typed (8, coerceRow) (List.mem_singleton_self _))

/-- **F1 on the step**: the settling step with the semantic settler admits the coerce firing. -/
theorem coerce_settled :
    (settlingStep setting.levels Nat (Settler.ideal setting.levels)).Admits coerceFiring :=
  ideal_admits_of_admitsAfterMatch setting.levels coerce_admitsAfterMatch toGround_initial

/-- **The separation**: settled, the coerce firing is admitted; on the present step it is refused. -/
theorem coerce_separation :
    (settlingStep setting.levels Nat (Settler.ideal setting.levels)).Admits coerceFiring ∧
      ¬ (step setting.levels Nat).Admits coerceFiring :=
  ⟨coerce_settled, coerce_refused⟩

/-- **The made row of the result has its declared type `Ground`.** -/
theorem coerce_result_type :
    (((settlingStep setting.levels Nat (Settler.ideal setting.levels)).result coerceFiring
      coerce_settled).label 8).1.code = ground := rfl

/-! ## Controls -/

/-- The coerce firing without its tell. -/
def untoldFiring : Firing setting.levels baseState where
  helpers := .cons xType (.cons (groundType _) (.nil _))
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(8, coerceRow)]
  tells := []
  guards := []
  queries := []

theorem untold_information : untoldFiring.information = [] := rfl

/-- **Control: without its tell, the row is not typed after the match.** -/
theorem untold_not_typedAfterMatch :
    ¬ TypedAfterMatch setting.levels untoldFiring.information coerceRow := by
  rw [untold_information]
  intro typed
  exact x_not_ground ((typedAfterMatch_nil_iff setting.levels coerceRow).mp typed)

/-- ... so the untold firing is not admitted after the match. -/
theorem untold_not_admittedAfterMatch : ¬ AdmitsAfterMatch setting.levels untoldFiring :=
  fun admitted => untold_not_typedAfterMatch (admitted.1.2.2.2.2 (8, coerceRow) (List.mem_singleton_self _))

/-- **Control: the settler that never settles is the present step, and refuses the coerce firing.** -/
theorem never_refuses_coerce :
    ¬ (settlingStep setting.levels Nat (Settler.never setting.levels)).Admits coerceFiring :=
  fun admitted => coerce_refused ((never_admits_iff setting.levels coerceFiring).mp admitted)

/-- The row `U0` at `Ground`, in the empty frame. -/
def vacuousRow : Make (empty Tower.rules) := ⟨groundType _, .head (.sort Tower.zero)⟩

/-- Make `U0` at `Ground` and tell the rigid clash `Ground ≐ U0`. -/
def vacuousFiring : Firing setting.levels emptyState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(1, vacuousRow)]
  tells := ContextualDependentWorklist.Controls.clash
  guards := []
  queries := []

/-- **Control: an unsolvable information types every row, vacuously**, even `U0` at `Ground`, which
no frame types. -/
theorem vacuous_typedAfterMatch :
    TypedAfterMatch setting.levels vacuousFiring.information vacuousRow ∧ ¬ vacuousRow.WellTyped :=
  ⟨typedAfterMatch_of_not_solvable setting.levels
      (fun solvable => ContextualDependentWorklist.Controls.clash_refuted solvable) _,
    fun typed => ContextualDependentClosedBoundary.Controls.ground_uninhabited typed⟩

/-- **... and admission after the match refuses it, by solvability.** -/
theorem vacuous_refused : ¬ AdmitsAfterMatch setting.levels vacuousFiring :=
  fun admitted => ContextualDependentWorklist.Controls.clash_refuted admitted.2.2.1

/-- **Positive control: a firing whose row is typed in its frame is admitted by every settling
step** ... -/
theorem refined_settled (settler : Settler setting.levels) :
    (settlingStep setting.levels Nat settler).Admits refinedFiring :=
  settling_admits_of_admits setting.levels settler refined_admitted

/-- ... **with the present step's result.** -/
theorem refined_settled_result (settler : Settler setting.levels) :
    (settlingStep setting.levels Nat settler).result refinedFiring (refined_settled settler) =
      (step setting.levels Nat).result refinedFiring refined_admitted :=
  settling_result_eq setting.levels settler refined_admitted

end NativeTypesOnTheStep.Coerce

#print axioms NativeTypesOnTheStep.Coerce.coerce_typedAfterMatch
#print axioms NativeTypesOnTheStep.Coerce.coerce_not_typedInFrame
#print axioms NativeTypesOnTheStep.Coerce.coerce_admitsAfterMatch
#print axioms NativeTypesOnTheStep.Coerce.toGround_agrees
#print axioms NativeTypesOnTheStep.Coerce.toGround_principal
#print axioms NativeTypesOnTheStep.Coerce.toGround_epi
#print axioms NativeTypesOnTheStep.Coerce.toGround_initial
#print axioms NativeTypesOnTheStep.Coerce.coerce_settled
#print axioms NativeTypesOnTheStep.Coerce.coerce_separation
#print axioms NativeTypesOnTheStep.Coerce.coerce_result_type
#print axioms NativeTypesOnTheStep.Coerce.untold_not_typedAfterMatch
#print axioms NativeTypesOnTheStep.Coerce.untold_not_admittedAfterMatch
#print axioms NativeTypesOnTheStep.Coerce.never_refuses_coerce
#print axioms NativeTypesOnTheStep.Coerce.vacuous_typedAfterMatch
#print axioms NativeTypesOnTheStep.Coerce.vacuous_refused
#print axioms NativeTypesOnTheStep.Coerce.refined_settled
#print axioms NativeTypesOnTheStep.Coerce.refined_settled_result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
