import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SettlingStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativePrincipal

/-!
# Postponement: the cross store has a comprehension and no representing frame

Where the information of a firing has no principal answer, its comprehension still exists, but no
frame represents it, so syntactic typing cannot settle. The settling step then **postpones**: a third
outcome, not a refusal.

**Generic.** Initial solutions depend on a store only through its solutions
(`initialSolution_congr`). When the settler postpones, the settling step admits exactly what the
present step admits, with the same plan (`settling_admits_iff_of_postponed`). A firing whose rows
need the match, whose information is solvable and on which the settler postpones is `Postponed`:
not admitted (`Postponed.not_admitted`), and not refused for want of solutions.

**The cross store** (`λx. X x ≐ λx. Y x` over `X : U0 → U0, Y : U1 → U1`, solvable, with no
principal answer):
* its comprehension is not empty (`cross_comprehension_nonempty`) and is represented by no frame,
  not even up to agreement (`cross_not_representable`);
* it has no initial solution, so **every settler postpones on it** (`cross_postponed`);
* for every firing at the cross state that makes rows and adds no equation (`crossFiring`), every
  settler postpones (`crossFiring_postponed`), the settling step admits exactly what the present
  step admits (`crossFiring_settling_iff`), and a firing whose rows need the match is `Postponed`
  (`crossFiring_postponed_of_untyped`), with solvable information (`crossFiring_solvable`).

**The control** (`crossNeedsMatch_postponed`): the firing that makes `Y : U1 → U1` at `U0 → U0`. Its
row is not typed in the frame (`crossRow_untyped`: the domains `U1` and `U0` clash), and it is typed
at the solution `X := λx. x, Y := λz. z` (`crossRow_typed_at_identity`). So for every settler it is
postponed and not admitted, while a refusal would contradict that solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing Helpers)
open UnificationWithLevels (Agree InitialSolution)

section Generic

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-- **Initial solutions depend on a store only through its solutions.** -/
theorem initialSolution_congr {M Δ : Context rules} {I J : EquationStore (TotalTerm Δ)}
    (same : (frames levels).Equivalent I J) (σ : M ⟶ Δ) :
    InitialSolution (frames levels) I σ ↔ InitialSolution (frames levels) J σ := by
  constructor
  · intro initial
    exact ⟨(same M σ).mp initial.solves, fun b f solved => initial.factor b f ((same b f).mpr solved),
      initial.unique⟩
  · intro initial
    exact ⟨(same M σ).mpr initial.solves, fun b f solved => initial.factor b f ((same b f).mp solved),
      initial.unique⟩

variable {O : Type} [DecidableEq O] (settler : Settler levels)

omit [DecidableEq O] in
theorem plan_of_postponed {s : State rules O} {f : Firing levels s}
    (postponed : settler f.information = .postponed) :
    plan levels settler f = ⟨f.helpers.frame, 𝟙 _⟩ := by
  have along : (settler f.information).along = ⟨f.helpers.frame, 𝟙 f.helpers.frame⟩ := by
    rw [postponed]
    rfl
  unfold plan
  split
  · rfl
  · exact along

/-- **Where the settler postpones, the settling step admits what the present step admits.** -/
theorem settling_admits_iff_of_postponed {s : State rules O} {f : Firing levels s}
    (postponed : settler f.information = .postponed) :
    (settlingStep levels O settler).Admits f ↔ (DependentFull.step levels O).Admits f := by
  have identity := plan_of_postponed levels settler postponed
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(settledShapes_iff_of_plan levels settler identity).mp shapes, enabled, solvable, holds⟩
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(settledShapes_iff_of_plan levels settler identity).mpr shapes, enabled, solvable, holds⟩

/-- **Postponed**: the rows need the match, the information has solutions, and the settler
postpones. Neither admitted nor refused: settling waits for knowledge that makes an answer
principal. -/
def Postponed {s : State rules O} (f : Firing levels s) : Prop :=
  ¬ FrameTyped levels f ∧ settler f.information = .postponed ∧ (frames levels).Solvable f.information

/-- **A postponed firing is not admitted.** -/
theorem Postponed.not_admitted {s : State rules O} {f : Firing levels s}
    (postponed : Postponed levels settler f) : ¬ (settlingStep levels O settler).Admits f := by
  intro admitted
  exact postponed.1 ((settling_admits_iff_of_postponed levels settler postponed.2.1).mp admitted).1.2.2.2.2

end Generic

/-! ## The cross store -/

section Cross

open ContextualDependentSweep.Witnesses ContextualDependentDynamicFragment

/-- The package of the cross store: the cumulative tower. -/
abbrev crossSetting := ContextualDependentPatternFiring.Controls.setting

/-- **The cross store has no initial solution.** -/
theorem cross_no_initial (M : Context crossSetting.R) (σ : M ⟶ ctxCross) :
    ¬ InitialSolution (frames crossSetting.levels) crossStore σ :=
  fun initial => fragment_without_principal_answer.2.2 σ (principal_of_initial _ initial)

/-- **Every settler postpones on the cross store.** -/
theorem cross_postponed (settler : Settler crossSetting.levels) : settler crossStore = .postponed :=
  Verdict.eq_postponed _ cross_no_initial _

/-- **Its comprehension is not empty**: the store is solvable. -/
theorem cross_comprehension_nonempty : solutions crossSetting.levels crossStore ≠ ⊥ :=
  (solvable_iff_ne_bot _ _).mp fragment_without_principal_answer.2.1

/-- **No frame represents it, even up to agreement.** -/
theorem cross_not_representable (M : Context crossSetting.R) (σ : M ⟶ ctxCross) :
    solutions crossSetting.levels crossStore ≠ saturation crossSetting.levels (generated σ) :=
  fun same => fragment_without_principal_answer.2.2 σ ((principal_iff _ _ σ).mpr same)

/-- The state at the cross store: its frame, the cross equation as knowledge, no rows. -/
def crossState : State crossSetting.R Nat := ⟨ctxCross, crossStore, ∅, fun _ => crossEquation.1⟩

/-- A firing at the cross state that adds no equation and makes the given rows. -/
abbrev crossFiring (makes : List (Nat × Make ctxCross)) : Firing crossSetting.levels crossState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := makes
  tells := []
  guards := []
  queries := []

theorem crossFiring_information (makes : List (Nat × Make ctxCross)) :
    (crossFiring makes).information = crossStore := by
  have transported : (frames crossSetting.levels).applyStore (𝟙 ctxCross) crossStore = crossStore :=
    Frames.applyStore_id (X := frames crossSetting.levels) crossStore
  exact (List.append_nil _).trans ((List.append_nil _).trans ((List.append_nil _).trans transported))

theorem crossFiring_equivalent (makes : List (Nat × Make ctxCross)) :
    (frames crossSetting.levels).Equivalent (crossFiring makes).information crossStore := by
  intro Θ τ
  rw [crossFiring_information]

/-- **Every settler postpones on every such firing.** -/
theorem crossFiring_postponed (settler : Settler crossSetting.levels) (makes : List (Nat × Make ctxCross)) :
    settler (crossFiring makes).information = .postponed :=
  Verdict.eq_postponed _ (fun M σ initial => cross_no_initial M σ
    ((initialSolution_congr _ (crossFiring_equivalent makes) σ).mp initial)) _

/-- **The settling step admits there exactly what the present step admits.** -/
theorem crossFiring_settling_iff (settler : Settler crossSetting.levels) (makes : List (Nat × Make ctxCross)) :
    (settlingStep crossSetting.levels Nat settler).Admits (crossFiring makes) ↔
      (DependentFull.step crossSetting.levels Nat).Admits (crossFiring makes) :=
  settling_admits_iff_of_postponed _ settler (crossFiring_postponed settler makes)

/-- **Not refused for want of solutions**: the information is solvable. -/
theorem crossFiring_solvable (makes : List (Nat × Make ctxCross)) :
    (frames crossSetting.levels).Solvable (crossFiring makes).information :=
  (crossFiring_equivalent makes).solvable_iff.mpr fragment_without_principal_answer.2.1

/-- **A firing whose rows need the match is postponed**, for every settler. -/
theorem crossFiring_postponed_of_untyped (settler : Settler crossSetting.levels)
    {makes : List (Nat × Make ctxCross)} (untyped : ¬ FrameTyped crossSetting.levels (crossFiring makes)) :
    Postponed crossSetting.levels settler (crossFiring makes) :=
  ⟨untyped, crossFiring_postponed settler makes, crossFiring_solvable makes⟩

/-! ### A row that needs the match: `Y` at `U0 → U0` -/

/-- `U0 → U0`, as a formed type over the cross frame. -/
def smallOverCross : TypeOver ctxCross :=
  ⟨.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)), .sort (.max (.succ Tower.zero) (.succ Tower.zero)),
    .sort _, .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)⟩

/-- The row `Y`, made at `U0 → U0`. -/
def crossRow : Make ctxCross := ⟨smallOverCross, .var 0⟩

theorem cross_lookup_Y :
    Ctx.lookup ctxCross.raw 0 = .pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero))) := by
  decide +kernel

/-- **`Y` is not of type `U0 → U0` in the frame**: its type `U1 → U1` has a different domain. -/
theorem crossRow_untyped : ¬ crossRow.WellTyped := by
  intro typed
  have le : TypeLe crossSetting.R ctxCross.raw (Ctx.lookup ctxCross.raw 0) smallOverCross.code :=
    Typed.generation typed
  rw [cross_lookup_Y] at le
  obtain ⟨domains, -⟩ := TypeLe.pi_parts (S := crossSetting) TowerModel.facts le smallOverCross.isType
    ctxCross.formed
  have clash : ContextualDependentRigid.shapeClashes crossSetting.R
      (.head (.sort (.succ Tower.zero)) : Tower.Tm 0) (.head (.sort Tower.zero)) = true := by
    decide
  exact ContextualDependentRigid.not_typeEq_of_shapeClashes (S := crossSetting)
    ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete ctxCross.formed
    (ContextualDependentRigid.shapeClashes_subst crossSetting.R (fun i : Fin 0 => i.elim0) clash) domains

theorem crossIdentity_Y : crossIdentity.substitution 0 = .lam (.var 0) := by
  decide +kernel

/-- **... but it is at the solution `X := λx. x, Y := λz. z`**: a refusal would be wrong there. -/
theorem crossRow_typed_at_identity : (crossRow.reindex crossIdentity).WellTyped := by
  have lamTyped : Typed crossSetting.R Ctx.nil (.lam (.var 0))
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) :=
    .lamIntro (.piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _))
      (.sort _) (Derivable.var 0)
  have code : (crossIdentity.substitution 0 : Tower.Tm 0) = .lam (.var 0) := crossIdentity_Y
  show Typed crossSetting.R Ctx.nil (crossIdentity.substitution 0)
    (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
  rw [code]
  exact lamTyped

/-- The firing at the cross state that makes `Y` at `U0 → U0`. -/
abbrev crossNeedsMatch : Firing crossSetting.levels crossState := crossFiring [(0, crossRow)]

theorem crossNeedsMatch_untyped : ¬ FrameTyped crossSetting.levels crossNeedsMatch :=
  fun typed => crossRow_untyped (typed (0, crossRow) (List.mem_singleton_self _))

/-- **The control**: for every settler, the firing is postponed: not admitted, its information
solvable, and its row typed at a solution, so neither admission nor refusal is justified. -/
theorem crossNeedsMatch_postponed (settler : Settler crossSetting.levels) :
    Postponed crossSetting.levels settler crossNeedsMatch ∧
      ¬ (settlingStep crossSetting.levels Nat settler).Admits crossNeedsMatch ∧
      (crossRow.reindex crossIdentity).WellTyped :=
  ⟨crossFiring_postponed_of_untyped settler crossNeedsMatch_untyped,
    (crossFiring_postponed_of_untyped settler crossNeedsMatch_untyped).not_admitted,
    crossRow_typed_at_identity⟩

end Cross

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.initialSolution_congr
#print axioms NativeTypesOnTheStep.settling_admits_iff_of_postponed
#print axioms NativeTypesOnTheStep.Postponed.not_admitted
#print axioms NativeTypesOnTheStep.cross_no_initial
#print axioms NativeTypesOnTheStep.cross_postponed
#print axioms NativeTypesOnTheStep.cross_comprehension_nonempty
#print axioms NativeTypesOnTheStep.cross_not_representable
#print axioms NativeTypesOnTheStep.crossFiring_postponed
#print axioms NativeTypesOnTheStep.crossFiring_settling_iff
#print axioms NativeTypesOnTheStep.crossFiring_solvable
#print axioms NativeTypesOnTheStep.crossFiring_postponed_of_untyped
#print axioms NativeTypesOnTheStep.crossRow_untyped
#print axioms NativeTypesOnTheStep.crossRow_typed_at_identity
#print axioms NativeTypesOnTheStep.crossNeedsMatch_postponed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
