import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingCheckingMeta
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongControls

/-!
# Checking with metavariables: controls in the cumulative tower

The frame is `G : U0, g : G, x : Ground`: `G` is a metavariable type and `g` a metavariable of it.

* **Postponement, then a later solution.** Checking `g x ⇐ Ground` runs five admitted firings. The
  application firing tells `G ≐ Ground → Ground`, which cannot be decided while `G` is open: it
  fails at the identity solution (`residual_open`), and it is not refuted (`run_admitted`). Under
  the later solution `G ↦ Ground → Ground, g ↦ λy. y, x ↦ z` every residual holds, and the run
  gives the typing of the instance `(λy. y) z : Ground` (`postponed_then_solved`).
* **Postponement under a binder.** Checking `λy. g y ⇐ Ground → Ground` runs six admitted
  firings; inside the abstraction the application firing tells `G ≐ Ground → Ground` in the
  local context `y : Ground`, where it waits. Under the same solution the run gives the typing
  of `λy. (λz. z) y : Ground → Ground` (`binder_postponed_then_solved`).
* **Refuted once its residual is refuted.** If the knowledge already says `G ≐ Ground`, the same
  application firing is refused: its residual `G ≐ Ground → Ground` cannot hold with the
  knowledge (`refuted_by_knowledge`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingCheckingMetaControls

open _root_.CategoryTheory
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypingCheckingMeta TypingCheckingMeta.Kernel
open ContextualDependentEtaLong.Controls (setting ground arrow ground_typed ground_isType arrow_typed
  arrow_isType)

abbrev universe0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)

/-- The raw frame `G : U0, g : G, x : Ground`. -/
def frameRaw : Tower.Ctx 3 := .snoc (.snoc (.snoc .nil universe0) (.var 0)) ground

theorem frame_formed : CtxFormed setting.R frameRaw :=
  .snoc (.snoc (.snoc .nil ⟨_, .sort _, .headType (.sort Tower.zero)⟩) ⟨_, .sort _, Derivable.var 0⟩)
    (ground_isType _)

abbrev Θ : Context setting.R := ⟨3, frameRaw, frame_formed⟩

/-! ## The later solution -/

/-- The frame `z : Ground` of the solution. -/
abbrev solutionFrame : Context setting.R := ⟨1, .snoc .nil ground, .snoc .nil (ground_isType _)⟩

/-- `G ↦ Ground → Ground, g ↦ λy. y, x ↦ z`. -/
def solution : solutionFrame ⟶ Θ where
  substitution := consSub (.var 0) (consSub (.lam (.var 0)) (consSub arrow (fun k => k.elim0)))
  typed := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => k.elim0) i) i) i
    · exact Derivable.var 0
    · exact .lamIntro (arrow_typed _) (.sort _) (Derivable.var 0)
    · refine .cumul (arrow_typed _) ?_
      change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
      intro valuation
      simp [UniverseLevel.LevelExpr.eval]

/-- Every obligation in a list holds at the solution. -/
theorem solvable_at {Δ : Context setting.R} (σ : Δ ⟶ Θ) (ps : List (Obligation Θ))
    (holds : ∀ P ∈ ps, P.holds σ) :
    (obligationFrames setting).Solvable (a := Θ) (ps.map TypingCheckingMeta.tell) :=
  ⟨Δ, σ, (models_tells_iff σ ps).mpr holds⟩

theorem below_ground : (belowAt (Θ := Θ) .nil ground ground).holds solution :=
  IsType.below_refl (ground_isType _)

theorem typeEq_arrow : (typeEqAt (Θ := Θ) .nil (.var 2) arrow).holds solution :=
  IsType.refl (arrow_isType _)

/-! ## The run -/

/-- The root `g x ⇐ Ground`. -/
def root : Goal Θ := ⟨0, .nil, .check, .app (.var 1) (.var 0), ground⟩

def start : GoalState Θ Nat := ⟨fun _ => root, {0}, []⟩

/-- Switch to synthesis for the application. -/
def first : GoalFiring start :=
  switchFiring start 0 1 .nil (.app (.var 1) (.var 0)) ground ground rfl

theorem first_goal :
    first.after.goal 1 = ⟨0, .nil, .synth, .app (.var 1) (.var 0), inst0 (.var 0) ground⟩ := by
  simp [GoalFiring.after, first, switchFiring]
  rfl

/-- Synthesize the application, telling `G ≐ Ground → Ground`. -/
def second : GoalFiring first.after :=
  appFiring first.after 1 2 3 (by decide) .nil (.var 1) (.var 0) (.var 2) ground ground first_goal

theorem second_goal₂ :
    second.after.goal 2 = ⟨0, .nil, .synth, .var 1, Ctx.lookup (Tele.ctx Θ.raw .nil) 1⟩ := by
  simp [GoalFiring.after, second, appFiring]
  rfl

theorem second_goal₃ : second.after.goal 3 = ⟨0, .nil, .check, .var 0, ground⟩ := by
  simp [GoalFiring.after, second, appFiring]

/-- Synthesize `g : G`. -/
def third : GoalFiring second.after := varFiring second.after 2 .nil 1 second_goal₂

theorem third_goal : third.after.goal 3 = ⟨0, .nil, .check, .var 0, ground⟩ := by
  show (if (3 : Nat) ∈ third.made then third.premise 3 else second.after.goal 3) = _
  rw [if_neg (by simp [third, varFiring])]
  exact second_goal₃

/-- Switch to synthesis for the argument. -/
def fourth : GoalFiring third.after :=
  switchFiring third.after 3 4 .nil (.var 0) ground ground third_goal

theorem fourth_goal :
    fourth.after.goal 4 = ⟨0, .nil, .synth, .var 0, Ctx.lookup (Tele.ctx Θ.raw .nil) 0⟩ := by
  simp [GoalFiring.after, fourth, switchFiring]
  rfl

/-- Synthesize `x : Ground`. -/
def fifth : GoalFiring fourth.after := varFiring fourth.after 4 .nil 0 fourth_goal

/-- The residuals told by the run. -/
def residuals : List (Obligation Θ) :=
  [belowAt .nil ground ground, typeEqAt .nil (.var 2) (.pi ground ground), belowAt .nil ground ground]

theorem residuals_hold : ∀ P ∈ residuals, P.holds solution := by
  intro P member
  simp only [residuals, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact below_ground
  · exact typeEq_arrow
  · exact below_ground

theorem first_admitted : (metaGoalStep Θ Nat).Admits first := by
  refine ⟨List.nodup_singleton 1, ⟨?_, ?_, ?_, ?_, ?_⟩,
    solvable_at solution [belowAt .nil ground ground] (fun P member => ?_), fun _ _ _ => trivial⟩
  · simp [first, switchFiring, GoalFiring.selection, Selection.commit, start]
  · simp [first, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [first, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [first, switchFiring, GoalFiring.selection, Selection.commit, start]
  · simp [first, switchFiring, GoalFiring.selection, Selection.commit]
  · simp only [List.mem_singleton] at member
    subst member
    exact below_ground

theorem first_present : first.after.present = {1} := by decide

theorem second_admitted : (metaGoalStep Θ Nat).Admits second := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [second, appFiring, GoalFiring.selection, Selection.commit, first_present]
  · simp [second, appFiring, GoalFiring.selection, Selection.commit]
  · simp [second, appFiring, GoalFiring.selection, Selection.commit]
  · simp [second, appFiring, GoalFiring.selection, Selection.commit, first_present]
  · simp [second, appFiring, GoalFiring.selection, Selection.commit]
  · have : first.after.knowledge ++ second.residuals.map TypingCheckingMeta.tell =
        [belowAt .nil ground ground, typeEqAt .nil (.var 2) (.pi ground ground)].map
          TypingCheckingMeta.tell := rfl
    rw [this]
    refine solvable_at solution _ (fun P member => ?_)
    exact residuals_hold P (by simp only [residuals, List.mem_cons] at member ⊢; tauto)

theorem second_present : second.after.present = {2, 3} := by decide

theorem third_admitted : (metaGoalStep Θ Nat).Admits third := by
  refine ⟨List.nodup_nil, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [third, varFiring, GoalFiring.selection, Selection.commit, second_present]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]
  · have : second.after.knowledge ++ third.residuals.map TypingCheckingMeta.tell =
        [belowAt .nil ground ground, typeEqAt .nil (.var 2) (.pi ground ground)].map
          TypingCheckingMeta.tell := rfl
    rw [this]
    refine solvable_at solution _ (fun P member => ?_)
    exact residuals_hold P (by simp only [residuals, List.mem_cons] at member ⊢; tauto)

theorem third_present : third.after.present = {3} := by decide

theorem fourth_admitted : (metaGoalStep Θ Nat).Admits fourth := by
  refine ⟨List.nodup_singleton 4, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [fourth, switchFiring, GoalFiring.selection, Selection.commit, third_present]
  · simp [fourth, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [fourth, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [fourth, switchFiring, GoalFiring.selection, Selection.commit, third_present]
  · simp [fourth, switchFiring, GoalFiring.selection, Selection.commit]
  · have : third.after.knowledge ++ fourth.residuals.map TypingCheckingMeta.tell =
        residuals.map TypingCheckingMeta.tell := rfl
    rw [this]
    exact solvable_at solution _ residuals_hold

theorem fourth_present : fourth.after.present = {4} := by decide

theorem fifth_admitted : (metaGoalStep Θ Nat).Admits fifth := by
  refine ⟨List.nodup_nil, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [fifth, varFiring, GoalFiring.selection, Selection.commit, fourth_present]
  · simp [fifth, varFiring, GoalFiring.selection, Selection.commit]
  · simp [fifth, varFiring, GoalFiring.selection, Selection.commit]
  · simp [fifth, varFiring, GoalFiring.selection, Selection.commit]
  · simp [fifth, varFiring, GoalFiring.selection, Selection.commit]
  · have : fourth.after.knowledge ++ fifth.residuals.map TypingCheckingMeta.tell =
        residuals.map TypingCheckingMeta.tell := rfl
    rw [this]
    exact solvable_at solution _ residuals_hold

/-- **The checking run**: five admitted firings, with three told residuals. -/
def checkRun : (metaGoalStep Θ Nat).Run start :=
  .cons first first_admitted (.cons second second_admitted (.cons third third_admitted
    (.cons fourth fourth_admitted (.cons fifth fifth_admitted (.nil _)))))

theorem checkRun_done : checkRun.last.present = ∅ := by decide

theorem checkRun_knowledge : checkRun.last.knowledge = residuals.map TypingCheckingMeta.tell := rfl

/-- **The run is admitted, so its residuals are not refuted.** -/
theorem run_admitted : (obligationFrames setting).Solvable (a := Θ) checkRun.last.knowledge := by
  rw [checkRun_knowledge]
  exact solvable_at solution _ residuals_hold

/-- **The equation `G ≐ Ground → Ground` is open at the identity**: it must wait. -/
theorem residual_open : ¬ (typeEqAt (Θ := Θ) .nil (.var 2) (.pi ground ground)).holds (𝟙 Θ) := by
  intro equal
  change TypeEq setting.R Θ.raw (subst ids (.var 2)) (subst ids (.pi ground ground)) at equal
  rw [subst_ids, subst_ids] at equal
  exact (TypeEq.neutral_form TowerModel.facts equal Θ.formed (Neutral.var 2)
    (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl

/-- **Postponed, then solved**: under the later solution the run gives the typing of the
instance. -/
theorem postponed_then_solved :
    Typed setting.R solutionFrame.raw (.app (.lam (.var 0)) (.var 0)) ground := by
  have typed := checking_run_sound (Θ := Θ) (O := Nat) (o₀ := 0) (t := .app (.var 1) (.var 0))
    (T := ground) rfl rfl checkRun checkRun_done
    solution ((models_tells_iff solution residuals).mpr residuals_hold)
    (fun _ member => by cases member) (ground_isType _)
  exact typed

/-! ## Postponement under a binder -/

/-- The local telescope `y : Ground`. -/
abbrev local₁ : Tele Tower.Head Θ.arity 1 := .snoc .nil ground

/-- The root `λy. g y ⇐ Ground → Ground`. -/
def lamRoot : Goal Θ := ⟨0, .nil, .check, .lam (.app (.var 2) (.var 0)), arrow⟩

def lamStart : GoalState Θ Nat := ⟨fun _ => lamRoot, {0}, []⟩

/-- Check the abstraction, telling `Ground → Ground ≐ Ground → Ground`. -/
def lam₁ : GoalFiring lamStart :=
  lamFiring lamStart 0 1 .nil (.app (.var 2) (.var 0)) arrow ground ground rfl

theorem lam₁_goal : lam₁.after.goal 1 = ⟨1, local₁, .check, .app (.var 2) (.var 0), ground⟩ := by
  simp [GoalFiring.after, lam₁, lamFiring]

/-- Switch to synthesis for the body. -/
def lam₂ : GoalFiring lam₁.after :=
  switchFiring lam₁.after 1 2 local₁ (.app (.var 2) (.var 0)) (inst0 (.var 0) ground) ground lam₁_goal

theorem lam₂_goal :
    lam₂.after.goal 2 = ⟨1, local₁, .synth, .app (.var 2) (.var 0), inst0 (.var 0) ground⟩ := by
  simp [GoalFiring.after, lam₂, switchFiring]

/-- Synthesize the application under the binder, telling `G ≐ Ground → Ground` there. -/
def lam₃ : GoalFiring lam₂.after :=
  appFiring lam₂.after 2 3 4 (by decide) local₁ (.var 2) (.var 0) (.var 3) ground ground lam₂_goal

theorem lam₃_goal₃ :
    lam₃.after.goal 3 = ⟨1, local₁, .synth, .var 2, Ctx.lookup (local₁.ctx Θ.raw) 2⟩ := by
  simp [GoalFiring.after, lam₃, appFiring]
  rfl

theorem lam₃_goal₄ : lam₃.after.goal 4 = ⟨1, local₁, .check, .var 0, ground⟩ := by
  simp [GoalFiring.after, lam₃, appFiring]

def lam₄ : GoalFiring lam₃.after := varFiring lam₃.after 3 local₁ 2 lam₃_goal₃

theorem lam₄_goal : lam₄.after.goal 4 = ⟨1, local₁, .check, .var 0, ground⟩ := by
  show (if (4 : Nat) ∈ lam₄.made then lam₄.premise 4 else lam₃.after.goal 4) = _
  rw [if_neg (by simp [lam₄, varFiring])]
  exact lam₃_goal₄

def lam₅ : GoalFiring lam₄.after := switchFiring lam₄.after 4 5 local₁ (.var 0) ground ground lam₄_goal

theorem lam₅_goal :
    lam₅.after.goal 5 = ⟨1, local₁, .synth, .var 0, Ctx.lookup (local₁.ctx Θ.raw) 0⟩ := by
  simp [GoalFiring.after, lam₅, switchFiring]
  rfl

def lam₆ : GoalFiring lam₅.after := varFiring lam₅.after 5 local₁ 0 lam₅_goal

/-- The residuals of the binder run. -/
def lamResiduals : List (Obligation Θ) :=
  [typeEqAt .nil arrow (.pi ground ground), belowAt local₁ (inst0 (.var 0) ground) ground,
    typeEqAt local₁ (.var 3) (.pi ground ground), belowAt local₁ ground ground]

theorem lamResiduals_hold : ∀ P ∈ lamResiduals, P.holds solution := by
  intro P member
  simp only [lamResiduals, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact IsType.refl (arrow_isType _)
  · exact IsType.below_refl (ground_isType _)
  · exact IsType.refl (arrow_isType _)
  · exact IsType.below_refl (ground_isType _)

theorem lamResiduals_solvable (ps : List (Obligation Θ)) (sub : ∀ P ∈ ps, P ∈ lamResiduals) :
    (obligationFrames setting).Solvable (a := Θ) (ps.map TypingCheckingMeta.tell) :=
  solvable_at solution ps (fun P member => lamResiduals_hold P (sub P member))

theorem lam₁_admitted : (metaGoalStep Θ Nat).Admits lam₁ := by
  refine ⟨List.nodup_singleton 1, ⟨?_, ?_, ?_, ?_, ?_⟩,
    lamResiduals_solvable [typeEqAt .nil arrow (.pi ground ground)] (by simp [lamResiduals]),
    fun _ _ _ => trivial⟩
  · simp [lam₁, lamFiring, GoalFiring.selection, Selection.commit, lamStart]
  · simp [lam₁, lamFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₁, lamFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₁, lamFiring, GoalFiring.selection, Selection.commit, lamStart]
  · simp [lam₁, lamFiring, GoalFiring.selection, Selection.commit]

theorem lam₁_present : lam₁.after.present = {1} := by decide

theorem lam₂_admitted : (metaGoalStep Θ Nat).Admits lam₂ := by
  refine ⟨List.nodup_singleton 2, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [lam₂, switchFiring, GoalFiring.selection, Selection.commit, lam₁_present]
  · simp [lam₂, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₂, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₂, switchFiring, GoalFiring.selection, Selection.commit, lam₁_present]
  · simp [lam₂, switchFiring, GoalFiring.selection, Selection.commit]
  · exact lamResiduals_solvable [typeEqAt .nil arrow (.pi ground ground),
      belowAt local₁ (inst0 (.var 0) ground) ground] (by simp [lamResiduals])

theorem lam₂_present : lam₂.after.present = {2} := by decide

theorem lam₃_admitted : (metaGoalStep Θ Nat).Admits lam₃ := by
  refine ⟨by decide, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [lam₃, appFiring, GoalFiring.selection, Selection.commit, lam₂_present]
  · simp [lam₃, appFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₃, appFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₃, appFiring, GoalFiring.selection, Selection.commit, lam₂_present]
  · simp [lam₃, appFiring, GoalFiring.selection, Selection.commit]
  · exact lamResiduals_solvable [typeEqAt .nil arrow (.pi ground ground),
      belowAt local₁ (inst0 (.var 0) ground) ground, typeEqAt local₁ (.var 3) (.pi ground ground)]
      (by simp [lamResiduals])

theorem lam₃_present : lam₃.after.present = {3, 4} := by decide

theorem lam₄_admitted : (metaGoalStep Θ Nat).Admits lam₄ := by
  refine ⟨List.nodup_nil, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [lam₄, varFiring, GoalFiring.selection, Selection.commit, lam₃_present]
  · simp [lam₄, varFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₄, varFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₄, varFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₄, varFiring, GoalFiring.selection, Selection.commit]
  · exact lamResiduals_solvable [typeEqAt .nil arrow (.pi ground ground),
      belowAt local₁ (inst0 (.var 0) ground) ground, typeEqAt local₁ (.var 3) (.pi ground ground)]
      (by simp [lamResiduals])

theorem lam₄_present : lam₄.after.present = {4} := by decide

theorem lam₅_admitted : (metaGoalStep Θ Nat).Admits lam₅ := by
  refine ⟨List.nodup_singleton 5, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [lam₅, switchFiring, GoalFiring.selection, Selection.commit, lam₄_present]
  · simp [lam₅, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₅, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₅, switchFiring, GoalFiring.selection, Selection.commit, lam₄_present]
  · simp [lam₅, switchFiring, GoalFiring.selection, Selection.commit]
  · exact lamResiduals_solvable lamResiduals (fun _ member => member)

theorem lam₅_present : lam₅.after.present = {5} := by decide

theorem lam₆_admitted : (metaGoalStep Θ Nat).Admits lam₆ := by
  refine ⟨List.nodup_nil, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ _ _ => trivial⟩
  · simp [lam₆, varFiring, GoalFiring.selection, Selection.commit, lam₅_present]
  · simp [lam₆, varFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₆, varFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₆, varFiring, GoalFiring.selection, Selection.commit]
  · simp [lam₆, varFiring, GoalFiring.selection, Selection.commit]
  · exact lamResiduals_solvable lamResiduals (fun _ member => member)

/-- **The binder run**: six admitted firings. -/
def lamRun : (metaGoalStep Θ Nat).Run lamStart :=
  .cons lam₁ lam₁_admitted (.cons lam₂ lam₂_admitted (.cons lam₃ lam₃_admitted
    (.cons lam₄ lam₄_admitted (.cons lam₅ lam₅_admitted (.cons lam₆ lam₆_admitted (.nil _))))))

theorem lamRun_done : lamRun.last.present = ∅ := by decide

theorem lamRun_knowledge : lamRun.last.knowledge = lamResiduals.map TypingCheckingMeta.tell := rfl

/-- **The equation under the binder is open at the identity**: it must wait. -/
theorem binder_residual_open :
    ¬ (typeEqAt (Θ := Θ) local₁ (.var 3) (.pi ground ground)).holds (𝟙 Θ) := by
  intro equal
  change TypeEq setting.R (.snoc Θ.raw (subst ids ground)) (subst (liftSub ids) (.var 3))
    (subst (liftSub ids) (.pi ground ground)) at equal
  rw [liftSub_ids, subst_ids, subst_ids, subst_ids] at equal
  have formed : CtxFormed setting.R (.snoc Θ.raw ground) := .snoc Θ.formed (ground_isType _)
  exact (TypeEq.neutral_form TowerModel.facts equal formed (Neutral.var 3)
    (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl

/-- **Postponed under a binder, then solved**: the run gives the typing of
`λy. (λz. z) y : Ground → Ground` under the later solution. -/
theorem binder_postponed_then_solved :
    Typed setting.R solutionFrame.raw (.lam (.app (.lam (.var 0)) (.var 0))) arrow := by
  have typed := checking_run_sound (Θ := Θ) (O := Nat) (o₀ := 0)
    (t := .lam (.app (.var 2) (.var 0))) (T := arrow) rfl rfl lamRun lamRun_done
    solution ((models_tells_iff solution lamResiduals).mpr lamResiduals_hold)
    (fun _ member => by cases member) (arrow_isType _)
  exact typed

/-! ## Refuted once its residual is refuted -/

/-- The knowledge already says `G ≐ Ground`. -/
def knownStart : GoalState Θ Nat :=
  ⟨fun _ => root, {0}, [TypingCheckingMeta.tell (typeEqAt .nil (.var 2) ground)]⟩

def knownFirst : GoalFiring knownStart :=
  switchFiring knownStart 0 1 .nil (.app (.var 1) (.var 0)) ground ground rfl

theorem knownFirst_goal :
    knownFirst.after.goal 1 = ⟨0, .nil, .synth, .app (.var 1) (.var 0), inst0 (.var 0) ground⟩ := by
  simp [GoalFiring.after, knownFirst, switchFiring]
  rfl

def knownSecond : GoalFiring knownFirst.after :=
  appFiring knownFirst.after 1 2 3 (by decide) .nil (.var 1) (.var 0) (.var 2) ground ground
    knownFirst_goal

/-- **The application firing is refused**: `G ≐ Ground` and `G ≐ Ground → Ground` have no common
solution. -/
theorem refuted_by_knowledge : ¬ (metaGoalStep Θ Nat).Admits knownSecond := by
  apply refused_of_unsolvable
  rintro ⟨Δ, σ, solved⟩
  have known : (typeEqAt (Θ := Θ) .nil (.var 2) ground).holds σ :=
    (models_tells_iff σ [typeEqAt .nil (.var 2) ground]).mp
      (fun e member => solved e (List.mem_append_left _ (List.mem_append_left _ member))) _
      (List.mem_singleton_self _)
  have told : (typeEqAt (Θ := Θ) .nil (.var 2) (.pi ground ground)).holds σ :=
    (models_tells_iff σ [typeEqAt .nil (.var 2) (.pi ground ground)]).mp
      (fun e member => solved e (List.mem_append_right _ member)) _ (List.mem_singleton_self _)
  have clash := TypeEq.trans setting.levels known.symm told
  exact TypeEq.pi_ne_head TowerModel.facts Δ.formed clash.symm

#print axioms checkRun_done
#print axioms run_admitted
#print axioms residual_open
#print axioms postponed_then_solved
#print axioms lamRun_done
#print axioms binder_residual_open
#print axioms binder_postponed_then_solved
#print axioms refuted_by_knowledge

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingCheckingMetaControls
