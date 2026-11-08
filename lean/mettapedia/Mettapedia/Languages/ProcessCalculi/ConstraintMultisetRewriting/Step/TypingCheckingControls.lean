import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingChecking

/-!
# Controls for checking as firings

In the two-head package of `DependentHelpers.Consumer`, the goal `λx.x ⇐ g → g` is checked by a
completed run of three firings: check the abstraction (telling that `g → g` reduces to a dependent
function type), switch to synthesis for the body (telling the subtype test `g ≤ g`), and synthesize
the variable. The run derives the goal (`identity_checked`).

Negative control (`ground_not_function`): checking `λx.x` against `g` tells an obligation that does
not hold, `g` reducing to a dependent function type, so that firing is not admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingCheckingControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Normalization
open Interface (Frames)
open Interface.Dependent.Consumer (TinyHead tiny arrow)
open TypingChecking TypingChecking.Kernel

theorem solvable_tells (store : EquationStore Prop) (ps : List Prop)
    (old : ∀ e ∈ store, (e.1 ↔ e.2)) (new : ∀ p ∈ ps, p) :
    (Frames.ofSubstitution obligations).Solvable (a := PUnit.unit) (store ++ ps.map tell) := by
  refine (solvable_iff _).mpr fun e member => ?_
  rcases List.mem_append.mp member with inside | told
  · exact old e inside
  · obtain ⟨p, present, rfl⟩ := List.mem_map.mp told
    exact iff_true_intro (new p present)

/-- The context `x : g`. -/
abbrev Γ₁ : Ctx TinyHead 1 := .snoc .nil (.head .ground)

/-- The goal `λx.x ⇐ g → g`. -/
def root : Goal TinyHead := ⟨0, .check, .nil, .lam (.var 0), arrow⟩

def start : GoalState (Goal TinyHead) Nat := ⟨fun _ => root, {0}, []⟩

/-- Check the abstraction against `g → g`. -/
def first : GoalFiring (Checks tiny) start :=
  lamFiring tiny start 0 1 .nil (.var 0) arrow (.head .ground) (.head .ground) rfl

theorem first_admitted : (goalStep (Checks tiny)).Admits first := by
  refine ⟨List.nodup_singleton 1, ⟨?_, ?_, ?_, ?_, ?_⟩,
    solvable_tells _ _ (fun _ member => by cases member) ?_, fun _ _ _ _ member => by cases member⟩
  · simp [first, lamFiring, GoalFiring.selection, Selection.commit, start]
  · simp [first, lamFiring, GoalFiring.selection, Selection.commit]
  · simp [first, lamFiring, GoalFiring.selection, Selection.commit]
  · simp [first, lamFiring, GoalFiring.selection, Selection.commit, start]
  · simp [first, lamFiring, GoalFiring.selection, Selection.commit]
  · intro p member
    simp only [first, lamFiring, List.mem_singleton] at member
    subst member
    exact Relation.ReflTransGen.refl

theorem first_goal : first.after.goal 1 = ⟨1, .check, Γ₁, .var 0, .head .ground⟩ := by
  simp [GoalFiring.after, first, lamFiring]

/-- Switch to synthesis for the body. -/
def second : GoalFiring (Checks tiny) first.after :=
  switchFiring tiny first.after 1 2 Γ₁ (.var 0) (Ctx.lookup Γ₁ 0) (.head .ground) first_goal

theorem first_present : first.after.present = {1} := by
  decide

theorem second_admitted : (goalStep (Checks tiny)).Admits second := by
  refine ⟨List.nodup_singleton 2, ⟨?_, ?_, ?_, ?_, ?_⟩,
    solvable_tells _ _ ((solvable_iff _).mp first_admitted.2.2.1) ?_,
    fun _ _ _ _ member => by cases member⟩
  · simp [second, switchFiring, GoalFiring.selection, Selection.commit, first_present]
  · simp [second, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [second, switchFiring, GoalFiring.selection, Selection.commit]
  · simp [second, switchFiring, GoalFiring.selection, Selection.commit, first_present]
  · simp [second, switchFiring, GoalFiring.selection, Selection.commit]
  · intro p member
    simp only [second, switchFiring, List.mem_singleton] at member
    subst member
    exact .conv (.heads Relation.ReflTransGen.refl Relation.ReflTransGen.refl (.inl rfl))

theorem second_goal : second.after.goal 2 = ⟨1, .synth, Γ₁, .var 0, Ctx.lookup Γ₁ 0⟩ := by
  simp [GoalFiring.after, second, switchFiring]

/-- Synthesize the variable. -/
def third : GoalFiring (Checks tiny) second.after :=
  varFiring tiny second.after 2 Γ₁ 0 second_goal

theorem second_present : second.after.present = {2} := by
  decide

theorem third_admitted : (goalStep (Checks tiny)).Admits third := by
  refine ⟨List.nodup_nil, ⟨?_, ?_, ?_, ?_, ?_⟩,
    solvable_tells _ _ ((solvable_iff _).mp second_admitted.2.2.1) (fun _ member => by cases member),
    fun _ _ _ _ member => by cases member⟩
  · simp [third, varFiring, GoalFiring.selection, Selection.commit, second_present]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]
  · simp [third, varFiring, GoalFiring.selection, Selection.commit]

/-- **The checking run**: three admitted firings. -/
def identity_run : (goalStep (Checks tiny)).Run start :=
  .cons first first_admitted (.cons second second_admitted (.cons third third_admitted (.nil _)))

theorem identity_run_done : identity_run.last.present = ∅ := by
  decide

/-- **The completed run derives the goal** `λx.x ⇐ g → g`. -/
theorem identity_checked :
    CheckingAlgorithm tiny .check .nil (.lam (.var 0)) (arrow : Tm TinyHead 0) :=
  completed_run_derives (Derives := Checks tiny) (root := root) (o₀ := 0) rfl rfl identity_run
    identity_run_done third_admitted.2.2.1

/-! ## A residual that fails -/

/-- Nothing reachable from a head is a dependent function type: the package has no root rules. -/
theorem head_reduces_to_head {n : Nat} {h : TinyHead} {t : Tm TinyHead n}
    (reduces : Reduces tiny (.head h) t) : ∃ h', t = .head h' := by
  induction reduces with
  | refl => exact ⟨h, rfl⟩
  | tail _ step ih =>
      obtain ⟨h', rfl⟩ := ih
      cases step with
      | head _ => exact ⟨_, rfl⟩
      | root impossible => exact impossible.elim

def ground : Goal TinyHead := ⟨0, .check, .nil, .lam (.var 0), .head .ground⟩

def groundStart : GoalState (Goal TinyHead) Nat := ⟨fun _ => ground, {0}, []⟩

/-- **Checking `λx.x` against `g` is refused**: the told obligation that `g` reduces to a dependent
function type has no solution, whatever domain and codomain the firing proposes. -/
theorem ground_not_function (A : Tm TinyHead 0) (B : Tm TinyHead 1) :
    ¬ (goalStep (Checks tiny)).Admits
      (lamFiring tiny groundStart 0 1 .nil (.var 0) (.head .ground) A B rfl) := by
  rintro ⟨_, _, solvable, _⟩
  have holds := (solvable_iff _).mp solvable (tell (Reduces tiny (.head .ground) (.pi A B)))
    (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  obtain ⟨_, wrong⟩ := head_reduces_to_head (holds.mpr trivial)
  cases wrong

#print axioms first_admitted
#print axioms second_admitted
#print axioms third_admitted
#print axioms identity_run_done
#print axioms identity_checked
#print axioms ground_not_function

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingCheckingControls
