import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveLocals
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionControls

/-!
# Decisiveness on a concrete store with distinct rigid locals

The store `λ x y. x ≐ λ x y. y` over `T : U0, F : (a b : T) → U0` is in the class of stores with
distinct rigid locals: its annotation `(x y : T) → T` is normal with two leading binders, and under
every telescope of its annotation of length two its sides reduce to the locals `x` and `y`. The
driver's decision on that class (`ContextualDependentDecisiveDriver.Settled.decided`) therefore
applies to it, as an instance: at one joint budget and at every larger one, the rigid solver refutes
it with a certified refutation and keeps that outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveLocals.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentScope ContextualDependentPiSpine ContextualDependentWorklist
open ContextualDependentExecutableJoin ContextualDependentExecutableDiscovery ContextualDependentDecisiveDriver
open ContextualDependentGeneralPattern

local instance : DecidableRel (LevelTower.rules Nat).headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

local instance (head : LevelTower.Head Nat) : Decidable ((LevelTower.rules Nat).isUniverse head) :=
  ExecutableTowerChoices.universeDecidable head

local instance : DecidableRel (LevelTower.rules Nat).cumulative := fun left right =>
  LevelTower.instDecidableCumulative left right

/-- Opening a function under a telescope applies its renamed code to distinct locals of the telescope,
one for each binder. -/
theorem opening {Γ : Context (LevelTower.rules Nat)} {whole : TypeOver Γ} (scope : Spine whole) :
    ∃ arguments : List (Tm (LevelTower.Head Nat) scope.target.arity),
      arguments.length = scope.length ∧ arguments.Nodup ∧
      (∀ argument ∈ arguments, ∃ position, argument = .var (scope.localIndex position)) ∧
      ∀ function : Term Γ whole,
        (scope.openFunction function).code = appSpine (Presentation.rename scope.outerRen function.code) arguments := by
  induction scope with
  | stop type =>
      refine ⟨[], rfl, List.nodup_nil, fun _ member => absurd member List.not_mem_nil, fun function => ?_⟩
      exact (Presentation.rename_id function.code).symm
  | bind shape rest ih =>
      obtain ⟨arguments, length, nodup, locals, opened⟩ := ih
      refine ⟨.var (rest.outerRen 0) :: arguments, ?_, ?_, ?_, fun function => ?_⟩
      · change arguments.length + 1 = rest.length + 1
        rw [length]
      · refine List.nodup_cons.mpr ⟨fun member => ?_, nodup⟩
        obtain ⟨position, same⟩ := locals _ member
        exact rest.outer_ne_local 0 position (Tm.var.inj same)
      · intro argument member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨.inl (), (congrArg Tm.var (Spine.localIndex_head shape rest)).symm⟩
        · obtain ⟨position, rfl⟩ := locals argument later
          exact ⟨.inr position, rfl⟩
      · rw [Spine.openFunction, opened]
        simp only [ContextualDependentPiShape.Shape.fresh, Presentation.rename, rename_comp]
        rfl

/-- Under a telescope of length two, `λ a b. a` and `λ a b. b` open to its two distinct locals. -/
theorem two_locals {Γ : Context (LevelTower.rules Nat)} {whole : TypeOver Γ} (scope : Spine whole)
    (length : scope.length = 2) (left right : Term Γ whole)
    (leftCode : left.code = .lam (.lam (.var 1))) (rightCode : right.code = .lam (.lam (.var 0))) :
    ∃ first second : scope.Local, first ≠ second ∧
      Star (R := LevelTower.rules Nat) (scope.openFunction left).code (.var (scope.localIndex first)) ∧
      Star (R := LevelTower.rules Nat) (scope.openFunction right).code (.var (scope.localIndex second)) := by
  obtain ⟨arguments, argumentsLength, nodup, locals, opened⟩ := opening scope
  rw [length] at argumentsLength
  match arguments, argumentsLength, nodup, locals, opened with
  | [one, two], _, nodup, locals, opened =>
      obtain ⟨first, rfl⟩ := locals one (by simp)
      obtain ⟨second, rfl⟩ := locals two (by simp)
      have different : first ≠ second := by
        rintro rfl
        simp at nodup
      refine ⟨first, second, different, ?_, ?_⟩
      · rw [opened, leftCode]
        exact .tail (.tail .refl (.congAppFun (.betaPi _ _))) (.betaPi _ _)
      · rw [opened, rightCode]
        exact .tail (.tail .refl (.congAppFun (.betaPi _ _))) (.betaPi _ _)

/-- **The concrete store is in the class.** -/
theorem distinct_member : ∃ equation ∈ ContextualDependentRigidDecomposition.Controls.distinctStore,
    DistinctLocals equation := by
  refine ⟨_, List.mem_singleton_self _, IsType.refl (TypeOver.isType _), ?_, by decide +kernel,
    fun scope length => ?_⟩
  · exact ContextualDependentReductionBudget.normal_of_stopped (LevelTower.rules Nat) (fun _ => none)
      (fun _ _ _ impossible => impossible.elim) _ rfl
  · exact two_locals scope length _ _ rfl rfl

/-- **Decisiveness, instantiated**: the rigid solver refutes the concrete store at one joint budget
and at every larger one, with the same outcome. -/
theorem distinct_decided :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((family (fun _ => (0 : Nat)) (fun _ => rfl) DispatchControls.tower_normalizes
          DispatchControls.certifyNormal).solver larger) ContextualDependentRigidDecomposition.Controls.distinctStore
          larger =
        run ((family (fun _ => (0 : Nat)) (fun _ => rfl) DispatchControls.tower_normalizes
          DispatchControls.certifyNormal).solver budget) ContextualDependentRigidDecomposition.Controls.distinctStore
          budget ∧
      ∃ absent, run ((family (fun _ => (0 : Nat)) (fun _ => rfl) DispatchControls.tower_normalizes
          DispatchControls.certifyNormal).solver larger) ContextualDependentRigidDecomposition.Controls.distinctStore
          larger = .refuted absent :=
  decided (fun _ => (0 : Nat)) (fun _ => rfl) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    distinct_member

end ContextualDependentDecisiveLocals.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
