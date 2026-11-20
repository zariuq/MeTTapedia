import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Comparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration

/-!
# The cumulative tower is an instance

The bare cumulative tower has the facts of the normalization model, a complete algorithmic equality, no
root computation (so the empty root evaluator is complete) and strongly normalizing typed terms
(`tower_sn`). So the general theorem gives eventual success of the executable comparison over the tower's
normalizer directly (`tower_compare_eventually`, `tower_types_eventually`): the same statements as the tree's
tower proof, which follows the algorithmic equality through joinability of directed reduction, confluence
and the shapes of reducts; the general proof needs none of these.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- The tower's typed terms are strongly normalizing. -/
theorem tower_typedSN : TypedSN (LevelTower.rules L) := fun formed typed =>
  TowerInterpretation.tower_sn formed typed

/-- The tower has no root step, so the empty root evaluator is complete. -/
theorem tower_rootComplete : RootComplete (LevelTower.rules L) (fun _ => none) :=
  fun _ _ _ impossible => impossible.elim

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]

/-- **The tower's executable conversion eventually accepts every equality**, as an instance of the general
theorem. -/
theorem tower_compare_eventually {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t u A : Tm (LevelTower.Head L) n} (formed : CtxFormed (LevelTower.rules L) Γ)
    (equal : Equal (LevelTower.rules L) Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      compare (LevelTower.rules L) (normalize (LevelTower.rules L) (fun _ => none)) larger Γ t u A =
        some certificate := by
  let _ :DecidableRel (TowerModel.setting (L := L) fun _ => UniverseLevel.LevelOrder.bot).R.headEq :=
    inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)
  let _ :∀ head, Decidable
      ((TowerModel.setting (L := L) fun _ => UniverseLevel.LevelOrder.bot).R.isUniverse head) :=
    fun head => inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))
  exact sn_compare_eventually (S := TowerModel.setting (L := L) fun _ => UniverseLevel.LevelOrder.bot)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra TowerModel.complete
    tower_typedSN (fun _ => none) tower_rootComplete formed equal

/-- **The tower's executable type comparison eventually accepts every equality of types.** -/
theorem tower_types_eventually {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n} (formed : CtxFormed (LevelTower.rules L) Γ)
    (equal : TypeEq (LevelTower.rules L) Γ A B) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      types (LevelTower.rules L) (normalize (LevelTower.rules L) (fun _ => none)) larger Γ A B =
        some certificate := by
  let _ :DecidableRel (TowerModel.setting (L := L) fun _ => UniverseLevel.LevelOrder.bot).R.headEq :=
    inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)
  let _ :∀ head, Decidable
      ((TowerModel.setting (L := L) fun _ => UniverseLevel.LevelOrder.bot).R.isUniverse head) :=
    fun head => inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))
  exact sn_types_eventually (S := TowerModel.setting (L := L) fun _ => UniverseLevel.LevelOrder.bot)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra TowerModel.complete
    tower_typedSN (fun _ => none) tower_rootComplete formed equal

/-- **The same statement as the tree's tower theorem** (`ContextualDependentExecutableConversion.compare_eventually`),
here obtained from the general theorem. -/
theorem tower_compare_eventually_same {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t u A : Tm (LevelTower.Head L) n} (formed : CtxFormed (LevelTower.rules L) Γ)
    (equal : Equal (LevelTower.rules L) Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      compare (LevelTower.rules L) ContextualDependentExecutableConversion.red larger Γ t u A =
        some certificate :=
  tower_compare_eventually formed equal

/-- **The same statement as the tree's tower theorem for types**
(`ContextualDependentExecutableConversion.types_eventually`). -/
theorem tower_types_eventually_same {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n} (formed : CtxFormed (LevelTower.rules L) Γ)
    (equal : TypeEq (LevelTower.rules L) Γ A B) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      types (LevelTower.rules L) ContextualDependentExecutableConversion.red larger Γ A B =
        some certificate :=
  tower_types_eventually formed equal

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms tower_typedSN
#print axioms tower_rootComplete
#print axioms tower_compare_eventually
#print axioms tower_types_eventually
#print axioms tower_compare_eventually_same
#print axioms tower_types_eventually_same
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
