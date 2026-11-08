import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenamingTower

/-!
# Strengthening typed equality past an unused variable, in the cumulative tower

The first rung of the dead-helper converse. Two terms typed in `Γ` that are equal in `Γ.D` after
weakening are equal in `Γ` (`equal_strengthen`); the same for types (`typeEq_strengthen`).

The proof runs the actual conversion executable:
* it accepts the weakened equality at some budget (`compare_eventually`, completeness in the tower);
* it accepts weakened inputs exactly when it accepts the originals
  (`ContextualDependentRenaming.conversion_commutes`, along the embedding `Γ ⟶ Γ.D`);
* its certificate is sound for terms typed in `Γ` (`Algorithm.sound`).

**What is not proved here: strengthening of typing.** A raw term typed in `Γ.D` after weakening need
not be shown typed in `Γ` by these means: the checking executable is complete only on the
bidirectional fragment, and typing is not closed under expansion. The dead-helper converse needs it
for made rows given as raw codes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.Strengthening

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableConversion

variable {L : Type} [UniverseLevel.LevelOrder L]

omit [UniverseLevel.LevelOrder L] in
/-- The weakening embeds a context into its extension. -/
theorem embedding_wk {n : Nat} (Γ : Ctx (LevelTower.Head L) n) (D : Tm (LevelTower.Head L) n) :
    ContextualDependentRenaming.Embedding Γ (.snoc Γ D) wk :=
  ⟨Fin.succ_injective _, CtxRen.wk Γ D⟩

theorem prefix_formed {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {D : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) (.snoc Γ D)) : CtxFormed (LevelTower.rules L) Γ := by
  cases formed
  assumption

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]

/-- **Strengthening of typed equality past an unused variable.** -/
theorem equal_strengthen (valuation : Nat → L) {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {D : Tm (LevelTower.Head L) n} (formed : CtxFormed (LevelTower.rules L) (.snoc Γ D))
    {t u A : Tm (LevelTower.Head L) n} (tt : Typed (LevelTower.rules L) Γ t A)
    (tu : Typed (LevelTower.rules L) Γ u A)
    (equal : Equal (LevelTower.rules L) (.snoc Γ D) (rename wk t) (rename wk u) (rename wk A)) :
    Equal (LevelTower.rules L) Γ t u A := by
  obtain ⟨fuel, certificate, stable⟩ := ContextualDependentExecutableConversion.compare_eventually formed equal
  have same := (ContextualDependentRenaming.conversion_commutes (R := LevelTower.rules L)
    ContextualDependentRenaming.red_renames fuel).1 (embedding_wk Γ D) t u A
  rw [stable fuel le_rfl] at same
  cases computed : compare (LevelTower.rules L) ContextualDependentExecutableConversion.red fuel Γ t u A with
  | none =>
      rw [computed] at same
      cases same
  | some found =>
      exact Algorithm.sound (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra found.down (prefix_formed formed) tt tu

/-- **Strengthening of type equality past an unused variable.** -/
theorem typeEq_strengthen (valuation : Nat → L) {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {D : Tm (LevelTower.Head L) n} (formed : CtxFormed (LevelTower.rules L) (.snoc Γ D))
    {A B : Tm (LevelTower.Head L) n} {u : LevelTower.Head L} (universe' : (LevelTower.rules L).isUniverse u)
    (tA : Typed (LevelTower.rules L) Γ A (.head u)) (tB : Typed (LevelTower.rules L) Γ B (.head u))
    (equal : TypeEq (LevelTower.rules L) (.snoc Γ D) (rename wk A) (rename wk B)) :
    TypeEq (LevelTower.rules L) Γ A B := by
  obtain ⟨fuel, certificate, stable⟩ := ContextualDependentExecutableConversion.types_eventually formed equal
  have same := (ContextualDependentRenaming.conversion_commutes (R := LevelTower.rules L)
    ContextualDependentRenaming.red_renames fuel).2.2.2 (embedding_wk Γ D) A B
  rw [stable fuel le_rfl] at same
  cases computed : types (LevelTower.rules L) ContextualDependentExecutableConversion.red fuel Γ A B with
  | none =>
      rw [computed] at same
      cases same
  | some found =>
      exact ⟨u, universe', Algorithm.sound (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra found.down (prefix_formed formed) universe' tA tB⟩

end DependentFull.Strengthening

#print axioms DependentFull.Strengthening.equal_strengthen
#print axioms DependentFull.Strengthening.typeEq_strengthen

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
