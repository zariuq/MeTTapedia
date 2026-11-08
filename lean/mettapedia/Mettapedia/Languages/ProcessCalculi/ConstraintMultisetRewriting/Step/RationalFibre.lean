import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalUnification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# The finite-tree fibre inside the rational-tree fibre

Finite terms are rational trees (`RTree.ofTerm`), and finite substitution is substitution of trees
(`subst_ofTerm`). Along this map:

* **Solutions are preserved and reflected** (`models_ofStore_iff`): a finite substitution solves a
  finite store exactly when, read as rational trees, it solves the store read as rational trees.
  Hence **solvability is preserved** (`consistent_ofStore`).
* **Principal answers are preserved** (`principal_ofSubst`): a most general finite solution stays most
  general among the rational solutions.
* **Solvability is reflected exactly on acyclic problems** (`consistent_iff_acyclic`): a finite store
  is solvable over finite trees exactly when its rational principal answer takes finite values. When
  it is solvable, *every* rational principal answer takes finite values (`principal_finite`), and the
  rational solved form pulls back to a finite principal answer (`finite_principal_of_consistent`).

Solvability is not reflected in general: `X = f(X)` is solvable over rational trees and not over
finite ones (`RationalControls`).

The finite-tree fibre's check calculus (`CertainChecks.Derives`) is sound for the finite term
algebra only: its refutations use the occurs check. The rational-tree fibre has its own calculus
(`RationalModels`), whose refutations are clashes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP

variable {σ : LPSignature}

/-- A finite substitution, read as rational trees. -/
def ofSubst (θ : Subst σ) : RSubst σ := fun v => RTree.ofTerm (θ v)

/-- A finite store, read as rational trees. -/
def ofStore (P : EquationStore (Term σ)) : EquationStore (RTree σ) :=
  P.map fun e => (RTree.ofTerm e.1, RTree.ofTerm e.2)

/-- A rational tree that is a finite term. -/
def IsFinite (t : RTree σ) : Prop := ∃ u : Term σ, RTree.ofTerm u = t

theorem subst_ofTerm (θ : Subst σ) (u : Term σ) :
    RTree.subst (ofSubst θ) (RTree.ofTerm u) = RTree.ofTerm (θ.applyTerm u) :=
  (RTree.ofTerm_subst θ u).symm

/-- **Solutions are preserved and reflected.** -/
theorem models_ofStore_iff (θ : Subst σ) (P : EquationStore (Term σ)) :
    (rationalAction σ).Models (ofSubst θ) (ofStore P) ↔ (FirstOrder.action σ).Models θ P := by
  unfold SubstitutionAction.Models ofStore
  rw [List.forall_mem_map]
  refine forall₂_congr fun e _ => ?_
  show RTree.subst (ofSubst θ) (RTree.ofTerm e.1) = RTree.subst (ofSubst θ) (RTree.ofTerm e.2) ↔
    θ.applyTerm e.1 = θ.applyTerm e.2
  rw [subst_ofTerm, subst_ofTerm]
  exact RTree.ofTerm_injective.eq_iff

/-- **Solvability is preserved.** -/
theorem consistent_ofStore {P : EquationStore (Term σ)}
    (consistent : (FirstOrder.action σ).Consistent P) : (rationalAction σ).Consistent (ofStore P) := by
  obtain ⟨θ, solved⟩ := consistent
  exact ⟨ofSubst θ, (models_ofStore_iff θ P).mpr solved⟩

/-- A tree that a substitution makes finite was finite already. -/
theorem IsFinite.of_subst {δ : RSubst σ} {t : RTree σ} (finite : IsFinite (RTree.subst δ t)) :
    IsFinite t := by
  obtain ⟨u, same⟩ := finite
  obtain ⟨s, eq⟩ := Raw.eq_ofTerm_of_subst u t.2.1 (congrArg Subtype.val same).symm
  exact ⟨s, RTree.ext eq.symm⟩

/-- **A finitely solvable store has finite rational principal answers**, whichever is chosen. -/
theorem principal_finite {P : EquationStore (Term σ)} (consistent : (FirstOrder.action σ).Consistent P)
    {θ : RSubst σ} (principal : (rationalAction σ).Principal (ofStore P) θ) (v : σ.vars) :
    IsFinite (θ v) := by
  obtain ⟨δ, solved⟩ := consistent
  obtain ⟨residual, through⟩ := principal.factors (ofSubst δ) ((models_ofStore_iff δ P).mpr solved)
  have atLeaf : RTree.subst (ofSubst δ) (RTree.leaf v) =
      RTree.subst ((rationalAction σ).compose residual θ) (RTree.leaf v) := through (RTree.leaf v)
  rw [RTree.subst_leaf, RTree.subst_leaf] at atLeaf
  exact IsFinite.of_subst (δ := residual) ⟨δ v, atLeaf⟩

/-- Finite values pull back to a finite substitution. -/
theorem exists_ofSubst {θ : RSubst σ} (finite : ∀ v, IsFinite (θ v)) : ∃ θ' : Subst σ, ofSubst θ' = θ := by
  choose θ' same using finite
  exact ⟨θ', funext same⟩

/-- **The rational solved form of a finitely solvable store pulls back to a finite principal
answer.** -/
theorem finite_principal_of_consistent {P : EquationStore (Term σ)}
    (consistent : (FirstOrder.action σ).Consistent P) :
    ∃ θ' : Subst σ, ofSubst θ' = mgu (ofStore P) ∧ (FirstOrder.action σ).Principal P θ' := by
  have unrefuted : ¬ Refuted (ofStore P) :=
    (consistent_iff_not_refuted _).mp (consistent_ofStore consistent)
  have principal := mgu_principal unrefuted
  obtain ⟨θ', same⟩ := exists_ofSubst (principal_finite consistent principal)
  refine ⟨θ', same, (models_ofStore_iff θ' P).mp (same ▸ principal.sound), ?_⟩
  intro δ solved
  refine ⟨δ, fun t => ?_⟩
  have pointwise : ∀ v, δ.applyTerm (θ' v) = δ v := by
    intro v
    have factored := mgu_factors ((models_ofStore_iff δ P).mpr solved) v
    rw [← same] at factored
    exact RTree.ofTerm_injective ((subst_ofTerm δ (θ' v)).symm.trans factored)
  have composed : Subst.comp δ θ' = δ := funext pointwise
  show δ.applyTerm t = (Subst.comp δ θ').applyTerm t
  rw [composed]

/-- **Most general finite solutions stay most general among the rational solutions.** -/
theorem principal_ofSubst {P : EquationStore (Term σ)} {θ : Subst σ}
    (principal : (FirstOrder.action σ).Principal P θ) :
    (rationalAction σ).Principal (ofStore P) (ofSubst θ) := by
  refine ⟨(models_ofStore_iff θ P).mpr principal.sound, ?_⟩
  intro δ solved
  obtain ⟨θ'', same, principal''⟩ := finite_principal_of_consistent ⟨θ, principal.sound⟩
  obtain ⟨ρ, through⟩ := principal.factors θ'' principal''.sound
  refine ⟨(rationalAction σ).compose δ (ofSubst ρ), fun t => ?_⟩
  have pointwise : ∀ v, RTree.subst ((rationalAction σ).compose δ (ofSubst ρ)) (ofSubst θ v) = δ v := by
    intro v
    have atVar : θ'' v = ρ.applyTerm (θ v) := through (.var v)
    show RTree.subst (fun w => RTree.subst δ (ofSubst ρ w)) (RTree.ofTerm (θ v)) = δ v
    rw [RTree.subst_comp, subst_ofTerm, ← atVar]
    have factored := mgu_factors solved v
    rw [← same] at factored
    exact factored
  have composed : (rationalAction σ).compose ((rationalAction σ).compose δ (ofSubst ρ)) (ofSubst θ) = δ :=
    funext pointwise
  rw [composed]
  exact rfl

/-- **Solvability is reflected exactly on acyclic problems**: a finite store is solvable over finite
trees exactly when it has a rational principal answer with finite values. -/
theorem consistent_iff_acyclic (P : EquationStore (Term σ)) :
    (FirstOrder.action σ).Consistent P ↔
      ∃ θ : RSubst σ, (rationalAction σ).Principal (ofStore P) θ ∧ ∀ v, IsFinite (θ v) := by
  constructor
  · intro consistent
    have unrefuted : ¬ Refuted (ofStore P) :=
      (consistent_iff_not_refuted _).mp (consistent_ofStore consistent)
    exact ⟨mgu (ofStore P), mgu_principal unrefuted, principal_finite consistent (mgu_principal unrefuted)⟩
  · rintro ⟨θ, principal, finite⟩
    obtain ⟨θ', rfl⟩ := exists_ofSubst finite
    exact ⟨θ', (models_ofStore_iff θ' P).mp principal.sound⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.models_ofStore_iff
#print axioms Rational.consistent_ofStore
#print axioms Rational.IsFinite.of_subst
#print axioms Rational.principal_finite
#print axioms Rational.finite_principal_of_consistent
#print axioms Rational.principal_ofSubst
#print axioms Rational.consistent_iff_acyclic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
