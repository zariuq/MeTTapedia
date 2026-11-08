import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScope

/-!
# Exchanging independent rigid parameters

Two local domains formed over the same outer context may be exchanged.
The result type and both terms are transported along the actual typed swap.
Outer metavariables are fixed. The scoped equation has the same solutions
before and after exchange, at every future outer substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentParameterExchange

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentScope

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

def second (first next : TypeOver Γ) : TypeOver (extend Γ first) :=
  next.reindex (projectionHom Γ first)

abbrev context (first next : TypeOver Γ) := extend (extend Γ first) (second first next)

def base (first next : TypeOver Γ) : context first next ⟶ Γ :=
  projectionHom (extend Γ first) (second first next) ≫ projectionHom Γ first

def earlier (first next : TypeOver Γ) : Term (context first next) (first.reindex (base first next)) :=
  pulledNewest (projectionHom (extend Γ first) (second first next))

def later (first next : TypeOver Γ) : Term (context first next) (next.reindex (base first next)) :=
  (newest (extend Γ first) (second first next)).cast
    (next.reindex_comp (projectionHom (extend Γ first) (second first next)) (projectionHom Γ first)).symm

def swap (first next : TypeOver Γ) : context first next ⟶ context next first :=
  pair (pair (base first next) (later first next))
    ((earlier first next).cast (by
      change first.reindex (base first next) =
        (first.reindex (projectionHom Γ next)).reindex (pair (base first next) (later first next))
      rw [← TypeOver.reindex_comp, pair_projection]))

theorem swap_zero (first next : TypeOver Γ) :
    (swap first next).substitution 0 = .var (0 : Fin (Γ.arity + 1)).succ := by
  exact (Term.cast_code _ _).trans (by rw [earlier, pulledNewest_code]; rfl)

theorem swap_one (first next : TypeOver Γ) :
    (swap first next).substitution (0 : Fin (Γ.arity + 1)).succ = .var 0 :=
  Term.cast_code _ _

theorem swap_older (first next : TypeOver Γ) (index : Fin Γ.arity) :
    (swap first next).substitution index.succ.succ = .var index.succ.succ := rfl

theorem swap_twice (first next : TypeOver Γ) : swap first next ≫ swap next first = 𝟙 _ := by
  apply Hom.ext
  funext index
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun index => ?_) index) index
  · change subst (swap first next).substitution ((swap next first).substitution 0) = .var 0
    rw [swap_zero]
    exact swap_one first next
  · change subst (swap first next).substitution ((swap next first).substitution (0 : Fin (Γ.arity + 1)).succ) = _
    rw [swap_one]
    exact swap_zero first next
  · change subst (swap first next).substitution ((swap next first).substitution index.succ.succ) = _
    rw [swap_older]
    exact swap_older first next index

def reindexActive {Δ Θ : Context rules} (active : Active Θ) (map : Δ ⟶ Θ) : Active Δ :=
  ⟨active.type.reindex map, active.left.reindex map, active.right.reindex map⟩

theorem reindexActive_holds {Δ Θ Ξ : Context rules} (active : Active Θ) (map : Δ ⟶ Θ)
    (solution : Ξ ⟶ Δ) : (reindexActive active map).Holds solution ↔ active.Holds (solution ≫ map) := by
  simp only [Active.Holds, reindexActive, Term.reindex, TypeOver.reindex, subst_subComp]
  rfl

theorem active_holds_comp {Δ Θ Ξ : Context rules} (active : Active Θ) (map : Δ ⟶ Θ)
    (refinement : Ξ ⟶ Δ) (solved : active.Holds map) : active.Holds (refinement ≫ map) := by
  have carried := solved.substitute refinement.typed
  simp only [subst_subComp] at carried
  exact carried

def problem (first next : TypeOver Γ) (active : Active (context first next)) : Scoped Γ :=
  .bind first (.bind (second first next) (.active active))

def exchanged (first next : TypeOver Γ) (active : Active (context first next)) : Scoped Γ :=
  problem next first (reindexActive active (swap next first))

theorem second_reindex {Δ : Context rules} (solution : Δ ⟶ Γ) (first next : TypeOver Γ) :
    (second first next).reindex (rawLift solution first) = second (first.reindex solution) (next.reindex solution) := by
  unfold second
  rw [← TypeOver.reindex_comp, ContextualDependentUpdate.lift_projection, TypeOver.reindex_comp]

def liftBoth {Δ : Context rules} (solution : Δ ⟶ Γ) (first next : TypeOver Γ) :
    context (first.reindex solution) (next.reindex solution) ⟶ context first next :=
  convertedLift (rawLift solution first) (second first next)
    (second (first.reindex solution) (next.reindex solution)) (by
      change TypeEq rules (extend Δ (first.reindex solution)).raw
        ((second first next).reindex (rawLift solution first)).code _
      rw [second_reindex]
      exact (second (first.reindex solution) (next.reindex solution)).isType.refl)

theorem liftBoth_substitution {Δ : Context rules} (solution : Δ ⟶ Γ) (first next : TypeOver Γ) :
    (liftBoth solution first next).substitution = liftSub (liftSub solution.substitution) :=
  convertedLift_substitution _ _ _ _

theorem swap_weaken_twice (first next : TypeOver Γ) (term : Tm Head Γ.arity) :
    subst (swap first next).substitution (rename wk (rename wk term)) = rename wk (rename wk term) := by
  rw [subst_rename, subst_rename, ← subst_renSub, ← subst_renSub, subst_subComp]
  apply subst_ext
  intro index
  exact swap_older first next index

theorem lift_swap {Δ : Context rules} (solution : Δ ⟶ Γ) (first next : TypeOver Γ) :
    liftBoth solution first next ≫ swap first next =
      swap (first.reindex solution) (next.reindex solution) ≫ liftBoth solution next first := by
  apply Hom.ext
  funext index
  change subst (liftBoth solution first next).substitution ((swap first next).substitution index) =
    subst (swap (first.reindex solution) (next.reindex solution)).substitution
      ((liftBoth solution next first).substitution index)
  rw [liftBoth_substitution, liftBoth_substitution]
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun index => ?_) index) index
  · rw [swap_zero]
    exact (swap_zero (first.reindex solution) (next.reindex solution)).symm
  · rw [swap_one]
    exact (swap_one (first.reindex solution) (next.reindex solution)).symm
  · rw [swap_older]
    exact (swap_weaken_twice (first.reindex solution) (next.reindex solution) (solution.substitution index)).symm

theorem problem_holds_iff {Δ : Context rules} (solution : Δ ⟶ Γ) (first next : TypeOver Γ)
    (active : Active (context first next)) :
    (problem first next active).Holds solution ↔ active.Holds (liftBoth solution first next) := by
  change active.Holds (rawLift (rawLift solution first) (second first next)) ↔ _
  unfold Active.Holds
  rw [liftBoth_substitution]
  change Equal rules (extend (extend Δ (first.reindex solution))
    ((second first next).reindex (rawLift solution first))).raw
      (subst (liftSub (liftSub solution.substitution)) active.left.code)
      (subst (liftSub (liftSub solution.substitution)) active.right.code)
      (subst (liftSub (liftSub solution.substitution)) active.type.code) ↔ _
  rw [second_reindex]

theorem exchanged_holds_iff {Δ : Context rules} (solution : Δ ⟶ Γ) (first next : TypeOver Γ)
    (active : Active (context first next)) :
    (exchanged first next active).Holds solution ↔ (problem first next active).Holds solution := by
  rw [exchanged, problem_holds_iff, reindexActive_holds, lift_swap, problem_holds_iff]
  constructor
  · intro solved
    have carried := active_holds_comp active _ (swap (first.reindex solution) (next.reindex solution)) solved
    simpa only [← Category.assoc, swap_twice, Category.id_comp] using carried
  · intro solved
    exact active_holds_comp active _ (swap (next.reindex solution) (first.reindex solution)) solved

end ContextualDependentParameterExchange
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
