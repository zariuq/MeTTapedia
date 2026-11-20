import Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax
import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternLaws
import Mathlib.Data.List.Forall2

/-!
# Soundness and completeness of the generic-fact syntax check

The evidence identifies the actual input slot and the complete canonical
equation, including its pattern and result. Freshness is checked on the
rendered head. The laws concern the unconditional generic branch, before
joining its operational interpretation to the rest of the compiler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax

open Algorithms.MeTTa.Simple.Parser (SExpr)

@[simp] theorem inputSlot_equation (relation slot : String) (arguments : List SExpr) :
    inputSlot? (equation relation slot arguments) = some slot := rfl

theorem inputSlot_of_equation {head emitted : SExpr} {slot : String}
    (generated : equation? head slot = some emitted) : inputSlot? emitted = some slot := by
  cases head with
  | atom token => simp [equation?] at generated
  | list values =>
      cases values with
      | nil => simp [equation?] at generated
      | cons first rest =>
          cases first with
          | list terms => simp [equation?] at generated
          | atom relation =>
              have same : equation relation slot rest = emitted := by
                simpa only [equation?, Option.some.injEq] using generated
              rw [← same, inputSlot_equation]

theorem check_iff (head emitted : SExpr) :
    check head emitted = true ↔
      ∃ slot, inputSlot? emitted = some slot ∧ freshSlot head slot = true ∧
        equation? head slot = some emitted := by
  unfold check
  cases read : inputSlot? emitted with
  | none => simp
  | some slot =>
      dsimp only
      cases generated : equation? head slot with
      | none => simp [generated]
      | some expected =>
          dsimp only
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨fresh, same⟩
            refine ⟨slot, rfl, fresh, ?_⟩
            simpa only [same] using generated
          · rintro ⟨other, sameRead, fresh, source⟩
            have sameSlot : other = slot := (Option.some.inj sameRead).symm
            subst other
            have same : expected = emitted := Option.some.inj (generated.symm.trans source)
            exact ⟨fresh, same.symm⟩

theorem check_equation {head emitted : SExpr} {slot : String}
    (fresh : freshSlot head slot = true)
    (generated : equation? head slot = some emitted) : check head emitted = true :=
  (check_iff head emitted).2 ⟨slot, inputSlot_of_equation generated, fresh, generated⟩

/-- The complete output tree is determined, while the fresh slot's spelling
is allowed to vary. No claim about a digest is needed. -/
theorem checked_equation {head emitted : SExpr}
    (checked : check head emitted = true) :
    ∃ relation arguments slot,
      head = .list (.atom relation :: arguments) ∧ freshSlot head slot = true ∧
      emitted = equation relation slot arguments := by
  obtain ⟨slot, _, fresh, generated⟩ := (check_iff head emitted).1 checked
  cases head with
  | atom token => simp [equation?] at generated
  | list values =>
      cases values with
      | nil => simp [equation?] at generated
      | cons first rest =>
          cases first with
          | list terms => simp [equation?] at generated
          | atom relation =>
              refine ⟨relation, rest, slot, rfl, fresh, ?_⟩
              exact (Option.some.inj generated).symm

theorem checkMany_iff (heads equations : List SExpr) :
    checkMany heads equations = true ↔
      List.Forall₂ (fun head emitted => check head emitted = true) heads equations := by
  induction heads generalizing equations with
  | nil =>
      cases equations <;> simp [checkMany]
  | cons head heads ih =>
      cases equations with
      | nil => simp [checkMany]
      | cons emitted equations =>
          simp only [checkMany, Bool.and_eq_true, ih, List.forall₂_cons]

theorem checked_occurrence_count {heads equations : List SExpr}
    (checked : checkMany heads equations = true) : heads.length = equations.length :=
  ((checkMany_iff heads equations).1 checked).length_eq

#print axioms check_iff
#print axioms checked_equation
#print axioms checked_occurrence_count

end Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax
