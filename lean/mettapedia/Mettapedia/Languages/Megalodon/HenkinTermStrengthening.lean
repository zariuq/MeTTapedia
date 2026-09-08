import Mettapedia.Languages.Megalodon.HenkinTermInterpretation
import Mettapedia.Logic.HOL.Syntax.PartialRenaming

/-!
# Typed strengthening for native eta reduction

Successful native removal of an unused term-variable level has an intrinsic
counterpart. Partial renaming reconstructs a term in the smaller context, and
ordinary weakening gives back the original typed term exactly. Native erasure
commutes with this operation, including below binders; no injectivity of the
partial erasure or extensional model law is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

variable {environment : Environment} {Γ Δ : Ctx Base} {τ σ : Ty Base}

private theorem native_dropAt?_db_succ (cutoff index : Nat) :
    Tm.dropAt? (cutoff + 1) (.db (index + 1)) =
      (Tm.dropAt? cutoff (.db index)).map (Tm.shift 0 1) := by
  by_cases below : index < cutoff
  · simp [Tm.dropAt?, below, show index + 1 < cutoff + 1 by omega, Tm.shift]
  · by_cases same : index = cutoff
    · subst index
      simp [Tm.dropAt?]
    · have above : cutoff < index := by omega
      have predecessor : index - 1 + 1 = index := by omega
      simp [Tm.dropAt?, below, same, show ¬ index + 1 < cutoff + 1 by omega,
        Tm.shift, predecessor]

private theorem lift_index_drop (ρ : PartialRename Base Γ Δ) (cutoff : Nat)
    (indexed : ∀ {a} (v : Var Γ a),
      (ρ v).map (fun target => Tm.db (variableIndex target)) =
        Tm.dropAt? cutoff (.db (variableIndex v))) :
    ∀ {a} (v : Var (σ :: Γ) a),
      (PartialRename.lift ρ v).map (fun target => Tm.db (variableIndex target)) =
        Tm.dropAt? (cutoff + 1) (.db (variableIndex v)) := by
  intro a v
  cases v with
  | vz => simp [PartialRename.lift, variableIndex, Tm.dropAt?]
  | vs v =>
      simp only [PartialRename.lift, variableIndex, Option.map_map,
        native_dropAt?_db_succ, ← indexed v]
      simp [Function.comp_def, variableIndex, Tm.shift]

private theorem option_binary_traverse {A B C D E : Type}
    (left : Option A) (right : Option B) (f : A → Option C) (g : B → Option D)
    (construct : C → D → E) :
    left.bind (fun x => right.bind (fun y =>
      (f x).bind (fun fx => (g y).bind (fun gy => some (construct fx gy))))) =
      (left.bind f).bind (fun fx => (right.bind g).bind (fun gy => some (construct fx gy))) := by
  cases left <;> cases right <;> simp

/-- Partial typed renaming implements the native drop whenever its variable
action implements the same index operation. Both sides retain real failure. -/
theorem erase_rename?_dropAt (term : Term (Constant environment) Γ τ)
    (ρ : PartialRename Base Γ Δ) (cutoff : Nat)
    (indexed : ∀ {a} (v : Var Γ a),
      (ρ v).map (fun target => Tm.db (variableIndex target)) =
        Tm.dropAt? cutoff (.db (variableIndex v))) :
    (rename? ρ term).bind erase = (erase term).bind (Tm.dropAt? cutoff) := by
  induction term generalizing Δ cutoff with
  | var v =>
      simpa only [rename?, erase, Option.bind_map, Option.bind_some,
        Function.comp_def, Option.map_eq_bind, Option.bind_assoc] using indexed v
  | const constant => cases constant <;> rfl
  | app function argument ihf iha | imp function argument ihf iha =>
      have functionComparison := ihf ρ cutoff indexed
      have argumentComparison := iha ρ cutoff indexed
      simp only [rename?, erase, Option.bind_eq_bind, Option.pure_def,
        Option.bind_assoc, Option.bind_some, Tm.dropAt?]
      rw [option_binary_traverse, option_binary_traverse, functionComparison, argumentComparison]
  | lam body ih | all body ih =>
      have bodyComparison := ih (PartialRename.lift ρ) (cutoff + 1)
        (lift_index_drop ρ cutoff indexed)
      simp only [rename?, erase, Option.bind_map, Function.comp_def,
        Option.bind_eq_bind, Option.pure_def, Option.bind_assoc, Option.bind_some, Tm.dropAt?]
      rw [← Option.bind_assoc, ← Option.bind_assoc, bodyComparison]
  | top | bot => rfl
  | and left right | or left right | eq left right =>
      simp only [rename?, erase]
      cases rename? ρ left <;> cases rename? ρ right <;> rfl
  | not body =>
      simp only [rename?, erase]
      cases rename? ρ body <;> rfl
  | ex body =>
      simp only [rename?, erase]
      cases rename? (PartialRename.lift ρ) body <;> rfl

/-- At the newest context entry, intrinsic strengthening erases to the native drop. -/
theorem erase_rename?_drop (term : Term (Constant environment) (σ :: Γ) τ) :
    (rename? PartialRename.drop term).bind erase = (erase term).bind (Tm.dropAt? 0) := by
  apply erase_rename?_dropAt
  intro a v
  cases v with
  | vz => rfl
  | vs v => simp [PartialRename.drop, variableIndex, Tm.dropAt?]

/-- A successful native drop reconstructs a smaller-context intrinsic term with
the exact contracted erasure and the original term as its weakening. -/
theorem erase_dropAt?_strengthen (term : Term (Constant environment) (σ :: Γ) τ)
    {raw contracted : Tm} (erased : erase term = some raw)
    (dropped : Tm.dropAt? 0 raw = some contracted) :
    ∃ lowered : Term (Constant environment) Γ τ,
      erase lowered = some contracted ∧ weaken lowered = term := by
  have comparison := erase_rename?_drop term
  rw [erased, Option.bind_some, dropped] at comparison
  obtain ⟨lowered, renamed, erasedLowered⟩ := Option.bind_eq_some_iff.mp comparison
  exact ⟨lowered, erasedLowered, weaken_of_rename?_drop renamed⟩

namespace StrengtheningExamples

def underBinder : Term (Constant {}) [.prop, .prop] (.arr .prop .prop) :=
  .lam (.var (.vs (.vs .vz)))

theorem native_drop_under_binder :
    Tm.dropAt? 0 (.lam .prop (.db 2)) = some (.lam .prop (.db 1)) := rfl

theorem reconstructed_under_binder :
    ∃ lowered : Term (Constant {}) [.prop] (.arr .prop .prop),
      erase lowered = some (.lam .prop (.db 1)) ∧ weaken lowered = underBinder :=
  erase_dropAt?_strengthen underBinder rfl native_drop_under_binder

/-- An occurrence of the removed variable below a binder is not discarded. -/
theorem captured_variable_not_droppable :
    Tm.dropAt? 0 (.lam .prop (.db 1)) = none := rfl

end StrengtheningExamples

#print axioms erase_rename?_dropAt
#print axioms erase_dropAt?_strengthen
#print axioms StrengtheningExamples.reconstructed_under_binder

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
