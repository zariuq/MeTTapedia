import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

/-!
# Recovering a contextual body along a variable spine

The spine may select and permute ambient variables. Its entries must be
distinct for inverse matching; forward application remains unrestricted.
Recovery renames selected indices back to parameter positions and verifies
scope and reconstruction. Completeness and uniqueness follow from the proved
left inverse on scoped bodies, including bodies with internal binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication

variable {Head : Type}

namespace Recovery

def indices? : List (Term Head) → Option (List Nat)
  | [] => some []
  | .idx i :: rest => (indices? rest).map (i :: ·)
  | .node _ _ :: _ => none

theorem indices?_map (indices : List Nat) :
    indices? (indices.map (Term.idx (Head := Head))) = some indices := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [indices?, ih]

theorem indices?_sound : ∀ (arguments : List (Term Head)) (indices : List Nat),
    indices? arguments = some indices → arguments = indices.map Term.idx
  | [], indices, success => by simpa [indices?] using success.symm
  | .idx i :: rest, indices, success => by
      cases found : indices? rest with
      | none => simp [indices?, found] at success
      | some tail =>
        have same : i :: tail = indices := by simpa [indices?, found] using success
        subst indices
        simp [indices?_sound rest tail found]
  | .node _ _ :: _, _, success => by simp [indices?] at success

/-- This rename puts an unlisted index at the first out-of-scope parameter. -/
def inverse (indices : List Nat) (target : Term Head) : Term Head :=
  Term.renameMany (fun i => indices.idxOf i) target

theorem inverse_graft {indices : List Nat} (distinct : indices.Nodup)
    {body target : Term Head}
    (applied : graft indices.length (indices.map Term.idx) body = some target) :
    inverse indices target = body := by
  unfold graft at applied
  split at applied
  · rename_i qualified
    have same := Option.some.inj applied
    rw [← same]
    unfold inverse
    rw [Term.renameMany_substitute]
    calc
      Term.substituteMany
          (fun i => Term.renameMany (fun j => indices.idxOf j)
            (argumentAt (indices.map Term.idx) i)) body =
          Term.substituteMany Term.idx body := by
        apply Term.substituteMany_congr_scoped _ body qualified.2
        intro i inside
        have position := distinct.idxOf_getElem i inside
        simpa [argumentAt, List.getElem?_eq_getElem inside,
          List.getElem?_eq_getElem (show i < (indices.map (Term.idx (Head := Head))).length by
            simpa using inside)] using congrArg (Term.idx (Head := Head)) position
      _ = body := Term.substituteMany_ids body
  · cases applied

theorem graft_unique {indices : List Nat} (distinct : indices.Nodup)
    {first second target : Term Head}
    (left : graft indices.length (indices.map Term.idx) first = some target)
    (right : graft indices.length (indices.map Term.idx) second = some target) : first = second :=
  (inverse_graft distinct left).symm.trans (inverse_graft distinct right)

variable [DecidableEq Head]

def recover (arity : Nat) (arguments : List (Term Head)) (target : Term Head) : Option (Term Head) := do
  let indices ← indices? arguments
  if indices.length = arity ∧ indices.Nodup then
    let body := inverse indices target
    if graft arity arguments body = some target then some body else none
  else none

theorem recover_sound {arity : Nat} {arguments : List (Term Head)} {target body : Term Head}
    (recovered : recover arity arguments target = some body) :
    graft arity arguments body = some target := by
  unfold recover at recovered
  cases found : indices? arguments with
  | none => simp [found] at recovered
  | some indices =>
    simp only [found] at recovered
    change (if indices.length = arity ∧ indices.Nodup then
      if graft arity arguments (inverse indices target) = some target then
        some (inverse indices target) else none else none) = some body at recovered
    split at recovered
    · split at recovered
      · rename_i forward
        cases recovered
        exact forward
      · cases recovered
    · cases recovered

theorem recover_complete {indices : List Nat} (distinct : indices.Nodup)
    {target body : Term Head}
    (applied : graft indices.length (indices.map Term.idx) body = some target) :
    recover indices.length (indices.map Term.idx) target = some body := by
  have inverseEq := inverse_graft distinct applied
  simp [recover, indices?_map, distinct, inverseEq, applied]

/-- Executable inverse matching is exact for every injective variable spine. -/
theorem recover_exact {indices : List Nat} (distinct : indices.Nodup)
    (target body : Term Head) :
    recover indices.length (indices.map Term.idx) target = some body ↔
      graft indices.length (indices.map Term.idx) body = some target :=
  ⟨recover_sound, recover_complete distinct⟩

theorem recover_refuses_iff {indices : List Nat} (distinct : indices.Nodup) (target : Term Head) :
    recover indices.length (indices.map Term.idx) target = none ↔
      ¬∃ body, graft indices.length (indices.map Term.idx) body = some target := by
  constructor
  · intro refused ⟨body, applied⟩
    have found := recover_complete distinct applied
    rw [refused] at found
    cases found
  · intro noBody
    cases found : recover indices.length (indices.map Term.idx) target with
    | none => rfl
    | some body => exact False.elim (noBody ⟨body, recover_sound found⟩)

namespace Controls

def pair (a b : Term Nat) : Term Nat := .node 2 (.cons 0 a (.cons 0 b .nil))
def lam (body : Term Nat) : Term Nat := .node 1 (.cons 1 body .nil)

theorem reversed_spine_recovers :
    recover 2 [.idx 2, .idx 0] (pair (.idx 0) (.idx 2)) =
      some (pair (.idx 1) (.idx 0)) := by decide

theorem unused_parameter_retained :
    recover 2 [.idx 2, .idx 0] (.idx 0 : Term Nat) = some (.idx 1) := by decide

theorem unlisted_dependency_refused :
    recover 2 [.idx 2, .idx 0] (.idx 1 : Term Nat) = none := by decide

theorem recovery_under_binder :
    recover 1 [.idx 2] (lam (pair (.idx 0) (.idx 3))) =
      some (lam (pair (.idx 0) (.idx 1))) := by decide

theorem repeated_input_spine_refused :
    recover 2 [.idx 0, .idx 0] (.idx 0 : Term Nat) = none := by decide

theorem repeated_output_spine_applies :
    graft 2 [.idx 0, .idx 0] (pair (.idx 0) (.idx 1)) =
      some (pair (.idx 0) (.idx 0)) := by decide

end Controls
end Recovery
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
