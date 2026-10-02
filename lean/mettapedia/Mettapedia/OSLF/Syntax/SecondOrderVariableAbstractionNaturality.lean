import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstraction

/-!
# Naturality of fresh-variable abstraction

Changing the original metavariable assignment retains every newly introduced
nullary declaration. Abstraction and restoration commute with that assignment
for arbitrary dependency contexts, sorts, and operator binder lists.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction

open Mettapedia.OSLF.Binding

variable {S : Signature} {M N : List (MetaArity S)}

/-- Extend an assignment by retaining the newly introduced nullary declaration. -/
def liftHeadAssignment (a : S.Srt)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    (i : Fin (headMetas a M).length) →
      Term (withMetas S (headMetas a N))
        ((headMetas a M).get i).1 ((headMetas a M).get i).2
  | ⟨0, _⟩ => fresh (S := S) (M := N) a []
  | ⟨n + 1, h⟩ => shift (S := S) (M := N) a (body ⟨n, Nat.lt_of_succ_lt_succ h⟩)

/-- Inclusion is natural under every old-metavariable assignment. -/
theorem shift_instInto (a : S.Srt)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S M) Γ s) :
    instInto (liftHeadAssignment a body) (shift (S := S) (M := M) a t) =
      shift (S := S) (M := N) a (instInto body t) := by
  unfold shift
  rw [instInto_instInto, instInto_instInto]
  congr 1
  funext i
  exact instInto_metaVar (liftHeadAssignment a body) i.succ

theorem instInto_closeHead (a : S.Srt)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (Γ : Ctx S) :
    (fun s v => instInto (liftHeadAssignment a body) (closeHead (S := S) (M := M) a Γ s v)) =
      closeHead (S := S) (M := N) a Γ := by
  funext s v
  cases v <;> rfl

/-- One-variable abstraction commutes with arbitrary substitution of the old
metavariables; the fresh declaration itself is preserved. -/
theorem abstractHead_instInto
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {a s : S.Srt} {Γ : Ctx S} (t : Term (withMetas S M) (a :: Γ) s) :
    abstractHead (S := S) (M := N) (instInto body t) =
      instInto (liftHeadAssignment a body) (abstractHead (S := S) (M := M) t) := by
  unfold abstractHead
  rw [instInto_bind, instInto_closeHead (S := S) (M := M) (N := N) a body Γ,
    shift_instInto (S := S) (M := M) (N := N) a body t]

/-- Restoration is natural too, obtained from the already checked inverse law. -/
theorem openHead_instInto
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {a s : S.Srt} {Γ : Ctx S} (t : Term (withMetas S (headMetas a M)) Γ s) :
    openHead (S := S) (M := N) (instInto (liftHeadAssignment a body) t) =
      instInto body (openHead (S := S) (M := M) t) := by
  apply (headEquiv (S := S) (M := N) a s Γ).injective
  change abstractHead (openHead (instInto (liftHeadAssignment a body) t)) =
    abstractHead (instInto body (openHead (S := S) (M := M) t))
  rw [abstractHead_openHead, abstractHead_instInto, abstractHead_openHead]

/-- Extend an assignment by retaining all fresh declarations for Γ. -/
def liftAssignment {S : Signature} {M N : List (MetaArity S)} : (Γ : Ctx S) →
    ((i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) →
    (i : Fin (extendedMetas Γ M).length) →
      Term (withMetas S (extendedMetas Γ N))
        ((extendedMetas Γ M).get i).1 ((extendedMetas Γ M).get i).2
  | [], body => body
  | a :: Γ, body => liftAssignment (S := S) (M := headMetas a M) (N := headMetas a N)
      Γ (liftHeadAssignment a body)

/-- Full abstraction is natural for every old-metavariable assignment. -/
theorem abstractVars_instInto
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (Γ : Ctx S) {s : S.Srt} (t : Term (withMetas S M) Γ s) :
    abstractVars (S := S) (M := N) (instInto body t) =
      instInto (liftAssignment Γ body) (abstractVars (S := S) (M := M) t) := by
  induction Γ generalizing M N with
  | nil => rfl
  | cons a Γ ih =>
      change abstractVars (S := S) (M := headMetas a N)
          (abstractHead (S := S) (M := N) (instInto body t)) =
        instInto (liftAssignment Γ (liftHeadAssignment a body))
          (abstractVars (S := S) (M := headMetas a M) (abstractHead (S := S) (M := M) t))
      rw [abstractHead_instInto]
      exact ih (liftHeadAssignment a body) (abstractHead (S := S) (M := M) t)

/-- Full restoration commutes with changing the old metavariable assignment. -/
theorem restoreVars_instInto
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (Γ : Ctx S) {s : S.Srt}
    (t : Term (withMetas S (extendedMetas Γ M)) [] s) :
    restoreVars (S := S) (M := N) (Γ := Γ) (instInto (liftAssignment Γ body) t) =
      instInto body (restoreVars (S := S) (M := M) (Γ := Γ) t) := by
  apply (variablesEquiv (S := S) Γ N s).injective
  change abstractVars (restoreVars (S := S) (M := N) (Γ := Γ)
      (instInto (liftAssignment Γ body) t)) =
    abstractVars (instInto body (restoreVars (S := S) (M := M) (Γ := Γ) t))
  rw [abstractVars_restoreVars, abstractVars_instInto, abstractVars_restoreVars]

/-- Retaining fresh variables sends the identity old-metavariable assignment
to the identity assignment of the full extended context. -/
theorem liftHeadAssignment_id (a : S.Srt) :
    liftHeadAssignment (S := S) (M := M) (N := M) a (fun i => metaVar i) =
      fun i => metaVar (S := S) (M := headMetas a M) i := by
  funext i
  rcases i with ⟨_ | n, h⟩
  · rfl
  · change shift (S := S) (M := M) a (metaVar ⟨n, Nat.lt_of_succ_lt_succ h⟩) = _
    exact instInto_metaVar (shiftAssignment a) _

/-- Extending old-metavariable assignments commutes with their actual
metavariable substitution composition. -/
theorem liftHeadAssignment_comp {L : List (MetaArity S)} (a : S.Srt)
    (first : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (later : (i : Fin N.length) → Term (withMetas S L) (N.get i).1 (N.get i).2) :
    liftHeadAssignment a (fun i => instInto later (first i)) =
      fun i => instInto (liftHeadAssignment a later) (liftHeadAssignment a first i) := by
  funext i
  rcases i with ⟨_ | n, h⟩
  · rfl
  · exact (shift_instInto a later (first ⟨n, Nat.lt_of_succ_lt_succ h⟩)).symm

/-- All fresh declarations are retained by the extended identity assignment. -/
theorem liftAssignment_id (Γ : Ctx S) :
    liftAssignment (S := S) (M := M) (N := M) Γ (fun i => metaVar i) =
      fun i => metaVar (S := S) (M := extendedMetas Γ M) i := by
  induction Γ generalizing M with
  | nil => rfl
  | cons a Γ ih =>
    change liftAssignment Γ (liftHeadAssignment a (fun i => metaVar (S := S) (M := M) i)) = _
    rw [liftHeadAssignment_id]
    exact ih

/-- Retaining a whole variable context is functorial for arbitrary,
possibly noninjective old-metavariable assignments. -/
theorem liftAssignment_comp {L : List (MetaArity S)} (Γ : Ctx S)
    (first : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (later : (i : Fin N.length) → Term (withMetas S L) (N.get i).1 (N.get i).2) :
    liftAssignment Γ (fun i => instInto later (first i)) =
      fun i => instInto (liftAssignment Γ later) (liftAssignment Γ first i) := by
  induction Γ generalizing M N L with
  | nil => rfl
  | cons a Γ ih =>
    change liftAssignment Γ (liftHeadAssignment a (fun i => instInto later (first i))) = _
    rw [liftHeadAssignment_comp]
    exact ih (liftHeadAssignment a first) (liftHeadAssignment a later)

end Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction
