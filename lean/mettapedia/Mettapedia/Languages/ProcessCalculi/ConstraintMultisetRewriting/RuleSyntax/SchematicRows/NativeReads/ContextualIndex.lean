import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeMatchKernel

/-!
# Stable-head retrieval for the existing binding-aware source terms

Original signature operators remain rigid through contextual instantiation.
Metavariable operators remain candidates even when applied to bound variables;
their images may be arbitrarily nested binder terms. Stored row equations
are not discarded: the exclusion proof uses the actual `rowUse` problem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ContextualIndex

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {V W Z : Type}
  {source : V → MetaArity S} {other : W → MetaArity S} {target : Z → MetaArity S}
  {Γ : Ctx S} {sort : S.Srt}

def head : Term (signature S source) Γ sort → Option (S.Op sort)
  | .var _ => none
  | .op (.inl original) _ => some original
  | .op (.inr _) _ => none

theorem head_preserved (point : Assignment source target)
    (term : Term (signature S source) Γ sort) (operator : S.Op sort)
    (known : head term = some operator) : head (instantiate point term) = some operator := by
  match term, known with
  | .var _, impossible => nomatch impossible
  | .op (.inl _) _, same => exact same
  | .op (.inr _) _, impossible => nomatch impossible

variable [DecidableEq (S.Op sort)]

def permits (pattern : Term (signature S source) Γ sort)
    (row : Term (signature S other) Γ sort) : Bool :=
  match head pattern, head row with
  | some first, some second => decide (first = second)
  | _, _ => true

theorem permits_of_instances (pattern : Term (signature S source) Γ sort)
    (row : Term (signature S other) Γ sort)
    (caller : Assignment source target) (locals : Assignment other target)
    (same : instantiate caller pattern = instantiate locals row) : permits pattern row = true := by
  cases hp : head pattern with
  | none => simp [permits, hp]
  | some first =>
      cases hr : head row with
      | none => simp [permits, hp, hr]
      | some second =>
          have keys := (head_preserved caller pattern first hp).symm.trans
            ((congrArg head same).trans (head_preserved locals row second hr))
          have equal := Option.some.inj keys
          simp [permits, hp, hr, equal]

variable {κ : Keys S}

theorem row_problem_survives (scope : Nat) (store : List (Constraint κ Γ sort))
    (pattern : Data κ Γ sort) (row : SourceLanguage.Row κ Γ sort)
    (solvable : Solvable (store ++ rowUse scope row pattern)) : permits pattern row.atom = true := by
  obtain ⟨Names, declaration, point, known⟩ := solvable
  have member : (pattern, instantiate (copyAt κ scope) row.atom) ∈
      store ++ rowUse scope row pattern :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _))
  have same := known _ member
  have composed : instantiate point pattern =
      instantiate (Assignment.compose point (copyAt κ scope)) row.atom := by
    rw [Assignment.instantiate_compose]
    exact same
  exact permits_of_instances pattern row.atom point (Assignment.compose point (copyAt κ scope)) composed

theorem rejected_problem_unsolvable (scope : Nat) (store : List (Constraint κ Γ sort))
    (pattern : Data κ Γ sort) (row : SourceLanguage.Row κ Γ sort)
    (rejected : permits pattern row.atom = false) :
    ¬ Solvable (store ++ rowUse scope row pattern) := by
  intro solvable
  have accepted := row_problem_survives scope store pattern row solvable
  rw [rejected] at accepted
  cases accepted

#print axioms head_preserved
#print axioms permits_of_instances
#print axioms row_problem_survives
#print axioms rejected_problem_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ContextualIndex
