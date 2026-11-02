import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUpdate

/-!
# Discharge structurally identical contextual equations

Reflexivity solves an equation without constraining its holes or creating a
fresh declaration family. The executable check compares existing binding
terms after verifying context and result-sort metadata. Repeated and
compound applications are included; no uniquely recoverable spine is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexive

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} [DecidableEq V] {source : V → MetaArity S}

def discharge {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    ContextualFrameUpdate.Update [(observe term, observe term)] :=
  ⟨V, inferInstance, source, generator source, [], by
    constructor
    · intro Next next candidate _ equation member
      have same := List.mem_singleton.mp member
      subst equation
      rfl
    · intro Next next candidate _
      exact ⟨candidate, (fun _ member => False.elim (List.not_mem_nil member)),
        fun identity => (instantiate_generator candidate identity).symm⟩⟩

def tryTerms [∀ sort, DecidableEq (S.Op sort)] {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S source) Γ sort) :
    Option (ContextualFrameUpdate.Update [(observe left, observe right)]) := by
  letI (result : S.Srt) : DecidableEq ((signature S source).Op result) :=
    inferInstanceAs (DecidableEq (S.Op result ⊕ Operator source result))
  by_cases same : left = right
  · subst right
    exact some (discharge left)
  · exact none

theorem tryTerms_accepted_iff [∀ sort, DecidableEq (S.Op sort)]
    {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort) :
    (tryTerms left right).isSome = true ↔ left = right := by
  by_cases same : left = right
  · subst right
    simp [tryTerms]
  · simp [tryTerms, same]

def tryEquation [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (equation : Equation (Observation S source)) : Option (ContextualFrameUpdate.Update [equation]) := by
  rcases equation with ⟨⟨Γ, sort, left⟩, ⟨Δ, result, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = result
    · subst result
      exact tryTerms left right
    · exact none
  · exact none

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexive
