import Mettapedia.Languages.OpenTheory.OperationalGSLTAdequacy
import Mettapedia.Logic.WorldModel.Basic

/-!
# Theorem lists as a world of facts

A policy-qualified OpenTheory derivation is a growing list of theorems.
That list is a world-model *state*: empty is `[]`, revision is append,
extraction is membership.  A kernel `Expand` step is one such revision
(`[t] ++ Γ`).  The converse is false: append does not check primitives.

This is an interpretation, not an identification with
`Logic.WorldModel.GSLTRealization` query machines, and it is not HOL
support.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.WorldModelInterpretation

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.OperationalGSLT
open Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures

instance theoremListWorld : MonoidalWorldModel (List Theorem) Theorem Prop where
  revise := List.append
  empty := []
  extract := fun Γ t => t ∈ Γ
  revise_assoc := List.append_assoc
  revise_empty_left := List.nil_append
  revise_empty_right := List.append_nil

@[simp] theorem revise_eq_append (xs ys : List Theorem) :
    theoremListWorld.revise xs ys = xs ++ ys :=
  rfl

@[simp] theorem empty_eq_nil : theoremListWorld.empty = [] :=
  rfl

@[simp] theorem extract_eq_mem (Γ : List Theorem) (t : Theorem) :
    theoremListWorld.extract Γ t = (t ∈ Γ) :=
  rfl

section
variable (policy : AxiomPolicy)

theorem expand_is_revise {Γ Δ : List Theorem} (h : Expand policy Γ Δ) :
    ∃ t : Theorem, Δ = theoremListWorld.revise [t] Γ := by
  obtain ⟨t, hEq⟩ := expand_cons_eq policy h
  exact ⟨t, hEq⟩

theorem expand_preserves_extract {Γ Δ : List Theorem}
    (h : Expand policy Γ Δ) (t : Theorem) :
    theoremListWorld.extract Γ t → theoremListWorld.extract Δ t :=
  expand_persists policy h t

theorem derived_is_extractable {t : Theorem}
    (h : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) t) :
    ∃ Γ : List Theorem,
      (openTheoryGSLT policy).MultiStep theoremListWorld.empty Γ ∧
        theoremListWorld.extract Γ t :=
  reachable_of_derives policy h

end

/-- Append will cons any theorem.  The `onlyP` kernel will not. -/
theorem revise_is_not_the_kernel :
    ¬ ∀ (t : Theorem) (Γ : List Theorem), Expand onlyP Γ (t :: Γ) := by
  intro h
  exact onlyP_does_not_expand_axiomQ (h axiomQ [])

#print axioms expand_is_revise
#print axioms expand_preserves_extract
#print axioms revise_is_not_the_kernel
#print axioms derived_is_extractable

end Mettapedia.Languages.OpenTheory.WorldModelInterpretation
