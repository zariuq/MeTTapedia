import Mettapedia.GSLT.Core.GSLT
import Mettapedia.Languages.OpenTheory.TheoryClosure
import Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
import Mettapedia.Languages.OpenTheory.TheoryClosureCanary

/-!
# OpenTheory primitives as a GSLT on theorem lists

A bare `GSLT` rewrite is binary on one carrier. Multi-premise kernel rules
(`app`, `eqMp`, `deductAntisym`) therefore live in the *state*, exactly as
propositional resolution stores both parent clauses in a CNF: the term is a
list of theorems, and one rewrite adds a conclusion whose premises are already
in the list.

This is the native OpenTheory kernel as a GSLT consumer. It is not a
LanguageDef, not HOL Light, not HOL4, and not a world-model query machine
(`Logic.WorldModel.GSLTRealization`). Those are other GSLTs. A morphism from
theorems to world-model states would be an interpretation, not an
identification, and is not claimed here.

INV-010: steps are `PrimitiveStep` / `checkPrimitive`, not a hidden relation
query. INV-011: this is the OpenTheory milestone, not a named HOL system.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.OperationalGSLT

open Mettapedia.GSLT
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.TheoryClosureCanary
open Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures

/-- One GSLT step: apply a policy-qualified primitive whose premises already
sit in the current theorem list, and cons the conclusion. -/
inductive Expand (policy : AxiomPolicy) :
    List Theorem → List Theorem → Prop where
  | cons (request : PrimitiveRequest) (out : Theorem) (Γ : List Theorem)
      (hmem : ∀ t ∈ request.premises, t ∈ Γ)
      (hpol : request.InputAxiomsAllowed policy)
      (hstep : PrimitiveStep request out) :
      Expand policy Γ (out :: Γ)

def openTheoryGSLT (policy : AxiomPolicy) : GSLT where
  Term := List Theorem
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Expand policy
  rewrites_resp_left := by
    intro t t' u htt step
    exact ⟨u, htt ▸ step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step huu
    exact huu ▸ step

theorem step_iff_expand (policy : AxiomPolicy) (Γ Δ : List Theorem) :
    (openTheoryGSLT policy).Step Γ Δ ↔ Expand policy Γ Δ :=
  Iff.rfl

/-- The GSLT step is exactly a `PolicyPrimitiveRule` whose premises are
members of the current list. -/
theorem expand_iff_rule (policy : AxiomPolicy) {Γ Δ : List Theorem} :
    Expand policy Γ Δ ↔
      ∃ (request : PrimitiveRequest) (out : Theorem),
        Δ = out :: Γ ∧
          (∀ t ∈ request.premises, t ∈ Γ) ∧
            PolicyPrimitiveRule policy request.premises out := by
  constructor
  · rintro ⟨request, out, Γ, hmem, hpol, hstep⟩
    exact ⟨request, out, rfl, hmem, ⟨request, rfl, hpol, hstep⟩⟩
  · rintro ⟨request, out, rfl, hmem, ⟨request', hprem, hpol, hstep⟩⟩
    refine Expand.cons request' out Γ ?_ hpol hstep
    intro t ht
    exact hmem t (hprem ▸ ht)

theorem expand_preserves_authorized (policy : AxiomPolicy)
    {Γ Δ : List Theorem} (step : Expand policy Γ Δ)
    (hΓ : ∀ t ∈ Γ, policy.AllowsTheorem t) :
    ∀ t ∈ Δ, policy.AllowsTheorem t := by
  intro t ht
  cases step with
  | cons request out Γ hmem hpol hstep =>
      have hmemΔ : t = out ∨ t ∈ Γ := List.mem_cons.mp ht
      rcases hmemΔ with rfl | hΓt
      · exact (PolicyPrimitiveRule.outputAxiomsAllowed policy
          ⟨request, rfl, hpol, hstep⟩)
      · exact hΓ t hΓt

/-- Nullary primitive steps start from the empty list, matching
`derives_of_nullary_check`. -/
theorem expand_nullary (policy : AxiomPolicy)
    (request : PrimitiveRequest) (out : Theorem)
    (nullary : request.premises = [])
    (hpol : request.InputAxiomsAllowed policy)
    (hstep : PrimitiveStep request out) :
    Expand policy [] [out] := by
  refine Expand.cons request out [] ?_ hpol hstep
  intro t ht
  rw [nullary] at ht
  cases ht

theorem expand_nullary_derives (policy : AxiomPolicy)
    (request : PrimitiveRequest) (out : Theorem)
    (nullary : request.premises = [])
    (hpol : request.InputAxiomsAllowed policy)
    (hstep : PrimitiveStep request out) :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out :=
  derives_of_nullary_check policy request out nullary hpol
    ((checkPrimitive_eq_some_iff request out).mpr hstep)

/-! ## Canaries: the `onlyP` fixture -/

theorem onlyP_expands_axiomP :
    Expand onlyP [] [axiomP] :=
  expand_nullary onlyP (.core (.axiom boolSequentP)) axiomP rfl
    onlyP_allows_axiomP
    ((checkPrimitive_eq_some_iff _ _).mp bareKernel_accepts_axiomP)

theorem onlyP_step_axiomP :
    (openTheoryGSLT onlyP).Step [] [axiomP] :=
  onlyP_expands_axiomP

/-- Negative: the disallowed axiom is not a GSLT step from the empty theory. -/
theorem onlyP_does_not_expand_axiomQ :
    ¬ Expand onlyP [] [axiomQ] := by
  intro h
  have hauth := expand_preserves_authorized onlyP h (fun t ht => nomatch ht)
  exact onlyP_disallows_axiomQ_provenance (hauth axiomQ (by simp))

#print axioms expand_iff_rule
#print axioms expand_preserves_authorized
#print axioms onlyP_expands_axiomP
#print axioms onlyP_does_not_expand_axiomQ

end Mettapedia.Languages.OpenTheory.OperationalGSLT
