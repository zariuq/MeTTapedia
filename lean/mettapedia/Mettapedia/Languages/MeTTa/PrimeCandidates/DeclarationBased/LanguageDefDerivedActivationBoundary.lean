import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceActivationPolicyBoundary

/-!
# LanguageDef-derived rewrite activation

The authored language determines the exact rewrite successor family of a
pattern.  A space policy separately determines whether a resident occurrence
may request that rewrite.

For the generated unary rewrite fragment, a singleton occurrence can fire
exactly when the presentation-derived successor family is nonempty.  Every
transition receipt retains that exact family.  The construction grants no
binary communication, scheduling, resource, or external-effect authority.
Other capabilities require their own checked boundaries.
-/


open Mettapedia.OSLF.Framework
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace LanguageDefDerivedActivationBoundary

open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open SpaceActivationPolicyBoundary
open SpaceOperationalViewBoundary

/-- The generic one-cell rewrite view satisfies the resident-source
obligation required by the activation-policy interface. -/
theorem rewriteTriggered_residentSound
    (language : LanguageDef) (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    ResidentSound (rewriteTriggeredView language reduction environment depth) := by
  intro store occurrence next receipt step
  rw [step.1]
  simp [rewriteTriggeredView]

/-- The unary rewrite capability generated from one checked language
presentation.  It exposes only explicit requested activation. -/
def generatedRewritePolicy
    (language : LanguageDef) (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat) :=
  ofOperationalView (rewriteTriggeredView language reduction environment depth)
    (rewriteTriggered_residentSound language reduction environment depth)

/-- Firing the generated policy returns exactly the successor family computed
from the authored `LanguageDef` and relation environment. -/
theorem fired_is_exact_language_rewrite
    {language : LanguageDef}
    {reduction : ReductionViewIndexedModalities.ReductionView language}
    {environment : RelationEnv} {depth : Nat}
    {source : Pattern} {next : List Pattern}
    {receipt : RewriteReceipt language environment depth}
    (fired :
      (generatedRewritePolicy language reduction environment depth).step
        [source] (.requested () source) next receipt) :
    receipt.source = source ∧
      next = rewriteAt (engineBasePremises environment) language depth source := by
  have receiptExact := receipt.exact
  rw [fired.2.1] at receiptExact
  exact ⟨fired.2.1, fired.2.2.1.trans receiptExact⟩

/-- On a singleton store, explicit rewrite activation exists exactly when the
presentation-derived successor family is nonempty. -/
theorem canFire_singleton_iff_rewriteAt_nonempty
    (language : LanguageDef)
    (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat) (source : Pattern) :
    (generatedRewritePolicy language reduction environment depth).CanFire
        [source] (.requested () source) ↔
      rewriteAt (engineBasePremises environment) language depth source ≠ [] := by
  constructor
  · rintro ⟨next, receipt, fired⟩
    intro successorsEmpty
    have receiptExact := receipt.exact
    rw [fired.2.1] at receiptExact
    exact fired.2.2.2 (receiptExact.trans successorsEmpty)
  · intro successorsNonempty
    let successors :=
      rewriteAt (engineBasePremises environment) language depth source
    let receipt : RewriteReceipt language environment depth := {
      source := source
      successors := successors
      exact := rfl }
    exact ⟨successors, receipt, rfl, rfl, rfl, successorsNonempty⟩

/-- The presentation-derived unary fragment does not gain rho-style
communication merely because its rewrite relation is executable. -/
theorem generatedRewritePolicy_no_communication
    (language : LanguageDef)
    (reduction : ReductionViewIndexedModalities.ReductionView language)
    (environment : RelationEnv) (depth : Nat)
    (store : List Pattern) (sender receiver : Pattern) :
    ¬ (generatedRewritePolicy language reduction environment depth).CanFire
        store (.communication sender receiver) :=
  no_communication_fire
    (rewriteTriggeredView language reduction environment depth)
    (rewriteTriggered_residentSound language reduction environment depth)
    store sender receiver

#print axioms rewriteTriggered_residentSound
#print axioms fired_is_exact_language_rewrite
#print axioms canFire_singleton_iff_rewriteAt_nonempty
#print axioms generatedRewritePolicy_no_communication

end LanguageDefDerivedActivationBoundary
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
