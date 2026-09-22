import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.ReductionViewIndexedModalities

/-!
# Independent coordinates of operational space views

An operational view declares residency, a reduction carrier, a transition
handler, and a store observation separately.  The generic inert and
rewrite-triggered views use the same list occurrence store, reduction view
and observation.  Their transition handlers remain distinct authored data.

Rewrite receipts retain the exact successor family computed by the supplied
language and environment.  Concrete firing and non-firing specimens belong
to the application layer; no language-specific activation policy is chosen
by this interface.
-/


open Mettapedia.OSLF.Framework
set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace SpaceOperationalViewBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open ReductionViewIndexedModalities

universe uStore uObservation uReceipt

/-- A narrow operational view over one store.  The record deliberately does
not prescribe a final taxonomy of spaces; it separates residency, reduction,
activation and observation as independently supplied coordinates. -/
structure OperationalView (language : LanguageDef)
    (Store : Type uStore) (Observation : Type uObservation)
    (Receipt : Type uReceipt) where
  reduction : ReductionView language
  resident : Store → Pattern → Prop
  step : Store → Pattern → Store → Receipt → Prop
  observe : Store → Observation

namespace OperationalView

def CanFire {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (view : OperationalView language Store Observation Receipt)
    (store : Store) (occurrence : Pattern) : Prop :=
  ∃ next receipt, view.step store occurrence next receipt

/-- Two operational views expose the same resident occurrences and the same
store observation.  Their transition handlers are intentionally absent from
this relation. -/
def SameVisibleSubstrate {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (first second : OperationalView language Store Observation Receipt) : Prop :=
  (∀ store occurrence,
      first.resident store occurrence ↔ second.resident store occurrence) ∧
    (∀ store, first.observe store = second.observe store)

end OperationalView

/-! ## Generic inert and rewrite-triggered views -/

/-- A proof-carrying exact engine step. -/
structure RewriteReceipt (language : LanguageDef) (environment : RelationEnv)
    (depth : Nat) where
  source : Pattern
  successors : List Pattern
  exact : successors =
    rewriteAt (engineBasePremises environment) language depth source

def inertView (language : LanguageDef) (reduction : ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    OperationalView language (List Pattern) (List Pattern)
      (RewriteReceipt language environment depth) where
  reduction := reduction
  resident := fun store occurrence => occurrence ∈ store
  step := fun _store _occurrence _next _receipt => False
  observe := id

/-- A one-cell triggered view.  Firing replaces the selected resident source
with the exact nonempty successor occurrence list carried by its receipt. -/
def rewriteTriggeredView (language : LanguageDef)
    (reduction : ReductionView language) (environment : RelationEnv)
    (depth : Nat) :
    OperationalView language (List Pattern) (List Pattern)
      (RewriteReceipt language environment depth) where
  reduction := reduction
  resident := fun store occurrence => occurrence ∈ store
  step := fun store occurrence next receipt =>
    store = [occurrence] ∧
      receipt.source = occurrence ∧
      next = receipt.successors ∧
      receipt.successors ≠ []
  observe := id

theorem inert_and_triggered_same_visible_substrate
    (language : LanguageDef) (reduction : ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    OperationalView.SameVisibleSubstrate
      (inertView language reduction environment depth)
      (rewriteTriggeredView language reduction environment depth) := by
  constructor
  · intro store occurrence
    rfl
  · intro store
    rfl

theorem inert_and_triggered_same_reduction
    (language : LanguageDef) (reduction : ReductionView language)
    (environment : RelationEnv) (depth : Nat) :
    (inertView language reduction environment depth).reduction =
      (rewriteTriggeredView language reduction environment depth).reduction :=
  rfl

#print axioms inert_and_triggered_same_visible_substrate
#print axioms inert_and_triggered_same_reduction

end SpaceOperationalViewBoundary
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
