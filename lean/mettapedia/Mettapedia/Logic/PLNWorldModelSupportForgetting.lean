import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.GenericWorldModelForgetting

/-!
# Support-Tracked WM Forgetting Layer

Positive counterpart to scoped forgetting no-go theorems:

- extend the existing `ForgettingLayer` with explicit support/scope footprints;
- require exact inverse forgetting under support containment;
- derive outside-scope zero-evidence consequence from that exact inverse law.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

variable {State Scope Query Ev Supp : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]

/-- Forgetting layer enriched with support tracking and exact inverse law under
support containment. -/
structure SupportTrackedForgettingLayer (State Scope Query Ev Supp : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]
    extends ForgettingLayer State Scope Query Ev where
  scopeFootprint : Scope → Finset Supp
  support : State → Query → Finset Supp
  exactInverse_of_supported :
    ∀ {S Δ}, (∀ q, support Δ q ⊆ scopeFootprint S) →
      ∀ W : State, forget S (W + Δ) = W

namespace SupportTrackedForgettingLayer

variable {State Scope Query Ev Supp : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [GenericWorldModel State Query Ev]

theorem exactInverse_revision_of_support_subset
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {Δ : State}
    (hsupp : ∀ q, F.support Δ q ⊆ F.scopeFootprint S) :
    ∀ W : State, F.forget S (W + Δ) = W :=
  F.exactInverse_of_supported hsupp

theorem exactInverse_revision_supported_outside_zero
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hsupp : ∀ q, F.support Δ q ⊆ F.scopeFootprint S) :
    ∀ q, ¬ F.inScope S q →
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 := by
  intro q hout
  exact ForgettingLayer.exactInverse_revision_supported
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F.toForgettingLayer hzero (F.exactInverse_of_supported hsupp) q hout

theorem no_exactInverse_revision_of_nonzero_outside_scope_of_supported
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State} {q : Query}
    (hsupp : ∀ q, F.support Δ q ⊆ F.scopeFootprint S)
    (hout : ¬ F.inScope S q)
    (hne :
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) Δ q ≠ 0) :
    False := by
  exact
    (ForgettingLayer.no_exactInverse_revision_of_nonzero_outside_scope
      (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
      F.toForgettingLayer hzero hout hne)
      (F.exactInverse_of_supported hsupp)

end SupportTrackedForgettingLayer
end Mettapedia.Logic
