import Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting
import Mettapedia.PLN.WorldModel.WorldModelConservationPack

/-!
# Forgetting laws: no manufactured evidence, and support-closed deletion

The existing forgetting layer fixes idempotence and invariance outside the
forgotten scope.  Those two laws leave the operation almost entirely open
inside the scope: a layer that resets in-scope claims to a prior satisfies
both.  Two further laws close that gap for a world model whose readouts are
evidence.

* **No manufactured evidence.**  Forgetting never increases the extracted
  evidence of any query, in the evidence order.  Zeroing evidence in scope is
  allowed; resetting to a prior or redistributing counts is not.  Under this
  law every observation count is non-increasing, so confidence can only fall.

* **Support-closed deletion.**  With support tracking, the support retained
  after forgetting is part of the earlier support and avoids the forgotten
  footprint, and nonzero evidence always has nonempty support.  Consequently
  every conclusion supported only inside the footprint is deleted, and every
  surviving conclusion keeps a derivation that does not pass through the
  forgotten sources.  This is causal deletion, as opposed to zeroing one claim
  while leaving its dependants standing.

Both are stated as structure fields, so a forgetting profile must carry them
explicitly.  The canaries show that the pre-existing interface does not imply
either law: a reset-to-prior layer satisfies idempotence and outside
invariance and manufactures evidence, whereas a zeroing layer satisfies the
first new law with nothing further assumed.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting
open Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting

/-! ## No manufactured evidence -/

/-- A forgetting layer that never increases extracted evidence. -/
structure EvidenceMonotoneForgettingLayer (State Scope Query Ev : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [PartialOrder Ev]
    [AdditiveWorldModel State Query Ev]
    extends ForgettingLayer State Scope Query Ev where
  forget_le : ∀ (S : Scope) (W : State) (q : Query),
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
        (forget S W) q ≤
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q

namespace EvidenceMonotoneForgettingLayer

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [PartialOrder Ev]
variable [AdditiveWorldModel State Query Ev]

/-- Successive forgettings only lower evidence further. -/
theorem forget_forget_le (L : EvidenceMonotoneForgettingLayer State Scope Query Ev)
    (S T : Scope) (W : State) (q : Query) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
        (L.forget S (L.forget T W)) q ≤
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q :=
  le_trans (L.forget_le S (L.forget T W) q) (L.forget_le T W q)

/-- Outside the scope the law is an equality, so it is compatible with the
existing outside-invariance field rather than a competing constraint. -/
theorem forget_eq_of_outside (L : EvidenceMonotoneForgettingLayer State Scope Query Ev)
    {S : Scope} {W : State} {q : Query} (hout : ¬ L.inScope S q) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
        (L.forget S W) q =
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q :=
  L.outsideInvariant hout

end EvidenceMonotoneForgettingLayer

section ObservationCount

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [PartialOrder Ev]
variable [AdditiveWorldModel State Query Ev]

/-- Under a monotone observation count, forgetting never raises the count of
any query. -/
theorem queryObservationCount_forget_le
    (L : EvidenceMonotoneForgettingLayer State Scope Query Ev)
    (hmono : Monotone (ConjugateEvidence.observationCount (Ev := Ev)))
    (S : Scope) (W : State) (q : Query) :
    AdditiveWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := Ev) (L.forget S W) q ≤
      AdditiveWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := Ev) W q := by
  unfold AdditiveWorldModel.queryObservationCount
  exact hmono (L.forget_le S W q)

end ObservationCount

/-- Binary evidence counts are monotone in the coordinatewise order. -/
theorem BinaryEvidence.total_mono {x y : BinaryEvidence} (h : x ≤ y) :
    x.total ≤ y.total := by
  have hp : x.pos ≤ y.pos := h.1
  have hn : x.neg ≤ y.neg := h.2
  unfold BinaryEvidence.total
  exact add_le_add hp hn

section BinaryBridge

variable {State Scope Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- For the binary PLN world model, a lawful forgetting never raises the
total observation count of any query. -/
theorem binary_queryObservationCount_forget_le
    (L : EvidenceMonotoneForgettingLayer State Scope Query BinaryEvidence)
    (S : Scope) (W : State) (q : Query) :
    AdditiveWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := BinaryEvidence) (L.forget S W) q ≤
      AdditiveWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := BinaryEvidence) W q := by
  rw [AdditiveWorldModel.queryObservationCount_eq_binary_total,
    AdditiveWorldModel.queryObservationCount_eq_binary_total]
  exact BinaryEvidence.total_mono (L.forget_le S W q)

end BinaryBridge

/-! ## Support-closed deletion -/

/-- A support-tracked forgetting layer whose retained supports avoid the
forgotten footprint and shrink, and whose nonzero evidence is always
supported. -/
structure SupportClosedForgettingLayer (State Scope Query Ev Supp : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    extends SupportTrackedForgettingLayer State Scope Query Ev Supp where
  support_nonempty_of_ne_zero : ∀ (W : State) (q : Query),
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q ≠ 0 →
      (support W q).Nonempty
  retained_support_subset : ∀ (S : Scope) (W : State) (q : Query),
    support (forget S W) q ⊆ support W q
  retained_support_disjoint : ∀ (S : Scope) (W : State) (q : Query),
    Disjoint (support (forget S W) q) (scopeFootprint S)

namespace SupportClosedForgettingLayer

variable {State Scope Query Ev Supp : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- Causal deletion: a query supported only inside the forgotten footprint
loses all its evidence. -/
theorem extract_forget_eq_zero_of_support_subset
    (L : SupportClosedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {W : State} {q : Query}
    (hsub : L.support W q ⊆ L.scopeFootprint S) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
      (L.forget S W) q = 0 := by
  by_contra hne
  obtain ⟨s, hs⟩ := L.support_nonempty_of_ne_zero (L.forget S W) q hne
  have hbefore : s ∈ L.support W q := L.retained_support_subset S W q hs
  have hfoot : s ∈ L.scopeFootprint S := hsub hbefore
  exact Finset.disjoint_left.mp (L.retained_support_disjoint S W q) hs hfoot

/-- Every surviving conclusion keeps a source outside the forgotten
footprint: a retained derivation rather than a dangling count. -/
theorem exists_outside_support_of_retained
    (L : SupportClosedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {W : State} {q : Query}
    (hne : AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
      (L.forget S W) q ≠ 0) :
    ∃ s ∈ L.support W q, s ∉ L.scopeFootprint S := by
  obtain ⟨s, hs⟩ := L.support_nonempty_of_ne_zero (L.forget S W) q hne
  refine ⟨s, L.retained_support_subset S W q hs, ?_⟩
  exact Finset.disjoint_left.mp (L.retained_support_disjoint S W q) hs

/-- A revision whose support lies inside the footprint is exactly undone
(inherited), and after forgetting it contributes nothing anywhere. -/
theorem revision_inside_footprint_vanishes
    (L : SupportClosedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {Δ : State}
    (hsupp : ∀ q, L.support Δ q ⊆ L.scopeFootprint S) (W : State) :
    L.forget S (W + Δ) = W :=
  L.exactInverse_of_supported hsupp W

end SupportClosedForgettingLayer

/-! ## Canaries on a one-query numeric world model -/

namespace Canary

/-- One query, evidence a natural number, state the same number. -/
local instance : EvidenceType ℕ := {}

instance : AdditiveWorldModel ℕ Unit ℕ where
  extract W _ := W
  extract_add _ _ _ := rfl

/-- Reset every claim to the prior `5`.  Idempotent and trivially invariant
outside a scope that contains everything: a legal forgetting layer. -/
def resetLayer : ForgettingLayer ℕ Unit Unit ℕ where
  inScope _ _ := True
  forget _ _ := 5
  idempotent _ _ := rfl
  outsideInvariant hout := absurd trivial hout

/-- Zero every claim.  Also a legal forgetting layer. -/
def zeroLayer : ForgettingLayer ℕ Unit Unit ℕ where
  inScope _ _ := True
  forget _ _ := 0
  idempotent _ _ := rfl
  outsideInvariant hout := absurd trivial hout

/-- The reset layer manufactures evidence: from an empty state it produces
five observations. -/
theorem resetLayer_manufactures_evidence :
    ¬ ∀ (S : Unit) (W : ℕ) (q : Unit),
      AdditiveWorldModel.extract (State := ℕ) (Query := Unit) (Ev := ℕ)
          (resetLayer.forget S W) q ≤
        AdditiveWorldModel.extract (State := ℕ) (Query := Unit) (Ev := ℕ) W q := by
  intro h
  have := h () 0 ()
  change (5 : ℕ) ≤ 0 at this
  omega

/-- Hence no evidence-monotone layer extends the reset layer. -/
theorem no_monotone_extension_of_reset :
    ¬ ∃ L : EvidenceMonotoneForgettingLayer ℕ Unit Unit ℕ,
      L.toForgettingLayer = resetLayer := by
  rintro ⟨L, hL⟩
  apply resetLayer_manufactures_evidence
  intro S W q
  have := L.forget_le S W q
  simpa [← hL] using this

/-- The zeroing layer is evidence-monotone. -/
def zeroMonotone : EvidenceMonotoneForgettingLayer ℕ Unit Unit ℕ where
  toForgettingLayer := zeroLayer
  forget_le _ W _ := Nat.zero_le W

/-- The two legal layers agree on every law of the earlier interface and
differ exactly on the new one. -/
theorem reset_and_zero_share_earlier_laws :
    resetLayer.inScope = zeroLayer.inScope ∧
      (∀ S W, resetLayer.forget S (resetLayer.forget S W) = resetLayer.forget S W) ∧
      (∀ S W, zeroLayer.forget S (zeroLayer.forget S W) = zeroLayer.forget S W) :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end Canary

end Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws
