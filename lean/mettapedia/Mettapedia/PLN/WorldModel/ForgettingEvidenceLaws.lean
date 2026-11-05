import Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting
import Mettapedia.PLN.WorldModel.WorldModelConservationPack

/-!
# Forgetting laws: exact unlearning, no manufactured evidence, support closure and relevance

The forgetting layer of `GenericWorldModelForgetting` fixes idempotence and
invariance outside the forgotten scope.  Those two laws leave the operation
almost entirely open inside the scope: a layer that resets in-scope claims to a
prior satisfies both.  Forgetting a scope withdraws the sources in its
footprint, and the laws below say what that must do.

## The law set

Each law is read off a theory of retraction: provenance semirings (deletion is
the homomorphism that sends the withdrawn tokens to zero), deletion propagation
and view maintenance, truth maintenance (labels are sets of environments, and
retracting an assumption removes the environments containing it), belief-base
contraction (success, inclusion, relevance, core retainment) and exact
unlearning (the result equals recomputing without the data).

1. **Exact unlearning.**  The result is what would have been computed without
   the withdrawn sources.  On an additive state: forgetting a supported
   revision of a clean base recovers the base
   (`SupportTrackedForgettingLayer.exactInverse_of_clean`).  It is asked only
   of clean bases.  Asked of every base it is degenerate: the layer forgets
   nothing and the revision is zero
   (`ForgettingLayer.exactInverse_everywhere_degenerate`).
2. **Homomorphism.**  Forgetting commutes with revision
   (`SupportTrackedForgettingLayer.forget_add`), so a supported revision is
   absorbed on every base (`forget_add_of_supported`).  On provenance
   polynomials forgetting is the substitution homomorphism, which commutes with
   deduction too and with every stage of a recursive derivation
   (`ProvenanceRetraction`).
3. **No manufactured evidence** (inclusion, read on evidence): forgetting never
   increases the extracted evidence of any query
   (`EvidenceMonotoneForgettingLayer`).  Under this law every observation
   count is non-increasing, so confidence can only fall.
4. **Support closure** (inclusion and success, read on supports): the support
   retained after forgetting is part of the earlier support and avoids the
   forgotten footprint, and nonzero evidence always has nonempty support
   (`SupportClosedForgettingLayer`).  Consequently every conclusion supported
   only inside the footprint is deleted, and every surviving conclusion keeps a
   derivation that does not pass through the forgotten sources.  This is causal
   deletion, as opposed to zeroing one claim while leaving its dependants
   standing.
5. **Relevance** (relevance and core retainment): a claim whose support avoids
   the footprint keeps its evidence exactly
   (`RetractionLayer.extract_forget_of_disjoint`).
6. **Idempotence and commutation** are derived rather than assumed.
   Idempotence follows from support closure and the clean law
   (`SupportClosedForgettingLayer.forget_forget_of_closed`); on the ledger and
   on provenance polynomials two forgettings commute and compose to forgetting
   the union.

`RetractionLayer` carries laws 1 to 5.  On the ledger of identified
observations, exact unlearning alone determines forgetting: it is causal
deletion (`LedgerRetraction`).  The discriminator controls
(`LedgerRetractionControls`) show that laws 3, 4 (its two parts) and 5 are
independent, each failing alone under one policy, and that exact unlearning is
strictly stronger than their conjunction.

Forgetting a symbol (Lin and Reiter; uniform interpolation) is a different
operation: it removes vocabulary and keeps every consequence stated in the
remaining vocabulary, whereas retraction removes data, and the consequences
that rested on it go with it.

## Canaries

The canaries show that the earlier interface implies none of the new laws: a
reset-to-prior layer satisfies idempotence and outside invariance and
manufactures evidence, whereas a zeroing layer satisfies the evidence law with
nothing further assumed.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
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

/-- A revision whose support lies inside the footprint vanishes on forgetting:
it leaves no trace on any base.  On a clean base the base is recovered exactly
(`SupportTrackedForgettingLayer.exactInverse_of_clean`). -/
theorem revision_inside_footprint_vanishes
    (L : SupportClosedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {Δ : State}
    (hsupp : ∀ q, L.support Δ q ⊆ L.scopeFootprint S) (W : State) :
    L.forget S (W + Δ) = L.forget S W :=
  L.toSupportTrackedForgettingLayer.forget_add_of_supported hsupp W

/-- **Idempotence is derived**: a forgotten state is clean, so forgetting it
again changes nothing. -/
theorem forget_forget_of_closed
    (L : SupportClosedForgettingLayer State Scope Query Ev Supp)
    (S : Scope) (W : State) :
    L.forget S (L.forget S W) = L.forget S W :=
  L.forget_eq_self_of_clean fun q => L.retained_support_disjoint S W q

end SupportClosedForgettingLayer

/-! ## Retraction: both laws, exact unlearning and relevance -/

/-- **A retraction layer**: support-closed deletion with exact unlearning on
clean bases, no manufactured evidence, and relevance: a claim whose support
avoids the footprint keeps its evidence exactly. -/
structure RetractionLayer (State Scope Query Ev Supp : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [PartialOrder Ev]
    [AdditiveWorldModel State Query Ev]
    extends SupportClosedForgettingLayer State Scope Query Ev Supp,
      EvidenceMonotoneForgettingLayer State Scope Query Ev where
  extract_forget_of_disjoint : ∀ {S : Scope} {W : State} {q : Query},
    Disjoint (support W q) (scopeFootprint S) →
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
          (forget S W) q =
        AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q

namespace RetractionLayer

variable {State Scope Query Ev Supp : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [PartialOrder Ev]
variable [AdditiveWorldModel State Query Ev]

/-- **Exact unlearning on clean bases.** -/
theorem exactInverse_of_clean (L : RetractionLayer State Scope Query Ev Supp)
    {S : Scope} {Δ W : State}
    (hsupp : ∀ q, L.support Δ q ⊆ L.scopeFootprint S)
    (hclean : ∀ q, Disjoint (L.support W q) (L.scopeFootprint S)) :
    L.forget S (W + Δ) = W :=
  L.toSupportTrackedForgettingLayer.exactInverse_of_clean hsupp hclean

/-- **No manufactured evidence.** -/
theorem extract_forget_le (L : RetractionLayer State Scope Query Ev Supp)
    (S : Scope) (W : State) (q : Query) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
        (L.forget S W) q ≤
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q :=
  L.toEvidenceMonotoneForgettingLayer.forget_le S W q

/-- **Success**: a claim supported only inside the footprint loses all its
evidence. -/
theorem extract_forget_eq_zero_of_support_subset
    (L : RetractionLayer State Scope Query Ev Supp)
    {S : Scope} {W : State} {q : Query}
    (hsub : L.support W q ⊆ L.scopeFootprint S) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
      (L.forget S W) q = 0 :=
  L.toSupportClosedForgettingLayer.extract_forget_eq_zero_of_support_subset hsub

end RetractionLayer

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

/-- **The zeroing layer undoes nothing but zero.**  It is the identity on no
nonzero state, so it undoes no nonzero revision on every base: the
all-bases inverse law fails for it at every nonzero revision. -/
theorem zeroLayer_no_allBases_inverse {Δ : ℕ} (hΔ : Δ ≠ 0) :
    ¬ ∀ W : ℕ, zeroLayer.forget () (W + Δ) = W :=
  fun hinv => hΔ (zeroLayer.exactInverse_everywhere_degenerate hinv).2

end Canary

end Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws
