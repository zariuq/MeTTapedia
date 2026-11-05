import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-!
# Generic World-Model Forgetting

This module adds an explicit forgetting/contraction layer on top of the generic
world-model interface.

- forgetting is *not* default revision;
- it is a separate operation with its own laws;
- asking forgetting to undo a revision on **every** base state is degenerate:
  with idempotence it forces forgetting to be the identity and the revision to
  be zero (`ForgettingLayer.exactInverse_everywhere_degenerate`).  A base that
  already carries forgotten material must lose it too, so the inverse law can
  only be asked of bases that carry nothing forgotten.  That law needs
  supports and is stated in `PLNWorldModelSupportForgetting`;
- at this level, a revision that forgetting erases contributes no evidence
  outside the forgotten scope (`ForgettingLayer.erased_revision_supported`),
  and a revision with evidence outside the scope cannot be erased
  (`ForgettingLayer.not_erased_of_nonzero_outside_scope`).
-/

namespace Mettapedia.PLN.WorldModel.GenericWorldModelForgetting

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

section Generic

variable {State Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- A generic world model is zero-preserving when the empty/zero state extracts
zero evidence for every query. Additivity alone does not force this. -/
def GenericWorldModelZeroPreserving : Prop :=
  ∀ q,
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (0 : State) q = 0

/-- A forgetting layer over a generic world model.

`inScope S q` means that query `q` lies inside the forgotten scope `S`. Outside
that scope, forgetting must leave the extracted evidence unchanged. -/
structure ForgettingLayer (State Scope Query Ev : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev] where
  inScope : Scope → Query → Prop
  forget : Scope → State → State
  idempotent : ∀ S W, forget S (forget S W) = forget S W
  outsideInvariant :
    ∀ {S W q}, ¬ inScope S q →
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (forget S W) q =
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) W q

namespace ForgettingLayer

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

theorem idempotent' (F : ForgettingLayer State Scope Query Ev)
    (S : Scope) (W : State) :
    F.forget S (F.forget S W) = F.forget S W :=
  F.idempotent S W

theorem outsideInvariant'
    (F : ForgettingLayer State Scope Query Ev)
    {S : Scope} {W : State} {q : Query}
    (hout : ¬ F.inScope S q) :
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) (F.forget S W) q =
    AdditiveWorldModel.extract
      (State := State) (Query := Query) (Ev := Ev) W q :=
  F.outsideInvariant hout

/-- **An exact inverse at every base is degenerate.**  If forgetting `S` undoes
the revision `Δ` on every base state, then forgetting `S` is the identity and
`Δ = 0`: by idempotence `forget S W = forget S (forget S (W + Δ)) = forget S (W + Δ) = W`,
and the base `0` then gives `Δ = forget S (0 + Δ) = 0`. -/
theorem exactInverse_everywhere_degenerate
    (F : ForgettingLayer State Scope Query Ev)
    {S : Scope} {Δ : State}
    (hinv : ∀ W : State, F.forget S (W + Δ) = W) :
    (∀ W : State, F.forget S W = W) ∧ Δ = 0 := by
  have identity : ∀ W : State, F.forget S W = W := by
    intro W
    calc F.forget S W = F.forget S (F.forget S (W + Δ)) := by rw [hinv W]
      _ = F.forget S (W + Δ) := F.idempotent S (W + Δ)
      _ = W := hinv W
  refine ⟨identity, ?_⟩
  calc Δ = 0 + Δ := (zero_add Δ).symm
    _ = F.forget S (0 + Δ) := (identity (0 + Δ)).symm
    _ = 0 := hinv 0

/-- **A revision that forgetting erases is supported inside the scope**: it
contributes no evidence to any query outside the forgotten scope. -/
theorem erased_revision_supported
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0) :
    ∀ q, ¬ F.inScope S q →
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 := by
  intro q hout
  calc
    AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q
      = AdditiveWorldModel.extract
          (State := State) (Query := Query) (Ev := Ev) (F.forget S Δ) q :=
            (F.outsideInvariant hout).symm
    _ = AdditiveWorldModel.extract
          (State := State) (Query := Query) (Ev := Ev) (0 : State) q := by
            rw [herase]
    _ = 0 := hzero q

/-- **No forgetting erases a revision that changes a query outside the
forgotten scope.** -/
theorem not_erased_of_nonzero_outside_scope
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State} {q : Query}
    (hout : ¬ F.inScope S q)
    (hne :
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q ≠ 0) :
    F.forget S Δ ≠ 0 :=
  fun herase => hne (erased_revision_supported
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F hzero herase q hout)

end ForgettingLayer

end Generic

namespace ForgettingLayer

section Conjugate

variable {State Scope Query Ev : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]

theorem outsideInvariant_queryObservationCount
    (F : ForgettingLayer State Scope Query Ev)
    {S : Scope} {W : State} {q : Query}
    (hout : ¬ F.inScope S q) :
    AdditiveWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) (F.forget S W) q =
    AdditiveWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) W q := by
  unfold AdditiveWorldModel.queryObservationCount
  simpa using congrArg ConjugateEvidence.observationCount (F.outsideInvariant hout)

theorem outsideInvariant_queryObservationConfidence
    (F : ForgettingLayer State Scope Query Ev)
    (κ : ℝ≥0∞)
    {S : Scope} {W : State} {q : Query}
    (hout : ¬ F.inScope S q) :
    AdditiveWorldModel.queryObservationConfidence
      (State := State) (Query := Query) (Ev := Ev) κ (F.forget S W) q =
    AdditiveWorldModel.queryObservationConfidence
      (State := State) (Query := Query) (Ev := Ev) κ W q := by
  unfold AdditiveWorldModel.queryObservationConfidence
  simpa using congrArg (observationConfidence κ) (F.outsideInvariant hout)

end Conjugate

end ForgettingLayer

/-! ## Profile-Level Restatements

The per-query forgetting laws can be packaged as a single statement on
evidence profiles `Query → Ev`.  This is the "answer profile" perspective
from the categorical reorganization. -/

/-- Two evidence profiles agree outside a scope. -/
def profileAgreesOutsideScope
    {Scope Query Ev : Type*}
    (inScope : Scope → Query → Prop)
    (S : Scope) (p₁ p₂ : Query → Ev) : Prop :=
  ∀ q, ¬ inScope S q → p₁ q = p₂ q

/-- Forgetting preserves the evidence profile outside the scope.
    This is `outsideInvariant` lifted to a single profile-level statement. -/
theorem ForgettingLayer.forget_profile_invariant
    {State Scope Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (F : ForgettingLayer State Scope Query Ev)
    (S : Scope) (W : State) :
    profileAgreesOutsideScope F.inScope S
      (fun q => AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) (F.forget S W) q)
      (fun q => AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) W q) :=
  fun _ hq => F.outsideInvariant hq

/-- The evidence profile of a revision that forgetting erases vanishes outside
    the scope.  This is `erased_revision_supported` lifted to profile level. -/
theorem ForgettingLayer.erased_profile_vanishes
    {State Scope Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (F : ForgettingLayer State Scope Query Ev)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (herase : F.forget S Δ = 0) :
    profileAgreesOutsideScope F.inScope S
      (fun q => AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q)
      (fun _ => (0 : Ev)) :=
  fun q hq => F.erased_revision_supported hzero herase q hq

end Mettapedia.PLN.WorldModel.GenericWorldModelForgetting
