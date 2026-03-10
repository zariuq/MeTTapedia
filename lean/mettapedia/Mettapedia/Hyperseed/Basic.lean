import Mettapedia.Logic.SufficientStatisticSurface
import Mettapedia.Logic.PLNWorldModelFixpointCascade

/-!
# Hyperseed Basic

Hyperseed is a thin observation-ingestion and closure layer above the existing
WM foundations. It does not introduce a new semantics stack:

- observations are still accumulated through `SufficientStatisticSurface`,
- binary WM closure still runs through `PLNWorldModelFixpointClosure`,
- bounded discovery still runs through `PLNWorldModelFixpointCascade`.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNWorldModelFixpointCascade
open Mettapedia.Logic.SufficientStatisticSurface

variable {Obs Query : Type*}

/-- Queries directly suggested by an observation trace. -/
def traceSeed (frontier : Obs → Set Query) (σ : Multiset Obs) : Set Query :=
  { q | ∃ o, o ∈ σ ∧ q ∈ frontier o }

@[simp] theorem mem_traceSeed
    (frontier : Obs → Set Query) (σ : Multiset Obs) (q : Query) :
    q ∈ traceSeed frontier σ ↔ ∃ o, o ∈ σ ∧ q ∈ frontier o :=
  Iff.rfl

@[simp] theorem traceSeed_zero
    (frontier : Obs → Set Query) :
    traceSeed frontier (0 : Multiset Obs) = (∅ : Set Query) := by
  ext q
  simp [traceSeed]

@[simp] theorem traceSeed_singleton
    (frontier : Obs → Set Query) (o : Obs) (q : Query) :
    q ∈ traceSeed frontier ({o} : Multiset Obs) ↔ q ∈ frontier o := by
  simp [traceSeed]

/-- Rule pool for Hyperseed over the binary WM induced by a sufficient-statistics
surface. -/
abbrev RulePool
    (S : SufficientStatisticSurface Obs Query Evidence) :=
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  RuleSet (Multiset Obs) Query

/-- Hyperseed closure: observation-trace seeding plus WM fixpoint closure on the
binary evidence world model induced by a sufficient-statistics surface. -/
noncomputable def closureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) : Set Query :=
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  leastRuleClosure R σ (traceSeed frontier σ)

/-- Fair synchronous Hyperseed cascade from an observation trace. -/
def cascadeFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) : ℕ → Set Query :=
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  immediateIter R σ (traceSeed frontier σ)

theorem seed_subset_closureFromTrace
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) :
    traceSeed frontier σ ⊆ closureFromTrace S frontier R σ := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact seed_subset_leastRuleClosure (R := R) (W := σ) (seed := traceSeed frontier σ)

theorem mem_closureFromTrace_iff_mem_cascade_card_of_finite
    [Fintype Query]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs) (q : Query) :
    q ∈ closureFromTrace S frontier R σ ↔
      q ∈ cascadeFromTrace S frontier R σ (Fintype.card Query) := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact
    mem_leastRuleClosure_iff_mem_immediateIter_card_of_finite
      (R := R) (W := σ) (seed := traceSeed frontier σ) q

theorem mem_closureFromTrace_implies_eventualDiscovery_of_finite
    [Fintype Query]
    (S : SufficientStatisticSurface Obs Query Evidence)
    (frontier : Obs → Set Query)
    (R : RulePool S)
    (σ : Multiset Obs)
    {q : Query}
    (hq : q ∈ closureFromTrace S frontier R σ) :
    ∃ N ≤ Fintype.card Query, q ∈ cascadeFromTrace S frontier R σ N := by
  letI : EvidenceType (Multiset Obs) := multisetEvidenceType Obs
  letI : WorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact
    mem_leastRuleClosure_implies_eventual_discovery_of_finite
      (R := R) (W := σ) (seed := traceSeed frontier σ) hq

end Mettapedia.Hyperseed
