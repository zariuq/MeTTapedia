import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Multiset.Basic
import Mettapedia.Logic.PLNWorldModel

/-!
# Abstract MLN Semantics

This module records the semantics-first core for the MLN→WM bridge.

- `AbstractMLNSemantics` keeps the world/query/feature layer abstract.
- `MassSemantics` packages the query-mass / total-mass interface.
- `MassState` turns any such semantic source into an additive `WorldModel`.

The key theorem is the generic transfer:

`WorldModel.queryStrength = queryProb`

whenever the extracted evidence matches the semantic query mass and total mass.
-/

namespace Mettapedia.Logic.PLNMarkovLogicAbstract

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

/-- Abstract MLN-style semantics: world weights, query truth, and feature potentials.

The abstract layer intentionally does **not** impose a specific factorization law.
Those details enter in the countable and finite-specialization modules. -/
structure AbstractMLNSemantics (World Query Feature : Type*) where
  worldWeight : World → ENNReal
  queryHolds : Query → World → Prop
  featurePotential : Feature → World → ENNReal

/-- A query-mass semantics packages the exact information needed by the WM bridge. -/
structure MassSemantics (Query : Type*) where
  queryMass : Query → ENNReal
  totalMass : ENNReal
  queryMass_le_total : ∀ q, queryMass q ≤ totalMass
  totalMass_ne_top : totalMass ≠ ⊤

namespace MassSemantics

variable {Query : Type*} (S : MassSemantics Query)

/-- Semantic query probability, with the same `0` convention used by `Evidence.toStrength`
when the total mass vanishes. -/
noncomputable def queryProb (q : Query) : ENNReal :=
  if S.totalMass = 0 then 0 else S.queryMass q / S.totalMass

/-- Convert semantic masses into binary evidence. -/
noncomputable def evidenceOfMasses (q : Query) : Evidence :=
  ⟨S.queryMass q, S.totalMass - S.queryMass q⟩

theorem evidenceOfMasses_total (q : Query) :
    (S.evidenceOfMasses q).total = S.totalMass := by
  unfold evidenceOfMasses Evidence.total
  rw [add_comm]
  exact tsub_add_cancel_of_le (S.queryMass_le_total q)

theorem toStrength_evidenceOfMasses (q : Query) :
    Evidence.toStrength (S.evidenceOfMasses q) = S.queryProb q := by
  by_cases hzero : S.totalMass = 0
  · unfold Evidence.toStrength queryProb
    rw [S.evidenceOfMasses_total q, if_pos hzero, if_pos hzero]
  · unfold Evidence.toStrength queryProb
    rw [S.evidenceOfMasses_total q, if_neg hzero, if_neg hzero]
    simp [evidenceOfMasses]

end MassSemantics

/-- Additive state of semantic sources. Revision is multiset addition. -/
abbrev MassState (Query : Type*) := Multiset (MassSemantics Query)

namespace MassState

variable {Query : Type*}

instance : EvidenceType (MassState Query) where
  toAddCommMonoid := inferInstance

/-- Extract the evidence supplied by a multiset of semantic sources. -/
noncomputable def evidence (W : MassState Query) (q : Query) : Evidence :=
  (W.map fun src => src.evidenceOfMasses q).sum

noncomputable instance : WorldModel (MassState Query) Query where
  evidence W q := evidence W q
  evidence_add W₁ W₂ q := by
    let f : MassSemantics Query → Evidence := fun src => src.evidenceOfMasses q
    have h :
        (Multiset.map f (W₁ + W₂)).sum =
          (Multiset.map f W₁).sum + (Multiset.map f W₂).sum := by
      rw [Multiset.map_add, Multiset.sum_add]
    change (Multiset.map f (W₁ + W₂)).sum =
      (Multiset.map f W₁).sum + (Multiset.map f W₂).sum
    exact h

theorem evidence_singleton (S : MassSemantics Query) (q : Query) :
    evidence ({S} : MassState Query) q = S.evidenceOfMasses q := by
  unfold evidence
  simp [Multiset.map_singleton, Multiset.sum_singleton]

theorem queryStrength_singleton_eq_queryProb (S : MassSemantics Query) (q : Query) :
    WorldModel.queryStrength ({S} : MassState Query) q = S.queryProb q := by
  unfold WorldModel.queryStrength
  rw [show WorldModel.evidence ({S} : MassState Query) q = S.evidenceOfMasses q by
      exact evidence_singleton S q]
  exact S.toStrength_evidenceOfMasses q

end MassState

theorem queryStrength_eq_queryProb_of_evidence_eq
    {State Query : Type*}
    [EvidenceType State] [WorldModel State Query]
    (W : State) (S : MassSemantics Query)
    (hEvidence : ∀ q, WorldModel.evidence (State := State) (Query := Query) W q = S.evidenceOfMasses q)
    (q : Query) :
    WorldModel.queryStrength (State := State) (Query := Query) W q = S.queryProb q := by
  unfold WorldModel.queryStrength
  rw [hEvidence q]
  exact S.toStrength_evidenceOfMasses q

end Mettapedia.Logic.PLNMarkovLogicAbstract
