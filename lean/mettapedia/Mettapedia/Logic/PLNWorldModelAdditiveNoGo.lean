import Mathlib.Data.ENNReal.Real
import Mettapedia.Logic.PLNWorldModel

/-!
# Additive World-Model No-Go Theorems

This module records the first basic incompatibility theorem for additive world models:

- if state revision is idempotent (`W + W = W`),
- and extracted evidence is finite,
- then additive extraction forces that evidence to be zero.

This does **not** say that every additive world model is trivial. It isolates the exact
conflict between:

- additive accumulation of independent evidence, and
- globally idempotent revision at the state layer.

Positive example:
- multiset/bag-style evidence ledgers are additive and non-idempotent.

Negative example:
- a deduplicating/set-style merge cannot remain both additive and finitely nontrivial
  under the current `BinaryWorldModel.evidence_add` law.
-/

namespace Mettapedia.Logic.PLNWorldModelAdditiveNoGo

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

namespace EvidenceQuantale.BinaryEvidence

/-- Finite evidence excludes the `∞` idempotence corner case in `ℝ≥0∞`. -/
def IsFinite (e : BinaryEvidence) : Prop :=
  e.pos ≠ ⊤ ∧ e.neg ≠ ⊤

theorem finite_coord_add_idempotent_eq_zero
    {x : ℝ≥0∞} (hfin : x ≠ ⊤) (hidem : x + x = x) :
    x = 0 := by
  have htoReal : x.toReal + x.toReal = x.toReal := by
    rw [← ENNReal.toReal_add hfin hfin, hidem]
  have hzeroReal : x.toReal = 0 := by
    nlinarith
  rcases (ENNReal.toReal_eq_zero_iff x).mp hzeroReal with hx | hx
  · exact hx
  · exact False.elim (hfin hx)

theorem eq_zero_of_hplus_idempotent
    {e : BinaryEvidence} (hfin : EvidenceQuantale.BinaryEvidence.IsFinite e) (hidem : e + e = e) :
    e = 0 := by
  rcases hfin with ⟨hposFin, hnegFin⟩
  apply BinaryEvidence.ext'
  · have hpos : e.pos + e.pos = e.pos := by
      simpa [BinaryEvidence.hplus_def] using congrArg BinaryEvidence.pos hidem
    exact finite_coord_add_idempotent_eq_zero hposFin hpos
  · have hneg : e.neg + e.neg = e.neg := by
      simpa [BinaryEvidence.hplus_def] using congrArg BinaryEvidence.neg hidem
    exact finite_coord_add_idempotent_eq_zero hnegFin hneg

end EvidenceQuantale.BinaryEvidence

section BinaryWorldModel

variable {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-- In an additive world model, an idempotent state revision law forces every
finite extracted evidence value to vanish. -/
theorem evidence_eq_zero_of_revision_idempotent
    (W : State) (q : Query)
    (hidem : W + W = W)
    (hfin : EvidenceQuantale.BinaryEvidence.IsFinite
      (BinaryWorldModel.evidence (State := State) (Query := Query) W q)) :
    BinaryWorldModel.evidence (State := State) (Query := Query) W q = 0 := by
  have hEvidenceIdem :
      BinaryWorldModel.evidence (State := State) (Query := Query) W q +
          BinaryWorldModel.evidence (State := State) (Query := Query) W q =
        BinaryWorldModel.evidence (State := State) (Query := Query) W q := by
    calc
      BinaryWorldModel.evidence (State := State) (Query := Query) W q +
          BinaryWorldModel.evidence (State := State) (Query := Query) W q
        = BinaryWorldModel.evidence (State := State) (Query := Query) (W + W) q := by
            simpa using
              (BinaryWorldModel.evidence_add' (State := State) (Query := Query) W W q).symm
      _ = BinaryWorldModel.evidence (State := State) (Query := Query) W q := by
            simp [hidem]
  exact EvidenceQuantale.BinaryEvidence.eq_zero_of_hplus_idempotent hfin hEvidenceIdem

/-- No additive world model with globally idempotent revision can exhibit nonzero
finite evidence on any query. -/
theorem not_exists_nonzero_finite_evidence_of_revision_idempotent
    (hidem : ∀ W : State, W + W = W) :
    ¬ ∃ (W : State) (q : Query),
        let e := BinaryWorldModel.evidence (State := State) (Query := Query) W q
        EvidenceQuantale.BinaryEvidence.IsFinite e ∧ e ≠ 0 := by
  intro hExists
  rcases hExists with ⟨W, q, hfin, hne⟩
  have hzero :
      BinaryWorldModel.evidence (State := State) (Query := Query) W q = 0 :=
    evidence_eq_zero_of_revision_idempotent
      (State := State) (Query := Query) W q (hidem W) hfin
  exact hne hzero

end BinaryWorldModel

end Mettapedia.Logic.PLNWorldModelAdditiveNoGo
