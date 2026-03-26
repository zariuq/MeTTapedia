import Mettapedia.Logic.MarkovLogicWorldModel

/-!
# MLN Regression Fixtures

Small regression fixtures for the infinite-first MLN→WM bridge.

We use a two-world finite support embedded in the countable semantics layer:
- world `0` has weight `2`,
- world `1` has weight `1`.

This gives:
- a positive finite-support witness over `univ`,
- a negative witness for the smaller singleton support `{0}`,
- a query with nonzero probability that is not true in every live world,
- a concrete WM correspondence example.
-/

namespace Mettapedia.Logic.MarkovLogicRegression

open scoped ENNReal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicCountable
open Mettapedia.Logic.MarkovLogicFiniteRestriction
open Mettapedia.Logic.MarkovLogicFactorGraph
open Mettapedia.Logic.MarkovLogicWorldModel

inductive DemoQuery where
  | ideal
  | reachable
  | impossible
deriving DecidableEq

abbrev DemoWorld := Fin 2
abbrev DemoFeature := Unit

def demoWorldWeight (w : DemoWorld) : ENNReal :=
  if w = 0 then 2 else 1

def demoQueryHolds : DemoQuery → DemoWorld → Prop
  | .ideal, w => w = 0
  | .reachable, _ => True
  | .impossible, _ => False

theorem demoWorldWeight_tsum_eq_three :
    (∑' w : DemoWorld, demoWorldWeight w) = 3 := by
  unfold demoWorldWeight
  rw [tsum_eq_sum (s := (Finset.univ : Finset DemoWorld))
    (fun x hx => (hx (Finset.mem_univ x)).elim)]
  norm_num [Fin.sum_univ_two]

noncomputable def demoMLN : CountableMLNSemantics DemoWorld DemoQuery DemoFeature where
  worldWeight := demoWorldWeight
  queryHolds := demoQueryHolds
  featurePotential := fun _ _ => 1
  totalMass_ne_top := by
    rw [demoWorldWeight_tsum_eq_three]
    norm_num

theorem demo_totalMass_eq_three :
    CountableMLNSemantics.totalMass demoMLN = 3 := by
  simpa [CountableMLNSemantics.totalMass] using demoWorldWeight_tsum_eq_three

theorem demo_supportWitness :
    FiniteSupportWitness demoMLN (Finset.univ : Finset DemoWorld) := by
  constructor
  intro w hw
  exact False.elim (hw (Finset.mem_univ w))

theorem demo_not_singleton_support :
    ¬ FiniteSupportWitness demoMLN ({0} : Finset DemoWorld) := by
  intro hs
  have h := hs.zero_outside 1 (by simp)
  norm_num [demoMLN, demoWorldWeight] at h

theorem demo_compiledPartition_eq_three :
    compiledPartition demoMLN (Finset.univ : Finset DemoWorld) = 3 := by
  rw [compiledPartition_eq_restrictedTotalMass]
  norm_num [restrictedTotalMass, Fin.sum_univ_two, demoMLN, demoWorldWeight]

theorem demo_compiledQueryMass_ideal_eq_two :
    compiledQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.ideal = 2 := by
  rw [compiledQueryMass_eq_restrictedQueryMass]
  simp [restrictedQueryMass, demoMLN, demoWorldWeight, demoQueryHolds]

theorem demo_restrictedTotalMass_eq_three :
    restrictedTotalMass demoMLN (Finset.univ : Finset DemoWorld) = 3 := by
  norm_num [restrictedTotalMass, Fin.sum_univ_two, demoMLN, demoWorldWeight]

theorem demo_restrictedQueryMass_ideal_eq_two :
    restrictedQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.ideal = 2 := by
  simp [restrictedQueryMass, demoMLN, demoWorldWeight, demoQueryHolds]

theorem demo_restrictedQueryMass_reachable_eq_three :
    restrictedQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.reachable = 3 := by
  norm_num [restrictedQueryMass, demoMLN, demoWorldWeight, demoQueryHolds]

theorem demo_restrictedQueryMass_impossible_eq_zero :
    restrictedQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.impossible = 0 := by
  simp [restrictedQueryMass, demoMLN, demoQueryHolds]

theorem demo_compiledQueryMass_reachable_eq_three :
    compiledQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.reachable = 3 := by
  rw [compiledQueryMass_eq_restrictedQueryMass]
  rw [demo_restrictedQueryMass_reachable_eq_three]

theorem demo_compiledQueryMass_impossible_eq_zero :
    compiledQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.impossible = 0 := by
  rw [compiledQueryMass_eq_restrictedQueryMass]
  rw [demo_restrictedQueryMass_impossible_eq_zero]

theorem ideal_not_true_in_every_live_world :
    ¬ ∀ w ∈ (Finset.univ : Finset DemoWorld), demoQueryHolds DemoQuery.ideal w := by
  intro hall
  have h1 := hall 1 (by simp)
  simp [demoQueryHolds] at h1

theorem wm_queryStrength_ideal_eq_two_thirds :
    BinaryWorldModel.queryStrength
      ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
      DemoQuery.ideal = (2 : ENNReal) / 3 := by
  rw [wm_queryStrength_eq_restricted_queryProb demoMLN demo_supportWitness]
  have htotal_ne_zero :
      restrictedTotalMass demoMLN (Finset.univ : Finset DemoWorld) ≠ 0 := by
    rw [demo_restrictedTotalMass_eq_three]
    norm_num
  unfold restrictedMassSemantics MassSemantics.queryProb
  rw [if_neg htotal_ne_zero]
  change
    restrictedQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.ideal /
      restrictedTotalMass demoMLN (Finset.univ : Finset DemoWorld) = (2 : ENNReal) / 3
  rw [demo_restrictedQueryMass_ideal_eq_two, demo_restrictedTotalMass_eq_three]

theorem wm_queryStrength_reachable_eq_one :
    BinaryWorldModel.queryStrength
      ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
      DemoQuery.reachable = 1 := by
  rw [wm_queryStrength_eq_restricted_queryProb demoMLN demo_supportWitness]
  have htotal_ne_zero :
      restrictedTotalMass demoMLN (Finset.univ : Finset DemoWorld) ≠ 0 := by
    rw [demo_restrictedTotalMass_eq_three]
    norm_num
  unfold restrictedMassSemantics MassSemantics.queryProb
  rw [if_neg htotal_ne_zero]
  change
    restrictedQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.reachable /
      restrictedTotalMass demoMLN (Finset.univ : Finset DemoWorld) = 1
  rw [demo_restrictedQueryMass_reachable_eq_three, demo_restrictedTotalMass_eq_three]
  rw [ENNReal.div_self (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num : (3 : ENNReal) ≠ ⊤)]

theorem wm_queryStrength_impossible_eq_zero :
    BinaryWorldModel.queryStrength
      ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
      DemoQuery.impossible = 0 := by
  rw [wm_queryStrength_eq_restricted_queryProb demoMLN demo_supportWitness]
  have htotal_ne_zero :
      restrictedTotalMass demoMLN (Finset.univ : Finset DemoWorld) ≠ 0 := by
    rw [demo_restrictedTotalMass_eq_three]
    norm_num
  unfold restrictedMassSemantics MassSemantics.queryProb
  rw [if_neg htotal_ne_zero]
  change
    restrictedQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.impossible /
      restrictedTotalMass demoMLN (Finset.univ : Finset DemoWorld) = 0
  rw [demo_restrictedQueryMass_impossible_eq_zero, demo_restrictedTotalMass_eq_three]
  simp

theorem singleton_evidence_ideal_eq_two_one :
    BinaryWorldModel.evidence
      ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
      DemoQuery.ideal = ⟨2, 1⟩ := by
  change MassState.evidence
      ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
      DemoQuery.ideal = ⟨2, 1⟩
  rw [MassState.evidence_singleton]
  unfold MassSemantics.evidenceOfMasses compiledMassSemantics
  change
    ({ pos := compiledQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.ideal,
       neg := compiledPartition demoMLN (Finset.univ : Finset DemoWorld) -
         compiledQueryMass demoMLN (Finset.univ : Finset DemoWorld) DemoQuery.ideal } :
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) = ⟨2, 1⟩
  rw [demo_compiledQueryMass_ideal_eq_two, demo_compiledPartition_eq_three]
  ext <;> simp
  exact (ENNReal.eq_sub_of_add_eq (a := (1 : ENNReal)) (b := (3 : ENNReal)) (c := (2 : ENNReal))
    (by norm_num) (by norm_num)).symm

theorem doubled_evidence_ideal_eq_four_two :
    BinaryWorldModel.evidence
      (({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery) +
        {compiledMassSemantics demoMLN demo_supportWitness})
      DemoQuery.ideal = ⟨4, 2⟩ := by
  calc
    BinaryWorldModel.evidence
        (({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery) +
          {compiledMassSemantics demoMLN demo_supportWitness})
        DemoQuery.ideal
      = BinaryWorldModel.evidence
          ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
          DemoQuery.ideal +
        BinaryWorldModel.evidence
          ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
          DemoQuery.ideal := by
            simpa using
              (BinaryWorldModel.evidence_add' (State := MassState DemoQuery) (Query := DemoQuery)
                ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
                ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
                DemoQuery.ideal)
    _ = ⟨4, 2⟩ := by
      have hpos :
          (BinaryWorldModel.evidence
            ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
            DemoQuery.ideal).pos = 2 := by
        simpa using
          congrArg Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.pos
            singleton_evidence_ideal_eq_two_one
      have hneg :
          (BinaryWorldModel.evidence
            ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
            DemoQuery.ideal).neg = 1 := by
        simpa using
          congrArg Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.neg
            singleton_evidence_ideal_eq_two_one
      ext <;> simp [Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.hplus_def, hpos, hneg] <;> norm_num

theorem additive_revision_changes_evidence :
    BinaryWorldModel.evidence
      (({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery) +
        {compiledMassSemantics demoMLN demo_supportWitness})
      DemoQuery.ideal ≠
    BinaryWorldModel.evidence
      ({compiledMassSemantics demoMLN demo_supportWitness} : MassState DemoQuery)
      DemoQuery.ideal := by
  intro hEq
  have hPos :=
    congrArg Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.pos hEq
  rw [doubled_evidence_ideal_eq_four_two, singleton_evidence_ideal_eq_two_one] at hPos
  norm_num at hPos

end Mettapedia.Logic.MarkovLogicRegression
