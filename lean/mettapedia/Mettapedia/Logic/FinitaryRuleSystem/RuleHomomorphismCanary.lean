import Mettapedia.Logic.FinitaryRuleSystem.FiniteModelCanary
import Mettapedia.Logic.FinitaryRuleSystem.RuleHomomorphism

/-!
# Rule-homomorphism positive and negative controls

The positive control changes the physical judgment representation from `J` to
`J × Unit`.  Primitive rules, finite models, witnesses, certificates, and the
complete replay test all commute.

The adversarial control collapses both Boolean judgments to `Unit`.  It still
preserves every successful rule test and accepted certificate, but turns a
source rejection into a target acceptance when the queried claim changes.
This isolates injectivity as a necessary condition for exact replay
translation rather than for one-way proof preservation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem.RuleHomomorphismCanary

open Mettapedia.Logic
open Mettapedia.Logic.FinitaryRuleSystem.FiniteModelCanary

/-! ## Exact representation change -/

abbrev SourceJudgment := Judgment
abbrev sourceRules := BaseRules
abbrev sourceInterface := baseRuleWitness

abbrev TargetJudgment := SourceJudgment × Unit

def embed (judgment : SourceJudgment) : TargetJudgment :=
  (judgment, ())

theorem embed_injective : Function.Injective embed := by
  intro left right equality
  exact congrArg Prod.fst equality

/-- The target rule system reads the same logical judgment through the first
projection of its changed representation. -/
def targetRules (premises : List TargetJudgment)
    (conclusion : TargetJudgment) : Prop :=
  sourceRules (premises.map Prod.fst) conclusion.1

def targetInterface : RuleWitness targetRules where
  W := sourceInterface.W
  isInstance := fun witness premises conclusion =>
    sourceInterface.isInstance witness (premises.map Prod.fst) conclusion.1
  sound := by
    intro witness premises conclusion accepted
    exact sourceInterface.sound witness (premises.map Prod.fst) conclusion.1
      accepted
  complete := by
    intro premises conclusion rule
    exact sourceInterface.complete (premises.map Prod.fst) conclusion.1 rule

def strictHomomorphism : RuleHomomorphism sourceRules targetRules where
  mapJudgment := embed
  map_rule := by
    intro premises conclusion rule
    change sourceRules ((premises.map embed).map Prod.fst) (embed conclusion).1
    simpa [List.map_map, Function.comp_def, embed] using rule

def witnessedHomomorphism :
    WitnessedRuleHomomorphism sourceInterface targetInterface where
  mapJudgment := embed
  mapWitness := fun witness => witness
  rule_test_preserved := by
    intro witness premises conclusion accepted
    change sourceInterface.isInstance witness
      ((premises.map embed).map Prod.fst) (embed conclusion).1 = true
    simpa [List.map_map, Function.comp_def, embed] using accepted

def exactHomomorphism :
    ExactWitnessedRuleHomomorphism sourceInterface targetInterface where
  mapJudgment := embed
  mapJudgment_injective := embed_injective
  mapWitness := fun witness => witness
  rule_test_exact := by
    intro witness premises conclusion
    change sourceInterface.isInstance witness
      ((premises.map embed).map Prod.fst) (embed conclusion).1 =
        sourceInterface.isInstance witness premises conclusion
    simp [List.map_map, Function.comp_def, embed]

/-- A target model over the changed representation. -/
def targetModel : FiniteModel targetRules where
  World := Bool
  worldFintype := inferInstance
  satisfies := fun world judgment => baseModel.satisfies world judgment.1
  rulesSound := by
    intro premises conclusion rule world premiseSatisfaction
    exact baseModel.rulesSound (premises.map Prod.fst) conclusion.1 rule world
      fun premise member => by
        rw [List.mem_map] at member
        obtain ⟨targetPremise, targetMember, rfl⟩ := member
        exact premiseSatisfaction targetPremise targetMember

def targetCountermodel :
    FiniteCountermodel targetRules (embed .bottom) where
  model := targetModel
  refutes := ⟨false, rfl⟩

/-- Model pullback reconstructs a finite countermodel of source bottom. -/
def pulledBackCountermodel :
    FiniteCountermodel sourceRules Judgment.bottom :=
  targetCountermodel.reduct strictHomomorphism .bottom

theorem pulledBack_model_rejects_bottom :
    pulledBackCountermodel.model.checkValid .bottom = false := by
  rfl

/-- Translate the genuine two-node source certificate. -/
def mappedCopiedTruthCertificate :
    Derivation TargetJudgment targetInterface.W :=
  exactHomomorphism.toWitnessed.mapCertificate copiedTruthCertificate

theorem mappedCopiedTruthCertificate_valid :
    mappedCopiedTruthCertificate.valid targetInterface = true := by
  change
    (exactHomomorphism.toWitnessed.mapCertificate
      copiedTruthCertificate).valid targetInterface = true
  rw [exactHomomorphism.mapCertificate_valid]
  exact copiedTruthCertificate_valid

/-- Positive exactness control: every claim query commutes, not only the
accepted truth query. -/
theorem exact_replay_commutes_for_every_claim (claim : SourceJudgment) :
    (mappedCopiedTruthCertificate.valid targetInterface &&
      decide (mappedCopiedTruthCertificate.concl = embed claim)) =
    (copiedTruthCertificate.valid sourceInterface &&
      decide (copiedTruthCertificate.concl = claim)) :=
  exactHomomorphism.replay_test_commutes claim copiedTruthCertificate

/-! ## Non-injective one-way translation -/

def trueOnlyRules (premises : List Bool) (conclusion : Bool) : Prop :=
  premises = [] ∧ conclusion = true

def unitRules (premises : List Unit) (conclusion : Unit) : Prop :=
  premises = [] ∧ conclusion = ()

def trueOnlyInterface : RuleWitness trueOnlyRules where
  W := Unit
  isInstance := fun _ premises conclusion =>
    decide (premises = [] ∧ conclusion = true)
  sound := by
    intro _ premises conclusion accepted
    change premises = [] ∧ conclusion = true
    exact of_decide_eq_true accepted
  complete := by
    intro premises conclusion rule
    change premises = [] ∧ conclusion = true at rule
    exact ⟨(), decide_eq_true rule⟩

def unitInterface : RuleWitness unitRules where
  W := Unit
  isInstance := fun _ premises conclusion =>
    decide (premises = [] ∧ conclusion = ())
  sound := by
    intro _ premises conclusion accepted
    change premises = [] ∧ conclusion = ()
    exact of_decide_eq_true accepted
  complete := by
    intro premises conclusion rule
    change premises = [] ∧ conclusion = () at rule
    exact ⟨(), decide_eq_true rule⟩

def collapse (_judgment : Bool) : Unit := ()

def collapsingHomomorphism :
    WitnessedRuleHomomorphism trueOnlyInterface unitInterface where
  mapJudgment := collapse
  mapWitness := fun witness => witness
  rule_test_preserved := by
    intro witness premises conclusion accepted
    change decide (premises.map collapse = [] ∧ collapse conclusion = ()) = true
    have sourceRule : premises = [] ∧ conclusion = true :=
      of_decide_eq_true accepted
    simp [sourceRule.1]

def trueCertificate : Derivation Bool trueOnlyInterface.W :=
  .node true () 0 Fin.elim0

theorem trueCertificate_valid :
    trueCertificate.valid trueOnlyInterface = true := by
  rfl

def collapsedCertificate : Derivation Unit unitInterface.W :=
  collapsingHomomorphism.mapCertificate trueCertificate

/-- The source correctly rejects its true certificate as evidence for false. -/
theorem source_rejects_false_query :
    (trueCertificate.valid trueOnlyInterface &&
      decide (trueCertificate.concl = false)) = false := by
  rfl

/-- After a non-injective map, the translated certificate is accepted for the
translated false claim because true and false have collapsed. -/
theorem collapsed_target_accepts_false_query :
    (collapsedCertificate.valid unitInterface &&
      decide (collapsedCertificate.concl = collapse false)) = true := by
  rfl

theorem collapse_not_injective : ¬ Function.Injective collapse := by
  intro injective
  have : true = false := injective rfl
  exact Bool.noConfusion this

/-- One-way witness preservation cannot imply exact replay commutation. -/
theorem witnessed_preservation_does_not_force_exact_replay :
    (collapsedCertificate.valid unitInterface &&
      decide (collapsedCertificate.concl = collapse false)) ≠
    (trueCertificate.valid trueOnlyInterface &&
      decide (trueCertificate.concl = false)) := by
  rw [collapsed_target_accepts_false_query, source_rejects_false_query]
  exact Bool.noConfusion

end Mettapedia.Logic.FinitaryRuleSystem.RuleHomomorphismCanary
