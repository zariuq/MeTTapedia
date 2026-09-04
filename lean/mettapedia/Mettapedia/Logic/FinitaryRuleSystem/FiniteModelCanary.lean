import Mettapedia.Logic.FinitaryRuleSystem.FiniteModel

/-!
# Finite-model positive and adversarial controls

The positive control has a truth axiom and an identity rule.  Its two-world
model validates the truth judgment, varies an atom, and refutes bottom.  The
negative control extends exactly the same rule system with a direct bottom
axiom.  Replay then accepts a bottom certificate and no bottom-refuting model
of the extended rules can exist.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem.FiniteModelCanary

open Mettapedia.Logic

/-- Three judgments are enough to distinguish global truth, contingent truth,
and bottom. -/
inductive Judgment where
  | truth
  | atom
  | bottom
deriving DecidableEq

/-- A truth axiom plus an identity rule with one genuine premise. -/
inductive BaseRules : List Judgment → Judgment → Prop where
  | truthAxiom : BaseRules [] .truth
  | identity (judgment : Judgment) : BaseRules [judgment] judgment

inductive BaseWitness where
  | truthAxiom
  | identity (judgment : Judgment)
deriving DecidableEq

def baseIsInstance (witness : BaseWitness) (premises : List Judgment)
    (conclusion : Judgment) : Bool :=
  match witness with
  | .truthAxiom => decide (premises = [] ∧ conclusion = .truth)
  | .identity judgment =>
      decide (premises = [judgment] ∧ conclusion = judgment)

def baseRuleWitness : RuleWitness BaseRules where
  W := BaseWitness
  isInstance := baseIsInstance
  sound := by
    intro witness premises conclusion accepted
    cases witness with
    | truthAxiom =>
        simp only [baseIsInstance, decide_eq_true_eq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact .truthAxiom
    | identity =>
        simp only [baseIsInstance, decide_eq_true_eq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact .identity conclusion
  complete := by
    intro premises conclusion rule
    cases rule with
    | truthAxiom =>
        exact ⟨.truthAxiom, by simp [baseIsInstance]⟩
    | identity =>
        exact ⟨.identity conclusion, by simp [baseIsInstance]⟩

/-- Two valuations: the atom is false in one world and true in the other. -/
def baseModel : FiniteModel BaseRules where
  World := Bool
  worldFintype := inferInstance
  satisfies := fun world judgment =>
    match judgment with
    | .truth => true
    | .atom => world
    | .bottom => false
  rulesSound := by
    intro premises conclusion rule world premiseValid
    cases rule with
    | truthAxiom => rfl
    | identity => exact premiseValid conclusion (by simp)

def baseCountermodel : FiniteCountermodel BaseRules .bottom where
  model := baseModel
  refutes := ⟨false, rfl⟩

/-- Positive executable control: truth holds at every valuation. -/
theorem truth_is_globally_valid : baseModel.checkValid .truth = true := by
  rfl

/-- Negative executable control: the atom is not globally valid. -/
theorem atom_is_not_globally_valid : baseModel.checkValid .atom = false := by
  rfl

/-- Negative executable control: bottom is not globally valid. -/
theorem bottom_is_not_globally_valid : baseModel.checkValid .bottom = false := by
  rfl

def truthCertificate : Derivation Judgment baseRuleWitness.W :=
  .node .truth .truthAxiom 0 Fin.elim0

/-- A nontrivial two-node certificate exercises the premise-preserving rule. -/
def copiedTruthCertificate : Derivation Judgment baseRuleWitness.W :=
  .node .truth (.identity .truth) 1 (fun _ => truthCertificate)

theorem copiedTruthCertificate_valid :
    copiedTruthCertificate.valid baseRuleWitness = true := by
  rfl

/-- Every valid certificate over the base rules fails to conclude bottom. -/
theorem every_valid_base_certificate_rejects_bottom
    (certificate : Derivation Judgment baseRuleWitness.W)
    (accepted : certificate.valid baseRuleWitness = true) :
    certificate.concl ≠ .bottom :=
  baseCountermodel.valid_derivation_does_not_conclude certificate accepted

/-- The exact Boolean replay test rejects every proposed base-rule
certificate for bottom. -/
theorem base_replay_test_rejects_bottom
    (certificate : Derivation Judgment baseRuleWitness.W) :
    (certificate.valid baseRuleWitness &&
        decide (certificate.concl = .bottom)) = false :=
  baseCountermodel.replay_test_rejects certificate

/-! ## Adversarial extension -/

/-- A direct bottom axiom, deliberately absent from `BaseRules`. -/
def DirectBottom (premises : List Judgment) (conclusion : Judgment) : Prop :=
  premises = [] ∧ conclusion = .bottom

def ExtendedRules (premises : List Judgment) (conclusion : Judgment) : Prop :=
  BaseRules premises conclusion ∨ DirectBottom premises conclusion

inductive ExtendedWitness where
  | base (witness : BaseWitness)
  | bottomAxiom
deriving DecidableEq

def extendedIsInstance (witness : ExtendedWitness)
    (premises : List Judgment) (conclusion : Judgment) : Bool :=
  match witness with
  | .base base => baseIsInstance base premises conclusion
  | .bottomAxiom => decide (premises = [] ∧ conclusion = .bottom)

def extendedRuleWitness : RuleWitness ExtendedRules where
  W := ExtendedWitness
  isInstance := extendedIsInstance
  sound := by
    intro witness premises conclusion accepted
    cases witness with
    | base witness =>
        exact Or.inl (baseRuleWitness.sound witness premises conclusion accepted)
    | bottomAxiom =>
        right
        simpa [extendedIsInstance, DirectBottom] using
          (of_decide_eq_true accepted)
  complete := by
    intro premises conclusion rule
    rcases rule with base | bottom
    · obtain ⟨witness, accepted⟩ :=
        baseRuleWitness.complete premises conclusion base
      exact ⟨.base witness, accepted⟩
    · exact ⟨.bottomAxiom, decide_eq_true bottom⟩

def bottomCertificate : Derivation Judgment extendedRuleWitness.W :=
  .node .bottom .bottomAxiom 0 Fin.elim0

/-- The extended checker data really accepts the direct bottom certificate. -/
theorem bottomCertificate_valid :
    bottomCertificate.valid extendedRuleWitness = true := by
  rfl

theorem extendedRules_derives_bottom : Derives ExtendedRules .bottom :=
  Derivation.valid_sound extendedRuleWitness bottomCertificate
    bottomCertificate_valid

/-- Adding the direct bottom rule destroys every bottom-refuting finite model;
finite semantics does not manufacture consistency for a bad rule set. -/
theorem extendedRules_have_no_finite_countermodel :
    ¬ Nonempty (FiniteCountermodel ExtendedRules .bottom) := by
  rintro ⟨countermodel⟩
  exact countermodel.not_derivable extendedRules_derives_bottom

end Mettapedia.Logic.FinitaryRuleSystem.FiniteModelCanary
