import Lean.Data.Json
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
import Mettapedia.GSLT.Distinction.RouteGrades
import Mettapedia.GSLT.Logic.ConstructiveModalStrength
import Mettapedia.Logic.KernelFoundationManifest
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HypersetLogicalStrength
import Mettapedia.TypeTheory.MaterialSets.Hypersets.SetIndexedAntiFoundation

/-!
# Profile ledgers joined to the checked foundation manifest

The principle ledgers state what a profile assumes, derives and refutes.
`KernelFoundationManifest` schema 2 reads the checked environment: complete
types, universe parameters, transitive primitive axioms, the host kernel,
and each declaration's `checkingRole`, `hasCheckedBody` and
`runtimeCounterpart`. Safe mathematical declarations are counted apart from
partial runtime entries. A runtime counterpart records a safe definition
with the same type, levels and owner. That pairing is metadata, not
evidence that a runtime implementation realizes the mathematical body.

The join is profile-specific, so it lives with the ledgers. The inspection
commands stay where they are and are reused unchanged.

An abstract profile is a theorem argument. A Choice0 model and a classical
host-choice model are separate evidence. `HypersetAssumptions` is an abstract
profile. The classical collection development is a model of that profile on
the material carrier. Material infinity and set-indexed decoration are
Choice0 models. No foundation is selected.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.Manifest

open Lean Elab Command Meta
open Mettapedia.Logic.KernelFoundationManifest

/-! ## A propositional reading

The four theorems below are one theory interpretation: an axiom schema read
in the target, modus ponens, substitution, and the reading of falsity.
-/

inductive Formula where
  | falsity : Formula
  | atom : Nat → Formula
  | imp : Formula → Formula → Formula

/-- Substitute a formula for each atom. -/
def substitute (σ : Nat → Formula) : Formula → Formula
  | .falsity => .falsity
  | .atom index => σ index
  | .imp antecedent consequent =>
    .imp (substitute σ antecedent) (substitute σ consequent)

/-- Read formulas as implications and falsity. -/
def denote (valuation : Nat → Prop) : Formula → Prop
  | .falsity => False
  | .atom index => valuation index
  | .imp antecedent consequent =>
    denote valuation antecedent → denote valuation consequent

/-- The weakening schema. -/
def axiomK (antecedent consequent : Formula) : Formula :=
  .imp antecedent (.imp consequent antecedent)

/-- The weakening schema holds in the reading. -/
theorem translated_axiom (valuation : Nat → Prop) (antecedent consequent : Formula) :
    denote valuation (axiomK antecedent consequent) :=
  fun holds _ignored => holds

/-- Modus ponens is the logic of the reading. -/
theorem logic_modusPonens (valuation : Nat → Prop) (antecedent consequent : Formula)
    (step : denote valuation (.imp antecedent consequent))
    (premise : denote valuation antecedent) : denote valuation consequent :=
  step premise

/-- Substitution commutes with the reading. -/
theorem substitution_commutes (valuation : Nat → Prop) (σ : Nat → Formula)
    (formula : Formula) :
    denote valuation (substitute σ formula) ↔
      denote (fun index => denote valuation (σ index)) formula := by
  induction formula with
  | falsity => exact Iff.rfl
  | atom index => exact Iff.rfl
  | imp antecedent consequent antecedentIH consequentIH =>
    show
      (denote valuation (substitute σ antecedent) →
        denote valuation (substitute σ consequent)) ↔
      (denote (fun index => denote valuation (σ index)) antecedent →
        denote (fun index => denote valuation (σ index)) consequent)
    constructor
    · intro step premise
      exact consequentIH.mp (step (antecedentIH.mpr premise))
    · intro step premise
      exact consequentIH.mpr (step (antecedentIH.mp premise))

/-- The reading of falsity is falsity. -/
theorem falsity_preserved (valuation : Nat → Prop) :
    denote valuation .falsity ↔ False := Iff.rfl

/-! ## Classification -/

inductive EvidenceStatus where
  | abstractProfile
  | modelChoice0
  | modelClassicalHostChoice
  | consequence
  | inspected
  deriving BEq, DecidableEq, Repr

inductive Strength where
  | profile
  | derived
  | refuted
  | entailment
  | lowerBound
  | equivalence
  | construction
  | statedBound
  deriving BEq, DecidableEq, Repr

inductive RecordKind where
  | ledgerPrinciple
  | modelTheorem
  | universeBound
  | routeGrade
  | theoryInterpretation
  deriving BEq, DecidableEq, Repr

inductive Role where
  | diaconescu
  | quineIncompatibility
  | pairing
  | abstractLedger
  | materialInfinity
  | setIndexedAntiFoundation
  | classicalCollection
  | universeBound
  | logicalStrength
  | llpoLowerBound
  | observerDistortion
  | translatedAxioms
  | interpretationLogic
  | substitution
  | falsityPreservation
  deriving BEq, DecidableEq, Repr

/-- How the generated axiom list is required to treat `Classical.choice`. -/
inductive HostChoiceExpectation where
  | absent
  | present
  | report
  deriving BEq, DecidableEq, Repr

/-- A route-grade record and a theory interpretation are different kinds. -/
theorem route_grade_kind_differs :
    RecordKind.routeGrade ≠ RecordKind.theoryInterpretation := by
  intro same
  cases same

/-- An abstract profile and a classical host-choice model are different evidence. -/
theorem abstract_profile_differs_from_host_choice_model :
    EvidenceStatus.abstractProfile ≠ EvidenceStatus.modelClassicalHostChoice := by
  intro same
  cases same

/-- A lower bound and an equivalence are different strengths. -/
theorem lower_bound_differs_from_equivalence :
    Strength.lowerBound ≠ Strength.equivalence := by
  intro same
  cases same

structure Attachment where
  declaration : Name
  evidence : EvidenceStatus
  strength : Strength
  kind : RecordKind
  role : Role
  hostChoice : HostChoiceExpectation
  assumptionNames : Array Name
  requiresUniverseParameter : Bool
  secretHostChoice : Bool
  ledgerMentionsHostChoice : Bool
  note : String

def entry (declaration : Name) (evidence : EvidenceStatus) (strength : Strength)
    (kind : RecordKind) (role : Role) (hostChoice : HostChoiceExpectation)
    (assumptionNames : Array Name := #[]) (requiresUniverseParameter : Bool := false)
    (secretHostChoice : Bool := false) (ledgerMentionsHostChoice : Bool := false)
    (note : String := "") : Attachment where
  declaration := declaration
  evidence := evidence
  strength := strength
  kind := kind
  role := role
  hostChoice := hostChoice
  assumptionNames := assumptionNames
  requiresUniverseParameter := requiresUniverseParameter
  secretHostChoice := secretHostChoice
  ledgerMentionsHostChoice := ledgerMentionsHostChoice
  note := note

namespace Decl

def lemOfChoice : Name := ``Mettapedia.SetTheory.Profiles.lem_of_choice
def lemOfPairSubsetChoice : Name := ``Mettapedia.SetTheory.Profiles.lem_of_pairSubsetChoice
def irreflexiveOfInduction : Name := ``Mettapedia.SetTheory.Profiles.irreflexive_of_induction
def noQuineAtomOfInduction : Name := ``Mettapedia.SetTheory.Profiles.noQuineAtom_of_induction
def selfMemberOfQuineAtom : Name := ``Mettapedia.SetTheory.Profiles.selfMember_of_quineAtom
def quineAtomRefutesInduction : Name :=
  ``Mettapedia.SetTheory.Profiles.quineAtom_refutes_induction
def quineAtomRefutesIrreflexive : Name :=
  ``Mettapedia.SetTheory.Profiles.quineAtom_refutes_irreflexive
def unorderedPair : Name := ``Mettapedia.SetTheory.Profiles.unorderedPair
def unorderedPairOfChoice : Name := ``Mettapedia.SetTheory.Profiles.unorderedPair_of_choice
def megalodonAssumptions : Name := ``Mettapedia.SetTheory.Profiles.MegalodonAssumptions
def megalodonLedger : Name := ``Mettapedia.SetTheory.Profiles.megalodonLedger
def hypersetAssumptions : Name := ``Mettapedia.SetTheory.Profiles.HypersetAssumptions
def hypersetLedger : Name := ``Mettapedia.SetTheory.Profiles.hypersetLedger
def bareAssumptions : Name := ``Mettapedia.SetTheory.Profiles.BareAssumptions
def infinity : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel.infinity
def induction : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel.induction
def leastInductive : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel.least_inductive
def naturalMembersInjective : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel.naturalMembers_injective
def naturalMembersSurjective : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel.naturalMembers_surjective
def setDecoration : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.SetIndexedAntiFoundation.existsUnique_setDecoration
def naturalDecoration : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.SetIndexedAntiFoundation.existsUnique_naturalDecoration
def strongCollection : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection.strongCollection
def replacement : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection.replacement
def assumptions : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection.assumptions
def ledger : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection.ledger
def collectionUniverseBound : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.ClassicalHypersetCollection.Controls.selecting_and_collecting_all_differ
def excludedMiddleOfDecidableEquality : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HypersetLogicalStrength.excludedMiddle_of_decidableEquality
def singletonSubsetsBinary : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HypersetLogicalStrength.singleton_subsets_binary_iff_excludedMiddle
def nonemptyReadoutReflection : Name :=
  ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HypersetLogicalStrength.nonempty_readout_reflection_iff_doubleNegationElimination
def llpo : Name :=
  ``Mettapedia.GSLT.ConstructiveModalStrength.image_finite_reflection_implies_llpo
def distortsAtMost : Name := ``Mettapedia.GSLT.Distinction.RouteGrades.DistortsAtMost

end Decl

/-- Ledger entries, model theorems and the two record kinds.
The axiom lists are not stored here. The checking command reads them from
the kernel manifest. -/
def profileAttachments : Array Attachment := #[
  entry Decl.lemOfChoice .abstractProfile .derived .ledgerPrinciple .diaconescu .report
    (assumptionNames := #[`S, `mem, `ext, `sep, `emp, `pow, `eps, `choice])
    (requiresUniverseParameter := true)
    (note := "Extensionality, separation, empty set, power set and a choice operator yield excluded middle. The choice operator is a theorem argument."),
  entry Decl.lemOfPairSubsetChoice .abstractProfile .derived .ledgerPrinciple .diaconescu .report
    (assumptionNames := #[`S, `mem, `ext, `sep, `emp, `pair, `pick, `chosen])
    (requiresUniverseParameter := true)
    (note := "Excluded middle from choice used only on subsets of one unordered pair. The pair and the picker are theorem arguments."),
  entry Decl.irreflexiveOfInduction .abstractProfile .derived .ledgerPrinciple
    .quineIncompatibility .report
    (assumptionNames := #[`S, `mem, `ind])
    (requiresUniverseParameter := true)
    (note := "Membership induction yields that no set belongs to itself."),
  entry Decl.noQuineAtomOfInduction .abstractProfile .refuted .ledgerPrinciple
    .quineIncompatibility .report
    (assumptionNames := #[`S, `mem, `ind])
    (requiresUniverseParameter := true)
    (note := "Membership induction yields that there is no Quine atom."),
  entry Decl.selfMemberOfQuineAtom .abstractProfile .derived .ledgerPrinciple
    .quineIncompatibility .report
    (assumptionNames := #[`S, `mem, `atom])
    (requiresUniverseParameter := true)
    (note := "A Quine atom belongs to itself."),
  entry Decl.quineAtomRefutesInduction .abstractProfile .refuted .ledgerPrinciple
    .quineIncompatibility .report
    (assumptionNames := #[`S, `mem, `atom])
    (requiresUniverseParameter := true)
    (note := "A Quine atom refutes membership induction. This is the abstract incompatibility."),
  entry Decl.quineAtomRefutesIrreflexive .abstractProfile .refuted .ledgerPrinciple
    .quineIncompatibility .report
    (assumptionNames := #[`S, `mem, `atom])
    (requiresUniverseParameter := true)
    (note := "A Quine atom refutes irreflexivity of membership."),
  entry Decl.unorderedPair .abstractProfile .derived .ledgerPrinciple .pairing .report
    (assumptionNames := #[`S, `mem, `emp, `pow, `sep, `rep])
    (requiresUniverseParameter := true)
    (note := "Empty set, power set, separation and replacement yield unordered pairs."),
  entry Decl.unorderedPairOfChoice .abstractProfile .derived .ledgerPrinciple .pairing .report
    (assumptionNames := #[`S, `mem, `emp, `pow, `sep, `rep, `eps, `choice])
    (requiresUniverseParameter := true)
    (note := "Unordered pairs formed with a choice operator. The operator is a theorem argument."),
  entry Decl.megalodonAssumptions .abstractProfile .profile .ledgerPrinciple .abstractLedger
    .report
    (assumptionNames := #[`S, `mem])
    (requiresUniverseParameter := true)
    (note := "Abstract Megalodon profile: extensionality, empty set, union, power set, separation, replacement, membership induction and a choice operator."),
  entry Decl.megalodonLedger .abstractProfile .derived .ledgerPrinciple .abstractLedger .report
    (assumptionNames := #[`S, `mem, `A])
    (requiresUniverseParameter := true)
    (note := "Facts derived from the abstract Megalodon profile. The profile is a theorem argument."),
  entry Decl.hypersetAssumptions .abstractProfile .profile .ledgerPrinciple .abstractLedger
    .report
    (assumptionNames := #[`S, `mem])
    (requiresUniverseParameter := true)
    (note := "Abstract hyperset profile: the set-forming principles and a Quine atom, without membership induction. This record is an abstract profile."),
  entry Decl.hypersetLedger .abstractProfile .derived .ledgerPrinciple .abstractLedger .report
    (assumptionNames := #[`S, `mem, `A])
    (requiresUniverseParameter := true)
    (note := "Facts derived from an abstract hyperset profile supplied as a theorem argument."),
  entry Decl.bareAssumptions .abstractProfile .profile .ledgerPrinciple .abstractLedger .report
    (note := "The bare profile states no membership principle."),
  entry Decl.infinity .modelChoice0 .construction .modelTheorem .materialInfinity .absent
    (requiresUniverseParameter := true)
    (note := "Original-bound material infinity. The witness is the constructed natural set."),
  entry Decl.induction .modelChoice0 .construction .modelTheorem .materialInfinity .absent
    (assumptionNames := #[`predicate, `zero, `step])
    (requiresUniverseParameter := true)
    (note := "Arbitrary-predicate induction local to the constructed natural set. The predicate and the two steps are theorem arguments."),
  entry Decl.leastInductive .modelChoice0 .construction .modelTheorem .materialInfinity .absent
    (assumptionNames := #[`carrier, `zero, `step])
    (requiresUniverseParameter := true)
    (note := "The constructed natural set is the least inductive set. The carrier and its closure steps are theorem arguments."),
  entry Decl.naturalMembersInjective .modelChoice0 .construction .modelTheorem .materialInfinity
    .absent
    (requiresUniverseParameter := true)
    (note := "The natural-member map is injective."),
  entry Decl.naturalMembersSurjective .modelChoice0 .construction .modelTheorem .materialInfinity
    .absent
    (requiresUniverseParameter := true)
    (note := "The natural-member map is propositionally surjective. No inverse is selected."),
  entry Decl.setDecoration .modelChoice0 .construction .modelTheorem .setIndexedAntiFoundation
    .absent
    (assumptionNames := #[`domain, `relation])
    (requiresUniverseParameter := true)
    (note := "Every relation on the members of any material set has a unique decoration at the original graph bound."),
  entry Decl.naturalDecoration .modelChoice0 .construction .modelTheorem .setIndexedAntiFoundation
    .absent
    (assumptionNames := #[`relation])
    (requiresUniverseParameter := true)
    (note := "The set-indexed decoration schema at the constructed infinite natural set."),
  entry Decl.strongCollection .modelClassicalHostChoice .construction .modelTheorem
    .classicalCollection .present
    (requiresUniverseParameter := true)
    (note := "Unrestricted original-bound strong collection in the classical comparison profile. Host choice selects one witness and one graph."),
  entry Decl.replacement .modelClassicalHostChoice .derived .modelTheorem .classicalCollection
    .present
    (requiresUniverseParameter := true)
    (note := "Replacement derived from that strong collection on the material carrier."),
  entry Decl.assumptions .modelClassicalHostChoice .construction .modelTheorem
    .classicalCollection .present
    (requiresUniverseParameter := true)
    (note := "The displayed hyperset assumptions instantiated on the material carrier. This is the classical model of the abstract profile."),
  entry Decl.ledger .modelClassicalHostChoice .derived .modelTheorem .classicalCollection .present
    (requiresUniverseParameter := true)
    (secretHostChoice := true)
    (note := "The hyperset ledger derived from the classical model. The ledger fields do not mention host choice."),
  entry Decl.collectionUniverseBound .inspected .statedBound .universeBound .universeBound .report
    (requiresUniverseParameter := true)
    (note := "Strong collection of the everywhere-true relation has a small witness set. The complete raised collection on ULift.{u + 1, 0} PUnit does not descend to HSet.{u}."),
  entry Decl.excludedMiddleOfDecidableEquality .consequence .entailment .ledgerPrinciple
    .logicalStrength .report
    (assumptionNames := #[`equality])
    (requiresUniverseParameter := true)
    (note := "A decision procedure for material equality entails excluded middle. The decision procedure is a theorem argument."),
  entry Decl.singletonSubsetsBinary .consequence .equivalence .ledgerPrinciple .logicalStrength
    .report
    (requiresUniverseParameter := true)
    (note := "Binary classification of the subsets of a singleton is equivalent to excluded middle."),
  entry Decl.nonemptyReadoutReflection .consequence .equivalence .ledgerPrinciple .logicalStrength
    .report
    (requiresUniverseParameter := true)
    (note := "Positive reflection of nonempty truth sets is equivalent to double-negation elimination."),
  entry Decl.llpo .consequence .lowerBound .ledgerPrinciple .llpoLowerBound .absent
    (assumptionNames := #[`reflection, `stream, `unique])
    (note := "Image-finite reflection of an infinite stream yields LLPO. The strength is a lower bound. The reflection hypothesis, the stream and the uniqueness hypothesis are theorem arguments."),
  entry Decl.distortsAtMost .inspected .statedBound .routeGrade .observerDistortion .report
    (assumptionNames := #[`route])
    (requiresUniverseParameter := true)
    (note := "A route, which is a relation, changes observed distances by at most a bound. This certifies observer distortion."),
  entry ``translated_axiom .consequence .derived .theoryInterpretation .translatedAxioms .absent
    (assumptionNames := #[`valuation, `antecedent, `consequent])
    (note := "The weakening schema holds after translation into the target."),
  entry ``logic_modusPonens .consequence .derived .theoryInterpretation .interpretationLogic
    .absent
    (assumptionNames := #[`valuation, `antecedent, `consequent, `step, `premise])
    (note := "Modus ponens is preserved by the reading."),
  entry ``substitution_commutes .consequence .derived .theoryInterpretation .substitution .absent
    (assumptionNames := #[`valuation, `σ, `formula])
    (note := "Substitution commutes with the reading."),
  entry ``falsity_preserved .consequence .derived .theoryInterpretation .falsityPreservation
    .absent
    (assumptionNames := #[`valuation])
    (note := "The reading of falsity is falsity.")
]

theorem attachment_count : profileAttachments.size = 35 := by
  decide

theorem hyperset_assumptions_are_abstract :
    (profileAttachments.find? fun item => item.declaration == Decl.hypersetAssumptions).map
        (·.evidence) =
      some .abstractProfile := by
  decide

theorem classical_assumptions_are_host_choice_model :
    (profileAttachments.find? fun item => item.declaration == Decl.assumptions).map (·.evidence) =
      some .modelClassicalHostChoice := by
  decide

theorem quine_incompatibility_is_abstract :
    (profileAttachments.find? fun item => item.declaration == Decl.noQuineAtomOfInduction).map
        (·.evidence) =
      some .abstractProfile := by
  decide

theorem set_decoration_is_choice0 :
    (profileAttachments.find? fun item => item.declaration == Decl.setDecoration).map
        (·.evidence) =
      some .modelChoice0 := by
  decide

theorem llpo_strength_is_lower_bound :
    (profileAttachments.find? fun item => item.declaration == Decl.llpo).map (·.strength) =
      some .lowerBound := by
  decide

theorem classical_ledger_omits_host_choice_from_the_claim :
    (profileAttachments.find? fun item => item.declaration == Decl.ledger).map
        (fun item => item.secretHostChoice && !item.ledgerMentionsHostChoice) =
      some true := by
  decide

theorem choice_operator_is_an_assumption_of_diaconescu :
    (profileAttachments.find? fun item => item.declaration == Decl.lemOfChoice).map
        (·.assumptionNames) =
      some #[`S, `mem, `ext, `sep, `emp, `pow, `eps, `choice] := by
  decide

theorem reflection_is_an_assumption_of_the_llpo_bound :
    (profileAttachments.find? fun item => item.declaration == Decl.llpo).map (·.assumptionNames) =
      some #[`reflection, `stream, `unique] := by
  decide

theorem equality_decision_is_an_assumption :
    (profileAttachments.find? fun item =>
        item.declaration == Decl.excludedMiddleOfDecidableEquality).map (·.assumptionNames) =
      some #[`equality] := by
  decide

theorem route_entry_and_falsity_entry_differ :
    ((profileAttachments.find? fun item => item.declaration == Decl.distortsAtMost).map
        (·.kind) =
      some .routeGrade) ∧
      ((profileAttachments.find? fun item => item.declaration == ``falsity_preserved).map
          (·.kind) =
        some .theoryInterpretation) := by
  decide

theorem choice0_entries_expect_no_host_choice :
    ((profileAttachments.find? fun item => item.declaration == Decl.infinity).map (·.hostChoice) =
        some .absent) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.induction).map
          (·.hostChoice) =
        some .absent) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.leastInductive).map
          (·.hostChoice) =
        some .absent) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.naturalMembersInjective).map
          (·.hostChoice) =
        some .absent) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.naturalMembersSurjective).map
          (·.hostChoice) =
        some .absent) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.setDecoration).map
          (·.hostChoice) =
        some .absent) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.naturalDecoration).map
          (·.hostChoice) =
        some .absent) := by
  decide

theorem classical_entries_expect_host_choice :
    ((profileAttachments.find? fun item => item.declaration == Decl.strongCollection).map
          (·.hostChoice) =
        some .present) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.replacement).map
          (·.hostChoice) =
        some .present) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.assumptions).map
          (·.hostChoice) =
        some .present) ∧
      ((profileAttachments.find? fun item => item.declaration == Decl.ledger).map (·.hostChoice) =
        some .present) := by
  decide

theorem exactly_one_secret_host_choice_entry :
    (profileAttachments.filter (·.secretHostChoice)).size = 1 := by
  decide

/-- Partial runtime implementation of `lookahead`, beside the LLPO theorem. -/
def excludedPartialRuntimeName : Name :=
  `Mettapedia.GSLT.ConstructiveModalStrength.lookahead._unsafe_rec

/-- Safe definition named by that runtime entry's counterpart metadata. -/
def excludedPartialRuntimeCounterpart : Name :=
  `Mettapedia.GSLT.ConstructiveModalStrength.lookahead

/-- The partial runtime entry is not one of the ledger rows. -/
theorem excluded_partial_runtime_is_not_a_ledger_row :
    (profileAttachments.filter (·.declaration == excludedPartialRuntimeName)).size = 0 := by
  decide

/-- Counts read from schema 2. Checked bodies are a subset of the safe count. -/
structure MathematicalCensus where
  safeMathematicalDeclarations : Nat
  checkedBodies : Nat

private def jsonString (value : Json) (field : String) : MetaM String := do
  match value.getObjValAs? String field with
  | .ok text => return text
  | .error err => throwError "{field}: {err}"

private def jsonBool (value : Json) (field : String) : MetaM Bool := do
  match value.getObjValAs? Bool field with
  | .ok flag => return flag
  | .error err => throwError "{field}: {err}"

private def jsonNat (value : Json) (field : String) : MetaM Nat := do
  match value.getObjValAs? Nat field with
  | .ok count => return count
  | .error err => throwError "{field}: {err}"

private def jsonArray (value : Json) (field : String) : MetaM (Array Json) := do
  match value.getObjVal? field with
  | .ok (.arr items) => return items
  | .ok other => throwError "{field} has shape {other}"
  | .error err => throwError "{field}: {err}"

private def runtimeCounterpartText (summary : Json) : MetaM (Option String) := do
  match summary.getObjVal? "runtimeCounterpart" with
  | .ok .null => return none
  | .ok (.str parent) => return some parent
  | .ok other => throwError "runtimeCounterpart has shape {other}"
  | .error err => throwError "runtimeCounterpart: {err}"

/-- A ledger row is a safe mathematical declaration.
Inductive profiles are kernel typing, not checked bodies.
A runtime counterpart on that row would be a second entry, not this body. -/
private def requireSafeMathematical (name : Name) (summary : Json) : MetaM Unit := do
  let role ← jsonString summary "checkingRole"
  let body ← jsonBool summary "hasCheckedBody"
  let unsafeFlag ← jsonBool summary "unsafe"
  let partialFlag ← jsonBool summary "partial"
  let counterpart ← runtimeCounterpartText summary
  if unsafeFlag || partialFlag || role == "nonLogicalImplementation" || counterpart.isSome then
    throwError "{name} is not a safe mathematical declaration (checkingRole {role})"
  if (role == "checkedBody") != body then
    throwError "{name} has checkingRole {role} and hasCheckedBody {body}"
  if role != "checkedBody" && role != "kernelInductiveTyping" &&
      role != "primitiveAxiom" && role != "kernelQuotientPrimitive" then
    throwError "{name} has checkingRole {role}"

/-- The safe definition named by runtime-counterpart metadata has a checked body. -/
private def requireCheckedBody (name : Name) (summary : Json) : MetaM Unit := do
  requireSafeMathematical name summary
  if (← jsonString summary "checkingRole") != "checkedBody" then
    throwError "{name} has no checked body"

/-- The manifest command checks these flags against `collectAxioms` and schema 2. -/
def checkProfileLedger : MetaM MathematicalCensus := do
  let mut secrets : Nat := 0
  let mut safe : Nat := 0
  let mut bodies : Nat := 0
  let mut sawTranslated : Bool := false
  let mut sawLogic : Bool := false
  let mut sawSubstitution : Bool := false
  let mut sawFalsity : Bool := false
  let mut sawDistortion : Bool := false
  let mut sawLlpo : Bool := false
  for item in profileAttachments do
    let info ← getConstInfo item.declaration
    if item.requiresUniverseParameter && info.levelParams.isEmpty then
      throwError "{item.declaration} has no universe parameter"
    let summary ← declarationSummary item.declaration
    requireSafeMathematical item.declaration summary
    let countedBody ← jsonBool summary "hasCheckedBody"
    safe := safe + 1
    if countedBody then bodies := bodies + 1
    let found ← forallTelescope info.type fun binders _body =>
      binders.mapM fun binder => binder.fvarId!.getUserName
    for expected in item.assumptionNames do
      if !found.contains expected then
        throwError "{item.declaration} dropped assumption binder {expected}. Telescope: {found}"
    let axioms ← collectAxioms item.declaration
    if axioms.contains ``sorryAx then
      throwError "{item.declaration} depends on sorryAx. Axioms: {axioms}"
    for expected in item.assumptionNames do
      if axioms.contains expected then
        throwError "assumption {expected} of {item.declaration} is listed as a primitive axiom"
    let hasChoice := axioms.contains ``Classical.choice
    match item.hostChoice with
    | .absent =>
      if hasChoice then
        throwError "{item.declaration} is marked free of host choice, but its manifest contains Classical.choice. Axioms: {axioms}"
    | .present =>
      if !hasChoice then
        throwError "{item.declaration} is marked as using host choice, but its manifest does not contain Classical.choice. Axioms: {axioms}"
    | .report => pure ()
    if item.secretHostChoice then
      secrets := secrets + 1
      if item.ledgerMentionsHostChoice then
        throwError "{item.declaration} is the secret-choice entry, and its ledger claim is marked as mentioning host choice"
      if !hasChoice then
        throwError "{item.declaration} is the secret-choice entry, but its manifest does not contain Classical.choice. Axioms: {axioms}"
    if item.role == .llpoLowerBound then
      sawLlpo := true
      if item.strength != .lowerBound then
        throwError "LLPO entry {item.declaration} is recorded with strength {reprStr item.strength}"
    if item.role == .translatedAxioms then sawTranslated := true
    if item.role == .interpretationLogic then sawLogic := true
    if item.role == .substitution then sawSubstitution := true
    if item.role == .falsityPreservation then sawFalsity := true
    if item.role == .observerDistortion then
      sawDistortion := true
      if item.kind != .routeGrade then
        throwError "{item.declaration} is an observer-distortion entry recorded as {reprStr item.kind}"
    if item.kind == .theoryInterpretation && item.role == .observerDistortion then
      throwError "{item.declaration} is both a route grade and a theory interpretation"
  if secrets != 1 then
    throwError "expected one secret-choice entry, found {secrets}"
  if !sawLlpo then
    throwError "the LLPO lower bound is missing"
  if !(sawTranslated && sawLogic && sawSubstitution && sawFalsity) then
    throwError "the theory interpretation is missing a field"
  if !sawDistortion then
    throwError "the route-grade example is missing"
  let abstractInfo ← getConstInfo Decl.hypersetAssumptions
  let modelInfo ← getConstInfo Decl.assumptions
  if abstractInfo.name == modelInfo.name then
    throwError "the abstract hyperset profile and the classical model are the same declaration"
  if safe != profileAttachments.size then
    throwError "safe mathematical declaration count {safe} differs from the ledger rows"
  if bodies > safe then
    throwError "checked bodies {bodies} exceed safe mathematical declarations {safe}"
  return { safeMathematicalDeclarations := safe, checkedBodies := bodies }

private def binderJson (binder : Name) (typeText : String) : Json :=
  Json.mkObj [("name", .str binder.toString), ("type", .str typeText)]

private def renderedTelescope (name : Name) : MetaM (Array (Name × String)) := do
  let info ← getConstInfo name
  forallTelescope info.type fun binders _body => do
    binders.mapM fun binder => do
      let binderName ← binder.fvarId!.getUserName
      let binderType ← inferType binder
      let typeText ← withOptions (fun options => options.setBool `pp.all true) do
        return (← ppExpr binderType).pretty
      return (binderName, typeText)

private def classificationJson (item : Attachment) : Json :=
  Json.mkObj [
    ("declaration", .str item.declaration.toString),
    ("evidence", .str (reprStr item.evidence)),
    ("strength", .str (reprStr item.strength)),
    ("kind", .str (reprStr item.kind)),
    ("role", .str (reprStr item.role)),
    ("hostChoice", .str (reprStr item.hostChoice)),
    ("secretHostChoice", .bool item.secretHostChoice),
    ("ledgerMentionsHostChoice", .bool item.ledgerMentionsHostChoice),
    ("requiresUniverseParameter", .bool item.requiresUniverseParameter),
    ("note", .str item.note)
  ]

/-- The partial runtime entry is refused by `declarationManifest` and kept out
of the safe mathematical count. Its counterpart string is metadata. -/
def excludePartialRuntime : MetaM Json := do
  let name := excludedPartialRuntimeName
  let summary ← declarationSummary name
  let role ← jsonString summary "checkingRole"
  let body ← jsonBool summary "hasCheckedBody"
  let partialFlag ← jsonBool summary "partial"
  let unsafeFlag ← jsonBool summary "unsafe"
  if role != "nonLogicalImplementation" || body || !partialFlag || unsafeFlag then
    throwError "{name} is not a partial runtime entry (checkingRole {role})"
  let some counterpart ← runtimeCounterpartText summary
    | throwError "{name} has no runtime counterpart metadata"
  if counterpart != excludedPartialRuntimeCounterpart.toString then
    throwError "runtime counterpart metadata was {counterpart}"
  let parentSummary ← declarationSummary excludedPartialRuntimeCounterpart
  requireCheckedBody excludedPartialRuntimeCounterpart parentSummary
  let refused ← try
      let _manifest ← declarationManifest name
      pure false
    catch _exception =>
      pure true
  if !refused then
    throwError "{name} was certified as a checked mathematical body"
  if profileAttachments.any (·.declaration == name) then
    throwError "{name} is counted among safe mathematical declarations"
  let moduleJson ← moduleManifest `Mettapedia.GSLT.Logic.ConstructiveModalStrength
  let schema ← jsonNat moduleJson "schemaVersion"
  if schema != 2 then
    throwError "module manifest schemaVersion is {schema}"
  let kernel ← jsonNat moduleJson "kernelDeclarationCount"
  let checkedBodies ← jsonNat moduleJson "checkedBodyDeclarationCount"
  let runtimeCount ← jsonNat moduleJson "nonLogicalDeclarationCount"
  let safeItems ← jsonArray moduleJson "declarations"
  let runtimeItems ← jsonArray moduleJson "nonLogicalDeclarations"
  let compilerItems ← jsonArray moduleJson "compilerOnlyDeclarations"
  if kernel != safeItems.size then
    throwError "kernelDeclarationCount {kernel} differs from the safe list"
  if runtimeCount != runtimeItems.size then
    throwError "nonLogicalDeclarationCount {runtimeCount} differs from the runtime list"
  if checkedBodies > kernel then
    throwError "checked bodies {checkedBodies} exceed safe mathematical declarations {kernel}"
  let mut listedSafe : Bool := false
  let mut llpoSafe : Bool := false
  for item in safeItems do
    match item.getObjVal? "declaration" with
    | .ok declared =>
      let declaredName ← jsonString declared "name"
      if declaredName == name.toString then listedSafe := true
      if declaredName == Decl.llpo.toString then
        llpoSafe := true
        requireCheckedBody Decl.llpo declared
    | .error err => throwError "{err}"
  if listedSafe then
    throwError "{name} is listed among safe mathematical declarations"
  if !llpoSafe then
    throwError "{Decl.llpo} is absent from the module's safe mathematical declarations"
  let mut listedRuntime : Bool := false
  for item in runtimeItems do
    if (← jsonString item "name") == name.toString then
      listedRuntime := true
      if (← jsonString item "checkingRole") != "nonLogicalImplementation" then
        throwError "{name} is a runtime entry with another checking role"
      if ← jsonBool item "hasCheckedBody" then
        throwError "{name} is a runtime entry marked with a checked body"
  if !listedRuntime then
    throwError "{name} is absent from nonLogicalDeclarations"
  for item in compilerItems do
    match item with
    | .str compilerName =>
      if compilerName == name.toString then
        throwError "{name} is recorded as compiler-only rather than a partial runtime entry"
    | other => throwError "compiler-only entry has shape {other}"
  return summary

/-- Classification plus the kernel manifest. Assumptions stay out of the axiom list.
Partial runtime entries are a separate array. -/
def profileLedgerManifest : MetaM Json := do
  let census ← checkProfileLedger
  let excluded ← excludePartialRuntime
  let excludedPartialRuntime := #[excluded]
  let entries ← profileAttachments.mapM fun item => do
    let manifest ← declarationManifest item.declaration
    let summary ← match manifest.getObjVal? "declaration" with
      | .ok summary => pure summary
      | .error err => throwError "{err}"
    requireSafeMathematical item.declaration summary
    let role ← jsonString summary "checkingRole"
    let body ← jsonBool summary "hasCheckedBody"
    let counterpart ← runtimeCounterpartText summary
    let telescope ← renderedTelescope item.declaration
    let mut assumptions : Array Json := #[]
    let mut otherBinders : Array Json := #[]
    for (binder, typeText) in telescope do
      let encoded := binderJson binder typeText
      if item.assumptionNames.contains binder then
        assumptions := assumptions.push encoded
      else
        otherBinders := otherBinders.push encoded
    return Json.mkObj [
      ("classification", classificationJson item),
      ("checkingRole", .str role),
      ("hasCheckedBody", .bool body),
      ("runtimeCounterpart", match counterpart with
        | some parent => .str parent
        | none => .null),
      ("countedAsMathematics", .bool true),
      ("assumptions", .arr assumptions),
      ("otherBinders", .arr otherBinders),
      ("manifest", manifest)
    ]
  return Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("checkingEnvironment", ← checkingEnvironment),
    ("safeMathematicalDeclarationCount", toJson census.safeMathematicalDeclarations),
    ("checkedBodyDeclarationCount", toJson census.checkedBodies),
    ("excludedPartialRuntimeCount", toJson excludedPartialRuntime.size),
    ("entries", .arr entries),
    ("excludedPartialRuntime", .arr excludedPartialRuntime)
  ]

elab "#profile_ledger_controls" : command => do
  let census ← liftTermElabM checkProfileLedger
  logInfo m!"profile ledger controls passed ({census.safeMathematicalDeclarations} safe mathematical declarations, {census.checkedBodies} checked bodies)"

elab "#profile_ledger_manifest" : command => do
  let manifest ← liftTermElabM profileLedgerManifest
  logInfo manifest.pretty

elab "#profile_ledger_exclude_partial_runtime" : command => do
  let _summary ← liftTermElabM excludePartialRuntime
  logInfo m!"excluded partial runtime entry {excludedPartialRuntimeName}; not counted as a safe mathematical declaration"

elab "#profile_ledger_refuse_fake" : command => do
  let name : Name := `Mettapedia.SetTheory.Profiles.Manifest.NoSuchDeclaration
  let refused ← liftTermElabM do
    try
      let _manifest ← declarationSummary name
      return false
    catch _exception =>
      return true
  if refused then
    logInfo m!"refused nonexistent declaration {name}"
  else
    throwError "nonexistent declaration {name} was accepted"

/-- info: profile ledger controls passed (35 safe mathematical declarations, 32 checked bodies) -/
#guard_msgs in
#profile_ledger_controls

/-- info: excluded partial runtime entry Mettapedia.GSLT.ConstructiveModalStrength.lookahead._unsafe_rec; not counted as a safe mathematical declaration -/
#guard_msgs in
#profile_ledger_exclude_partial_runtime

/-- info: refused nonexistent declaration Mettapedia.SetTheory.Profiles.Manifest.NoSuchDeclaration -/
#guard_msgs in
#profile_ledger_refuse_fake

end Mettapedia.SetTheory.Profiles.Manifest
