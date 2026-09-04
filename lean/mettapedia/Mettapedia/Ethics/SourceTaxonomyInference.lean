import Mettapedia.Ethics.SourceHierarchyConcordance
import Mettapedia.Languages.KIF.TaxonomyInference

/-!
# Certified taxonomy consequences of the Formal Ethics source

These certificates use exact SUO-KIF symbol names.  Their leaves are checked
against the facts decoded from the ontology source; their internal nodes are
the generic subclass-transitivity and instance-inheritance rules.  The
companion executable supplies the decoded source list, so source drift causes
replay failure rather than silently changing the Lean theorem.

Two specimens are retained.  The first derives a theory-family edge through
two source subclass assertions.  The second derives that the source
individual `KDT` is an instance of `EthicalTheory` through three subclass
levels.  A reversed source leaf is retained as a rejection control.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.SourceTaxonomyInference

open Mettapedia.Logic
open Mettapedia.Languages.KIF.TaxonomyInference

abbrev SourceFact := TaxonomyFact String
abbrev SourceWitness := TaxonomyWitness String
abbrev SourceCertificate := Derivation SourceFact SourceWitness

/-- A source assertion as a certificate leaf. -/
def sourceLeaf (fact : SourceFact) : SourceCertificate :=
  .node fact (.source fact) 0 Fin.elim0

/-- Join two displayed subclass certificates by transitivity. -/
def subclassTransCertificate
    (child middle parent : String)
    (childMiddle middleParent : SourceCertificate) : SourceCertificate :=
  .node (.subclass child parent) (.subclassTrans child middle parent) 2
    (Fin.cases childMiddle (Fin.cases middleParent Fin.elim0))

/-- Join an instance certificate and a subclass certificate by inheritance. -/
def instanceInheritanceCertificate
    (individual child parent : String)
    (individualChild childParent : SourceCertificate) : SourceCertificate :=
  .node (.instance individual parent)
    (.instanceInheritance individual child parent) 2
    (Fin.cases individualChild (Fin.cases childParent Fin.elim0))

def targetCenteredGeneralFact : SourceFact :=
  .subclass "TargetCenteredVirtueEthicsTheory" "GeneralVirtueEthicsTheory"

def generalVirtueEthicalFact : SourceFact :=
  .subclass "GeneralVirtueEthicsTheory" "EthicalTheory"

def targetCenteredEthicalFact : SourceFact :=
  .subclass "TargetCenteredVirtueEthicsTheory" "EthicalTheory"

/-- The two exact source facts used by the target-centered certificate. -/
def targetCenteredRequiredFacts : List SourceFact :=
  [targetCenteredGeneralFact, generalVirtueEthicalFact]

/-- A real two-level source consequence rather than a copied direct edge. -/
def targetCenteredEthicalCertificate : SourceCertificate :=
  subclassTransCertificate
    "TargetCenteredVirtueEthicsTheory"
    "GeneralVirtueEthicsTheory"
    "EthicalTheory"
    (sourceLeaf targetCenteredGeneralFact)
    (sourceLeaf generalVirtueEthicalFact)

theorem targetCenteredEthicalCertificate_accepted
    (source : List SourceFact)
    (containsRequired : ∀ fact ∈ targetCenteredRequiredFacts, fact ∈ source) :
    targetCenteredEthicalCertificate.valid (taxonomyRuleWitness source) = true := by
  have firstMember := containsRequired targetCenteredGeneralFact (by
    simp [targetCenteredRequiredFacts])
  have secondMember := containsRequired generalVirtueEthicalFact (by
    simp [targetCenteredRequiredFacts])
  have firstMember' :
      TaxonomyFact.subclass "TargetCenteredVirtueEthicsTheory"
        "GeneralVirtueEthicsTheory" ∈ source := by
    simpa [targetCenteredGeneralFact] using firstMember
  have secondMember' :
      TaxonomyFact.subclass "GeneralVirtueEthicsTheory" "EthicalTheory" ∈
        source := by
    simpa [generalVirtueEthicalFact] using secondMember
  simp [Derivation.valid, Derivation.concl, targetCenteredEthicalCertificate,
    subclassTransCertificate, sourceLeaf,
    targetCenteredGeneralFact, generalVirtueEthicalFact, taxonomyRuleWitness,
    checkRuleInstance, TaxonomyWitness.premises, TaxonomyWitness.conclusion,
    TaxonomyWitness.authorized, firstMember', secondMember']

theorem targetCenteredEthical_derivable
    (source : List SourceFact)
    (containsRequired : ∀ fact ∈ targetCenteredRequiredFacts, fact ∈ source) :
    Derives (TaxonomyRule source) targetCenteredEthicalFact := by
  exact Derivation.valid_sound (taxonomyRuleWitness source)
    targetCenteredEthicalCertificate
    (targetCenteredEthicalCertificate_accepted source containsRequired)

def kdtKantianFact : SourceFact :=
  .instance "KDT" "KantianDeontologicalTheory"

def kantianImperativeFact : SourceFact :=
  .subclass "KantianDeontologicalTheory" "DeontologicalImperativeTheory"

def imperativeDeontologicalFact : SourceFact :=
  .subclass "DeontologicalImperativeTheory" "DeontologicalTheory"

def deontologicalEthicalFact : SourceFact :=
  .subclass "DeontologicalTheory" "EthicalTheory"

def kdtEthicalFact : SourceFact :=
  .instance "KDT" "EthicalTheory"

def kdtRequiredFacts : List SourceFact :=
  [kdtKantianFact, kantianImperativeFact,
    imperativeDeontologicalFact, deontologicalEthicalFact]

def imperativeEthicalCertificate : SourceCertificate :=
  subclassTransCertificate
    "DeontologicalImperativeTheory" "DeontologicalTheory" "EthicalTheory"
    (sourceLeaf imperativeDeontologicalFact)
    (sourceLeaf deontologicalEthicalFact)

def kantianEthicalCertificate : SourceCertificate :=
  subclassTransCertificate
    "KantianDeontologicalTheory" "DeontologicalImperativeTheory"
    "EthicalTheory"
    (sourceLeaf kantianImperativeFact)
    imperativeEthicalCertificate

/-- A four-leaf source certificate crossing both taxonomy rules. -/
def kdtEthicalCertificate : SourceCertificate :=
  instanceInheritanceCertificate "KDT" "KantianDeontologicalTheory"
    "EthicalTheory"
    (sourceLeaf kdtKantianFact)
    kantianEthicalCertificate

theorem kdtEthicalCertificate_accepted
    (source : List SourceFact)
    (containsRequired : ∀ fact ∈ kdtRequiredFacts, fact ∈ source) :
    kdtEthicalCertificate.valid (taxonomyRuleWitness source) = true := by
  have kdtMember := containsRequired kdtKantianFact (by
    simp [kdtRequiredFacts])
  have kantianMember := containsRequired kantianImperativeFact (by
    simp [kdtRequiredFacts])
  have imperativeMember := containsRequired imperativeDeontologicalFact (by
    simp [kdtRequiredFacts])
  have deontologicalMember := containsRequired deontologicalEthicalFact (by
    simp [kdtRequiredFacts])
  have kdtMember' :
      TaxonomyFact.instance "KDT" "KantianDeontologicalTheory" ∈ source := by
    simpa [kdtKantianFact] using kdtMember
  have kantianMember' :
      TaxonomyFact.subclass "KantianDeontologicalTheory"
        "DeontologicalImperativeTheory" ∈ source := by
    simpa [kantianImperativeFact] using kantianMember
  have imperativeMember' :
      TaxonomyFact.subclass "DeontologicalImperativeTheory"
        "DeontologicalTheory" ∈ source := by
    simpa [imperativeDeontologicalFact] using imperativeMember
  have deontologicalMember' :
      TaxonomyFact.subclass "DeontologicalTheory" "EthicalTheory" ∈ source := by
    simpa [deontologicalEthicalFact] using deontologicalMember
  simp [Derivation.valid, Derivation.concl, kdtEthicalCertificate,
    kantianEthicalCertificate,
    imperativeEthicalCertificate, instanceInheritanceCertificate,
    subclassTransCertificate, sourceLeaf, kdtKantianFact, kantianImperativeFact,
    imperativeDeontologicalFact, deontologicalEthicalFact, taxonomyRuleWitness,
    checkRuleInstance, TaxonomyWitness.premises, TaxonomyWitness.conclusion,
    TaxonomyWitness.authorized, kdtMember', kantianMember', imperativeMember',
    deontologicalMember']

theorem kdtEthical_derivable
    (source : List SourceFact)
    (containsRequired : ∀ fact ∈ kdtRequiredFacts, fact ∈ source) :
    Derives (TaxonomyRule source) kdtEthicalFact := by
  exact Derivation.valid_sound (taxonomyRuleWitness source)
    kdtEthicalCertificate
    (kdtEthicalCertificate_accepted source containsRequired)

/-- Every set-theoretic model of the checked source therefore makes `KDT` an
instance of `EthicalTheory`. -/
theorem kdtEthical_semantically_sound
    {Entity : Type*}
    (interpretation : TaxonomyInterpretation String Entity)
    (source : List SourceFact)
    (sourceValid : interpretation.ModelsSource source)
    (containsRequired : ∀ fact ∈ kdtRequiredFacts, fact ∈ source) :
    interpretation.Satisfies kdtEthicalFact :=
  interpretation.derives_sound sourceValid
    (kdtEthical_derivable source containsRequired)

def reversedTargetCenteredFact : SourceFact :=
  .subclass "EthicalTheory" "TargetCenteredVirtueEthicsTheory"

def reversedTargetCenteredLeaf : SourceCertificate :=
  sourceLeaf reversedTargetCenteredFact

/-- A leaf not asserted by the source is rejected by exact replay. -/
theorem reversedTargetCenteredLeaf_rejected
    (source : List SourceFact)
    (absent : reversedTargetCenteredFact ∉ source) :
    reversedTargetCenteredLeaf.valid (taxonomyRuleWitness source) = false := by
  have absent' :
      TaxonomyFact.subclass "EthicalTheory" "TargetCenteredVirtueEthicsTheory" ∉
        source := by
    simpa [reversedTargetCenteredFact] using absent
  simp [Derivation.valid, Derivation.concl, reversedTargetCenteredLeaf, sourceLeaf,
    reversedTargetCenteredFact,
    taxonomyRuleWitness, checkRuleInstance, TaxonomyWitness.premises,
    TaxonomyWitness.conclusion, TaxonomyWitness.authorized, absent']

/-! ## Axiom audit -/

#print axioms targetCenteredEthicalCertificate_accepted
#print axioms targetCenteredEthical_derivable
#print axioms kdtEthicalCertificate_accepted
#print axioms kdtEthical_derivable
#print axioms kdtEthical_semantically_sound
#print axioms reversedTargetCenteredLeaf_rejected

end Mettapedia.Ethics.SourceTaxonomyInference
