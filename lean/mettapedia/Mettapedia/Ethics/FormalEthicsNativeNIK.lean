import Mettapedia.Languages.SUMO.Native.SignatureInference

/-!
# Native SUMO consequences in the Formal Ethics ontology

This module checks an upper-ontology consequence directly in the native SUMO
calculus.  The source slice contains the inheritance axiom from SUMO and four
unchanged formulas from the Formal Ethics ontology.  The certificate does not
carry an asserted conclusion: the native checker reconstructs each universal
instantiation and implication elimination.

The checked context intentionally contains the logical formulas only.  SUMO's
domain declarations and the distinct question of source-signature typing are
examined separately; omitting them here is not a claim that they are logically
inert in the full ontology.  A separate executable canary connects every native
formula below to its SUO-KIF text without making proof checking rerun the source
compiler inside kernel reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.FormalEthicsNativeNIK

open Mettapedia.Languages.SUMO.Native

abbrev Claim := NIKAuthority.Claim
abbrev Evidence := NIKAuthority.Evidence

/-- The general class-inheritance axiom used by SUMO. -/
def inheritanceSource : String :=
    "(=>\n" ++
    "  (and\n" ++
    "    (subclass ?X ?Y)\n" ++
    "    (instance ?Z ?X))\n" ++
    "  (instance ?Z ?Y))\n"

/-- The exact hierarchy facts needed to classify `KDT` as an ethical theory. -/
def formalEthicsSource : String :=
    "(subclass DeontologicalTheory EthicalTheory)\n" ++
    "(subclass DeontologicalImperativeTheory DeontologicalTheory)\n" ++
    "(subclass KantianDeontologicalTheory DeontologicalImperativeTheory)\n" ++
    "(instance KDT KantianDeontologicalTheory)\n"

/-- A closed binary source atom. -/
def binaryAtom (relation left right : String) : Claim :=
  .atom (.constant relation)
    (.term (.constant left) (.term (.constant right) .nil))

def subclassAtom (child parent : String) : Claim :=
  binaryAtom "subclass" child parent

def instanceAtom (individual className : String) : Claim :=
  binaryAtom "instance" individual className

/-- A binary atom over an open native object scope. -/
def binaryOpenAtom {ordinary : Nat}
    (relation : String)
    (left right : Term String String ordinary 0) :
    Formula String String ordinary 0 :=
  .atom (.constant relation) (.term left (.term right .nil))

/-- Direct native form of SUMO's implicitly universally closed inheritance
axiom.  The three de Bruijn indices denote `?Z`, `?Y`, and `?X` respectively. -/
def inheritanceAxiom : Claim :=
  .allObject (.allObject (.allObject
    (.implies
      (.and
        (binaryOpenAtom "subclass" (.var 2) (.var 1))
        (.and
          (binaryOpenAtom "instance" (.var 0) (.var 2))
          .top))
      (binaryOpenAtom "instance" (.var 0) (.var 1)))))

def logicalAssumptions : List Claim :=
  [ inheritanceAxiom
  , subclassAtom "DeontologicalTheory" "EthicalTheory"
  , subclassAtom "DeontologicalImperativeTheory" "DeontologicalTheory"
  , subclassAtom "KantianDeontologicalTheory" "DeontologicalImperativeTheory"
  , instanceAtom "KDT" "KantianDeontologicalTheory" ]

/-- Instantiate SUMO's inheritance axiom at three named constants and apply it
to checked subclass and instance evidence. -/
def inherit
    (child parent individual : String)
    (subclassEvidence instanceEvidence : Evidence) : Evidence :=
  .implicationElimination
    (.allObjectElimination (.constant individual)
      (.allObjectElimination (.constant parent)
        (.allObjectElimination (.constant child) (.hypothesis 0))))
    (.andIntroduction subclassEvidence
      (.andIntroduction instanceEvidence .topIntroduction))

def kdtImperativeCertificate : Evidence :=
  inherit "KantianDeontologicalTheory" "DeontologicalImperativeTheory" "KDT"
    (.hypothesis 3) (.hypothesis 4)

def kdtDeontologicalCertificate : Evidence :=
  inherit "DeontologicalImperativeTheory" "DeontologicalTheory" "KDT"
    (.hypothesis 2) kdtImperativeCertificate

/-- Three inheritance steps from the source fact about `KDT` to the ontology's
top ethical-theory class. -/
def kdtEthicalCertificate : Evidence :=
  inherit "DeontologicalTheory" "EthicalTheory" "KDT"
    (.hypothesis 1) kdtDeontologicalCertificate

def kdtEthicalClaim : NIKAuthority.EntailmentClaim :=
  { assumptions := logicalAssumptions
    conclusion := instanceAtom "KDT" "EthicalTheory" }

theorem kdtEthical_accepted :
    NIKAuthority.entailmentChecker.check
      kdtEthicalClaim kdtEthicalCertificate = true := by
  decide

/-- Proof-relevant NIK evidence for the reconstructed ontology consequence. -/
def kdtEthicalNIKEvidence :
    NIKAuthority.EntailmentNIKEvidence kdtEthicalClaim :=
  ⟨kdtEthicalCertificate, kdtEthical_accepted⟩

theorem kdtEthical_reaches_native_empty :
    (ProofSearch.nativeProofSearchGSLT String String).MultiStep
      [ProofSearch.Sequent.of kdtEthicalClaim.assumptions
        kdtEthicalClaim.conclusion] [] := by
  apply ProofSearch.accepted_certificate_reaches_empty
  exact (NIKAuthority.entailmentChecker_accepts_iff
    kdtEthicalClaim kdtEthicalCertificate).mp kdtEthical_accepted

/-- The accepted source consequence is sound in every native SUMO model that
satisfies this exact finite source context. -/
theorem kdtEthical_valid_in_model
    (model : Model.{0, 0, 0} String String) (world : model.World)
    (assumptionsHold :
      SatisfiesAssumptions model model.emptyObjects model.emptyRows world
        kdtEthicalClaim.assumptions) :
    model.satisfies model.emptyObjects model.emptyRows
      kdtEthicalClaim.conclusion world := by
  exact NIKAuthority.nonempty_entailmentEvidence_valid_in_model
    kdtEthicalClaim ⟨kdtEthicalNIKEvidence⟩ model world assumptionsHold

/-! ## The full source-signature judgment -/

def instanceRestrictions : List SourceElaboration.DomainRestriction :=
  [ ⟨"instance", 1, .object, "Entity"⟩
  , ⟨"instance", 2, .object, "Class"⟩ ]

def subclassRestrictions : List SourceElaboration.DomainRestriction :=
  [ ⟨"subclass", 1, .object, "Class"⟩
  , ⟨"subclass", 2, .object, "Class"⟩ ]

/-- The proof-readable finite restriction profile extracted from SUMO's source
declarations for `instance` and `subclass`. -/
def formalEthicsSignature : SourceElaboration.SourceSignature :=
  { domainRestrictions := instanceRestrictions ++ subclassRestrictions
    restrictionTable :=
      [("instance", instanceRestrictions), ("subclass", subclassRestrictions)]
    operatorArities := [("instance", 2), ("subclass", 2)] }

@[simp] theorem formalEthicsSignature_declaredOperators :
    formalEthicsSignature.declaredOperators = ["instance", "subclass"] := by
  rfl

@[simp] theorem formalEthicsSignature_instance_first :
    formalEthicsSignature.argumentRestrictions "instance" 1 =
      [⟨"instance", 1, .object, "Entity"⟩] := by
  rfl

@[simp] theorem formalEthicsSignature_instance_second :
    formalEthicsSignature.argumentRestrictions "instance" 2 =
      [⟨"instance", 2, .object, "Class"⟩] := by
  rfl

@[simp] theorem formalEthicsSignature_subclass_first :
    formalEthicsSignature.argumentRestrictions "subclass" 1 =
      [⟨"subclass", 1, .object, "Class"⟩] := by
  rfl

@[simp] theorem formalEthicsSignature_subclass_second :
    formalEthicsSignature.argumentRestrictions "subclass" 2 =
      [⟨"subclass", 2, .object, "Class"⟩] := by
  rfl

/-- Exact guarded form of the inheritance axiom under the finite SUMO source
signature. -/
def guardedInheritanceAxiom : Claim :=
  (DomainGuardElaboration.apply formalEthicsSignature inheritanceAxiom).sentence

@[simp] theorem guardedInheritanceAxiom_has_no_direct_domainConsequence :
    SignatureInference.atomDomainConsequences
      formalEthicsSignature guardedInheritanceAxiom = [] := by
  rfl

@[simp] theorem subclassAtom_domainConsequences (child parent : String) :
    SignatureInference.atomDomainConsequences formalEthicsSignature
        (subclassAtom child parent) =
      [instanceAtom child "Class", instanceAtom parent "Class"] := by
  simp [SignatureInference.atomDomainConsequences, subclassAtom, instanceAtom,
    binaryAtom, SignatureInference.closedTerms,
    SignatureInference.consequencesFrom, SignatureInference.restrictionFormula]

@[simp] theorem instanceAtom_domainConsequences
    (individual className : String) :
    SignatureInference.atomDomainConsequences formalEthicsSignature
        (instanceAtom individual className) =
      [instanceAtom individual "Entity", instanceAtom className "Class"] := by
  simp [SignatureInference.atomDomainConsequences, instanceAtom, binaryAtom,
    SignatureInference.closedTerms, SignatureInference.consequencesFrom,
    SignatureInference.restrictionFormula]

def guardedAssumptions : List Claim :=
  guardedInheritanceAxiom :: logicalAssumptions.tail

/-- Domain facts contributed, in source order, by the four ground ontology
atoms.  Repeated facts retain distinct source occurrences. -/
def formalEthicsDomainConsequences : List Claim :=
  [ instanceAtom "DeontologicalTheory" "Class"
  , instanceAtom "EthicalTheory" "Class"
  , instanceAtom "DeontologicalImperativeTheory" "Class"
  , instanceAtom "DeontologicalTheory" "Class"
  , instanceAtom "KantianDeontologicalTheory" "Class"
  , instanceAtom "DeontologicalImperativeTheory" "Class"
  , instanceAtom "KDT" "Entity"
  , instanceAtom "KantianDeontologicalTheory" "Class" ]

theorem guarded_domainConsequences_exact :
    SignatureInference.domainConsequences
        formalEthicsSignature guardedAssumptions =
      formalEthicsDomainConsequences := by
  simp [SignatureInference.domainConsequences, guardedAssumptions,
    logicalAssumptions, formalEthicsDomainConsequences]

theorem guarded_expandedAssumptions_exact :
    SignatureInference.expandedAssumptions
        formalEthicsSignature guardedAssumptions =
      guardedAssumptions ++ formalEthicsDomainConsequences := by
  simp [SignatureInference.expandedAssumptions,
    guarded_domainConsequences_exact]

/-- Instantiate the fully guarded SUMO inheritance axiom.  Domain evidence is
obtained from the signature-aware checker context, not asserted by this proof. -/
def guardedInherit
    (child parent individual : String)
    (childClassEvidence parentClassEvidence individualEntityEvidence : Evidence)
    (subclassEvidence instanceEvidence : Evidence) : Evidence :=
  let childInstantiation : Evidence :=
    .allObjectElimination (.constant child) (.hypothesis 0)
  let childGuarded : Evidence :=
    .implicationElimination childInstantiation
      (.andIntroduction childClassEvidence childClassEvidence)
  let parentInstantiation : Evidence :=
    .allObjectElimination (.constant parent) childGuarded
  let parentGuarded : Evidence :=
    .implicationElimination parentInstantiation
      (.andIntroduction parentClassEvidence parentClassEvidence)
  let individualInstantiation : Evidence :=
    .allObjectElimination (.constant individual) parentGuarded
  let individualGuarded : Evidence :=
    .implicationElimination individualInstantiation individualEntityEvidence
  .implicationElimination individualGuarded
    (.andIntroduction subclassEvidence
      (.andIntroduction instanceEvidence .topIntroduction))

def guardedKdtImperativeCertificate : Evidence :=
  guardedInherit
    "KantianDeontologicalTheory" "DeontologicalImperativeTheory" "KDT"
    (.hypothesis 9) (.hypothesis 10) (.hypothesis 11)
    (.hypothesis 3) (.hypothesis 4)

def guardedKdtDeontologicalCertificate : Evidence :=
  guardedInherit
    "DeontologicalImperativeTheory" "DeontologicalTheory" "KDT"
    (.hypothesis 7) (.hypothesis 8) (.hypothesis 11)
    (.hypothesis 2) guardedKdtImperativeCertificate

def guardedKdtEthicalCertificate : Evidence :=
  guardedInherit
    "DeontologicalTheory" "EthicalTheory" "KDT"
    (.hypothesis 5) (.hypothesis 6) (.hypothesis 11)
    (.hypothesis 1) guardedKdtDeontologicalCertificate

def guardedKdtEthicalClaim : SignatureInference.EntailmentClaim :=
  { signature := formalEthicsSignature
    assumptions := guardedAssumptions
    conclusion := instanceAtom "KDT" "EthicalTheory" }

theorem guardedKdtEthical_accepted :
    SignatureInference.checker.check guardedKdtEthicalClaim
      guardedKdtEthicalCertificate = true := by
  apply (SignatureInference.checker_accepts_iff _ _).2
  change Certificate.infer
      (SignatureInference.expandedAssumptions
        formalEthicsSignature guardedAssumptions)
      guardedKdtEthicalCertificate =
    some (instanceAtom "KDT" "EthicalTheory")
  rw [guarded_expandedAssumptions_exact]
  decide

def guardedKdtEthicalNIKEvidence :
    SignatureInference.NIKEvidence guardedKdtEthicalClaim :=
  ⟨guardedKdtEthicalCertificate, guardedKdtEthical_accepted⟩

theorem guardedKdtEthical_reaches_native_empty :
    (ProofSearch.nativeProofSearchGSLT String String).MultiStep
      [ProofSearch.Sequent.of
        (SignatureInference.expandedAssumptions
          guardedKdtEthicalClaim.signature guardedKdtEthicalClaim.assumptions)
        guardedKdtEthicalClaim.conclusion] [] := by
  apply ProofSearch.accepted_certificate_reaches_empty
  exact (SignatureInference.checker_accepts_iff
    guardedKdtEthicalClaim guardedKdtEthicalCertificate).mp
      guardedKdtEthical_accepted

/-- The full guarded consequence is sound in every domain-respecting native
SUMO model realizing this exact finite signature. -/
theorem guardedKdtEthical_valid_in_model
    (model : Model.{0, 0, 0} String String) (world : model.World)
    (realizes : SignatureSemantics.RealizesSourceSignature
      formalEthicsSignature model)
    (applicationsRespectDomains :
      SignatureInference.RelationApplicationsRespectDomains model)
    (assumptionsHold :
      SatisfiesAssumptions model model.emptyObjects model.emptyRows world
        guardedKdtEthicalClaim.assumptions) :
    model.satisfies model.emptyObjects model.emptyRows
      guardedKdtEthicalClaim.conclusion world := by
  exact SignatureInference.nonempty_nikEvidence_valid_in_model
    guardedKdtEthicalClaim ⟨guardedKdtEthicalNIKEvidence⟩ model world
      realizes applicationsRespectDomains assumptionsHold

/-! ## Negative control -/

def unrelatedVirtueClaim : NIKAuthority.EntailmentClaim :=
  { assumptions := logicalAssumptions
    conclusion := instanceAtom "KDT" "TargetCenteredVirtueEthicsTheory" }

/-- A valid proof tree cannot be relabelled with an unrelated conclusion. -/
theorem retargeted_conclusion_rejected :
    NIKAuthority.entailmentChecker.check
      unrelatedVirtueClaim kdtEthicalCertificate = false := by
  decide

def guardedUnrelatedVirtueClaim : SignatureInference.EntailmentClaim :=
  { signature := formalEthicsSignature
    assumptions := guardedAssumptions
    conclusion := instanceAtom "KDT" "TargetCenteredVirtueEthicsTheory" }

theorem guarded_retargeted_conclusion_rejected :
    SignatureInference.checker.check guardedUnrelatedVirtueClaim
      guardedKdtEthicalCertificate = false := by
  unfold SignatureInference.checker
  change decide (Certificate.infer
      (SignatureInference.expandedAssumptions
        formalEthicsSignature guardedAssumptions)
      guardedKdtEthicalCertificate =
    some (instanceAtom "KDT" "TargetCenteredVirtueEthicsTheory")) = false
  rw [guarded_expandedAssumptions_exact]
  decide

end Mettapedia.Ethics.FormalEthicsNativeNIK
