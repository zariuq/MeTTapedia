import Mettapedia.Languages.MeTTa.Prime.PackageIdentityV1
import Mathlib.Tactic

/-!
# Prime / PeTTaChainer DAG replay boundary V1

This module independently reconstructs the shared proof DAG emitted by the
PeTTaChainer forward proof store.  The graph adapter is untrusted.  Accepted
nodes are replayed through the same generic inference checker used by the
other Prime checking-first fixtures.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.MeTTa.Prime.PackageAuthority

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def pvar (name : String) : Pattern := .fvar name

private def schema (id : String) (metavariables : List (String × Nat))
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ⟨id⟩, metavariables, premises, conclusion }

def atomA : Pattern := app "ppd.A"
def atomB : Pattern := app "ppd.B"
def edge (left right : Pattern) : Pattern := app "ppd.Edge" [left, right]
def path (left right : Pattern) : Pattern := app "ppd.Path" [left, right]
def reach (left right : Pattern) : Pattern := app "ppd.Reach" [left, right]
def witness (left right : Pattern) : Pattern :=
  app "ppd.Witness" [left, right]
def derives (formula : Pattern) : Pattern := app "ppd.Derives" [formula]

def ruleEdgeAB : RuleSchema :=
  schema "ppd.edge-ab" [] [] (derives (edge atomA atomB))

def ruleEdgeToPath : RuleSchema :=
  schema "ppd.edge-to-path" [("left", 0), ("right", 0)]
    [derives (edge (pvar "left") (pvar "right"))]
    (derives (path (pvar "left") (pvar "right")))

def ruleEdgeToReach : RuleSchema :=
  schema "ppd.edge-to-reach" [("left", 0), ("right", 0)]
    [derives (edge (pvar "left") (pvar "right"))]
    (derives (reach (pvar "left") (pvar "right")))

def rulePathReachWitness : RuleSchema :=
  schema "ppd.path-reach-witness" [("left", 0), ("right", 0)]
    [derives (path (pvar "left") (pvar "right")),
     derives (reach (pvar "left") (pvar "right"))]
    (derives (witness (pvar "left") (pvar "right")))

def rules : List RuleSchema :=
  [ruleEdgeAB, ruleEdgeToPath, ruleEdgeToReach, rulePathReachWitness]

def package : PrimeRulePackageV1 :=
  { format := "prime-rule-package-v1"
    dialect := "prime"
    semanticVersion := "0.5"
    rules
    conversions := [] }

private def dataConstructor (label : String) (arity : Nat) : GrammarRule :=
  { label
    category := "PrimeMinimalData"
    params := (List.range arity).map fun index =>
      .simple ("argument" ++ toString index) (.base "PrimeMinimalData")
    syntaxPattern := [] }

private def cacheLanguage : LanguageDef :=
  { name := "PrimeMinimalCheckingCache"
    types := [TypeDecl.plain "PrimeMinimalData"]
    terms := [dataConstructor "ppd.Edge" 2,
      dataConstructor "ppd.A" 0,
      dataConstructor "ppd.B" 0,
      dataConstructor "ppd.Path" 2,
      dataConstructor "ppd.Reach" 2,
      dataConstructor "ppd.Witness" 2]
    equations := []
    rewrites := [] }

private def cacheCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  { judgments := [{ head := "ppd.Derives", arity := 1 }]
    rules }

def cache : Presentation :=
  { language := cacheLanguage, calculus := cacheCalculus }

def projectedCache :=
  Mettapedia.Languages.MeTTa.Prime.MinimalCheckingPackage.project rules

private theorem cache_language_valid : cache.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [cache, cacheLanguage, dataConstructor, LanguageDef.typeNames,
      TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]

theorem cache_is_valid : cache.isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [cache_language_valid]
  simp [cache, cacheCalculus, rules, ruleEdgeAB, ruleEdgeToPath, ruleEdgeToReach,
    rulePathReachWitness, schema, derives, edge, path, reach, witness,
    atomA, atomB, app, pvar, cacheLanguage, dataConstructor,
    Presentation.ruleIds, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, List.eraseDups,
    List.eraseDupsBy]
  norm_num [List.eraseDupsBy.loop]
  decide

def validated : ValidatedPresentation := ⟨cache, cache_is_valid⟩

def goal : Pattern := derives (witness atomA atomB)
def wrongGoal : Pattern := derives (path atomA atomB)

inductive NodeId where
  | edgeAB
  | edgeToPath
  | edgeToReach
  | root
  | missing
deriving Repr, DecidableEq

inductive NodeKind where
  | leaf (name : String)
  | rule (name : String)
deriving Repr, DecidableEq

structure DAGNode where
  id : NodeId
  kind : NodeKind
  ruleInstance : RuleInstance
  children : List NodeId
deriving Repr

structure ProofDAG where
  format : String
  root : NodeId
  nodes : List DAGNode
deriving Repr

def edgeABNode : DAGNode :=
  { id := .edgeAB
    kind := .leaf "edgeAB"
    ruleInstance := { ruleId := ⟨"ppd.edge-ab"⟩, arguments := [] }
    children := [] }

def edgeToPathNode : DAGNode :=
  { id := .edgeToPath
    kind := .rule "edgeToPath"
    ruleInstance :=
      { ruleId := ⟨"ppd.edge-to-path"⟩, arguments := [atomA, atomB] }
    children := [.edgeAB] }

def edgeToReachNode : DAGNode :=
  { id := .edgeToReach
    kind := .rule "edgeToReach"
    ruleInstance :=
      { ruleId := ⟨"ppd.edge-to-reach"⟩, arguments := [atomA, atomB] }
    children := [.edgeAB] }

def rootNode : DAGNode :=
  { id := .root
    kind := .rule "pathReachWitness"
    ruleInstance :=
      { ruleId := ⟨"ppd.path-reach-witness"⟩,
        arguments := [atomA, atomB] }
    children := [.edgeToPath, .edgeToReach] }

def canonicalDAG : ProofDAG :=
  { format := "pettachainer-forward-proof-v1"
    root := .root
    nodes := [edgeABNode, edgeToPathNode, edgeToReachNode, rootNode] }

structure CheckedNode where
  id : NodeId
  goal : Pattern
  proof : RawProof
deriving Repr

def lookupNode? (environment : List CheckedNode) (id : NodeId) :
    Option CheckedNode :=
  environment.find? fun node => node.id == id

def replayNode (environment : List CheckedNode) (node : DAGNode) :
    Option (List CheckedNode) := do
  if (lookupNode? environment node.id).isSome then
    none
  else
    let (premises, conclusion) ←
      instantiateRule? validated node.ruleInstance
    let children ← node.children.mapM (lookupNode? environment)
    if children.map (·.goal) == premises then
      let proof := RawProof.node node.ruleInstance (children.map (·.proof))
      some ({ id := node.id, goal := conclusion, proof } :: environment)
    else
      none

def replayNodes : List CheckedNode → List DAGNode → Option (List CheckedNode)
  | environment, [] => some environment
  | environment, node :: nodes => do
      let next ← replayNode environment node
      replayNodes next nodes

def replayProof? (dag : ProofDAG) (expectedGoal : Pattern) : Option RawProof := do
  if dag.format != "pettachainer-forward-proof-v1" then
    none
  else
    let environment ← replayNodes [] dag.nodes
    let root ← lookupNode? environment dag.root
    if root.goal == expectedGoal then some root.proof else none

def replay (dag : ProofDAG) (expectedGoal : Pattern) : Bool :=
  match replayProof? dag expectedGoal with
  | none => false
  | some proof => checkRaw validated expectedGoal proof

/-- DAG acceptance reconstructs an ordinary generic-checker derivation; graph
syntax and producer evidence add no authority. -/
theorem replay_sound {dag : ProofDAG} {expectedGoal : Pattern}
    (accepted : replay dag expectedGoal = true) :
    ∃ proof : RawProof,
      checkRaw validated expectedGoal proof = true ∧
      ∃ derivation : Derivation validated expectedGoal,
        derivation.erase = proof := by
  unfold replay at accepted
  cases hproof : replayProof? dag expectedGoal with
  | none => simp [hproof] at accepted
  | some proof =>
      have checked : checkRaw validated expectedGoal proof = true := by
        simpa [hproof] using accepted
      exact ⟨proof, checked,
        checkRaw_exists_derivation_with_exact_erasure checked⟩

def missingChildDAG : ProofDAG :=
  { canonicalDAG with
    nodes := [edgeABNode, edgeToPathNode, edgeToReachNode,
      { rootNode with children := [.missing, .edgeToReach] }] }

def swappedChildrenDAG : ProofDAG :=
  { canonicalDAG with
    nodes := [edgeABNode, edgeToPathNode, edgeToReachNode,
      { rootNode with children := [.edgeToReach, .edgeToPath] }] }

def duplicateIdDAG : ProofDAG :=
  { canonicalDAG with
    nodes := [edgeABNode, edgeABNode, edgeToPathNode,
      edgeToReachNode, rootNode] }

def forwardReferenceDAG : ProofDAG :=
  { canonicalDAG with
    nodes := [rootNode, edgeABNode, edgeToPathNode,
      edgeToReachNode] }

def cycleDAG : ProofDAG :=
  { canonicalDAG with
    nodes := [edgeABNode, edgeToPathNode, edgeToReachNode,
      { rootNode with children := [.root, .edgeToReach] }] }

def changedPremiseDAG : ProofDAG :=
  { canonicalDAG with
    nodes := [edgeABNode, edgeToPathNode,
      { edgeToReachNode with children := [.edgeToPath] }, rootNode] }

def invalidLogicalStepDAG : ProofDAG :=
  { canonicalDAG with
    nodes := [edgeABNode,
      { edgeToPathNode with
        ruleInstance :=
          { ruleId := ⟨"ppd.path-reach-witness"⟩,
            arguments := [atomA, atomB] } },
      edgeToReachNode, rootNode] }

def wrongRootDAG : ProofDAG := { canonicalDAG with root := .edgeToPath }

/-! ## Canonical serialization and authenticated certificate -/

def renderNodeId : NodeId → String
  | .edgeAB => "(PeTTaProofNodeIdV1 edgeAB)"
  | .edgeToPath => "(PeTTaProofNodeIdV1 (edgeToPath edgeAB))"
  | .edgeToReach => "(PeTTaProofNodeIdV1 (edgeToReach edgeAB))"
  | .root =>
      "(PeTTaProofNodeIdV1 (pathReachWitness (rule-proof conjunction " ++
        "(edgeToPath edgeAB) (edgeToReach edgeAB))))"
  | .missing => "(PeTTaProofNodeIdV1 missingProof)"

def renderRef (id : NodeId) : String :=
  s!"(PeTTaProofRefV1 {renderNodeId id})"

def renderRefs : List NodeId → String
  | [] => "PCDNil"
  | id :: ids => s!"(PCDCons {renderRef id} {renderRefs ids})"

def renderNodeKind : NodeKind → String
  | .leaf name => s!"(PeTTaProofLeafV1 {name})"
  | .rule name => s!"(PeTTaProofRuleV1 {name})"

def renderDAGNode (node : DAGNode) : String :=
  s!"(PeTTaProofNodeV1 {renderNodeId node.id} " ++
    s!"{renderNodeKind node.kind} {renderRefs node.children})"

def renderNodes : List DAGNode → String
  | [] => "PCDNil"
  | node :: nodes => s!"(PCDCons {renderDAGNode node} {renderNodes nodes})"

def renderDAG (dag : ProofDAG) : String :=
  s!"(PeTTaProofDAGV1 {quote dag.format} {renderRef dag.root} " ++
    s!"{renderNodes dag.nodes})"

def dagDigest (dag : ProofDAG) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex (renderDAG dag)

structure ArtifactIdentityV1 where
  format : String
  digest : String
deriving Repr, DecidableEq

structure SubjectMaterialV1 where
  format : String
  packageIdentity : PackageIdentityV1
  dialect : String
  artifactIdentity : ArtifactIdentityV1
  goal : Pattern
deriving Repr, DecidableEq

structure SubjectRefV1 where
  material : SubjectMaterialV1
  digest : String
  handle : String
deriving Repr, DecidableEq

structure CertificateMaterialV1 where
  format : String
  subject : SubjectRefV1
  dag : ProofDAG
  goal : Pattern
deriving Repr

structure CertificateV1 where
  material : CertificateMaterialV1
  digest : String
deriving Repr

def renderPackageIdentity (identity : PackageIdentityV1) : String :=
  s!"(PackageIdentityV1 {quote identity.format} {quote identity.dialect} " ++
    s!"{quote identity.semanticVersion} {quote identity.digest})"

def renderArtifactIdentity (identity : ArtifactIdentityV1) : String :=
  s!"(PeTTaProofArtifactIdentityV1 {quote identity.format} " ++
    s!"{quote identity.digest})"

def renderSubjectMaterial (material : SubjectMaterialV1) : String :=
  s!"(PrimePeTTaDAGSubjectMaterialV1 {quote material.format} " ++
    s!"{renderPackageIdentity material.packageIdentity} " ++
    s!"{quote material.dialect} " ++
    s!"{renderArtifactIdentity material.artifactIdentity} " ++
    s!"{renderPattern material.goal})"

def renderSubject (subject : SubjectRefV1) : String :=
  s!"(PrimePeTTaDAGSubjectRefV1 {renderSubjectMaterial subject.material} " ++
    s!"{quote subject.digest} (SubjectLocalHandleV1 {quote subject.handle}))"

def renderCertificateMaterial (material : CertificateMaterialV1) : String :=
  s!"(PrimePeTTaDAGCertificateMaterialV1 {quote material.format} " ++
    s!"{renderSubject material.subject} {renderDAG material.dag} " ++
    s!"{renderPattern material.goal})"

def renderCertificate (certificate : CertificateV1) : String :=
  s!"(PrimePeTTaDAGCertificateV1 " ++
    s!"{renderCertificateMaterial certificate.material} " ++
    s!"{quote certificate.digest})"

def makeSubject (dag : ProofDAG) (expectedGoal : Pattern) : SubjectRefV1 :=
  let material : SubjectMaterialV1 :=
    { format := "prime-pettachainer-dag-subject-v1"
      packageIdentity := package.identity
      dialect := "prime"
      artifactIdentity :=
        { format := "pettachainer-forward-proof-v1"
          digest := dagDigest dag }
      goal := expectedGoal }
  let digest := MeTTailCore.Crypto.SHA256.sha256Hex
    (renderSubjectMaterial material)
  { material, digest, handle := digest }

def makeCertificate (dag : ProofDAG) (expectedGoal : Pattern) : CertificateV1 :=
  let material : CertificateMaterialV1 :=
    { format := "prime-pettachainer-dag-certificate-v1"
      subject := makeSubject dag expectedGoal
      dag
      goal := expectedGoal }
  { material
    digest := MeTTailCore.Crypto.SHA256.sha256Hex
      (renderCertificateMaterial material) }

def certificateValid (certificate : CertificateV1) : Bool :=
  renderCertificate certificate ==
      renderCertificate
        (makeCertificate certificate.material.dag certificate.material.goal) &&
    replay certificate.material.dag certificate.material.goal

theorem certificateValid_sound {certificate : CertificateV1}
    (accepted : certificateValid certificate = true) :
    ∃ proof : RawProof,
      checkRaw validated certificate.material.goal proof = true ∧
      ∃ derivation : Derivation validated certificate.material.goal,
        derivation.erase = proof := by
  have replayed :
      replay certificate.material.dag certificate.material.goal = true := by
    rw [certificateValid, Bool.and_eq_true] at accepted
    exact accepted.2
  exact replay_sound replayed

def canonicalCertificate : CertificateV1 :=
  makeCertificate canonicalDAG goal

/-- The V1 boundary admits one canonical certificate spelling.  General
parsing remains the responsibility of the MeTTa reader; this decoder models
the independently checked serialized boundary exercised by the gate. -/
def decodeCertificate (bytes : String) : Option CertificateV1 :=
  if bytes == renderCertificate canonicalCertificate then
    some canonicalCertificate
  else
    none

def decodeAndCheck (bytes : String) : Bool :=
  match decodeCertificate bytes with
  | none => false
  | some certificate => certificateValid certificate

theorem decodeAndCheck_sound {bytes : String}
    (accepted : decodeAndCheck bytes = true) :
    ∃ proof : RawProof,
      checkRaw validated goal proof = true ∧
      ∃ derivation : Derivation validated goal,
        derivation.erase = proof := by
  by_cases hbytes : bytes = renderCertificate canonicalCertificate
  · subst bytes
    have hcertificate : certificateValid canonicalCertificate = true := by
      simpa [decodeAndCheck, decodeCertificate] using accepted
    simpa [canonicalCertificate, makeCertificate] using
      (certificateValid_sound hcertificate)
  · simp [decodeAndCheck, decodeCertificate, hbytes] at accepted

def wrongPackageCertificate : CertificateV1 :=
  let original := canonicalCertificate
  let forgedSubjectMaterial :=
    { original.material.subject.material with
      packageIdentity := Mettapedia.Languages.MeTTa.Prime.PackageAuthority.package.identity }
  let forgedSubjectDigest := MeTTailCore.Crypto.SHA256.sha256Hex
    (renderSubjectMaterial forgedSubjectMaterial)
  let forgedSubject : SubjectRefV1 :=
    { material := forgedSubjectMaterial
      digest := forgedSubjectDigest
      handle := forgedSubjectDigest }
  let forgedMaterial :=
    { original.material with subject := forgedSubject }
  { material := forgedMaterial
    digest := MeTTailCore.Crypto.SHA256.sha256Hex
      (renderCertificateMaterial forgedMaterial) }

def forgedCertificateDigest : CertificateV1 :=
  { canonicalCertificate with digest := String.replicate 64 '0' }

/-! ## Decision × Coverage and evidence boundaries -/

inductive QueryKind where
  | may
  | must
deriving Repr, DecidableEq

inductive Coverage where
  | complete
  | resourceIncomplete
  | heuristicPruned
deriving Repr, DecidableEq

inductive Decision where
  | established
  | refuted
  | undetermined
deriving Repr, DecidableEq

structure PLNEvidence where
  strength : Float
  confidence : Float
deriving Repr

structure Verdict where
  query : QueryKind
  coverage : Coverage
  decision : Decision
  evidence : PLNEvidence
  certificate : CertificateV1
deriving Repr

def verdictValid (verdict : Verdict) : Bool :=
  match verdict.decision with
  | .established =>
      certificateValid verdict.certificate &&
        (verdict.query == .may || verdict.coverage == .complete)
  | .refuted | .undetermined => false

def canonicalEvidence : PLNEvidence :=
  { strength := 1.0, confidence := 1.0 }

def canonicalMustVerdict : Verdict :=
  { query := .must
    coverage := .complete
    decision := .established
    evidence := canonicalEvidence
    certificate := canonicalCertificate }

def highConfidenceInvalidVerdict : Verdict :=
  { canonicalMustVerdict with
    query := .may
    certificate := makeCertificate invalidLogicalStepDAG goal }

def heuristicMustVerdict : Verdict :=
  { canonicalMustVerdict with coverage := .heuristicPruned }

def incompleteEstablishedVerdict : Verdict :=
  { canonicalMustVerdict with coverage := .resourceIncomplete }

structure PatternSupportClaim where
  pattern : String
  minimum : Nat
  witnesses : List CertificateV1
  evidence : PLNEvidence
deriving Repr

def supportClaimValid (claim : PatternSupportClaim) : Bool :=
  claim.witnesses.all certificateValid &&
    claim.minimum ≤ claim.witnesses.length

def supportedClaim : PatternSupportClaim :=
  { pattern := "PathAndReach A B"
    minimum := 1
    witnesses := [canonicalCertificate]
    evidence := canonicalEvidence }

def unsupportedPlausibleClaim : PatternSupportClaim :=
  { pattern := "PathAndReach A B"
    minimum := 2
    witnesses := [canonicalCertificate]
    evidence := { strength := 0.999, confidence := 0.999 } }

def canonicalNodeCount : Nat := canonicalDAG.nodes.length
def canonicalEdgeCount : Nat :=
  canonicalDAG.nodes.foldl (fun count node => count + node.children.length) 0
def canonicalTreeOccurrences : Nat := 5

private def runChecks : IO Unit := do
  match projectedCache with
  | .error _ =>
      throw <| IO.userError "rule package projection failed"
  | .ok projected =>
      unless renderPresentation projected == renderPresentation cache do
        throw <| IO.userError "derived cache differs from the independent cache"
  unless replay canonicalDAG goal do
    throw <| IO.userError "canonical shared DAG was rejected"
  if replay canonicalDAG wrongGoal then
    throw <| IO.userError "wrong DAG root judgment was accepted"
  if replay missingChildDAG goal then
    throw <| IO.userError "missing child was accepted"
  if replay swappedChildrenDAG goal then
    throw <| IO.userError "swapped premise order was accepted"
  if replay duplicateIdDAG goal then
    throw <| IO.userError "duplicate node identifier was accepted"
  if replay forwardReferenceDAG goal then
    throw <| IO.userError "forward reference was accepted"
  if replay cycleDAG goal then
    throw <| IO.userError "cycle was accepted"
  if replay changedPremiseDAG goal then
    throw <| IO.userError "changed premise was accepted"
  if replay invalidLogicalStepDAG goal then
    throw <| IO.userError "invalid logical step was accepted"
  if replay wrongRootDAG goal then
    throw <| IO.userError "wrong root was accepted"
  unless certificateValid canonicalCertificate do
    throw <| IO.userError "canonical DAG certificate was rejected"
  if certificateValid wrongPackageCertificate then
    throw <| IO.userError "certificate crossed package identity"
  if certificateValid forgedCertificateDigest then
    throw <| IO.userError "forged certificate digest was accepted"
  unless verdictValid canonicalMustVerdict do
    throw <| IO.userError "complete Must certificate was rejected"
  if verdictValid highConfidenceInvalidVerdict then
    throw <| IO.userError "high PLN evidence repaired an invalid step"
  if verdictValid heuristicMustVerdict then
    throw <| IO.userError "heuristic pruning produced Must"
  if verdictValid incompleteEstablishedVerdict then
    throw <| IO.userError "resource incompleteness became Established Must"
  unless supportClaimValid supportedClaim do
    throw <| IO.userError "witnessed support claim was rejected"
  if supportClaimValid unsupportedPlausibleClaim then
    throw <| IO.userError "statistical plausibility replaced a witness"
  unless decodeAndCheck (renderCertificate canonicalCertificate) do
    throw <| IO.userError "canonical certificate bytes did not decode"
  if decodeAndCheck "(PrimePeTTaDAGCertificateV1" then
    throw <| IO.userError "truncated certificate was accepted"
  if decodeAndCheck (" " ++ renderCertificate canonicalCertificate) then
    throw <| IO.userError "noncanonical certificate spelling was accepted"
  unless canonicalNodeCount == 4 && canonicalEdgeCount == 4 &&
      canonicalTreeOccurrences == 5 do
    throw <| IO.userError "shared-DAG metrics changed"
  IO.println "PRIME_PETTACHAINER_DAG_BEGIN"
  IO.println (renderDAG canonicalDAG)
  IO.println "PRIME_PETTACHAINER_DAG_END"
  IO.println "PRIME_PETTACHAINER_DAG_DIGEST_BEGIN"
  IO.println (dagDigest canonicalDAG)
  IO.println "PRIME_PETTACHAINER_DAG_DIGEST_END"
  IO.println "PRIME_PETTACHAINER_CERTIFICATE_BEGIN"
  IO.println (renderCertificate canonicalCertificate)
  IO.println "PRIME_PETTACHAINER_CERTIFICATE_END"
  IO.println "(PrimePeTTaChainerDAGMetricsV1 4 4 1 5 \"5/4\")"
  IO.println "(PrimePeTTaChainerDAGReplayLeanSummaryV1 24 24 0)"

end Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1

#print axioms Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1.replay_sound
#print axioms Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1.certificateValid_sound
#print axioms Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1.decodeAndCheck_sound

#eval Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1.runChecks
