import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat
import Mettapedia.GSLT.LanguageDef.M0GCWireFormat

/-!
# Logical replay for M0GC certificates

`M0GCWireFormat` establishes exact physical framing.  This module adds the
logical admission boundary for one runtime profile and one independently
validated source calculus:

* profile and source digests are pinned;
* the ground-term heap is reconstructed chronologically from a declared
  symbol signature and every structural hash is recomputed;
* proof arguments cite reconstructed terms and premises cite earlier proof
  nodes only;
* numeric rule indices and fingerprints resolve to stable source rule IDs;
* each rule instance is re-instantiated by the ordinary source calculus;
* ordered premise results and the redundantly stored conclusion must agree
  with that independent reconstruction; and
* the final result must be the pinned goal.

Successful materialization produces an ordinary `WireArticle`.  The existing
CertificateGSLT checker then replays that article, so byte acceptance implies
a source-calculus derivation.

This module does not claim equivalence with the generated C template matcher,
completeness of M0GC for a source calculus, or compatibility with official
MMB.  Those are separate compiler and implementation-correspondence results.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat

/-! ## Runtime profile -/

/-- One physical symbol index and its source-level application head. -/
structure SymbolProfile where
  name : String
  arity : UInt16
deriving DecidableEq, Repr

/-- One physical rule index and the independently authored source rule it
selects.  Counts and fingerprints remain explicit physical guards. -/
structure RuleProfile where
  ruleId : RuleId
  argumentCount : UInt16
  premiseCount : UInt16
  fingerprint : UInt64
deriving DecidableEq, Repr

/-- Runtime identity and index tables selected for one M0GC certificate. -/
structure RuntimeProfile where
  profileDigest : List UInt8
  sourceDigest : List UInt8
  symbols : Array SymbolProfile
  rules : Array RuleProfile
deriving DecidableEq, Repr

/-- The only proof opcode currently admitted by M0GC v1. -/
def applyOpcode : UInt16 := 1

/-! ## Checked physical-table operations -/

/-- A bounded contiguous slice of a physical table. -/
def checkedSlice? (values : List α) (start count : Nat) : Option (List α) :=
  if start <= values.length && count <= values.length - start then
    some ((values.drop start).take count)
  else
    none

/-- Resolve physical indices against an already admitted chronological
prefix.  Consequently an unresolved current or future index fails closed. -/
def resolveIds? (values : Array α) : List UInt32 → Option (List α)
  | [] => some []
  | id :: ids => do
      let value ← values[id.toNat]?
      let resolved ← resolveIds? values ids
      some (value :: resolved)

/-- Exact structural term hash used by the M0GC C checker: symbol and arity,
then the stored hashes of the ordered children, all little-endian. -/
def structuralTermHash
    (symbol arity : UInt16) (childHashes : List UInt64) : UInt64 :=
  fnv1a64
    (encodeUInt16LE symbol ++ encodeUInt16LE arity ++
      childHashes.flatMap encodeUInt64LE)

/-! ## Ground-term heap reconstruction -/

structure TermState where
  patterns : Array Pattern := #[]
  hashes : Array UInt64 := #[]
deriving Repr

def materializeTermsLoop (profile : RuntimeProfile)
    (children : List UInt32) :
    List TermNode → TermState → Option TermState
  | [], state => some state
  | node :: nodes, state => do
      let symbol ← profile.symbols[node.symbol.toNat]?
      if node.arity = symbol.arity then
      let childIds ←
        checkedSlice? children node.childStart.toNat node.arity.toNat
      let childPatterns ← resolveIds? state.patterns childIds
      let childHashes ← resolveIds? state.hashes childIds
      let expectedHash := structuralTermHash node.symbol node.arity childHashes
      if node.termHash = expectedHash then
        let pattern := Pattern.apply symbol.name childPatterns
        materializeTermsLoop profile children nodes
          { patterns := state.patterns.push pattern
            hashes := state.hashes.push expectedHash }
      else none
      else none

/-- One successfully resolved term record advances the chronological state by
exactly one reconstructed application and one recomputed hash. -/
theorem materializeTermsLoop_cons_of
    {profile : RuntimeProfile} {children : List UInt32}
    {node : TermNode} {nodes : List TermNode} {state : TermState}
    {symbol : SymbolProfile} {childIds : List UInt32}
    {childPatterns : List Pattern} {childHashes : List UInt64}
    (symbolResolves : profile.symbols[node.symbol.toNat]? = some symbol)
    (arityMatches : node.arity = symbol.arity)
    (sliceResolves :
      checkedSlice? children node.childStart.toNat node.arity.toNat =
        some childIds)
    (patternsResolve : resolveIds? state.patterns childIds = some childPatterns)
    (hashesResolve : resolveIds? state.hashes childIds = some childHashes)
    (hashMatches :
      node.termHash = structuralTermHash node.symbol node.arity childHashes) :
    materializeTermsLoop profile children (node :: nodes) state =
      materializeTermsLoop profile children nodes
        { patterns := state.patterns.push (.apply symbol.name childPatterns)
          hashes := state.hashes.push
            (structuralTermHash node.symbol node.arity childHashes) } := by
  rw [materializeTermsLoop, symbolResolves]
  dsimp
  rw [if_pos arityMatches]
  rw [sliceResolves]
  dsimp
  rw [patternsResolve]
  dsimp
  rw [hashesResolve]
  dsimp
  rw [if_pos hashMatches]

def materializeTerms? (profile : RuntimeProfile)
    (certificate : Certificate) : Option TermState :=
  materializeTermsLoop profile certificate.children certificate.terms {}

/-- Ground-term materialization depends only on the selected symbol table.
Proof-rule, digest, and other runtime-profile fields cannot affect it. -/
theorem materializeTermsLoop_congr_symbols
    {left right : RuntimeProfile}
    (symbolsEq : left.symbols = right.symbols)
    (children : List UInt32) (nodes : List TermNode) (state : TermState) :
    materializeTermsLoop left children nodes state =
      materializeTermsLoop right children nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes inductionHypothesis =>
      simp [materializeTermsLoop, symbolsEq, inductionHypothesis]

/-! ## Chronological proof reconstruction -/

structure ProofState where
  nodes : Array OpenDAGNode := #[]
  results : Array Pattern := #[]
deriving Repr

def materializeProofsLoop (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) (terms : Array Pattern)
    (arguments premiseReferences : List UInt32) :
    List ProofNode → ProofState → Option ProofState
  | [], state => some state
  | proof :: proofs, state => do
      if proof.opcode = applyOpcode then
      let rule ← profile.rules[proof.rule.toNat]?
      if proof.ruleFingerprint = rule.fingerprint then
      if proof.argumentCount = rule.argumentCount then
      if proof.premiseCount = rule.premiseCount then
      let argumentIds ← checkedSlice? arguments
        proof.argumentStart.toNat proof.argumentCount.toNat
      let premiseIds ← checkedSlice? premiseReferences
        proof.premiseStart.toNat proof.premiseCount.toNat
      let ruleArguments ← resolveIds? terms argumentIds
      let premiseResults ← resolveIds? state.results premiseIds
      let explicitResult ← terms[proof.resultTerm.toNat]?
      let ruleInstance : RuleInstance :=
        { ruleId := rule.ruleId, arguments := ruleArguments }
      let (expectedPremises, expectedConclusion) ←
        instantiateRule? definition ruleInstance
      if expectedPremises = premiseResults then
      if expectedConclusion = explicitResult then
        let node : OpenDAGNode :=
          { id := state.nodes.size
            ruleInstance
            children := premiseIds.map (OpenDAGReference.node ∘ UInt32.toNat) }
        materializeProofsLoop definition profile terms arguments
          premiseReferences proofs
          { nodes := state.nodes.push node
            results := state.results.push expectedConclusion }
      else none
      else none
      else none
      else none
      else none
      else none

/-- One fully checked proof record advances both chronological arrays by one
source-reconstructed rule application. -/
theorem materializeProofsLoop_cons_of
    {definition : ValidatedCalculusLanguageDef} {profile : RuntimeProfile}
    {terms : Array Pattern} {arguments premiseReferences : List UInt32}
    {proof : ProofNode} {proofs : List ProofNode} {state : ProofState}
    {rule : RuleProfile} {argumentIds premiseIds : List UInt32}
    {ruleArguments premiseResults : List Pattern}
    {explicitResult : Pattern} {expectedPremises : List Pattern}
    {expectedConclusion : Pattern}
    (opcodeMatches : proof.opcode = applyOpcode)
    (ruleResolves : profile.rules[proof.rule.toNat]? = some rule)
    (fingerprintMatches : proof.ruleFingerprint = rule.fingerprint)
    (argumentCountMatches : proof.argumentCount = rule.argumentCount)
    (premiseCountMatches : proof.premiseCount = rule.premiseCount)
    (argumentSliceResolves :
      checkedSlice? arguments proof.argumentStart.toNat
        proof.argumentCount.toNat = some argumentIds)
    (premiseSliceResolves :
      checkedSlice? premiseReferences proof.premiseStart.toNat
        proof.premiseCount.toNat = some premiseIds)
    (argumentsResolve : resolveIds? terms argumentIds = some ruleArguments)
    (premisesResolve : resolveIds? state.results premiseIds = some premiseResults)
    (resultResolves : terms[proof.resultTerm.toNat]? = some explicitResult)
    (ruleInstantiates :
      instantiateRule? definition
        { ruleId := rule.ruleId, arguments := ruleArguments } =
          some (expectedPremises, expectedConclusion))
    (premisesMatch : expectedPremises = premiseResults)
    (conclusionMatches : expectedConclusion = explicitResult) :
    materializeProofsLoop definition profile terms arguments premiseReferences
        (proof :: proofs) state =
      materializeProofsLoop definition profile terms arguments premiseReferences
        proofs
        { nodes := state.nodes.push
            { id := state.nodes.size
              ruleInstance :=
                { ruleId := rule.ruleId, arguments := ruleArguments }
              children :=
                premiseIds.map (OpenDAGReference.node ∘ UInt32.toNat) }
          results := state.results.push expectedConclusion } := by
  rw [materializeProofsLoop]
  rw [if_pos opcodeMatches]
  rw [ruleResolves]
  dsimp
  rw [if_pos fingerprintMatches]
  rw [if_pos argumentCountMatches]
  rw [if_pos premiseCountMatches]
  rw [argumentSliceResolves]
  dsimp
  rw [premiseSliceResolves]
  dsimp
  rw [argumentsResolve]
  dsimp
  rw [premisesResolve]
  dsimp
  rw [resultResolves]
  dsimp
  rw [ruleInstantiates]
  dsimp
  rw [if_pos premisesMatch]
  rw [if_pos conclusionMatches]

/-- Even when every physical reference and source-rule premise resolves, an
explicit result that differs from the independently reconstructed conclusion
is rejected. -/
theorem materializeProofsLoop_conclusion_mismatch
    {definition : ValidatedCalculusLanguageDef} {profile : RuntimeProfile}
    {terms : Array Pattern} {arguments premiseReferences : List UInt32}
    {proof : ProofNode} {proofs : List ProofNode} {state : ProofState}
    {rule : RuleProfile} {argumentIds premiseIds : List UInt32}
    {ruleArguments premiseResults : List Pattern}
    {explicitResult : Pattern} {expectedPremises : List Pattern}
    {expectedConclusion : Pattern}
    (opcodeMatches : proof.opcode = applyOpcode)
    (ruleResolves : profile.rules[proof.rule.toNat]? = some rule)
    (fingerprintMatches : proof.ruleFingerprint = rule.fingerprint)
    (argumentCountMatches : proof.argumentCount = rule.argumentCount)
    (premiseCountMatches : proof.premiseCount = rule.premiseCount)
    (argumentSliceResolves :
      checkedSlice? arguments proof.argumentStart.toNat
        proof.argumentCount.toNat = some argumentIds)
    (premiseSliceResolves :
      checkedSlice? premiseReferences proof.premiseStart.toNat
        proof.premiseCount.toNat = some premiseIds)
    (argumentsResolve : resolveIds? terms argumentIds = some ruleArguments)
    (premisesResolve : resolveIds? state.results premiseIds = some premiseResults)
    (resultResolves : terms[proof.resultTerm.toNat]? = some explicitResult)
    (ruleInstantiates :
      instantiateRule? definition
        { ruleId := rule.ruleId, arguments := ruleArguments } =
          some (expectedPremises, expectedConclusion))
    (premisesMatch : expectedPremises = premiseResults)
    (conclusionMismatch : expectedConclusion ≠ explicitResult) :
    materializeProofsLoop definition profile terms arguments premiseReferences
        (proof :: proofs) state = none := by
  rw [materializeProofsLoop]
  rw [if_pos opcodeMatches]
  rw [ruleResolves]
  dsimp
  rw [if_pos fingerprintMatches]
  rw [if_pos argumentCountMatches]
  rw [if_pos premiseCountMatches]
  rw [argumentSliceResolves]
  dsimp
  rw [premiseSliceResolves]
  dsimp
  rw [argumentsResolve]
  dsimp
  rw [premisesResolve]
  dsimp
  rw [resultResolves]
  dsimp
  rw [ruleInstantiates]
  dsimp
  rw [if_pos premisesMatch]
  rw [if_neg conclusionMismatch]

def materializeProofs? (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) (terms : Array Pattern)
    (certificate : Certificate) : Option ProofState :=
  materializeProofsLoop definition profile terms certificate.arguments
    certificate.premises certificate.proofs {}

/-! ## Complete materialization and checking -/

/-- Reconstruct an ordinary logical article from a physically decoded M0GC
certificate.  Profile identity, source identity, term topology, proof
chronology, source-rule instantiation, explicit results, and the final goal
are all checked before an article is returned. -/
def materializeArticle? (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) (certificate : Certificate) :
    Option WireArticle := do
  if profile.profileDigest.length = digestWidth then
  if profile.sourceDigest.length = digestWidth then
  if certificate.profileDigest = profile.profileDigest then
  if certificate.sourceDigest = profile.sourceDigest then
  let terms ← materializeTerms? profile certificate
  let proofs ← materializeProofs? definition profile terms.patterns certificate
  let goal ← terms.patterns[certificate.goalTerm.toNat]?
  let rootId := proofs.nodes.size - 1
  let finalResult ← proofs.results[rootId]?
  if finalResult = goal then
    some
      { version := wireArticleVersion
        nodes := proofs.nodes.toList
        rootId
        target := goal }
  else none
  else none
  else none
  else none
  else none

/-- Check a decoded certificate against both a submitted claim and the source
calculus.  The submitted claim is not inferred from the certificate. -/
def checkCertificate (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) (submitted : Pattern)
    (certificate : Certificate) : Bool :=
  match materializeArticle? definition profile certificate with
  | none => false
  | some article =>
      decide (article.target = submitted) &&
        checkWireArticle definition article

/-- Decode exact M0GC bytes, materialize their logical article, and replay it
against the independently supplied source calculus. -/
def checkBytes (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) (submitted : Pattern)
    (bytes : List UInt8) : Bool :=
  match decodeCertificate? bytes with
  | none => false
  | some certificate => checkCertificate definition profile submitted certificate

/-- Logical soundness of decoded-certificate admission. -/
theorem checkCertificate_sound
    {definition : ValidatedCalculusLanguageDef}
    {profile : RuntimeProfile} {submitted : Pattern}
    {certificate : Certificate}
    (accepted : checkCertificate definition profile submitted certificate = true) :
    Nonempty (Derivation definition submitted) := by
  unfold checkCertificate at accepted
  cases materialized : materializeArticle? definition profile certificate with
  | none => simp [materialized] at accepted
  | some article =>
      simp only [materialized, Bool.and_eq_true, decide_eq_true_eq] at accepted
      rw [← accepted.1]
      exact checkWireArticle_sound accepted.2

/-- End-to-end logical soundness from exact bytes. -/
theorem checkBytes_sound
    {definition : ValidatedCalculusLanguageDef}
    {profile : RuntimeProfile} {submitted : Pattern} {bytes : List UInt8}
    (accepted : checkBytes definition profile submitted bytes = true) :
    Nonempty (Derivation definition submitted) := by
  unfold checkBytes at accepted
  cases decoded : decodeCertificate? bytes with
  | none => simp [decoded] at accepted
  | some certificate =>
      exact checkCertificate_sound (by simpa [decoded] using accepted)

#print axioms checkCertificate_sound
#print axioms checkBytes_sound
#print axioms materializeTermsLoop_congr_symbols
#print axioms materializeProofsLoop_conclusion_mismatch

end Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
