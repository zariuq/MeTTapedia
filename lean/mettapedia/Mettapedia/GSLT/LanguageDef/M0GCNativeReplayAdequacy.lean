import Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification

/-!
# Source-level adequacy boundary for the native M0GC replay loop

The connected M0GC C checker keeps only raw term identifiers while replaying
proof records.  Premise references select earlier result identifiers, and the
physical rule matcher compares those identifiers directly against generated
flat templates.  This module gives that control loop an executable Lean model
and relates its accepted states to the independently validated source
calculus.

Maturity boundary: this is a fully connected source-level model of the
current custom M0GC proof-of-concept replay core.  It is not a semantics of C
text, pointers, packed records, a compiler, object code, or hardware.  The
flat tables, recursive matcher, fixed depth bound, and raw result array are
explicitly non-endgame mechanisms.  Later optimized implementations must
replace them behind the same decoding, chronology, and source-derivation
obligations rather than inheriting their layout accidentally.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification

/-! ## Exact raw-identifier control state -/

/-- The only hot proof state retained by the current native replay core.
Entry `i` is the raw certificate term identifier concluded by proof `i`. -/
structure NativeProofState where
  resultIds : Array UInt32 := #[]
deriving DecidableEq, Repr

/-- Source-level model of the current C `replay` loop after exact wire loading
and chronological term validation.  It deliberately performs identifier
matching rather than reconstructing a source rule instance.

The explicit resolution of every argument identifier mirrors the C range
guard.  Resolving premise references against `state.resultIds` enforces the C
condition that every premise names a strictly earlier proof node. -/
def nativeReplayLoop (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat) :
    List ProofNode → NativeProofState → Option NativeProofState
  | [], state => some state
  | proof :: proofs, state => do
      if proof.opcode = applyOpcode then
      let rule ← profile.rules[proof.rule.toNat]?
      if proof.ruleFingerprint = rule.fingerprint then
      if proof.argumentCount = rule.argumentCount then
      if proof.premiseCount = rule.premiseCount then
      let argumentIds ← checkedSlice? certificate.arguments
        proof.argumentStart.toNat proof.argumentCount.toNat
      let premiseReferences ← checkedSlice? certificate.premises
        proof.premiseStart.toNat proof.premiseCount.toNat
      let _argumentPatterns ← resolveIds? terms.patterns argumentIds
      let premiseConcreteIds ← resolveIds? state.resultIds premiseReferences
      let _conclusion ← terms.patterns[proof.resultTerm.toNat]?
      if matchRuleIds profile tables certificate argumentIds fuel proof.rule
          premiseConcreteIds proof.resultTerm then
        nativeReplayLoop profile tables certificate terms fuel proofs
          { resultIds := state.resultIds.push proof.resultTerm }
      else none
      else none
      else none
      else none
      else none

/-- One fully admitted raw proof record advances the result-identifier array
by exactly its declared conclusion identifier. -/
theorem nativeReplayLoop_cons_of
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proof : ProofNode} {proofs : List ProofNode}
    {state : NativeProofState} {rule : RuleProfile}
    {argumentIds premiseReferences premiseConcreteIds : List UInt32}
    {argumentPatterns : List Pattern} {conclusion : Pattern}
    (opcodeMatches : proof.opcode = applyOpcode)
    (ruleResolves : profile.rules[proof.rule.toNat]? = some rule)
    (fingerprintMatches : proof.ruleFingerprint = rule.fingerprint)
    (argumentCountMatches : proof.argumentCount = rule.argumentCount)
    (premiseCountMatches : proof.premiseCount = rule.premiseCount)
    (argumentSliceResolves :
      checkedSlice? certificate.arguments proof.argumentStart.toNat
        proof.argumentCount.toNat = some argumentIds)
    (premiseSliceResolves :
      checkedSlice? certificate.premises proof.premiseStart.toNat
        proof.premiseCount.toNat = some premiseReferences)
    (argumentsResolve :
      resolveIds? terms.patterns argumentIds = some argumentPatterns)
    (premisesResolve :
      resolveIds? state.resultIds premiseReferences = some premiseConcreteIds)
    (conclusionResolves :
      terms.patterns[proof.resultTerm.toNat]? = some conclusion)
    (ruleMatches :
      matchRuleIds profile tables certificate argumentIds fuel proof.rule
        premiseConcreteIds proof.resultTerm = true) :
    nativeReplayLoop profile tables certificate terms fuel
        (proof :: proofs) state =
      nativeReplayLoop profile tables certificate terms fuel proofs
        { resultIds := state.resultIds.push proof.resultTerm } := by
  rw [nativeReplayLoop]
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
  rw [conclusionResolves]
  dsimp
  rw [if_pos ruleMatches]

/-- A physical template mismatch rejects the proof record without advancing
the raw state. -/
theorem nativeReplayLoop_rule_mismatch
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proof : ProofNode} {proofs : List ProofNode}
    {state : NativeProofState} {rule : RuleProfile}
    {argumentIds premiseReferences premiseConcreteIds : List UInt32}
    {argumentPatterns : List Pattern} {conclusion : Pattern}
    (opcodeMatches : proof.opcode = applyOpcode)
    (ruleResolves : profile.rules[proof.rule.toNat]? = some rule)
    (fingerprintMatches : proof.ruleFingerprint = rule.fingerprint)
    (argumentCountMatches : proof.argumentCount = rule.argumentCount)
    (premiseCountMatches : proof.premiseCount = rule.premiseCount)
    (argumentSliceResolves :
      checkedSlice? certificate.arguments proof.argumentStart.toNat
        proof.argumentCount.toNat = some argumentIds)
    (premiseSliceResolves :
      checkedSlice? certificate.premises proof.premiseStart.toNat
        proof.premiseCount.toNat = some premiseReferences)
    (argumentsResolve :
      resolveIds? terms.patterns argumentIds = some argumentPatterns)
    (premisesResolve :
      resolveIds? state.resultIds premiseReferences = some premiseConcreteIds)
    (conclusionResolves :
      terms.patterns[proof.resultTerm.toNat]? = some conclusion)
    (ruleMismatch :
      matchRuleIds profile tables certificate argumentIds fuel proof.rule
        premiseConcreteIds proof.resultTerm = false) :
    nativeReplayLoop profile tables certificate terms fuel
        (proof :: proofs) state = none := by
  rw [nativeReplayLoop]
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
  rw [conclusionResolves]
  dsimp
  rw [if_neg (by simpa using Bool.eq_false_iff.mp ruleMismatch)]

/-- A mismatched rule fingerprint fails before any template traversal. -/
theorem nativeReplayLoop_fingerprint_mismatch
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proof : ProofNode} {proofs : List ProofNode}
    {state : NativeProofState} {rule : RuleProfile}
    (opcodeMatches : proof.opcode = applyOpcode)
    (ruleResolves : profile.rules[proof.rule.toNat]? = some rule)
    (fingerprintMismatch : proof.ruleFingerprint ≠ rule.fingerprint) :
    nativeReplayLoop profile tables certificate terms fuel
        (proof :: proofs) state = none := by
  rw [nativeReplayLoop]
  rw [if_pos opcodeMatches]
  rw [ruleResolves]
  dsimp
  rw [if_neg fingerprintMismatch]

/-- Complete raw replay after profile identity and chronological term loading.
The final raw result identifier must equal the certificate's separately pinned
goal identifier, exactly as in the C replay core. -/
def nativeReplay? (profile : RuntimeProfile) (tables : RuleTables)
    (fuel : Nat) (certificate : Certificate) :
    Option (TermState × NativeProofState) := do
  if profile.profileDigest.length = digestWidth then
  if profile.sourceDigest.length = digestWidth then
  if certificate.profileDigest = profile.profileDigest then
  if certificate.sourceDigest = profile.sourceDigest then
  let terms ← materializeTerms? profile certificate
  let _goal ← terms.patterns[certificate.goalTerm.toNat]?
  let proofs ← nativeReplayLoop profile tables certificate terms fuel
    certificate.proofs {}
  let finalResultId ← proofs.resultIds[proofs.resultIds.size - 1]?
  if finalResultId = certificate.goalTerm then
    some (terms, proofs)
  else none
  else none
  else none
  else none
  else none

/-- NIK-facing decoded-certificate observation: raw native replay must succeed,
and the pinned goal term must be exactly the separately submitted claim. -/
def nativeCheckCertificate (profile : RuntimeProfile) (tables : RuleTables)
    (fuel : Nat) (submitted : Pattern) (certificate : Certificate) : Bool :=
  match nativeReplay? profile tables fuel certificate with
  | none => false
  | some (terms, _) =>
      match terms.patterns[certificate.goalTerm.toNat]? with
      | none => false
      | some goal => decide (goal = submitted)

/-- Exact wire decoding followed by the raw native replay model. -/
def nativeCheckBytes (profile : RuntimeProfile) (tables : RuleTables)
    (fuel : Nat) (submitted : Pattern) (bytes : List UInt8) : Bool :=
  match decodeCertificate? bytes with
  | none => false
  | some certificate =>
      nativeCheckCertificate profile tables fuel submitted certificate

/-! ## Relation to ordinary logical replay -/

/-- The raw C-style result identifiers and the ordinary logical replay state
have the same chronology and denote the same source patterns. -/
structure ReplayStateRelation (terms : Array Pattern)
    (native : NativeProofState) (logical : ProofState) : Prop where
  resultCount : logical.results.size = native.resultIds.size
  nodeCount : logical.nodes.size = native.resultIds.size
  realizes : ∀ {index : Nat} {termId : UInt32},
    native.resultIds[index]? = some termId →
      ∃ pattern,
        logical.results[index]? = some pattern ∧
        terms[termId.toNat]? = some pattern

/-- Every logical result accumulated so far has an actual typed derivation in
the independently validated source calculus. -/
def ProofStateSound (definition : ValidatedCalculusLanguageDef)
    (state : ProofState) : Prop :=
  ∀ {index : Nat} {pattern : Pattern},
    state.results[index]? = some pattern →
      Nonempty (Derivation definition pattern)

theorem ReplayStateRelation.empty (terms : Array Pattern) :
    ReplayStateRelation terms {} {} := by
  constructor <;> simp

theorem ProofStateSound.empty (definition : ValidatedCalculusLanguageDef) :
    ProofStateSound definition {} := by
  intro index pattern patternEq
  simp at patternEq

/-- Pointwise proof soundness turns any successfully resolved ordered premise
vector into the correspondingly indexed typed derivation list. -/
theorem ProofStateSound.derivationList_of_resolve
    {definition : ValidatedCalculusLanguageDef} {state : ProofState}
    (sound : ProofStateSound definition state)
    {references : List UInt32} {patterns : List Pattern}
    (resolved : resolveIds? state.results references = some patterns) :
    Nonempty (DerivationList definition patterns) := by
  induction references generalizing patterns with
  | nil =>
      simp [resolveIds?] at resolved
      subst patterns
      exact ⟨DerivationList.nil⟩
  | cons reference references inductionHypothesis =>
      cases headEq : state.results[reference.toNat]? with
      | none => simp [resolveIds?, headEq] at resolved
      | some head =>
          cases tailEq : resolveIds? state.results references with
          | none => simp [resolveIds?, headEq, tailEq] at resolved
          | some tail =>
              simp [resolveIds?, headEq, tailEq] at resolved
              subst patterns
              obtain ⟨headProof⟩ := sound headEq
              obtain ⟨tailProofs⟩ := inductionHypothesis tailEq
              exact ⟨DerivationList.cons headProof tailProofs⟩

/-- Appending a newly derived conclusion preserves pointwise proof soundness. -/
theorem ProofStateSound.push
    {definition : ValidatedCalculusLanguageDef} {logical : ProofState}
    (sound : ProofStateSound definition logical)
    {conclusion : Pattern}
    (conclusionProof : Nonempty (Derivation definition conclusion))
    (node : OpenDAGNode) :
    ProofStateSound definition
      { nodes := logical.nodes.push node
        results := logical.results.push conclusion } := by
  intro index pattern patternEq
  by_cases inPrefix : index < logical.results.size
  · have indexNe : index ≠ logical.results.size := Nat.ne_of_lt inPrefix
    have oldEq : logical.results[index]? = some pattern := by
      simpa [Array.getElem?_push, indexNe] using patternEq
    exact sound oldEq
  · have inExtended : index < logical.results.size + 1 := by
      simpa using (Array.getElem?_eq_some_iff.mp patternEq).choose
    have indexEq : index = logical.results.size := by omega
    subst index
    have patternIsConclusion : conclusion = pattern := by
      simpa using patternEq
    subst pattern
    exact conclusionProof

/-- Resolve the same chronological proof references through a raw identifier
state and a related logical result state.  The resulting concrete term IDs
and logical premise patterns agree pointwise through the loaded term table. -/
theorem resolveIds?_through_relation
    {termIds : Array UInt32} {logicalResults terms : Array Pattern}
    (realizes : ∀ {index : Nat} {termId : UInt32},
      termIds[index]? = some termId →
        ∃ pattern,
          logicalResults[index]? = some pattern ∧
          terms[termId.toNat]? = some pattern)
    {references concreteIds : List UInt32}
    (rawResolved : resolveIds? termIds references = some concreteIds) :
    ∃ patterns,
      resolveIds? logicalResults references = some patterns ∧
      resolveIds? terms concreteIds = some patterns := by
  induction references generalizing concreteIds with
  | nil =>
      simp [resolveIds?] at rawResolved
      subst concreteIds
      exact ⟨[], rfl, rfl⟩
  | cons reference references inductionHypothesis =>
      cases rawHead : termIds[reference.toNat]? with
      | none => simp [resolveIds?, rawHead] at rawResolved
      | some concreteId =>
          cases rawTail : resolveIds? termIds references with
          | none => simp [resolveIds?, rawHead, rawTail] at rawResolved
          | some concreteTail =>
              simp [resolveIds?, rawHead, rawTail] at rawResolved
              subst concreteIds
              obtain ⟨pattern, logicalHead, termHead⟩ := realizes rawHead
              obtain ⟨patterns, logicalTail, termTail⟩ :=
                inductionHypothesis rawTail
              exact ⟨pattern :: patterns,
                by simp [resolveIds?, logicalHead, logicalTail],
                by simp [resolveIds?, termHead, termTail]⟩

/-- Appending one raw result identifier and its proved logical conclusion
preserves the replay-state relation. -/
theorem ReplayStateRelation.push
    {terms : Array Pattern} {native : NativeProofState}
    {logical : ProofState} (relation : ReplayStateRelation terms native logical)
    {termId : UInt32} {conclusion : Pattern}
    (termResolves : terms[termId.toNat]? = some conclusion)
    (node : OpenDAGNode) :
    ReplayStateRelation terms
      { resultIds := native.resultIds.push termId }
      { nodes := logical.nodes.push node
        results := logical.results.push conclusion } := by
  constructor
  · simp [relation.resultCount]
  · simp [relation.nodeCount]
  · intro index queriedId queriedIdEq
    by_cases inPrefix : index < native.resultIds.size
    · have indexNe : index ≠ native.resultIds.size := Nat.ne_of_lt inPrefix
      have oldIdEq : native.resultIds[index]? = some queriedId := by
        simpa [Array.getElem?_push, indexNe] using queriedIdEq
      obtain ⟨pattern, logicalEq, termEq⟩ := relation.realizes oldIdEq
      have logicalIndexNe : index ≠ logical.results.size := by
        rw [relation.resultCount]
        exact indexNe
      exact ⟨pattern,
        by simpa [Array.getElem?_push, logicalIndexNe] using logicalEq,
        termEq⟩
    · have inExtended : index < native.resultIds.size + 1 := by
        simpa using (Array.getElem?_eq_some_iff.mp queriedIdEq).choose
      have indexEq : index = native.resultIds.size := by omega
      subst index
      have queriedEq : termId = queriedId := by
        simpa using queriedIdEq
      subst queriedId
      refine ⟨conclusion, ?_, termResolves⟩
      rw [← relation.resultCount]
      simp

/-- One raw native proof step selected from a connected generated profile is
an ordinary step of the independently validated source calculus.  This is the
local commuting square used by the whole-loop simulation. -/
theorem qualified_native_step_simulates
    {candidate : Candidate} (connected : candidate.Connected)
    {certificate : Certificate} {terms : TermState}
    (termsMaterialized :
      materializeTerms? candidate.physical.profile certificate = some terms)
    {proof : ProofNode} {proofs : List ProofNode}
    {native : NativeProofState} {logical : ProofState}
    (relation : ReplayStateRelation terms.patterns native logical)
    (logicalSound :
      ProofStateSound (candidate.validatedSource connected) logical)
    {physicalRule : RuleProfile}
    {argumentIds premiseReferences premiseConcreteIds : List UInt32}
    {argumentPatterns : List Pattern} {conclusion : Pattern}
    (opcodeMatches : proof.opcode = applyOpcode)
    (ruleResolves :
      candidate.physical.profile.rules[proof.rule.toNat]? = some physicalRule)
    (fingerprintMatches :
      proof.ruleFingerprint = physicalRule.fingerprint)
    (argumentCountMatches : proof.argumentCount = physicalRule.argumentCount)
    (premiseCountMatches : proof.premiseCount = physicalRule.premiseCount)
    (argumentSliceResolves :
      checkedSlice? certificate.arguments proof.argumentStart.toNat
        proof.argumentCount.toNat = some argumentIds)
    (premiseSliceResolves :
      checkedSlice? certificate.premises proof.premiseStart.toNat
        proof.premiseCount.toNat = some premiseReferences)
    (argumentsResolve :
      resolveIds? terms.patterns argumentIds = some argumentPatterns)
    (premisesResolve :
      resolveIds? native.resultIds premiseReferences = some premiseConcreteIds)
    (conclusionResolves :
      terms.patterns[proof.resultTerm.toNat]? = some conclusion)
    (ruleMatches :
      matchRuleIds candidate.physical.profile candidate.physical.tables
        certificate argumentIds candidate.decodeFuel proof.rule
        premiseConcreteIds proof.resultTerm = true) :
    ∃ logicalNext,
      materializeProofsLoop (candidate.validatedSource connected)
          candidate.physical.profile terms.patterns certificate.arguments
          certificate.premises (proof :: proofs) logical =
        materializeProofsLoop (candidate.validatedSource connected)
          candidate.physical.profile terms.patterns certificate.arguments
          certificate.premises proofs logicalNext ∧
      ReplayStateRelation terms.patterns
        { resultIds := native.resultIds.push proof.resultTerm } logicalNext ∧
      ProofStateSound (candidate.validatedSource connected) logicalNext := by
  obtain ⟨sourceRule, template, _sourceAtIndex, ruleIdEq,
      _argumentCountEq, _premiseCountEq, _fingerprintEq,
      sourceCompiled, physicalDecodedAtIndex, sourceLookup⟩ :=
    selected_physical_rule_qualifies connected ruleResolves
  have physicalDecoded :
      decodeRuleTemplate? candidate.physical.profile
          candidate.physical.tables candidate.decodeFuel proof.rule =
        some template := by
    simpa using physicalDecodedAtIndex
  obtain ⟨premisePatterns, logicalPremisesResolve,
      concretePremisesResolve⟩ :=
    resolveIds?_through_relation relation.realizes premisesResolve
  have templateInstantiates :
      template.instantiate? argumentPatterns =
        some (premisePatterns, conclusion) :=
    matchRuleIds_sound_of_decode termsMaterialized argumentsResolve
      physicalDecoded ruleMatches concretePremisesResolve conclusionResolves
  have everyArgumentValid : ∀ argument ∈ argumentPatterns,
      argumentValidAt 0 argument = true :=
    resolveIds?_argumentValidAt_zero
      (fun patternEq =>
        materializeTerms?_argumentValidAt_zero termsMaterialized patternEq)
      argumentsResolve
  have argumentLength :
      argumentPatterns.length = sourceRule.formals.length := by
    calc
      argumentPatterns.length = template.formalCount :=
        RuleTemplate.argument_length_of_instantiate templateInstantiates
      _ = sourceRule.toRuleSchema.metavariables.length :=
        compileRuleTemplate?_formalCount sourceCompiled
      _ = sourceRule.formals.length := by
        simp [SourceRule.toRuleSchema]
  have argumentsValid :
      argumentsValidAt sourceRule.toRuleSchema.metavariables
        argumentPatterns = true := by
    change argumentsValidAt
      (sourceRule.formals.map fun name => (name, 0)) argumentPatterns = true
    exact argumentsValidAt_map_zero sourceRule.formals argumentPatterns
      argumentLength everyArgumentValid
  have sourceInstantiates :
      instantiateRule? (candidate.validatedSource connected)
          { ruleId := sourceRule.toRuleSchema.id
            arguments := argumentPatterns } =
        some (premisePatterns, conclusion) := by
    rw [← RuleTemplate.instantiate_eq_source_rule sourceCompiled
      argumentPatterns sourceLookup argumentsValid]
    exact templateInstantiates
  have nativeRuleInstantiates :
      instantiateRule? (candidate.validatedSource connected)
          { ruleId := physicalRule.ruleId
            arguments := argumentPatterns } =
        some (premisePatterns, conclusion) := by
    simpa [ruleIdEq] using sourceInstantiates
  let ruleInstance : RuleInstance :=
    { ruleId := physicalRule.ruleId
      arguments := argumentPatterns }
  let node : OpenDAGNode :=
    { id := logical.nodes.size
      ruleInstance
      children :=
        premiseReferences.map (OpenDAGReference.node ∘ UInt32.toNat) }
  let logicalNext : ProofState :=
    { nodes := logical.nodes.push node
      results := logical.results.push conclusion }
  have ruleInstanceInstantiates :
      instantiateRule? (candidate.validatedSource connected) ruleInstance =
        some (premisePatterns, conclusion) := by
    simpa [ruleInstance] using nativeRuleInstantiates
  obtain ⟨children⟩ :=
    logicalSound.derivationList_of_resolve logicalPremisesResolve
  have conclusionProof :
      Derivation (candidate.validatedSource connected) conclusion :=
    Derivation.byRule ruleInstance
      (instantiateRule?_eq_some_iff_application.mp ruleInstanceInstantiates)
      children
  refine ⟨logicalNext, ?_, ?_, ?_⟩
  · exact materializeProofsLoop_cons_of
      (rule := physicalRule) (argumentIds := argumentIds)
      (premiseIds := premiseReferences) (ruleArguments := argumentPatterns)
      (premiseResults := premisePatterns) (explicitResult := conclusion)
      (expectedPremises := premisePatterns) (expectedConclusion := conclusion)
      opcodeMatches ruleResolves fingerprintMatches argumentCountMatches
      premiseCountMatches argumentSliceResolves premiseSliceResolves
      argumentsResolve logicalPremisesResolve conclusionResolves
      nativeRuleInstantiates rfl rfl
  · exact relation.push conclusionResolves node
  · exact logicalSound.push ⟨conclusionProof⟩ node

/-- Whole-loop simulation: every successful raw identifier replay over a
connected generated profile materializes as the ordinary source-calculus
proof loop, with chronology and conclusions related at every prefix. -/
theorem nativeReplayLoop_simulates_logical
    {candidate : Candidate} (connected : candidate.Connected)
    {certificate : Certificate} {terms : TermState}
    (termsMaterialized :
      materializeTerms? candidate.physical.profile certificate = some terms)
    {proofs : List ProofNode}
    {native finalNative : NativeProofState} {logical : ProofState}
    (relation : ReplayStateRelation terms.patterns native logical)
    (logicalSound :
      ProofStateSound (candidate.validatedSource connected) logical)
    (accepted :
      nativeReplayLoop candidate.physical.profile candidate.physical.tables
          certificate terms candidate.decodeFuel proofs native =
        some finalNative) :
    ∃ finalLogical,
      materializeProofsLoop (candidate.validatedSource connected)
          candidate.physical.profile terms.patterns certificate.arguments
          certificate.premises proofs logical = some finalLogical ∧
      ReplayStateRelation terms.patterns finalNative finalLogical ∧
      ProofStateSound (candidate.validatedSource connected) finalLogical := by
  induction proofs generalizing native logical finalNative with
  | nil =>
      simp [nativeReplayLoop] at accepted
      subst finalNative
      exact ⟨logical, rfl, relation, logicalSound⟩
  | cons proof proofs inductionHypothesis =>
      rw [nativeReplayLoop] at accepted
      by_cases opcodeMatches : proof.opcode = applyOpcode
      · rw [if_pos opcodeMatches] at accepted
        cases ruleResolves :
            candidate.physical.profile.rules[proof.rule.toNat]? with
        | none => simp [ruleResolves] at accepted
        | some physicalRule =>
            rw [ruleResolves] at accepted
            dsimp at accepted
            by_cases fingerprintMatches :
                proof.ruleFingerprint = physicalRule.fingerprint
            · rw [if_pos fingerprintMatches] at accepted
              by_cases argumentCountMatches :
                  proof.argumentCount = physicalRule.argumentCount
              · rw [if_pos argumentCountMatches] at accepted
                by_cases premiseCountMatches :
                    proof.premiseCount = physicalRule.premiseCount
                · rw [if_pos premiseCountMatches] at accepted
                  cases argumentSliceResolves :
                      checkedSlice? certificate.arguments
                        proof.argumentStart.toNat
                        proof.argumentCount.toNat with
                  | none => simp [argumentSliceResolves] at accepted
                  | some argumentIds =>
                      rw [argumentSliceResolves] at accepted
                      dsimp at accepted
                      cases premiseSliceResolves :
                          checkedSlice? certificate.premises
                            proof.premiseStart.toNat
                            proof.premiseCount.toNat with
                      | none => simp [premiseSliceResolves] at accepted
                      | some premiseReferences =>
                          rw [premiseSliceResolves] at accepted
                          dsimp at accepted
                          cases argumentsResolve :
                              resolveIds? terms.patterns argumentIds with
                          | none => simp [argumentsResolve] at accepted
                          | some argumentPatterns =>
                              rw [argumentsResolve] at accepted
                              dsimp at accepted
                              cases premisesResolve :
                                  resolveIds? native.resultIds
                                    premiseReferences with
                              | none => simp [premisesResolve] at accepted
                              | some premiseConcreteIds =>
                                  rw [premisesResolve] at accepted
                                  dsimp at accepted
                                  cases conclusionResolves :
                                      terms.patterns[
                                        proof.resultTerm.toNat]? with
                                  | none =>
                                      simp [conclusionResolves] at accepted
                                  | some conclusion =>
                                      rw [conclusionResolves] at accepted
                                      dsimp at accepted
                                      by_cases ruleMatches :
                                          matchRuleIds
                                            candidate.physical.profile
                                            candidate.physical.tables
                                            certificate argumentIds
                                            candidate.decodeFuel proof.rule
                                            premiseConcreteIds
                                            proof.resultTerm = true
                                      · rw [if_pos ruleMatches] at accepted
                                        obtain ⟨logicalNext, logicalStep,
                                            nextRelation, nextSound⟩ :=
                                          qualified_native_step_simulates
                                            connected termsMaterialized relation
                                            logicalSound
                                            opcodeMatches ruleResolves
                                            fingerprintMatches
                                            argumentCountMatches
                                            premiseCountMatches
                                            argumentSliceResolves
                                            premiseSliceResolves
                                            argumentsResolve premisesResolve
                                            conclusionResolves ruleMatches
                                        obtain ⟨finalLogical,
                                            tailMaterializes,
                                            finalRelation, finalSound⟩ :=
                                          inductionHypothesis nextRelation
                                            nextSound
                                            accepted
                                        exact ⟨finalLogical,
                                          logicalStep.trans tailMaterializes,
                                          finalRelation, finalSound⟩
                                      · rw [if_neg ruleMatches] at accepted
                                        contradiction
                · rw [if_neg premiseCountMatches] at accepted
                  contradiction
              · rw [if_neg argumentCountMatches] at accepted
                contradiction
            · rw [if_neg fingerprintMatches] at accepted
              contradiction
      · rw [if_neg opcodeMatches] at accepted
        contradiction

/-! ## End-to-end source-calculus soundness -/

/-- Successful complete native replay exposes all of the evidence needed by
the source-calculus simulation.  This lemma only eliminates the fail-closed
administrative guards of `nativeReplay?`; it adds no semantic assumption. -/
theorem nativeReplay?_success_evidence
    {profile : RuntimeProfile} {tables : RuleTables} {fuel : Nat}
    {certificate : Certificate} {terms : TermState}
    {finalNative : NativeProofState}
    (replayed :
      nativeReplay? profile tables fuel certificate =
        some (terms, finalNative)) :
    ∃ goal finalResultId,
      materializeTerms? profile certificate = some terms ∧
      terms.patterns[certificate.goalTerm.toNat]? = some goal ∧
      nativeReplayLoop profile tables certificate terms fuel
          certificate.proofs {} = some finalNative ∧
      finalNative.resultIds[finalNative.resultIds.size - 1]? =
        some finalResultId ∧
      finalResultId = certificate.goalTerm := by
  unfold nativeReplay? at replayed
  by_cases profileWidth : profile.profileDigest.length = digestWidth
  · rw [if_pos profileWidth] at replayed
    by_cases sourceWidth : profile.sourceDigest.length = digestWidth
    · rw [if_pos sourceWidth] at replayed
      by_cases profileMatches :
          certificate.profileDigest = profile.profileDigest
      · rw [if_pos profileMatches] at replayed
        by_cases sourceMatches :
            certificate.sourceDigest = profile.sourceDigest
        · rw [if_pos sourceMatches] at replayed
          cases termsEq : materializeTerms? profile certificate with
          | none => simp [termsEq] at replayed
          | some loadedTerms =>
              rw [termsEq] at replayed
              dsimp at replayed
              cases goalEq :
                  loadedTerms.patterns[certificate.goalTerm.toNat]? with
              | none => simp [goalEq] at replayed
              | some goal =>
                  rw [goalEq] at replayed
                  dsimp at replayed
                  cases nativeEq :
                      nativeReplayLoop profile tables certificate loadedTerms
                        fuel certificate.proofs {} with
                  | none => simp [nativeEq] at replayed
                  | some loadedNative =>
                      rw [nativeEq] at replayed
                      dsimp at replayed
                      cases finalResultEq :
                          loadedNative.resultIds[
                            loadedNative.resultIds.size - 1]? with
                      | none => simp [finalResultEq] at replayed
                      | some finalResultId =>
                          rw [finalResultEq] at replayed
                          dsimp at replayed
                          by_cases finalMatches :
                              finalResultId = certificate.goalTerm
                          · rw [if_pos finalMatches] at replayed
                            simp only [Option.some.injEq, Prod.mk.injEq]
                              at replayed
                            rcases replayed with ⟨rfl, rfl⟩
                            exact ⟨goal, finalResultId, rfl, goalEq, nativeEq,
                              finalResultEq, finalMatches⟩
                          · rw [if_neg finalMatches] at replayed
                            contradiction
        · rw [if_neg sourceMatches] at replayed
          contradiction
      · rw [if_neg profileMatches] at replayed
        contradiction
    · rw [if_neg sourceWidth] at replayed
      contradiction
  · rw [if_neg profileWidth] at replayed
    contradiction

/-- For a connected generated profile, acceptance by the raw native replay
model entails a typed derivation in the independently validated source
calculus.  The proof does not appeal to the ordinary logical checker as a
second oracle: it constructs derivation evidence while simulating every raw
identifier step. -/
theorem nativeCheckCertificate_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {certificate : Certificate}
    (accepted :
      nativeCheckCertificate candidate.physical.profile
          candidate.physical.tables candidate.decodeFuel submitted
          certificate = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  unfold nativeCheckCertificate at accepted
  cases replayed :
      nativeReplay? candidate.physical.profile candidate.physical.tables
        candidate.decodeFuel certificate with
  | none => simp [replayed] at accepted
  | some replayResult =>
      rcases replayResult with ⟨terms, finalNative⟩
      cases submittedGoalEq :
          terms.patterns[certificate.goalTerm.toNat]? with
      | none => simp [replayed, submittedGoalEq] at accepted
      | some submittedGoal =>
          simp only [replayed, submittedGoalEq, decide_eq_true_eq] at accepted
          obtain ⟨replayGoal, finalResultId, termsMaterialized,
              replayGoalEq, nativeAccepted, finalResultEq, finalIdEq⟩ :=
            nativeReplay?_success_evidence replayed
          obtain ⟨finalLogical, _logicalReplay, finalRelation,
              finalSound⟩ :=
            nativeReplayLoop_simulates_logical connected termsMaterialized
              (ReplayStateRelation.empty terms.patterns)
              (ProofStateSound.empty
                (candidate.validatedSource connected))
              nativeAccepted
          obtain ⟨finalPattern, logicalResultEq, termResultEq⟩ :=
            finalRelation.realizes finalResultEq
          have finalPatternEqReplayGoal : finalPattern = replayGoal := by
            rw [finalIdEq] at termResultEq
            exact Option.some.inj (termResultEq.symm.trans replayGoalEq)
          have replayGoalEqSubmittedGoal : replayGoal = submittedGoal :=
            Option.some.inj (replayGoalEq.symm.trans submittedGoalEq)
          have finalPatternEqSubmitted : finalPattern = submitted := by
            calc
              finalPattern = replayGoal := finalPatternEqReplayGoal
              _ = submittedGoal := replayGoalEqSubmittedGoal
              _ = submitted := accepted
          rw [← finalPatternEqSubmitted]
          exact finalSound logicalResultEq

/-- Exact M0GC wire decoding followed by connected native replay is sound for
the selected source calculus. -/
theorem nativeCheckBytes_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {bytes : List UInt8}
    (accepted :
      nativeCheckBytes candidate.physical.profile candidate.physical.tables
          candidate.decodeFuel submitted bytes = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  unfold nativeCheckBytes at accepted
  cases decoded : decodeCertificate? bytes with
  | none => simp [decoded] at accepted
  | some certificate =>
      exact nativeCheckCertificate_sound connected
        (by simpa [decoded] using accepted)

/-! ## Executable discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def tables : RuleTables :=
  Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy.Canary.ruleTables

def acceptedState : NativeProofState :=
  { resultIds := #[2] }

/-- The pair fixture has one application layer above its variable leaves, so
two matcher frames suffice.  Production uses `nativeMatcherFuel`; keeping the
fixture minimal avoids turning a semantic canary into a stress test of numeral
normalization. -/
def canaryFuel : Nat := 2

theorem pair_raw_replay_accepts :
    nativeReplayLoop profile tables certificate termState canaryFuel
      certificate.proofs {} = some acceptedState := by
  change nativeReplayLoop profile tables certificate termState canaryFuel
    [proofNode] {} = some acceptedState
  rw [nativeReplayLoop_cons_of
    (rule := pairRuleProfile) (argumentIds := [0, 1])
    (premiseReferences := []) (premiseConcreteIds := [])
    (argumentPatterns :=
      [M0GCLogicalReplayCanary.left, M0GCLogicalReplayCanary.right])
    (conclusion := M0GCLogicalReplayCanary.pair)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by
      simpa [tables, canaryFuel, proofNode] using
        M0GCIdentifierMatcherAdequacy.Canary.pair_rule_identifier_match)]
  rfl

theorem pair_native_replay_accepts :
    nativeReplay? profile tables canaryFuel certificate =
      some (termState, acceptedState) := by
  unfold nativeReplay?
  rw [if_pos (by simp [profile, profileDigest, digestWidth])]
  rw [if_pos (by simp [profile, sourceDigest, digestWidth])]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [terms_materialize]
  dsimp
  rw [pair_raw_replay_accepts]
  rfl

theorem pair_native_checker_accepts :
    nativeCheckCertificate profile tables canaryFuel
      M0GCLogicalReplayCanary.pair certificate = true := by
  unfold nativeCheckCertificate
  rw [pair_native_replay_accepts]
  rfl

theorem wrong_fingerprint_rejected :
    nativeCheckCertificate profile tables canaryFuel
      M0GCLogicalReplayCanary.pair wrongFingerprintCertificate = false := by
  unfold nativeCheckCertificate nativeReplay?
  rw [if_pos (by simp [profile, profileDigest, digestWidth])]
  rw [if_pos (by simp [profile, sourceDigest, digestWidth])]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [show materializeTerms? profile wrongFingerprintCertificate =
      some termState by exact terms_materialize]
  dsimp
  have rawReject :
      nativeReplayLoop profile tables wrongFingerprintCertificate termState
        canaryFuel wrongFingerprintCertificate.proofs {} = none := by
    change nativeReplayLoop profile tables wrongFingerprintCertificate termState
      canaryFuel
      [{ proofNode with ruleFingerprint := ruleFingerprint + 1 }] {} = none
    apply nativeReplayLoop_fingerprint_mismatch
      (rule := pairRuleProfile)
    · rfl
    · rfl
    · decide
  rw [rawReject]
  rfl

theorem forged_conclusion_rejected :
    nativeCheckCertificate profile tables canaryFuel
      M0GCLogicalReplayCanary.left forgedConclusionCertificate = false := by
  unfold nativeCheckCertificate nativeReplay?
  rw [if_pos (by simp [profile, profileDigest, digestWidth])]
  rw [if_pos (by simp [profile, sourceDigest, digestWidth])]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [show materializeTerms? profile forgedConclusionCertificate =
      some termState by exact terms_materialize]
  dsimp
  have rawReject :
      nativeReplayLoop profile tables forgedConclusionCertificate termState
        canaryFuel forgedConclusionCertificate.proofs {} = none := by
    change nativeReplayLoop profile tables forgedConclusionCertificate termState
      canaryFuel [forgedProofNode] {} = none
    apply nativeReplayLoop_rule_mismatch
      (rule := pairRuleProfile) (argumentIds := [0, 1])
      (premiseReferences := []) (premiseConcreteIds := [])
      (argumentPatterns :=
        [M0GCLogicalReplayCanary.left, M0GCLogicalReplayCanary.right])
      (conclusion := M0GCLogicalReplayCanary.left)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [tables, canaryFuel, forgedProofNode,
        forgedConclusionCertificate, proofNode, matchRuleIds, matchTemplateId,
        matchTemplateIds, profile, pairRuleProfile, certificate,
        leftNode, rightNode, pairNode, checkedSlice?, variableKind,
        applicationKind,
        M0GCIdentifierMatcherAdequacy.Canary.ruleTables,
        M0GCPhysicalTemplateAdequacy.pairRuleTables,
        M0GCPhysicalTemplateAdequacy.pairTables]
  rw [rawReject]
  rfl

theorem current_proof_reference_rejected :
    nativeReplayLoop futurePremiseProfile tables futurePremiseCertificate
      termState canaryFuel futurePremiseCertificate.proofs {} = none := by
  rfl

end Canary

#print axioms ReplayStateRelation.push
#print axioms qualified_native_step_simulates
#print axioms nativeReplayLoop_simulates_logical
#print axioms nativeReplay?_success_evidence
#print axioms nativeCheckCertificate_sound
#print axioms nativeCheckBytes_sound
#print axioms Canary.pair_raw_replay_accepts
#print axioms Canary.pair_native_checker_accepts
#print axioms Canary.wrong_fingerprint_rejected
#print axioms Canary.forged_conclusion_rejected
#print axioms Canary.current_proof_reference_rejected

end Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
