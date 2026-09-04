import Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy

/-!
# Proof-prefix abstract-machine refinement for the M0GC certificate checker

The current M0GC C replay loop does not allocate a result-identifier array.
For a premise reference `j < i`, it indexes the already loaded proof array at
`j` and reads that proof record's `result_term` field.  The source-level native
model instead retains an array containing only those result identifiers.

This module separates the two representations.  `cCoreReplayLoop` is a
source-level abstract machine carrying an explicit prefix of complete proof
records and resolving premises through that prefix, while `nativeReplayLoop`
carries only result identifiers.  A forward simulation proves the standard
no-extra-acceptance property: every successful proof-prefix replay is accepted
by the independently qualified native certificate-checker model and therefore
yields a typed source derivation.

Maturity boundary: this is a fully connected proof of concept for the
algorithmic core of the current C certificate checker.  It is an abstract-
machine refinement theorem, not a semantics of C source text, packed
structures, pointer arithmetic, allocation, a compiler, object code, an OS,
or hardware.  The retained proof prefix is a proof model, not an endgame
runtime allocation strategy.  Later source-derived C and machine-code stages
must discharge separate compiler-correctness or translation-validation
obligations rather than citing this module as if the C implementation itself
were verified.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification
open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy

/-! ## Proof-prefix abstract-machine state -/

/-- Proof records already visited by the proof-prefix abstract machine.  The
live C checker indexes the immutable full proof table; retaining its admitted
prefix here makes the same chronology explicit and structurally inductive. -/
structure CProofPrefixState where
  processed : Array ProofNode := #[]
deriving DecidableEq, Repr

/-- Resolve premise references by reading the conclusion field of an earlier
proof record, matching the data dependency of the C loop. -/
def resolveProofResults? (processed : Array ProofNode) :
    List UInt32 → Option (List UInt32)
  | [] => some []
  | reference :: references => do
      let proof ← processed[reference.toNat]?
      let results ← resolveProofResults? processed references
      some (proof.resultTerm :: results)

/-- The proof-prefix state and the allocation-free native state have the same
chronology, and each earlier proof exposes exactly the result identifier
stored at the corresponding native position. -/
structure PrefixResultRelation (cState : CProofPrefixState)
    (native : NativeProofState) : Prop where
  resultCount : cState.processed.size = native.resultIds.size
  realizes : ∀ {index : Nat} {proof : ProofNode},
    cState.processed[index]? = some proof →
      native.resultIds[index]? = some proof.resultTerm

theorem PrefixResultRelation.empty :
    PrefixResultRelation {} {} := by
  constructor <;> simp

/-- Extending both representations with one admitted proof preserves their
pointwise result correspondence. -/
theorem PrefixResultRelation.push
    {cState : CProofPrefixState} {native : NativeProofState}
    (relation : PrefixResultRelation cState native) (proof : ProofNode) :
    PrefixResultRelation
      { processed := cState.processed.push proof }
      { resultIds := native.resultIds.push proof.resultTerm } := by
  constructor
  · simp [relation.resultCount]
  · intro index queriedProof queriedProofEq
    by_cases inPrefix : index < cState.processed.size
    · have indexNe : index ≠ cState.processed.size := Nat.ne_of_lt inPrefix
      have oldProofEq : cState.processed[index]? = some queriedProof := by
        simpa [Array.getElem?_push, indexNe] using queriedProofEq
      have oldResultEq := relation.realizes oldProofEq
      have nativeIndexNe : index ≠ native.resultIds.size := by
        rw [← relation.resultCount]
        exact indexNe
      simpa [Array.getElem?_push, nativeIndexNe] using oldResultEq
    · have inExtended : index < cState.processed.size + 1 := by
        simpa using (Array.getElem?_eq_some_iff.mp queriedProofEq).choose
      have indexEq : index = cState.processed.size := by omega
      subst index
      have queriedEq : proof = queriedProof := by
        simpa using queriedProofEq
      subst queriedProof
      rw [relation.resultCount]
      simp

/-- Premise resolution through earlier C proof records agrees exactly with
resolution through the related native result-identifier array. -/
theorem resolveProofResults?_through_relation
    {cState : CProofPrefixState} {native : NativeProofState}
    (relation : PrefixResultRelation cState native)
    {references results : List UInt32}
    (resolved : resolveProofResults? cState.processed references = some results) :
    resolveIds? native.resultIds references = some results := by
  induction references generalizing results with
  | nil =>
      simp [resolveProofResults?] at resolved
      subst results
      rfl
  | cons reference references inductionHypothesis =>
      cases proofEq : cState.processed[reference.toNat]? with
      | none => simp [resolveProofResults?, proofEq] at resolved
      | some proof =>
          cases restEq :
              resolveProofResults? cState.processed references with
          | none => simp [resolveProofResults?, proofEq, restEq] at resolved
          | some rest =>
              simp [resolveProofResults?, proofEq, restEq] at resolved
              subst results
              have resultEq := relation.realizes proofEq
              simp [resolveIds?, resultEq, inductionHypothesis restEq]

/-! ## One-record replay and the proof-prefix loop -/

/-- Validate exactly one proof record against the already admitted prefix.

Unlike `nativeReplayLoop`, premise references are resolved by indexing prior
complete proof records and reading their declared result fields.  This
operation has no storage effect; the separate `cCoreReplayRecord?` operation
performs the unique append after validation succeeds. -/
def cCoreValidateRecord? (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (state : CProofPrefixState) (proof : ProofNode) :
    Option Unit := do
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
  let premiseConcreteIds ←
    resolveProofResults? state.processed premiseReferences
  let _conclusion ← terms.patterns[proof.resultTerm.toNat]?
  if matchRuleIds profile tables certificate argumentIds fuel proof.rule
      premiseConcreteIds proof.resultTerm then
    some ()
  else none
  else none
  else none
  else none
  else none

/-- Check one proof record and perform its only storage effect: append the
validated record to the admitted prefix.  This separation makes the effect
boundary directly reusable by chronological and bounded-store machines. -/
def cCoreReplayRecord? (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (state : CProofPrefixState) (proof : ProofNode) :
    Option CProofPrefixState := do
  let _ ←
    cCoreValidateRecord? profile tables certificate terms fuel state proof
  some { processed := state.processed.push proof }

/-- Every successful one-record check has exactly one possible storage effect:
the checked record is appended to the admitted prefix. -/
theorem cCoreReplayRecord?_success_processed
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {state next : CProofPrefixState} {proof : ProofNode}
    (accepted :
      cCoreReplayRecord? profile tables certificate terms fuel state proof =
        some next) :
    next.processed = state.processed.push proof := by
  unfold cCoreReplayRecord? at accepted
  rcases Option.bind_eq_some_iff.mp accepted with
    ⟨_, _validated, resultEq⟩
  simp at resultEq
  subst next
  rfl

/-- Recursive source-level control model of the proof replay core.  It is the
chronological iteration of `cCoreReplayRecord?` over the certificate's proof
records. -/
def cCoreReplayLoop (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat) :
    List ProofNode → CProofPrefixState → Option CProofPrefixState
  | [], state => some state
  | proof :: proofs, state => do
      let next ←
        cCoreReplayRecord? profile tables certificate terms fuel state proof
      cCoreReplayLoop profile tables certificate terms fuel proofs next

/-- A record satisfying every physical and logical guard extends the admitted
prefix by exactly that record. -/
theorem cCoreReplayRecord?_of
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proof : ProofNode} {state : CProofPrefixState} {rule : RuleProfile}
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
      resolveProofResults? state.processed premiseReferences =
        some premiseConcreteIds)
    (conclusionResolves :
      terms.patterns[proof.resultTerm.toNat]? = some conclusion)
    (ruleMatches :
      matchRuleIds profile tables certificate argumentIds fuel proof.rule
        premiseConcreteIds proof.resultTerm = true) :
    cCoreReplayRecord? profile tables certificate terms fuel state proof =
      some { processed := state.processed.push proof } := by
  unfold cCoreReplayRecord?
  unfold cCoreValidateRecord?
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
  rfl

/-- One fully admitted proof-prefix record advances the recursive replay loop
to its chronological tail. -/
theorem cCoreReplayLoop_cons_of
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proof : ProofNode} {proofs : List ProofNode}
    {state : CProofPrefixState} {rule : RuleProfile}
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
      resolveProofResults? state.processed premiseReferences =
        some premiseConcreteIds)
    (conclusionResolves :
      terms.patterns[proof.resultTerm.toNat]? = some conclusion)
    (ruleMatches :
      matchRuleIds profile tables certificate argumentIds fuel proof.rule
        premiseConcreteIds proof.resultTerm = true) :
    cCoreReplayLoop profile tables certificate terms fuel
        (proof :: proofs) state =
      cCoreReplayLoop profile tables certificate terms fuel proofs
        { processed := state.processed.push proof } := by
  rw [cCoreReplayLoop]
  rw [cCoreReplayRecord?_of opcodeMatches ruleResolves fingerprintMatches
    argumentCountMatches premiseCountMatches argumentSliceResolves
    premiseSliceResolves argumentsResolve premisesResolve conclusionResolves
    ruleMatches]
  rfl

/-- Forward simulation and no-extra-acceptance theorem for the proof-prefix
abstract machine.
Every successful complete-proof-prefix replay is also a successful replay by
the independently qualified result-identifier model. -/
theorem cCoreReplayLoop_simulates_native
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proofs : List ProofNode}
    {cState finalCState : CProofPrefixState}
    {native : NativeProofState}
    (relation : PrefixResultRelation cState native)
    (accepted :
      cCoreReplayLoop profile tables certificate terms fuel proofs cState =
        some finalCState) :
    ∃ finalNative,
      nativeReplayLoop profile tables certificate terms fuel proofs native =
          some finalNative ∧
      PrefixResultRelation finalCState finalNative := by
  induction proofs generalizing cState native finalCState with
  | nil =>
      simp [cCoreReplayLoop] at accepted
      subst finalCState
      exact ⟨native, rfl, relation⟩
  | cons proof proofs inductionHypothesis =>
      rw [cCoreReplayLoop] at accepted
      unfold cCoreReplayRecord? at accepted
      unfold cCoreValidateRecord? at accepted
      by_cases opcodeMatches : proof.opcode = applyOpcode
      · rw [if_pos opcodeMatches] at accepted
        cases ruleResolves : profile.rules[proof.rule.toNat]? with
        | none => simp [ruleResolves] at accepted
        | some rule =>
            rw [ruleResolves] at accepted
            dsimp at accepted
            by_cases fingerprintMatches :
                proof.ruleFingerprint = rule.fingerprint
            · rw [if_pos fingerprintMatches] at accepted
              by_cases argumentCountMatches :
                  proof.argumentCount = rule.argumentCount
              · rw [if_pos argumentCountMatches] at accepted
                by_cases premiseCountMatches :
                    proof.premiseCount = rule.premiseCount
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
                                  resolveProofResults? cState.processed
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
                                          matchRuleIds profile tables
                                            certificate argumentIds fuel
                                            proof.rule premiseConcreteIds
                                            proof.resultTerm = true
                                      · rw [if_pos ruleMatches] at accepted
                                        have nativePremisesResolve :=
                                          resolveProofResults?_through_relation
                                            relation premisesResolve
                                        let nextRelation :=
                                          relation.push proof
                                        obtain ⟨finalNative, nativeTail,
                                            finalRelation⟩ :=
                                          inductionHypothesis nextRelation
                                            accepted
                                        refine ⟨finalNative, ?_,
                                          finalRelation⟩
                                        rw [nativeReplayLoop_cons_of
                                          (rule := rule)
                                          (argumentIds := argumentIds)
                                          (premiseReferences :=
                                            premiseReferences)
                                          (premiseConcreteIds :=
                                            premiseConcreteIds)
                                          (argumentPatterns := argumentPatterns)
                                          (conclusion := conclusion)
                                          opcodeMatches ruleResolves
                                          fingerprintMatches
                                          argumentCountMatches
                                          premiseCountMatches
                                          argumentSliceResolves
                                          premiseSliceResolves
                                          argumentsResolve
                                          nativePremisesResolve
                                          conclusionResolves ruleMatches]
                                        exact nativeTail
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

/-- Rejection form of the loop refinement: whenever the qualified native
model rejects a related state, the proof-prefix abstract machine rejects too.
This is useful for negative discriminators because it rules out hidden extra
behavior rather than merely comparing selected successful examples. -/
theorem cCoreReplayLoop_rejected_of_native_rejected
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proofs : List ProofNode} {cState : CProofPrefixState}
    {native : NativeProofState}
    (relation : PrefixResultRelation cState native)
    (nativeRejected :
      nativeReplayLoop profile tables certificate terms fuel proofs native =
        none) :
    cCoreReplayLoop profile tables certificate terms fuel proofs cState =
      none := by
  cases coreEq :
      cCoreReplayLoop profile tables certificate terms fuel proofs cState with
  | none => rfl
  | some finalCState =>
      exfalso
      obtain ⟨finalNative, nativeAccepted, _finalRelation⟩ :=
        cCoreReplayLoop_simulates_native relation coreEq
      rw [nativeRejected] at nativeAccepted
      contradiction

/-! ## Complete certificate-checker refinement -/

/-- Administrative preparation shared by complete recursive and small-step
checkers.  It validates digest widths and identities, materializes every term,
and requires the declared goal term to exist. -/
def cCorePrepare? (profile : RuntimeProfile) (certificate : Certificate) :
    Option TermState := do
  if profile.profileDigest.length = digestWidth then
  if profile.sourceDigest.length = digestWidth then
  if certificate.profileDigest = profile.profileDigest then
  if certificate.sourceDigest = profile.sourceDigest then
  let terms ← materializeTerms? profile certificate
  let _goal ← terms.patterns[certificate.goalTerm.toNat]?
  some terms
  else none
  else none
  else none
  else none

/-- Final-proof pinning shared by complete recursive and small-step checkers. -/
def cCoreFinalizeReplay? (certificate : Certificate) (terms : TermState)
    (proofs : CProofPrefixState) : Option (TermState × CProofPrefixState) := do
  let finalProof ← proofs.processed[proofs.processed.size - 1]?
  if finalProof.resultTerm = certificate.goalTerm then
    some (terms, proofs)
  else none

/-- Final Boolean observation after proof replay.  It retains both the
last-proof pinning check and equality with the submitted claim. -/
def cCoreObserveFinal (submitted : Pattern) (certificate : Certificate)
    (terms : TermState) (proofs : CProofPrefixState) : Bool :=
  match cCoreFinalizeReplay? certificate terms proofs with
  | none => false
  | some (finalTerms, _) =>
      match finalTerms.patterns[certificate.goalTerm.toNat]? with
      | none => false
      | some goal => decide (goal = submitted)

/-- Complete replay by the proof-prefix abstract machine.  The administrative
guards and pinned-goal check intentionally match `nativeReplay?`; the only
representation difference is how earlier proof results are retained. -/
def cCoreReplay? (profile : RuntimeProfile) (tables : RuleTables)
    (fuel : Nat) (certificate : Certificate) :
    Option (TermState × CProofPrefixState) := do
  let terms ← cCorePrepare? profile certificate
  let proofs ← cCoreReplayLoop profile tables certificate terms fuel
    certificate.proofs {}
  cCoreFinalizeReplay? certificate terms proofs

/-- Decoded-certificate observation for the proof-prefix abstract machine. -/
def cCoreCheckCertificate (profile : RuntimeProfile) (tables : RuleTables)
    (fuel : Nat) (submitted : Pattern) (certificate : Certificate) : Bool :=
  match cCoreReplay? profile tables fuel certificate with
  | none => false
  | some (terms, _) =>
      match terms.patterns[certificate.goalTerm.toNat]? with
      | none => false
      | some goal => decide (goal = submitted)

/-- The complete checker is exactly preparation, chronological replay, and
final observation.  Later control machines use this theorem rather than
copying administrative guards. -/
theorem cCoreCheckCertificate_eq_pipeline
    (profile : RuntimeProfile) (tables : RuleTables) (fuel : Nat)
    (submitted : Pattern) (certificate : Certificate) :
    cCoreCheckCertificate profile tables fuel submitted certificate =
      match cCorePrepare? profile certificate with
      | none => false
      | some terms =>
          match cCoreReplayLoop profile tables certificate terms fuel
              certificate.proofs {} with
          | none => false
          | some proofs =>
              cCoreObserveFinal submitted certificate terms proofs := by
  unfold cCoreCheckCertificate cCoreReplay? cCoreObserveFinal
  simp only [Option.bind_eq_bind]
  cases prepareEq : cCorePrepare? profile certificate with
  | none => simp
  | some terms =>
      cases loopEq :
          cCoreReplayLoop profile tables certificate terms fuel
            certificate.proofs {} with
      | none => simp [loopEq]
      | some proofs => simp [loopEq]

/-- Exact M0GC wire decoding followed by proof-prefix replay. -/
def cCoreCheckBytes (profile : RuntimeProfile) (tables : RuleTables)
    (fuel : Nat) (submitted : Pattern) (bytes : List UInt8) : Bool :=
  match decodeCertificate? bytes with
  | none => false
  | some certificate =>
      cCoreCheckCertificate profile tables fuel submitted certificate

/-- Complete-replay refinement.  Successful proof-prefix replay produces a
successful run of the independently qualified native certificate-verifier
model, with the final states related pointwise. -/
theorem cCoreReplay?_simulates_native
    {profile : RuntimeProfile} {tables : RuleTables} {fuel : Nat}
    {certificate : Certificate} {terms : TermState}
    {finalCState : CProofPrefixState}
    (replayed :
      cCoreReplay? profile tables fuel certificate =
        some (terms, finalCState)) :
    ∃ finalNative,
      nativeReplay? profile tables fuel certificate =
          some (terms, finalNative) ∧
      PrefixResultRelation finalCState finalNative := by
  unfold cCoreReplay? cCorePrepare? cCoreFinalizeReplay? at replayed
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
                  cases cLoopEq :
                      cCoreReplayLoop profile tables certificate loadedTerms
                        fuel certificate.proofs {} with
                  | none => simp [cLoopEq] at replayed
                  | some loadedCState =>
                      rw [cLoopEq] at replayed
                      dsimp at replayed
                      cases finalProofEq :
                          loadedCState.processed[
                            loadedCState.processed.size - 1]? with
                      | none => simp [finalProofEq] at replayed
                      | some finalProof =>
                          rw [finalProofEq] at replayed
                          dsimp at replayed
                          by_cases finalMatches :
                              finalProof.resultTerm = certificate.goalTerm
                          · rw [if_pos finalMatches] at replayed
                            simp only [Option.some.injEq, Prod.mk.injEq]
                              at replayed
                            rcases replayed with ⟨rfl, rfl⟩
                            obtain ⟨finalNative, nativeLoopEq,
                                finalRelation⟩ :=
                              cCoreReplayLoop_simulates_native
                                PrefixResultRelation.empty cLoopEq
                            have nativeFinalEq :
                                finalNative.resultIds[
                                  finalNative.resultIds.size - 1]? =
                                  some finalProof.resultTerm := by
                              have relatedFinal :=
                                finalRelation.realizes finalProofEq
                              simpa only [finalRelation.resultCount] using
                                relatedFinal
                            refine ⟨finalNative, ?_, finalRelation⟩
                            unfold nativeReplay?
                            rw [if_pos profileWidth]
                            rw [if_pos sourceWidth]
                            rw [if_pos profileMatches]
                            rw [if_pos sourceMatches]
                            rw [termsEq]
                            dsimp
                            rw [goalEq]
                            dsimp
                            rw [nativeLoopEq]
                            dsimp
                            rw [nativeFinalEq]
                            dsimp
                            rw [if_pos finalMatches]
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

/-- Rejection form of complete-replay refinement. -/
theorem cCoreReplay?_rejected_of_native_rejected
    {profile : RuntimeProfile} {tables : RuleTables} {fuel : Nat}
    {certificate : Certificate}
    (nativeRejected : nativeReplay? profile tables fuel certificate = none) :
    cCoreReplay? profile tables fuel certificate = none := by
  cases coreEq : cCoreReplay? profile tables fuel certificate with
  | none => rfl
  | some replayResult =>
      exfalso
      rcases replayResult with ⟨terms, finalCState⟩
      obtain ⟨finalNative, nativeAccepted, _finalRelation⟩ :=
        cCoreReplay?_simulates_native coreEq
      rw [nativeRejected] at nativeAccepted
      contradiction

/-- A connected generated profile makes proof-prefix certificate acceptance
sound for the independently validated source calculus.  This composes the
abstract-machine refinement with native replay soundness; it does not assume
that the current C source or compiler realizes the abstract machine. -/
theorem cCoreCheckCertificate_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {certificate : Certificate}
    (accepted :
      cCoreCheckCertificate candidate.physical.profile
          candidate.physical.tables candidate.decodeFuel submitted
          certificate = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  unfold cCoreCheckCertificate at accepted
  cases replayed :
      cCoreReplay? candidate.physical.profile candidate.physical.tables
        candidate.decodeFuel certificate with
  | none => simp [replayed] at accepted
  | some replayResult =>
      rcases replayResult with ⟨terms, finalCState⟩
      cases goalEq : terms.patterns[certificate.goalTerm.toNat]? with
      | none => simp [replayed, goalEq] at accepted
      | some goal =>
          simp only [replayed, goalEq, decide_eq_true_eq] at accepted
          obtain ⟨finalNative, nativeReplayed, _finalRelation⟩ :=
            cCoreReplay?_simulates_native replayed
          apply nativeCheckCertificate_sound connected
          unfold nativeCheckCertificate
          rw [nativeReplayed]
          change
            (match terms.patterns[certificate.goalTerm.toNat]? with
              | none => false
              | some checkedGoal => decide (checkedGoal = submitted)) = true
          rw [goalEq]
          exact decide_eq_true accepted

/-- Exact M0GC wire decoding followed by connected proof-prefix replay is
sound for the selected source calculus. -/
theorem cCoreCheckBytes_sound
    {candidate : Candidate} (connected : candidate.Connected)
    {submitted : Pattern} {bytes : List UInt8}
    (accepted :
      cCoreCheckBytes candidate.physical.profile candidate.physical.tables
          candidate.decodeFuel submitted bytes = true) :
    Nonempty (Derivation (candidate.validatedSource connected) submitted) := by
  unfold cCoreCheckBytes at accepted
  cases decoded : decodeCertificate? bytes with
  | none => simp [decoded] at accepted
  | some certificate =>
      exact cCoreCheckCertificate_sound connected
        (by simpa [decoded] using accepted)

/-! ## Executable discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def tables : RuleTables :=
  Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy.Canary.tables

def canaryFuel : Nat :=
  Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy.Canary.canaryFuel

def acceptedState : CProofPrefixState :=
  { processed := #[proofNode] }

/-- Positive discriminator: the proof-prefix abstract machine accepts the
same nontrivial pair-constructor rule instance as the native model. -/
theorem pair_core_loop_accepts :
    cCoreReplayLoop profile tables certificate termState canaryFuel
      certificate.proofs {} = some acceptedState := by
  change cCoreReplayLoop profile tables certificate termState canaryFuel
    [proofNode] {} = some acceptedState
  rw [cCoreReplayLoop_cons_of
    (rule := pairRuleProfile) (argumentIds := [0, 1])
    (premiseReferences := []) (premiseConcreteIds := [])
    (argumentPatterns :=
      [M0GCLogicalReplayCanary.left, M0GCLogicalReplayCanary.right])
    (conclusion := M0GCLogicalReplayCanary.pair)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by
      simpa [tables, canaryFuel,
          M0GCNativeReplayAdequacy.Canary.tables,
          M0GCNativeReplayAdequacy.Canary.canaryFuel, proofNode] using
        M0GCIdentifierMatcherAdequacy.Canary.pair_rule_identifier_match)]
  rfl

theorem pair_core_replay_accepts :
    cCoreReplay? profile tables canaryFuel certificate =
      some (termState, acceptedState) := by
  unfold cCoreReplay? cCorePrepare? cCoreFinalizeReplay?
  rw [if_pos (by simp [profile, profileDigest, digestWidth])]
  rw [if_pos (by simp [profile, sourceDigest, digestWidth])]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [terms_materialize]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show termState.patterns[certificate.goalTerm.toNat]? =
      some M0GCLogicalReplayCanary.pair by rfl]
  dsimp
  rw [pair_core_loop_accepts]
  rfl

theorem pair_core_checker_accepts :
    cCoreCheckCertificate profile tables canaryFuel
      M0GCLogicalReplayCanary.pair certificate = true := by
  unfold cCoreCheckCertificate
  rw [pair_core_replay_accepts]
  rfl

/-- Negative discriminator: a proof cannot cite its own not-yet-admitted
result.  The proof-prefix representation rejects the reference directly. -/
theorem current_proof_reference_rejected :
    cCoreReplayLoop futurePremiseProfile tables futurePremiseCertificate
      termState canaryFuel futurePremiseCertificate.proofs {} = none := by
  rfl

end Canary

#print axioms PrefixResultRelation.push
#print axioms resolveProofResults?_through_relation
#print axioms cCoreReplayRecord?_success_processed
#print axioms cCoreReplayRecord?_of
#print axioms cCoreReplayLoop_simulates_native
#print axioms cCoreReplayLoop_rejected_of_native_rejected
#print axioms cCoreCheckCertificate_eq_pipeline
#print axioms cCoreReplay?_simulates_native
#print axioms cCoreReplay?_rejected_of_native_rejected
#print axioms cCoreCheckCertificate_sound
#print axioms cCoreCheckBytes_sound
#print axioms Canary.pair_core_loop_accepts
#print axioms Canary.pair_core_checker_accepts
#print axioms Canary.current_proof_reference_rejected

end Mettapedia.GSLT.LanguageDef.M0GCCoreLoopCorrespondence
