import Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement

/-!
# Addressed chronological replay for the M0GC checker

This module runs M0GC proof-record validation against the fixed-capacity,
64-bit-addressed result store.  Premise references read only the initialized
prefix; successful records write one 32-bit result identifier without growing
the allocation.  The one-record transition and the complete chronological
loop are proved observationally identical to the independently qualified
source-level native replay model whenever the allocation is sufficient.

Maturity boundary: this is a fully connected intermediate proof of concept.
It is an abstract machine over typed cells, not a byte-packed target ABI,
pointer-provenance semantics, Pancake, Clight, generated C, compiler proof,
object code, an OS, or hardware.  The record-validation table layout and
recursive identifier matcher are also not claimed to be endgame optimized.
Their semantic obligations are explicit so later representations can replace
them without becoming new authorities.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCAddressedReplayControlMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCIdentifierMatcherAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement.ResultStore

/-! ## Addressed premise lookup -/

/-- Resolve chronological premise references through checked physical reads. -/
def resolveAdmitted? (store : ResultStore) :
    List UInt32 → Option (List UInt32)
  | [] => some []
  | reference :: references => do
      let resultId ← store.readAdmitted? reference.toNat
      let results ← resolveAdmitted? store references
      some (resultId :: results)

/-- Addressed premise reads agree exactly with lookup in the initialized
source-level result prefix. -/
theorem resolveAdmitted?_eq_resolveIds (store : ResultStore)
    (wellFormed : store.WellFormed) (references : List UInt32) :
    resolveAdmitted? store references =
      resolveIds? store.snapshot references := by
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      simp [resolveAdmitted?, resolveIds?,
        store.readAdmitted?_eq_snapshot reference.toNat wellFormed,
        inductionHypothesis]

/-! ## Shared record validation -/

/-- Validate one record against an explicitly supplied chronological premise
resolver, returning exactly the admitted result identifier.

This factors the checks common to the allocation-free source model and the
addressed machine.  It does not define meaning: source soundness remains the
separate generated-profile qualification theorem. -/
def recordResult? (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (resolvePremises : List UInt32 → Option (List UInt32))
    (proof : ProofNode) : Option UInt32 := do
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
  let premiseConcreteIds ← resolvePremises premiseReferences
  let _conclusion ← terms.patterns[proof.resultTerm.toNat]?
  if matchRuleIds profile tables certificate argumentIds fuel proof.rule
      premiseConcreteIds proof.resultTerm then
    some proof.resultTerm
  else none
  else none
  else none
  else none
  else none

/-- One addressed replay transition: validate, then write the admitted result
into the next preallocated cell. -/
def replayRecord? (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (store : ResultStore) (proof : ProofNode) : Option ResultStore := do
  let resultId ← recordResult? profile tables certificate terms fuel
    (resolveAdmitted? store) proof
  store.writeNext? resultId

/-- A successful addressed record transition preserves the reachable-store
invariant. -/
theorem replayRecord?_wellFormed
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {store next : ResultStore} {proof : ProofNode}
    (wellFormed : store.WellFormed)
    (accepted :
      replayRecord? profile tables certificate terms fuel store proof =
        some next) :
    next.WellFormed := by
  unfold replayRecord? at accepted
  rcases Option.bind_eq_some_iff.mp accepted with
    ⟨resultId, _validated, writeAccepted⟩
  exact writeNext?_wellFormed wellFormed writeAccepted

/-- Source-level one-record replay expressed through the same factored record
validator. -/
def nativeReplayRecord? (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (state : NativeProofState) (proof : ProofNode) : Option NativeProofState := do
  let resultId ← recordResult? profile tables certificate terms fuel
    (resolveIds? state.resultIds) proof
  some { resultIds := state.resultIds.push resultId }

/-- Factoring record validation changes no behavior of the pre-existing native
replay loop.  The explicit cases are the executable rejection boundary: every
failed lookup or guard returns before the continuation is invoked. -/
theorem nativeReplayRecord?_eq_loop
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (state : NativeProofState) (proof : ProofNode) :
    nativeReplayRecord? profile tables certificate terms fuel state proof =
      nativeReplayLoop profile tables certificate terms fuel [proof] state := by
  unfold nativeReplayRecord? recordResult? nativeReplayLoop
  by_cases opcode : proof.opcode = applyOpcode
  · rw [if_pos opcode, if_pos opcode]
    cases ruleResult : profile.rules[proof.rule.toNat]? with
    | none => rfl
    | some rule =>
      dsimp
      by_cases fingerprint : proof.ruleFingerprint = rule.fingerprint
      · rw [if_pos fingerprint, if_pos fingerprint]
        by_cases arguments : proof.argumentCount = rule.argumentCount
        · rw [if_pos arguments, if_pos arguments]
          by_cases premises : proof.premiseCount = rule.premiseCount
          · rw [if_pos premises, if_pos premises]
            cases argumentSlice : checkedSlice? certificate.arguments
                proof.argumentStart.toNat proof.argumentCount.toNat with
            | none => rfl
            | some argumentIds =>
              dsimp
              cases premiseSlice : checkedSlice? certificate.premises
                  proof.premiseStart.toNat proof.premiseCount.toNat with
              | none => rfl
              | some premiseReferences =>
                dsimp
                cases argumentResolution :
                    resolveIds? terms.patterns argumentIds with
                | none => rfl
                | some argumentPatterns =>
                  dsimp
                  cases premiseResolution :
                      resolveIds? state.resultIds premiseReferences with
                  | none => rfl
                  | some premiseConcreteIds =>
                    dsimp
                    cases conclusionResolution :
                        terms.patterns[proof.resultTerm.toNat]? with
                    | none => rfl
                    | some conclusion =>
                      dsimp
                      by_cases ruleMatches :
                          matchRuleIds profile tables certificate argumentIds
                              fuel proof.rule premiseConcreteIds
                                proof.resultTerm = true
                      · rw [if_pos ruleMatches, if_pos ruleMatches]
                        rfl
                      · rw [if_neg ruleMatches, if_neg ruleMatches]
                        rfl
          · rw [if_neg premises, if_neg premises]
            rfl
        · rw [if_neg arguments, if_neg arguments]
          rfl
      · rw [if_neg fingerprint, if_neg fingerprint]
        rfl
  · rw [if_neg opcode, if_neg opcode]
    rfl

/-- With one free cell, an addressed record transition has exactly the native
source-level observation. -/
theorem replayRecord?_refines_native
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (store : ResultStore) (proof : ProofNode)
    (wellFormed : store.WellFormed)
    (room : store.used < store.cells.size) :
    Option.map ResultStore.toNative
        (replayRecord? profile tables certificate terms fuel store proof) =
      nativeReplayLoop profile tables certificate terms fuel [proof]
        store.toNative := by
  have resolveEq :
      resolveAdmitted? store = resolveIds? store.snapshot := by
    funext references
    exact resolveAdmitted?_eq_resolveIds store wellFormed references
  rw [← nativeReplayRecord?_eq_loop]
  unfold replayRecord? nativeReplayRecord?
  rw [resolveEq]
  simp only [ResultStore.toNative]
  cases validation :
      recordResult? profile tables certificate terms fuel
        (resolveIds? store.snapshot) proof with
  | none => rfl
  | some resultId =>
      dsimp
      exact map_toNative_writeNext_of_room store resultId wellFormed room

/-! ## Complete chronological loop -/

/-- Replay a chronological proof list through the addressed result store. -/
def replayLoop (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat) :
    List ProofNode → ResultStore → Option ResultStore
  | [], store => some store
  | proof :: proofs, store => do
      let next ← replayRecord? profile tables certificate terms fuel
        store proof
      replayLoop profile tables certificate terms fuel proofs next

/-- Every successful complete addressed replay preserves the reachable-store
invariant. -/
theorem replayLoop_wellFormed
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proofs : List ProofNode} {store final : ResultStore}
    (wellFormed : store.WellFormed)
    (accepted :
      replayLoop profile tables certificate terms fuel proofs store =
        some final) :
    final.WellFormed := by
  induction proofs generalizing store with
  | nil =>
      simp only [replayLoop, Option.some.injEq] at accepted
      subst final
      exact wellFormed
  | cons proof proofs inductionHypothesis =>
      simp only [replayLoop] at accepted
      rcases Option.bind_eq_some_iff.mp accepted with
        ⟨next, recordAccepted, tailAccepted⟩
      exact inductionHypothesis
        (replayRecord?_wellFormed wellFormed recordAccepted) tailAccepted

/-- Native replay of a nonempty list factors through the shared one-record
validator and then continues from the extended result prefix. -/
theorem nativeReplayLoop_cons_eq_recordResult
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (proof : ProofNode) (proofs : List ProofNode)
    (state : NativeProofState) :
    (do
      let resultId ← recordResult? profile tables certificate terms fuel
        (resolveIds? state.resultIds) proof
      nativeReplayLoop profile tables certificate terms fuel proofs
        { resultIds := state.resultIds.push resultId }) =
      nativeReplayLoop profile tables certificate terms fuel
        (proof :: proofs) state := by
  unfold recordResult?
  conv_rhs => rw [nativeReplayLoop]
  by_cases opcode : proof.opcode = applyOpcode
  · rw [if_pos opcode, if_pos opcode]
    cases ruleResult : profile.rules[proof.rule.toNat]? with
    | none => rfl
    | some rule =>
      dsimp
      by_cases fingerprint : proof.ruleFingerprint = rule.fingerprint
      · rw [if_pos fingerprint, if_pos fingerprint]
        by_cases arguments : proof.argumentCount = rule.argumentCount
        · rw [if_pos arguments, if_pos arguments]
          by_cases premises : proof.premiseCount = rule.premiseCount
          · rw [if_pos premises, if_pos premises]
            cases argumentSlice : checkedSlice? certificate.arguments
                proof.argumentStart.toNat proof.argumentCount.toNat with
            | none => rfl
            | some argumentIds =>
              dsimp
              cases premiseSlice : checkedSlice? certificate.premises
                  proof.premiseStart.toNat proof.premiseCount.toNat with
              | none => rfl
              | some premiseReferences =>
                dsimp
                cases argumentResolution :
                    resolveIds? terms.patterns argumentIds with
                | none => rfl
                | some argumentPatterns =>
                  dsimp
                  cases premiseResolution :
                      resolveIds? state.resultIds premiseReferences with
                  | none => rfl
                  | some premiseConcreteIds =>
                    dsimp
                    cases conclusionResolution :
                        terms.patterns[proof.resultTerm.toNat]? with
                    | none => rfl
                    | some conclusion =>
                      dsimp
                      by_cases ruleMatches :
                          matchRuleIds profile tables certificate argumentIds
                              fuel proof.rule premiseConcreteIds
                                proof.resultTerm = true
                      · rw [if_pos ruleMatches, if_pos ruleMatches]
                        rfl
                      · rw [if_neg ruleMatches, if_neg ruleMatches]
                        rfl
          · rw [if_neg premises, if_neg premises]
            rfl
        · rw [if_neg arguments, if_neg arguments]
          rfl
      · rw [if_neg fingerprint, if_neg fingerprint]
        rfl
  · rw [if_neg opcode, if_neg opcode]
    rfl

/-- Sufficient fixed allocation makes complete addressed replay exactly equal
to the qualified allocation-free native replay. -/
theorem replayLoop_refines_native_of_capacity
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (proofs : List ProofNode) (store : ResultStore)
    (wellFormed : store.WellFormed)
    (enough : store.used + proofs.length ≤ store.cells.size) :
    Option.map ResultStore.toNative
        (replayLoop profile tables certificate terms fuel proofs store) =
      nativeReplayLoop profile tables certificate terms fuel proofs
        store.toNative := by
  induction proofs generalizing store with
  | nil => rfl
  | cons proof proofs inductionHypothesis =>
      have room : store.used < store.cells.size := by
        simp only [List.length_cons] at enough
        omega
      have resolveEq :
          resolveAdmitted? store = resolveIds? store.snapshot := by
        funext references
        exact resolveAdmitted?_eq_resolveIds store wellFormed references
      rw [← nativeReplayLoop_cons_eq_recordResult]
      simp only [replayLoop, replayRecord?]
      rw [resolveEq]
      simp only [ResultStore.toNative]
      cases validation :
          recordResult? profile tables certificate terms fuel
            (resolveIds? store.snapshot) proof with
      | none => rfl
      | some resultId =>
          dsimp
          obtain ⟨next, writeAccepted⟩ :=
            writeNext?_exists_of_room store resultId wellFormed room
          rw [writeAccepted]
          dsimp
          have nextWellFormed :=
            writeNext?_wellFormed wellFormed writeAccepted
          have nextUsed := writeNext?_used writeAccepted
          have sameCapacity := writeNext?_capacity writeAccepted
          have enoughTail : next.used + proofs.length ≤ next.cells.size := by
            rw [nextUsed, sameCapacity]
            simp only [List.length_cons] at enough
            omega
          have nativeNext := writeNext?_toNative writeAccepted
          have nativeNext' :
              next.toNative =
                { resultIds := store.snapshot.push resultId } := by
            simpa [ResultStore.toNative] using nativeNext
          rw [← nativeNext']
          exact inductionHypothesis next nextWellFormed enoughTail

/-! ## Executable discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def tables : RuleTables :=
  Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy.Canary.tables

def emptyOneSlot : ResultStore :=
  { base := 100, cells := #[0], used := 0 }

def acceptedOneSlot : ResultStore :=
  { base := 100, cells := #[2], used := 1 }

def zeroSlot : ResultStore :=
  { base := 100, cells := #[], used := 0 }

/-- The pair record's semantic checks are independent of the result-store
capacity because it has no premises. -/
theorem pair_record_validation (store : ResultStore) :
    recordResult? profile tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel
        (resolveAdmitted? store) proofNode = some proofNode.resultTerm := by
  unfold recordResult?
  rw [if_pos (by rfl)]
  rw [show profile.rules[proofNode.rule.toNat]? = some pairRuleProfile by rfl]
  dsimp
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [if_pos (by rfl)]
  rw [show checkedSlice? certificate.arguments proofNode.argumentStart.toNat
      proofNode.argumentCount.toNat = some [0, 1] by rfl]
  dsimp
  rw [show checkedSlice? certificate.premises proofNode.premiseStart.toNat
      proofNode.premiseCount.toNat = some [] by rfl]
  dsimp
  rw [show resolveIds? termState.patterns [0, 1] =
      some [M0GCLogicalReplayCanary.left,
        M0GCLogicalReplayCanary.right] by rfl]
  dsimp
  rw [show resolveAdmitted? store [] = some [] by rfl]
  dsimp
  rw [show termState.patterns[proofNode.resultTerm.toNat]? =
      some M0GCLogicalReplayCanary.pair by rfl]
  dsimp
  rw [if_pos (by
    simpa [tables, M0GCNativeReplayAdequacy.Canary.tables,
      M0GCNativeReplayAdequacy.Canary.canaryFuel, proofNode] using
      M0GCIdentifierMatcherAdequacy.Canary.pair_rule_identifier_match)]

/-- Positive discriminator: the valid pair record is admitted into exactly one
preallocated result cell. -/
theorem pair_record_accepts :
    replayRecord? profile tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel emptyOneSlot proofNode =
        some acceptedOneSlot := by
  unfold replayRecord?
  rw [pair_record_validation emptyOneSlot]
  change emptyOneSlot.writeNext? 2 = some acceptedOneSlot
  decide

/-- The complete addressed loop has the same positive result. -/
theorem pair_loop_accepts :
    replayLoop profile tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel certificate.proofs
        emptyOneSlot = some acceptedOneSlot := by
  change replayLoop profile tables certificate termState
    M0GCNativeReplayAdequacy.Canary.canaryFuel [proofNode] emptyOneSlot =
      some acceptedOneSlot
  rw [replayLoop, pair_record_accepts]
  rfl

/-- Negative capacity discriminator: a semantically valid record cannot write
past a zero-cell allocation. -/
theorem zero_capacity_rejected :
    replayRecord? profile tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel zeroSlot proofNode = none := by
  unfold replayRecord?
  rw [pair_record_validation zeroSlot]
  change zeroSlot.writeNext? 2 = none
  decide

/-- Negative authority discriminator: storage capacity cannot rescue a record
with the wrong rule fingerprint. -/
theorem wrong_fingerprint_rejected :
    replayRecord? profile tables wrongFingerprintCertificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel emptyOneSlot
        { proofNode with ruleFingerprint := ruleFingerprint + 1 } = none := by
  decide

end Canary

#print axioms resolveAdmitted?_eq_resolveIds
#print axioms replayRecord?_wellFormed
#print axioms replayLoop_wellFormed
#print axioms nativeReplayRecord?_eq_loop
#print axioms replayRecord?_refines_native
#print axioms nativeReplayLoop_cons_eq_recordResult
#print axioms replayLoop_refines_native_of_capacity
#print axioms Canary.pair_record_accepts
#print axioms Canary.pair_loop_accepts
#print axioms Canary.zero_capacity_rejected
#print axioms Canary.wrong_fingerprint_rejected

end Mettapedia.GSLT.LanguageDef.M0GCAddressedReplayControlMachine
