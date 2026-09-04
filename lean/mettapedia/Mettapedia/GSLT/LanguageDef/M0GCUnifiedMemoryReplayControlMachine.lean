import Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory

/-!
# Chronological M0GC replay in unified byte memory

This module replaces the typed result store of the addressed M0GC replay
machine with the single byte allocation containing both an immutable
certificate prefix and a mutable, aligned result suffix.  Premise lookup and
result writes operate only through checked addresses.  One-record and
complete-loop theorems refine the earlier typed addressed replay in both
success and rejection behavior.

The certificate snapshot is carried through every transition and its frame
invariant is preserved by the replay loop.  The logical record validator is
deliberately reused: this tranche changes physical storage, not proof-rule
authority.

Maturity boundary: this is a fully connected intermediate proof of concept.
Lean arrays model one allocation functionally; there is not yet pointer
provenance, an optimized rule-table ABI, generated C, verified compilation,
object code, an OS, or hardware.  The module establishes the state relation
that those lower layers must preserve.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCUnifiedMemoryReplayControlMachine

open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCPhysicalTemplateAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCNativeReplayAdequacy
open Mettapedia.GSLT.LanguageDef.M0GCFixedResultStoreRefinement
open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory
open Mettapedia.GSLT.LanguageDef.M0GCDisjointCertificateResultMemory.CheckerMemory
open Mettapedia.GSLT.LanguageDef.M0GCAddressedReplayControlMachine
open Mettapedia.GSLT.LanguageDef.M0GCBytePackedResultStoreRefinement.PackedReplay

/-! ## Premise resolution and one-record replay -/

/-- Resolve chronological premise references through checked reads from the
initialized result suffix. -/
def resolveAdmitted? (memory : CheckerMemory) :
    List UInt32 → Option (List UInt32)
  | [] => some []
  | reference :: references => do
      let resultId ← memory.readResult? reference.toNat
      let results ← resolveAdmitted? memory references
      some (resultId :: results)

/-- Unified-memory and typed-store premise resolution agree extensionally. -/
theorem resolveAdmitted?_eq_typed {memory : CheckerMemory}
    {typed : ResultStore} (refines : RefinesResultStore memory typed)
    (references : List UInt32) :
    resolveAdmitted? memory references =
      M0GCAddressedReplayControlMachine.resolveAdmitted? typed references := by
  induction references with
  | nil => rfl
  | cons reference references inductionHypothesis =>
      simp [resolveAdmitted?,
        M0GCAddressedReplayControlMachine.resolveAdmitted?,
        RefinesResultStore.read_eq_all refines reference.toNat,
        inductionHypothesis]

/-- Validate one proof record and write its result to the unified allocation. -/
def replayRecord? (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (memory : CheckerMemory) (proof : ProofNode) : Option CheckerMemory := do
  let resultId ← recordResult? profile tables certificate terms fuel
    (resolveAdmitted? memory) proof
  memory.writeResultNext? resultId

/-- One unified-memory replay transition refines the typed addressed
transition, including identical success or rejection. -/
theorem replayRecord?_refines_typed
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (memory : CheckerMemory) (typed : ResultStore) (proof : ProofNode)
    (refines : RefinesResultStore memory typed) :
    OptionRefines RefinesResultStore
      (replayRecord? profile tables certificate terms fuel memory proof)
      (M0GCAddressedReplayControlMachine.replayRecord?
        profile tables certificate terms fuel typed proof) := by
  have resolverEq :
      resolveAdmitted? memory =
        M0GCAddressedReplayControlMachine.resolveAdmitted? typed := by
    funext references
    exact resolveAdmitted?_eq_typed refines references
  unfold replayRecord?
    M0GCAddressedReplayControlMachine.replayRecord?
  rw [resolverEq]
  cases validation : recordResult? profile tables certificate terms fuel
      (M0GCAddressedReplayControlMachine.resolveAdmitted? typed) proof with
  | none => simp [OptionRefines]
  | some resultId =>
      dsimp
      by_cases memoryRoom : memory.resultUsed < memory.resultCapacity
      · have typedRoom : typed.used < typed.cells.size := by
          rw [← refines.used_eq, ← refines.capacity_eq]
          exact memoryRoom
        obtain ⟨memoryNext, memoryAccepted⟩ :=
          CheckerMemory.writeResultNext?_exists_of_room memory resultId
            refines.memoryWellFormed memoryRoom
        obtain ⟨typedNext, typedAccepted⟩ :=
          ResultStore.writeNext?_exists_of_room typed resultId
            refines.typedWellFormed typedRoom
        rw [memoryAccepted, typedAccepted]
        exact RefinesResultStore.write refines memoryAccepted typedAccepted
      · have typedNoRoom : ¬ typed.used < typed.cells.size := by
          rw [← refines.used_eq, ← refines.capacity_eq]
          exact memoryRoom
        simp [CheckerMemory.writeResultNext?, ResultStore.writeNext?,
          memoryRoom, typedNoRoom, OptionRefines]

/-- A successful record preserves the unified-memory invariant. -/
theorem replayRecord?_wellFormed
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {memory next : CheckerMemory} {proof : ProofNode}
    (wellFormed : memory.WellFormed)
    (accepted :
      replayRecord? profile tables certificate terms fuel memory proof =
        some next) :
    next.WellFormed := by
  unfold replayRecord? at accepted
  rcases Option.bind_eq_some_iff.mp accepted with
    ⟨resultId, _validated, writeAccepted⟩
  exact CheckerMemory.writeResultNext?_wellFormed wellFormed writeAccepted

/-- Any successful record retains the certificate snapshot and capacity and
advances the result frontier exactly once. -/
theorem replayRecord?_shape
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {memory next : CheckerMemory} {proof : ProofNode}
    (accepted :
      replayRecord? profile tables certificate terms fuel memory proof =
        some next) :
    next.certificate = memory.certificate ∧
      next.resultCapacity = memory.resultCapacity ∧
      next.resultUsed = memory.resultUsed + 1 := by
  unfold replayRecord? at accepted
  rcases Option.bind_eq_some_iff.mp accepted with
    ⟨resultId, _validated, writeAccepted⟩
  obtain ⟨_base, certificateEq, _offset, _resultBase, capacityEq,
      _cells, usedEq⟩ :=
    CheckerMemory.writeResultNext?_shape writeAccepted
  exact ⟨certificateEq, capacityEq, usedEq⟩

/-! ## Complete chronological replay -/

/-- Replay a chronological proof list through the unified allocation. -/
def replayLoop (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat) :
    List ProofNode → CheckerMemory → Option CheckerMemory
  | [], memory => some memory
  | proof :: proofs, memory => do
      let next ← replayRecord? profile tables certificate terms fuel
        memory proof
      replayLoop profile tables certificate terms fuel proofs next

/-- Successful complete replay preserves the unified-memory invariant. -/
theorem replayLoop_wellFormed
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proofs : List ProofNode} {memory final : CheckerMemory}
    (wellFormed : memory.WellFormed)
    (accepted :
      replayLoop profile tables certificate terms fuel proofs memory =
        some final) :
    final.WellFormed := by
  induction proofs generalizing memory with
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

/-- On success, complete replay keeps the same certificate and capacity and
advances the initialized result prefix by exactly the proof-list length. -/
theorem replayLoop_shape
    {profile : RuntimeProfile} {tables : RuleTables}
    {certificate : Certificate} {terms : TermState} {fuel : Nat}
    {proofs : List ProofNode} {memory final : CheckerMemory}
    (accepted :
      replayLoop profile tables certificate terms fuel proofs memory =
        some final) :
    final.certificate = memory.certificate ∧
      final.resultCapacity = memory.resultCapacity ∧
      final.resultUsed = memory.resultUsed + proofs.length := by
  induction proofs generalizing memory with
  | nil =>
      simp only [replayLoop, Option.some.injEq] at accepted
      subst final
      simp
  | cons proof proofs inductionHypothesis =>
      simp only [replayLoop] at accepted
      rcases Option.bind_eq_some_iff.mp accepted with
        ⟨next, recordAccepted, tailAccepted⟩
      obtain ⟨recordCertificate, recordCapacity, recordUsed⟩ :=
        replayRecord?_shape recordAccepted
      obtain ⟨tailCertificate, tailCapacity, tailUsed⟩ :=
        inductionHypothesis tailAccepted
      refine ⟨?_, ?_, ?_⟩
      · rw [tailCertificate, recordCertificate]
      · rw [tailCapacity, recordCapacity]
      · rw [tailUsed, recordUsed]
        simp only [List.length_cons]
        omega

/-- Sufficient capacity makes complete unified-memory replay refine the typed
addressed replay, including identical rejection behavior. -/
theorem replayLoop_refines_typed_of_capacity
    (profile : RuntimeProfile) (tables : RuleTables)
    (certificate : Certificate) (terms : TermState) (fuel : Nat)
    (proofs : List ProofNode) (memory : CheckerMemory)
    (typed : ResultStore) (refines : RefinesResultStore memory typed)
    (enough : memory.resultUsed + proofs.length ≤ memory.resultCapacity) :
    OptionRefines RefinesResultStore
      (replayLoop profile tables certificate terms fuel proofs memory)
      (M0GCAddressedReplayControlMachine.replayLoop
        profile tables certificate terms fuel proofs typed) := by
  induction proofs generalizing memory typed with
  | nil =>
      simpa [replayLoop,
        M0GCAddressedReplayControlMachine.replayLoop, OptionRefines]
  | cons proof proofs inductionHypothesis =>
      simp only [replayLoop,
        M0GCAddressedReplayControlMachine.replayLoop]
      have stepRefines := replayRecord?_refines_typed
        profile tables certificate terms fuel memory typed proof refines
      cases memoryStep :
          replayRecord? profile tables certificate terms fuel memory proof with
      | none =>
          cases typedStep :
              M0GCAddressedReplayControlMachine.replayRecord?
                profile tables certificate terms fuel typed proof with
          | none => simp [OptionRefines]
          | some typedNext =>
              simp [memoryStep, typedStep, OptionRefines] at stepRefines
      | some memoryNext =>
          cases typedStep :
              M0GCAddressedReplayControlMachine.replayRecord?
                profile tables certificate terms fuel typed proof with
          | none =>
              simp [memoryStep, typedStep, OptionRefines] at stepRefines
          | some typedNext =>
              have nextRefines :
                  RefinesResultStore memoryNext typedNext := by
                simpa [memoryStep, typedStep, OptionRefines] using stepRefines
              obtain ⟨_certificate, nextCapacity, nextUsed⟩ :=
                replayRecord?_shape memoryStep
              have enoughTail :
                  memoryNext.resultUsed + proofs.length ≤
                    memoryNext.resultCapacity := by
                rw [nextCapacity, nextUsed]
                simp only [List.length_cons] at enough
                omega
              exact inductionHypothesis memoryNext typedNext nextRefines
                enoughTail

/-! ## Executable discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

def pairWrittenMemory : CheckerMemory :=
  { CheckerMemory.Canary.emptyMemory with
    cells := #[10, 20, 0, 2, 0, 0, 0, 0, 0, 0, 0]
    resultUsed := 1 }

def typedPairWritten : ResultStore :=
  { base := 4
    cells := #[2, 0]
    used := 1 }

def zeroCapacityMemory : CheckerMemory :=
  { base := 1
    certificate := CheckerMemory.Canary.certificate
    cells := #[10, 20, 0]
    resultOffset := 3
    resultBase := 4
    resultCapacity := 0
    resultUsed := 0 }

theorem pair_record_accepts :
    replayRecord? profile
      M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel
      CheckerMemory.Canary.emptyMemory proofNode =
        some pairWrittenMemory := by
  have resolverEq :
      resolveAdmitted? CheckerMemory.Canary.emptyMemory =
        M0GCAddressedReplayControlMachine.resolveAdmitted?
          CheckerMemory.Canary.typedEmpty := by
    funext references
    exact resolveAdmitted?_eq_typed
      CheckerMemory.Canary.initial_refines_typed references
  unfold replayRecord?
  rw [resolverEq]
  rw [M0GCAddressedReplayControlMachine.Canary.pair_record_validation]
  decide

theorem pair_loop_accepts :
    replayLoop profile
      M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel certificate.proofs
      CheckerMemory.Canary.emptyMemory = some pairWrittenMemory := by
  change replayLoop profile
    M0GCAddressedReplayControlMachine.Canary.tables certificate termState
    M0GCNativeReplayAdequacy.Canary.canaryFuel [proofNode]
    CheckerMemory.Canary.emptyMemory = some pairWrittenMemory
  rw [replayLoop, pair_record_accepts]
  rfl

/-- Negative resource discriminator: a valid record cannot grow a zero-cell
result suffix. -/
theorem zero_capacity_rejected :
    replayRecord? profile
      M0GCAddressedReplayControlMachine.Canary.tables certificate termState
      M0GCNativeReplayAdequacy.Canary.canaryFuel zeroCapacityMemory proofNode =
        none := by
  unfold replayRecord?
  have validation :
      recordResult? profile
        M0GCAddressedReplayControlMachine.Canary.tables certificate termState
        M0GCNativeReplayAdequacy.Canary.canaryFuel
        (resolveAdmitted? zeroCapacityMemory) proofNode =
          some proofNode.resultTerm := by
    exact M0GCAddressedReplayControlMachine.Canary.pair_record_validation
      { base := 4, cells := #[], used := 0 }
  rw [validation]
  decide

/-- The real replay transition retains the immutable certificate bytes. -/
theorem pair_certificate_survives :
    pairWrittenMemory.cells.extract 0
        CheckerMemory.Canary.certificate.size =
      CheckerMemory.Canary.certificate := by
  decide

theorem pair_result_reads : pairWrittenMemory.readResult? 0 = some 2 := by
  decide

theorem pair_refines_typed :
    RefinesResultStore pairWrittenMemory typedPairWritten := by
  exact RefinesResultStore.write (resultId := 2)
    CheckerMemory.Canary.initial_refines_typed (by decide) (by decide)

end Canary

#print axioms resolveAdmitted?_eq_typed
#print axioms replayRecord?_refines_typed
#print axioms replayRecord?_wellFormed
#print axioms replayLoop_wellFormed
#print axioms replayLoop_shape
#print axioms replayLoop_refines_typed_of_capacity
#print axioms Canary.pair_loop_accepts
#print axioms Canary.zero_capacity_rejected
#print axioms Canary.pair_refines_typed

end Mettapedia.GSLT.LanguageDef.M0GCUnifiedMemoryReplayControlMachine
