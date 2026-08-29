import Mettapedia.GSLT.LanguageDef.DerivationCheckMachine

/-!
# Dense word records for the derivation-check machine

This module gives the derivation-check machine a compact, target-owned data
representation.  Formulae, rules, evidence, provenance, and obligations are
relocated through explicit codecs; the control stream itself contains only
natural-number words.  The representation is deliberately an array of
self-contained records: a native checker can dispatch on the first word and
reject a malformed record without allocating an intermediate syntax tree.

This is not a second semantics.  Decoding produces the exact instruction type
executed by `DerivationCheckMachine.execute`, and the round-trip theorem below
connects every encoded program to that authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine

/-- A relocation table or other finite catalog used by a compiled verifier.
The only semantic requirement is exact decoding of every emitted index. -/
structure AtomCodec (Atom : Type) where
  encode : Atom → Nat
  decode? : Nat → Option Atom
  decode_encode : ∀ atom, decode? (encode atom) = some atom

structure Codecs
    (Formula Rule Evidence Provenance Obligation : Type) where
  formula : AtomCodec Formula
  rule : AtomCodec Rule
  evidence : AtomCodec Evidence
  provenance : AtomCodec Provenance
  obligation : AtomCodec Obligation

/-- Runtime checking needs only bounded decoding from proof-local arenas.
Unlike `AtomCodec`, this interface does not pretend that every possible
semantic atom has already been assigned a global natural number. -/
structure AtomDecoder (Atom : Type) where
  decode? : Nat → Option Atom

variable {Atom : Type}

/-- A proof-local arena.  Native realizations may store the same finite catalog
as a packed array; the semantic interface is bounded lookup. -/
def AtomDecoder.ofList {Atom : Type} (entries : List Atom) : AtomDecoder Atom :=
  ⟨fun index => entries[index]?⟩

/-- First occurrence of an atom in a finite arena. -/
def findAtomIndex? [DecidableEq Atom] (needle : Atom) : List Atom → Option Nat
  | [] => none
  | entry :: rest =>
      if needle = entry then some 0
      else (findAtomIndex? needle rest).map Nat.succ

theorem getElem?_findAtomIndex? [DecidableEq Atom]
    (needle : Atom) (entries : List Atom) (index : Nat)
    (found : findAtomIndex? needle entries = some index) :
    entries[index]? = some needle := by
  induction entries generalizing index with
  | nil => simp [findAtomIndex?] at found
  | cons entry rest induction =>
      by_cases equal : needle = entry
      · subst entry
        simp [findAtomIndex?] at found
        subst index
        rfl
      · cases restFound : findAtomIndex? needle rest with
        | none => simp [findAtomIndex?, equal, restFound] at found
        | some restIndex =>
            simp [findAtomIndex?, equal, restFound] at found
            subst index
            simpa using induction restIndex restFound

theorem exists_findAtomIndex?_eq_some [DecidableEq Atom]
    (needle : Atom) (entries : List Atom) (membership : needle ∈ entries) :
    ∃ index, findAtomIndex? needle entries = some index := by
  induction entries with
  | nil => simp at membership
  | cons entry rest induction =>
      by_cases equal : needle = entry
      · subst entry
        exact ⟨0, by simp [findAtomIndex?]⟩
      · have tailMembership : needle ∈ rest := by
          simpa [equal] using membership
        obtain ⟨index, found⟩ := induction tailMembership
        exact ⟨index + 1, by simp [findAtomIndex?, equal, found]⟩

/-- A finite partial codec assigns words only to atoms present in its arena.
Unlike `AtomCodec`, it makes no global-enumeration claim. -/
structure FiniteAtomCodec (Atom : Type) where
  entries : List Atom

def FiniteAtomCodec.encode? [DecidableEq Atom]
    (codec : FiniteAtomCodec Atom) (atom : Atom) : Option Nat :=
  findAtomIndex? atom codec.entries

def FiniteAtomCodec.decoder (codec : FiniteAtomCodec Atom) :
    AtomDecoder Atom :=
  AtomDecoder.ofList codec.entries

theorem FiniteAtomCodec.decode_encode [DecidableEq Atom]
    (codec : FiniteAtomCodec Atom) (atom : Atom) (index : Nat)
    (encoded : codec.encode? atom = some index) :
    codec.decoder.decode? index = some atom :=
  getElem?_findAtomIndex? atom codec.entries index encoded

structure FiniteCodecs
    (Formula Rule Evidence Provenance Obligation : Type) where
  formula : FiniteAtomCodec Formula
  rule : FiniteAtomCodec Rule
  evidence : FiniteAtomCodec Evidence
  provenance : FiniteAtomCodec Provenance
  obligation : FiniteAtomCodec Obligation

structure Decoders
    (Formula Rule Evidence Provenance Obligation : Type) where
  formula : AtomDecoder Formula
  rule : AtomDecoder Rule
  evidence : AtomDecoder Evidence
  provenance : AtomDecoder Provenance
  obligation : AtomDecoder Obligation

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}

def Codecs.decoders
    (codecs : Codecs Formula Rule Evidence Provenance Obligation) :
    Decoders Formula Rule Evidence Provenance Obligation where
  formula := ⟨codecs.formula.decode?⟩
  rule := ⟨codecs.rule.decode?⟩
  evidence := ⟨codecs.evidence.decode?⟩
  provenance := ⟨codecs.provenance.decode?⟩
  obligation := ⟨codecs.obligation.decode?⟩

def FiniteCodecs.decoders
    (codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation) :
    Decoders Formula Rule Evidence Provenance Obligation where
  formula := codecs.formula.decoder
  rule := codecs.rule.decoder
  evidence := codecs.evidence.decoder
  provenance := codecs.provenance.decoder
  obligation := codecs.obligation.decoder

abbrev WordRecord := List Nat
abbrev WordProgram := List WordRecord

private def relevanceWords (relevance : RelevanceWitness) : List Nat :=
  [relevance.distance,
    match relevance.towardRoot with
    | none => 0
    | some child => child + 1]

private def decodeRelevance (distance childCode : Nat) : RelevanceWitness :=
  if childCode = 0 then
    ⟨distance, none⟩
  else
    ⟨distance, some (childCode - 1)⟩

/-- Opcodes are stable data, not calculus rules.  A calculus is supplied only
through the codec-selected rule and the service catalog used by execution. -/
def opcodeInput : Nat := 0
def opcodeInfer : Nat := 1
def opcodeDrop : Nat := 2
def opcodeRoot : Nat := 3
def opcodeFinish : Nat := 4

def encodeInstruction
    (codecs : Codecs Formula Rule Evidence Provenance Obligation) :
    Instruction Formula Rule Evidence Provenance Obligation → WordRecord
  | .input id formula provenance relevance =>
      [opcodeInput, id, codecs.formula.encode formula,
        codecs.provenance.encode provenance] ++ relevanceWords relevance
  | .infer id rule parents evidence conclusion relevance =>
      [opcodeInfer, id, codecs.rule.encode rule,
        codecs.evidence.encode evidence, codecs.formula.encode conclusion] ++
        relevanceWords relevance ++ [parents.length] ++ parents
  | .drop id => [opcodeDrop, id]
  | .root id obligation =>
      [opcodeRoot, id, codecs.obligation.encode obligation]
  | .finish => [opcodeFinish]

/-- Partially encode one semantic instruction against proof-local finite
arenas.  Missing atoms reject compilation instead of being assigned invented
global codes. -/
def encodeInstructionFinite?
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation) :
    Instruction Formula Rule Evidence Provenance Obligation → Option WordRecord
  | .input id formula provenance relevance => do
      let formulaCode ← codecs.formula.encode? formula
      let provenanceCode ← codecs.provenance.encode? provenance
      some ([opcodeInput, id, formulaCode, provenanceCode] ++
        relevanceWords relevance)
  | .infer id rule parents evidence conclusion relevance => do
      let ruleCode ← codecs.rule.encode? rule
      let evidenceCode ← codecs.evidence.encode? evidence
      let conclusionCode ← codecs.formula.encode? conclusion
      some ([opcodeInfer, id, ruleCode, evidenceCode, conclusionCode] ++
        relevanceWords relevance ++ [parents.length] ++ parents)
  | .drop id => some [opcodeDrop, id]
  | .root id obligation => do
      let obligationCode ← codecs.obligation.encode? obligation
      some [opcodeRoot, id, obligationCode]
  | .finish => some [opcodeFinish]

def encodeProgramFinite?
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation) :
    List (Instruction Formula Rule Evidence Provenance Obligation) →
      Option WordProgram
  | [] => some []
  | instruction :: rest => do
      let record ← encodeInstructionFinite? codecs instruction
      let records ← encodeProgramFinite? codecs rest
      some (record :: records)

private def instructionFormulas :
    Instruction Formula Rule Evidence Provenance Obligation → List Formula
  | .input _ formula _ _ => [formula]
  | .infer _ _ _ _ conclusion _ => [conclusion]
  | _ => []

private def instructionRules :
    Instruction Formula Rule Evidence Provenance Obligation → List Rule
  | .infer _ rule _ _ _ _ => [rule]
  | _ => []

private def instructionEvidence :
    Instruction Formula Rule Evidence Provenance Obligation → List Evidence
  | .infer _ _ _ evidence _ _ => [evidence]
  | _ => []

private def instructionProvenance :
    Instruction Formula Rule Evidence Provenance Obligation → List Provenance
  | .input _ _ provenance _ => [provenance]
  | _ => []

private def instructionObligations :
    Instruction Formula Rule Evidence Provenance Obligation → List Obligation
  | .root _ obligation => [obligation]
  | _ => []

/-- Derive every finite semantic arena from the program itself.  Duplicate
atoms share their first code, so repeated rule and evidence payloads do not
inflate the artifact. -/
def finiteCodecsOfProgram
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    FiniteCodecs Formula Rule Evidence Provenance Obligation where
  formula := ⟨(program.flatMap instructionFormulas).eraseDups⟩
  rule := ⟨(program.flatMap instructionRules).eraseDups⟩
  evidence := ⟨(program.flatMap instructionEvidence).eraseDups⟩
  provenance := ⟨(program.flatMap instructionProvenance).eraseDups⟩
  obligation := ⟨(program.flatMap instructionObligations).eraseDups⟩

structure FiniteProgramArtifact
    (Formula Rule Evidence Provenance Obligation : Type) where
  codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation
  words : WordProgram

/-- Compile a semantic program to its proof-local arenas and compact word
stream.  The option is fail-closed; the theorem below shows that every returned
artifact decodes to exactly the supplied program. -/
def compileFiniteProgram?
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    Option (FiniteProgramArtifact Formula Rule Evidence Provenance Obligation) :=
  let codecs := finiteCodecsOfProgram program
  match encodeProgramFinite? codecs program with
  | none => none
  | some words => some ⟨codecs, words⟩

theorem exists_encodeInstructionFinite?_eq_some_of_mem
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (instruction : Instruction Formula Rule Evidence Provenance Obligation)
    (membership : instruction ∈ program) :
    ∃ record,
      encodeInstructionFinite? (finiteCodecsOfProgram program) instruction =
        some record := by
  cases instruction with
  | input id formula provenance relevance =>
      have formulaMem :
          formula ∈ (program.flatMap instructionFormulas).eraseDups := by
        simp only [List.mem_eraseDups]
        exact List.mem_flatMap.mpr
          ⟨.input id formula provenance relevance, membership, by simp
            [instructionFormulas]⟩
      have provenanceMem :
          provenance ∈ (program.flatMap instructionProvenance).eraseDups := by
        simp only [List.mem_eraseDups]
        exact List.mem_flatMap.mpr
          ⟨.input id formula provenance relevance, membership, by simp
            [instructionProvenance]⟩
      obtain ⟨formulaCode, formulaFound⟩ :=
        exists_findAtomIndex?_eq_some formula _ formulaMem
      obtain ⟨provenanceCode, provenanceFound⟩ :=
        exists_findAtomIndex?_eq_some provenance _ provenanceMem
      refine ⟨[opcodeInput, id, formulaCode, provenanceCode] ++
        relevanceWords relevance, ?_⟩
      simp [encodeInstructionFinite?, finiteCodecsOfProgram,
        FiniteAtomCodec.encode?, formulaFound, provenanceFound]
  | infer id rule parents evidence conclusion relevance =>
      have ruleMem : rule ∈ (program.flatMap instructionRules).eraseDups := by
        simp only [List.mem_eraseDups]
        exact List.mem_flatMap.mpr
          ⟨.infer id rule parents evidence conclusion relevance, membership,
            by simp [instructionRules]⟩
      have evidenceMem :
          evidence ∈ (program.flatMap instructionEvidence).eraseDups := by
        simp only [List.mem_eraseDups]
        exact List.mem_flatMap.mpr
          ⟨.infer id rule parents evidence conclusion relevance, membership,
            by simp [instructionEvidence]⟩
      have conclusionMem :
          conclusion ∈ (program.flatMap instructionFormulas).eraseDups := by
        simp only [List.mem_eraseDups]
        exact List.mem_flatMap.mpr
          ⟨.infer id rule parents evidence conclusion relevance, membership,
            by simp [instructionFormulas]⟩
      obtain ⟨ruleCode, ruleFound⟩ :=
        exists_findAtomIndex?_eq_some rule _ ruleMem
      obtain ⟨evidenceCode, evidenceFound⟩ :=
        exists_findAtomIndex?_eq_some evidence _ evidenceMem
      obtain ⟨conclusionCode, conclusionFound⟩ :=
        exists_findAtomIndex?_eq_some conclusion _ conclusionMem
      refine ⟨[opcodeInfer, id, ruleCode, evidenceCode, conclusionCode] ++
        relevanceWords relevance ++ [parents.length] ++ parents, ?_⟩
      simp [encodeInstructionFinite?, finiteCodecsOfProgram,
        FiniteAtomCodec.encode?, ruleFound, evidenceFound, conclusionFound]
  | drop id =>
      exact ⟨[opcodeDrop, id], rfl⟩
  | root id obligation =>
      have obligationMem :
          obligation ∈
            (program.flatMap instructionObligations).eraseDups := by
        simp only [List.mem_eraseDups]
        exact List.mem_flatMap.mpr
          ⟨.root id obligation, membership, by simp [instructionObligations]⟩
      obtain ⟨obligationCode, obligationFound⟩ :=
        exists_findAtomIndex?_eq_some obligation _ obligationMem
      refine ⟨[opcodeRoot, id, obligationCode], ?_⟩
      simp [encodeInstructionFinite?, finiteCodecsOfProgram,
        FiniteAtomCodec.encode?, obligationFound]
  | finish =>
      exact ⟨[opcodeFinish], rfl⟩

private theorem exists_encodeProgramFinite?_eq_some_of_each
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (encodable : ∀ instruction ∈ program,
      ∃ record, encodeInstructionFinite? codecs instruction = some record) :
    ∃ words, encodeProgramFinite? codecs program = some words := by
  induction program with
  | nil => exact ⟨[], rfl⟩
  | cons instruction rest induction =>
      obtain ⟨record, recordEq⟩ := encodable instruction (by simp)
      obtain ⟨records, recordsEq⟩ := induction fun candidate membership =>
        encodable candidate (by simp [membership])
      exact ⟨record :: records, by
        simp [encodeProgramFinite?, recordEq, recordsEq]⟩

theorem exists_compileFiniteProgram?_eq_some
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    ∃ artifact : FiniteProgramArtifact
        Formula Rule Evidence Provenance Obligation,
      compileFiniteProgram? program = some artifact := by
  have each : ∀ instruction ∈ program,
      ∃ record,
        encodeInstructionFinite? (finiteCodecsOfProgram program) instruction =
          some record := by
    intro instruction membership
    exact exists_encodeInstructionFinite?_eq_some_of_mem program instruction
      membership
  obtain ⟨words, encoded⟩ :=
    exists_encodeProgramFinite?_eq_some_of_each
      (finiteCodecsOfProgram program) program each
  exact ⟨⟨finiteCodecsOfProgram program, words⟩, by
    simp [compileFiniteProgram?, encoded]⟩

/-- Decode exactly one record.  Extra words, truncated records, unknown
opcodes, and a dishonest parent count all fail closed. -/
def decodeInstructionUsing?
    (decoders : Decoders Formula Rule Evidence Provenance Obligation) :
    WordRecord →
      Option (Instruction Formula Rule Evidence Provenance Obligation)
  | [opcode, id, formulaCode, provenanceCode, distance, childCode] => do
      if opcode != opcodeInput then none else
      let formula ← decoders.formula.decode? formulaCode
      let provenance ← decoders.provenance.decode? provenanceCode
      some (.input id formula provenance (decodeRelevance distance childCode))
  | opcode :: id :: ruleCode :: evidenceCode :: conclusionCode ::
      distance :: childCode :: parentCount :: parents => do
      if opcode != opcodeInfer || parents.length != parentCount then none else
      let rule ← decoders.rule.decode? ruleCode
      let evidence ← decoders.evidence.decode? evidenceCode
      let conclusion ← decoders.formula.decode? conclusionCode
      some (.infer id rule parents evidence conclusion
        (decodeRelevance distance childCode))
  | [opcode, id] =>
      if opcode = opcodeDrop then some (.drop id) else none
  | [opcode, id, obligationCode] => do
      if opcode != opcodeRoot then none else
      let obligation ← decoders.obligation.decode? obligationCode
      some (.root id obligation)
  | [opcode] =>
      if opcode = opcodeFinish then some .finish else none
  | _ => none

def decodeInstruction?
    (codecs : Codecs Formula Rule Evidence Provenance Obligation) :
    WordRecord →
      Option (Instruction Formula Rule Evidence Provenance Obligation) :=
  decodeInstructionUsing? codecs.decoders

theorem decodeInstructionUsing?_of_encodeInstructionFinite?
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation)
    (instruction : Instruction Formula Rule Evidence Provenance Obligation)
    (record : WordRecord)
    (encoded : encodeInstructionFinite? codecs instruction = some record) :
    decodeInstructionUsing? codecs.decoders record = some instruction := by
  cases instruction with
  | input id formula provenance relevance =>
      cases formulaEq : codecs.formula.encode? formula with
      | none => simp [encodeInstructionFinite?, formulaEq] at encoded
      | some formulaCode =>
          cases provenanceEq : codecs.provenance.encode? provenance with
          | none =>
              simp [encodeInstructionFinite?, formulaEq, provenanceEq] at encoded
          | some provenanceCode =>
              simp [encodeInstructionFinite?, formulaEq, provenanceEq] at encoded
              subst record
              have formulaDecode := codecs.formula.decode_encode formula
                formulaCode formulaEq
              have provenanceDecode := codecs.provenance.decode_encode provenance
                provenanceCode provenanceEq
              cases relevance with
              | mk distance towardRoot =>
                  cases towardRoot with
                  | none =>
                      simp [decodeInstructionUsing?, FiniteCodecs.decoders,
                        relevanceWords, decodeRelevance, formulaDecode,
                        provenanceDecode, opcodeInput]
                  | some child =>
                      simp [decodeInstructionUsing?, FiniteCodecs.decoders,
                        relevanceWords, decodeRelevance, formulaDecode,
                        provenanceDecode, opcodeInput]
  | infer id rule parents evidence conclusion relevance =>
      cases ruleEq : codecs.rule.encode? rule with
      | none => simp [encodeInstructionFinite?, ruleEq] at encoded
      | some ruleCode =>
          cases evidenceEq : codecs.evidence.encode? evidence with
          | none => simp [encodeInstructionFinite?, ruleEq, evidenceEq] at encoded
          | some evidenceCode =>
              cases conclusionEq : codecs.formula.encode? conclusion with
              | none =>
                  simp [encodeInstructionFinite?, ruleEq, evidenceEq,
                    conclusionEq] at encoded
              | some conclusionCode =>
                  simp [encodeInstructionFinite?, ruleEq, evidenceEq,
                    conclusionEq] at encoded
                  subst record
                  have ruleDecode := codecs.rule.decode_encode rule ruleCode ruleEq
                  have evidenceDecode := codecs.evidence.decode_encode evidence
                    evidenceCode evidenceEq
                  have conclusionDecode := codecs.formula.decode_encode conclusion
                    conclusionCode conclusionEq
                  cases relevance with
                  | mk distance towardRoot =>
                      cases towardRoot with
                      | none =>
                          simp [decodeInstructionUsing?, FiniteCodecs.decoders,
                            relevanceWords, decodeRelevance, ruleDecode,
                            evidenceDecode, conclusionDecode, opcodeInfer]
                      | some child =>
                          simp [decodeInstructionUsing?, FiniteCodecs.decoders,
                            relevanceWords, decodeRelevance, ruleDecode,
                            evidenceDecode, conclusionDecode, opcodeInfer]
  | drop id =>
      simp [encodeInstructionFinite?] at encoded
      subst record
      simp [decodeInstructionUsing?, opcodeDrop]
  | root id obligation =>
      cases obligationEq : codecs.obligation.encode? obligation with
      | none => simp [encodeInstructionFinite?, obligationEq] at encoded
      | some obligationCode =>
          simp [encodeInstructionFinite?, obligationEq] at encoded
          subst record
          have obligationDecode := codecs.obligation.decode_encode obligation
            obligationCode obligationEq
          simp [decodeInstructionUsing?, FiniteCodecs.decoders,
            obligationDecode, opcodeRoot]
  | finish =>
      simp [encodeInstructionFinite?] at encoded
      subst record
      simp [decodeInstructionUsing?, opcodeFinish]

private theorem decodeRelevance_words (relevance : RelevanceWitness) :
    (match relevanceWords relevance with
      | [distance, childCode] => decodeRelevance distance childCode
      | _ => ⟨0, none⟩) = relevance := by
  cases relevance with
  | mk distance towardRoot =>
      cases towardRoot with
      | none => simp [relevanceWords, decodeRelevance]
      | some child => simp [relevanceWords, decodeRelevance]

@[simp] theorem decodeInstruction?_encodeInstruction
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (instruction :
      Instruction Formula Rule Evidence Provenance Obligation) :
    decodeInstruction? codecs (encodeInstruction codecs instruction) =
      some instruction := by
  cases instruction with
  | input id formula provenance relevance =>
      cases relevance with
      | mk distance towardRoot =>
          cases towardRoot with
          | none =>
              simp [encodeInstruction, relevanceWords, decodeInstruction?,
                decodeInstructionUsing?, Codecs.decoders,
                decodeRelevance, codecs.formula.decode_encode,
                codecs.provenance.decode_encode, opcodeInput]
          | some child =>
              simp [encodeInstruction, relevanceWords, decodeInstruction?,
                decodeInstructionUsing?, Codecs.decoders,
                decodeRelevance, codecs.formula.decode_encode,
                codecs.provenance.decode_encode, opcodeInput]
  | infer id rule parents evidence conclusion relevance =>
      cases relevance with
      | mk distance towardRoot =>
          cases towardRoot with
          | none =>
              simp [encodeInstruction, relevanceWords, decodeInstruction?,
                decodeInstructionUsing?, Codecs.decoders,
                decodeRelevance, codecs.rule.decode_encode,
                codecs.evidence.decode_encode, codecs.formula.decode_encode,
                opcodeInfer]
          | some child =>
              simp [encodeInstruction, relevanceWords, decodeInstruction?,
                decodeInstructionUsing?, Codecs.decoders,
                decodeRelevance, codecs.rule.decode_encode,
                codecs.evidence.decode_encode, codecs.formula.decode_encode,
                opcodeInfer]
  | drop id =>
      simp [encodeInstruction, decodeInstruction?, decodeInstructionUsing?,
        opcodeDrop]
  | root id obligation =>
      simp [encodeInstruction, decodeInstruction?, decodeInstructionUsing?,
        Codecs.decoders,
        codecs.obligation.decode_encode, opcodeRoot]
  | finish =>
      simp [encodeInstruction, decodeInstruction?, decodeInstructionUsing?,
        opcodeFinish]

@[simp] theorem decodeInstructionUsing?_encodeInstruction
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (instruction :
      Instruction Formula Rule Evidence Provenance Obligation) :
    decodeInstructionUsing? codecs.decoders
        (encodeInstruction codecs instruction) = some instruction := by
  simpa [decodeInstruction?] using
    decodeInstruction?_encodeInstruction codecs instruction

def encodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    WordProgram :=
  program.map (encodeInstruction codecs)

def decodeProgramUsing?
    (decoders : Decoders Formula Rule Evidence Provenance Obligation) :
    WordProgram →
      Option (List
        (Instruction Formula Rule Evidence Provenance Obligation))
  | [] => some []
  | record :: rest => do
      let instruction ← decodeInstructionUsing? decoders record
      let instructions ← decodeProgramUsing? decoders rest
      some (instruction :: instructions)

def decodeProgram?
    (codecs : Codecs Formula Rule Evidence Provenance Obligation) :
    WordProgram →
      Option (List
        (Instruction Formula Rule Evidence Provenance Obligation)) :=
  decodeProgramUsing? codecs.decoders

theorem decodeProgramUsing?_of_encodeProgramFinite?
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (codecs : FiniteCodecs Formula Rule Evidence Provenance Obligation)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (words : WordProgram)
    (encoded : encodeProgramFinite? codecs program = some words) :
    decodeProgramUsing? codecs.decoders words = some program := by
  induction program generalizing words with
  | nil =>
      simp [encodeProgramFinite?] at encoded
      subst words
      rfl
  | cons instruction rest induction =>
      cases recordEq : encodeInstructionFinite? codecs instruction with
      | none => simp [encodeProgramFinite?, recordEq] at encoded
      | some record =>
          cases restEq : encodeProgramFinite? codecs rest with
          | none => simp [encodeProgramFinite?, recordEq, restEq] at encoded
          | some records =>
              simp [encodeProgramFinite?, recordEq, restEq] at encoded
              subst words
              simp [decodeProgramUsing?,
                decodeInstructionUsing?_of_encodeInstructionFinite? codecs
                  instruction record recordEq,
                induction records restEq]

theorem compileFiniteProgram?_decodes
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (artifact : FiniteProgramArtifact
      Formula Rule Evidence Provenance Obligation)
    (compiled : compileFiniteProgram? program = some artifact) :
    decodeProgramUsing? artifact.codecs.decoders artifact.words =
      some program := by
  unfold compileFiniteProgram? at compiled
  cases encoded : encodeProgramFinite? (finiteCodecsOfProgram program) program with
  | none => simp [encoded] at compiled
  | some words =>
      simp [encoded] at compiled
      subst artifact
      exact decodeProgramUsing?_of_encodeProgramFinite?
        (finiteCodecsOfProgram program) program words encoded

@[simp] theorem decodeProgramUsing?_encodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    decodeProgramUsing? codecs.decoders (encodeProgram codecs program) =
      some program := by
  induction program with
  | nil => simp [encodeProgram, decodeProgramUsing?]
  | cons instruction rest induction =>
      change decodeProgramUsing? codecs.decoders
          (encodeInstruction codecs instruction ::
            List.map (encodeInstruction codecs) rest) =
        some (instruction :: rest)
      change decodeProgramUsing? codecs.decoders
          (List.map (encodeInstruction codecs) rest) = some rest at induction
      simp [decodeProgramUsing?, induction]

@[simp] theorem decodeProgram?_encodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    decodeProgram? codecs (encodeProgram codecs program) = some program := by
  exact decodeProgramUsing?_encodeProgram codecs program

theorem decodeProgramUsing?_preserves_isEmpty
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (words : WordProgram)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (decoded : decodeProgramUsing? decoders words = some program) :
    words.isEmpty = program.isEmpty := by
  cases words with
  | nil => simp [decodeProgramUsing?] at decoded; subst program; rfl
  | cons record rest =>
      cases instructionEq : decodeInstructionUsing? decoders record with
      | none => simp [decodeProgramUsing?, instructionEq] at decoded
      | some instruction =>
          cases restEq : decodeProgramUsing? decoders rest with
          | none => simp [decodeProgramUsing?, instructionEq, restEq] at decoded
          | some instructions =>
              simp [decodeProgramUsing?, instructionEq, restEq] at decoded
              subst program
              rfl

theorem decodeProgram?_preserves_isEmpty
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (words : WordProgram)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (decoded : decodeProgram? codecs words = some program) :
    words.isEmpty = program.isEmpty :=
  decodeProgramUsing?_preserves_isEmpty codecs.decoders words program decoded

/-- Execute decoded instructions without storing the unconsumed suffix in the
semantic state.  This is the fold that a native word-stream loop realizes. -/
def runDecodedFrom
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    State Formula Rule Evidence Provenance Obligation ServiceState →
      List (Instruction Formula Rule Evidence Provenance Obligation) →
      Config Formula Rule Evidence Provenance Obligation ServiceState
  | _, [] => .halted (.fault .missingFinish)
  | state, instruction :: rest =>
      match advance services (!rest.isEmpty) instruction state with
      | .halted outcome => .halted outcome
      | .running next => runDecodedFrom services next rest

/-- The fold form and the reflexive-transitive list-machine runner are the
same execution.  This is the fusion license used by the word target. -/
theorem runFuel_eq_runDecodedFrom
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    runFuel services (program.length + 1)
        (.running { state with instructions := program }) =
      runDecodedFrom services state program := by
  induction program generalizing state with
  | nil => simp [runFuel, step?, runDecodedFrom, haltFault]
  | cons instruction rest induction =>
      change runFuel services (rest.length + 1)
          (replaceInstructions rest
            (advance services (!rest.isEmpty) instruction
              { state with instructions := instruction :: rest })) =
        (match advance services (!rest.isEmpty) instruction state with
        | .halted outcome => .halted outcome
        | .running next => runDecodedFrom services next rest)
      rw [advance_set_instructions]
      cases advanced : advance services (!rest.isEmpty) instruction state with
      | halted outcome =>
          simp [replaceInstructions, runFuel, step?]
      | running next =>
          simpa [replaceInstructions, advanced, runDecodedFrom] using
            induction next

/-- The initial fold is exactly the public semantic executor. -/
theorem runDecodedFrom_initial_eq_execute
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    runDecodedFrom services
        { instructions := [], nodes := [], nextId := 0, root? := none,
          serviceState := services.initial }
        program =
      execute services program := by
  symm
  exact runFuel_eq_runDecodedFrom services
    { instructions := [], nodes := [], nextId := 0, root? := none,
      serviceState := services.initial }
    program

/-- Decode and execute one record at a time.  A semantic fault halts without
decoding later records, while a malformed record encountered on the live path
fails closed with `none`. -/
def runEncodedFromUsing?
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    State Formula Rule Evidence Provenance Obligation ServiceState →
      WordProgram →
      Option (Config Formula Rule Evidence Provenance Obligation ServiceState)
  | _, [] => some (.halted (.fault .missingFinish))
  | state, record :: rest => do
      let instruction ← decodeInstructionUsing? decoders record
      match advance services (!rest.isEmpty) instruction state with
      | .halted outcome => some (.halted outcome)
      | .running next => runEncodedFromUsing? decoders services next rest

def runEncodedFrom?
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    State Formula Rule Evidence Provenance Obligation ServiceState →
      WordProgram →
      Option (Config Formula Rule Evidence Provenance Obligation ServiceState) :=
  runEncodedFromUsing? codecs.decoders services

def executeEncodedFusedUsing?
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : WordProgram) :
    Option (Config Formula Rule Evidence Provenance Obligation ServiceState) :=
  runEncodedFromUsing? decoders services
    { instructions := [], nodes := [], nextId := 0, root? := none,
      serviceState := services.initial }
    program

def executeEncodedFused?
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : WordProgram) :
    Option (Config Formula Rule Evidence Provenance Obligation ServiceState) :=
  executeEncodedFusedUsing? codecs.decoders services program

theorem runEncodedFrom?_encodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    runEncodedFromUsing? codecs.decoders services state
        (encodeProgram codecs program) =
      some (runDecodedFrom services state program) := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest induction =>
      simp only [encodeProgram, List.map_cons, runEncodedFromUsing?,
        decodeInstructionUsing?_encodeInstruction]
      cases advanced : advance services (!rest.isEmpty) instruction state with
      | halted outcome => simp [runDecodedFrom, advanced]
      | running next =>
          simpa [runDecodedFrom, advanced, encodeProgram] using induction next

theorem runEncodedFromUsing?_eq_of_decodeProgram
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (decoded : decodeProgramUsing? decoders words = some program) :
    runEncodedFromUsing? decoders services state words =
      some (runDecodedFrom services state program) := by
  induction words generalizing state program with
  | nil =>
      simp [decodeProgramUsing?] at decoded
      subst program
      rfl
  | cons record rest induction =>
      cases instructionEq : decodeInstructionUsing? decoders record with
      | none => simp [decodeProgramUsing?, instructionEq] at decoded
      | some instruction =>
          cases restEq : decodeProgramUsing? decoders rest with
          | none => simp [decodeProgramUsing?, instructionEq, restEq] at decoded
          | some instructions =>
              simp [decodeProgramUsing?, instructionEq, restEq] at decoded
              subst program
              have emptiness :=
                decodeProgramUsing?_preserves_isEmpty decoders rest instructions
                  restEq
              simp only [runEncodedFromUsing?, runDecodedFrom]
              rw [instructionEq]
              rw [← emptiness]
              cases advanced : advance services (!rest.isEmpty) instruction
                  state with
              | halted outcome =>
                  simp [advanced]
              | running next =>
                  simpa [advanced] using induction next instructions restEq

theorem runEncodedFrom?_eq_of_decodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (decoded : decodeProgram? codecs words = some program) :
    runEncodedFrom? codecs services state words =
      some (runDecodedFrom services state program) :=
  by
    exact runEncodedFromUsing?_eq_of_decodeProgram codecs.decoders services state
      words program decoded

@[simp] theorem executeEncodedFused?_encodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    executeEncodedFused? codecs services (encodeProgram codecs program) =
      some (execute services program) := by
  rw [executeEncodedFused?, executeEncodedFusedUsing?,
    runEncodedFrom?_encodeProgram,
    runDecodedFrom_initial_eq_execute]

/-- The native-facing entry point: decode once, then run the unique semantic
machine.  Production lowering fuses these two phases into one array loop. -/
def executeEncoded?
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : WordProgram) :
    Option (Config Formula Rule Evidence Provenance Obligation ServiceState) := do
  let instructions ← decodeProgram? codecs program
  some (execute services instructions)

theorem executeEncodedFused?_eq_executeEncoded?_of_decode
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (decoded : decodeProgram? codecs words = some program) :
    executeEncodedFused? codecs services words =
      executeEncoded? codecs services words := by
  rw [executeEncodedFused?,
    executeEncodedFusedUsing?,
    runEncodedFromUsing?_eq_of_decodeProgram codecs.decoders services _ words
      program decoded,
    runDecodedFrom_initial_eq_execute]
  simp [executeEncoded?, decoded]

/-! ## The compact word machine as a GSLT -/

inductive WordConfig
    (Formula Rule Evidence Provenance Obligation ServiceState : Type) where
  | running (records : WordProgram)
      (state : State Formula Rule Evidence Provenance Obligation ServiceState)
  | halted (outcome : Outcome Formula Obligation)
deriving DecidableEq, Repr

def WordConfig.ofConfig :
    Config Formula Rule Evidence Provenance Obligation ServiceState →
      WordConfig Formula Rule Evidence Provenance Obligation ServiceState
  | .running state => .running [] state
  | .halted outcome => .halted outcome

/-- One compact-machine step decodes at most one record and immediately applies
the shared semantic core.  Malformed records are explicit language faults. -/
def wordStepUsing?
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    WordConfig Formula Rule Evidence Provenance Obligation ServiceState →
      Option
        (WordConfig Formula Rule Evidence Provenance Obligation ServiceState)
  | .halted _ => none
  | .running [] _ => some (.halted (.fault .missingFinish))
  | .running (record :: rest) state =>
      match decodeInstructionUsing? decoders record with
      | none => some (.halted (.fault .malformedRecord))
      | some instruction =>
          match advance services (!rest.isEmpty) instruction state with
          | .halted outcome => some (.halted outcome)
          | .running next => some (.running rest next)

def wordStep?
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :=
  wordStepUsing? codecs.decoders services

def wordGsltUsing
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    Mettapedia.GSLT.GSLT where
  Term := WordConfig Formula Rule Evidence Provenance Obligation ServiceState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    wordStepUsing? decoders services source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def wordGslt
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    Mettapedia.GSLT.GSLT :=
  wordGsltUsing codecs.decoders services

def runWordFuelUsing
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :
    Nat → WordConfig Formula Rule Evidence Provenance Obligation ServiceState →
      WordConfig Formula Rule Evidence Provenance Obligation ServiceState
  | 0, config => config
  | fuel + 1, config =>
      match wordStepUsing? decoders services config with
      | none => config
      | some next => runWordFuelUsing decoders services fuel next

def runWordFuel
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState) :=
  runWordFuelUsing codecs.decoders services

def executeWordUsing
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram) :
    WordConfig Formula Rule Evidence Provenance Obligation ServiceState :=
  runWordFuelUsing decoders services (words.length + 1)
    (.running words
      { instructions := [], nodes := [], nextId := 0, root? := none,
        serviceState := services.initial })

def executeWord
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram) :
    WordConfig Formula Rule Evidence Provenance Obligation ServiceState :=
  executeWordUsing codecs.decoders services words

theorem runWordFuelUsing_eq_runEncodedFromUsing
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram) :
    runWordFuelUsing decoders services (words.length + 1)
        (.running words state) =
      match runEncodedFromUsing? decoders services state words with
      | none => .halted (.fault .malformedRecord)
      | some config => .ofConfig config := by
  induction words generalizing state with
  | nil =>
      simp [runWordFuelUsing, wordStepUsing?, runEncodedFromUsing?,
        WordConfig.ofConfig]
  | cons record rest induction =>
      cases decoded : decodeInstructionUsing? decoders record with
      | none =>
          simp [runWordFuelUsing, wordStepUsing?, runEncodedFromUsing?, decoded]
      | some instruction =>
          cases advanced : advance services (!rest.isEmpty) instruction state with
          | halted outcome =>
              simp [runWordFuelUsing, wordStepUsing?, runEncodedFromUsing?,
                decoded, advanced, WordConfig.ofConfig]
          | running next =>
              simpa [runWordFuelUsing, wordStepUsing?, runEncodedFromUsing?,
                decoded, advanced]
                using induction next

theorem runWordFuel_eq_runEncodedFrom
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (state : State Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram) :
    runWordFuel codecs services (words.length + 1) (.running words state) =
      match runEncodedFrom? codecs services state words with
      | none => .halted (.fault .malformedRecord)
      | some config => .ofConfig config := by
  exact runWordFuelUsing_eq_runEncodedFromUsing codecs.decoders services state
    words

theorem executeWordUsing_eq_of_decodeProgram
    (decoders : Decoders Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (words : WordProgram)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (decoded : decodeProgramUsing? decoders words = some program) :
    executeWordUsing decoders services words =
      .ofConfig (execute services program) := by
  rw [executeWordUsing, runWordFuelUsing_eq_runEncodedFromUsing,
    runEncodedFromUsing?_eq_of_decodeProgram decoders services _ words program
      decoded,
    runDecodedFrom_initial_eq_execute]

def executeFiniteArtifact
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (artifact : FiniteProgramArtifact
      Formula Rule Evidence Provenance Obligation) :
    WordConfig Formula Rule Evidence Provenance Obligation ServiceState :=
  executeWordUsing artifact.codecs.decoders services artifact.words

theorem executeFiniteArtifact_eq_of_compile
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (artifact : FiniteProgramArtifact
      Formula Rule Evidence Provenance Obligation)
    (compiled : compileFiniteProgram? program = some artifact) :
    executeFiniteArtifact services artifact =
      .ofConfig (execute services program) := by
  exact executeWordUsing_eq_of_decodeProgram artifact.codecs.decoders services
    artifact.words program
    (compileFiniteProgram?_decodes program artifact compiled)

@[simp] theorem executeWord_encodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    executeWord codecs services (encodeProgram codecs program) =
      .ofConfig (execute services program) := by
  exact executeWordUsing_eq_of_decodeProgram codecs.decoders services
    (encodeProgram codecs program) program
    (decodeProgramUsing?_encodeProgram codecs program)

@[simp] theorem executeEncoded?_encodeProgram
    (codecs : Codecs Formula Rule Evidence Provenance Obligation)
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    executeEncoded? codecs services (encodeProgram codecs program) =
      some (execute services program) := by
  simp [executeEncoded?]

/-! ## Format canaries -/

def natCodec : AtomCodec Nat where
  encode := id
  decode? := some
  decode_encode := by intro atom; rfl

def natCodecs : Codecs Nat Nat Nat Nat Nat where
  formula := natCodec
  rule := natCodec
  evidence := natCodec
  provenance := natCodec
  obligation := natCodec

def canaryProgram : List (Instruction Nat Nat Nat Nat Nat) := [
  .input 0 17 3 ⟨1, some 1⟩,
  .infer 1 8 [0] 9 17 ⟨0, none⟩,
  .root 1 4,
  .finish
]

theorem canary_round_trip :
    decodeProgram? natCodecs (encodeProgram natCodecs canaryProgram) =
      some canaryProgram := by
  exact decodeProgram?_encodeProgram natCodecs canaryProgram

theorem unknown_opcode_rejected :
    decodeInstruction? natCodecs [99] = none := by decide

theorem truncated_input_rejected :
    decodeInstruction? natCodecs [opcodeInput, 0, 17] = none := by decide

theorem dishonest_parent_count_rejected :
    decodeInstruction? natCodecs
      [opcodeInfer, 1, 8, 9, 17, 0, 0, 2, 0] = none := by decide

theorem trailing_finish_words_rejected :
    decodeInstruction? natCodecs [opcodeFinish, 0] = none := by decide

#print axioms decodeInstruction?_encodeInstruction
#print axioms decodeProgram?_encodeProgram
#print axioms getElem?_findAtomIndex?
#print axioms exists_compileFiniteProgram?_eq_some
#print axioms decodeInstructionUsing?_of_encodeInstructionFinite?
#print axioms decodeProgramUsing?_of_encodeProgramFinite?
#print axioms compileFiniteProgram?_decodes
#print axioms runFuel_eq_runDecodedFrom
#print axioms runDecodedFrom_initial_eq_execute
#print axioms runEncodedFrom?_encodeProgram
#print axioms runEncodedFrom?_eq_of_decodeProgram
#print axioms executeEncodedFused?_encodeProgram
#print axioms executeEncodedFused?_eq_executeEncoded?_of_decode
#print axioms executeEncoded?_encodeProgram
#print axioms runWordFuel_eq_runEncodedFrom
#print axioms executeWord_encodeProgram
#print axioms executeWordUsing_eq_of_decodeProgram
#print axioms executeFiniteArtifact_eq_of_compile
#print axioms canary_round_trip
#print axioms unknown_opcode_rejected
#print axioms truncated_input_rejected
#print axioms dishonest_parent_count_rejected
#print axioms trailing_finish_words_rejected

end Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
