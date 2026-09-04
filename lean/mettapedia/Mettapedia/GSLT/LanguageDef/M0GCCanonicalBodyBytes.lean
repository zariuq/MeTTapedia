import Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence

/-!
# Canonical body bytes for M0GC

The C proof of concept authenticates the original M0GC body bytes, while the
canonical Lean certificate reader authenticates the re-encoding of decoded
tables.  This module proves the missing canonicality bridge: successful
fixed-width decoding followed by encoding reproduces the consumed prefix.

Maturity boundary: this is a fully connected proof of concept for byte-level
canonicality of the M0GC physical records.  It is independent of C source
semantics, pointer casts, compilers, object code, operating systems, and
hardware.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCCanonicalBodyBytes

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence

/-- Successful decoding followed by encoding reproduces the exact consumed
input prefix. -/
def ReencodesPrefix (read : Reader alpha)
    (encode : alpha → List UInt8) : Prop :=
  ∀ input value rest,
    read input = some (value, rest) → input = encode value ++ rest

theorem readUInt16LE_reencodesPrefix :
    ReencodesPrefix readUInt16LE encodeUInt16LE := by
  intro input value rest accepted
  rcases input with _ | ⟨byte0, input⟩
  · simp [readUInt16LE] at accepted
  rcases input with _ | ⟨byte1, suffix⟩
  · simp [readUInt16LE] at accepted
  simp only [readUInt16LE, Option.some.injEq, Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl, rfl⟩
  simp only [encodeUInt16LE, List.cons_append, List.nil_append,
    List.cons.injEq]
  constructor
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    exact BitVec.extractLsb'_append_eq_right.symm
  · constructor
    · apply UInt8.eq_iff_toBitVec_eq.mpr
      exact BitVec.extractLsb'_append_eq_left.symm
    · trivial

theorem readUInt32LE_reencodesPrefix :
    ReencodesPrefix readUInt32LE encodeUInt32LE := by
  intro input value rest accepted
  rcases input with _ | ⟨byte0, input⟩
  · simp [readUInt32LE] at accepted
  rcases input with _ | ⟨byte1, input⟩
  · simp [readUInt32LE] at accepted
  rcases input with _ | ⟨byte2, input⟩
  · simp [readUInt32LE] at accepted
  rcases input with _ | ⟨byte3, suffix⟩
  · simp [readUInt32LE] at accepted
  simp only [readUInt32LE, Option.some.injEq, Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl, rfl⟩
  simp only [encodeUInt32LE, List.cons_append, List.nil_append,
    List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, True.intro⟩
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    exact BitVec.extractLsb'_append_eq_right.symm
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_eq_self]

theorem readUInt64LE_reencodesPrefix :
    ReencodesPrefix readUInt64LE encodeUInt64LE := by
  intro input value rest accepted
  rcases input with _ | ⟨byte0, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte1, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte2, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte3, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte4, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte5, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte6, input⟩
  · simp [readUInt64LE] at accepted
  rcases input with _ | ⟨byte7, suffix⟩
  · simp [readUInt64LE] at accepted
  simp only [readUInt64LE, Option.some.injEq, Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl, rfl⟩
  simp only [encodeUInt64LE, List.cons_append, List.nil_append,
    List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    exact BitVec.extractLsb'_append_eq_right.symm
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right]
  · apply UInt8.eq_iff_toBitVec_eq.mpr
    symm
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_eq_self]

/-! ## Composition through physical records and tables -/

theorem ReencodesPrefix.readMany
    {read : Reader alpha} {encode : alpha → List UInt8}
    (single : ReencodesPrefix read encode) :
    ∀ count,
      ReencodesPrefix
        (CompiledPlanWireFormat.readMany read count) (List.flatMap encode) := by
  intro count
  induction count with
  | zero =>
      intro input values rest accepted
      simp only [CompiledPlanWireFormat.readMany, Option.some.injEq,
        Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      rfl
  | succ count inductionHypothesis =>
      intro input values rest accepted
      cases firstResult : read input with
      | none =>
          simp [CompiledPlanWireFormat.readMany, firstResult] at accepted
      | some firstPair =>
          rcases firstPair with ⟨head, suffix⟩
          cases tailResult :
              CompiledPlanWireFormat.readMany read count suffix with
          | none =>
              simp [CompiledPlanWireFormat.readMany, firstResult, tailResult]
                at accepted
          | some tailPair =>
              rcases tailPair with ⟨tail, finalRest⟩
              simp [CompiledPlanWireFormat.readMany, firstResult, tailResult,
                Option.bind] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              have headCanonical := single input head suffix firstResult
              have tailCanonical :=
                inductionHypothesis suffix tail finalRest tailResult
              simp only [List.flatMap_cons]
              rw [headCanonical, tailCanonical, List.append_assoc]

theorem readTermNode_reencodesPrefix :
    ReencodesPrefix readTermNode encodeTermNode := by
  intro input node rest accepted
  cases symbolResult : readUInt16LE input with
  | none =>
      simp [readTermNode, symbolResult] at accepted
  | some symbolPair =>
      rcases symbolPair with ⟨symbol, rest1⟩
      cases arityResult : readUInt16LE rest1 with
      | none =>
          simp [readTermNode, symbolResult, arityResult] at accepted
      | some arityPair =>
          rcases arityPair with ⟨arity, rest2⟩
          cases childStartResult : readUInt32LE rest2 with
          | none =>
              simp [readTermNode, symbolResult, arityResult,
                childStartResult] at accepted
          | some childStartPair =>
              rcases childStartPair with ⟨childStart, rest3⟩
              cases reservedResult : readUInt32LE rest3 with
              | none =>
                  simp [readTermNode, symbolResult, arityResult,
                    childStartResult, reservedResult] at accepted
              | some reservedPair =>
                  rcases reservedPair with ⟨reserved, rest4⟩
                  cases hashResult : readUInt64LE rest4 with
                  | none =>
                      simp [readTermNode, symbolResult, arityResult,
                        childStartResult, reservedResult, hashResult]
                        at accepted
                  | some hashPair =>
                      rcases hashPair with ⟨termHash, finalRest⟩
                      simp [readTermNode, symbolResult, arityResult,
                        childStartResult, reservedResult, hashResult,
                        Option.bind] at accepted
                      rcases accepted with ⟨rfl, rfl⟩
                      have symbolCanonical :=
                        readUInt16LE_reencodesPrefix input symbol rest1
                          symbolResult
                      have arityCanonical :=
                        readUInt16LE_reencodesPrefix rest1 arity rest2
                          arityResult
                      have childStartCanonical :=
                        readUInt32LE_reencodesPrefix rest2 childStart rest3
                          childStartResult
                      have reservedCanonical :=
                        readUInt32LE_reencodesPrefix rest3 reserved rest4
                          reservedResult
                      have hashCanonical :=
                        readUInt64LE_reencodesPrefix rest4 termHash finalRest
                          hashResult
                      calc
                        input = encodeUInt16LE symbol ++ rest1 :=
                          symbolCanonical
                        _ = encodeUInt16LE symbol ++
                            (encodeUInt16LE arity ++ rest2) := by
                          rw [arityCanonical]
                        _ = encodeUInt16LE symbol ++
                            (encodeUInt16LE arity ++
                              (encodeUInt32LE childStart ++ rest3)) := by
                          rw [childStartCanonical]
                        _ = encodeUInt16LE symbol ++
                            (encodeUInt16LE arity ++
                              (encodeUInt32LE childStart ++
                                (encodeUInt32LE reserved ++ rest4))) := by
                          rw [reservedCanonical]
                        _ = encodeUInt16LE symbol ++
                            (encodeUInt16LE arity ++
                              (encodeUInt32LE childStart ++
                                (encodeUInt32LE reserved ++
                                  (encodeUInt64LE termHash ++ finalRest)))) := by
                          rw [hashCanonical]
                        _ = encodeTermNode
                              { symbol, arity, childStart, reserved,
                                termHash } ++ finalRest := by
                          simp only [encodeTermNode, List.append_assoc]

theorem readProofNode_reencodesPrefix :
    ReencodesPrefix readProofNode encodeProofNode := by
  intro input node rest accepted
  cases opcodeResult : readUInt16LE input with
  | none => simp [readProofNode, opcodeResult] at accepted
  | some opcodePair =>
      rcases opcodePair with ⟨opcode, rest1⟩
      cases ruleResult : readUInt16LE rest1 with
      | none => simp [readProofNode, opcodeResult, ruleResult] at accepted
      | some rulePair =>
          rcases rulePair with ⟨rule, rest2⟩
          cases argumentCountResult : readUInt16LE rest2 with
          | none =>
              simp [readProofNode, opcodeResult, ruleResult,
                argumentCountResult] at accepted
          | some argumentCountPair =>
              rcases argumentCountPair with ⟨argumentCount, rest3⟩
              cases premiseCountResult : readUInt16LE rest3 with
              | none =>
                  simp [readProofNode, opcodeResult, ruleResult,
                    argumentCountResult, premiseCountResult] at accepted
              | some premiseCountPair =>
                  rcases premiseCountPair with ⟨premiseCount, rest4⟩
                  cases argumentStartResult : readUInt32LE rest4 with
                  | none =>
                      simp [readProofNode, opcodeResult, ruleResult,
                        argumentCountResult, premiseCountResult,
                        argumentStartResult] at accepted
                  | some argumentStartPair =>
                      rcases argumentStartPair with ⟨argumentStart, rest5⟩
                      cases premiseStartResult : readUInt32LE rest5 with
                      | none =>
                          simp [readProofNode, opcodeResult, ruleResult,
                            argumentCountResult, premiseCountResult,
                            argumentStartResult, premiseStartResult]
                            at accepted
                      | some premiseStartPair =>
                          rcases premiseStartPair with
                            ⟨premiseStart, rest6⟩
                          cases resultTermResult : readUInt32LE rest6 with
                          | none =>
                              simp [readProofNode, opcodeResult, ruleResult,
                                argumentCountResult, premiseCountResult,
                                argumentStartResult, premiseStartResult,
                                resultTermResult] at accepted
                          | some resultTermPair =>
                              rcases resultTermPair with ⟨resultTerm, rest7⟩
                              cases reservedResult : readUInt32LE rest7 with
                              | none =>
                                  simp [readProofNode, opcodeResult,
                                    ruleResult, argumentCountResult,
                                    premiseCountResult, argumentStartResult,
                                    premiseStartResult, resultTermResult,
                                    reservedResult] at accepted
                              | some reservedPair =>
                                  rcases reservedPair with ⟨reserved, rest8⟩
                                  cases fingerprintResult :
                                      readUInt64LE rest8 with
                                  | none =>
                                      simp [readProofNode, opcodeResult,
                                        ruleResult, argumentCountResult,
                                        premiseCountResult,
                                        argumentStartResult,
                                        premiseStartResult, resultTermResult,
                                        reservedResult, fingerprintResult]
                                        at accepted
                                  | some fingerprintPair =>
                                      rcases fingerprintPair with
                                        ⟨ruleFingerprint, finalRest⟩
                                      simp [readProofNode, opcodeResult,
                                        ruleResult, argumentCountResult,
                                        premiseCountResult,
                                        argumentStartResult,
                                        premiseStartResult, resultTermResult,
                                        reservedResult, fingerprintResult,
                                        Option.bind] at accepted
                                      rcases accepted with ⟨rfl, rfl⟩
                                      have opcodeCanonical :=
                                        readUInt16LE_reencodesPrefix input
                                          opcode rest1 opcodeResult
                                      have ruleCanonical :=
                                        readUInt16LE_reencodesPrefix rest1 rule
                                          rest2 ruleResult
                                      have argumentCountCanonical :=
                                        readUInt16LE_reencodesPrefix rest2
                                          argumentCount rest3
                                          argumentCountResult
                                      have premiseCountCanonical :=
                                        readUInt16LE_reencodesPrefix rest3
                                          premiseCount rest4 premiseCountResult
                                      have argumentStartCanonical :=
                                        readUInt32LE_reencodesPrefix rest4
                                          argumentStart rest5
                                          argumentStartResult
                                      have premiseStartCanonical :=
                                        readUInt32LE_reencodesPrefix rest5
                                          premiseStart rest6 premiseStartResult
                                      have resultTermCanonical :=
                                        readUInt32LE_reencodesPrefix rest6
                                          resultTerm rest7 resultTermResult
                                      have reservedCanonical :=
                                        readUInt32LE_reencodesPrefix rest7
                                          reserved rest8 reservedResult
                                      have fingerprintCanonical :=
                                        readUInt64LE_reencodesPrefix rest8
                                          ruleFingerprint finalRest
                                          fingerprintResult
                                      calc
                                        input = encodeUInt16LE opcode ++ rest1 :=
                                          opcodeCanonical
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++ rest2) := by
                                          rw [ruleCanonical]
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++
                                              (encodeUInt16LE argumentCount ++
                                                rest3)) := by
                                          rw [argumentCountCanonical]
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++
                                              (encodeUInt16LE argumentCount ++
                                                (encodeUInt16LE premiseCount ++
                                                  rest4))) := by
                                          rw [premiseCountCanonical]
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++
                                              (encodeUInt16LE argumentCount ++
                                                (encodeUInt16LE premiseCount ++
                                                  (encodeUInt32LE
                                                    argumentStart ++ rest5)))) := by
                                          rw [argumentStartCanonical]
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++
                                              (encodeUInt16LE argumentCount ++
                                                (encodeUInt16LE premiseCount ++
                                                  (encodeUInt32LE
                                                    argumentStart ++
                                                    (encodeUInt32LE
                                                      premiseStart ++
                                                      rest6))))) := by
                                          rw [premiseStartCanonical]
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++
                                              (encodeUInt16LE argumentCount ++
                                                (encodeUInt16LE premiseCount ++
                                                  (encodeUInt32LE
                                                    argumentStart ++
                                                    (encodeUInt32LE
                                                      premiseStart ++
                                                      (encodeUInt32LE
                                                        resultTerm ++
                                                        rest7)))))) := by
                                          rw [resultTermCanonical]
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++
                                              (encodeUInt16LE argumentCount ++
                                                (encodeUInt16LE premiseCount ++
                                                  (encodeUInt32LE
                                                    argumentStart ++
                                                    (encodeUInt32LE
                                                      premiseStart ++
                                                      (encodeUInt32LE
                                                        resultTerm ++
                                                        (encodeUInt32LE
                                                          reserved ++
                                                          rest8))))))) := by
                                          rw [reservedCanonical]
                                        _ = encodeUInt16LE opcode ++
                                            (encodeUInt16LE rule ++
                                              (encodeUInt16LE argumentCount ++
                                                (encodeUInt16LE premiseCount ++
                                                  (encodeUInt32LE
                                                    argumentStart ++
                                                    (encodeUInt32LE
                                                      premiseStart ++
                                                      (encodeUInt32LE
                                                        resultTerm ++
                                                        (encodeUInt32LE
                                                          reserved ++
                                                          (encodeUInt64LE
                                                            ruleFingerprint ++
                                                            finalRest)))))))) := by
                                          rw [fingerprintCanonical]
                                        _ = encodeProofNode
                                              { opcode, rule, argumentCount,
                                                premiseCount, argumentStart,
                                                premiseStart, resultTerm,
                                                reserved, ruleFingerprint } ++
                                              finalRest := by
                                          simp only [encodeProofNode,
                                            List.append_assoc]

/-! ## Canonical bytes for complete body tables -/

/-- The byte representation of decoded body tables, independent of header
metadata. -/
def encodeBodyTables (tables : BodyTables) : List UInt8 :=
  tables.terms.flatMap encodeTermNode ++
    tables.children.flatMap encodeUInt32LE ++
    tables.proofs.flatMap encodeProofNode ++
    tables.arguments.flatMap encodeUInt32LE ++
    tables.premises.flatMap encodeUInt32LE

theorem readBodySequential_reencodesPrefix (counts : BodyCounts) :
    ReencodesPrefix (readBodySequential counts) encodeBodyTables := by
  intro input tables rest accepted
  cases termsResult :
      CompiledPlanWireFormat.readMany readTermNode counts.termCount input with
  | none =>
      simp [readBodySequential, termsResult] at accepted
  | some termsPair =>
      rcases termsPair with ⟨terms, rest1⟩
      cases childrenResult :
          CompiledPlanWireFormat.readMany readUInt32LE counts.childCount
            rest1 with
      | none =>
          simp [readBodySequential, termsResult, childrenResult] at accepted
      | some childrenPair =>
          rcases childrenPair with ⟨children, rest2⟩
          cases proofsResult :
              CompiledPlanWireFormat.readMany readProofNode counts.proofCount
                rest2 with
          | none =>
              simp [readBodySequential, termsResult, childrenResult,
                proofsResult] at accepted
          | some proofsPair =>
              rcases proofsPair with ⟨proofs, rest3⟩
              cases argumentsResult :
                  CompiledPlanWireFormat.readMany readUInt32LE
                    counts.argumentCount rest3 with
              | none =>
                  simp [readBodySequential, termsResult, childrenResult,
                    proofsResult, argumentsResult] at accepted
              | some argumentsPair =>
                  rcases argumentsPair with ⟨arguments, rest4⟩
                  cases premisesResult :
                      CompiledPlanWireFormat.readMany readUInt32LE
                        counts.premiseCount rest4 with
                  | none =>
                      simp [readBodySequential, termsResult, childrenResult,
                        proofsResult, argumentsResult, premisesResult]
                        at accepted
                  | some premisesPair =>
                      rcases premisesPair with ⟨premises, finalRest⟩
                      simp [readBodySequential, termsResult, childrenResult,
                        proofsResult, argumentsResult, premisesResult,
                        Option.bind] at accepted
                      rcases accepted with ⟨rfl, rfl⟩
                      have termsCanonical :=
                        (ReencodesPrefix.readMany
                          readTermNode_reencodesPrefix counts.termCount)
                          input terms rest1 termsResult
                      have childrenCanonical :=
                        (ReencodesPrefix.readMany
                          readUInt32LE_reencodesPrefix counts.childCount)
                          rest1 children rest2 childrenResult
                      have proofsCanonical :=
                        (ReencodesPrefix.readMany
                          readProofNode_reencodesPrefix counts.proofCount)
                          rest2 proofs rest3 proofsResult
                      have argumentsCanonical :=
                        (ReencodesPrefix.readMany
                          readUInt32LE_reencodesPrefix counts.argumentCount)
                          rest3 arguments rest4 argumentsResult
                      have premisesCanonical :=
                        (ReencodesPrefix.readMany
                          readUInt32LE_reencodesPrefix counts.premiseCount)
                          rest4 premises finalRest premisesResult
                      calc
                        input = terms.flatMap encodeTermNode ++ rest1 :=
                          termsCanonical
                        _ = terms.flatMap encodeTermNode ++
                            (children.flatMap encodeUInt32LE ++ rest2) := by
                          rw [childrenCanonical]
                        _ = terms.flatMap encodeTermNode ++
                            (children.flatMap encodeUInt32LE ++
                              (proofs.flatMap encodeProofNode ++ rest3)) := by
                          rw [proofsCanonical]
                        _ = terms.flatMap encodeTermNode ++
                            (children.flatMap encodeUInt32LE ++
                              (proofs.flatMap encodeProofNode ++
                                (arguments.flatMap encodeUInt32LE ++
                                  rest4))) := by
                          rw [argumentsCanonical]
                        _ = terms.flatMap encodeTermNode ++
                            (children.flatMap encodeUInt32LE ++
                              (proofs.flatMap encodeProofNode ++
                                (arguments.flatMap encodeUInt32LE ++
                                  (premises.flatMap encodeUInt32LE ++
                                    finalRest)))) := by
                          rw [premisesCanonical]
                        _ = encodeBodyTables
                              { terms, children, proofs, arguments,
                                premises } ++ finalRest := by
                          simp only [encodeBodyTables, List.append_assoc]

/-- A header and its decoded body tables determine the certificate value
used by the canonical reader. -/
def certificateOfTables (header : Header)
    (tables : BodyTables) : Certificate :=
  { flags := header.flags
    terms := tables.terms
    children := tables.children
    proofs := tables.proofs
    arguments := tables.arguments
    premises := tables.premises
    goalTerm := header.goalTerm
    profileDigest := header.profileDigest
    sourceDigest := header.sourceDigest }

@[simp] theorem encodeBody_certificateOfTables
    (header : Header) (tables : BodyTables) :
    encodeBody (certificateOfTables header tables) = encodeBodyTables tables :=
  rfl

/-- Successful flat-table loading fixes every byte of the body: the input is
exactly the canonical encoding of the decoded tables. -/
theorem readBodyFlat?_canonical_bytes
    (counts : BodyCounts) (bytes : List UInt8) (tables : BodyTables)
    (accepted : readBodyFlat? counts bytes = some tables) :
    bytes = encodeBodyTables tables := by
  have sequential :=
    readBodyFlat?_refines_sequential counts bytes tables accepted
  have canonical :=
    readBodySequential_reencodesPrefix counts bytes tables [] sequential
  simpa using canonical

/-! ## Executable discriminators and audit -/

theorem canary_flat_body_is_canonical :
    encodeBody canaryCertificate = encodeBodyTables canaryTables := by
  have accepted := canary_flat_body_accepts
  have canonical :=
    readBodyFlat?_canonical_bytes canaryCounts
      (encodeBody canaryCertificate) canaryTables accepted
  exact canonical

#print axioms readUInt16LE_reencodesPrefix
#print axioms readUInt32LE_reencodesPrefix
#print axioms readUInt64LE_reencodesPrefix
#print axioms ReencodesPrefix.readMany
#print axioms readTermNode_reencodesPrefix
#print axioms readProofNode_reencodesPrefix
#print axioms readBodySequential_reencodesPrefix
#print axioms readBodyFlat?_canonical_bytes
#print axioms canary_flat_body_is_canonical

end Mettapedia.GSLT.LanguageDef.M0GCCanonicalBodyBytes
