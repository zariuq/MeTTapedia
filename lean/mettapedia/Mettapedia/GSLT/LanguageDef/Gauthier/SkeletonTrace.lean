/-
# Authenticated postfix traces and higher-order child roles

The runtime parser and graph adapter use postfix operator ids.  This module
proves that the established E1 parser and its canonical postfix emitter are
mutual inverses on accepted streams, then attaches child roles computed from
the authenticated signature's `hoArity` field.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.Gauthier.SkeletonMask

namespace Mettapedia.GSLT.LanguageDef.GauthierSkeletonTrace

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton

/-- Canonical tokens represented by a raw parser stack, oldest tree first. -/
def stackTokens (stack : List Prog) : List Tok :=
  (stack.reverse.map rpnTokens).flatten

/-- One successful raw parser step appends exactly the consumed operator id. -/
theorem recognizeRawStep_stackTokens {sig : Signature σ} {id : Tok}
    {stack next : List Prog}
    (hstep : recognizeRawStep sig id stack = some next) :
    stackTokens next = stackTokens stack ++ [id] := by
  unfold recognizeRawStep at hstep
  cases hentry : entryAt sig id with
  | none => simp [hentry] at hstep
  | some entry =>
      simp only [hentry] at hstep
      cases hpop : popN entry.arity stack with
      | none => simp [hpop] at hstep
      | some popped =>
          rcases popped with ⟨args, rest⟩
          simp only [hpop, Option.some.injEq] at hstep
          subst next
          have hsplit : args ++ rest = stack := popN_append hpop
          subst stack
          simp [stackTokens, rpnTokens, List.reverse_append, List.map_append,
            List.flatten_append, List.append_assoc]

/-- Folding a successful token suffix appends precisely that suffix to stack serialization. -/
theorem recognizeRawStack_stackTokens (sig : Signature σ) :
    ∀ (tokens : List Tok) (stack finalStack : List Prog),
      recognizeRawStack sig tokens stack = some finalStack →
      stackTokens finalStack = stackTokens stack ++ tokens
  | [], stack, finalStack, hrun => by
      simp only [recognizeRawStack, Option.some.injEq] at hrun
      subst finalStack
      simp
  | id :: rest, stack, finalStack, hrun => by
      simp only [recognizeRawStack] at hrun
      cases hstep : recognizeRawStep sig id stack with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some middle =>
          rw [hstep] at hrun
          have hfirst := recognizeRawStep_stackTokens hstep
          have htail := recognizeRawStack_stackTokens sig rest middle finalStack hrun
          rw [htail, hfirst]
          simp [List.append_assoc]

/-- Accepted postfix streams are already the canonical serialization of their parsed tree. -/
theorem recognize_eq_some_rpnTokens {sig : Signature σ} {tokens : List Tok} {program : Prog}
    (hrecognize : recognize sig tokens = some program) :
    rpnTokens program = tokens := by
  unfold recognize recognizeRaw at hrecognize
  cases hstack : recognizeRawStack sig tokens [] with
  | none => simp [hstack] at hrecognize
  | some stack =>
      rw [hstack] at hrecognize
      cases stack with
      | nil => simp at hrecognize
      | cons head tail =>
          cases tail with
          | nil =>
              simp only [Option.some.injEq] at hrecognize
              subst head
              have htokens := recognizeRawStack_stackTokens sig tokens [] [program] hstack
              simpa [stackTokens] using htokens
          | cons second rest => simp at hrecognize

/-- T3 encoder→decoder crown. -/
theorem parse_emit_roundTrip {sig : Signature σ} {program : Prog}
    (hwellFormed : WellFormed sig program) :
    recognize sig (rpnTokens program) = some program := by
  unfold recognize recognizeRaw
  simp [recognizeRawStack_rpnTokens_complete hwellFormed []]

/-- T3 decoder→encoder crown. -/
theorem emit_parse_roundTrip {sig : Signature σ} {tokens : List Tok} {program : Prog}
    (hrecognize : recognize sig tokens = some program) :
    rpnTokens program = tokens :=
  recognize_eq_some_rpnTokens hrecognize

/-! ## Authenticated higher-order child roles -/

/-- Flat node metadata consumed by the graph adapter, in postfix node order. -/
structure RoleRecord where
  opId : Nat
  arity : Nat
  higherOrderArity : Nat
  childRoles : List ChildRole
  deriving DecidableEq, Repr

/-- Role metadata is computed from the same table row as parser arity. -/
def roleRecord (sig : Signature σ) (id : Nat) : RoleRecord :=
  match entryAt sig id with
  | none =>
      { opId := id, arity := 0, higherOrderArity := 0, childRoles := [] }
  | some entry =>
      { opId := id
        arity := entry.arity
        higherOrderArity := entry.hoArity
        childRoles := childRoles entry }

/-- Every node contributes one independently table-derived role record. -/
def roleRecords (sig : Signature σ) : Prog → List RoleRecord
  | .node id children => (children.map (roleRecords sig)).flatten ++ [roleRecord sig id]

@[ext] structure ActionTrace where
  tokens : List Tok
  nodes : List RoleRecord
  deriving DecidableEq, Repr

def encodeTrace (sig : Signature σ) (program : Prog) : ActionTrace :=
  { tokens := rpnTokens program, nodes := roleRecords sig program }

/-- Parsing owns tree recovery; the role lane is checked independently against the table. -/
def decodeTrace (sig : Signature σ) (trace : ActionTrace) : Option Prog :=
  match recognize sig trace.tokens with
  | none => none
  | some program =>
      if roleRecords sig program = trace.nodes then some program else none

theorem roleRecord_of_entry {sig : Signature σ} {id : Nat} {entry : Entry σ}
    (hentry : entryAt sig id = some entry) :
    roleRecord sig id =
      { opId := id
        arity := entry.arity
        higherOrderArity := entry.hoArity
        childRoles := childRoles entry } := by
  simp [roleRecord, hentry]

/-- Every serialized role bit is `code` exactly in the leading `hoArity` positions. -/
theorem roleRecord_childRole_iff {sig : Signature σ} {id index : Nat}
    {entry : Entry σ} (hentry : entryAt sig id = some entry)
    (hindex : index < (roleRecord sig id).childRoles.length) :
    (roleRecord sig id).childRoles[index] = ChildRole.code ↔ index < entry.hoArity := by
  simp only [roleRecord, hentry] at hindex ⊢
  simp only [childRoles_getElem entry index hindex]
  by_cases hcode : index < entry.hoArity <;> simp [hcode]

/-- T3 full-trace forward round trip, including all table-derived child roles. -/
theorem decode_encodeTrace {sig : Signature σ} {program : Prog}
    (hwellFormed : WellFormed sig program) :
    decodeTrace sig (encodeTrace sig program) = some program := by
  simp [decodeTrace, encodeTrace, parse_emit_roundTrip hwellFormed]

/-- T3 full-trace reverse round trip: accepted traces have canonical tokens and roles. -/
theorem encode_decodeTrace {sig : Signature σ} {trace : ActionTrace} {program : Prog}
    (hdecode : decodeTrace sig trace = some program) :
    encodeTrace sig program = trace := by
  unfold decodeTrace at hdecode
  cases hrecognize : recognize sig trace.tokens with
  | none => simp [hrecognize] at hdecode
  | some parsed =>
      rw [hrecognize] at hdecode
      change
        (if roleRecords sig parsed = trace.nodes then some parsed else none) =
          some program at hdecode
      by_cases hroles : roleRecords sig parsed = trace.nodes
      · rw [if_pos hroles] at hdecode
        simp only [Option.some.injEq] at hdecode
        subst parsed
        apply ActionTrace.ext
        · exact emit_parse_roundTrip hrecognize
        · exact hroles
      · rw [if_neg hroles] at hdecode
        contradiction

/-! ## Higher-order and stateful positive/negative fixtures -/

def roleRichProgram : Prog :=
  .node 13
    [ .node 9 [.node 10 [], .node 1 [], .node 0 []]
    , .node 12 [.node 10 [], .node 11 []]
    , .node 15 [.node 14 [.node 10 [], .node 1 []]]
    , .node 10 []
    , .node 11 []
    ]

theorem roleRichProgram_wellFormed : WellFormed orgMemoSignature roleRichProgram := by
  apply recognize_sound (toks := rpnTokens roleRichProgram)
  simp [roleRichProgram, rpnTokens, recognize, recognizeRaw, recognizeRawStack,
    recognizeRawStep, orgMemoSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
    entry, entryAt, listGet?, popN]

example : (roleRecord orgMemoSignature 9).childRoles =
    [.code, .value, .value] := by decide

example : (roleRecord orgMemoSignature 12).childRoles =
    [.code, .value] := by decide

example : (roleRecord orgMemoSignature 13).childRoles =
    [.code, .code, .value, .value, .value] := by decide

example : (roleRecord orgMemoSignature 14).childRoles =
    [.value, .value] := by decide

example : (roleRecord orgMemoSignature 15).childRoles = [.value] := by decide

example : decodeTrace orgMemoSignature (encodeTrace orgMemoSignature roleRichProgram) =
    some roleRichProgram :=
  decode_encodeTrace roleRichProgram_wellFormed

/-- Swapping the two distinct higher-order roles corrupts the authenticated trace. -/
example :
    decodeTrace orgMemoSignature
      { tokens := [10, 11, 12]
        nodes :=
          [ roleRecord orgMemoSignature 10
          , roleRecord orgMemoSignature 11
          , { (roleRecord orgMemoSignature 12) with
                childRoles := [.value, .code] }
          ] } = none := by
  simp [decodeTrace, recognize, recognizeRaw, recognizeRawStack, recognizeRawStep,
    roleRecords, roleRecord, orgMemoSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.listOps,
    entry, entryAt, listGet?, popN, childRoles]
  decide

end Mettapedia.GSLT.LanguageDef.GauthierSkeletonTrace
