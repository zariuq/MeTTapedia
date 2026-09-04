import Mathlib.Data.List.Basic

/-!
# Source authority for the mainline PeTTa call guard

This module records the updateable source coordinate and the exact source
spans modeled by the closed call-guard formalization.  The public upstream
coordinate is review ref `refs/pull/219/head`; the qualification branch is
retained on the project fork under the name below.  Both currently name the
same selected commit.

The table is navigational evidence, not a semantic axiom.  Behavioral evidence
comes from the cross-runtime fixture gate, while the Lean development proves
the internal semantic and operational correspondences.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardReferenceAuthority

set_option autoImplicit false

def upstreamRepository : String := "trueagi-io/PeTTa"
def upstreamReviewRef : String := "refs/pull/219/head"
def qualificationRepository : String := "zariuq/PeTTa"
def qualificationBranch : String := "fix/minimal-space-owned-eval-20260827"
def selectedCommit : String :=
  "91c27146b129f4d54776362ddb58898568f4665f"
def coherenceCommit : String :=
  "9c036a506b7c2bf14b26d7034f95add5e371d4ce"

/-- One separately auditable responsibility of the selected Prolog source. -/
inductive ClauseId where
  | defaultTypeQuery
  | ownedTypeQuery
  | metatypeQuery
  | softCutGuard
  | typeChainRouting
  | typeChainOrder
  | typedBranchDispatch
  | branchDisjunctionOrder
  | inputModeTranslation
  | loadPredeclaration
  | compiledClauseCurrentness
  | typeRevisionRecompilation
  | spaceMutationOwnership
deriving DecidableEq, Repr

/-- An inclusive line interval in one file at `selectedCommit`. -/
structure ClauseReference where
  id : ClauseId
  file : String
  firstLine : Nat
  lastLine : Nat
  subject : String
deriving DecidableEq, Repr

def ClauseReference.wellFormed (reference : ClauseReference) : Bool :=
  decide (0 < reference.firstLine ∧ reference.firstLine ≤ reference.lastLine)

/-- Exact clause ledger for the closed call-guard authority. -/
def clauseTable : List ClauseReference := [
  { id := .defaultTypeQuery
    file := "src/metta.pl"
    firstLine := 181
    lastLine := 196
    subject := "default-space get-type candidates and fallback" },
  { id := .ownedTypeQuery
    file := "src/metta.pl"
    firstLine := 198
    lastLine := 215
    subject := "space-owned get-type candidates and function typing" },
  { id := .metatypeQuery
    file := "src/metta.pl"
    firstLine := 216
    lastLine := 223
    subject := "ordered structural get-metatype clauses" },
  { id := .softCutGuard
    file := "src/translator.pl"
    firstLine := 94
    lastLine := 98
    subject := "exact type before metatype soft cut" },
  { id := .typeChainRouting
    file := "src/translator.pl"
    firstLine := 100
    lastLine := 102
    subject := "compiled predicate to owning-space type-chain routing" },
  { id := .typeChainOrder
    file := "src/translator.pl"
    firstLine := 145
    lastLine := 168
    subject := "ordered type-chain collection and stable variant deduplication" },
  { id := .typedBranchDispatch
    file := "src/translator.pl"
    firstLine := 650
    lastLine := 704
    subject := "typed overload branch generation and output guarding" },
  { id := .branchDisjunctionOrder
    file := "src/translator.pl"
    firstLine := 762
    lastLine := 763
    subject := "source-order-preserving branch disjunction" },
  { id := .inputModeTranslation
    file := "src/translator.pl"
    firstLine := 707
    lastLine := 717
    subject := "raw, evaluated-unchecked, and evaluated-checked inputs" },
  { id := .loadPredeclaration
    file := "src/filereader.pl"
    firstLine := 13
    lastLine := 55
    subject := "predeclaration and ordered two-pass loading" },
  { id := .compiledClauseCurrentness
    file := "src/translator.pl"
    firstLine := 170
    lastLine := 178
    subject := "live compiled clauses as source-definition authority" },
  { id := .typeRevisionRecompilation
    file := "src/translator.pl"
    firstLine := 233
    lastLine := 313
    subject := "transactional dependent recompilation after type revision" },
  { id := .spaceMutationOwnership
    file := "src/spaces.pl"
    firstLine := 9
    lastLine := 57
    subject := "space-owned type and function addition and removal" }
]

def allClauseIds : List ClauseId := [
  .defaultTypeQuery,
  .ownedTypeQuery,
  .metatypeQuery,
  .softCutGuard,
  .typeChainRouting,
  .typeChainOrder,
  .typedBranchDispatch,
  .branchDisjunctionOrder,
  .inputModeTranslation,
  .loadPredeclaration,
  .compiledClauseCurrentness,
  .typeRevisionRecompilation,
  .spaceMutationOwnership
]

/-- Boolean admission check used by authority-roll tooling. -/
def tableCovers (table : List ClauseReference) : Bool :=
  allClauseIds.all fun id => table.any fun reference => reference.id == id

def tableSpansWellFormed (table : List ClauseReference) : Bool :=
  table.all ClauseReference.wellFormed

theorem clauseTable_ids_nodup :
    (clauseTable.map ClauseReference.id).Nodup := by
  decide

theorem clauseTable_covers : tableCovers clauseTable = true := by
  decide

theorem clauseTable_spans_wellFormed :
    tableSpansWellFormed clauseTable = true := by
  decide

/-! ## Negative authority control -/

def withoutSoftCut : List ClauseReference :=
  clauseTable.filter fun reference => reference.id != .softCutGuard

/-- A ledger that omits the operational soft-cut clause is not admissible. -/
theorem withoutSoftCut_not_covers : tableCovers withoutSoftCut = false := by
  decide

#print axioms clauseTable_ids_nodup
#print axioms clauseTable_covers
#print axioms clauseTable_spans_wellFormed
#print axioms withoutSoftCut_not_covers

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardReferenceAuthority
