/-
# Role-aware alignment at an authenticated postfix decoder prefix

The parser forest is recovered with the established raw recognizer and related
back to the exact bounded decoder.  Historical programs are replayed at every
proper prefix.  A reference contributes its following action only after that
action passes the current `legalTokens` mask.

The alignment score is syntactic specificity of the role-indexed LGG.  Ties
are resolved by the earliest prefix in the canonical postfix stream.  This is
an evidence-ranking layer only: it never changes checker-owned legal support.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.RoleIndexedAntiUnification
import Mettapedia.GSLT.LanguageDef.Gauthier.SkeletonMask

namespace Mettapedia.GSLT.LanguageDef.GauthierPartialPostfixAlignment

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification

universe u

/-- A natural-token prefix that actually reached the exact bounded decoder
state from the initial state. -/
structure AcceptedPrefix (sig : Signature σ) (maxLen : Nat) where
  tokens : List Nat
  state : MaskState
  run_eq : run sig (tokens.map Int.ofNat) (initial maxLen) = some state

/-- Recover the well-formed parser forest represented by a postfix prefix. -/
def prefixForest? (sig : Signature σ) (tokens : List Nat) : Option (List Prog) :=
  recognizeRawStack sig tokens []

/-- Every decoder-accepted natural prefix has a parser forest. -/
theorem acceptedPrefix_has_forest (accepted : AcceptedPrefix sig maxLen) :
    ∃ forest, prefixForest? sig accepted.tokens = some forest := by
  rcases run_ofNat_maskStack_sync sig accepted.tokens (initial maxLen) accepted.state
      accepted.run_eq with ⟨maskForest, hmask, _⟩
  have hmaskEmpty : maskStack? sig accepted.tokens [] = some maskForest := by
    simpa [initial] using hmask
  have hlock := rawStack_maskStack_correct sig accepted.tokens [] [] rfl
  cases hraw : recognizeRawStack sig accepted.tokens [] with
  | none => simp [hraw, hmaskEmpty] at hlock
  | some forest => exact ⟨forest, hraw⟩

/-- Every recovered prefix-forest component is a well-formed program. -/
theorem prefixForest_wellFormed {sig : Signature σ} {tokens : List Nat}
    {forest : List Prog} (hforest : prefixForest? sig tokens = some forest) :
    ∀ program ∈ forest, WellFormed sig program := by
  exact recognizeRawStack_sound (sig := sig)
    (by intro program hmem; cases hmem) hforest

/-- One authenticated historical reference.  The ordinal is a stable
provenance order used after specificity to break ties deterministically. -/
structure AuthenticatedReference (sig : Signature σ) (maxLen : Nat) where
  sourceOrdinal : Nat
  program : Prog
  wellFormed : WellFormed sig program
  withinBudget : (rpnTokens program).length ≤ maxLen

/-- One proper prefix and its following operator token. -/
structure ReferenceEvent where
  sourceOrdinal : Nat
  prefixOrdinal : Nat
  tokensBefore : List Nat
  action : Nat
  deriving DecidableEq, Repr

def referenceEventsAux (sourceOrdinal prefixOrdinal : Nat) :
    List Nat → List Nat → List ReferenceEvent
  | _, [] => []
  | before, action :: after =>
      { sourceOrdinal, prefixOrdinal, tokensBefore := before, action } ::
        referenceEventsAux sourceOrdinal (prefixOrdinal + 1)
          (before ++ [action]) after

/-- Canonical proper-prefix enumeration of a reference program. -/
def referenceEvents (reference : AuthenticatedReference sig maxLen) :
    List ReferenceEvent :=
  referenceEventsAux reference.sourceOrdinal 0 []
    (rpnTokens reference.program)

/-- Every operator of a reference program is legal at its own authenticated
prefix.  This is exactly the established prefix-completeness theorem. -/
theorem referenceEvent_legal_at_own_prefix
    (reference : AuthenticatedReference sig maxLen)
    {before : List Int} {token : Int} {after : List Int}
    (hsplit : (rpnTokens reference.program).map Int.ofNat =
      before ++ token :: after) :
    ∃ prefixState,
      run sig before (initial maxLen) = some prefixState ∧
      token ∈ legalTokens sig prefixState := by
  exact rpnTokens_every_prefix_legal reference.wellFormed
    reference.withinBudget before token after hsplit

mutual

/-- Number of retained ranked constructors in an anti-unification pattern. -/
def patternSpecificity : Pattern → Nat
  | .hole _ => 0
  | .node _ children => 1 + patternListSpecificity children

def patternListSpecificity : List Pattern → Nat
  | [] => 0
  | head :: tail => patternSpecificity head + patternListSpecificity tail

end

/-- One tree coordinate exposed by an alignment.  `exact = false` marks an LGG
hole; its role is still part of the coordinate. -/
structure AlignmentCoordinate where
  forestIndex : Nat
  path : List Nat
  role : HoleRole
  exact : Bool
  deriving DecidableEq, Repr

mutual

def patternCoordinates (sig : Signature σ) (forestIndex : Nat) :
    Nat → HoleRole → List Nat → Pattern → List AlignmentCoordinate
  | _, role, path, .hole _ =>
      [{ forestIndex, path, role, exact := false }]
  | index, role, path, .node op children =>
      { forestIndex, path, role, exact := true } ::
        patternChildrenCoordinates sig forestIndex op index path 0 children

def patternChildrenCoordinates (sig : Signature σ) (forestIndex parentOp index : Nat)
    (path : List Nat) : Nat → List Pattern → List AlignmentCoordinate
  | _, [] => []
  | childIndex, head :: tail =>
      patternCoordinates sig forestIndex index
          (childHoleRoleAt sig parentOp childIndex) (path ++ [childIndex]) head ++
        patternChildrenCoordinates sig forestIndex parentOp index path
          (childIndex + 1) tail

end

/-- Alignment of two equal-depth parser forests. -/
structure ForestAlignment where
  patterns : List Pattern
  score : Nat
  coordinates : List AlignmentCoordinate
  deriving DecidableEq, Repr

def alignForestsFrom (sig : Signature σ) : Nat → List Prog → List Prog →
    Option ForestAlignment
  | _, [], [] => some { patterns := [], score := 0, coordinates := [] }
  | index, current :: currents, reference :: references =>
      match alignForestsFrom sig (index + 1) currents references with
      | none => none
      | some rest =>
          let pattern := lgg sig .root current reference
          some
            { patterns := pattern :: rest.patterns
              score := patternSpecificity pattern + rest.score
              coordinates :=
                patternCoordinates sig index 0 .root [] pattern ++ rest.coordinates }
  | _, _, _ => none

def alignForests (sig : Signature σ) (current reference : List Prog) :
    Option ForestAlignment :=
  alignForestsFrom sig 0 current reference

theorem alignForests_some_lengths_eq {sig : Signature σ} {current reference}
    {alignment : ForestAlignment}
    (halign : alignForests sig current reference = some alignment) :
    current.length = reference.length := by
  unfold alignForests at halign
  generalize hindex : (0 : Nat) = index at halign
  clear hindex
  induction current generalizing index reference alignment with
  | nil =>
      cases reference <;> simp [alignForestsFrom] at halign ⊢
  | cons head tail ih =>
      cases reference with
      | nil => simp [alignForestsFrom] at halign
      | cons reference references =>
          simp only [alignForestsFrom] at halign
          cases hrest : alignForestsFrom sig (index + 1) tail references with
          | none => simp [hrest] at halign
          | some rest =>
              simp only [hrest, Option.some.injEq] at halign
              have htail := ih (index := index + 1) (reference := references)
                (alignment := rest) hrest
              simp [htail]

/-- A legal action supported by one aligned reference prefix. -/
structure ActionCandidate where
  sourceOrdinal : Nat
  prefixOrdinal : Nat
  referencePrefix : List Nat
  action : PyToken
  alignment : ForestAlignment
  deriving DecidableEq, Repr

/-- Construct an action candidate, failing closed on parse failure, forest-depth
mismatch, or checker-mask rejection. -/
def candidateForEvent (sig : Signature σ) (currentForest : List Prog)
    (currentState : MaskState) (event : ReferenceEvent) : Option ActionCandidate :=
  match prefixForest? sig event.tokensBefore with
  | none => none
  | some referenceForest =>
      match alignForests sig currentForest referenceForest with
      | none => none
      | some alignment =>
          let action : PyToken := Int.ofNat event.action
          if action ∈ legalTokens sig currentState then
            some
              { sourceOrdinal := event.sourceOrdinal
                prefixOrdinal := event.prefixOrdinal
                referencePrefix := event.tokensBefore
                action
                alignment }
          else none

/-- Candidates for one historical reference, in canonical prefix order. -/
def candidatesForReference (sig : Signature σ) (currentForest : List Prog)
    (currentState : MaskState) (reference : AuthenticatedReference sig maxLen) :
    List ActionCandidate :=
  (referenceEvents reference).filterMap
    (candidateForEvent sig currentForest currentState)

/-- `List.argmax` returns the first maximal element, so canonical reference
prefix order is the explicit deterministic tie-break. -/
def chooseMostSpecific (candidates : List ActionCandidate) : Option ActionCandidate :=
  candidates.argmax fun candidate => candidate.alignment.score

theorem chooseMostSpecific_mem {candidates : List ActionCandidate}
    {chosen : ActionCandidate}
    (hchoose : chooseMostSpecific candidates = some chosen) :
    chosen ∈ candidates := by
  unfold chooseMostSpecific at hchoose
  have hoption : chosen ∈ candidates.argmax
      (fun candidate : ActionCandidate => candidate.alignment.score) := by
    rw [hchoose]
    simp
  exact List.argmax_mem hoption

/-- The selected alignment has maximal syntactic specificity; equal scores keep
the earliest canonical prefix. -/
theorem chooseMostSpecific_maximal {candidates : List ActionCandidate}
    {chosen candidate : ActionCandidate}
    (hchoose : chooseMostSpecific candidates = some chosen)
    (hmem : candidate ∈ candidates) :
    candidate.alignment.score ≤ chosen.alignment.score := by
  unfold chooseMostSpecific at hchoose
  apply List.le_of_mem_argmax hmem
  rw [hchoose]
  simp

/-- One most-specific legal alignment per authenticated reference. -/
def transferredCandidates (sig : Signature σ) (currentForest : List Prog)
    (currentState : MaskState)
    (references : List (AuthenticatedReference sig maxLen)) :
    List ActionCandidate :=
  references.filterMap fun reference =>
    chooseMostSpecific (candidatesForReference sig currentForest currentState reference)

theorem candidateForEvent_action_legal {sig : Signature σ}
    {currentForest : List Prog} {currentState : MaskState}
    {event : ReferenceEvent} {candidate : ActionCandidate}
    (hcandidate : candidateForEvent sig currentForest currentState event =
      some candidate) :
    candidate.action ∈ legalTokens sig currentState := by
  unfold candidateForEvent at hcandidate
  cases hforest : prefixForest? sig event.tokensBefore with
  | none => simp [hforest] at hcandidate
  | some referenceForest =>
      simp only [hforest] at hcandidate
      cases halign : alignForests sig currentForest referenceForest with
      | none => simp [halign] at hcandidate
      | some alignment =>
          simp only [halign] at hcandidate
          split at hcandidate
          next hlegal =>
            simp only [Option.some.injEq] at hcandidate
            subst candidate
            exact hlegal
          next hnot => simp at hcandidate

theorem mem_candidatesForReference_action_legal {sig : Signature σ}
    {currentForest : List Prog} {currentState : MaskState}
    {reference : AuthenticatedReference sig maxLen}
    {candidate : ActionCandidate}
    (hmem : candidate ∈
      candidatesForReference sig currentForest currentState reference) :
    candidate.action ∈ legalTokens sig currentState := by
  simp only [candidatesForReference, List.mem_filterMap] at hmem
  rcases hmem with ⟨event, _hevent, hcandidate⟩
  exact candidateForEvent_action_legal hcandidate

/-- Alignment may reorder the checker-owned legal actions, but cannot add
support outside them. -/
theorem mem_transferredCandidates_action_legal {sig : Signature σ}
    {currentForest : List Prog} {currentState : MaskState}
    {references : List (AuthenticatedReference sig maxLen)}
    {candidate : ActionCandidate}
    (hmem : candidate ∈
      transferredCandidates sig currentForest currentState references) :
    candidate.action ∈ legalTokens sig currentState := by
  simp only [transferredCandidates, List.mem_filterMap] at hmem
  rcases hmem with ⟨reference, _href, hchosen⟩
  apply mem_candidatesForReference_action_legal
  exact chooseMostSpecific_mem hchosen

/-- An illegal (including over-budget) action receives no transferable
alignment evidence. -/
theorem illegal_action_not_transferred {sig : Signature σ}
    {currentForest : List Prog} {currentState : MaskState}
    {references : List (AuthenticatedReference sig maxLen)} {action : PyToken}
    (hillegal : action ∉ legalTokens sig currentState) :
    ∀ candidate ∈ transferredCandidates sig currentForest currentState references,
      candidate.action ≠ action := by
  intro candidate hcandidate heq
  subst action
  exact hillegal (mem_transferredCandidates_action_legal hcandidate)

/-! ## Executable positive and negative fixtures -/

def addZeroOne : Prog := .node 3 [.node 0 [], .node 1 []]

def addZeroOneReference : AuthenticatedReference orgMemoSignature 8 :=
  { sourceOrdinal := 0
    program := addZeroOne
    wellFormed := by
      unfold addZeroOne
      apply WellFormed.node (e := entry "addi" 2 0
        Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.addi)
      · rfl
      · rfl
      · intro child hchild
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl
        · exact WellFormed.node (e := entry "zero" 0 0
            Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.zero) rfl rfl
            (by intro program hmem; cases hmem)
        · exact WellFormed.node (e := entry "one" 0 0
            Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.one) rfl rfl
            (by intro program hmem; cases hmem)
    withinBudget := by norm_num [addZeroOne, rpnTokens] }

theorem exact_reference_actions_are_own_prefix_legal :
    ∀ before token after,
      (rpnTokens addZeroOne).map Int.ofNat = before ++ token :: after →
      ∃ state, run orgMemoSignature before (initial 8) = some state ∧
        token ∈ legalTokens orgMemoSignature state := by
  exact rpnTokens_every_prefix_legal addZeroOneReference.wellFormed
    addZeroOneReference.withinBudget

def illegalEvent : ReferenceEvent :=
  { sourceOrdinal := 7, prefixOrdinal := 0, tokensBefore := [], action := 15 }

theorem illegal_fixture_rejected :
    candidateForEvent orgMemoSignature [] (initial 8) illegalEvent = none := by
  have hillegal : (Int.ofNat 15 : PyToken) ∉
      legalTokens orgMemoSignature (initial 8) := by
    rw [ofNat_mem_legalTokens_iff]
    have hop : opLegal orgMemoSignature (initial 8) 15 = false := by rfl
    simp [hop]
  simp only [candidateForEvent, illegalEvent, prefixForest?,
    recognizeRawStack.eq_def, alignForests, alignForestsFrom, hillegal, if_false]

#print axioms acceptedPrefix_has_forest
#print axioms prefixForest_wellFormed
#print axioms referenceEvent_legal_at_own_prefix
#print axioms alignForests_some_lengths_eq
#print axioms chooseMostSpecific_mem
#print axioms chooseMostSpecific_maximal
#print axioms mem_transferredCandidates_action_legal
#print axioms illegal_action_not_transferred
#print axioms exact_reference_actions_are_own_prefix_legal
#print axioms illegal_fixture_rejected

end Mettapedia.GSLT.LanguageDef.GauthierPartialPostfixAlignment
