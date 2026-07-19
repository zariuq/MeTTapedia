/-
# Atomic refinement view of the sealed Gauthier postfix machine

Gauthier has one continuation hole.  Refining it with an operator token is the
sealed mask step itself.  EOS is not an atomic action: completion is observed
by the existing depth-one terminal predicate.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.AtomicRefinement
import Mettapedia.GSLT.LanguageDef.Gauthier.RefinementInstance

namespace Mettapedia.GSLT.LanguageDef.GauthierAtomicRefinement

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierRefinement

abbrev AtomicAction := RefineAction StreamHole PyToken

/-- Checker transition with terminality removed from the action vocabulary. -/
def refine? (state : MaskState) (_hole : StreamHole) (head : PyToken) :
    Option MaskState :=
  if postfixTerminal state then none
  else if head = eos then none
  else step? orgMemoSignature state head

def legalHeads (state : MaskState) (_hole : StreamHole) : List PyToken :=
  (legalTokens orgMemoSignature state).filter fun head => head != eos

def decode (trace : List AtomicAction) : Option Prog :=
  decodeOperatorTrace (trace.map fun action => action.head)

def encode (program : Prog) : List AtomicAction :=
  ((rpnTokens program).map Int.ofNat).map fun head =>
    ⟨StreamHole.continuation, head⟩

/-- Atomic wrapper around the sealed org.memo root. -/
def orgMemoAtomicRoot : AtomicRoot where
  State := MaskState
  Hole := StreamHole
  Head := PyToken
  Program := Prog
  initial := initial
  holes := fun state =>
    if postfixTerminal state then [] else [.continuation]
  legalHeads := legalHeads
  refine? := refine?
  terminal := postfixTerminal
  decode := decode
  wellFormed := WellFormed orgMemoSignature
  programCost := fun program => (rpnTokens program).length
  encode := encode
  invariant := Viable orgMemoSignature
  canComplete := Viable orgMemoSignature
  budgetOK := fun budget => 1 ≤ budget

/-- The sealed serialized operator vocabulary has no duplicate tokens. -/
theorem orgMemo_legalTokens_nodup (state : MaskState) :
    (legalTokens orgMemoSignature state).Nodup := by
  have hops :
      (((operatorIds orgMemoSignature).filter
          (opLegal orgMemoSignature state)).map Int.ofNat).Nodup := by
    have hids : (operatorIds orgMemoSignature).Nodup := by
      unfold operatorIds
      exact List.nodup_range
    exact (hids.filter _).map Int.ofNat_injective
  by_cases hterminal : state.depth = 1 ∧ state.tokensEmitted ≤ state.maxLen
  · unfold legalTokens
    rw [if_pos hterminal]
    apply List.Nodup.append (by simp) hops
    rw [List.disjoint_left]
    intro token htoken hmem
    rw [List.mem_singleton] at htoken
    subst token
    rcases List.mem_map.mp hmem with ⟨id, _hid, heq⟩
    exact ofNat_ne_eos id heq
  · unfold legalTokens
    rw [if_neg hterminal]
    exact hops

/-- Gauthier exposes either the unique continuation hole or no hole. -/
theorem orgMemoAtomicRoot_holes_nodup (state : MaskState) :
    (orgMemoAtomicRoot.holes state).Nodup := by
  by_cases hterminal : postfixTerminal state <;>
    simp [orgMemoAtomicRoot, hterminal]

/-- Removing EOS from duplicate-free sealed support preserves uniqueness. -/
theorem legalHeads_nodup (state : MaskState) (hole : StreamHole) :
    (legalHeads state hole).Nodup := by
  exact (orgMemo_legalTokens_nodup state).filter _

/-- The concrete Gauthier legal-action enumeration is a genuine partition. -/
theorem orgMemoAtomicRoot_legalActions_nodup (state : MaskState) :
    (orgMemoAtomicRoot.legalActions state).Nodup := by
  apply orgMemoAtomicRoot.legalActions_nodup state
  · exact orgMemoAtomicRoot_holes_nodup state
  · intro hole
    exact legalHeads_nodup state hole

/-- Away from terminality and EOS, atomic refinement is definitionally sealed. -/
theorem refine_eq_sealed {state : MaskState} {head : PyToken}
    (hnonterminal : ¬ postfixTerminal state) (hne : head ≠ eos) :
    refine? state .continuation head = step? orgMemoSignature state head := by
  simp [refine?, hnonterminal, hne]

/-- The atomic transition is absent exactly at the two removed action cases. -/
theorem refine_eq_none_of_terminal_or_eos {state : MaskState} {head : PyToken}
    (hremoved : postfixTerminal state ∨ head = eos) :
    refine? state .continuation head = none := by
  rcases hremoved with hterminal | heos
  · simp [refine?, hterminal]
  · subst head
    simp [refine?]

/-- Factored atomic support is the sealed operator support minus EOS at nonterminals. -/
theorem legal_iff_sealed_nonterminal (state : MaskState) (head : PyToken) :
    (orgMemoAtomicRoot.asRefinementInterface).legal state
        ⟨.continuation, head⟩ ↔
      ¬ postfixTerminal state ∧ head ≠ eos ∧
        head ∈ legalTokens orgMemoSignature state := by
  simp only [AtomicRoot.asRefinementInterface, orgMemoAtomicRoot]
  by_cases hterminal : postfixTerminal state
  · simp [hterminal]
  · simp [legalHeads, hterminal, and_comm]

/-- Successful atomic application is exactly the factored legal support. -/
theorem exists_refine_iff_legal (state : MaskState) (head : PyToken) :
    (∃ next, refine? state .continuation head = some next) ↔
      (orgMemoAtomicRoot.asRefinementInterface).legal state
        ⟨.continuation, head⟩ := by
  rw [legal_iff_sealed_nonterminal]
  constructor
  · rintro ⟨next, hrefine⟩
    by_cases hterminal : postfixTerminal state
    · simp [refine?, hterminal] at hrefine
    · by_cases hne : head = eos
      · subst head
        simp [refine?, hterminal] at hrefine
      · refine ⟨hterminal, hne, ?_⟩
        have hstep : step? orgMemoSignature state head = some next := by
          simpa [refine?, hterminal, hne] using hrefine
        exact mem_legalTokens_of_step?_some hstep
  · rintro ⟨hnonterminal, hne, hmem⟩
    rcases (exists_step_iff_mem state head).mpr hmem with ⟨next, hstep⟩
    exact ⟨next, by simpa [refine?, hnonterminal, hne] using hstep⟩

/-- Compatibility restatement: the wrapper decoder is the sealed decoder. -/
theorem decode_eq_sealed (trace : List AtomicAction) :
    decode trace = decodeOperatorTrace (trace.map fun action => action.head) := by
  rfl

/-- Compatibility restatement: the wrapper encoder recovers the sealed stream. -/
theorem encode_heads_eq_sealed (program : Prog) :
    (encode program).map (fun action => action.head) =
      (rpnTokens program).map Int.ofNat := by
  simp [encode]

/-- Every successful atomic run is the same run of the sealed machine. -/
theorem run_eq_sealed_of_atomic_run {trace : List AtomicAction}
    {state finalState : MaskState}
    (hrun : orgMemoAtomicRoot.asRefinementInterface.run trace state =
      some finalState) :
    orgMemoRoot.run (trace.map fun action => action.head) state = some finalState := by
  induction trace generalizing state finalState with
  | nil =>
      have heq : state = finalState := Option.some.inj hrun
      subst finalState
      rfl
  | cons action rest ih =>
      simp only [RefinementInterface.run, AtomicRoot.asRefinementInterface,
        orgMemoAtomicRoot] at hrun
      cases hrefine : refine? state action.hole action.head with
      | none => simp [hrefine] at hrun
      | some next =>
          rw [hrefine] at hrun
          have hnonterminal : ¬ postfixTerminal state := by
            intro hterminal
            simp [refine?, hterminal] at hrefine
          have hne : action.head ≠ eos := by
            intro heos
            rw [heos] at hrefine
            simp [refine?, hnonterminal] at hrefine
          have hsealed :
              step? orgMemoSignature state action.head = some next := by
            simpa [refine?, hnonterminal, hne] using hrefine
          simp only [List.map_cons, RefinementInterface.run, orgMemoRoot, hsealed]
          exact ih hrun

/-- T2 crown: the Gauthier atomic layer removes only EOS-as-action. -/
theorem gauthier_atomic_collapse :
    (∀ state head,
      ¬ postfixTerminal state → head ≠ eos →
        refine? state .continuation head = step? orgMemoSignature state head) ∧
    (∀ state, orgMemoAtomicRoot.terminal state ↔ postfixTerminal state) ∧
    (∀ program,
      (orgMemoAtomicRoot.encode program).map (fun action => action.head) =
        orgMemoRoot.encode program) := by
  exact ⟨fun _ _ => refine_eq_sealed, fun _ => Iff.rfl,
    fun program => encode_heads_eq_sealed program⟩

#print axioms exists_refine_iff_legal
#print axioms orgMemoAtomicRoot_legalActions_nodup
#print axioms run_eq_sealed_of_atomic_run
#print axioms gauthier_atomic_collapse

end Mettapedia.GSLT.LanguageDef.GauthierAtomicRefinement
