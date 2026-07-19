/-
# The Gauthier postfix root as a refinement-action interface

This module does not introduce a second Gauthier machine.  It packages the
sealed `SkeletonMask` state, legal-token set, step function, recognizer, and
bounded viability predicate behind the root-parametric refinement interface.
The equivalence theorems at the end expose that delegation explicitly.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.RefinementInterface
import Mettapedia.GSLT.LanguageDef.Gauthier.SkeletonTrace

namespace Mettapedia.GSLT.LanguageDef.GauthierRefinement

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonTrace
open Mettapedia.GSLT.LanguageDef.RefinementInterface

/-- A postfix decoder exposes one continuation site until its stack is complete. -/
inductive StreamHole where
  | continuation
  deriving DecidableEq, Repr

/-- Executable check that every Python integer token is an operator id. -/
def nonnegativeTokens (tokens : List PyToken) : Bool :=
  tokens.all fun token => decide (0 ≤ token)

/-- Decode the exact operator-token serialization used by `SkeletonMask`. -/
def decodeOperatorTrace (tokens : List PyToken) : Option Prog :=
  if nonnegativeTokens tokens then
    recognize orgMemoSignature (tokens.map Int.toNat)
  else
    none

/-- A completed bounded postfix stack is the unique terminal shape. -/
def postfixTerminal (state : MaskState) : Prop :=
  state.depth = 1 ∧ state.tokensEmitted ≤ state.maxLen

instance postfixTerminalDecidable (state : MaskState) :
    Decidable (postfixTerminal state) := by
  unfold postfixTerminal
  infer_instance

/-- The concrete E2/org.memo root; all operational fields delegate to sealed code. -/
abbrev orgMemoRoot : RefinementInterface where
  State := MaskState
  Hole := StreamHole
  Action := PyToken
  Program := Prog
  initial := initial
  holes := fun state =>
    if postfixTerminal state then [] else [.continuation]
  legal := fun state token => token ∈ legalTokens orgMemoSignature state
  apply? := step? orgMemoSignature
  terminal := postfixTerminal
  decode := decodeOperatorTrace
  wellFormed := WellFormed orgMemoSignature
  programCost := fun program => (rpnTokens program).length
  encode := fun program => (rpnTokens program).map Int.ofNat
  invariant := Viable orgMemoSignature
  canComplete := Viable orgMemoSignature
  budgetOK := fun budget => 1 ≤ budget

theorem nonnegativeTokens_map_ofNat (ids : List Nat) :
    nonnegativeTokens (ids.map Int.ofNat) = true := by
  simp [nonnegativeTokens]

theorem map_toNat_map_ofNat (ids : List Nat) :
    (ids.map Int.ofNat).map Int.toNat = ids := by
  induction ids with
  | nil => rfl
  | cons id rest ih => simp [ih]

theorem decodeOperatorTrace_encode {program : Prog}
    (hwellFormed : WellFormed orgMemoSignature program) :
    decodeOperatorTrace ((rpnTokens program).map Int.ofNat) = some program := by
  rw [decodeOperatorTrace, if_pos (nonnegativeTokens_map_ofNat _),
    map_toNat_map_ofNat]
  exact parse_emit_roundTrip hwellFormed

theorem canComplete_depth_one (remaining : Nat) :
    canComplete orgMemoSignature 1 remaining = true := by
  cases remaining <;> simp [canComplete]

/-- Membership in the sealed mask is exactly successful application. -/
theorem exists_step_iff_mem (state : MaskState) (token : PyToken) :
    (∃ next, step? orgMemoSignature state token = some next) ↔
      token ∈ legalTokens orgMemoSignature state := by
  constructor
  · rintro ⟨next, hstep⟩
    exact mem_legalTokens_of_step?_some hstep
  · intro hmem
    by_cases hterminator : token = eos
    · subst token
      exact ⟨state, by simp [step?, hmem]⟩
    · rcases mem_legalTokens_of_ne_eos hmem hterminator with
        ⟨id, htoken, _hid, hopLegal⟩
      subst token
      unfold opLegal at hopLegal
      by_cases htime : state.tokensEmitted < state.maxLen
      · rw [if_pos htime] at hopLegal
        cases hnext : nextDepth? orgMemoSignature id state.depth with
        | none => simp [hnext] at hopLegal
        | some nextDepth =>
            refine
              ⟨{ depth := nextDepth
                 tokensEmitted := state.tokensEmitted + 1
                 maxLen := state.maxLen }, ?_⟩
            unfold step?
            have htoNat : (Int.ofNat id).toNat = id := by simp
            rw [if_pos hmem, if_neg (ofNat_ne_eos id), htoNat, hnext]
      · simp [htime] at hopLegal

/-- Any successful sealed action already certifies viability of its source. -/
theorem viable_of_step {state next : MaskState} {token : PyToken}
    (hstep : step? orgMemoSignature state token = some next) :
    Viable orgMemoSignature state := by
  have hmem := mem_legalTokens_of_step?_some hstep
  by_cases hterminator : token = eos
  · subst token
    rcases (eos_mem_legalTokens_iff orgMemoSignature state).mp hmem with
      ⟨hdepth, hbudget⟩
    constructor
    · exact hbudget
    · rw [hdepth]
      exact canComplete_depth_one _
  · rcases mem_legalTokens_of_ne_eos hmem hterminator with
      ⟨id, htoken, hid, hopLegal⟩
    unfold opLegal at hopLegal
    by_cases htime : state.tokensEmitted < state.maxLen
    · rw [if_pos htime] at hopLegal
      cases hnext : nextDepth? orgMemoSignature id state.depth with
      | none => simp [hnext] at hopLegal
      | some nextDepth =>
          rw [hnext] at hopLegal
          constructor
          · omega
          · have hremaining :
                state.maxLen - state.tokensEmitted =
                  state.maxLen - (state.tokensEmitted + 1) + 1 := by
                omega
            rw [hremaining]
            simp only [canComplete, Bool.or_eq_true, beq_iff_eq]
            right
            simp only [List.any_eq_true]
            exact ⟨id, hid, by simp [hnext, hopLegal]⟩
    · simp [htime] at hopLegal

theorem viable_of_terminal {state : MaskState}
    (hterminal : postfixTerminal state) :
    Viable orgMemoSignature state := by
  rcases hterminal with ⟨hdepth, hbudget⟩
  constructor
  · exact hbudget
  · rw [hdepth]
    exact canComplete_depth_one _

/-- The generic runner is definitionally the sealed runner, exposed as a theorem. -/
theorem run_eq_sealed (tokens : List PyToken) (state : MaskState) :
    orgMemoRoot.run tokens state = run orgMemoSignature tokens state := by
  induction tokens generalizing state with
  | nil => rfl
  | cons token rest ih =>
      simp only [RefinementInterface.run, orgMemoRoot,
        GauthierSkeletonMask.run]
      cases hstep : step? orgMemoSignature state token with
      | none => rfl
      | some next => exact ih next

/-- Exact bounded completion: the interface adds no optimistic states. -/
theorem hasCompletion_iff_viable (state : MaskState) :
    orgMemoRoot.HasCompletion state ↔ Viable orgMemoSignature state := by
  constructor
  · rintro ⟨suffix, finalState, hrun, hterminal⟩
    cases suffix with
    | nil =>
        simp only [RefinementInterface.run, Option.some.injEq] at hrun
        subst finalState
        exact viable_of_terminal hterminal
    | cons token rest =>
        simp only [RefinementInterface.run, orgMemoRoot] at hrun
        cases hstep : step? orgMemoSignature state token with
        | none =>
            rw [hstep] at hrun
            contradiction
        | some next => exact viable_of_step hstep
  · intro hviable
    rcases viable_has_completion orgMemoSignature state hviable with
      ⟨suffix, finalState, _hstream, _hlength, hrun, hdepth, hbudget⟩
    exact
      ⟨suffix, finalState,
        (run_eq_sealed suffix state).trans hrun,
        ⟨hdepth, hbudget⟩⟩

/-- All generic obligations are discharged by sealed Gauthier theorems. -/
def orgMemoLaws : RefinementLaws orgMemoRoot where
  legal_iff_apply := by
    intro state token
    exact (exists_step_iff_mem state token).symm
  terminal_iff_holes_empty := by
    intro state
    simp [orgMemoRoot]
  initial_invariant := by
    intro budget hbudget
    exact orgMemo_initial_viable hbudget
  apply_invariant := by
    intro state token next hviable hstep
    exact step?_preserves_viable hviable hstep
  sound := by
    intro budget trace finalState program _hrun _hterminal hdecode
    change decodeOperatorTrace trace = some program at hdecode
    unfold decodeOperatorTrace at hdecode
    by_cases hnonnegative : nonnegativeTokens trace = true
    · rw [if_pos hnonnegative] at hdecode
      exact recognize_sound hdecode
    · rw [if_neg hnonnegative] at hdecode
      contradiction
  complete := by
    intro budget program hbudget hwellFormed hcost
    rcases rpnTokens_complete hwellFormed hcost with
      ⟨_hstream, _hnonempty, _hlength, finalState, hrun, hdepth⟩
    have hreachable : Reachable orgMemoSignature budget finalState :=
      ⟨(rpnTokens program).map Int.ofNat, hrun⟩
    have hviable := orgMemo_reachable_viable hbudget hreachable
    exact
      ⟨finalState,
        (run_eq_sealed _ _).trans hrun,
        ⟨hdepth, hviable.1⟩,
        decodeOperatorTrace_encode hwellFormed⟩
  invariant_canComplete := by
    intro state hviable
    exact hviable
  canComplete_iff_hasCompletion := by
    intro state
    exact (hasCompletion_iff_viable state).symm

/-! ## Explicit recovery and non-vacuity gates -/

theorem legal_iff_sealed (state : MaskState) (token : PyToken) :
    orgMemoRoot.legal state token ↔
      token ∈ legalTokens orgMemoSignature state := by
  rfl

theorem apply_eq_sealed (state : MaskState) (token : PyToken) :
    orgMemoRoot.apply? state token = step? orgMemoSignature state token := by
  rfl

theorem completion_iff_sealed_canComplete (state : MaskState) :
    orgMemoRoot.HasCompletion state ↔
      state.tokensEmitted ≤ state.maxLen ∧
        canComplete orgMemoSignature state.depth
          (state.maxLen - state.tokensEmitted) = true := by
  exact hasCompletion_iff_viable state

theorem encode_eq_sealed (program : Prog) :
    orgMemoRoot.encode program = (rpnTokens program).map Int.ofNat := by
  rfl

theorem encode_with_eos_eq_sealed_trace (program : Prog) :
    orgMemoRoot.encode program ++ [eos] =
      (rpnTokens program).map Int.ofNat ++ [eos] := by
  rfl

example : orgMemoRoot.legal (initial 9) 0 := by decide

example : ¬ orgMemoRoot.legal (initial 9) 3 := by decide

example :
    orgMemoRoot.run forceCloseCounterexample (initial 9) =
      some { depth := 1, tokensEmitted := 7, maxLen := 9 } := by
  rw [run_eq_sealed]
  decide

example :
    orgMemoRoot.HasCompletion
      { depth := 5, tokensEmitted := 5, maxLen := 9 } := by
  rw [completion_iff_sealed_canComplete]
  decide

end Mettapedia.GSLT.LanguageDef.GauthierRefinement
