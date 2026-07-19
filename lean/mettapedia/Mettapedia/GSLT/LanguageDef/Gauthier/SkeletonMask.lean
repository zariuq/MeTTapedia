/-
# Exact bounded mask for the GSLT2GSLT postfix skeleton

`GauthierE1.maskStep?` is the structural authority.  This module adds the exact
Python-facing state (`depth`, `tokens_emitted`, `max_len`) and bounded viability.
An operator is legal precisely when its structural step succeeds and the
resulting depth still has some completion inside the remaining token budget.

The bounded decision replaces the former `tokens + depth - 1` heuristic, which
was unsound for reachability in a signature containing arity-three and
arity-five operators.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.Gauthier.Skeleton

namespace Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton

abbrev PyToken := Int

def eos : PyToken := -1

/-- Exact counterpart of `gslt.grammar_mask.MaskState`. -/
structure MaskState where
  depth : Nat := 0
  tokensEmitted : Nat := 0
  maxLen : Nat := 60
  deriving DecidableEq, Repr

def initial (maxLen : Nat) : MaskState :=
  { maxLen := maxLen }

def operatorIds (sig : Signature σ) : List Nat :=
  List.range sig.length

/-- Structural successor depth, delegated to the established E1 mask step. -/
def nextDepth? (sig : Signature σ) (id depth : Nat) : Option Nat :=
  (maskStep? sig id (List.replicate depth ())).map List.length

/--
Exact bounded completion decision.  Stopping at depth one consumes no operator
token; every recursive branch consumes exactly one remaining operator slot.
-/
def canComplete (sig : Signature σ) (depth : Nat) : Nat → Bool
  | 0 => depth == 1
  | remaining + 1 =>
      depth == 1 ||
        (operatorIds sig).any fun id =>
          match nextDepth? sig id depth with
          | none => false
          | some nextDepth => canComplete sig nextDepth remaining

def opLegal (sig : Signature σ) (state : MaskState) (id : Nat) : Bool :=
  if state.tokensEmitted < state.maxLen then
    match nextDepth? sig id state.depth with
    | none => false
    | some nextDepth =>
        canComplete sig nextDepth (state.maxLen - (state.tokensEmitted + 1))
  else
    false

/-- Integer serialization used by Python: EOS is `-1`; operator keys are nonnegative. -/
def legalTokens (sig : Signature σ) (state : MaskState) : List PyToken :=
  let eosTokens :=
    if state.depth = 1 ∧ state.tokensEmitted ≤ state.maxLen then [eos] else []
  let ops :=
    ((operatorIds sig).filter (opLegal sig state)).map Int.ofNat
  eosTokens ++ ops

/-- Exact counterpart of `gslt.grammar_mask.step`, made partial rather than throwing. -/
def step? (sig : Signature σ) (state : MaskState) (token : PyToken) : Option MaskState :=
  if token ∈ legalTokens sig state then
    if token = eos then
      some state
    else
      match nextDepth? sig token.toNat state.depth with
      | none => none
      | some nextDepth =>
          some
            { depth := nextDepth
              tokensEmitted := state.tokensEmitted + 1
              maxLen := state.maxLen }
  else
    none

def run (sig : Signature σ) : List PyToken → MaskState → Option MaskState
  | [], state => some state
  | token :: rest, state =>
      match step? sig state token with
      | none => none
      | some next => run sig rest next

/-- A runtime program stream contains only nonnegative operator tokens. -/
def OperatorStream (tokens : List PyToken) : Prop :=
  ∀ token, token ∈ tokens → 0 ≤ token

/-- Exact logical contract of `recognizes_postfix`, excluding the external EOS token. -/
def AcceptsProgram (sig : Signature σ) (tokens : List PyToken) (maxLen : Nat) : Prop :=
  OperatorStream tokens ∧
    tokens ≠ [] ∧
    tokens.length ≤ maxLen ∧
    ∃ finalState,
      run sig tokens (initial maxLen) = some finalState ∧ finalState.depth = 1

/-- A decoder trace terminates by appending EOS to an accepted operator stream. -/
def AcceptsTrace (sig : Signature σ) (trace : List PyToken) (maxLen : Nat) : Prop :=
  ∃ tokens, AcceptsProgram sig tokens maxLen ∧ trace = tokens ++ [eos]

/-! ## Structural synchronization lemmas -/

theorem unitList_eq_replicate (values : List Unit) :
    values = List.replicate values.length () := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      have hvalue : value = () := Subsingleton.elim _ _
      subst value
      change () :: rest = () :: List.replicate rest.length ()
      exact congrArg (fun tail => () :: tail) ih

theorem nextDepth?_eq_some_iff (sig : Signature σ) (id depth nextDepth : Nat) :
    nextDepth? sig id depth = some nextDepth ↔
      maskStep? sig id (List.replicate depth ()) =
        some (List.replicate nextDepth ()) := by
  unfold nextDepth?
  cases hstep : maskStep? sig id (List.replicate depth ()) with
  | none => simp only [Option.map_none, reduceCtorEq, iff_self]
  | some stack =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro hlength
        rw [← hlength]
        exact unitList_eq_replicate stack
      · intro hstack
        have hlength := congrArg List.length hstack
        simpa using hlength

theorem entryAt_some_lt {sig : Signature σ} {id : Nat} {tableEntry : Entry σ}
    (hentry : entryAt sig id = some tableEntry) : id < sig.length := by
  induction sig generalizing id with
  | nil =>
      cases id <;> simp [entryAt, listGet?] at hentry
  | cons head tail ih =>
      cases id with
      | zero => simp
      | succ id =>
          simp only [entryAt, listGet?] at hentry
          have hlt := ih hentry
          simpa using Nat.succ_lt_succ hlt

theorem maskStep?_some_id_lt {sig : Signature σ} {id depth : Nat} {stack : List Unit}
    (hstep : maskStep? sig id (List.replicate depth ()) = some stack) :
    id < sig.length := by
  unfold maskStep? at hstep
  cases hentry : entryAt sig id with
  | none => simp [hentry] at hstep
  | some tableEntry => exact entryAt_some_lt hentry

theorem nextDepth?_some_id_lt {sig : Signature σ} {id depth nextDepth : Nat}
    (hnext : nextDepth? sig id depth = some nextDepth) : id < sig.length := by
  exact maskStep?_some_id_lt ((nextDepth?_eq_some_iff sig id depth nextDepth).mp hnext)

theorem canComplete_succ_of_true (sig : Signature σ) :
    ∀ remaining depth,
      canComplete sig depth remaining = true →
        canComplete sig depth (remaining + 1) = true
  | 0, depth, h => by
      simp only [canComplete, beq_iff_eq] at h
      subst depth
      simp [canComplete]
  | remaining + 1, depth, h => by
      simp only [canComplete, Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with hdone | hstep
      · exact Or.inl hdone
      · right
        simp only [List.any_eq_true] at hstep ⊢
        rcases hstep with ⟨id, hid, hbranch⟩
        refine ⟨id, hid, ?_⟩
        cases hnext : nextDepth? sig id depth with
        | none => simp [hnext] at hbranch
        | some nextDepth =>
            simp only [hnext] at hbranch ⊢
            exact canComplete_succ_of_true sig remaining nextDepth hbranch

theorem canComplete_mono (sig : Signature σ) {depth first second : Nat}
    (hle : first ≤ second)
    (h : canComplete sig depth first = true) :
    canComplete sig depth second = true := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
      rw [Nat.add_succ]
      exact canComplete_succ_of_true sig (first + extra) depth ih

theorem canComplete_of_maskStack (sig : Signature σ) :
    ∀ (tokens : List Nat) (depth : Nat),
      maskStack? sig tokens (List.replicate depth ()) = some [()] →
        canComplete sig depth tokens.length = true
  | [], depth, hrun => by
      simp only [maskStack?] at hrun
      have hlength := congrArg List.length (Option.some.inj hrun)
      simp at hlength
      subst depth
      rfl
  | id :: rest, depth, hrun => by
      simp only [maskStack?] at hrun
      cases hstep : maskStep? sig id (List.replicate depth ()) with
      | none => simp [hstep] at hrun
      | some stack =>
          simp only [hstep] at hrun
          have hstack : stack = List.replicate stack.length () :=
            unitList_eq_replicate stack
          rw [hstack] at hrun
          have htail := canComplete_of_maskStack sig rest stack.length hrun
          have hid : id ∈ operatorIds sig := by
            simp [operatorIds, maskStep?_some_id_lt hstep]
          have hnext : nextDepth? sig id depth = some stack.length := by
            unfold nextDepth?
            rw [hstep]
            rfl
          simp only [List.length_cons, canComplete, Bool.or_eq_true, beq_iff_eq]
          right
          simp only [List.any_eq_true]
          exact ⟨id, hid, by simp [hnext, htail]⟩

/-- `canComplete` is not merely optimistic: it constructs a structural completion. -/
theorem canComplete_witness (sig : Signature σ) :
    ∀ (remaining depth : Nat),
      canComplete sig depth remaining = true →
        ∃ tokens,
          tokens.length ≤ remaining ∧
          maskStack? sig tokens (List.replicate depth ()) = some [()]
  | 0, depth, hcomplete => by
      simp only [canComplete, beq_iff_eq] at hcomplete
      subst depth
      exact ⟨[], by simp, rfl⟩
  | remaining + 1, depth, hcomplete => by
      simp only [canComplete, Bool.or_eq_true, beq_iff_eq] at hcomplete
      rcases hcomplete with hfinished | hbranch
      · subst depth
        exact ⟨[], by simp, rfl⟩
      · simp only [List.any_eq_true] at hbranch
        rcases hbranch with ⟨id, _hid, hchosen⟩
        cases hnext : nextDepth? sig id depth with
        | none => simp [hnext] at hchosen
        | some nextDepth =>
            simp only [hnext] at hchosen
            rcases canComplete_witness sig remaining nextDepth hchosen with
              ⟨rest, hrestLength, hrestRun⟩
            have hfirst :=
              (nextDepth?_eq_some_iff sig id depth nextDepth).mp hnext
            refine ⟨id :: rest, ?_, ?_⟩
            · simp only [List.length_cons]
              omega
            · simp only [maskStack?, hfirst]
              exact hrestRun

/-! ## Exact-token and structural-machine agreement -/

theorem ofNat_ne_eos (id : Nat) : (Int.ofNat id : PyToken) ≠ eos := by
  simp [eos]

theorem ofNat_mem_legalTokens_iff (sig : Signature σ) (state : MaskState) (id : Nat) :
    (Int.ofNat id : PyToken) ∈ legalTokens sig state ↔
      id ∈ operatorIds sig ∧ opLegal sig state id = true := by
  simp [legalTokens, eos]

theorem eos_mem_legalTokens_iff (sig : Signature σ) (state : MaskState) :
    eos ∈ legalTokens sig state ↔
      state.depth = 1 ∧ state.tokensEmitted ≤ state.maxLen := by
  simp [legalTokens, eos]

theorem mem_legalTokens_of_ne_eos {sig : Signature σ} {state : MaskState}
    {token : PyToken} (hmem : token ∈ legalTokens sig state) (hne : token ≠ eos) :
    ∃ id,
      token = Int.ofNat id ∧
      id ∈ operatorIds sig ∧
      opLegal sig state id = true := by
  unfold legalTokens at hmem
  rcases List.mem_append.mp hmem with hterminator | hoperator
  · by_cases hdone : state.depth = 1 ∧ state.tokensEmitted ≤ state.maxLen
    · simp only [if_pos hdone, List.mem_singleton] at hterminator
      exact False.elim (hne hterminator)
    · simp only [if_neg hdone, List.not_mem_nil] at hterminator
  · rcases List.mem_map.mp hoperator with ⟨id, hid, htoken⟩
    rcases List.mem_filter.mp hid with ⟨hid, hlegal⟩
    exact ⟨id, htoken.symm, hid, hlegal⟩

theorem step?_ofNat_sync {sig : Signature σ} {state finalState : MaskState} {id : Nat}
    (hstep : step? sig state (Int.ofNat id) = some finalState) :
    ∃ structuralStack,
      maskStep? sig id (List.replicate state.depth ()) = some structuralStack ∧
      finalState.depth = structuralStack.length ∧
      finalState.tokensEmitted = state.tokensEmitted + 1 ∧
      finalState.maxLen = state.maxLen := by
  unfold step? at hstep
  by_cases hlegal : (Int.ofNat id : PyToken) ∈ legalTokens sig state
  · rw [if_pos hlegal] at hstep
    rw [if_neg (ofNat_ne_eos id)] at hstep
    change
      (match nextDepth? sig id state.depth with
        | none => none
        | some nextDepth =>
            some
              { depth := nextDepth
                tokensEmitted := state.tokensEmitted + 1
                maxLen := state.maxLen }) = some finalState at hstep
    cases hnext : nextDepth? sig id state.depth with
    | none => simp [hnext] at hstep
    | some nextDepth =>
        simp only [hnext, Option.some.injEq] at hstep
        subst finalState
        refine ⟨List.replicate nextDepth (), ?_, by simp, rfl, rfl⟩
        exact (nextDepth?_eq_some_iff sig id state.depth nextDepth).mp hnext
  · rw [if_neg hlegal] at hstep
    simp at hstep

theorem run_ofNat_maskStack_sync (sig : Signature σ) :
    ∀ (tokens : List Nat) (state finalState : MaskState),
      run sig (tokens.map Int.ofNat) state = some finalState →
        ∃ structuralStack,
          maskStack? sig tokens (List.replicate state.depth ()) = some structuralStack ∧
          finalState.depth = structuralStack.length
  | [], state, finalState, hrun => by
      simp only [List.map_nil, run, Option.some.injEq] at hrun
      subst finalState
      exact ⟨List.replicate state.depth (), rfl, by simp⟩
  | id :: rest, state, finalState, hrun => by
      simp only [List.map_cons, run] at hrun
      cases hfirst : step? sig state (Int.ofNat id) with
      | none =>
          rw [hfirst] at hrun
          contradiction
      | some middle =>
          simp only [hfirst] at hrun
          rcases step?_ofNat_sync hfirst with
            ⟨firstStack, hstructuralFirst, hmiddleDepth, _hmiddleTokens, _hmiddleMax⟩
          rcases run_ofNat_maskStack_sync sig rest middle finalState hrun with
            ⟨lastStack, hstructuralRest, hfinalDepth⟩
          have hfirstStack : firstStack = List.replicate middle.depth () := by
            rw [hmiddleDepth]
            exact unitList_eq_replicate firstStack
          rw [← hfirstStack] at hstructuralRest
          refine ⟨lastStack, ?_, hfinalDepth⟩
          simp only [maskStack?, hstructuralFirst]
          exact hstructuralRest

theorem operatorStream_eq_map_toNat {tokens : List PyToken}
    (hstream : OperatorStream tokens) :
    tokens = (tokens.map Int.toNat).map Int.ofNat := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      have hnonneg : 0 ≤ token := hstream token (by simp)
      have hrest : OperatorStream rest := by
        intro value hvalue
        exact hstream value (by simp [hvalue])
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨(Int.toNat_of_nonneg hnonneg).symm, ih hrest⟩

/-- T2 soundness: every accepted Python integer stream parses to a well-formed E1 program. -/
theorem acceptsProgram_sound {sig : Signature σ} {tokens : List PyToken} {maxLen : Nat}
    (haccept : AcceptsProgram sig tokens maxLen) :
    ∃ program,
      recognize sig (tokens.map Int.toNat) = some program ∧ WellFormed sig program := by
  rcases haccept with ⟨hstream, _hnonempty, _hlength, finalState, hrun, hdepth⟩
  have htokens := operatorStream_eq_map_toNat hstream
  rw [htokens] at hrun
  rcases run_ofNat_maskStack_sync sig (tokens.map Int.toNat) (initial maxLen) finalState hrun with
    ⟨structuralStack, hstructural, hfinal⟩
  have hstackLength : structuralStack.length = 1 := by
    omega
  have hstack : structuralStack = [()] := by
    rw [unitList_eq_replicate structuralStack, hstackLength]
    rfl
  have hmask : maskLegal sig (tokens.map Int.toNat) := by
    unfold maskLegal
    simpa [initial, hstack] using hstructural
  have hsome : (recognize sig (tokens.map Int.toNat)).isSome :=
    (recognize_iff_maskLegal sig (tokens.map Int.toNat)).mp hmask
  cases hrecognized : recognize sig (tokens.map Int.toNat) with
  | none => simp [hrecognized] at hsome
  | some program =>
      refine ⟨program, rfl, ?_⟩
      exact recognize_sound hrecognized

/-! ## Completeness and prefix legality -/

theorem run_of_structural_completion (sig : Signature σ) :
    ∀ (tokens : List Nat) (state : MaskState),
      state.tokensEmitted + tokens.length ≤ state.maxLen →
      maskStack? sig tokens (List.replicate state.depth ()) = some [()] →
        ∃ finalState,
          run sig (tokens.map Int.ofNat) state = some finalState ∧
          finalState.depth = 1 ∧
          finalState.tokensEmitted = state.tokensEmitted + tokens.length ∧
          finalState.maxLen = state.maxLen
  | [], state, _hbudget, hstructural => by
      simp only [maskStack?] at hstructural
      have hlength := congrArg List.length (Option.some.inj hstructural)
      have hdepth : state.depth = 1 := by simpa using hlength
      exact ⟨state, rfl, hdepth, by simp, rfl⟩
  | id :: rest, state, hbudget, hstructural => by
      simp only [maskStack?] at hstructural
      cases hfirst : maskStep? sig id (List.replicate state.depth ()) with
      | none =>
          rw [hfirst] at hstructural
          contradiction
      | some structuralMiddle =>
          rw [hfirst] at hstructural
          have hmiddleReplicate :
              structuralMiddle = List.replicate structuralMiddle.length () :=
            unitList_eq_replicate structuralMiddle
          have hrestStructural :
              maskStack? sig rest (List.replicate structuralMiddle.length ()) = some [()] := by
            rw [hmiddleReplicate] at hstructural
            exact hstructural
          have hnext : nextDepth? sig id state.depth = some structuralMiddle.length := by
            unfold nextDepth?
            rw [hfirst]
            rfl
          have hid : id ∈ operatorIds sig := by
            simp [operatorIds, maskStep?_some_id_lt hfirst]
          have htime : state.tokensEmitted < state.maxLen := by
            simp only [List.length_cons] at hbudget
            omega
          have htailCan :
              canComplete sig structuralMiddle.length rest.length = true :=
            canComplete_of_maskStack sig rest structuralMiddle.length hrestStructural
          have hremaining :
              rest.length ≤ state.maxLen - (state.tokensEmitted + 1) := by
            simp only [List.length_cons] at hbudget
            omega
          have hcan :
              canComplete sig structuralMiddle.length
                  (state.maxLen - (state.tokensEmitted + 1)) = true :=
            canComplete_mono sig hremaining htailCan
          have hopLegal : opLegal sig state id = true := by
            simp [opLegal, htime, hnext, hcan]
          have htoken : (Int.ofNat id : PyToken) ∈ legalTokens sig state :=
            (ofNat_mem_legalTokens_iff sig state id).mpr ⟨hid, hopLegal⟩
          let middle : MaskState :=
            { depth := structuralMiddle.length
              tokensEmitted := state.tokensEmitted + 1
              maxLen := state.maxLen }
          have hexactFirst : step? sig state (Int.ofNat id) = some middle := by
            unfold step?
            rw [if_pos htoken, if_neg (ofNat_ne_eos id)]
            change
              (match nextDepth? sig id state.depth with
                | none => none
                | some nextDepth =>
                    some
                      { depth := nextDepth
                        tokensEmitted := state.tokensEmitted + 1
                        maxLen := state.maxLen }) = some middle
            rw [hnext]
          have hrestBudget : middle.tokensEmitted + rest.length ≤ middle.maxLen := by
            simp only [middle]
            simp only [List.length_cons] at hbudget
            omega
          rcases run_of_structural_completion sig rest middle hrestBudget hrestStructural with
            ⟨finalState, hrestRun, hfinalDepth, hfinalTokens, hfinalMax⟩
          refine ⟨finalState, ?_, hfinalDepth, ?_, hfinalMax⟩
          · simp only [List.map_cons, run, hexactFirst]
            exact hrestRun
          · simp only [middle] at hfinalTokens
            simp only [List.length_cons]
            omega

theorem rpnTokens_ne_nil (program : Prog) : rpnTokens program ≠ [] := by
  cases program with
  | node id children => simp [rpnTokens]

/-- T2 completeness: every well-formed program fitting the budget has every token admitted. -/
theorem rpnTokens_complete {sig : Signature σ} {program : Prog}
    (hwellFormed : WellFormed sig program) {maxLen : Nat}
    (hbudget : (rpnTokens program).length ≤ maxLen) :
    AcceptsProgram sig ((rpnTokens program).map Int.ofNat) maxLen := by
  have hrecognize : recognize sig (rpnTokens program) = some program := by
    unfold recognize recognizeRaw
    simp [recognizeRawStack_rpnTokens_complete hwellFormed []]
  have hmask : maskLegal sig (rpnTokens program) :=
    (recognize_iff_maskLegal sig (rpnTokens program)).mpr (by simp [hrecognize])
  rcases run_of_structural_completion sig (rpnTokens program) (initial maxLen)
      (by simpa [initial] using hbudget) (by simpa [maskLegal, initial] using hmask) with
    ⟨finalState, hrun, hdepth, _htokens, _hmax⟩
  refine ⟨?_, ?_, ?_, finalState, hrun, hdepth⟩
  · intro token htoken
    rcases List.mem_map.mp htoken with ⟨id, _hid, rfl⟩
    simp
  · simpa using rpnTokens_ne_nil program
  · simpa using hbudget

theorem run_append (sig : Signature σ) (first second : List PyToken) (state : MaskState) :
    run sig (first ++ second) state =
      match run sig first state with
      | none => none
      | some middle => run sig second middle := by
  induction first generalizing state with
  | nil => rfl
  | cons token rest ih =>
      simp only [List.cons_append, run]
      cases hstep : step? sig state token with
      | none => rfl
      | some middle => exact ih middle

theorem mem_legalTokens_of_step?_some {sig : Signature σ} {state next : MaskState}
    {token : PyToken} (hstep : step? sig state token = some next) :
    token ∈ legalTokens sig state := by
  unfold step? at hstep
  by_cases hlegal : token ∈ legalTokens sig state
  · exact hlegal
  · rw [if_neg hlegal] at hstep
    contradiction

/-- A successful run exposes legality at every proper prefix, not only at its endpoint. -/
theorem every_prefix_legal_of_run {sig : Signature σ} {tokens : List PyToken}
    {state finalState : MaskState}
    (hrun : run sig tokens state = some finalState) :
    ∀ before token after,
      tokens = before ++ token :: after →
        ∃ prefixState,
          run sig before state = some prefixState ∧
          token ∈ legalTokens sig prefixState := by
  intro before token after htokens
  rw [htokens, run_append] at hrun
  cases hprefix : run sig before state with
  | none =>
      rw [hprefix] at hrun
      contradiction
  | some prefixState =>
      rw [hprefix] at hrun
      simp only [run] at hrun
      cases hstep : step? sig prefixState token with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some middle =>
          exact ⟨prefixState, rfl, mem_legalTokens_of_step?_some hstep⟩

/-- Explicit prefix form of completeness for the canonical postfix serialization. -/
theorem rpnTokens_every_prefix_legal {sig : Signature σ} {program : Prog}
    (hwellFormed : WellFormed sig program) {maxLen : Nat}
    (hbudget : (rpnTokens program).length ≤ maxLen) :
    ∀ before token after,
      (rpnTokens program).map Int.ofNat = before ++ token :: after →
        ∃ prefixState,
          run sig before (initial maxLen) = some prefixState ∧
          token ∈ legalTokens sig prefixState := by
  rcases rpnTokens_complete hwellFormed hbudget with
    ⟨_hstream, _hne, _hlen, finalState, hrun, _hdepth⟩
  exact every_prefix_legal_of_run hrun

/-! ## No-dead-end invariant -/

/-- Budget-respecting states from which some complete postfix program remains reachable. -/
def Viable (sig : Signature σ) (state : MaskState) : Prop :=
  state.tokensEmitted ≤ state.maxLen ∧
    canComplete sig state.depth (state.maxLen - state.tokensEmitted) = true

/-- An explicit operator suffix that reaches depth one inside the remaining budget. -/
def HasCompletion (sig : Signature σ) (state : MaskState) : Prop :=
  ∃ suffix finalState,
    OperatorStream suffix ∧
    suffix.length ≤ state.maxLen - state.tokensEmitted ∧
    run sig suffix state = some finalState ∧
    finalState.depth = 1 ∧
    finalState.tokensEmitted ≤ finalState.maxLen

theorem viable_has_completion (sig : Signature σ) (state : MaskState)
    (hviable : Viable sig state) :
    HasCompletion sig state := by
  rcases hviable with ⟨hbudget, hcomplete⟩
  rcases canComplete_witness sig (state.maxLen - state.tokensEmitted) state.depth hcomplete with
    ⟨ids, hidsLength, hstructural⟩
  have hrunBudget : state.tokensEmitted + ids.length ≤ state.maxLen := by omega
  rcases run_of_structural_completion sig ids state hrunBudget hstructural with
    ⟨finalState, hrun, hdepth, htokens, hmaxLen⟩
  refine ⟨ids.map Int.ofNat, finalState, ?_, ?_, hrun, hdepth, ?_⟩
  · intro token htoken
    rcases List.mem_map.mp htoken with ⟨id, _hid, rfl⟩
    simp
  · simpa using hidsLength
  · rw [htokens, hmaxLen]
    exact hrunBudget

/-- Exact bounded viability always exposes at least one legal next token. -/
theorem exists_mem_legalTokens_of_viable (sig : Signature σ) (state : MaskState)
    (hbudget : state.tokensEmitted ≤ state.maxLen)
    (hviable :
      canComplete sig state.depth (state.maxLen - state.tokensEmitted) = true) :
    ∃ token, token ∈ legalTokens sig state := by
  by_cases hdone : state.depth = 1
  · exact ⟨eos, (eos_mem_legalTokens_iff sig state).mpr ⟨hdone, hbudget⟩⟩
  · cases hremaining : state.maxLen - state.tokensEmitted with
    | zero =>
        simp [canComplete, hremaining, hdone] at hviable
    | succ remaining =>
        rw [hremaining] at hviable
        simp only [canComplete, Bool.or_eq_true, beq_iff_eq] at hviable
        rcases hviable with hfinished | hbranch
        · exact False.elim (hdone hfinished)
        · simp only [List.any_eq_true] at hbranch
          rcases hbranch with ⟨id, hid, hchosen⟩
          cases hnext : nextDepth? sig id state.depth with
          | none => simp [hnext] at hchosen
          | some nextDepth =>
              simp only [hnext] at hchosen
              have htime : state.tokensEmitted < state.maxLen := by omega
              have hslots :
                  state.maxLen - (state.tokensEmitted + 1) = remaining := by
                omega
              have hopLegal : opLegal sig state id = true := by
                simp [opLegal, htime, hnext, hslots, hchosen]
              exact
                ⟨Int.ofNat id,
                  (ofNat_mem_legalTokens_iff sig state id).mpr ⟨hid, hopLegal⟩⟩

theorem step?_preserves_viable {sig : Signature σ} {state next : MaskState}
    {token : PyToken} (hviable : Viable sig state)
    (hstep : step? sig state token = some next) :
    Viable sig next := by
  unfold step? at hstep
  by_cases hmem : token ∈ legalTokens sig state
  · rw [if_pos hmem] at hstep
    by_cases hterminator : token = eos
    · rw [if_pos hterminator] at hstep
      simp only [Option.some.injEq] at hstep
      subst next
      exact hviable
    · rw [if_neg hterminator] at hstep
      rcases mem_legalTokens_of_ne_eos hmem hterminator with
        ⟨id, htoken, _hid, hopLegal⟩
      cases hnext : nextDepth? sig token.toNat state.depth with
      | none => simp [hnext] at hstep
      | some nextDepth =>
          simp only [hnext, Option.some.injEq] at hstep
          subst next
          have htokenToNat : token.toNat = id := by
            rw [htoken]
            simp
          rw [htokenToNat] at hnext
          unfold opLegal at hopLegal
          by_cases htime : state.tokensEmitted < state.maxLen
          · rw [if_pos htime, hnext] at hopLegal
            unfold Viable
            constructor
            · change state.tokensEmitted + 1 ≤ state.maxLen
              omega
            · change
                canComplete sig nextDepth
                  (state.maxLen - (state.tokensEmitted + 1)) = true
              exact hopLegal
          · rw [if_neg htime] at hopLegal
            contradiction
  · rw [if_neg hmem] at hstep
    contradiction

theorem run_preserves_viable (sig : Signature σ) :
    ∀ (tokens : List PyToken) (state finalState : MaskState),
      Viable sig state →
      run sig tokens state = some finalState →
      Viable sig finalState
  | [], state, finalState, hviable, hrun => by
      simp only [run, Option.some.injEq] at hrun
      subst finalState
      exact hviable
  | token :: rest, state, finalState, hviable, hrun => by
      simp only [run] at hrun
      cases hstep : step? sig state token with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some middle =>
          rw [hstep] at hrun
          exact run_preserves_viable sig rest middle finalState
            (step?_preserves_viable hviable hstep) hrun

/-- A state actually reached by running a legal decoder prefix from the initial state. -/
def Reachable (sig : Signature σ) (maxLen : Nat) (state : MaskState) : Prop :=
  ∃ tokens, run sig tokens (initial maxLen) = some state

theorem orgMemo_initial_viable {maxLen : Nat} (hmaxLen : 1 ≤ maxLen) :
    Viable orgMemoSignature (initial maxLen) := by
  constructor
  · simp [initial]
  · simpa [initial] using
      (canComplete_mono orgMemoSignature hmaxLen
        (by decide : canComplete orgMemoSignature 0 1 = true))

theorem orgMemo_reachable_viable {maxLen : Nat} (hmaxLen : 1 ≤ maxLen)
    {state : MaskState} (hreachable : Reachable orgMemoSignature maxLen state) :
    Viable orgMemoSignature state := by
  rcases hreachable with ⟨tokens, hrun⟩
  exact run_preserves_viable orgMemoSignature tokens (initial maxLen) state
    (orgMemo_initial_viable hmaxLen) hrun

/--
T2 completion crown: every state reachable under the authenticated org.memo
signature has an explicit operator suffix that completes within its budget.
-/
theorem orgMemo_reachable_has_completion {maxLen : Nat} (hmaxLen : 1 ≤ maxLen)
    {state : MaskState} (hreachable : Reachable orgMemoSignature maxLen state) :
    HasCompletion orgMemoSignature state :=
  viable_has_completion orgMemoSignature state
    (orgMemo_reachable_viable hmaxLen hreachable)

/--
T2 no-dead-ends crown: every state reachable under the authenticated org.memo
signature has a legal continuation (EOS at a completed state, an operator otherwise).
-/
theorem orgMemo_reachable_has_legal_token {maxLen : Nat} (hmaxLen : 1 ≤ maxLen)
    {state : MaskState} (hreachable : Reachable orgMemoSignature maxLen state) :
    ∃ token, token ∈ legalTokens orgMemoSignature state := by
  have hviable := orgMemo_reachable_viable hmaxLen hreachable
  exact exists_mem_legalTokens_of_viable orgMemoSignature state hviable.1 hviable.2

/-! ## Executable non-vacuity and the former force-close counterexample -/

def forceCloseCounterexample : List PyToken :=
  [0, 1, 2, 10, 11, 15, 13]

example :
    15 ∈ legalTokens orgMemoSignature
      { depth := 5, tokensEmitted := 5, maxLen := 9 } := by
  decide

example :
    run orgMemoSignature forceCloseCounterexample (initial 9) =
      some { depth := 1, tokensEmitted := 7, maxLen := 9 } := by
  decide

example :
    run orgMemoSignature [3] (initial 9) = none := by
  decide

end Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
