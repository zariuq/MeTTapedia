import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNativeRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedExample
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.UnmatchedControls

/-!
# Controls for hosted firings as native live firings

The constructions compared are those of `HostedNative`: the contextual rule-syntax step (a bag store
of labelled occurrences; one match per step; guards asked at every solution of the information,
after the firing's own tells; the program a fixed set of rules beside the store; one knowledge store)
and the native step on live firings (a bag store of conditional rows; one match per step, its rule and
rows opened at reserved scopes; guards and queries asked at every solution of the information, after
the firing's own tells; the rule carried by the firing, its unknowns in the private family; one
knowledge store, published along the solver's returned frame).

## Positive

* `call_admitted`, `call_realized`, `call_result`: the actual call of the program with an equation
  written twice (`Counted.Example`) is admitted by the hosted step; its live firing is admitted by
  the native step, at every scope ledger and budget; and the native result is a dead-name extension of
  the hosted result. The laws of `HostedNative` are not vacuous.
* `call_return_residual`: the residual law at the actual run `[call, return]`.
* `call_jointly`, `call_run`: the one-member family of the call is jointly solvable in the hosted
  reading, is a hosted run, and so has a native sequential run agreeing up to dead names.

## Negative

* `ret_on_call_refused`, `ret_on_call_no_run`: the `ret` rule at the call's row is refused by the hosted
  step, so its live firing is refused by the native step, and its family has no run in either step.
* `guard_refuses`: beside a row that matches the call at one solution, the none guard of `apply`
  without a matching equation refuses the hosted firing, so the native step refuses its live firing.
* `competing_calls_not_apart`, `competing_calls_not_compatible`: two calls consuming the same call row
  are not apart, and in the packet image (`NativePacketRounds.compatible_iff`) they are not compatible:
  alternatives of one choice, not two independent firings.
* **A first-order collapse merges what the adapter keeps apart** (`choice_unknowns_apart`,
  `choice_unknowns_collapse`, `adapter_does_not_entail`, `collapse_entails`): the two alternatives of a
  choice are distinct names of the native information frame, and no solution of the empty knowledge
  identifies them; after `Frames.toFirstOrder` they are one observation.
* **The returned ledger cannot be dropped** (`ledger_grows`, `no_extension_at_old_ledger`,
  `call_no_extension_at_old_ledger`): the native result reserves the step's scopes, so the hosted result
  adapted at the old ledger has no dead-name extension onto the native result. One ledger gives every
  firing the same rule scope (`rule_scope_shared`), and the step shifts it by a positive amount
  (`shift_pos`): the residual of a second firing opens beyond the first firing's scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Interface (NativeState LiveFiring native)
open Interface.Frames (Frame)
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting Hosting.Alternatives
open Hosting.Alternatives.Controls (N dupP q3 eqAt)

/-! ## The ledger and the scope shift, at every firing -/

section Ledger

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  (M : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
  {P : CProgram S} {r : CRule S} (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ)

/-- **The native result reserves the step's scopes**: the first scope beyond the old ledger is in the
native result's ledger and not in the old one. -/
theorem ledger_grows (realized : (live M s p occupied pl selection fuel).toNative.Realized) :
    ContextualActivationScopes.start occupied ∈ (native.result (live M s p occupied pl selection fuel).toNative realized).state.occupied ∧
      ContextualActivationScopes.start occupied ∉ occupied := by
  refine ⟨?_, fun inside => lt_irrefl _ (ContextualActivationScopes.occupied_lt_start occupied inside)⟩
  have reserved := ContextualActivationScopes.at_mem_reserved occupied selection (ContextualActivationScopes.rulePort selection)
  have after : ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection) ∈
      ContextualActivationScopes.after occupied selection := Finset.mem_union_right _ reserved
  exact ContextualFreshFrameScopeLedger.old_scopes_retained _ after

/-- **Without the returned ledger the result law fails**: the hosted result adapted at the old ledger
has no dead-name extension onto the native result. -/
theorem no_extension_at_old_ledger (realized : (live M s p occupied pl selection fuel).toNative.Realized) :
    IsEmpty (Interface.NativeDead.DeadExtension
      (state κ ((RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).result
        (Interface.Frames.contextual S) s) (resultPresented s p member pl selection) occupied)
      (native.result (live M s p occupied pl selection fuel).toNative realized)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨inside, outside⟩ := ledger_grows M s p occupied pl selection fuel realized
  have same : (native.result (live M s p occupied pl selection fuel).toNative realized).state.occupied = occupied :=
    e.occupied
  rw [same] at inside
  exact outside inside

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **One ledger, one rule scope**: at one ledger every firing opens its rule at the same scope. -/
theorem rule_scope_shared (selection₂ : Selection ℕ) :
    ruleScope occupied selection₂ = ruleScope occupied selection :=
  rfl

/-- **The step shifts the rule scope by a positive amount.** -/
theorem shift_pos (realized : (live M s p occupied pl selection fuel).toNative.Realized) :
    0 < Interface.NativeResidual.shift (Interface.LiveFiring.execution realized) := by
  obtain ⟨inside, outside⟩ := ledger_grows M s p occupied pl selection fuel realized
  have bound : ContextualActivationScopes.start occupied <
      ContextualActivationScopes.start (Interface.LiveFiring.execution realized).target.occupied :=
    ContextualActivationScopes.occupied_lt_start _ inside
  unfold Interface.NativeResidual.shift
  change 0 < ContextualActivationScopes.start (Interface.LiveFiring.execution realized).target.occupied -
    ContextualActivationScopes.start occupied
  omega

end Ledger

/-! ## The actual call of the program written twice -/

/-- The start of the query `(f)` in the program written twice, presented. -/
def startTwicePresented : Presented ([] : Ctx MSig) () Counted.Example.startTwice :=
  startPresented N dupP q3

/-- The call's schema, placed. -/
def callPlaced : Placed ([] : Ctx MSig) () mkeys Counted.Example.callRule :=
  placedSchema N (eqAt [1])

/-- The canonical call firing is admitted by the hosted step. -/
theorem call_admitted :
    (RuleSyntax.Contextual.canonical (F := Counted.Example.startTwice.frame) Counted.Example.callRule
      Counted.Example.callRule_mem ⟨[2], [], [3]⟩ []).Admits (Interface.Frames.contextual MSig)
      Counted.Example.startTwice :=
  Counted.Example.callFiring_admits (RuleSyntax.Contextual.canonical_fresh _ _ _ _ _)

/-- **Positive**: the call's live firing is admitted by the native step, at every ledger and budget. -/
theorem call_realized (occupied : Finset ℕ) (fuel : ℕ) :
    (live N Counted.Example.startTwice startTwicePresented occupied callPlaced ⟨[2], [], [3]⟩ fuel).toNative.Realized :=
  (admits_iff N Counted.Example.startTwice startTwicePresented occupied Counted.Example.callRule_mem callPlaced
    ⟨[2], [], [3]⟩ fuel).mp call_admitted

/-- **Positive**: the call's native result is a dead-name extension of the hosted result. -/
theorem call_result (occupied : Finset ℕ) (fuel : ℕ) :
    Nonempty (Interface.NativeDead.DeadExtension
      (resultState N Counted.Example.startTwice startTwicePresented occupied Counted.Example.callRule_mem callPlaced
        ⟨[2], [], [3]⟩ fuel (call_realized occupied fuel))
      ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).result (live N Counted.Example.startTwice
        startTwicePresented occupied callPlaced ⟨[2], [], [3]⟩ fuel).toNative (call_realized occupied fuel))) :=
  ⟨resultExtension N Counted.Example.startTwice startTwicePresented occupied Counted.Example.callRule_mem callPlaced
    ⟨[2], [], [3]⟩ fuel (call_realized occupied fuel)⟩

/-- **Positive**: the residual law at the actual run `[call, return]`: after the call, the native
residual of the return's live firing (taking the call's made row `3`) is the return's live firing at the
hosted result, carried along the result inclusion. -/
theorem call_return_residual (occupied : Finset ℕ) (fuel : ℕ) :
    Interface.NativeIterated.residualAfter (call_realized occupied fuel)
        (live N Counted.Example.startTwice startTwicePresented occupied (placedRet (κ := mkeys) N) ⟨[3], [], [4]⟩
          fuel) =
      (resultInclusion N Counted.Example.startTwice startTwicePresented occupied Counted.Example.callRule_mem callPlaced
          ⟨[2], [], [3]⟩ fuel (call_realized occupied fuel)).firing
        (live N ((RuleSyntax.Contextual.canonical (F := Counted.Example.startTwice.frame) Counted.Example.callRule
            Counted.Example.callRule_mem ⟨[2], [], [3]⟩ []).result (Interface.Frames.contextual MSig)
            Counted.Example.startTwice)
          (resultPresented Counted.Example.startTwice startTwicePresented Counted.Example.callRule_mem callPlaced
            ⟨[2], [], [3]⟩)
          ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).result (live N Counted.Example.startTwice
            startTwicePresented occupied callPlaced ⟨[2], [], [3]⟩ fuel).toNative (call_realized occupied fuel)).state.occupied
          (placedRet N) ⟨[3], [], [4]⟩ fuel) :=
  residual_eq N Counted.Example.startTwice startTwicePresented occupied Counted.Example.callRule_mem callPlaced
    ⟨[2], [], [3]⟩ fuel (call_realized occupied fuel) (placedRet N) ⟨[3], [], [4]⟩ fuel

/-- The call, as a member of a hosted family. -/
def callMember : Rounds.Member ([] : Ctx MSig) () mkeys (translate N dupP) :=
  ⟨Counted.Example.callRule, Counted.Example.callRule_mem, callPlaced, ⟨[2], [], [3]⟩, 0⟩

/-- **Positive**: the one-member family of the call is jointly solvable in the hosted reading, through
`Rounds.jointly_iff` from the native solution of the call's information. -/
theorem call_jointly (occupied : Finset ℕ) :
    Rounds.HostedJointly Counted.Example.startTwice ([callMember].map (Rounds.Member.hosted · Counted.Example.startTwice)) := by
  apply (Rounds.jointly_iff N Counted.Example.startTwice startTwicePresented occupied [callMember]).mp
  obtain ⟨b, σ, solved⟩ := Interface.NativeFiring.solvable_of_realized (call_realized occupied 0)
  refine ⟨b, Assignment.compose σ (ContextualSelectionViews.capturedTarget (ruleLocals ([] : Ctx MSig) () mkeys)
    Counted.Example.startTwice.frame.arity), fun g inside => ?_⟩
  obtain ⟨m, insideM, rfl⟩ := List.mem_map.mp inside
  obtain rfl := List.mem_singleton.mp insideM
  exact ⟨σ, solved, rfl⟩

/-- **Positive**: the one-member family of the call is a hosted run, so (`Rounds.sequential_iff`) a native
sequential run of its live firing exists, ending in a state that agrees with the adapted hosted result up
to dead names. -/
theorem call_run (occupied : Finset ℕ) :
    ∃ u : NativeState MSig ℕ ([] : Ctx MSig) (),
      Interface.NativeIterated.Sequential (state mkeys Counted.Example.startTwice startTwicePresented occupied)
        ([callMember].map (Rounds.Member.live N Counted.Example.startTwice startTwicePresented occupied)) u ∧
      Interface.NativeDead.DeadEquiv
        (state mkeys ((callMember.hosted Counted.Example.startTwice).result (Interface.Frames.contextual MSig)
          Counted.Example.startTwice)
          (resultPresented Counted.Example.startTwice startTwicePresented callMember.member callMember.placed
            callMember.selection) (Rounds.nextLedger occupied callMember.selection)) u :=
  (Rounds.sequential_iff N [callMember] Counted.Example.startTwice startTwicePresented occupied).2
    (.cons callMember [] call_admitted (.nil _ _ _))

/-- The call taking the call's row `2` and making the row `made`. -/
def callMemberAt (made : ℕ) : Rounds.Member ([] : Ctx MSig) () mkeys (translate N dupP) :=
  ⟨Counted.Example.callRule, Counted.Example.callRule_mem, callPlaced, ⟨[2], [], [made]⟩, 0⟩

/-- Two calls competing for the call's row. -/
noncomputable def competing (occupied : Finset ℕ) : List (LiveFiring (state mkeys Counted.Example.startTwice
    startTwicePresented occupied)) :=
  [callMemberAt 3, callMemberAt 4].map (Rounds.Member.live N Counted.Example.startTwice startTwicePresented occupied)

/-- **Negative**: two calls that consume the same call row are not apart. -/
theorem competing_calls_not_apart : ¬ Rounds.Apart (callMemberAt 3).selection (callMemberAt 4).selection := by
  rintro ⟨takes, -⟩
  exact (Finset.disjoint_left.mp takes) (show (2 : ℕ) ∈ ([2] : List ℕ).toFinset by simp)
    (show (2 : ℕ) ∈ ([2] : List ℕ).toFinset by simp)

/-- **Negative**: in the packet image, the two competing calls are not compatible: they are
alternatives of one choice, not two independent firings. -/
theorem competing_calls_not_compatible (occupied : Finset ℕ) :
    ¬ AnnotatedRuns.Compatible
      (Interface.Bridges.Concurrency.NativePacketStep.packetAction (S := MSig) (O := ℕ) (Γ := []) (sort := ()))
      (Interface.Bridges.Concurrency.NativePacketRounds.label (competing occupied))
      (Interface.Bridges.Concurrency.NativePacketStep.configuration
        (state mkeys Counted.Example.startTwice startTwicePresented occupied) 0)
      (Interface.Bridges.Concurrency.NativePacketStep.baseFiring (competing occupied)[(⟨0, by simp [competing]⟩ :
        Fin (competing occupied).length)] (Interface.Bridges.Concurrency.NativePacketRounds.useTag
          (⟨0, by simp [competing]⟩ : Fin (competing occupied).length)))
      (Interface.Bridges.Concurrency.NativePacketStep.baseFiring (competing occupied)[(⟨1, by simp [competing]⟩ :
        Fin (competing occupied).length)] (Interface.Bridges.Concurrency.NativePacketRounds.useTag
          (⟨1, by simp [competing]⟩ : Fin (competing occupied).length))) := by
  intro compatible
  have apart := (Interface.Bridges.Concurrency.NativePacketRounds.compatible_iff (competing occupied)
    ⟨0, by simp [competing]⟩ ⟨1, by simp [competing]⟩).mp compatible
  exact (Finset.disjoint_left.mp apart.1) (show (2 : ℕ) ∈ ([2] : List ℕ).toFinset by simp)
    (show (2 : ℕ) ∈ ([2] : List ℕ).toFinset by simp)

/-- **Negative**: at the old ledger the call's hosted result has no dead-name extension onto the
native result. -/
theorem call_no_extension_at_old_ledger (occupied : Finset ℕ) (fuel : ℕ) :
    IsEmpty (Interface.NativeDead.DeadExtension
      (state mkeys ((RuleSyntax.Contextual.canonical (F := Counted.Example.startTwice.frame) Counted.Example.callRule
        Counted.Example.callRule_mem ⟨[2], [], [3]⟩ []).result (Interface.Frames.contextual MSig) Counted.Example.startTwice)
        (resultPresented Counted.Example.startTwice startTwicePresented Counted.Example.callRule_mem callPlaced
          ⟨[2], [], [3]⟩) occupied)
      ((native (S := MSig) (O := ℕ) (Γ := []) (sort := ())).result (live N Counted.Example.startTwice
        startTwicePresented occupied callPlaced ⟨[2], [], [3]⟩ fuel).toNative (call_realized occupied fuel))) :=
  no_extension_at_old_ledger N Counted.Example.startTwice startTwicePresented occupied Counted.Example.callRule_mem
    callPlaced ⟨[2], [], [3]⟩ fuel (call_realized occupied fuel)

/-! ## A refused firing -/

section NodeTags

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (M : Nodes S Γ star)
  {V W X : Type} {D : V → MetaArity S} {E : W → MetaArity S} {F : X → MetaArity S}

/-- Instances of two nodes with one tag agree argument by argument. -/
theorem node_args {k : Tag} {σ : Assignment D F} {τ : Assignment E F}
    {args : Fin k.arity → Term (signature S D) Γ star} {args' : Fin k.arity → Term (signature S E) Γ star}
    (same : instantiate σ (M.node k args) = instantiate τ (M.node k args')) (i : Fin k.arity) :
    instantiate σ (args i) = instantiate τ (args' i) := by
  rw [M.instantiate_node, M.instantiate_node] at same
  exact congrFun (M.args_eq same) i

/-- Instances of two nodes are equal only at one tag. -/
theorem node_tags {k k' : Tag} {σ : Assignment D F} {τ : Assignment E F}
    {args : Fin k.arity → Term (signature S D) Γ star} {args' : Fin k'.arity → Term (signature S E) Γ star}
    (same : instantiate σ (M.node k args) = instantiate τ (M.node k' args')) : k = k' := by
  rw [M.instantiate_node, M.instantiate_node] at same
  exact M.tag_eq same

end NodeTags

/-- **Negative**: the `ret` rule at the call's row is refused by the hosted step (the call's row is
`alt(eval(apply f), empty)`, which no instance of `alt(eval(ret T), FS)` equals), so its live firing is
refused by the native step. -/
theorem ret_on_call_refused (occupied : Finset ℕ) (fuel : ℕ) :
    ¬ (live N Counted.Example.startTwice startTwicePresented occupied (placedRet (κ := mkeys) N) ⟨[2], [], [3]⟩
      fuel).toNative.Realized := by
  rw [← admits_iff N Counted.Example.startTwice startTwicePresented occupied (retRule_mem N dupP) (placedRet N)
    ⟨[2], [], [3]⟩ fuel]
  rintro ⟨-, -, ⟨B, σ, solved⟩, -⟩
  have taken := RuleSyntax.Firing.take_solved
    (RuleSyntax.Contextual.canonical (F := Counted.Example.startTwice.frame) (retRule N) (retRule_mem N dupP)
      ⟨[2], [], [3]⟩ []) solved (List.mem_singleton_self _)
  have terms : instantiate σ (instantiate (RuleSyntax.Contextual.canonicalOpening MSig Counted.Example.startTwice.frame
        (retRule N).locals) (altN N (evalN N (retN N (unk (Γ := ([] : Ctx MSig)) (star := ()) .datum)))
          (unk (Γ := ([] : Ctx MSig)) (star := ()) .stack))) =
      instantiate σ (instantiate (RuleSyntax.Contextual.weakenNames MSig Counted.Example.startTwice.frame
        (retRule N).locals) (encAlt N (instantiate queryNames) (.eval q3) [])) :=
    observe_injective taken
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose] at terms
  have focus := node_args N (k := .alt) terms ⟨0, by decide⟩
  have inner := node_args N (k := .eval) focus ⟨0, by decide⟩
  exact absurd (node_tags N inner) (by decide)

/-- The return rule taking the call's row, as a member. -/
def retOnCallMember : Rounds.Member ([] : Ctx MSig) () mkeys (translate N dupP) :=
  ⟨retRule N, retRule_mem N dupP, placedRet N, ⟨[2], [], [3]⟩, 0⟩

/-- **Negative**: the family of the return taking the call's row has no hosted run, and no native
sequential run. -/
theorem ret_on_call_no_run (occupied : Finset ℕ) :
    (∀ {t : HostState MSig} {q : Presented ([] : Ctx MSig) () t} {final : Finset ℕ},
      ¬ Rounds.HostedRun Counted.Example.startTwice startTwicePresented occupied [retOnCallMember] t q final) ∧
    ∀ u : NativeState MSig ℕ ([] : Ctx MSig) (),
      ¬ Interface.NativeIterated.Sequential (state mkeys Counted.Example.startTwice startTwicePresented occupied)
        ([retOnCallMember].map (Rounds.Member.live N Counted.Example.startTwice startTwicePresented occupied)) u := by
  have refused := ret_on_call_refused occupied 0
  refine ⟨fun {t q final} run => ?_, fun u run => ?_⟩
  · cases run with
    | cons _ _ admitted _ =>
        exact refused ((admits_iff N Counted.Example.startTwice startTwicePresented occupied (retRule_mem N dupP)
          (placedRet N) ⟨[2], [], [3]⟩ 0).mp admitted)
  · cases run with
    | cons _ _ realized _ => exact refused realized

/-! ## A guard refuses -/

/-- The row `eqn((g a b))`, with the start's private copy of the names for row `7`. -/
abbrev besideRow : Observation MSig (startArity mkeys) :=
  observe (eqnN N (instantiate (rowNames 7) Hosting.Composition.UnmatchedControls.gabT))

/-- The start of the query `(g $x b)` of the program with no equation, beside the row `eqn((g a b))`. -/
abbrev besideState : HostState MSig :=
  Hosting.Composition.startWith N Hosting.Composition.Controls.P0 Hosting.Composition.UnmatchedControls.qgx besideRow

/-- That state, presented. -/
def besidePresented : Presented ([] : Ctx MSig) () besideState where
  term o := if o = 1 then eqnN N (instantiate (rowNames 7) Hosting.Composition.UnmatchedControls.gabT)
    else (startPresented N Hosting.Composition.Controls.P0 Hosting.Composition.UnmatchedControls.qgx).term o
  label_eq o := by
    by_cases one : o = 1
    · subst one
      rfl
    · rw [if_neg one]
      show Function.update (startLabel N Hosting.Composition.Controls.P0 Hosting.Composition.UnmatchedControls.qgx)
        (Hosting.Composition.Controls.P0.equations.length + 1) besideRow o = _
      rw [Function.update_of_ne (a' := Hosting.Composition.Controls.P0.equations.length + 1) one]
      exact (startPresented N Hosting.Composition.Controls.P0 Hosting.Composition.UnmatchedControls.qgx).label_eq o

/-- **Negative, through the guard**: beside a row that matches the call at one solution, the none query
guard of `apply` with no matching equation refuses the hosted firing
(`Composition.UnmatchedControls.partial_match_stuck`), so the native step refuses its live firing: the
none check over shared rows reads the row at every solution, as the hosted check does. -/
theorem guard_refuses (occupied : Finset ℕ) (fuel : ℕ) :
    ¬ (live N besideState besidePresented occupied (placedUnmatched (κ := mkeys) N) ⟨[0], [], [2]⟩
      fuel).toNative.Realized := by
  rw [← admits_iff N besideState besidePresented occupied (unmatchedRule_mem N Hosting.Composition.Controls.P0)
    (placedUnmatched N) ⟨[0], [], [2]⟩ fuel]
  intro admitted
  exact Hosting.Composition.UnmatchedControls.partial_match_stuck _ ⟨_, admitted, rfl⟩

/-! ## A first-order collapse merges what the adapter keeps apart -/

/-- The native information frame of a firing at a hosted frame. -/
abbrev nativeFrame (F : Frame MSig) : Frame MSig :=
  ⟨ScopedVar (RuleLocal mkeys) ⊕ F.Names, ContextualActivatedStep.target (ruleLocals ([] : Ctx MSig) () mkeys) F.arity⟩

/-- An unknown of the left choice rule, opened by the canonical firing at `F` and carried to the
native information frame. -/
def choiceUnknown (F : Frame MSig) (scope : ℕ) (x : Unknown) : Observation MSig (nativeFrame F).arity :=
  instantiateObservation (infoExtension (placedLeft (κ := mkeys) N) F scope).assignment
    (instantiateObservation (RuleSyntax.Contextual.canonicalOpening MSig F (choiceLeftRule N).locals)
      (observe (unk (Γ := ([] : Ctx MSig)) (star := ()) x)))

/-- **The adapter keeps the two alternatives of a choice apart.** -/
theorem choice_unknowns_apart (F : Frame MSig) (scope : ℕ) :
    choiceUnknown F scope .first ≠ choiceUnknown F scope .second := by
  intro same
  have opened := info_injective _ _ _ same
  have terms := observe_injective opened
  have names := congrArg (support (S := MSig) (source := (RuleSyntax.Contextual.extend MSig F (choiceLeftRule N).locals).arity))
    terms
  change [Sum.inr Unknown.first] = [Sum.inr Unknown.second] at names
  simp at names

/-- **A first-order collapse merges them**: after `Frames.toFirstOrder` the two are one observation. -/
theorem choice_unknowns_collapse (F : Frame MSig) (scope : ℕ) :
    instantiateObservation (Interface.Frames.toFirstOrder (nativeFrame F)) (choiceUnknown F scope .first) =
      instantiateObservation (Interface.Frames.toFirstOrder (nativeFrame F)) (choiceUnknown F scope .second) := by
  unfold choiceUnknown
  rw [opened_term, opened_term]
  rfl

/-- **No solution of the empty knowledge identifies the two alternatives** in the native frame. -/
theorem adapter_does_not_entail (F : Frame MSig) (scope : ℕ) :
    ¬ (Interface.Frames.contextual MSig).Entails (a := nativeFrame F) [] (fun _ candidate =>
      instantiateObservation candidate (choiceUnknown F scope .first) =
        instantiateObservation candidate (choiceUnknown F scope .second)) := by
  intro entailed
  have atIdentity := entailed (nativeFrame F) (generator (nativeFrame F).arity)
    ((Interface.Frames.contextual MSig).models_nil (generator (nativeFrame F).arity))
  have same : choiceUnknown F scope .first = choiceUnknown F scope .second := by
    simpa only [instantiateObservation_identity] using atIdentity
  exact choice_unknowns_apart F scope same

/-- **After the collapse the identification is entailed.** -/
theorem collapse_entails (F : Frame MSig) (scope : ℕ) :
    (Interface.Frames.contextual MSig).Entails (a := Interface.Frames.firstOrderFrame MSig) [] (fun _ candidate =>
      instantiateObservation candidate
          (instantiateObservation (Interface.Frames.toFirstOrder (nativeFrame F)) (choiceUnknown F scope .first)) =
        instantiateObservation candidate
          (instantiateObservation (Interface.Frames.toFirstOrder (nativeFrame F)) (choiceUnknown F scope .second))) := by
  intro _ candidate _
  exact congrArg (instantiateObservation candidate) (choice_unknowns_collapse F scope)

#print axioms ledger_grows
#print axioms no_extension_at_old_ledger
#print axioms rule_scope_shared
#print axioms shift_pos
#print axioms call_admitted
#print axioms call_realized
#print axioms call_result
#print axioms call_return_residual
#print axioms call_jointly
#print axioms call_run
#print axioms competing_calls_not_apart
#print axioms competing_calls_not_compatible
#print axioms ret_on_call_no_run
#print axioms call_no_extension_at_old_ledger
#print axioms ret_on_call_refused
#print axioms guard_refuses
#print axioms choice_unknowns_apart
#print axioms choice_unknowns_collapse
#print axioms adapter_does_not_entail
#print axioms collapse_entails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative.Controls
