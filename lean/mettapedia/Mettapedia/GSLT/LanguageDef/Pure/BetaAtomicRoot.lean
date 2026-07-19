/-
# The Pure beta atomic root and its generic laws

This module packages the beta-aware elaborator behind the same atomic
`Refine(hole, head)` interface as the conversion-free root.  Because beta
normalization is deliberately fuel-bounded, root well-formedness includes a
structural elaborability derivation recording the successful bounded match at
each deterministic spine boundary; semantic soundness is discharged
separately through the declarative beta typing judgment.
-/

import Mettapedia.GSLT.LanguageDef.Pure.BetaAtomicRefinement

namespace Mettapedia.GSLT.LanguageDef.PureBetaAtomicRoot

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureRefinement
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBeta
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement

mutual
/-- Structural certificate that the canonical atomic trace elaborates a term at a target. -/
inductive ElaboratesTerm : Ctx → Nf → Expr → Prop where
  | lam {context domain body bodyTerm} :
      ElaboratesTerm (domain :: context) bodyTerm body →
      ElaboratesTerm context (.lam domain bodyTerm) (.pi domain body)
  | head {context index headType arguments expected} :
      ctxLookup context index = some headType →
      (∀ domain body, expected ≠ .pi domain body) →
      ElaboratesSpine context headType arguments expected →
      ElaboratesTerm context (.head index arguments) expected

/-- Structural certificate for every deterministic dependent-spine boundary. -/
inductive ElaboratesSpine : Ctx → Expr → List Nf → Expr → Prop where
  | nil {context headType expected} :
      (∀ domain body, headType ≠ .pi domain body) →
      conversionVerdict normalizationFuel headType expected = .convertible →
      ElaboratesSpine context headType [] expected
  | last {context domain body argument expected} :
      ElaboratesTerm context argument domain →
      conversionVerdict normalizationFuel
        (Expr.subst0 argument.erase body) expected = .convertible →
      ElaboratesSpine context (.pi domain body) [argument] expected
  | cons {context domain body argument nextArgument rest expected
      nextDomain nextBody} :
      ElaboratesTerm context argument domain →
      Expr.subst0 argument.erase body = .pi nextDomain nextBody →
      conversionVerdict normalizationFuel
        (Expr.subst0 argument.erase body) expected = .normalFormsDiffer →
      ElaboratesSpine context (.pi nextDomain nextBody)
        (nextArgument :: rest) expected →
      ElaboratesSpine context (.pi domain body)
        (argument :: nextArgument :: rest) expected
end

mutual
/-- Executable reflection of canonical term elaborability. -/
def elaboratesTermFuel : Nat → Ctx → Nf → Expr → Bool
  | 0, _, _, _ => false
  | fuel + 1, context, .lam domain bodyTerm, .pi expectedDomain expectedBody =>
      decide (domain = expectedDomain) &&
        elaboratesTermFuel fuel (domain :: context) bodyTerm expectedBody
  | _fuel + 1, _, .lam _ _, _ => false
  | _fuel + 1, _, .head _ _, .pi _ _ => false
  | fuel + 1, context, .head index arguments, expected =>
      match ctxLookup context index with
      | none => false
      | some headType =>
          elaboratesSpineFuel fuel context headType arguments expected

/-- Executable reflection of every deterministic dependent-spine boundary. -/
def elaboratesSpineFuel : Nat → Ctx → Expr → List Nf → Expr → Bool
  | 0, _, _, _, _ => false
  | _fuel + 1, _, .pi _ _, [], _ => false
  | _fuel + 1, _, headType, [], expected =>
      decide (conversionVerdict normalizationFuel headType expected = .convertible)
  | fuel + 1, context, .pi domain body, [argument], expected =>
      elaboratesTermFuel fuel context argument domain &&
        decide (conversionVerdict normalizationFuel
          (Expr.subst0 argument.erase body) expected = .convertible)
  | fuel + 1, context, .pi domain body,
      argument :: nextArgument :: rest, expected =>
      elaboratesTermFuel fuel context argument domain &&
        match Expr.subst0 argument.erase body with
        | .pi nextDomain nextBody =>
            decide (conversionVerdict normalizationFuel
              (.pi nextDomain nextBody) expected = .normalFormsDiffer) &&
            elaboratesSpineFuel fuel context (.pi nextDomain nextBody)
              (nextArgument :: rest) expected
        | _ => false
  | _fuel + 1, _, _, _ :: _, _ => false
end

def elaboratesTerm (context : Ctx) (term : Nf) (expected : Expr) : Bool :=
  elaboratesTermFuel (term.weight + 1) context term expected

def elaboratesSpine (context : Ctx) (headType : Expr)
    (arguments : List Nf) (expected : Expr) : Bool :=
  elaboratesSpineFuel (Nf.listWeight arguments + 1)
    context headType arguments expected

mutual
/-- Successful executable elaborability yields its structural term certificate. -/
theorem elaboratesFuel_sound : ∀ fuel,
    (∀ context term expected,
      elaboratesTermFuel fuel context term expected = true →
        ElaboratesTerm context term expected) ∧
    (∀ context headType arguments expected,
      elaboratesSpineFuel fuel context headType arguments expected = true →
        ElaboratesSpine context headType arguments expected) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intro <;>
        simp [elaboratesTermFuel, elaboratesSpineFuel] at *
  | succ fuel ih =>
      constructor
      · intro context term expected helaborates
        cases term with
        | lam domain bodyTerm =>
            cases expected with
            | pi expectedDomain expectedBody =>
                simp only [elaboratesTermFuel, Bool.and_eq_true] at helaborates
                have hdomain : domain = expectedDomain :=
                  of_decide_eq_true helaborates.1
                subst expectedDomain
                exact ElaboratesTerm.lam (ih.1 _ _ _ helaborates.2)
            | sort => simp [elaboratesTermFuel] at helaborates
            | bvar index => simp [elaboratesTermFuel] at helaborates
            | lam expectedDomain expectedBody =>
                simp [elaboratesTermFuel] at helaborates
            | app fn argument => simp [elaboratesTermFuel] at helaborates
        | head index arguments =>
            cases expected with
            | pi domain body => simp [elaboratesTermFuel] at helaborates
            | sort =>
                simp only [elaboratesTermFuel] at helaborates
                cases hlookup : ctxLookup context index with
                | none => simp [hlookup] at helaborates
                | some headType =>
                    exact ElaboratesTerm.head hlookup (by intro; simp)
                      (ih.2 _ _ _ _ (by simpa [hlookup] using helaborates))
            | bvar targetIndex =>
                simp only [elaboratesTermFuel] at helaborates
                cases hlookup : ctxLookup context index with
                | none => simp [hlookup] at helaborates
                | some headType =>
                    exact ElaboratesTerm.head hlookup (by intro; simp)
                      (ih.2 _ _ _ _ (by simpa [hlookup] using helaborates))
            | lam targetDomain targetBody =>
                simp only [elaboratesTermFuel] at helaborates
                cases hlookup : ctxLookup context index with
                | none => simp [hlookup] at helaborates
                | some headType =>
                    exact ElaboratesTerm.head hlookup (by intro; simp)
                      (ih.2 _ _ _ _ (by simpa [hlookup] using helaborates))
            | app targetFn targetArgument =>
                simp only [elaboratesTermFuel] at helaborates
                cases hlookup : ctxLookup context index with
                | none => simp [hlookup] at helaborates
                | some headType =>
                    exact ElaboratesTerm.head hlookup (by intro; simp)
                      (ih.2 _ _ _ _ (by simpa [hlookup] using helaborates))
      · intro context headType arguments expected helaborates
        cases arguments with
        | nil =>
            cases headType with
            | pi domain body => simp [elaboratesSpineFuel] at helaborates
            | sort =>
                exact ElaboratesSpine.nil (by intro; simp)
                  (of_decide_eq_true (by simpa [elaboratesSpineFuel] using helaborates))
            | bvar index =>
                exact ElaboratesSpine.nil (by intro; simp)
                  (of_decide_eq_true (by simpa [elaboratesSpineFuel] using helaborates))
            | lam domain body =>
                exact ElaboratesSpine.nil (by intro; simp)
                  (of_decide_eq_true (by simpa [elaboratesSpineFuel] using helaborates))
            | app fn argument =>
                exact ElaboratesSpine.nil (by intro; simp)
                  (of_decide_eq_true (by simpa [elaboratesSpineFuel] using helaborates))
        | cons argument rest =>
            cases rest with
            | nil =>
                cases headType with
                | pi domain body =>
                    simp only [elaboratesSpineFuel, Bool.and_eq_true] at helaborates
                    exact ElaboratesSpine.last
                      (ih.1 _ _ _ helaborates.1)
                      (of_decide_eq_true helaborates.2)
                | sort => simp [elaboratesSpineFuel] at helaborates
                | bvar index => simp [elaboratesSpineFuel] at helaborates
                | lam domain body => simp [elaboratesSpineFuel] at helaborates
                | app fn arg => simp [elaboratesSpineFuel] at helaborates
            | cons nextArgument rest =>
                cases headType with
                | pi domain body =>
                    simp only [elaboratesSpineFuel, Bool.and_eq_true] at helaborates
                    rcases helaborates with ⟨hargument, htail⟩
                    generalize hnext : Expr.subst0 argument.erase body = nextType at htail
                    cases nextType with
                    | pi nextDomain nextBody =>
                        simp only [Bool.and_eq_true] at htail
                        have hconversion :
                            conversionVerdict normalizationFuel
                                (Expr.subst0 argument.erase body) expected =
                              .normalFormsDiffer := by
                          rw [hnext]
                          exact of_decide_eq_true htail.1
                        exact ElaboratesSpine.cons
                          (ih.1 _ _ _ hargument) hnext
                          hconversion
                          (ih.2 _ _ _ _ htail.2)
                    | sort => simp at htail
                    | bvar index => simp at htail
                    | lam nextDomain nextBody => simp at htail
                    | app fn arg => simp at htail
                | sort => simp [elaboratesSpineFuel] at helaborates
                | bvar index => simp [elaboratesSpineFuel] at helaborates
                | lam domain body => simp [elaboratesSpineFuel] at helaborates
                | app fn arg => simp [elaboratesSpineFuel] at helaborates
end

theorem elaboratesTerm_sound {context : Ctx} {term : Nf} {expected : Expr}
    (helaborates : elaboratesTerm context term expected = true) :
    ElaboratesTerm context term expected :=
  (elaboratesFuel_sound (term.weight + 1)).1 _ _ _ helaborates

/-- Empty continuation preserves every classified elaborator outcome. -/
@[simp] theorem runFromResult_nil (result : CheckResult Core) :
    runFromResult [] result = result := by
  cases result <;> rfl

/-- The canonical encoder emits no actions for an empty argument spine. -/
@[simp] theorem encodeArgsFuel_nil (fuel : Nat) (context : Ctx) :
    PureAtomicRefinement.encodeArgsFuel fuel context [] = [] := by
  cases fuel <;> rfl

/-- Canonical encoding simulates certified term elaboration, parametrically in frames. -/
theorem encodeFuel_simulation : ∀ fuel,
    (∀ context term expected frames,
      term.weight < fuel → ElaboratesTerm context term expected →
      rawRunResult
          (PureAtomicRefinement.encodeNfFuel fuel context term)
          (prepare 0 context expected frames) =
        PureBetaAtomicRefinement.deliver term frames) ∧
    (∀ context headType arguments expected head builtArguments frames,
      Nf.listWeight arguments < fuel →
      ElaboratesSpine context headType arguments expected →
      runFromResult
          (PureAtomicRefinement.encodeArgsFuel fuel context arguments)
          (PureBetaAtomicRefinement.startSpine
            context expected frames head builtArguments headType) =
        PureBetaAtomicRefinement.deliver
          (.head head (builtArguments ++ arguments)) frames) := by
  intro fuel
  induction fuel with
  | zero => constructor <;> intro <;> omega
  | succ fuel ih =>
      constructor
      · intro context term expected frames hweight helaborates
        cases helaborates with
        | lam hbody =>
            simp only [Nf.weight] at hweight
            simpa [PureAtomicRefinement.encodeNfFuel, prepare,
              PureBetaAtomicRefinement.deliver] using
              ih.1 _ _ _ (.lambda _ :: frames) (by omega) hbody
        | @head _ index headType arguments expected hlookup hnotPi hspine =>
            simp only [Nf.weight] at hweight
            have htail := ih.2 context headType arguments expected index [] frames
              (by omega) hspine
            cases expected with
            | pi domain body => exact False.elim (hnotPi domain body rfl)
            | sort =>
                simpa [PureAtomicRefinement.encodeNfFuel, prepare, rawRunResult,
                  rawRefineResult, hlookup, runFromResult] using htail
            | bvar targetIndex =>
                simpa [PureAtomicRefinement.encodeNfFuel, prepare, rawRunResult,
                  rawRefineResult, hlookup, runFromResult] using htail
            | lam targetDomain targetBody =>
                simpa [PureAtomicRefinement.encodeNfFuel, prepare, rawRunResult,
                  rawRefineResult, hlookup, runFromResult] using htail
            | app targetFn targetArgument =>
                simpa [PureAtomicRefinement.encodeNfFuel, prepare, rawRunResult,
                  rawRefineResult, hlookup, runFromResult] using htail
      · intro context headType arguments expected head builtArguments frames
          hweight helaborates
        cases helaborates with
        | @nil _ headType expected hnotPi hconversion =>
            cases headType with
            | pi domain body => exact False.elim (hnotPi domain body rfl)
            | sort =>
                simp [PureAtomicRefinement.encodeArgsFuel,
                  PureBetaAtomicRefinement.startSpine, hconversion]
            | bvar index =>
                simp [PureAtomicRefinement.encodeArgsFuel,
                  PureBetaAtomicRefinement.startSpine, hconversion]
            | lam domain body =>
                simp [PureAtomicRefinement.encodeArgsFuel,
                  PureBetaAtomicRefinement.startSpine, hconversion]
            | app fn argument =>
                simp [PureAtomicRefinement.encodeArgsFuel,
                  PureBetaAtomicRefinement.startSpine, hconversion]
        | @last _ domain body argument expected hargument hconversion =>
            simp only [Nf.listWeight] at hweight
            have hargumentRun := ih.1 context argument domain
              (.spine context head builtArguments body expected :: frames)
              (by omega) hargument
            simp only [PureAtomicRefinement.encodeArgsFuel, encodeArgsFuel_nil,
              List.append_nil]
            change
              runFromResult
                  (PureAtomicRefinement.encodeNfFuel fuel context argument)
                  (.ok (prepare 0 context domain
                    (.spine context head builtArguments body expected :: frames))) =
                PureBetaAtomicRefinement.deliver
                  (.head head (builtArguments ++ [argument])) frames
            simp only [runFromResult]
            rw [hargumentRun]
            simp [PureBetaAtomicRefinement.deliver, hconversion]
        | @cons _ domain body argument nextArgument rest expected
            nextDomain nextBody hargument hnext hconversion hrest =>
            simp only [Nf.listWeight] at hweight
            have hargumentRun := ih.1 context argument domain
              (.spine context head builtArguments body expected :: frames)
              (by omega) hargument
            have hrestWeight :
                Nf.listWeight (nextArgument :: rest) < fuel := by
              simp only [Nf.listWeight]
              omega
            have hrestRun := ih.2 context (.pi nextDomain nextBody)
              (nextArgument :: rest) expected head
              (builtArguments ++ [argument]) frames hrestWeight hrest
            have hconversion' :
                conversionVerdict normalizationFuel (.pi nextDomain nextBody) expected =
                  .normalFormsDiffer := by
              simpa [hnext] using hconversion
            simp [PureBetaAtomicRefinement.startSpine, runFromResult] at hrestRun
            change
              runFromResult
                  (PureAtomicRefinement.encodeNfFuel fuel context argument ++
                    PureAtomicRefinement.encodeArgsFuel fuel context
                      (nextArgument :: rest))
                  (.ok (prepare 0 context domain
                    (.spine context head builtArguments body expected :: frames))) =
                PureBetaAtomicRefinement.deliver
                  (.head head (builtArguments ++ argument :: nextArgument :: rest))
                  frames
            simp only [runFromResult, rawRunResult_append]
            rw [hargumentRun]
            simp only [PureBetaAtomicRefinement.deliver, hnext, hconversion']
            rw [hrestRun]
/-- Top-level canonical traces reach the independently checked terminal core. -/
theorem rawRun_encode {goal : Expr} {term : Nf}
    (helaborates : ElaboratesTerm [] term goal) :
    rawRunResult (PureAtomicRefinement.encode term) (prepare 0 [] goal []) =
      .ok (.done term) := by
  have hsimulation :=
    (encodeFuel_simulation (term.weight + 1)).1 [] term goal []
      (by omega) helaborates
  simpa [PureAtomicRefinement.encode, PureBetaAtomicRefinement.deliver] using
    hsimulation

/-- A root-well-formed program has both a semantic typing and a canonical trace certificate. -/
def RootWellFormed (goal : Expr) (term : Nf) : Prop :=
  (∃ inferred,
    CheckedHasType [] term inferred ∧
      conversionVerdict normalizationFuel inferred goal = .convertible) ∧
  elaboratesTerm [] term goal = true

theorem rootWellFormed_semantic {goal : Expr} {term : Nf}
    (hwellFormed : RootWellFormed goal term) :
    Mettapedia.GSLT.LanguageDef.PureBeta.HasType [] term goal := by
  rcases hwellFormed.1 with ⟨inferred, htype, hconversion⟩
  exact Mettapedia.GSLT.LanguageDef.PureBeta.HasType.conv
    (checkedHasType_sound htype) (conversionVerdict_sound hconversion)

/-! ## The budgeted root and its exact finite completion decision -/

/-- Structural completion is distinct from independent terminal type checking. -/
inductive StructurallyDone : Core → Prop where
  | done (term : Nf) : StructurallyDone (.done term)

def coreDone : Core → Bool
  | .done _ => true
  | _ => false

theorem coreDone_eq_true_iff (core : Core) :
    coreDone core = true ↔ StructurallyDone core := by
  cases core with
  | done term => exact ⟨fun _ => .done term, fun _ => rfl⟩
  | needHole => exact ⟨by simp [coreDone], fun h => by cases h⟩
  | needHead => exact ⟨by simp [coreDone], fun h => by cases h⟩
  | needSpine => exact ⟨by simp [coreDone], fun h => by cases h⟩
  | finished => exact ⟨by simp [coreDone], fun h => by cases h⟩

/-- Every raw head choice available at the current atomic boundary. -/
def rawActions : Core → List AtomicAction
  | .needHole hole context _ _ =>
      (List.range context.length).map fun head => ⟨hole, head⟩
  | _ => []

/-- Exact bounded structural completion through beta-aware raw transitions. -/
def canComplete : Core → Nat → Bool
  | core, 0 => coreDone core
  | core, remaining + 1 =>
      coreDone core || (rawActions core).any fun action =>
        match rawRefineResult core action with
        | .ok next => canComplete next remaining
        | .rejected | .conversionFuelExhausted => false

/-- Every successful raw transition occurs in the finite head enumeration. -/
theorem rawRefine_mem_rawActions {core next : Core} {action : AtomicAction}
    (hstep : rawRefineResult core action = .ok next) :
    action ∈ rawActions core := by
  cases core with
  | needHole hole context expected frames =>
      simp only [rawRefineResult] at hstep
      by_cases hhole : action.hole = hole
      · cases hlookup : ctxLookup context action.head with
        | none => simp [hhole, hlookup] at hstep
        | some headType =>
            simp only [rawActions, List.mem_map]
            exact
              ⟨action.head,
                List.mem_range.mpr (ctxLookup_some_lt hlookup), by
                  cases action
                  simp only [RefineAction.mk.injEq]
                  exact ⟨hhole.symm, trivial⟩⟩
      · simp [hhole] at hstep
  | needHead => simp [rawRefineResult] at hstep
  | needSpine => simp [rawRefineResult] at hstep
  | done => simp [rawRefineResult] at hstep
  | finished => simp [rawRefineResult] at hstep

/-- A successful raw suffix is a constructive bounded-completion certificate. -/
theorem canComplete_of_rawRun :
    ∀ (actions : List AtomicAction) (core finalCore : Core) (remaining : Nat),
      actions.length ≤ remaining →
      rawRunResult actions core = .ok finalCore →
      coreDone finalCore = true →
      canComplete core remaining = true
  | [], core, finalCore, remaining, _hlength, hrun, hdone => by
      simp only [rawRunResult, CheckResult.ok.injEq] at hrun
      subst finalCore
      cases remaining <;> simp [canComplete, hdone]
  | action :: rest, core, finalCore, remaining, hlength, hrun, hdone => by
      cases remaining with
      | zero => simp at hlength
      | succ remaining =>
          simp only [rawRunResult] at hrun
          cases hstep : rawRefineResult core action with
          | rejected => simp [hstep] at hrun
          | conversionFuelExhausted => simp [hstep] at hrun
          | ok next =>
              rw [hstep] at hrun
              have htail : canComplete next remaining = true :=
                canComplete_of_rawRun rest next finalCore remaining
                  (by simpa using hlength) hrun hdone
              simp only [canComplete, Bool.or_eq_true]
              right
              simp only [List.any_eq_true]
              exact
                ⟨action, rawRefine_mem_rawActions hstep, by simp [hstep, htail]⟩

/-- Every positive bounded-completion decision returns an explicit raw suffix. -/
theorem canComplete_witness : ∀ (remaining : Nat) (core : Core),
    canComplete core remaining = true →
    ∃ actions finalCore,
      actions.length ≤ remaining ∧
      rawRunResult actions core = .ok finalCore ∧
      coreDone finalCore = true
  | 0, core, hcomplete => by
      exact ⟨[], core, by simp, rfl, by simpa [canComplete] using hcomplete⟩
  | remaining + 1, core, hcomplete => by
      simp only [canComplete, Bool.or_eq_true] at hcomplete
      rcases hcomplete with hdone | hbranch
      · exact ⟨[], core, by simp, rfl, hdone⟩
      · simp only [List.any_eq_true] at hbranch
        rcases hbranch with ⟨action, _hmem, hchosen⟩
        cases hstep : rawRefineResult core action with
        | rejected => simp [hstep] at hchosen
        | conversionFuelExhausted => simp [hstep] at hchosen
        | ok next =>
            simp only [hstep] at hchosen
            rcases canComplete_witness remaining next hchosen with
              ⟨rest, finalCore, hlength, hrun, hdone⟩
            exact
              ⟨action :: rest, finalCore, by simp; omega,
                by simp [rawRunResult, hstep, hrun], hdone⟩

/-- Interface holes are exact even on unreachable legacy-core constructors. -/
def holes : Core → List Nat
  | .needHole hole _ _ _ => [hole]
  | .needHead hole _ _ _ => [hole]
  | .needSpine hole _ _ _ _ _ => [hole]
  | .done _ => []
  | .finished _ => [0]

def initial (goal : Expr) (budget : Nat) : State :=
  { core := prepare 0 [] goal []
    tokensEmitted := 0
    maxLen := budget }

def terminal (state : State) : Prop := StructurallyDone state.core

def viable (state : State) : Prop :=
  coreDone state.core = true ∨
    state.tokensEmitted ≤ state.maxLen ∧
      canComplete state.core (state.maxLen - state.tokensEmitted) = true

/-- A budgeted step succeeds only when its successor still has a completion. -/
def step? (state : State) (action : AtomicAction) : Option State :=
  if state.tokensEmitted < state.maxLen then
    match rawRefineResult state.core action with
    | .ok next =>
        if canComplete next (state.maxLen - (state.tokensEmitted + 1)) then
          some
            { core := next
              tokensEmitted := state.tokensEmitted + 1
              maxLen := state.maxLen }
        else none
    | .rejected | .conversionFuelExhausted => none
  else none

def legalHeads (state : State) (hole : Nat) : List Nat :=
  match state.core with
  | .needHole current context _ _ =>
      if hole = current then
        (List.range context.length).filter fun head =>
          (step? state ⟨hole, head⟩).isSome
      else []
  | _ => []

/-- Root decoding requires both independent typing and canonical elaborability. -/
def rootDecode (goal : Expr) (trace : List AtomicAction) : Option Nf :=
  match decodeResult goal trace with
  | .ok term =>
      if elaboratesTerm [] term goal then some term else none
  | .rejected | .conversionFuelExhausted => none

def betaAtomicRoot (goal : Expr) : AtomicRoot where
  State := State
  Hole := Nat
  Head := Nat
  Program := Nf
  initial := initial goal
  holes := fun state => holes state.core
  legalHeads := legalHeads
  refine? := fun state hole head => step? state ⟨hole, head⟩
  terminal := terminal
  decode := rootDecode goal
  wellFormed := RootWellFormed goal
  programCost := fun term => (PureAtomicRefinement.encode term).length
  encode := PureAtomicRefinement.encode
  invariant := viable
  canComplete := viable
  budgetOK := fun budget =>
    canComplete (prepare 0 [] goal []) budget = true

/-- The beta root exposes at most one construction hole. -/
theorem betaAtomicRoot_holes_nodup (goal : Expr) (state : State) :
    ((betaAtomicRoot goal).holes state).Nodup := by
  rcases state with ⟨core, tokens, budget⟩
  cases core <;> simp [betaAtomicRoot, holes]

/-- Every beta-root head block is a filtered de Bruijn-index range. -/
theorem legalHeads_nodup (state : State) (hole : Nat) :
    (legalHeads state hole).Nodup := by
  rcases state with ⟨core, tokens, budget⟩
  cases core with
  | needHole current context expected frames =>
      by_cases heq : hole = current
      · simpa [legalHeads, heq] using
          (@List.nodup_range context.length).filter
            (fun head => (step?
              { core := .needHole current context expected frames
                tokensEmitted := tokens
                maxLen := budget }
              ⟨hole, head⟩).isSome)
      · simp [legalHeads, heq]
  | needHead => simp [legalHeads]
  | needSpine => simp [legalHeads]
  | done => simp [legalHeads]
  | finished => simp [legalHeads]

/-- The concrete factored legal-action support has no duplicate actions. -/
theorem betaAtomicRoot_legalActions_nodup (goal : Expr) (state : State) :
    ((betaAtomicRoot goal).legalActions state).Nodup := by
  apply (betaAtomicRoot goal).legalActions_nodup state
  · exact betaAtomicRoot_holes_nodup goal state
  · exact legalHeads_nodup state

theorem terminal_iff_holes_empty (state : State) :
    terminal state ↔ holes state.core = [] := by
  rcases state with ⟨core, tokens, budget⟩
  cases core with
  | done term => exact ⟨fun _ => rfl, fun _ => .done term⟩
  | needHole =>
      constructor
      · intro h; cases h
      · intro h; simp [holes] at h
  | needHead =>
      constructor
      · intro h; cases h
      · intro h; simp [holes] at h
  | needSpine =>
      constructor
      · intro h; cases h
      · intro h; simp [holes] at h
  | finished =>
      constructor
      · intro h; cases h
      · intro h; simp [holes] at h

theorem step_success_data {state next : State} {action : AtomicAction}
    (hstep : step? state action = some next) :
    state.tokensEmitted < state.maxLen ∧
    ∃ nextCore,
      rawRefineResult state.core action = .ok nextCore ∧
      canComplete nextCore (state.maxLen - (state.tokensEmitted + 1)) = true ∧
      next =
        { core := nextCore
          tokensEmitted := state.tokensEmitted + 1
          maxLen := state.maxLen } := by
  unfold step? at hstep
  by_cases htime : state.tokensEmitted < state.maxLen
  · simp only [htime, ↓reduceIte] at hstep
    cases hraw : rawRefineResult state.core action with
    | rejected => simp [hraw] at hstep
    | conversionFuelExhausted => simp [hraw] at hstep
    | ok nextCore =>
        by_cases hcomplete :
            canComplete nextCore (state.maxLen - (state.tokensEmitted + 1)) = true
        · simp [hraw, hcomplete] at hstep
          subst next
          exact ⟨htime, nextCore, rfl, hcomplete, rfl⟩
        · simp [hraw, hcomplete] at hstep
  · simp [htime] at hstep

theorem step_preserves_viable {state next : State} {action : AtomicAction}
    (_hviable : viable state) (hstep : step? state action = some next) :
    viable next := by
  rcases step_success_data hstep with
    ⟨htime, nextCore, hraw, hcomplete, rfl⟩
  by_cases hdone : coreDone nextCore = true
  · exact Or.inl hdone
  · right
    constructor
    · change state.tokensEmitted + 1 ≤ state.maxLen
      omega
    · exact hcomplete

theorem viable_of_step {state next : State} {action : AtomicAction}
    (hstep : step? state action = some next) : viable state := by
  rcases step_success_data hstep with
    ⟨htime, nextCore, hraw, hcomplete, rfl⟩
  right
  constructor
  · omega
  · have hremaining :
        state.maxLen - state.tokensEmitted =
          (state.maxLen - (state.tokensEmitted + 1)) + 1 := by omega
    rw [hremaining]
    simp only [canComplete, Bool.or_eq_true]
    right
    simp only [List.any_eq_true]
    exact ⟨action, rawRefine_mem_rawActions hraw, by simp [hraw, hcomplete]⟩

/-- Successful refinement is exactly membership in the factored legal support. -/
theorem exists_step_iff_legal (state : State) (hole head : Nat) :
    (∃ next, step? state ⟨hole, head⟩ = some next) ↔
      hole ∈ holes state.core ∧ head ∈ legalHeads state hole := by
  constructor
  · rintro ⟨next, hstep⟩
    rcases step_success_data hstep with
      ⟨_htime, nextCore, hraw, _hcomplete, _hnext⟩
    cases state with
    | mk core tokens budget =>
      cases core with
      | needHole current context expected frames =>
          simp only [rawRefineResult] at hraw
          by_cases hhole : hole = current
          · cases hlookup : ctxLookup context head with
            | none => simp [hhole, hlookup] at hraw
            | some headType =>
                subst hole
                constructor
                · simp [holes]
                · simp only [legalHeads, ↓reduceIte, List.mem_filter]
                  exact
                    ⟨List.mem_range.mpr (ctxLookup_some_lt hlookup), by
                      rw [hstep]
                      rfl⟩
          · simp [hhole] at hraw
      | needHead => simp [rawRefineResult] at hraw
      | needSpine => simp [rawRefineResult] at hraw
      | done => simp [rawRefineResult] at hraw
      | finished => simp [rawRefineResult] at hraw
  · rintro ⟨hhole, hhead⟩
    rcases state with ⟨core, tokens, budget⟩
    cases core with
    | needHole current context expected frames =>
        simp only [holes, List.mem_singleton] at hhole
        subst hole
        simp only [legalHeads, ↓reduceIte, List.mem_filter] at hhead
        rcases hhead with ⟨_hrange, hsome⟩
        cases hstep : step?
            { core := .needHole current context expected frames
              tokensEmitted := tokens
              maxLen := budget }
            ⟨current, head⟩ with
        | none => simp [hstep] at hsome
        | some next => exact ⟨next, rfl⟩
    | needHead => simp [legalHeads] at hhead
    | needSpine => simp [legalHeads] at hhead
    | done => simp [holes] at hhole
    | finished => simp [legalHeads] at hhead

/-- Execute budget-filtered atomic actions independently of a goal's decoder. -/
def filteredRun : List AtomicAction → State → Option State
  | [], state => some state
  | action :: rest, state => do
      let next ← step? state action
      filteredRun rest next

theorem interface_run_eq_filteredRun (goal : Expr)
    (actions : List AtomicAction) (state : State) :
    (betaAtomicRoot goal).asRefinementInterface.run actions state =
      filteredRun actions state := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simp only [RefinementInterface.run, filteredRun]
      change (step? state action).bind
        ((betaAtomicRoot goal).asRefinementInterface.run rest) =
        (step? state action).bind (filteredRun rest)
      cases hstep : step? state action with
      | none => rfl
      | some next => exact ih next

/-- A raw completed suffix survives the viability filter action-for-action. -/
theorem run_of_rawRun :
    ∀ (actions : List AtomicAction) (core finalCore : Core)
      (tokens budget : Nat),
      tokens + actions.length ≤ budget →
      rawRunResult actions core = .ok finalCore →
      coreDone finalCore = true →
      filteredRun actions
          { core := core, tokensEmitted := tokens, maxLen := budget } =
        some
          { core := finalCore
            tokensEmitted := tokens + actions.length
            maxLen := budget }
  | [], core, finalCore, tokens, budget, _hbudget, hrun, _hdone => by
      simp only [rawRunResult, CheckResult.ok.injEq] at hrun
      subst finalCore
      rfl
  | action :: rest, core, finalCore, tokens, budget, hbudget, hrun, hdone => by
      simp only [rawRunResult] at hrun
      cases hraw : rawRefineResult core action with
      | rejected => simp [hraw] at hrun
      | conversionFuelExhausted => simp [hraw] at hrun
      | ok nextCore =>
          rw [hraw] at hrun
          have htime : tokens < budget := by
            simp only [List.length_cons] at hbudget
            omega
          have htailLength :
              rest.length ≤ budget - (tokens + 1) := by
            simp only [List.length_cons] at hbudget
            omega
          have htailComplete :
              canComplete nextCore (budget - (tokens + 1)) = true :=
            canComplete_of_rawRun rest nextCore finalCore
              (budget - (tokens + 1)) htailLength hrun hdone
          have hfiltered :
              step?
                { core := core, tokensEmitted := tokens, maxLen := budget }
                action =
              some
                { core := nextCore
                  tokensEmitted := tokens + 1
                  maxLen := budget } := by
            simp [step?, htime, hraw, htailComplete]
          simp only [filteredRun, hfiltered]
          have htailBudget : (tokens + 1) + rest.length ≤ budget := by
            simp only [List.length_cons] at hbudget
            omega
          have htailRun := run_of_rawRun rest nextCore finalCore
            (tokens + 1) budget htailBudget hrun hdone
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htailRun

/-- Interface completion is exactly the finite viability predicate. -/
theorem hasCompletion_iff_viable (goal : Expr) (state : State) :
    (betaAtomicRoot goal).asRefinementInterface.HasCompletion state ↔ viable state := by
  constructor
  · rintro ⟨suffix, finalState, hrun, hterminal⟩
    rw [interface_run_eq_filteredRun goal] at hrun
    cases suffix with
    | nil =>
        have hstate : state = finalState := Option.some.inj hrun
        subst finalState
        exact Or.inl ((coreDone_eq_true_iff _).mpr hterminal)
    | cons action rest =>
        simp only [filteredRun] at hrun
        cases hstep : step? state action with
        | none => rw [hstep] at hrun; contradiction
        | some next => exact viable_of_step hstep
  · intro hviable
    rcases hviable with hdone | ⟨hbudget, hcomplete⟩
    · exact ⟨[], state, rfl, (coreDone_eq_true_iff _).mp hdone⟩
    · rcases canComplete_witness
          (state.maxLen - state.tokensEmitted) state.core hcomplete with
        ⟨suffix, finalCore, hlength, hraw, hfinalDone⟩
      have hrunBudget : state.tokensEmitted + suffix.length ≤ state.maxLen := by
        omega
      let finalState : State :=
        { core := finalCore
          tokensEmitted := state.tokensEmitted + suffix.length
          maxLen := state.maxLen }
      have hrun := run_of_rawRun suffix state.core finalCore
        state.tokensEmitted state.maxLen hrunBudget hraw hfinalDone
      exact
        ⟨suffix, finalState, by
            rw [interface_run_eq_filteredRun goal]
            exact hrun,
          (coreDone_eq_true_iff _).mp hfinalDone⟩

theorem decode_eq_some_of_result {goal : Expr} {trace : List AtomicAction}
    {term : Nf} (hdecode : decodeResult goal trace = .ok term) :
    PureBetaAtomicRefinement.decode goal trace = some term := by
  unfold PureBetaAtomicRefinement.decode
  simp [hdecode, CheckResult.toOption]

theorem result_eq_ok_of_decode {goal : Expr} {trace : List AtomicAction}
    {term : Nf} (hdecode : PureBetaAtomicRefinement.decode goal trace = some term) :
    decodeResult goal trace = .ok term := by
  unfold PureBetaAtomicRefinement.decode at hdecode
  cases hresult : decodeResult goal trace with
  | rejected => simp [hresult, CheckResult.toOption] at hdecode
  | conversionFuelExhausted => simp [hresult, CheckResult.toOption] at hdecode
  | ok decoded =>
      simp [hresult, CheckResult.toOption] at hdecode
      subst decoded
      rfl

theorem rootDecode_eq_some_iff {goal : Expr} {trace : List AtomicAction}
    {term : Nf} :
    rootDecode goal trace = some term ↔
      decodeResult goal trace = .ok term ∧
        elaboratesTerm [] term goal = true := by
  unfold rootDecode
  cases hresult : decodeResult goal trace with
  | rejected => simp
  | conversionFuelExhausted => simp
  | ok decoded =>
      by_cases helaborates : elaboratesTerm [] decoded goal = true
      · simp [helaborates]
        intro heq
        subst term
        exact helaborates
      · simp [helaborates]
        intro heq
        subst term
        cases hbool : elaboratesTerm [] decoded goal <;> simp_all

/-- The root decoder returns exactly programs satisfying its executable contract. -/
theorem rootDecode_sound {goal : Expr} {trace : List AtomicAction} {term : Nf}
    (hdecode : rootDecode goal trace = some term) :
    RootWellFormed goal term := by
  rcases rootDecode_eq_some_iff.mp hdecode with ⟨hresult, helaborates⟩
  exact ⟨decodeResult_checked hresult, helaborates⟩

/-- Canonical traces receive the independently checked successful result. -/
theorem decodeResult_encode {goal : Expr} {term : Nf}
    (hwellFormed : RootWellFormed goal term) :
    decodeResult goal (PureAtomicRefinement.encode term) = .ok term := by
  rcases hwellFormed.1 with ⟨inferred, htype, hconversion⟩
  have hrun := rawRun_encode (elaboratesTerm_sound hwellFormed.2)
  simp [decodeResult, hrun, terminalResult, inferNf_complete htype, hconversion]

theorem decode_encode {goal : Expr} {term : Nf}
    (hwellFormed : RootWellFormed goal term) :
    PureBetaAtomicRefinement.decode goal (PureAtomicRefinement.encode term) =
      some term := by
  exact decode_eq_some_of_result (decodeResult_encode hwellFormed)

theorem rootDecode_encode {goal : Expr} {term : Nf}
    (hwellFormed : RootWellFormed goal term) :
    rootDecode goal (PureAtomicRefinement.encode term) = some term := by
  exact rootDecode_eq_some_iff.mpr ⟨decodeResult_encode hwellFormed, hwellFormed.2⟩

/-! ## Discharged generic root laws -/

/-- All generic atomic-root obligations hold for the beta-aware root. -/
def betaAtomicLaws (goal : Expr) : AtomicRootLaws (betaAtomicRoot goal) where
  refine_iff_legal := by
    intro state hole head
    change
      (∃ next : State, step? state ⟨hole, head⟩ = some next) ↔
        hole ∈ holes state.core ∧ head ∈ legalHeads state hole
    exact exists_step_iff_legal state hole head
  interfaceLaws := {
    legal_iff_apply := by
      intro state action
      change
        (action.hole ∈ holes state.core ∧
          action.head ∈ legalHeads state action.hole) ↔
        ∃ next, step? state action = some next
      exact (exists_step_iff_legal state action.hole action.head).symm
    terminal_iff_holes_empty := terminal_iff_holes_empty
    initial_invariant := by
      intro budget hbudget
      change canComplete (prepare 0 [] goal []) budget = true at hbudget
      change viable (initial goal budget)
      exact Or.inr ⟨by simp [initial], by simpa [initial] using hbudget⟩
    apply_invariant := by
      intro state action next hviable hstep
      exact step_preserves_viable hviable hstep
    sound := by
      intro budget trace finalState term _hrun _hterminal hdecode
      exact rootDecode_sound hdecode
    complete := by
      intro budget term _hbudget hwellFormed hcost
      change RootWellFormed goal term at hwellFormed
      change (PureAtomicRefinement.encode term).length ≤ budget at hcost
      have hraw := rawRun_encode (elaboratesTerm_sound hwellFormed.2)
      have hfiltered :=
        run_of_rawRun (PureAtomicRefinement.encode term)
          (prepare 0 [] goal []) (.done term) 0 budget (by simpa using hcost) hraw rfl
      let finalState : State :=
        { core := .done term
          tokensEmitted := (PureAtomicRefinement.encode term).length
          maxLen := budget }
      refine ⟨finalState, ?_, ?_, ?_⟩
      · change
          (betaAtomicRoot goal).asRefinementInterface.run
              (PureAtomicRefinement.encode term) (initial goal budget) =
            some finalState
        rw [interface_run_eq_filteredRun]
        change
          filteredRun (PureAtomicRefinement.encode term) (initial goal budget) =
            some finalState
        simpa [initial, finalState] using hfiltered
      · exact StructurallyDone.done term
      · exact rootDecode_encode hwellFormed
    invariant_canComplete := by
      intro state hviable
      exact hviable
    canComplete_iff_hasCompletion := by
      intro state
      exact (hasCompletion_iff_viable goal state).symm
  }

/-- Every accepted beta-root trace denotes a declaratively typed Pure term. -/
theorem betaRoot_accepts_sound {goal : Expr} {budget : Nat}
    {trace : List AtomicAction} {term : Nf}
    (haccepts :
      (betaAtomicRoot goal).asRefinementInterface.Accepts budget trace term) :
    RootWellFormed goal term :=
  (betaAtomicLaws goal).interfaceLaws.accepts_sound haccepts

/-- Every in-budget root-well-formed term has its canonical accepted trace. -/
theorem betaRoot_wellFormed_reachable {goal : Expr} {budget : Nat} {term : Nf}
    (hbudget : (betaAtomicRoot goal).budgetOK budget)
    (hwellFormed : RootWellFormed goal term)
    (hcost : (betaAtomicRoot goal).programCost term ≤ budget) :
    (betaAtomicRoot goal).asRefinementInterface.Accepts budget
      ((betaAtomicRoot goal).encode term) term :=
  (betaAtomicLaws goal).interfaceLaws.wellFormed_reachable
    hbudget hwellFormed hcost

/-- No state reachable under the registered budget is structurally stranded. -/
theorem betaRoot_reachable_hasCompletion {goal : Expr} {budget : Nat}
    (hbudget : (betaAtomicRoot goal).budgetOK budget)
    {state : State}
    (hreachable :
      (betaAtomicRoot goal).asRefinementInterface.Reachable budget state) :
    (betaAtomicRoot goal).asRefinementInterface.HasCompletion state :=
  (betaAtomicLaws goal).interfaceLaws.reachable_hasCompletion hbudget hreachable

/-- Reordering an exact legal-action support cannot change ranked acceptance. -/
theorem betaRoot_ordering_invariant {goal : Expr}
    (first second : State → List AtomicAction)
    (hfirst : ∀ state action,
      action ∈ first state ↔ action ∈ (betaAtomicRoot goal).legalActions state)
    (hpermutation : ∀ state, (first state).Perm (second state))
    {budget : Nat} {trace : List AtomicAction} {term : Nf} :
    (betaAtomicRoot goal).asRefinementInterface.RankedAccepts
        first budget trace term ↔
      (betaAtomicRoot goal).asRefinementInterface.RankedAccepts
        second budget trace term :=
  (betaAtomicLaws goal).rankedAcceptance_invariant_of_legalActions
    first second hfirst hpermutation

/-! ## Executable positive and negative root fixtures -/

def betaRootIdentityGoal : Expr := .pi .sort .sort

def betaRootIdentityTerm : Nf := .lam .sort (.head 0 [])

theorem betaRootIdentity_wellFormed :
    RootWellFormed betaRootIdentityGoal betaRootIdentityTerm := by
  refine ⟨⟨betaRootIdentityGoal, inferNf_sound (by decide), by decide⟩, by decide⟩

example : rootDecode betaRootIdentityGoal [⟨0, 0⟩] =
    some betaRootIdentityTerm := by rfl

example : rootDecode betaRootIdentityGoal [⟨0, 1⟩] = none := by rfl

#print axioms elaboratesTerm_sound
#print axioms rootWellFormed_semantic
#print axioms rootDecode_sound
#print axioms betaRoot_accepts_sound
#print axioms betaRoot_wellFormed_reachable
#print axioms betaRoot_reachable_hasCompletion
#print axioms betaRoot_ordering_invariant
#print axioms betaRootIdentity_wellFormed

end Mettapedia.GSLT.LanguageDef.PureBetaAtomicRoot
