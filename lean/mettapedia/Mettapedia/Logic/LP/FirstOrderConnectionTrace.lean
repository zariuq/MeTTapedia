import Mettapedia.Logic.LP.Unification
import Mettapedia.Logic.LP.UnificationComplete
import Mathlib.Data.List.TakeDrop

/-!
# First-Order Connection Trace Checker (PeTTa `proof_fo` Shape)

This module provides a minimal FO trace/checker layer aligned with the pure-PeTTa
`leancop_pure_fo_poc.metta` proof object style:

- signed FO literals over `LP.Atom`
- `step_reduce` / `step_extend` trace format
- replay checker with unification + substitution propagation
- soundness theorem: accepted trace implies FO trace-derivability
-/

namespace Mettapedia.Logic.LP

open scoped Classical

noncomputable section

section FirstOrderConnection

variable {σ : LPSignature}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
variable [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

/-- Signed FO literal. -/
inductive ConnFOLit (σ : LPSignature) where
  | pos : Atom σ → ConnFOLit σ
  | neg : Atom σ → ConnFOLit σ

abbrev ConnFOClause (σ : LPSignature) := List (ConnFOLit σ)
abbrev ConnFOCNF (σ : LPSignature) := List (ConnFOClause σ)

noncomputable instance : DecidableEq (ConnFOLit σ) := Classical.decEq _

/-- Literal complement. -/
def ConnFOLit.complement : ConnFOLit σ → ConnFOLit σ
  | .pos a => .neg a
  | .neg a => .pos a

/-- Apply substitution to FO literal. -/
def Subst.applyConnFOLit (θ : Subst σ) : ConnFOLit σ → ConnFOLit σ
  | .pos a => .pos (θ.applyAtom a)
  | .neg a => .neg (θ.applyAtom a)

/-- Apply substitution to FO clause. -/
def Subst.applyConnFOClause (θ : Subst σ) (c : ConnFOClause σ) : ConnFOClause σ :=
  c.map θ.applyConnFOLit

/-- Unify a literal with the complement of another literal. -/
def unifyComplementLit? (fuel : Nat) (l k : ConnFOLit σ) : Option (Subst σ) :=
  match l, k with
  | .pos a, .neg b => unifyAtoms a b fuel
  | .neg a, .pos b => unifyAtoms a b fuel
  | _, _ => none

/-- FO proof steps aligned with PeTTa `proof_fo` replay shape. -/
inductive FOProofStep (σ : LPSignature) where
  /-- Reduction against a path literal. -/
  | step_reduce : ConnFOLit σ → FOProofStep σ
  /-- Extension via matrix clause and selected clause literal. -/
  | step_extend : ConnFOClause σ → ConnFOLit σ → FOProofStep σ

abbrev FOProofTrace (σ : LPSignature) := List (FOProofStep σ)

/-- FO proof object aligned with PeTTa `(proof_fo fuel root trace)`. -/
structure FOProofObj (σ : LPSignature) where
  fuel : Nat
  root : ConnFOClause σ
  trace : FOProofTrace σ

/--
FO replay checker:
current goal literal is unified with a complement from path (`step_reduce`) or matrix
clause (`step_extend`), then substitutions are propagated to remaining goals/path.
-/
def replayFO (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ConnFOClause σ → ConnFOClause σ → FOProofTrace σ → Bool
  | goals, _path, [] =>
      decide (goals = [])
  | goals, path, step :: steps =>
      match goals with
      | [] => false
      | g :: gr =>
          match step with
          | .step_reduce pl =>
              if pl ∈ path then
                match unifyComplementLit? (σ := σ) uFuel g pl with
                | some θ =>
                    let gr1 := θ.applyConnFOClause gr
                    let path1 := θ.applyConnFOClause (g :: path)
                    replayFO clauses uFuel gr1 path1 steps
                | none => false
              else
                false
          | .step_extend clause clit =>
              if clause ∈ clauses then
                if clit ∈ clause then
                  match unifyComplementLit? (σ := σ) uFuel g clit with
                  | some θ =>
                      let clauseRem := clause.erase clit
                      let goals1 := θ.applyConnFOClause (clauseRem ++ gr)
                      let path1 := θ.applyConnFOClause (g :: path)
                      replayFO clauses uFuel goals1 path1 steps
                  | none => false
                else
                  false
              else
                false

/-- FO trace-indexed derivability semantics for replay. -/
inductive TraceDerivableFO (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ConnFOClause σ → ConnFOClause σ → FOProofTrace σ → Prop where
  | done (path : ConnFOClause σ) :
      TraceDerivableFO clauses uFuel [] path []
  | reduce
      (g : ConnFOLit σ) (gr path : ConnFOClause σ) (pl : ConnFOLit σ)
      (steps : FOProofTrace σ) (θ : Subst σ)
      (hMem : pl ∈ path)
      (hUnify : unifyComplementLit? (σ := σ) uFuel g pl = some θ)
      (hSub : TraceDerivableFO clauses uFuel
          (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)) steps) :
      TraceDerivableFO clauses uFuel (g :: gr) path (.step_reduce pl :: steps)
  | extend
      (g : ConnFOLit σ) (gr path : ConnFOClause σ)
      (clause : ConnFOClause σ) (clit : ConnFOLit σ)
      (steps : FOProofTrace σ) (θ : Subst σ)
      (hClause : clause ∈ clauses)
      (hLit : clit ∈ clause)
      (hUnify : unifyComplementLit? (σ := σ) uFuel g clit = some θ)
      (hSub : TraceDerivableFO clauses uFuel
          (θ.applyConnFOClause (clause.erase clit ++ gr))
          (θ.applyConnFOClause (g :: path))
          steps) :
      TraceDerivableFO clauses uFuel (g :: gr) path (.step_extend clause clit :: steps)

/-- Replay acceptance implies FO trace-derivability. -/
theorem traceDerivableFO_of_replayFO_true
    (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ (goals path : ConnFOClause σ) (trace : FOProofTrace σ),
      replayFO (σ := σ) clauses uFuel goals path trace = true →
      TraceDerivableFO clauses uFuel goals path trace
  | goals, path, [], h => by
      have hnil : goals = [] := by
        simpa [replayFO] using (decide_eq_true_iff (p := goals = [])).1 h
      subst hnil
      exact TraceDerivableFO.done path
  | [], path, _ :: _, h => by
      simp [replayFO] at h
  | g :: gr, path, step :: steps, h => by
      cases step with
      | step_reduce pl =>
          by_cases hMem : pl ∈ path
          · simp [replayFO, hMem] at h
            cases hUnify : unifyComplementLit? (σ := σ) uFuel g pl with
            | none =>
                simp [hUnify] at h
            | some θ =>
                have hSub :
                    replayFO clauses uFuel
                      (θ.applyConnFOClause gr)
                      (θ.applyConnFOClause (g :: path))
                      steps = true := by
                  simpa [hUnify] using h
                exact TraceDerivableFO.reduce g gr path pl steps θ hMem hUnify
                  (traceDerivableFO_of_replayFO_true clauses uFuel
                    (θ.applyConnFOClause gr)
                    (θ.applyConnFOClause (g :: path))
                    steps hSub)
          · simp [replayFO, hMem] at h
      | step_extend clause clit =>
          by_cases hClause : clause ∈ clauses
          · by_cases hLit : clit ∈ clause
            · simp [replayFO, hClause, hLit] at h
              cases hUnify : unifyComplementLit? (σ := σ) uFuel g clit with
              | none =>
                  simp [hUnify] at h
              | some θ =>
                  have hSub :
                      replayFO clauses uFuel
                        (θ.applyConnFOClause (clause.erase clit ++ gr))
                        (θ.applyConnFOClause (g :: path))
                        steps = true := by
                    simpa [hUnify] using h
                  exact TraceDerivableFO.extend g gr path clause clit steps θ
                    hClause hLit hUnify
                    (traceDerivableFO_of_replayFO_true clauses uFuel
                      (θ.applyConnFOClause (clause.erase clit ++ gr))
                      (θ.applyConnFOClause (g :: path))
                      steps hSub)
            · simp [replayFO, hClause, hLit] at h
          · simp [replayFO, hClause] at h

/-- FO replay checker soundness (accepted trace implies derivability). -/
theorem replayFO_sound
    {clauses : ConnFOCNF σ} {uFuel : Nat}
    {goals path : ConnFOClause σ} {trace : FOProofTrace σ}
    (h : replayFO (σ := σ) clauses uFuel goals path trace = true) :
    TraceDerivableFO clauses uFuel goals path trace :=
  traceDerivableFO_of_replayFO_true (σ := σ) clauses uFuel goals path trace h

/-! ## Executable DFS search (`connProveFODFS`) and refinement -/

/-- Try reduction against a path candidate list (FO). -/
def tryReducePathFO
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr path : ConnFOClause σ) :
    ConnFOClause σ → Option (FOProofTrace σ)
  | [] => none
  | pl :: ptail =>
      match unifyComplementLit? (σ := σ) uFuel g pl with
      | some θ =>
          match solver (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)) with
          | some tr => some (.step_reduce pl :: tr)
          | none => tryReducePathFO solver uFuel g gr path ptail
      | none => tryReducePathFO solver uFuel g gr path ptail

/-- Try extension within one clause by scanning candidate literals. -/
def tryExtendClauseFO
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr path : ConnFOClause σ)
    (clause : ConnFOClause σ) :
    ConnFOClause σ → Option (FOProofTrace σ)
  | [] => none
  | clit :: ctail =>
      match unifyComplementLit? (σ := σ) uFuel g clit with
      | some θ =>
          match solver
            (θ.applyConnFOClause (clause.erase clit ++ gr))
            (θ.applyConnFOClause (g :: path)) with
          | some tr => some (.step_extend clause clit :: tr)
          | none => tryExtendClauseFO solver uFuel g gr path clause ctail
      | none => tryExtendClauseFO solver uFuel g gr path clause ctail

/-- Try extension over a clause matrix candidate list (FO). -/
def tryExtendFO
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr path : ConnFOClause σ) :
    ConnFOCNF σ → Option (FOProofTrace σ)
  | [] => none
  | clause :: tail =>
      match tryExtendClauseFO solver uFuel g gr path clause clause with
      | some tr => some tr
      | none => tryExtendFO solver uFuel g gr path tail

/-- Executable depth-first FO connection prover with fuel. -/
def connProveFODFS (clauses : ConnFOCNF σ) (uFuel : Nat)
    (goals path : ConnFOClause σ) : Nat → Option (FOProofTrace σ)
  | 0 =>
      match goals with
      | [] => some []
      | _ :: _ => none
  | n + 1 =>
      match goals with
      | [] => some []
      | g :: gr =>
          match tryReducePathFO
            (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
            uFuel g gr path path with
          | some tr => some tr
          | none =>
              tryExtendFO
                (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                uFuel g gr path clauses

/-! ### Branch-complete FO collection (`connProveAllFO`) and refinement -/

/-- Prefix a FO proof step onto every trace. -/
def prependStepToFOTraces (step : FOProofStep σ) (trs : List (FOProofTrace σ)) :
    List (FOProofTrace σ) :=
  trs.map (fun tr => step :: tr)

/-- Collect all FO reduction traces from a path candidate list. -/
def tryReducePathAllFO
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr path : ConnFOClause σ) :
    ConnFOClause σ → List (FOProofTrace σ)
  | [] => []
  | pl :: ptail =>
      let here :=
        match unifyComplementLit? (σ := σ) uFuel g pl with
        | some θ =>
            prependStepToFOTraces (.step_reduce pl)
              (solverAll (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)))
        | none => []
      here ++ tryReducePathAllFO solverAll uFuel g gr path ptail

/-- Collect all FO extension traces from one clause literal scan. -/
def tryExtendClauseAllFO
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr path : ConnFOClause σ)
    (clause : ConnFOClause σ) :
    ConnFOClause σ → List (FOProofTrace σ)
  | [] => []
  | clit :: ctail =>
      let here :=
        match unifyComplementLit? (σ := σ) uFuel g clit with
        | some θ =>
            prependStepToFOTraces (.step_extend clause clit)
              (solverAll
                (θ.applyConnFOClause (clause.erase clit ++ gr))
                (θ.applyConnFOClause (g :: path)))
        | none => []
      here ++ tryExtendClauseAllFO solverAll uFuel g gr path clause ctail

/-- Collect all FO extension traces from a clause matrix candidate list. -/
def tryExtendAllFO
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr path : ConnFOClause σ) :
    ConnFOCNF σ → List (FOProofTrace σ)
  | [] => []
  | clause :: tail =>
      tryExtendClauseAllFO solverAll uFuel g gr path clause clause
        ++ tryExtendAllFO solverAll uFuel g gr path tail

/-- Branch-complete FO DFS search returning all traces within fuel. -/
def connProveAllFO (clauses : ConnFOCNF σ) (uFuel : Nat)
    (goals path : ConnFOClause σ) : Nat → List (FOProofTrace σ)
  | 0 =>
      match goals with
      | [] => [[]]
      | _ :: _ => []
  | n + 1 =>
      match goals with
      | [] => [[]]
      | g :: gr =>
          let rTraces :=
            tryReducePathAllFO
              (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
              uFuel g gr path path
          let eTraces :=
            tryExtendAllFO
              (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
              uFuel g gr path clauses
          rTraces ++ eTraces

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_prependStepToFOTraces_of_mem
    {step : FOProofStep σ} {tr : FOProofTrace σ} {trs : List (FOProofTrace σ)}
    (h : tr ∈ trs) :
    step :: tr ∈ prependStepToFOTraces (σ := σ) step trs := by
  unfold prependStepToFOTraces
  exact List.mem_map.mpr ⟨tr, h, rfl⟩

/-- Option-returning reduction success appears in all-traces reduction collection. -/
theorem tryReducePathFO_some_mem_tryReducePathAllFO
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (hsolver : ∀ g p tr, solver g p = some tr → tr ∈ solverAll g p)
    {uFuel : Nat} {g : ConnFOLit σ} {gr path pathIter : ConnFOClause σ}
    {tr : FOProofTrace σ}
    (h : tryReducePathFO (σ := σ) solver uFuel g gr path pathIter = some tr) :
    tr ∈ tryReducePathAllFO (σ := σ) solverAll uFuel g gr path pathIter := by
  induction pathIter generalizing tr with
  | nil =>
      simp [tryReducePathFO] at h
  | cons pl ptail ih =>
      cases hU : unifyComplementLit? (σ := σ) uFuel g pl with
      | none =>
          have hTail : tryReducePathFO (σ := σ) solver uFuel g gr path ptail = some tr := by
            simpa [tryReducePathFO, hU] using h
          simpa [tryReducePathAllFO, hU] using ih hTail
      | some θ =>
          cases hS : solver (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)) with
          | some trSub =>
              have hEq : .step_reduce pl :: trSub = tr := by
                simpa [tryReducePathFO, hU, hS] using h
              subst hEq
              have hSubMem : trSub ∈ solverAll (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)) :=
                hsolver _ _ _ hS
              have hHere :
                  .step_reduce pl :: trSub ∈
                    prependStepToFOTraces (σ := σ) (.step_reduce pl)
                      (solverAll (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path))) :=
                mem_prependStepToFOTraces_of_mem (σ := σ) hSubMem
              have hHereIf :
                  .step_reduce pl :: trSub ∈
                    (match unifyComplementLit? (σ := σ) uFuel g pl with
                     | some θ =>
                        prependStepToFOTraces (σ := σ) (.step_reduce pl)
                          (solverAll (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)))
                     | none => []) := by
                simpa [hU] using hHere
              exact List.mem_append.mpr (Or.inl hHereIf)
          | none =>
              have hTail : tryReducePathFO (σ := σ) solver uFuel g gr path ptail = some tr := by
                simpa [tryReducePathFO, hU, hS] using h
              exact List.mem_append.mpr (Or.inr (ih hTail))

/-- Option-returning clause-extension success appears in all-traces clause collection. -/
theorem tryExtendClauseFO_some_mem_tryExtendClauseAllFO
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (hsolver : ∀ g p tr, solver g p = some tr → tr ∈ solverAll g p)
    {uFuel : Nat} {g : ConnFOLit σ} {gr path clause clits : ConnFOClause σ}
    {tr : FOProofTrace σ}
    (h : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause clits = some tr) :
    tr ∈ tryExtendClauseAllFO (σ := σ) solverAll uFuel g gr path clause clits := by
  induction clits generalizing tr with
  | nil =>
      simp [tryExtendClauseFO] at h
  | cons clit ctail ih =>
      cases hU : unifyComplementLit? (σ := σ) uFuel g clit with
      | none =>
          have hTail : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause ctail = some tr := by
            simpa [tryExtendClauseFO, hU] using h
          simpa [tryExtendClauseAllFO, hU] using ih hTail
      | some θ =>
          cases hS : solver
              (θ.applyConnFOClause (clause.erase clit ++ gr))
              (θ.applyConnFOClause (g :: path)) with
          | some trSub =>
              have hEq : .step_extend clause clit :: trSub = tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              subst hEq
              have hSubMem :
                  trSub ∈ solverAll
                    (θ.applyConnFOClause (clause.erase clit ++ gr))
                    (θ.applyConnFOClause (g :: path)) :=
                hsolver _ _ _ hS
              have hHere :
                  .step_extend clause clit :: trSub ∈
                    prependStepToFOTraces (σ := σ) (.step_extend clause clit)
                      (solverAll
                        (θ.applyConnFOClause (clause.erase clit ++ gr))
                        (θ.applyConnFOClause (g :: path))) :=
                mem_prependStepToFOTraces_of_mem (σ := σ) hSubMem
              have hHereIf :
                  .step_extend clause clit :: trSub ∈
                    (match unifyComplementLit? (σ := σ) uFuel g clit with
                     | some θ =>
                        prependStepToFOTraces (σ := σ) (.step_extend clause clit)
                          (solverAll
                            (θ.applyConnFOClause (clause.erase clit ++ gr))
                            (θ.applyConnFOClause (g :: path)))
                     | none => []) := by
                simpa [hU] using hHere
              exact List.mem_append.mpr (Or.inl hHereIf)
          | none =>
              have hTail : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause ctail = some tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              exact List.mem_append.mpr (Or.inr (ih hTail))

/-- Option-returning matrix-extension success appears in all-traces matrix collection. -/
theorem tryExtendFO_some_mem_tryExtendAllFO
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (hsolver : ∀ g p tr, solver g p = some tr → tr ∈ solverAll g p)
    {uFuel : Nat} {g : ConnFOLit σ} {gr path : ConnFOClause σ} {cands : ConnFOCNF σ}
    {tr : FOProofTrace σ}
    (h : tryExtendFO (σ := σ) solver uFuel g gr path cands = some tr) :
    tr ∈ tryExtendAllFO (σ := σ) solverAll uFuel g gr path cands := by
  induction cands generalizing tr with
  | nil =>
      simp [tryExtendFO] at h
  | cons clause tail ih =>
      cases hC : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause clause with
      | some trC =>
          have hEq : trC = tr := by simpa [tryExtendFO, hC] using h
          subst hEq
          have hHere :
              trC ∈ tryExtendClauseAllFO (σ := σ) solverAll uFuel g gr path clause clause :=
            tryExtendClauseFO_some_mem_tryExtendClauseAllFO
              (σ := σ) (solver := solver) (solverAll := solverAll) hsolver (h := by simp [hC])
          exact List.mem_append.mpr (Or.inl hHere)
      | none =>
          have hTail : tryExtendFO (σ := σ) solver uFuel g gr path tail = some tr := by
            simpa [tryExtendFO, hC] using h
          exact List.mem_append.mpr (Or.inr (ih hTail))

/-- Refinement: every FO DFS witness appears in branch-complete FO collection. -/
theorem connProveFODFS_some_mem_connProveAllFO
    (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel goals path tr,
      connProveFODFS (σ := σ) clauses uFuel goals path fuel = some tr →
      tr ∈ connProveAllFO (σ := σ) clauses uFuel goals path fuel
  | 0, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFODFS] at h
          subst h
          simp [connProveAllFO]
      | cons g gr =>
          simp [connProveFODFS] at h
  | n + 1, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFODFS] at h
          subst h
          simp [connProveAllFO]
      | cons g gr =>
          simp [connProveFODFS] at h
          cases hRed : tryReducePathFO
              (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
              uFuel g gr path path with
          | some trRed =>
              have hEq : trRed = tr := by simpa [hRed] using h
              subst hEq
              have hMemRed :
                  trRed ∈ tryReducePathAllFO
                    (σ := σ)
                    (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
                    uFuel g gr path path :=
                tryReducePathFO_some_mem_tryReducePathAllFO
                  (σ := σ)
                  (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                  (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
                  (hsolver := by
                    intro g' p' tr' hs
                    exact connProveFODFS_some_mem_connProveAllFO clauses uFuel n g' p' tr' hs)
                  (h := hRed)
              exact List.mem_append.mpr (Or.inl hMemRed)
          | none =>
              have hMemExt :
                  tr ∈ tryExtendAllFO
                    (σ := σ)
                    (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
                    uFuel g gr path clauses :=
                tryExtendFO_some_mem_tryExtendAllFO
                  (σ := σ)
                  (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                  (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
                  (hsolver := by
                    intro g' p' tr' hs
                    exact connProveFODFS_some_mem_connProveAllFO clauses uFuel n g' p' tr' hs)
                  (h := by simpa [hRed] using h)
              exact List.mem_append.mpr (Or.inr hMemExt)

/-- Semantic soundness of branch-complete reduction collection. -/
theorem tryReducePathAllFO_sound_of_mem
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (hsolver : ∀ g p tr, tr ∈ solverAll g p → TraceDerivableFO clauses uFuel g p tr)
    {g : ConnFOLit σ} {gr path pathIter : ConnFOClause σ} {tr : FOProofTrace σ}
    (hmemPath : ∀ pl ∈ pathIter, pl ∈ path)
    (h : tr ∈ tryReducePathAllFO (σ := σ) solverAll uFuel g gr path pathIter) :
    TraceDerivableFO clauses uFuel (g :: gr) path tr := by
  induction pathIter generalizing tr with
  | nil =>
      simp [tryReducePathAllFO] at h
  | cons pl ptail ih =>
      have hsplit :
          tr ∈ (match unifyComplementLit? (σ := σ) uFuel g pl with
            | some θ =>
                prependStepToFOTraces (σ := σ) (.step_reduce pl)
                  (solverAll (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)))
            | none => [])
            ∨ tr ∈ tryReducePathAllFO (σ := σ) solverAll uFuel g gr path ptail := by
        simpa [tryReducePathAllFO] using (List.mem_append.mp h)
      rcases hsplit with hHere | hTail
      · cases hU : unifyComplementLit? (σ := σ) uFuel g pl with
        | none =>
            simp [hU] at hHere
        | some θ =>
            have hHere' :
                tr ∈ prependStepToFOTraces (σ := σ) (.step_reduce pl)
                  (solverAll (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path))) := by
              have hHere' := hHere
              simp [hU] at hHere'
              exact hHere'
            unfold prependStepToFOTraces at hHere'
            rcases List.mem_map.mp hHere' with ⟨trSub, hSub, hEq⟩
            subst hEq
            exact TraceDerivableFO.reduce g gr path pl trSub θ
              (hmemPath pl (by simp))
              hU
              (hsolver _ _ _ hSub)
      · exact ih
          (by
            intro p hp
            exact hmemPath p (by simp [hp]))
          hTail

/-- Semantic soundness of branch-complete single-clause extension collection. -/
theorem tryExtendClauseAllFO_sound_of_mem
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (hsolver : ∀ g p tr, tr ∈ solverAll g p → TraceDerivableFO clauses uFuel g p tr)
    {g : ConnFOLit σ} {gr path clause clits : ConnFOClause σ} {tr : FOProofTrace σ}
    (hClause : clause ∈ clauses)
    (hmemClits : ∀ clit ∈ clits, clit ∈ clause)
    (h : tr ∈ tryExtendClauseAllFO (σ := σ) solverAll uFuel g gr path clause clits) :
    TraceDerivableFO clauses uFuel (g :: gr) path tr := by
  induction clits generalizing tr with
  | nil =>
      simp [tryExtendClauseAllFO] at h
  | cons clit ctail ih =>
      have hsplit :
          tr ∈ (match unifyComplementLit? (σ := σ) uFuel g clit with
            | some θ =>
                prependStepToFOTraces (σ := σ) (.step_extend clause clit)
                  (solverAll
                    (θ.applyConnFOClause (clause.erase clit ++ gr))
                    (θ.applyConnFOClause (g :: path)))
            | none => [])
            ∨ tr ∈ tryExtendClauseAllFO (σ := σ) solverAll uFuel g gr path clause ctail := by
        simpa [tryExtendClauseAllFO] using (List.mem_append.mp h)
      rcases hsplit with hHere | hTail
      · cases hU : unifyComplementLit? (σ := σ) uFuel g clit with
        | none =>
            simp [hU] at hHere
        | some θ =>
            have hHere' :
                tr ∈ prependStepToFOTraces (σ := σ) (.step_extend clause clit)
                  (solverAll
                    (θ.applyConnFOClause (clause.erase clit ++ gr))
                    (θ.applyConnFOClause (g :: path))) := by
              have hHere' := hHere
              simp [hU] at hHere'
              exact hHere'
            unfold prependStepToFOTraces at hHere'
            rcases List.mem_map.mp hHere' with ⟨trSub, hSub, hEq⟩
            subst hEq
            exact TraceDerivableFO.extend g gr path clause clit trSub θ
              hClause
              (hmemClits clit (by simp))
              hU
              (hsolver _ _ _ hSub)
      · exact ih
          (by
            intro c hc
            exact hmemClits c (by simp [hc]))
          hTail

/-- Semantic soundness of branch-complete matrix extension collection. -/
theorem tryExtendAllFO_sound_of_mem
    (solverAll : ConnFOClause σ → ConnFOClause σ → List (FOProofTrace σ))
    (hsolver : ∀ g p tr, tr ∈ solverAll g p → TraceDerivableFO clauses uFuel g p tr)
    {g : ConnFOLit σ} {gr path : ConnFOClause σ} {cands : ConnFOCNF σ}
    {tr : FOProofTrace σ}
    (hsubset : ∀ c ∈ cands, c ∈ clauses)
    (h : tr ∈ tryExtendAllFO (σ := σ) solverAll uFuel g gr path cands) :
    TraceDerivableFO clauses uFuel (g :: gr) path tr := by
  induction cands generalizing tr with
  | nil =>
      simp [tryExtendAllFO] at h
  | cons clause tail ih =>
      have hsplit :
          tr ∈ tryExtendClauseAllFO (σ := σ) solverAll uFuel g gr path clause clause
            ∨ tr ∈ tryExtendAllFO (σ := σ) solverAll uFuel g gr path tail := by
        simpa [tryExtendAllFO] using (List.mem_append.mp h)
      rcases hsplit with hHere | hTail
      · exact tryExtendClauseAllFO_sound_of_mem
          (σ := σ) (clauses := clauses) (uFuel := uFuel)
          (solverAll := solverAll) hsolver
          (g := g) (gr := gr) (path := path)
          (clause := clause) (clits := clause) (tr := tr)
          (hClause := hsubset clause (by simp))
          (hmemClits := by intro c hc; exact hc)
          hHere
      · exact ih
          (by
            intro c hc
            exact hsubset c (by simp [hc]))
          hTail

/-- Semantic soundness of branch-complete FO search by membership. -/
theorem connProveAllFO_sound_of_mem
    (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel goals path tr,
      tr ∈ connProveAllFO (σ := σ) clauses uFuel goals path fuel →
      TraceDerivableFO clauses uFuel goals path tr
  | 0, goals, path, tr, h => by
      cases goals with
      | nil =>
          have hEq : tr = [] := by simpa [connProveAllFO] using h
          subst hEq
          exact TraceDerivableFO.done path
      | cons g gr =>
          simp [connProveAllFO] at h
  | n + 1, goals, path, tr, h => by
      cases goals with
      | nil =>
          have hEq : tr = [] := by simpa [connProveAllFO] using h
          subst hEq
          exact TraceDerivableFO.done path
      | cons g gr =>
          have hsplit :
              tr ∈ tryReducePathAllFO
                (σ := σ)
                (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
                uFuel g gr path path
                ∨
              tr ∈ tryExtendAllFO
                (σ := σ)
                (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
                uFuel g gr path clauses := by
            simpa [connProveAllFO] using (List.mem_append.mp h)
          rcases hsplit with hRed | hExt
          · exact tryReducePathAllFO_sound_of_mem
              (σ := σ) (clauses := clauses) (uFuel := uFuel)
              (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
              (hsolver := by
                intro g' p' tr' hs
                exact connProveAllFO_sound_of_mem clauses uFuel n g' p' tr' hs)
              (g := g) (gr := gr) (path := path) (pathIter := path)
              (tr := tr)
              (hmemPath := by intro pl hpl; exact hpl)
              hRed
          · exact tryExtendAllFO_sound_of_mem
              (σ := σ) (clauses := clauses) (uFuel := uFuel)
              (solverAll := fun g' p' => connProveAllFO clauses uFuel g' p' n)
              (hsolver := by
                intro g' p' tr' hs
                exact connProveAllFO_sound_of_mem clauses uFuel n g' p' tr' hs)
              (g := g) (gr := gr) (path := path) (cands := clauses) (tr := tr)
              (hsubset := by intro c hc; exact hc)
              hExt

/-- Erased statement: any trace in `connProveAllFO` is semantically derivable. -/
theorem connProveAllFO_sound
    {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {goals path : ConnFOClause σ} {tr : FOProofTrace σ}
    (h : tr ∈ connProveAllFO (σ := σ) clauses uFuel goals path fuel) :
    TraceDerivableFO clauses uFuel goals path tr :=
  connProveAllFO_sound_of_mem (σ := σ) clauses uFuel fuel goals path tr h

/-- Soundness of `tryReducePathFO` under a sound recursive solver. -/
theorem tryReducePathFO_sound_of_some
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (hsolver :
      ∀ g p tr, solver g p = some tr → TraceDerivableFO clauses uFuel g p tr)
    {g : ConnFOLit σ} {gr path pathIter : ConnFOClause σ} {tr : FOProofTrace σ}
    (hmem : ∀ pl ∈ pathIter, pl ∈ path)
    (h : tryReducePathFO (σ := σ) solver uFuel g gr path pathIter = some tr) :
    TraceDerivableFO clauses uFuel (g :: gr) path tr := by
  induction pathIter generalizing tr with
  | nil =>
      simp [tryReducePathFO] at h
  | cons pl ptail ih =>
      cases hU : unifyComplementLit? (σ := σ) uFuel g pl with
      | none =>
          have hTail : tryReducePathFO (σ := σ) solver uFuel g gr path ptail = some tr := by
            simpa [tryReducePathFO, hU] using h
          exact ih
            (by intro p hp; exact hmem p (by simp [hp]))
            hTail
      | some θ =>
          cases hS : solver (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)) with
          | some trSub =>
              have hEq : some (.step_reduce pl :: trSub) = some tr := by
                simpa [tryReducePathFO, hU, hS] using h
              have hEqTrace : .step_reduce pl :: trSub = tr := Option.some.inj hEq
              cases hEqTrace
              exact TraceDerivableFO.reduce g gr path pl trSub θ
                (hmem pl (by simp))
                hU
                (hsolver _ _ _ hS)
          | none =>
              have hTail : tryReducePathFO (σ := σ) solver uFuel g gr path ptail = some tr := by
                simpa [tryReducePathFO, hU, hS] using h
              exact ih
                (by intro p hp; exact hmem p (by simp [hp]))
                hTail

/-- Soundness of `tryExtendClauseFO` under a sound recursive solver. -/
theorem tryExtendClauseFO_sound_of_some
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (hsolver :
      ∀ g p tr, solver g p = some tr → TraceDerivableFO clauses uFuel g p tr)
    {g : ConnFOLit σ} {gr path clause clits : ConnFOClause σ} {tr : FOProofTrace σ}
    (hClause : clause ∈ clauses)
    (hmem : ∀ clit ∈ clits, clit ∈ clause)
    (h : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause clits = some tr) :
    TraceDerivableFO clauses uFuel (g :: gr) path tr := by
  induction clits generalizing tr with
  | nil =>
      simp [tryExtendClauseFO] at h
  | cons clit ctail ih =>
      cases hU : unifyComplementLit? (σ := σ) uFuel g clit with
      | none =>
          have hTail : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause ctail = some tr := by
            simpa [tryExtendClauseFO, hU] using h
          exact ih
            (by intro c hc; exact hmem c (by simp [hc]))
            hTail
      | some θ =>
          cases hS : solver (θ.applyConnFOClause (clause.erase clit ++ gr))
              (θ.applyConnFOClause (g :: path)) with
          | some trSub =>
              have hEq : some (.step_extend clause clit :: trSub) = some tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              have hEqTrace : .step_extend clause clit :: trSub = tr := Option.some.inj hEq
              cases hEqTrace
              exact TraceDerivableFO.extend g gr path clause clit trSub θ
                hClause
                (hmem clit (by simp))
                hU
                (hsolver _ _ _ hS)
          | none =>
              have hTail : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause ctail = some tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              exact ih
                (by intro c hc; exact hmem c (by simp [hc]))
                hTail

/-- Soundness of `tryExtendFO` under a sound recursive solver. -/
theorem tryExtendFO_sound_of_some
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    (hsolver :
      ∀ g p tr, solver g p = some tr → TraceDerivableFO clauses uFuel g p tr)
    {g : ConnFOLit σ} {gr path : ConnFOClause σ} {cands : ConnFOCNF σ} {tr : FOProofTrace σ}
    (hsubset : ∀ c ∈ cands, c ∈ clauses)
    (h : tryExtendFO (σ := σ) solver uFuel g gr path cands = some tr) :
    TraceDerivableFO clauses uFuel (g :: gr) path tr := by
  induction cands generalizing tr with
  | nil =>
      simp [tryExtendFO] at h
  | cons clause tail ih =>
      simp [tryExtendFO] at h
      cases hClause : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause clause with
      | some trClause =>
          have hEq : trClause = tr := by simpa [hClause] using h
          subst hEq
          have hmemClause : clause ∈ clauses := hsubset clause (by simp)
          exact tryExtendClauseFO_sound_of_some
            (σ := σ) (clauses := clauses) (uFuel := uFuel)
            (solver := solver) hsolver
            (g := g) (gr := gr) (path := path)
            (clause := clause) (clits := clause)
            (tr := trClause)
            (hClause := hmemClause)
            (hmem := by intro c hc; exact hc)
            (by simp [hClause])
      | none =>
          exact ih
            (by
              intro c hc
              exact hsubset c (by simp [hc]))
            (by simpa [hClause] using h)

/-- Soundness: executable FO DFS success implies FO trace-derivability. -/
theorem connProveFODFS_sound_of_some
    (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel goals path tr,
      connProveFODFS (σ := σ) clauses uFuel goals path fuel = some tr →
      TraceDerivableFO clauses uFuel goals path tr
  | 0, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFODFS] at h
          subst h
          exact TraceDerivableFO.done path
      | cons g gr =>
          simp [connProveFODFS] at h
  | n + 1, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFODFS] at h
          subst h
          exact TraceDerivableFO.done path
      | cons g gr =>
          simp [connProveFODFS] at h
          cases hRed : tryReducePathFO
            (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
            uFuel g gr path path with
          | some trRed =>
              have hEq : trRed = tr := by simpa [hRed] using h
              subst hEq
              exact tryReducePathFO_sound_of_some
                (σ := σ) (clauses := clauses) (uFuel := uFuel)
                (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                (hsolver := by
                  intro g' p' tr' hs
                  exact connProveFODFS_sound_of_some clauses uFuel n g' p' tr' hs)
                (g := g) (gr := gr) (path := path) (pathIter := path)
                (tr := trRed)
                (hmem := by intro pl hpl; exact hpl)
                (by simp [hRed])
          | none =>
              exact tryExtendFO_sound_of_some
                (σ := σ) (clauses := clauses) (uFuel := uFuel)
                (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                (hsolver := by
                  intro g' p' tr' hs
                  exact connProveFODFS_sound_of_some clauses uFuel n g' p' tr' hs)
                (g := g) (gr := gr) (path := path)
                (cands := clauses) (tr := tr)
                (hsubset := by intro c hc; exact hc)
                (by simpa [hRed] using h)

/-- Executable FO DFS soundness (erased statement). -/
theorem connProveFODFS_sound
    {clauses : ConnFOCNF σ} {uFuel fuel}
    {goals path : ConnFOClause σ} {tr : FOProofTrace σ}
    (h : connProveFODFS (σ := σ) clauses uFuel goals path fuel = some tr) :
    TraceDerivableFO clauses uFuel goals path tr :=
  connProveFODFS_sound_of_some (σ := σ) clauses uFuel fuel goals path tr h

/--
Combined refinement endpoint for FO DFS:
returned traces are semantically valid and included in branch-complete collection.
-/
theorem connProveFODFS_some_refines_connProveAllFO
    {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {goals path : ConnFOClause σ} {tr : FOProofTrace σ}
    (h : connProveFODFS (σ := σ) clauses uFuel goals path fuel = some tr) :
    tr ∈ connProveAllFO (σ := σ) clauses uFuel goals path fuel
      ∧ TraceDerivableFO clauses uFuel goals path tr := by
  exact ⟨
    connProveFODFS_some_mem_connProveAllFO (σ := σ) clauses uFuel fuel goals path tr h,
    connProveFODFS_sound (σ := σ) h
  ⟩

/-- Completeness helper for path-reduction search. -/
theorem tryReducePathFO_exists_of_member
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    {uFuel : Nat} {g : ConnFOLit σ} {gr path pathIter : ConnFOClause σ}
    {pl : ConnFOLit σ} {θ : Subst σ}
    (hmem : pl ∈ pathIter)
    (hUnify : unifyComplementLit? (σ := σ) uFuel g pl = some θ)
    (hSub : ∃ tr, solver (θ.applyConnFOClause gr) (θ.applyConnFOClause (g :: path)) = some tr) :
    ∃ tr, tryReducePathFO (σ := σ) solver uFuel g gr path pathIter = some tr := by
  induction pathIter with
  | nil =>
      cases hmem
  | cons pl0 ptail ih =>
      by_cases hEq : pl = pl0
      · subst hEq
        rcases hSub with ⟨trSub, hS⟩
        exact ⟨.step_reduce pl :: trSub, by simp [tryReducePathFO, hUnify, hS]⟩
      · have hmemTail : pl ∈ ptail := (List.mem_cons.1 hmem).resolve_left hEq
        cases hU0 : unifyComplementLit? (σ := σ) uFuel g pl0 with
        | some θ0 =>
            cases hS0 : solver (θ0.applyConnFOClause gr) (θ0.applyConnFOClause (g :: path)) with
            | some tr0 =>
                exact ⟨.step_reduce pl0 :: tr0, by simp [tryReducePathFO, hU0, hS0]⟩
            | none =>
                rcases ih hmemTail with ⟨trTail, hTail⟩
                exact ⟨trTail, by simpa [tryReducePathFO, hU0, hS0] using hTail⟩
        | none =>
            rcases ih hmemTail with ⟨trTail, hTail⟩
            exact ⟨trTail, by simpa [tryReducePathFO, hU0] using hTail⟩

/-- Completeness helper for literal scanning inside one extension clause. -/
theorem tryExtendClauseFO_exists_of_member
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    {uFuel : Nat} {g : ConnFOLit σ} {gr path clause clits : ConnFOClause σ}
    {clit : ConnFOLit σ} {θ : Subst σ}
    (hmem : clit ∈ clits)
    (hUnify : unifyComplementLit? (σ := σ) uFuel g clit = some θ)
    (hSub :
      ∃ tr, solver
        (θ.applyConnFOClause (clause.erase clit ++ gr))
        (θ.applyConnFOClause (g :: path)) = some tr) :
    ∃ tr, tryExtendClauseFO (σ := σ) solver uFuel g gr path clause clits = some tr := by
  induction clits with
  | nil =>
      cases hmem
  | cons cl0 ctail ih =>
      by_cases hEq : clit = cl0
      · subst hEq
        rcases hSub with ⟨trSub, hS⟩
        exact ⟨.step_extend clause clit :: trSub, by simp [tryExtendClauseFO, hUnify, hS]⟩
      · have hmemTail : clit ∈ ctail := (List.mem_cons.1 hmem).resolve_left hEq
        cases hU0 : unifyComplementLit? (σ := σ) uFuel g cl0 with
        | some θ0 =>
            cases hS0 : solver
                (θ0.applyConnFOClause (clause.erase cl0 ++ gr))
                (θ0.applyConnFOClause (g :: path)) with
            | some tr0 =>
                exact ⟨.step_extend clause cl0 :: tr0, by simp [tryExtendClauseFO, hU0, hS0]⟩
            | none =>
                rcases ih hmemTail with ⟨trTail, hTail⟩
                exact ⟨trTail, by simpa [tryExtendClauseFO, hU0, hS0] using hTail⟩
        | none =>
            rcases ih hmemTail with ⟨trTail, hTail⟩
            exact ⟨trTail, by simpa [tryExtendClauseFO, hU0] using hTail⟩

/-- Completeness helper for clause-matrix extension scan. -/
theorem tryExtendFO_exists_of_clause_member
    (solver : ConnFOClause σ → ConnFOClause σ → Option (FOProofTrace σ))
    {uFuel : Nat} {g : ConnFOLit σ} {gr path : ConnFOClause σ}
    {cands : ConnFOCNF σ} {clause : ConnFOClause σ}
    (hClauseMem : clause ∈ cands)
    {clit : ConnFOLit σ} {θ : Subst σ}
    (hLit : clit ∈ clause)
    (hUnify : unifyComplementLit? (σ := σ) uFuel g clit = some θ)
    (hSub :
      ∃ tr, solver
        (θ.applyConnFOClause (clause.erase clit ++ gr))
        (θ.applyConnFOClause (g :: path)) = some tr) :
    ∃ tr, tryExtendFO (σ := σ) solver uFuel g gr path cands = some tr := by
  induction cands with
  | nil =>
      cases hClauseMem
  | cons c0 ctail ih =>
      by_cases hEq : clause = c0
      · subst hEq
        rcases tryExtendClauseFO_exists_of_member
            (σ := σ) (solver := solver)
            (uFuel := uFuel) (g := g) (gr := gr) (path := path)
            (clause := clause) (clits := clause)
            (clit := clit) (θ := θ)
            hLit hUnify hSub with ⟨trC, hC⟩
        exact ⟨trC, by simp [tryExtendFO, hC]⟩
      · have hClauseTail : clause ∈ ctail := (List.mem_cons.1 hClauseMem).resolve_left hEq
        cases hC0 : tryExtendClauseFO (σ := σ) solver uFuel g gr path c0 c0 with
        | some tr0 =>
            exact ⟨tr0, by simp [tryExtendFO, hC0]⟩
        | none =>
            rcases ih hClauseTail with ⟨trTail, hTail⟩
            exact ⟨trTail, by simpa [tryExtendFO, hC0] using hTail⟩

/-- Witness-level completeness for FO DFS from trace derivations. -/
theorem connProveFODFS_complete_of_trace
    {clauses : ConnFOCNF σ} {uFuel : Nat}
    {goals path : ConnFOClause σ} {trace : FOProofTrace σ} {fuel : Nat}
    (hDer : TraceDerivableFO clauses uFuel goals path trace)
    (hLen : trace.length ≤ fuel) :
    ∃ tr, connProveFODFS (σ := σ) clauses uFuel goals path fuel = some tr := by
  induction hDer generalizing fuel with
  | done path =>
      refine ⟨[], ?_⟩
      cases fuel <;> simp [connProveFODFS]
  | reduce g gr path pl steps θ hMem hUnify hSub ih =>
      cases fuel with
      | zero =>
          simp at hLen
      | succ n =>
          have hLenSub : steps.length ≤ n := Nat.le_of_succ_le_succ (by simpa using hLen)
          rcases ih hLenSub with ⟨trSub, hRunSub⟩
          rcases tryReducePathFO_exists_of_member
              (σ := σ)
              (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
              (uFuel := uFuel) (g := g) (gr := gr) (path := path)
              (pathIter := path) (pl := pl) (θ := θ)
              hMem hUnify
              ⟨trSub, by simpa using hRunSub⟩ with ⟨trRed, hRed⟩
          exact ⟨trRed, by simp [connProveFODFS, hRed]⟩
  | extend g gr path clause clit steps θ hClause hLit hUnify hSub ih =>
      cases fuel with
      | zero =>
          simp at hLen
      | succ n =>
          have hLenSub : steps.length ≤ n := Nat.le_of_succ_le_succ (by simpa using hLen)
          rcases ih hLenSub with ⟨trSub, hRunSub⟩
          by_cases hRedEx :
              ∃ trRed,
                tryReducePathFO
                  (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                  uFuel g gr path path = some trRed
          · rcases hRedEx with ⟨trRed, hRed⟩
            exact ⟨trRed, by simp [connProveFODFS, hRed]⟩
          · rcases tryExtendFO_exists_of_clause_member
              (σ := σ)
              (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
              (uFuel := uFuel) (g := g) (gr := gr) (path := path)
              (cands := clauses) (clause := clause)
              (hClauseMem := hClause)
              (clit := clit) (θ := θ)
              hLit hUnify
              ⟨trSub, by simpa using hRunSub⟩ with ⟨trExt, hExt⟩
            have hNoRed :
                tryReducePathFO
                  (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                  uFuel g gr path path = none := by
              cases hTry :
                  tryReducePathFO
                    (solver := fun g' p' => connProveFODFS clauses uFuel g' p' n)
                    uFuel g gr path path with
              | some trTry =>
                  exact (hRedEx ⟨trTry, hTry⟩).elim
              | none =>
                  rfl
            exact ⟨trExt, by simp [connProveFODFS, hNoRed, hExt]⟩

/-- Existential FO DFS witness completeness (from trace-level derivability). -/
theorem connProveFODFS_witness_complete
    {clauses : ConnFOCNF σ} {uFuel : Nat}
    {goals path : ConnFOClause σ}
    (h : ∃ trace, TraceDerivableFO clauses uFuel goals path trace) :
    ∃ fuel tr, connProveFODFS (σ := σ) clauses uFuel goals path fuel = some tr := by
  rcases h with ⟨trace, hTrace⟩
  rcases connProveFODFS_complete_of_trace
      (σ := σ) (clauses := clauses) (uFuel := uFuel)
      (goals := goals) (path := path) (trace := trace) (fuel := trace.length)
      hTrace (Nat.le_refl _) with ⟨tr, hRun⟩
  exact ⟨trace.length, tr, hRun⟩

/-! ## FO collection + ranking contracts (PeTTa parity layer) -/

/-- Wrap FO traces as `FOProofObj` values for a fixed root/fuel. -/
def wrapFOTracesAsProofs (fuel : Nat) (root : ConnFOClause σ)
    (traces : List (FOProofTrace σ)) : List (FOProofObj σ) :=
  traces.map (fun tr => { fuel := fuel, root := root, trace := tr })

/-- Branch-complete proof objects for one root clause. -/
def rootProofsAllFO (clauses : ConnFOCNF σ) (uFuel fuel : Nat)
    (root : ConnFOClause σ) : List (FOProofObj σ) :=
  wrapFOTracesAsProofs (σ := σ) fuel root (connProveAllFO clauses uFuel root [] fuel)

/-- Branch-complete proof objects collected over a root list. -/
def collectRootProofsAllFO (clauses : ConnFOCNF σ) (uFuel fuel : Nat)
    (roots : ConnFOCNF σ) : List (FOProofObj σ) :=
  match roots with
  | [] => []
  | root :: tail =>
      rootProofsAllFO (σ := σ) clauses uFuel fuel root
        ++ collectRootProofsAllFO clauses uFuel fuel tail

/-- Branch-complete proof objects collected over matrix roots. -/
def collectProofsAllFO (clauses : ConnFOCNF σ) (uFuel fuel : Nat) : List (FOProofObj σ) :=
  collectRootProofsAllFO clauses uFuel fuel clauses

/-- Default FO ranking score used for deterministic topK extraction. -/
def foProofRankScore (p : FOProofObj σ) : Nat :=
  p.fuel + p.trace.length

/-- Insert one FO proof in descending score order. -/
def insertFOProofByScore (score : FOProofObj σ → Nat)
    (p : FOProofObj σ) : List (FOProofObj σ) → List (FOProofObj σ)
  | [] => [p]
  | q :: qs =>
      if score p ≥ score q then
        p :: q :: qs
      else
        q :: insertFOProofByScore score p qs

/-- Stable insertion-sort by descending score. -/
def sortFOProofsDescByScore (score : FOProofObj σ → Nat)
    (proofs : List (FOProofObj σ)) : List (FOProofObj σ) :=
  proofs.foldr (insertFOProofByScore score) []

/-- Top-K projection over sorted FO proofs. -/
def topKFOProofsByScore (score : FOProofObj σ → Nat)
    (proofs : List (FOProofObj σ)) (topK : Nat) : List (FOProofObj σ) :=
  (sortFOProofsDescByScore score proofs).take topK

/-- Top-K over branch-complete FO proofs. -/
def topKCollectProofsAllFO (score : FOProofObj σ → Nat)
    (clauses : ConnFOCNF σ) (uFuel fuel topK : Nat) : List (FOProofObj σ) :=
  topKFOProofsByScore score (collectProofsAllFO (σ := σ) clauses uFuel fuel) topK

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_insertFOProofByScore_iff
    (score : FOProofObj σ → Nat) (p : FOProofObj σ)
    {ps : List (FOProofObj σ)} {x : FOProofObj σ} :
    x ∈ insertFOProofByScore score p ps ↔ x = p ∨ x ∈ ps := by
  induction ps with
  | nil =>
      simp [insertFOProofByScore]
  | cons q qs ih =>
      by_cases hcmp : score p ≥ score q
      · simp [insertFOProofByScore, hcmp]
      · simp [insertFOProofByScore, hcmp, ih]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_sortFOProofsDescByScore_iff
    (score : FOProofObj σ → Nat) {proofs : List (FOProofObj σ)} {x : FOProofObj σ} :
    x ∈ sortFOProofsDescByScore score proofs ↔ x ∈ proofs := by
  induction proofs with
  | nil =>
      simp [sortFOProofsDescByScore]
  | cons p ps ih =>
      have ih' : x ∈ List.foldr (insertFOProofByScore score) [] ps ↔ x ∈ ps := by
        simpa [sortFOProofsDescByScore] using ih
      simp [sortFOProofsDescByScore, ih', mem_insertFOProofByScore_iff]

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_topKFOProofsByScore_implies_mem
    (score : FOProofObj σ → Nat) {proofs : List (FOProofObj σ)} {topK : Nat}
    {p : FOProofObj σ}
    (h : p ∈ topKFOProofsByScore score proofs topK) :
    p ∈ proofs := by
  have hMemSorted : p ∈ sortFOProofsDescByScore score proofs :=
    List.mem_of_mem_take h
  exact (mem_sortFOProofsDescByScore_iff (σ := σ) score).1 hMemSorted

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem length_topKFOProofsByScore_le
    (score : FOProofObj σ → Nat) (proofs : List (FOProofObj σ)) (topK : Nat) :
    (topKFOProofsByScore score proofs topK).length ≤ topK := by
  simp [topKFOProofsByScore]

theorem mem_topKCollectProofsAllFO_implies_mem_collectProofsAllFO
    (score : FOProofObj σ → Nat) {clauses : ConnFOCNF σ} {uFuel fuel topK : Nat}
    {p : FOProofObj σ}
    (h : p ∈ topKCollectProofsAllFO (σ := σ) score clauses uFuel fuel topK) :
    p ∈ collectProofsAllFO (σ := σ) clauses uFuel fuel := by
  exact mem_topKFOProofsByScore_implies_mem (σ := σ) score h

theorem length_topKCollectProofsAllFO_le
    (score : FOProofObj σ → Nat) (clauses : ConnFOCNF σ)
    (uFuel fuel topK : Nat) :
    (topKCollectProofsAllFO (σ := σ) score clauses uFuel fuel topK).length ≤ topK := by
  exact length_topKFOProofsByScore_le
    (σ := σ) score (collectProofsAllFO (σ := σ) clauses uFuel fuel) topK

/-- Contract alias: topK-over-all is definitionally topK over `collectProofsAllFO`. -/
theorem topKCollectProofsAllFO_contract
    (score : FOProofObj σ → Nat) (clauses : ConnFOCNF σ)
    (uFuel fuel topK : Nat) :
    topKCollectProofsAllFO (σ := σ) score clauses uFuel fuel topK =
      topKFOProofsByScore score (collectProofsAllFO (σ := σ) clauses uFuel fuel) topK := rfl

/-! ## FO `collectProofsAll` root-membership family (PeTTa parity layer) -/

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_wrapFOTracesAsProofs_of_mem
    {fuel : Nat} {root : ConnFOClause σ}
    {tr : FOProofTrace σ} {trs : List (FOProofTrace σ)}
    (h : tr ∈ trs) :
    ({ fuel := fuel, root := root, trace := tr } : FOProofObj σ) ∈
      wrapFOTracesAsProofs (σ := σ) fuel root trs := by
  unfold wrapFOTracesAsProofs
  exact List.mem_map.mpr ⟨tr, h, rfl⟩

theorem rootProofsAllFO_mem_collectRootProofsAllFO_of_mem_root
    {clauses roots : ConnFOCNF σ} {uFuel fuel : Nat}
    {root : ConnFOClause σ} {p : FOProofObj σ}
    (hRoot : root ∈ roots)
    (hp : p ∈ rootProofsAllFO (σ := σ) clauses uFuel fuel root) :
    p ∈ collectRootProofsAllFO (σ := σ) clauses uFuel fuel roots := by
  induction roots generalizing root p with
  | nil =>
      cases hRoot
  | cons r rs ih =>
      simp [collectRootProofsAllFO] at hRoot ⊢
      cases hRoot with
      | inl hr =>
          subst hr
          exact Or.inl hp
      | inr hTail =>
          exact Or.inr (ih hTail hp)

theorem proof_mem_collectProofsAllFO_of_root_mem_trace_mem
    {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {root : ConnFOClause σ} {tr : FOProofTrace σ}
    (hRoot : root ∈ clauses)
    (hTr : tr ∈ connProveAllFO (σ := σ) clauses uFuel root [] fuel) :
    ({ fuel := fuel, root := root, trace := tr } : FOProofObj σ) ∈
      collectProofsAllFO (σ := σ) clauses uFuel fuel := by
  unfold collectProofsAllFO
  exact rootProofsAllFO_mem_collectRootProofsAllFO_of_mem_root
    (σ := σ) (clauses := clauses) (roots := clauses)
    (uFuel := uFuel) (fuel := fuel) (root := root)
    hRoot
    (mem_wrapFOTracesAsProofs_of_mem (σ := σ) hTr)

/-! ## PeTTaFixtureMapFO (`test_leancop_*` parity names) -/

section PeTTaFixtureMapFO

inductive FOFixVar where
  | x
  deriving DecidableEq, Repr

inductive FOFixConst where
  | a
  deriving DecidableEq, Repr

inductive FOFixRel where
  | p
  deriving DecidableEq, Repr

inductive FOFixFun where
  | f
  deriving DecidableEq, Repr

def foFixtureSig : LPSignature where
  constants := FOFixConst
  vars := FOFixVar
  relationSymbols := FOFixRel
  relationArity
    | .p => 1
  functionSymbols := FOFixFun
  functionArity
    | .f => 1

def fo_tA : Term foFixtureSig := .const .a
def fo_tX : Term foFixtureSig := .var .x
def fo_tFa : Term foFixtureSig := .app .f (fun _ => fo_tA)

def fo_atomP (t : Term foFixtureSig) : Atom foFixtureSig where
  symbol := .p
  args := fun _ => t

def fo_lit_pos_a : ConnFOLit foFixtureSig := .pos (fo_atomP fo_tA)
def fo_lit_neg_a : ConnFOLit foFixtureSig := .neg (fo_atomP fo_tA)
def fo_lit_pos_x : ConnFOLit foFixtureSig := .pos (fo_atomP fo_tX)
def fo_lit_neg_fa : ConnFOLit foFixtureSig := .neg (fo_atomP fo_tFa)

def fo_unsat_ground_c1 : ConnFOClause foFixtureSig := [fo_lit_pos_a]
def fo_unsat_ground_c2 : ConnFOClause foFixtureSig := [fo_lit_neg_a]
def fo_unsat_ground_clauses : ConnFOCNF foFixtureSig := [fo_unsat_ground_c1, fo_unsat_ground_c2]
def fo_unsat_ground_root : ConnFOClause foFixtureSig := fo_unsat_ground_c1

def fo_unsat_unify_c1 : ConnFOClause foFixtureSig := [fo_lit_pos_x]
def fo_unsat_unify_c2 : ConnFOClause foFixtureSig := [fo_lit_neg_fa]
def fo_unsat_unify_clauses : ConnFOCNF foFixtureSig := [fo_unsat_unify_c1, fo_unsat_unify_c2]
def fo_unsat_unify_root : ConnFOClause foFixtureSig := fo_unsat_unify_c1

def fo_sat_singleton_clauses : ConnFOCNF foFixtureSig := [fo_unsat_ground_c1]
def fo_sat_singleton_root : ConnFOClause foFixtureSig := fo_unsat_ground_c1

/-- Named FO fixture lemma: ground contradiction has an executable FO proof witness. -/
theorem fo_unsat_ground :
    ∃ uFuel tr, connProveFODFS (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel fo_unsat_ground_root [] 2 = some tr := by
  have hUnifies : Unifies (Subst.id (σ := foFixtureSig))
      (finPairsToList (fun _ : Fin 1 => fo_tA) (fun _ : Fin 1 => fo_tA)) := by
    intro p hp
    have hp' : p = (fo_tA, fo_tA) := by
      simpa [finPairsToList, fo_tA] using hp
    subst hp'
    simp [Subst.id, fo_tA]
  rcases unifyFuel_exists_of_unifies
      (eqs := finPairsToList (fun _ : Fin 1 => fo_tA) (fun _ : Fin 1 => fo_tA))
      ⟨Subst.id (σ := foFixtureSig), hUnifies⟩ with ⟨uFuel, θ, hU⟩
  have hUnify :
      unifyComplementLit? (σ := foFixtureSig) uFuel fo_lit_pos_a fo_lit_neg_a = some θ := by
    simpa [unifyComplementLit?, unifyAtoms, fo_lit_pos_a, fo_lit_neg_a, fo_atomP] using hU
  have hDer : TraceDerivableFO fo_unsat_ground_clauses uFuel
      fo_unsat_ground_root [] [.step_extend fo_unsat_ground_c2 fo_lit_neg_a] := by
    have hErase : fo_unsat_ground_c2.erase fo_lit_neg_a = [] := by
      simp [fo_unsat_ground_c2, fo_lit_neg_a]
    refine TraceDerivableFO.extend
      fo_lit_pos_a [] [] fo_unsat_ground_c2 fo_lit_neg_a [] θ
      (by simp [fo_unsat_ground_clauses, fo_unsat_ground_c2, fo_unsat_ground_c1])
      (by simp [fo_unsat_ground_c2, fo_lit_neg_a]) hUnify ?_
    simpa [hErase] using (TraceDerivableFO.done (clauses := fo_unsat_ground_clauses)
      (uFuel := uFuel) (θ.applyConnFOClause [fo_lit_pos_a]))
  rcases connProveFODFS_complete_of_trace
      (σ := foFixtureSig) (clauses := fo_unsat_ground_clauses) (uFuel := uFuel)
      (goals := fo_unsat_ground_root) (path := [])
      (trace := [.step_extend fo_unsat_ground_c2 fo_lit_neg_a]) (fuel := 2)
      hDer (by decide) with ⟨tr, hRun⟩
  exact ⟨uFuel, tr, hRun⟩

/-- Named FO fixture lemma: unification contradiction has an executable FO proof witness. -/
theorem fo_unsat_unify :
    ∃ uFuel tr, connProveFODFS (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel fo_unsat_unify_root [] 2 = some tr := by
  let δ : Subst foFixtureSig := Subst.single .x fo_tFa
  have hUnifies : Unifies δ
      (finPairsToList (fun _ : Fin 1 => fo_tX) (fun _ : Fin 1 => fo_tFa)) := by
    intro p hp
    have hp' : p = (fo_tX, fo_tFa) := by
      simpa [finPairsToList, fo_tX, fo_tFa, fo_tA] using hp
    subst hp'
    simp [δ, Subst.single, Subst.applyTerm, fo_tX, fo_tFa, fo_tA]
  rcases unifyFuel_exists_of_unifies
      (eqs := finPairsToList (fun _ : Fin 1 => fo_tX) (fun _ : Fin 1 => fo_tFa))
      ⟨δ, hUnifies⟩ with ⟨uFuel, θ, hU⟩
  have hUnify :
      unifyComplementLit? (σ := foFixtureSig) uFuel fo_lit_pos_x fo_lit_neg_fa = some θ := by
    simpa [unifyComplementLit?, unifyAtoms, fo_lit_pos_x, fo_lit_neg_fa, fo_atomP] using hU
  have hDer : TraceDerivableFO fo_unsat_unify_clauses uFuel
      fo_unsat_unify_root [] [.step_extend fo_unsat_unify_c2 fo_lit_neg_fa] := by
    have hErase : fo_unsat_unify_c2.erase fo_lit_neg_fa = [] := by
      simp [fo_unsat_unify_c2, fo_lit_neg_fa]
    refine TraceDerivableFO.extend
      fo_lit_pos_x [] [] fo_unsat_unify_c2 fo_lit_neg_fa [] θ
      (by simp [fo_unsat_unify_clauses, fo_unsat_unify_c2, fo_unsat_unify_c1])
      (by simp [fo_unsat_unify_c2, fo_lit_neg_fa]) hUnify ?_
    simpa [hErase] using (TraceDerivableFO.done (clauses := fo_unsat_unify_clauses)
      (uFuel := uFuel) (θ.applyConnFOClause [fo_lit_pos_x]))
  rcases connProveFODFS_complete_of_trace
      (σ := foFixtureSig) (clauses := fo_unsat_unify_clauses) (uFuel := uFuel)
      (goals := fo_unsat_unify_root) (path := [])
      (trace := [.step_extend fo_unsat_unify_c2 fo_lit_neg_fa]) (fuel := 2)
      hDer (by decide) with ⟨tr, hRun⟩
  exact ⟨uFuel, tr, hRun⟩

/-- Named FO fixture lemma: singleton positive clause remains unsolved for all fuels. -/
theorem fo_sat_singleton :
    ∀ uFuel fuel, connProveFODFS (σ := foFixtureSig)
      fo_sat_singleton_clauses uFuel fo_sat_singleton_root [] fuel = none := by
  intro uFuel fuel
  cases fuel with
  | zero =>
      simp [connProveFODFS, fo_sat_singleton_root, fo_unsat_ground_c1]
  | succ n =>
      simp [connProveFODFS, fo_sat_singleton_clauses, fo_sat_singleton_root, fo_unsat_ground_c1,
        tryExtendFO, tryExtendClauseFO, tryReducePathFO, unifyComplementLit?, fo_lit_pos_a]

/-- FO fixture-parity: root-wise proof witnesses are members of branch-complete proof collection (ground). -/
theorem fo_unsat_ground_proof_mem_collectProofsAllFO :
    ∃ uFuel : Nat, ∃ p : FOProofObj foFixtureSig, p ∈ collectProofsAllFO (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel 2 := by
  rcases fo_unsat_ground with ⟨uFuel, tr, hRun⟩
  let p : FOProofObj foFixtureSig :=
    { fuel := 2, root := fo_unsat_ground_root, trace := tr }
  refine ⟨uFuel, p, ?_⟩
  have hTrMem : tr ∈ connProveAllFO (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel fo_unsat_ground_root [] 2 :=
    connProveFODFS_some_mem_connProveAllFO (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel 2 fo_unsat_ground_root [] tr hRun
  simpa [p] using
    (proof_mem_collectProofsAllFO_of_root_mem_trace_mem
      (clauses := fo_unsat_ground_clauses) (uFuel := uFuel) (fuel := 2)
      (root := fo_unsat_ground_root) (tr := tr)
      (by simp [fo_unsat_ground_root, fo_unsat_ground_clauses, fo_unsat_ground_c1]) hTrMem)

/-- FO fixture-parity: root-wise proof witnesses are members of branch-complete proof collection (unify). -/
theorem fo_unsat_unify_proof_mem_collectProofsAllFO :
    ∃ uFuel : Nat, ∃ p : FOProofObj foFixtureSig, p ∈ collectProofsAllFO (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel 2 := by
  rcases fo_unsat_unify with ⟨uFuel, tr, hRun⟩
  let p : FOProofObj foFixtureSig :=
    { fuel := 2, root := fo_unsat_unify_root, trace := tr }
  refine ⟨uFuel, p, ?_⟩
  have hTrMem : tr ∈ connProveAllFO (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel fo_unsat_unify_root [] 2 :=
    connProveFODFS_some_mem_connProveAllFO (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel 2 fo_unsat_unify_root [] tr hRun
  simpa [p] using
    (proof_mem_collectProofsAllFO_of_root_mem_trace_mem
      (clauses := fo_unsat_unify_clauses) (uFuel := uFuel) (fuel := 2)
      (root := fo_unsat_unify_root) (tr := tr)
      (by simp [fo_unsat_unify_root, fo_unsat_unify_clauses, fo_unsat_unify_c1]) hTrMem)

end PeTTaFixtureMapFO

end FirstOrderConnection

end

end Mettapedia.Logic.LP
