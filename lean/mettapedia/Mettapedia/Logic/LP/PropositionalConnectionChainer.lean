import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.TakeDrop

/-!
# Propositional Connection-Tableau Chainer (PeTTa/MeTTa-Aligned)

This module gives a minimal formal bridge for the pure propositional leanCoP-style
core loop used in PeTTa:

- connection literals and clause matrix (`ConnCNF`)
- trace steps (`step_reduce`, `step_extend`)
- replay checker (`replay`)
- abstract derivability without traces (`ConnDerivable`)
- refinement theorems between concrete checker and abstract semantics

The design matches the proof-object/checker shape used in:
`hyperon/PeTTa/resprover/leancop_pure_poc.metta`.
-/

namespace Mettapedia.Logic.LP

open scoped Classical

section PropositionalConnection

variable {α : Type*} [DecidableEq α]

/-- Propositional literal over atom type `α`. -/
inductive Lit (α : Type*)
  | pos : α → Lit α
  | neg : α → Lit α
  deriving DecidableEq, Repr

/-- Literal complement. -/
def Lit.complement : Lit α → Lit α
  | .pos a => .neg a
  | .neg a => .pos a

omit [DecidableEq α] in
@[simp] theorem complement_complement (l : Lit α) :
    l.complement.complement = l := by
  cases l <;> rfl

abbrev ConnClause (α : Type*) := List (Lit α)
abbrev ConnCNF (α : Type*) := List (ConnClause α)

/-- Trace step format aligned to PeTTa `step_reduce` / `step_extend`. -/
inductive ProofStep (α : Type*)
  | step_reduce : Lit α → ProofStep α
  | step_extend : Lit α → ConnClause α → ProofStep α
  deriving DecidableEq, Repr

abbrev ProofTrace (α : Type*) := List (ProofStep α)

/-- Concrete proof object format aligned to PeTTa `(proof fuel root trace)`. -/
structure ProofObj (α : Type*) where
  fuel : Nat
  root : ConnClause α
  trace : ProofTrace α
  deriving Repr

/--
Replay checker for a fixed clause matrix.

`goals` is the open goal list, `path` is the active path, and `trace` is consumed
step-by-step. This mirrors the concrete PeTTa replay checker control flow.
-/
def replay (clauses : ConnCNF α) (goals path : ConnClause α) : ProofTrace α → Bool
  | [] =>
      decide (goals = [])
  | step :: steps =>
      match goals with
      | [] => false
      | lit :: rest =>
          match step with
          | .step_reduce stepLit =>
              if lit = stepLit then
                if lit.complement ∈ path then
                  replay clauses rest (lit :: path) steps
                else
                  false
              else
                false
          | .step_extend stepLit clause =>
              if lit = stepLit then
                if clause ∈ clauses then
                  if lit.complement ∈ clause then
                    let newGoals := clause.erase lit.complement ++ rest
                    replay clauses newGoals (lit :: path) steps
                  else
                    false
                else
                  false
              else
                false

/-- Top-level checker for proof objects. -/
def checkProof (clauses : ConnCNF α) (p : ProofObj α) : Bool :=
  decide (p.root ∈ clauses) && replay clauses p.root [] p.trace

/-- Trace-indexed derivability (small-step semantics of replay). -/
inductive TraceDerivable (clauses : ConnCNF α) :
    ConnClause α → ConnClause α → ProofTrace α → Prop where
  | done (path : ConnClause α) :
      TraceDerivable clauses [] path []
  | reduce
      (lit : Lit α) (rest path : ConnClause α) (steps : ProofTrace α)
      (hComp : lit.complement ∈ path)
      (hSub : TraceDerivable clauses rest (lit :: path) steps) :
      TraceDerivable clauses (lit :: rest) path
        (.step_reduce lit :: steps)
  | extend
      (lit : Lit α) (rest path clause : ConnClause α) (steps : ProofTrace α)
      (hClause : clause ∈ clauses)
      (hComp : lit.complement ∈ clause)
      (hSub : TraceDerivable clauses (clause.erase lit.complement ++ rest) (lit :: path) steps) :
      TraceDerivable clauses (lit :: rest) path
        (.step_extend lit clause :: steps)

/-- Abstract connection-derivability, forgetting concrete trace objects. -/
inductive ConnDerivable (clauses : ConnCNF α) : ConnClause α → ConnClause α → Prop where
  | done (path : ConnClause α) :
      ConnDerivable clauses [] path
  | reduce
      (lit : Lit α) (rest path : ConnClause α)
      (hComp : lit.complement ∈ path)
      (hSub : ConnDerivable clauses rest (lit :: path)) :
      ConnDerivable clauses (lit :: rest) path
  | extend
      (lit : Lit α) (rest path clause : ConnClause α)
      (hClause : clause ∈ clauses)
      (hComp : lit.complement ∈ clause)
      (hSub : ConnDerivable clauses (clause.erase lit.complement ++ rest) (lit :: path)) :
      ConnDerivable clauses (lit :: rest) path

theorem replay_true_of_traceDerivable
    (clauses goals path trace)
    (h : TraceDerivable (α := α) clauses goals path trace) :
    replay clauses goals path trace = true := by
  induction h with
  | done path =>
      simp [replay]
  | reduce lit rest path steps hComp hSub ih =>
      simp [replay, hComp, ih]
  | extend lit rest path clause steps hClause hComp hSub ih =>
      simp [replay, hClause, hComp, ih]

theorem traceDerivable_of_replay_true
    (clauses : ConnCNF α) :
    ∀ (goals path : ConnClause α) (trace : ProofTrace α),
      replay clauses goals path trace = true →
      TraceDerivable clauses goals path trace
  | goals, path, [], h => by
      have hnil : goals = [] := by
        simpa [replay] using (decide_eq_true_iff (p := goals = [])).1 h
      subst hnil
      exact TraceDerivable.done path
  | [], path, _ :: _, h => by
      simp [replay] at h
  | lit :: rest, path, step :: steps, h => by
      cases step with
      | step_reduce stepLit =>
          by_cases hEq : lit = stepLit
          · subst hEq
            by_cases hComp : lit.complement ∈ path
            · have hSub :
                replay clauses rest (lit :: path) steps = true := by
                  simpa [replay, hComp] using h
              exact TraceDerivable.reduce lit rest path steps hComp
                (traceDerivable_of_replay_true clauses rest (lit :: path) steps hSub)
            · simp [replay, hComp] at h
          · simp [replay, hEq] at h
      | step_extend stepLit clause =>
          by_cases hEq : lit = stepLit
          · subst hEq
            by_cases hClause : clause ∈ clauses
            · by_cases hComp : lit.complement ∈ clause
              · have hSub :
                  replay clauses (clause.erase lit.complement ++ rest) (lit :: path) steps = true := by
                    simpa [replay, hClause, hComp] using h
                exact TraceDerivable.extend lit rest path clause steps hClause hComp
                  (traceDerivable_of_replay_true clauses
                    (clause.erase lit.complement ++ rest) (lit :: path) steps hSub)
              · simp [replay, hClause, hComp] at h
            · simp [replay, hClause] at h
          · simp [replay, hEq] at h

theorem replay_true_iff_traceDerivable
    (clauses goals path trace) :
    replay (α := α) clauses goals path trace = true ↔
      TraceDerivable clauses goals path trace := by
  constructor
  · exact traceDerivable_of_replay_true (α := α) clauses goals path trace
  · intro h
    exact replay_true_of_traceDerivable (α := α) clauses goals path trace h

theorem TraceDerivable.toConnDerivable
    {clauses goals path trace}
    (h : TraceDerivable (α := α) clauses goals path trace) :
    ConnDerivable clauses goals path := by
  induction h with
  | done path =>
      exact ConnDerivable.done path
  | reduce lit rest path steps hComp hSub ih =>
      exact ConnDerivable.reduce lit rest path hComp ih
  | extend lit rest path clause steps hClause hComp hSub ih =>
      exact ConnDerivable.extend lit rest path clause hClause hComp ih

theorem ConnDerivable.exists_trace
    {clauses goals path}
    (h : ConnDerivable (α := α) clauses goals path) :
    ∃ trace, TraceDerivable clauses goals path trace := by
  induction h with
  | done path =>
      exact ⟨[], TraceDerivable.done path⟩
  | reduce lit rest path hComp hSub ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.step_reduce lit :: trace,
        TraceDerivable.reduce lit rest path trace hComp htrace⟩
  | extend lit rest path clause hClause hComp hSub ih =>
      rcases ih with ⟨trace, htrace⟩
      exact ⟨.step_extend lit clause :: trace,
        TraceDerivable.extend lit rest path clause trace hClause hComp htrace⟩

theorem connDerivable_iff_exists_trace
    (clauses goals path) :
    ConnDerivable (α := α) clauses goals path ↔
      ∃ trace, TraceDerivable clauses goals path trace := by
  constructor
  · intro h
    exact ConnDerivable.exists_trace (α := α) h
  · rintro ⟨trace, htrace⟩
    exact htrace.toConnDerivable

/-- Trace-checker soundness: accepted traces imply abstract derivability. -/
theorem replay_sound
    {clauses goals path trace}
    (h : replay (α := α) clauses goals path trace = true) :
    ConnDerivable clauses goals path := by
  exact (traceDerivable_of_replay_true (α := α) clauses goals path trace h).toConnDerivable

/--
Trace-checker completeness against abstract connection semantics:
if the goals are derivable, some trace is accepted by replay.
-/
theorem replay_complete
    {clauses goals path}
    (h : ConnDerivable (α := α) clauses goals path) :
    ∃ trace, replay clauses goals path trace = true := by
  rcases ConnDerivable.exists_trace (α := α) h with ⟨trace, htrace⟩
  exact ⟨trace, replay_true_of_traceDerivable (α := α) clauses goals path trace htrace⟩

/-- Soundness + completeness for the proof-object checker against trace-indexed semantics. -/
theorem checkProof_true_iff_root_mem_and_traceDerivable
    (clauses : ConnCNF α) (p : ProofObj α) :
    checkProof (α := α) clauses p = true ↔
      p.root ∈ clauses ∧ TraceDerivable clauses p.root [] p.trace := by
  unfold checkProof
  constructor
  · intro h
    have hsplit :
        decide (p.root ∈ clauses) = true ∧ replay clauses p.root [] p.trace = true := by
      simpa [Bool.and_eq_true] using h
    refine ⟨(decide_eq_true_iff (p := p.root ∈ clauses)).1 hsplit.1,
      (replay_true_iff_traceDerivable (α := α) clauses p.root [] p.trace).1 hsplit.2⟩
  · rintro ⟨hRoot, hTrace⟩
    have hReplay :
        replay clauses p.root [] p.trace = true :=
      (replay_true_iff_traceDerivable (α := α) clauses p.root [] p.trace).2 hTrace
    have hRootB : decide (p.root ∈ clauses) = true :=
      (decide_eq_true_iff (p := p.root ∈ clauses)).2 hRoot
    simp [hRootB, hReplay]

/-- Concrete checker implies abstract root derivability (trace-erasing soundness). -/
theorem checkProof_sound
    (clauses : ConnCNF α) (p : ProofObj α) :
    checkProof (α := α) clauses p = true →
      p.root ∈ clauses ∧ ConnDerivable clauses p.root [] := by
  intro h
  rcases (checkProof_true_iff_root_mem_and_traceDerivable (α := α) clauses p).1 h with
    ⟨hRoot, hTrace⟩
  exact ⟨hRoot, hTrace.toConnDerivable⟩

/--
Existential checker completeness for proof objects:
if a root is in the matrix and abstractly derivable, there exists a concrete proof object
accepted by `checkProof`.
-/
theorem exists_checkProof_true_of_root_mem_and_connDerivable
    (clauses : ConnCNF α) (root : ConnClause α)
    (hRoot : root ∈ clauses)
    (hConn : ConnDerivable (α := α) clauses root []) :
    ∃ p : ProofObj α, checkProof clauses p = true := by
  rcases replay_complete (α := α) (clauses := clauses) (goals := root) (path := []) hConn with
    ⟨trace, hReplay⟩
  refine ⟨⟨trace.length, root, trace⟩, ?_⟩
  unfold checkProof
  have hRootB : decide (root ∈ clauses) = true :=
    (decide_eq_true_iff (p := root ∈ clauses)).2 hRoot
  simp [hRootB, hReplay]

/-! ## Operator-style refinement aliases (concrete API layer) -/

def op_replay_proof (clauses : ConnCNF α) (goals path : ConnClause α) (trace : ProofTrace α) : Bool :=
  replay clauses goals path trace

def op_check_proof (clauses : ConnCNF α) (p : ProofObj α) : Bool :=
  checkProof clauses p

def op_provable (clauses : ConnCNF α) (goals path : ConnClause α) : Prop :=
  ConnDerivable clauses goals path

theorem op_replay_refines
    (clauses : ConnCNF α) (goals path : ConnClause α) (trace : ProofTrace α) :
    op_replay_proof (α := α) clauses goals path trace = true →
      op_provable clauses goals path := by
  intro h
  exact replay_sound (α := α) h

theorem op_replay_complete
    (clauses : ConnCNF α) (goals path : ConnClause α)
    (h : op_provable (α := α) clauses goals path) :
    ∃ trace, op_replay_proof clauses goals path trace = true := by
  exact replay_complete (α := α) h

/-- Concrete checker implies abstract provability at root. -/
theorem op_check_proof_sound
    (clauses : ConnCNF α) (p : ProofObj α) :
    op_check_proof clauses p = true → p.root ∈ clauses ∧ op_provable clauses p.root [] := by
  intro h
  simpa [op_check_proof, op_provable] using
    (checkProof_sound (α := α) clauses p h)

/-! ## Executable DFS search (conn-prove style) and refinement -/

/--
Clause-extension helper parameterized by a recursive solver.
This mirrors the PeTTa `try-extend` loop over candidate clauses.
-/
def tryExtendWith
    (solver : ConnClause α → ConnClause α → Option (ProofTrace α))
    (clauses : ConnCNF α) (lit : Lit α) (rest path : ConnClause α) :
    ConnCNF α → Option (ProofTrace α)
  | [] => none
  | clause :: tail =>
      if lit.complement ∈ clause then
        let newGoals := clause.erase lit.complement ++ rest
        match solver newGoals (lit :: path) with
        | some tr => some (.step_extend lit clause :: tr)
        | none => tryExtendWith solver clauses lit rest path tail
      else
        tryExtendWith solver clauses lit rest path tail

/--
Executable depth-first connection prover with fuel.
This follows the same control pattern as PeTTa's `conn-prove`:
reduction first, then extension fallback.
-/
def connProveDFS (clauses : ConnCNF α) (goals path : ConnClause α) : Nat → Option (ProofTrace α)
  | 0 =>
      match goals with
      | [] => some []
      | _ :: _ => none
  | n + 1 =>
      match goals with
      | [] => some []
      | lit :: rest =>
          if lit.complement ∈ path then
            match connProveDFS clauses rest (lit :: path) n with
            | some tr => some (.step_reduce lit :: tr)
            | none =>
                tryExtendWith (fun g p => connProveDFS clauses g p n)
                  clauses lit rest path clauses
          else
            tryExtendWith (fun g p => connProveDFS clauses g p n)
              clauses lit rest path clauses

/-- Public `tryExtend` entry point aligned with PeTTa naming. -/
def tryExtendDFS
    (clauses : ConnCNF α) (lit : Lit α) (rest path : ConnClause α) (fuel : Nat)
    (cands : ConnCNF α) : Option (ProofTrace α) :=
  tryExtendWith (fun g p => connProveDFS clauses g p fuel) clauses lit rest path cands

/-- Soundness of `tryExtendWith` under a sound recursive solver. -/
theorem tryExtendWith_sound_of_some
    (solver : ConnClause α → ConnClause α → Option (ProofTrace α))
    (hsolver : ∀ g p tr, solver g p = some tr → TraceDerivable clauses g p tr)
    {lit : Lit α} {rest path : ConnClause α} {cands : ConnCNF α} {tr : ProofTrace α}
    (hsubset : ∀ c ∈ cands, c ∈ clauses)
    (h : tryExtendWith solver clauses lit rest path cands = some tr) :
    TraceDerivable clauses (lit :: rest) path tr := by
  induction cands generalizing tr with
  | nil =>
      simp [tryExtendWith] at h
  | cons clause tail ih =>
      by_cases hComp : lit.complement ∈ clause
      · simp [tryExtendWith, hComp] at h
        cases hSub : solver (clause.erase lit.complement ++ rest) (lit :: path) with
        | none =>
            have hsubsetTail : ∀ c ∈ tail, c ∈ clauses := by
              intro c hc
              exact hsubset c (by simp [hc])
            exact ih hsubsetTail (by simpa [hSub] using h)
        | some trSub =>
            have hEq : .step_extend lit clause :: trSub = tr := by
              simpa [hSub] using h
            cases hEq
            exact TraceDerivable.extend lit rest path clause trSub
              (hsubset clause (by simp))
              hComp
              (hsolver _ _ _ hSub)
      · have hsubsetTail : ∀ c ∈ tail, c ∈ clauses := by
          intro c hc
          exact hsubset c (by simp [hc])
        exact ih hsubsetTail (by simpa [tryExtendWith, hComp] using h)

/-- Soundness of `connProveDFS`: returned traces are semantically valid. -/
theorem connProveDFS_sound_of_some
    (clauses : ConnCNF α) :
    ∀ fuel goals path tr,
      connProveDFS clauses goals path fuel = some tr →
      TraceDerivable clauses goals path tr
  | 0, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveDFS] at h
          subst h
          exact TraceDerivable.done path
      | cons lit rest =>
          simp [connProveDFS] at h
  | n + 1, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveDFS] at h
          subst h
          exact TraceDerivable.done path
      | cons lit rest =>
          by_cases hPath : lit.complement ∈ path
          · simp [connProveDFS, hPath] at h
            cases hSub : connProveDFS clauses rest (lit :: path) n with
            | some trSub =>
                have hEq : .step_reduce lit :: trSub = tr := by
                  simpa [hSub] using h
                cases hEq
                exact TraceDerivable.reduce lit rest path trSub hPath
                  (connProveDFS_sound_of_some clauses n rest (lit :: path) trSub hSub)
            | none =>
                have hsubset : ∀ c ∈ clauses, c ∈ clauses := by
                  intro c hc
                  exact hc
                exact tryExtendWith_sound_of_some
                  (clauses := clauses)
                  (solver := fun g p => connProveDFS clauses g p n)
                  (hsolver := by
                    intro g p tr' hs
                    exact connProveDFS_sound_of_some clauses n g p tr' hs)
                  (lit := lit) (rest := rest) (path := path)
                  (cands := clauses) (tr := tr)
                  hsubset
                  (by simpa [hSub] using h)
          · have hsubset : ∀ c ∈ clauses, c ∈ clauses := by
              intro c hc
              exact hc
            exact tryExtendWith_sound_of_some
              (clauses := clauses)
              (solver := fun g p => connProveDFS clauses g p n)
              (hsolver := by
                intro g p tr' hs
                exact connProveDFS_sound_of_some clauses n g p tr' hs)
              (lit := lit) (rest := rest) (path := path)
              (cands := clauses) (tr := tr)
              hsubset
              (by simpa [connProveDFS, hPath] using h)

/-- DFS refinement: executable success implies abstract connection-derivability. -/
theorem connProveDFS_sound
    {clauses goals path fuel tr}
    (h : connProveDFS (α := α) clauses goals path fuel = some tr) :
    ConnDerivable clauses goals path := by
  exact (connProveDFS_sound_of_some (α := α) clauses fuel goals path tr h).toConnDerivable

/--
Completeness helper for extension loops:
if a candidate clause in the candidate list has a successful recursive branch,
then `tryExtendWith` succeeds.
-/
theorem tryExtendWith_exists_of_clause
    (solver : ConnClause α → ConnClause α → Option (ProofTrace α))
    {lit : Lit α} {rest path : ConnClause α}
    {cands : ConnCNF α} {clause : ConnClause α}
    (hmem : clause ∈ cands)
    (hcomp : lit.complement ∈ clause)
    (hsub : ∃ tr, solver (clause.erase lit.complement ++ rest) (lit :: path) = some tr) :
    ∃ tr, tryExtendWith solver clauses lit rest path cands = some tr := by
  induction cands with
  | nil =>
      cases hmem
  | cons head tail ih =>
      by_cases hEq : clause = head
      · subst hEq
        rcases hsub with ⟨trSub, hSub⟩
        exact ⟨.step_extend lit clause :: trSub, by simp [tryExtendWith, hcomp, hSub]⟩
      · have hmemTail : clause ∈ tail := by
          exact (List.mem_cons.1 hmem).resolve_left hEq
        by_cases hHeadComp : lit.complement ∈ head
        · cases hHeadSub : solver (head.erase lit.complement ++ rest) (lit :: path) with
          | some trHead =>
              exact ⟨.step_extend lit head :: trHead, by
                simp [tryExtendWith, hHeadComp, hHeadSub]⟩
          | none =>
              rcases ih hmemTail with ⟨trTail, hTail⟩
              exact ⟨trTail, by simpa [tryExtendWith, hHeadComp, hHeadSub] using hTail⟩
        · rcases ih hmemTail with ⟨trTail, hTail⟩
          exact ⟨trTail, by simpa [tryExtendWith, hHeadComp] using hTail⟩

/--
Witness-level completeness for DFS with a concrete trace-length budget:
if a trace derivation exists and `fuel` is at least its length, DFS returns some trace.
-/
theorem connProveDFS_complete_of_trace
    {clauses goals path trace fuel}
    (hDer : TraceDerivable (α := α) clauses goals path trace)
    (hLen : trace.length ≤ fuel) :
    ∃ tr, connProveDFS clauses goals path fuel = some tr := by
  induction hDer generalizing fuel with
  | done path =>
      refine ⟨[], ?_⟩
      cases fuel <;> simp [connProveDFS]
  | reduce lit rest path steps hComp hSub ih =>
      cases fuel with
      | zero =>
          simp at hLen
      | succ n =>
          have hLenSub : steps.length ≤ n := by
            exact Nat.le_of_succ_le_succ (by simpa using hLen)
          rcases ih hLenSub with ⟨trSub, hSubRun⟩
          refine ⟨.step_reduce lit :: trSub, ?_⟩
          simp [connProveDFS, hComp, hSubRun]
  | extend lit rest path clause steps hClause hComp hSub ih =>
      cases fuel with
      | zero =>
          simp at hLen
      | succ n =>
          have hLenSub : steps.length ≤ n := by
            exact Nat.le_of_succ_le_succ (by simpa using hLen)
          rcases ih hLenSub with ⟨trSub, hSubRun⟩
          by_cases hPath : lit.complement ∈ path
          · cases hRed : connProveDFS clauses rest (lit :: path) n with
            | some trRed =>
                exact ⟨.step_reduce lit :: trRed, by
                  simp [connProveDFS, hPath, hRed]⟩
            | none =>
                have hTry :
                    ∃ tr, tryExtendWith (fun g p => connProveDFS clauses g p n)
                      clauses lit rest path clauses = some tr := by
                  exact tryExtendWith_exists_of_clause
                    (solver := fun g p => connProveDFS clauses g p n)
                    (clauses := clauses)
                    (lit := lit) (rest := rest) (path := path)
                    (cands := clauses) (clause := clause)
                    hClause hComp ⟨trSub, hSubRun⟩
                rcases hTry with ⟨tr, hTryEq⟩
                exact ⟨tr, by simp [connProveDFS, hPath, hRed, hTryEq]⟩
          · have hTry :
              ∃ tr, tryExtendWith (fun g p => connProveDFS clauses g p n)
                clauses lit rest path clauses = some tr := by
              exact tryExtendWith_exists_of_clause
                (solver := fun g p => connProveDFS clauses g p n)
                (clauses := clauses)
                (lit := lit) (rest := rest) (path := path)
                (cands := clauses) (clause := clause)
                hClause hComp ⟨trSub, hSubRun⟩
            rcases hTry with ⟨tr, hTryEq⟩
            exact ⟨tr, by simp [connProveDFS, hPath, hTryEq]⟩

/-- Existential DFS completeness at abstract level. -/
theorem connProveDFS_witness_complete
    {clauses goals path}
    (h : ConnDerivable (α := α) clauses goals path) :
    ∃ fuel tr, connProveDFS clauses goals path fuel = some tr := by
  rcases ConnDerivable.exists_trace (α := α) h with ⟨trace, hTrace⟩
  rcases connProveDFS_complete_of_trace
      (clauses := clauses) (goals := goals) (path := path)
      (trace := trace) (fuel := trace.length)
      hTrace (Nat.le_refl _) with ⟨tr, hRun⟩
  exact ⟨trace.length, tr, hRun⟩

/-! ## Root-wise and branch-complete proof collection (PeTTa parity layer) -/

/-- Root-wise proof object, aligned with PeTTa `root-proof`. -/
def rootProof (clauses : ConnCNF α) (root : ConnClause α) (fuel : Nat) : Option (ProofObj α) :=
  match connProveDFS clauses root [] fuel with
  | some tr => some { fuel := fuel, root := root, trace := tr }
  | none => none

/-- Root-wise collection helper over an explicit root list. -/
def collectRootProofs (clauses : ConnCNF α) (fuel : Nat) : ConnCNF α → List (ProofObj α)
  | [] => []
  | root :: tail =>
      match rootProof clauses root fuel with
      | some p => p :: collectRootProofs clauses fuel tail
      | none => collectRootProofs clauses fuel tail

/-- Root-wise collection, aligned with PeTTa `collect-proofs`. -/
def collectProofs (clauses : ConnCNF α) (fuel : Nat) : List (ProofObj α) :=
  collectRootProofs clauses fuel clauses

/-- Prefix a step onto every trace (PeTTa `prepend-step-to-traces`). -/
def prependStepToTraces (step : ProofStep α) (trs : List (ProofTrace α)) : List (ProofTrace α) :=
  trs.map (fun tr => step :: tr)

/-- Extension loop collecting all branch traces from candidate clauses. -/
def tryExtendAllWith
    (solverAll : ConnClause α → ConnClause α → List (ProofTrace α))
    (clauses : ConnCNF α) (lit : Lit α) (rest path : ConnClause α) :
    ConnCNF α → List (ProofTrace α)
  | [] => []
  | clause :: tail =>
      let here :=
        if lit.complement ∈ clause then
          let newGoals := clause.erase lit.complement ++ rest
          prependStepToTraces (.step_extend lit clause) (solverAll newGoals (lit :: path))
        else
          []
      here ++ tryExtendAllWith solverAll clauses lit rest path tail

/-- Branch-complete DFS search returning all traces within fuel. -/
def connProveAll (clauses : ConnCNF α) (goals path : ConnClause α) : Nat → List (ProofTrace α)
  | 0 =>
      match goals with
      | [] => [[]]
      | _ :: _ => []
  | n + 1 =>
      match goals with
      | [] => [[]]
      | lit :: rest =>
          let rTraces :=
            if lit.complement ∈ path then
              prependStepToTraces
                (.step_reduce lit)
                (connProveAll clauses rest (lit :: path) n)
            else
              []
          let eTraces :=
            tryExtendAllWith
              (fun g p => connProveAll clauses g p n)
              clauses lit rest path clauses
          rTraces ++ eTraces

/-- Wrap traces as `(proof fuel root trace)` objects. -/
def wrapTracesAsProofs (fuel : Nat) (root : ConnClause α)
    (trs : List (ProofTrace α)) : List (ProofObj α) :=
  trs.map (fun tr => ({ fuel := fuel, root := root, trace := tr } : ProofObj α))

/-- All proofs for a fixed root, aligned with PeTTa `root-proofs-all`. -/
def rootProofsAll (clauses : ConnCNF α) (root : ConnClause α) (fuel : Nat) : List (ProofObj α) :=
  wrapTracesAsProofs fuel root (connProveAll clauses root [] fuel)

/-- Helper over root lists for branch-complete collection. -/
def collectRootProofsAll (clauses : ConnCNF α) (fuel : Nat) : ConnCNF α → List (ProofObj α)
  | [] => []
  | root :: tail =>
      rootProofsAll clauses root fuel ++ collectRootProofsAll clauses fuel tail

/-- Branch-complete collection, aligned with PeTTa `collect-proofs-all`. -/
def collectProofsAll (clauses : ConnCNF α) (fuel : Nat) : List (ProofObj α) :=
  collectRootProofsAll clauses fuel clauses

/-! ## Ranking and topK correctness over collected proofs -/

/-- Default deterministic ranking score (longer trace = higher score). -/
def proofRankScore (p : ProofObj α) : Nat :=
  p.trace.length

/-- Insert one proof into a descending-by-score list. -/
def insertProofByScore (score : ProofObj α → Nat)
    (p : ProofObj α) : List (ProofObj α) → List (ProofObj α)
  | [] => [p]
  | h :: t =>
      if score p >= score h then
        p :: h :: t
      else
        h :: insertProofByScore score p t

/-- Insertion sort descending by score. -/
def sortProofsDescByScore (score : ProofObj α → Nat) : List (ProofObj α) → List (ProofObj α)
  | [] => []
  | h :: t => insertProofByScore score h (sortProofsDescByScore score t)

/-- Top-k selection after descending score sort. -/
def topKProofsByScore (score : ProofObj α → Nat) (proofs : List (ProofObj α))
    (topK : Nat) : List (ProofObj α) :=
  (sortProofsDescByScore score proofs).take topK

/-- Top-k over root-wise collection. -/
def topKCollectProofs (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : List (ProofObj α) :=
  topKProofsByScore score (collectProofs clauses fuel) topK

/-- Top-k over branch-complete collection. -/
def topKCollectProofsAll (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : List (ProofObj α) :=
  topKProofsByScore score (collectProofsAll clauses fuel) topK

/-- Contract-level output object mirroring PeTTa Chapter-13 bundle shape. -/
structure Ch13Bundle (α : Type u) where
  proofs : List (ProofObj α)
  topKProofs : List (ProofObj α)

/-- Root-wise bundle endpoint (PeTTa `op_leancop_ch13_bundle` contract). -/
def ch13Bundle (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : Ch13Bundle α :=
  { proofs := collectProofs clauses fuel
  , topKProofs := topKCollectProofs score clauses fuel topK
  }

/-- Branch-complete bundle endpoint (PeTTa `op_leancop_ch13_bundle_all` contract). -/
def ch13BundleAll (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : Ch13Bundle α :=
  { proofs := collectProofsAll clauses fuel
  , topKProofs := topKCollectProofsAll score clauses fuel topK
  }

omit [DecidableEq α] in
theorem mem_insertProofByScore_iff
    (score : ProofObj α → Nat) (p x : ProofObj α) (ps : List (ProofObj α)) :
    x ∈ insertProofByScore score p ps ↔ x = p ∨ x ∈ ps := by
  induction ps with
  | nil =>
      simp [insertProofByScore]
  | cons h t ih =>
      by_cases hge : score p >= score h
      · simp [insertProofByScore, hge]
      · simp [insertProofByScore, hge, ih]
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

omit [DecidableEq α] in
theorem mem_sortProofsDescByScore_iff
    (score : ProofObj α → Nat) (x : ProofObj α) (ps : List (ProofObj α)) :
    x ∈ sortProofsDescByScore score ps ↔ x ∈ ps := by
  induction ps with
  | nil =>
      simp [sortProofsDescByScore]
  | cons h t ih =>
      simp [sortProofsDescByScore, mem_insertProofByScore_iff, ih]

omit [DecidableEq α] in
theorem mem_topKProofsByScore_implies_mem
    (score : ProofObj α → Nat) {proofs : List (ProofObj α)} {topK : Nat}
    {p : ProofObj α}
    (h : p ∈ topKProofsByScore score proofs topK) :
    p ∈ proofs := by
  have hSort : p ∈ sortProofsDescByScore score proofs := List.mem_of_mem_take h
  exact (mem_sortProofsDescByScore_iff score p proofs).1 hSort

omit [DecidableEq α] in
theorem length_topKProofsByScore_le
    (score : ProofObj α → Nat) (proofs : List (ProofObj α)) (topK : Nat) :
    (topKProofsByScore score proofs topK).length ≤ topK := by
  simp [topKProofsByScore]

omit [DecidableEq α] in
theorem topKProofsByScore_eq_sorted_of_len_le
    (score : ProofObj α → Nat) {proofs : List (ProofObj α)} {topK : Nat}
    (hLen : (sortProofsDescByScore score proofs).length ≤ topK) :
    topKProofsByScore score proofs topK = sortProofsDescByScore score proofs := by
  simpa [topKProofsByScore] using
    (List.take_eq_self_iff (sortProofsDescByScore score proofs)).2 hLen

theorem mem_topKCollectProofs_implies_mem_collectProofs
    (score : ProofObj α → Nat) {clauses : ConnCNF α} {fuel topK : Nat}
    {p : ProofObj α}
    (h : p ∈ topKCollectProofs score clauses fuel topK) :
    p ∈ collectProofs clauses fuel := by
  exact mem_topKProofsByScore_implies_mem score h

theorem mem_topKCollectProofsAll_implies_mem_collectProofsAll
    (score : ProofObj α → Nat) {clauses : ConnCNF α} {fuel topK : Nat}
    {p : ProofObj α}
    (h : p ∈ topKCollectProofsAll score clauses fuel topK) :
    p ∈ collectProofsAll clauses fuel := by
  exact mem_topKProofsByScore_implies_mem score h

theorem length_topKCollectProofsAll_le
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (topKCollectProofsAll score clauses fuel topK).length ≤ topK := by
  exact length_topKProofsByScore_le score (collectProofsAll clauses fuel) topK

/-- Contract parity: bundle proofs field is exactly root-wise proof collection. -/
theorem ch13Bundle_proofs_eq_collectProofs
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (ch13Bundle score clauses fuel topK).proofs = collectProofs clauses fuel := rfl

/-- Contract parity: bundle topK field is exactly root-wise topK projection. -/
theorem ch13Bundle_topK_eq_topKCollectProofs
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (ch13Bundle score clauses fuel topK).topKProofs =
      topKCollectProofs score clauses fuel topK := rfl

/-- Contract parity: branch-complete bundle proofs field matches `collectProofsAll`. -/
theorem ch13BundleAll_proofs_eq_collectProofsAll
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (ch13BundleAll score clauses fuel topK).proofs = collectProofsAll clauses fuel := rfl

/-- Contract parity: branch-complete bundle topK field matches `topKCollectProofsAll`. -/
theorem ch13BundleAll_topK_eq_topKCollectProofsAll
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (ch13BundleAll score clauses fuel topK).topKProofs =
      topKCollectProofsAll score clauses fuel topK := rfl

/-- Bundle-level topK membership always comes from bundle-level branch-complete proofs. -/
theorem mem_ch13BundleAll_topK_implies_mem_ch13BundleAll_proofs
    (score : ProofObj α → Nat) {clauses : ConnCNF α} {fuel topK : Nat}
    {p : ProofObj α}
    (h : p ∈ (ch13BundleAll score clauses fuel topK).topKProofs) :
    p ∈ (ch13BundleAll score clauses fuel topK).proofs := by
  simpa [ch13BundleAll] using
    (mem_topKCollectProofsAll_implies_mem_collectProofsAll
      (score := score) (clauses := clauses) (fuel := fuel) (topK := topK) (p := p) h)

omit [DecidableEq α] in
theorem mem_prependStepToTraces_of_mem
    {step : ProofStep α} {tr : ProofTrace α} {trs : List (ProofTrace α)}
    (h : tr ∈ trs) :
    step :: tr ∈ prependStepToTraces step trs := by
  unfold prependStepToTraces
  exact List.mem_map.mpr ⟨tr, h, rfl⟩

omit [DecidableEq α] in
theorem mem_wrapTracesAsProofs_of_mem
    {fuel : Nat} {root : ConnClause α}
    {tr : ProofTrace α} {trs : List (ProofTrace α)}
    (h : tr ∈ trs) :
    ({ fuel := fuel, root := root, trace := tr } : ProofObj α) ∈ wrapTracesAsProofs fuel root trs := by
  unfold wrapTracesAsProofs
  exact List.mem_map.mpr ⟨tr, h, rfl⟩

theorem tryExtendWith_some_mem_tryExtendAllWith
    (solver : ConnClause α → ConnClause α → Option (ProofTrace α))
    (solverAll : ConnClause α → ConnClause α → List (ProofTrace α))
    (hsolver : ∀ g p tr, solver g p = some tr → tr ∈ solverAll g p)
    {clauses : ConnCNF α} {lit : Lit α} {rest path : ConnClause α}
    {cands : ConnCNF α} {tr : ProofTrace α}
    (h : tryExtendWith solver clauses lit rest path cands = some tr) :
    tr ∈ tryExtendAllWith solverAll clauses lit rest path cands := by
  induction cands generalizing tr with
  | nil =>
      simp [tryExtendWith] at h
  | cons clause tail ih =>
      by_cases hComp : lit.complement ∈ clause
      · simp [tryExtendWith, tryExtendAllWith, hComp] at h ⊢
        cases hSub : solver (clause.erase lit.complement ++ rest) (lit :: path) with
        | none =>
            exact Or.inr (ih (by simpa [hSub] using h))
        | some trSub =>
            have hEq : .step_extend lit clause :: trSub = tr := by simpa [hSub] using h
            subst hEq
            have hmemSub : trSub ∈ solverAll (clause.erase lit.complement ++ rest) (lit :: path) :=
              hsolver _ _ _ hSub
            exact Or.inl (mem_prependStepToTraces_of_mem (step := .step_extend lit clause) hmemSub)
      · have hTail : tryExtendWith solver clauses lit rest path tail = some tr := by
          simpa [tryExtendWith, hComp] using h
        simpa [tryExtendAllWith, hComp] using ih hTail

/-- Parity: every DFS witness appears in branch-complete `connProveAll`. -/
theorem connProveDFS_some_mem_connProveAll
    (clauses : ConnCNF α) :
    ∀ fuel goals path tr,
      connProveDFS clauses goals path fuel = some tr →
      tr ∈ connProveAll clauses goals path fuel
  | 0, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveDFS] at h
          subst h
          simp [connProveAll]
      | cons lit rest =>
          simp [connProveDFS] at h
  | n + 1, goals, path, tr, h => by
      cases goals with
      | nil =>
          simp [connProveDFS] at h
          subst h
          simp [connProveAll]
      | cons lit rest =>
          by_cases hPath : lit.complement ∈ path
          · simp [connProveDFS, hPath] at h
            cases hSub : connProveDFS clauses rest (lit :: path) n with
            | some trSub =>
                have hEq : .step_reduce lit :: trSub = tr := by simpa [hSub] using h
                subst hEq
                have hMemSub : trSub ∈ connProveAll clauses rest (lit :: path) n :=
                  connProveDFS_some_mem_connProveAll clauses n rest (lit :: path) trSub hSub
                have hMemRed :
                    .step_reduce lit :: trSub ∈
                      prependStepToTraces (.step_reduce lit)
                        (connProveAll clauses rest (lit :: path) n) :=
                  mem_prependStepToTraces_of_mem (step := .step_reduce lit) hMemSub
                have hMemRedIf :
                    .step_reduce lit :: trSub ∈
                      (if lit.complement ∈ path then
                        prependStepToTraces (.step_reduce lit)
                          (connProveAll clauses rest (lit :: path) n)
                       else []) := by
                  simpa [hPath] using hMemRed
                exact List.mem_append.mpr (Or.inl hMemRedIf)
            | none =>
                have hMemExt :
                    tr ∈ tryExtendAllWith
                      (fun g p => connProveAll clauses g p n)
                      clauses lit rest path clauses := by
                  exact tryExtendWith_some_mem_tryExtendAllWith
                    (solver := fun g p => connProveDFS clauses g p n)
                    (solverAll := fun g p => connProveAll clauses g p n)
                    (hsolver := by
                      intro g p tr' hs
                      exact connProveDFS_some_mem_connProveAll clauses n g p tr' hs)
                    (clauses := clauses) (lit := lit) (rest := rest) (path := path)
                    (cands := clauses) (tr := tr)
                    (by simpa [hSub] using h)
                exact List.mem_append.mpr (Or.inr hMemExt)
          · have hMemExt :
              tr ∈ tryExtendAllWith
                (fun g p => connProveAll clauses g p n)
                clauses lit rest path clauses := by
              exact tryExtendWith_some_mem_tryExtendAllWith
                (solver := fun g p => connProveDFS clauses g p n)
                (solverAll := fun g p => connProveAll clauses g p n)
                (hsolver := by
                  intro g p tr' hs
                  exact connProveDFS_some_mem_connProveAll clauses n g p tr' hs)
                (clauses := clauses) (lit := lit) (rest := rest) (path := path)
                (cands := clauses) (tr := tr)
                (by simpa [connProveDFS, hPath] using h)
            simpa [connProveAll, hPath] using hMemExt

theorem rootProof_mem_rootProofsAll_of_some
    {clauses : ConnCNF α} {root : ConnClause α} {fuel : Nat} {p : ProofObj α}
    (h : rootProof clauses root fuel = some p) :
    p ∈ rootProofsAll clauses root fuel := by
  unfold rootProof at h
  cases hConn : connProveDFS clauses root [] fuel with
  | none =>
      simp [hConn] at h
  | some tr =>
      have hp : ({ fuel := fuel, root := root, trace := tr } : ProofObj α) = p := by
        simpa [hConn] using h
      subst hp
      unfold rootProofsAll
      exact mem_wrapTracesAsProofs_of_mem
        (connProveDFS_some_mem_connProveAll
          (clauses := clauses) fuel root [] tr hConn)

theorem rootProofsAll_mem_collectRootProofsAll_of_mem_root
    {clauses roots : ConnCNF α} {fuel : Nat}
    {root : ConnClause α} {p : ProofObj α}
    (hRoot : root ∈ roots)
    (hp : p ∈ rootProofsAll clauses root fuel) :
    p ∈ collectRootProofsAll clauses fuel roots := by
  induction roots generalizing root p with
  | nil =>
      cases hRoot
  | cons r rs ih =>
      simp [collectRootProofsAll] at hRoot ⊢
      cases hRoot with
      | inl hr =>
          subst hr
          exact Or.inl hp
      | inr hTail =>
          exact Or.inr (ih hTail hp)

theorem proof_mem_collectProofsAll_of_root_mem_trace_mem
    {clauses : ConnCNF α} {root : ConnClause α}
    {fuel : Nat} {tr : ProofTrace α}
    (hRoot : root ∈ clauses)
    (hTr : tr ∈ connProveAll clauses root [] fuel) :
    ({ fuel := fuel, root := root, trace := tr } : ProofObj α) ∈ collectProofsAll clauses fuel := by
  unfold collectProofsAll
  exact rootProofsAll_mem_collectRootProofsAll_of_mem_root
    (clauses := clauses) (roots := clauses) (fuel := fuel)
    (root := root)
    hRoot
    (mem_wrapTracesAsProofs_of_mem hTr)

/--
Mode monotonicity (PeTTa parity):
root-wise collection is included in branch-complete collection at the same fuel.
-/
theorem collectRootProofs_subset_collectRootProofsAll
    (clauses : ConnCNF α) (fuel : Nat) :
    ∀ roots p,
      p ∈ collectRootProofs clauses fuel roots →
      p ∈ collectRootProofsAll clauses fuel roots := by
  intro roots
  induction roots with
  | nil =>
      intro p hp
      simp [collectRootProofs] at hp
  | cons root tail ih =>
      intro p hp
      unfold collectRootProofs at hp
      cases hRoot : rootProof clauses root fuel with
      | none =>
          have hpTail : p ∈ collectRootProofs clauses fuel tail := by
            simpa [hRoot] using hp
          have hTailAll := ih p hpTail
          exact List.mem_append.mpr <| Or.inr (by simpa [collectRootProofsAll] using hTailAll)
      | some pr =>
          have hsplit : p = pr ∨ p ∈ collectRootProofs clauses fuel tail := by
            simpa [hRoot] using hp
          cases hsplit with
          | inl hpEq =>
              subst hpEq
              have hInRoot : p ∈ rootProofsAll clauses root fuel :=
                rootProof_mem_rootProofsAll_of_some (clauses := clauses) (root := root) (fuel := fuel)
                  (p := p) hRoot
              exact List.mem_append.mpr <| Or.inl (by simpa [collectRootProofsAll] using hInRoot)
          | inr hpTail =>
              have hTailAll := ih p hpTail
              exact List.mem_append.mpr <| Or.inr (by simpa [collectRootProofsAll] using hTailAll)

theorem collectProofs_subset_collectProofsAll
    (clauses : ConnCNF α) (fuel : Nat) :
    ∀ p, p ∈ collectProofs clauses fuel → p ∈ collectProofsAll clauses fuel := by
  intro p hp
  simpa [collectProofs, collectProofsAll] using
    (collectRootProofs_subset_collectRootProofsAll
      (clauses := clauses) (fuel := fuel) (roots := clauses) p hp)

/-! ## Canary fixtures matching PeTTa-style proof objects -/

section Canary

abbrev cPos (a : α) : ConnClause α := [Lit.pos a]
abbrev cNeg (a : α) : ConnClause α := [Lit.neg a]

variable (pAtom : α)

def unsatClauses : ConnCNF α := [cPos pAtom, cNeg pAtom]

def unsatWitnessTrace : ProofTrace α :=
  [.step_extend (Lit.pos pAtom) (cNeg pAtom)]

def unsatWitnessProof : ProofObj α :=
  { fuel := 1, root := cPos pAtom, trace := unsatWitnessTrace pAtom }

theorem canary_unsat_ground_checkProof_true :
    checkProof (clauses := unsatClauses pAtom) (unsatWitnessProof pAtom) = true := by
  unfold checkProof unsatWitnessProof unsatWitnessTrace unsatClauses cPos cNeg replay
  simp [Lit.complement]
  simp [replay]

theorem canary_forged_reduce_rejected :
    checkProof
      (clauses := unsatClauses pAtom)
      ({ fuel := 1
       , root := cPos pAtom
       , trace := [.step_reduce (Lit.pos pAtom)] } : ProofObj α)
      = false := by
  unfold checkProof unsatClauses cPos cNeg replay
  simp [Lit.complement]

theorem canary_singleton_not_checkable
    (hNotDer : ¬ ConnDerivable ([cPos pAtom] : ConnCNF α) (cPos pAtom) []) :
    ¬ ∃ p : ProofObj α, checkProof ([cPos pAtom] : ConnCNF α) p = true := by
  intro hEx
  rcases hEx with ⟨p, hp⟩
  have hSound := checkProof_sound
    (α := α) ([cPos pAtom] : ConnCNF α) p hp
  have hRootEq : p.root = cPos pAtom := by
    simpa using hSound.1
  exact hNotDer (by simpa [hRootEq] using hSound.2)

end Canary

/-! ## PeTTa Fixture Map (test_leancop_* parity names) -/

section PeTTaFixtureMap

inductive FixtureAtom where
  | p | q
  deriving DecidableEq, Repr

open FixtureAtom

def ic_unsat_c1 : ConnClause FixtureAtom := [Lit.pos p]
def ic_unsat_c2 : ConnClause FixtureAtom := [Lit.neg p]
def ic_unsat_clauses : ConnCNF FixtureAtom := [ic_unsat_c1, ic_unsat_c2]
def ic_unsat_root : ConnClause FixtureAtom := ic_unsat_c1

def ic_sat_clauses : ConnCNF FixtureAtom := [ic_unsat_c1]
def ic_sat_root : ConnClause FixtureAtom := ic_unsat_c1

def ic_branching_c1 : ConnClause FixtureAtom := [Lit.pos p, Lit.pos q]
def ic_branching_c2 : ConnClause FixtureAtom := [Lit.neg p]
def ic_branching_c3 : ConnClause FixtureAtom := [Lit.neg q]
def ic_branching_clauses : ConnCNF FixtureAtom :=
  [ic_branching_c1, ic_branching_c2, ic_branching_c3]

def ic_branching_root_negp : ConnClause FixtureAtom := ic_branching_c2
def ic_branching_root_negq : ConnClause FixtureAtom := ic_branching_c3

def ic_unsat_proof : ProofObj FixtureAtom where
  fuel := 2
  root := ic_unsat_root
  trace := [.step_extend (Lit.pos p) ic_unsat_c2]

def ic_branching_negp_proof : ProofObj FixtureAtom where
  fuel := 3
  root := ic_branching_root_negp
  trace := [.step_extend (Lit.neg p) ic_branching_c1,
            .step_extend (Lit.pos q) ic_branching_c3]

def ic_branching_negq_proof : ProofObj FixtureAtom where
  fuel := 3
  root := ic_branching_root_negq
  trace := [.step_extend (Lit.neg q) ic_branching_c1,
            .step_extend (Lit.pos p) ic_branching_c2]

theorem ic_unsat_checkProof_true :
    checkProof ic_unsat_clauses ic_unsat_proof = true := by
  decide

theorem ic_sat_connProve_none :
    ∀ fuel, connProveDFS ic_sat_clauses ic_sat_root [] fuel = none := by
  intro fuel
  cases fuel with
  | zero =>
      simp [connProveDFS, ic_sat_root, ic_unsat_c1]
  | succ n =>
      simp [connProveDFS, ic_sat_root, ic_sat_clauses, ic_unsat_c1, tryExtendWith, Lit.complement]

theorem ic_unsat_connProve_has_proof :
    ∃ tr, connProveDFS ic_unsat_clauses ic_unsat_root [] 2 = some tr := by
  refine ⟨ic_unsat_proof.trace, ?_⟩
  decide

theorem ic_branching_negp_checkProof_true :
    checkProof ic_branching_clauses ic_branching_negp_proof = true := by
  decide

theorem ic_branching_negq_checkProof_true :
    checkProof ic_branching_clauses ic_branching_negq_proof = true := by
  decide

theorem ic_branching_two_distinct_root_proofs :
    ic_branching_root_negp ≠ ic_branching_root_negq
      ∧ checkProof ic_branching_clauses ic_branching_negp_proof = true
      ∧ checkProof ic_branching_clauses ic_branching_negq_proof = true := by
  decide

theorem ic_branching_negp_connProve_has_proof :
    ∃ tr, connProveDFS ic_branching_clauses ic_branching_root_negp [] 3 = some tr := by
  have hChk : checkProof ic_branching_clauses ic_branching_negp_proof = true := by
    decide
  have hTrace : TraceDerivable ic_branching_clauses ic_branching_root_negp [] ic_branching_negp_proof.trace :=
    (checkProof_true_iff_root_mem_and_traceDerivable
      (clauses := ic_branching_clauses) (p := ic_branching_negp_proof)).1 hChk |>.2
  simpa [ic_branching_negp_proof] using
    connProveDFS_complete_of_trace
      (clauses := ic_branching_clauses)
      (goals := ic_branching_root_negp) (path := [])
      (trace := ic_branching_negp_proof.trace) (fuel := 3)
      hTrace (by decide)

theorem ic_branching_negq_connProve_has_proof :
    ∃ tr, connProveDFS ic_branching_clauses ic_branching_root_negq [] 3 = some tr := by
  have hChk : checkProof ic_branching_clauses ic_branching_negq_proof = true := by
    decide
  have hTrace : TraceDerivable ic_branching_clauses ic_branching_root_negq [] ic_branching_negq_proof.trace :=
    (checkProof_true_iff_root_mem_and_traceDerivable
      (clauses := ic_branching_clauses) (p := ic_branching_negq_proof)).1 hChk |>.2
  simpa [ic_branching_negq_proof] using
    connProveDFS_complete_of_trace
      (clauses := ic_branching_clauses)
      (goals := ic_branching_root_negq) (path := [])
      (trace := ic_branching_negq_proof.trace) (fuel := 3)
      hTrace (by decide)

/-- Fixture-level parity: root-wise proofs are included in branch-complete proofs (unsat case). -/
theorem ic_unsat_collectProofs_subset_collectProofsAll :
    ∀ p, p ∈ collectProofs ic_unsat_clauses 2 → p ∈ collectProofsAll ic_unsat_clauses 2 := by
  intro p hp
  exact collectProofs_subset_collectProofsAll (clauses := ic_unsat_clauses) (fuel := 2) p hp

/-- Fixture-level parity: root-wise proofs are included in branch-complete proofs (branching case). -/
theorem ic_branching_collectProofs_subset_collectProofsAll :
    ∀ p, p ∈ collectProofs ic_branching_clauses 3 → p ∈ collectProofsAll ic_branching_clauses 3 := by
  intro p hp
  exact collectProofs_subset_collectProofsAll (clauses := ic_branching_clauses) (fuel := 3) p hp

/--
Branch-complete fixture parity:
`collectProofsAll` contains proofs for both distinct branching roots.
-/
theorem ic_branching_collectProofsAll_two_distinct_roots :
    ∃ p1 p2 : ProofObj FixtureAtom,
      p1.root ≠ p2.root
        ∧ p1 ∈ collectProofsAll ic_branching_clauses 3
        ∧ p2 ∈ collectProofsAll ic_branching_clauses 3 := by
  rcases ic_branching_negp_connProve_has_proof with ⟨tr1, h1⟩
  rcases ic_branching_negq_connProve_has_proof with ⟨tr2, h2⟩
  let p1 : ProofObj FixtureAtom := { fuel := 3, root := ic_branching_root_negp, trace := tr1 }
  let p2 : ProofObj FixtureAtom := { fuel := 3, root := ic_branching_root_negq, trace := tr2 }
  refine ⟨p1, p2, ?_, ?_, ?_⟩
  · intro hEq
    have hRootEq : ic_branching_root_negp = ic_branching_root_negq := by
      simpa [p1, p2] using hEq
    exact (by decide : ic_branching_root_negp ≠ ic_branching_root_negq) hRootEq
  · have hTr1 : tr1 ∈ connProveAll ic_branching_clauses ic_branching_root_negp [] 3 :=
      connProveDFS_some_mem_connProveAll
        (clauses := ic_branching_clauses) 3 ic_branching_root_negp [] tr1 h1
    simpa [p1] using
      (proof_mem_collectProofsAll_of_root_mem_trace_mem
        (clauses := ic_branching_clauses)
        (root := ic_branching_root_negp) (fuel := 3) (tr := tr1)
        (by decide) hTr1)
  · have hTr2 : tr2 ∈ connProveAll ic_branching_clauses ic_branching_root_negq [] 3 :=
      connProveDFS_some_mem_connProveAll
        (clauses := ic_branching_clauses) 3 ic_branching_root_negq [] tr2 h2
    simpa [p2] using
      (proof_mem_collectProofsAll_of_root_mem_trace_mem
        (clauses := ic_branching_clauses)
        (root := ic_branching_root_negq) (fuel := 3) (tr := tr2)
        (by decide) hTr2)

end PeTTaFixtureMap

end PropositionalConnection

end Mettapedia.Logic.LP
