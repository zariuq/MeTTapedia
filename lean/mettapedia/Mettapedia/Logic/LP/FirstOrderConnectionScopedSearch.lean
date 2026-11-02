import Mettapedia.Logic.LP.FirstOrderConnectionScopeSemantics

/-!
# Scoped connection search returns checked scoped proofs

The DFS is the existing reduction/extension search over a scope-indexed
clause source. Its helpers are the same first-order scans. These theorems
show that their actual successful computations replay at the same scope;
search is not defined by filtering candidates through the checker.
-/

namespace Mettapedia.Logic.LP

noncomputable section

variable {σ : LPSignature}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

private theorem reduce_source_checked (source : Nat → ConnFOCNF σ) (uFuel nextScope : Nat)
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (sound : ∀ agenda trace, solver agenda = some trace → replayFOClauseSource source uFuel nextScope agenda trace = true)
    (literal : ConnFOLit σ) (rest : ConnFOAgenda σ) (path : ConnFOClause σ) :
    ∀ candidates trace, (∀ selected ∈ candidates, selected ∈ path) →
      tryReducePathFO solver uFuel literal rest path candidates = some trace →
        replayFOClauseSource source uFuel nextScope (⟨literal, path⟩ :: rest) trace = true := by
  intro candidates
  induction candidates with
  | nil => intro trace _ computed; simp [tryReducePathFO] at computed
  | cons selected others earlier =>
      intro trace within computed
      cases unified : unifyComplementLit? uFuel literal selected with
      | none =>
          exact earlier trace (fun chosen member => within chosen (List.mem_cons_of_mem _ member))
            (by simpa only [tryReducePathFO, unified] using computed)
      | some substitution =>
          cases solved : solver (substitution.applyConnFOAgenda rest) with
          | none =>
              exact earlier trace (fun chosen member => within chosen (List.mem_cons_of_mem _ member))
                (by simpa only [tryReducePathFO, unified, solved] using computed)
          | some tail =>
              have same : .step_reduce selected :: tail = trace := by
                simpa only [tryReducePathFO, unified, solved, Option.some.injEq] using computed
              subst trace
              simp only [replayFOClauseSource, if_pos (within selected (by simp)), unified]
              exact sound _ tail solved

private theorem extend_clause_source_checked (source : Nat → ConnFOCNF σ) (uFuel nextScope : Nat)
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (sound : ∀ agenda trace, solver agenda = some trace → replayFOClauseSource source uFuel (nextScope + 1) agenda trace = true)
    (literal : ConnFOLit σ) (rest : ConnFOAgenda σ) (path clause : ConnFOClause σ)
    (installed : clause ∈ source nextScope) :
    ∀ candidates trace, (∀ selected ∈ candidates, selected ∈ clause) →
      tryExtendClauseFO solver uFuel literal rest path clause candidates = some trace →
        replayFOClauseSource source uFuel nextScope (⟨literal, path⟩ :: rest) trace = true := by
  intro candidates
  induction candidates with
  | nil => intro trace _ computed; simp [tryExtendClauseFO] at computed
  | cons selected others earlier =>
      intro trace within computed
      cases unified : unifyComplementLit? uFuel literal selected with
      | none =>
          exact earlier trace (fun chosen member => within chosen (List.mem_cons_of_mem _ member))
            (by simpa only [tryExtendClauseFO, unified] using computed)
      | some substitution =>
          cases solved : solver (substitution.applyConnFOAgenda
            (connectionGoals (clause.erase selected) (literal :: path) ++ rest)) with
          | none =>
              exact earlier trace (fun chosen member => within chosen (List.mem_cons_of_mem _ member))
                (by simpa only [tryExtendClauseFO, unified, solved] using computed)
          | some tail =>
              have same : .step_extend clause selected :: tail = trace := by
                simpa only [tryExtendClauseFO, unified, solved, Option.some.injEq] using computed
              subst trace
              have belongs : clause ∈ source nextScope ∧ selected ∈ clause := ⟨installed, within selected (by simp)⟩
              simp only [replayFOClauseSource, if_pos belongs, unified]
              exact sound _ tail solved

private theorem extend_source_checked (source : Nat → ConnFOCNF σ) (uFuel nextScope : Nat)
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (sound : ∀ agenda trace, solver agenda = some trace → replayFOClauseSource source uFuel (nextScope + 1) agenda trace = true)
    (literal : ConnFOLit σ) (rest : ConnFOAgenda σ) (path : ConnFOClause σ) :
    ∀ candidates trace, (∀ clause ∈ candidates, clause ∈ source nextScope) →
      tryExtendFO solver uFuel literal rest path candidates = some trace →
        replayFOClauseSource source uFuel nextScope (⟨literal, path⟩ :: rest) trace = true := by
  intro candidates
  induction candidates with
  | nil => intro trace _ computed; simp [tryExtendFO] at computed
  | cons clause others earlier =>
      intro trace within computed
      cases selected : tryExtendClauseFO solver uFuel literal rest path clause clause with
      | none =>
          exact earlier trace (fun chosen member => within chosen (List.mem_cons_of_mem _ member))
            (by simpa only [tryExtendFO, selected] using computed)
      | some result =>
          have same : result = trace := by simpa only [tryExtendFO, selected, Option.some.injEq] using computed
          subst trace
          exact extend_clause_source_checked source uFuel nextScope solver sound literal rest path clause
            (within clause (by simp)) clause result (fun _ member => member) selected

theorem connProveFOClauseSourceDFS_checked (source : Nat → ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel nextScope agenda trace,
      connProveFOClauseSourceDFS source uFuel nextScope agenda fuel = some trace →
        replayFOClauseSource source uFuel nextScope agenda trace = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro nextScope agenda trace computed
      by_cases empty : agenda = []
      · subst agenda
        have same : trace = [] := by simpa [connProveFOClauseSourceDFS] using computed.symm
        subst trace
        rfl
      · simp [connProveFOClauseSourceDFS, empty] at computed
  | succ fuel earlier =>
      intro nextScope agenda trace computed
      cases agenda with
      | nil =>
          have same : trace = [] := by simpa [connProveFOClauseSourceDFS] using computed.symm
          subst trace
          rfl
      | cons goal rest =>
          rcases goal with ⟨literal, path⟩
          let reduceSolver := fun agenda => connProveFOClauseSourceDFS source uFuel nextScope agenda fuel
          cases reduced : tryReducePathFO reduceSolver uFuel literal rest path path with
          | some result =>
              dsimp only [reduceSolver] at reduced
              have same : result = trace := by
                simpa only [connProveFOClauseSourceDFS, reduced, Option.some.injEq] using computed
              subst trace
              exact reduce_source_checked source uFuel nextScope reduceSolver
                (earlier nextScope) literal rest path path result (fun _ member => member) reduced
          | none =>
              dsimp only [reduceSolver] at reduced
              let extendSolver := fun agenda => connProveFOClauseSourceDFS source uFuel (nextScope + 1) agenda fuel
              have extended : tryExtendFO extendSolver uFuel literal rest path (source nextScope) = some trace := by
                simpa only [connProveFOClauseSourceDFS, reduced] using computed
              exact extend_source_checked source uFuel nextScope extendSolver
                (earlier (nextScope + 1)) literal rest path (source nextScope) trace
                (fun _ member => member) extended

theorem connProveScopedFODFS_checked (clauses : ConnFOCNF σ) (uFuel fuel : Nat)
    (root : ConnFOClause σ) (proof : FOProofObj σ.scoped)
    (computed : connProveScopedFODFS clauses uFuel fuel root = some proof) :
    checkProofScopedFO clauses uFuel proof = true := by
  unfold connProveScopedFODFS at computed
  split at computed
  · rename_i member
    obtain ⟨trace, traced, same⟩ := Option.map_eq_some_iff.mp computed
    subst proof
    have checked := connProveFOClauseSourceDFS_checked (connFOMatrixAtScope clauses) uFuel fuel 1 _ trace traced
    have rootMember : connFOClauseAtScope 0 root ∈ connFOMatrixAtScope clauses 0 :=
      List.mem_map.mpr ⟨root, member, rfl⟩
    simpa only [checkProofScopedFO, rootMember, decide_true, Bool.true_and] using checked
  · cases computed

/-- A finite accepted scoped trace is eventually found by the actual DFS.
This is witness completeness, not an assumption that every unsatisfiable
first-order matrix has already supplied such a trace. -/
theorem connProveFOClauseSourceDFS_complete_of_checked_trace (source : Nat → ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel nextScope agenda trace, trace.length ≤ fuel →
      replayFOClauseSource source uFuel nextScope agenda trace = true →
        ∃ found, connProveFOClauseSourceDFS source uFuel nextScope agenda fuel = some found := by
  intro fuel
  induction fuel with
  | zero =>
      intro nextScope agenda trace budget checked
      have traceEmpty : trace = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero budget)
      subst trace
      have agendaEmpty : agenda = [] := by simpa [replayFOClauseSource] using checked
      subst agenda
      exact ⟨[], rfl⟩
  | succ fuel earlier =>
      intro nextScope agenda trace budget checked
      cases agenda with
      | nil => exact ⟨[], rfl⟩
      | cons goal rest =>
          rcases goal with ⟨literal, path⟩
          cases trace with
          | nil => simp [replayFOClauseSource] at checked
          | cons step steps =>
              have smaller : steps.length ≤ fuel := Nat.le_of_succ_le_succ budget
              cases step with
              | step_reduce selected =>
                  by_cases member : selected ∈ path
                  · simp only [replayFOClauseSource, if_pos member] at checked
                    cases unified : unifyComplementLit? uFuel literal selected with
                    | none => simp only [unified, Bool.false_eq_true] at checked
                    | some substitution =>
                        have tailChecked : replayFOClauseSource source uFuel nextScope
                            (substitution.applyConnFOAgenda rest) steps = true := by
                          simpa only [unified] using checked
                        obtain ⟨found, reduced⟩ := tryReducePathFO_exists_of_member
                          (fun agenda => connProveFOClauseSourceDFS source uFuel nextScope agenda fuel)
                          (uFuel := uFuel) (g := literal) (gr := rest) (path := path) (pathIter := path)
                          (pl := selected) (θ := substitution)
                          member unified (earlier nextScope _ steps smaller tailChecked)
                        exact ⟨found, by simp only [connProveFOClauseSourceDFS, reduced]⟩
                  · simp only [replayFOClauseSource, if_neg member, Bool.false_eq_true] at checked
              | step_extend clause selected =>
                  by_cases member : clause ∈ source nextScope ∧ selected ∈ clause
                  · simp only [replayFOClauseSource, if_pos member] at checked
                    cases unified : unifyComplementLit? uFuel literal selected with
                    | none => simp only [unified, Bool.false_eq_true] at checked
                    | some substitution =>
                        have tailChecked : replayFOClauseSource source uFuel (nextScope + 1)
                            (substitution.applyConnFOAgenda
                              (connectionGoals (clause.erase selected) (literal :: path) ++ rest)) steps = true := by
                          simpa only [unified] using checked
                        obtain ⟨found, extended⟩ := tryExtendFO_exists_of_clause_member
                          (fun agenda => connProveFOClauseSourceDFS source uFuel (nextScope + 1) agenda fuel)
                          (uFuel := uFuel) (g := literal) (gr := rest) (path := path)
                          (cands := source nextScope) (clause := clause) (clit := selected) (θ := substitution)
                          member.1 member.2 unified (earlier (nextScope + 1) _ steps smaller tailChecked)
                        cases reduced : tryReducePathFO
                          (fun agenda => connProveFOClauseSourceDFS source uFuel nextScope agenda fuel)
                          uFuel literal rest path path with
                        | some result => exact ⟨result, by simp only [connProveFOClauseSourceDFS, reduced]⟩
                        | none => exact ⟨found, by simpa only [connProveFOClauseSourceDFS, reduced] using extended⟩
                  · simp only [replayFOClauseSource, if_neg member, Bool.false_eq_true] at checked

theorem connProveScopedFODFS_unsatisfiable (clauses : ConnFOCNF σ) (uFuel fuel : Nat)
    (root : ConnFOClause σ) (proof : FOProofObj σ.scoped)
    (computed : connProveScopedFODFS clauses uFuel fuel root = some proof)
    (Model : Type*) [Nonempty Model] [(FirstOrderBridge.language σ).Structure Model] :
    ¬ ConnFOModels clauses Model :=
  checkProofScopedFO_unsatisfiable clauses uFuel proof
    (connProveScopedFODFS_checked clauses uFuel fuel root proof computed)

end

end Mettapedia.Logic.LP
