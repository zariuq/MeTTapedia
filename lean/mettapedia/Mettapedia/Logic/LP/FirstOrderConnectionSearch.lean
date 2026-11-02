import Mettapedia.Logic.LP.FirstOrderConnectionCore

/-!
# First-order connection search on branch-local agendas

The same global substitution maps every pending frame. Search and collection
preserve each sibling's stored path. The correspondence theorems concern
the supplied fixed-variable clause profile; they do not assert fresh clause
instances or first-order model-theoretic soundness.
-/

namespace Mettapedia.Logic.LP

noncomputable section

variable {σ : LPSignature}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
variable [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

/-- Try reduction against a path candidate list (FO). -/
def tryReducePathFO
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr : ConnFOAgenda σ) (path : ConnFOClause σ) :
    ConnFOClause σ → Option (FOProofTrace σ)
  | [] => none
  | pl :: ptail =>
      match unifyComplementLit? (σ := σ) uFuel g pl with
      | some θ =>
          match solver (θ.applyConnFOAgenda gr) with
          | some tr => some (.step_reduce pl :: tr)
          | none => tryReducePathFO solver uFuel g gr path ptail
      | none => tryReducePathFO solver uFuel g gr path ptail

/-- Try extension within one clause by scanning candidate literals. -/
def tryExtendClauseFO
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr : ConnFOAgenda σ) (path : ConnFOClause σ)
    (clause : ConnFOClause σ) :
    ConnFOClause σ → Option (FOProofTrace σ)
  | [] => none
  | clit :: ctail =>
      match unifyComplementLit? (σ := σ) uFuel g clit with
      | some θ =>
          match solver
            (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)) with
          | some tr => some (.step_extend clause clit :: tr)
          | none => tryExtendClauseFO solver uFuel g gr path clause ctail
      | none => tryExtendClauseFO solver uFuel g gr path clause ctail

/-- Try extension over a clause matrix candidate list (FO). -/
def tryExtendFO
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr : ConnFOAgenda σ) (path : ConnFOClause σ) :
    ConnFOCNF σ → Option (FOProofTrace σ)
  | [] => none
  | clause :: tail =>
      match tryExtendClauseFO solver uFuel g gr path clause clause with
      | some tr => some tr
      | none => tryExtendFO solver uFuel g gr path tail

/-- Executable depth-first FO connection prover with fuel. -/
def connProveFOAgendaDFS (clauses : ConnFOCNF σ) (uFuel : Nat)
    (goals : ConnFOAgenda σ) : Nat → Option (FOProofTrace σ)
  | 0 =>
      match goals with
      | [] => some []
      | _ :: _ => none
  | n + 1 =>
      match goals with
      | [] => some []
      | ⟨g, path⟩ :: gr =>
          match tryReducePathFO
            (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
            uFuel g gr path path with
          | some tr => some tr
          | none =>
              tryExtendFO
                (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                uFuel g gr path clauses

/-! ### Branch-complete FO collection (`connProveFOAgendaAll`) and refinement -/

/-- Prefix a FO proof step onto every trace. -/
def prependStepToFOTraces (step : FOProofStep σ) (trs : List (FOProofTrace σ)) :
    List (FOProofTrace σ) :=
  trs.map (fun tr => step :: tr)

/-- Collect all FO reduction traces from a path candidate list. -/
def tryReducePathAllFO
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr : ConnFOAgenda σ) (path : ConnFOClause σ) :
    ConnFOClause σ → List (FOProofTrace σ)
  | [] => []
  | pl :: ptail =>
      let here :=
        match unifyComplementLit? (σ := σ) uFuel g pl with
        | some θ =>
            prependStepToFOTraces (.step_reduce pl)
              (solverAll (θ.applyConnFOAgenda gr))
        | none => []
      here ++ tryReducePathAllFO solverAll uFuel g gr path ptail

/-- Collect all FO extension traces from one clause literal scan. -/
def tryExtendClauseAllFO
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr : ConnFOAgenda σ) (path : ConnFOClause σ)
    (clause : ConnFOClause σ) :
    ConnFOClause σ → List (FOProofTrace σ)
  | [] => []
  | clit :: ctail =>
      let here :=
        match unifyComplementLit? (σ := σ) uFuel g clit with
        | some θ =>
            prependStepToFOTraces (.step_extend clause clit)
              (solverAll
                (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)))
        | none => []
      here ++ tryExtendClauseAllFO solverAll uFuel g gr path clause ctail

/-- Collect all FO extension traces from a clause matrix candidate list. -/
def tryExtendAllFO
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (uFuel : Nat) (g : ConnFOLit σ) (gr : ConnFOAgenda σ) (path : ConnFOClause σ) :
    ConnFOCNF σ → List (FOProofTrace σ)
  | [] => []
  | clause :: tail =>
      tryExtendClauseAllFO solverAll uFuel g gr path clause clause
        ++ tryExtendAllFO solverAll uFuel g gr path tail

/-- Branch-complete FO DFS search returning all traces within fuel. -/
def connProveFOAgendaAll (clauses : ConnFOCNF σ) (uFuel : Nat)
    (goals : ConnFOAgenda σ) : Nat → List (FOProofTrace σ)
  | 0 =>
      match goals with
      | [] => [[]]
      | _ :: _ => []
  | n + 1 =>
      match goals with
      | [] => [[]]
      | ⟨g, path⟩ :: gr =>
          let rTraces :=
            tryReducePathAllFO
              (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
              uFuel g gr path path
          let eTraces :=
            tryExtendAllFO
              (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
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
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (hsolver : ∀ g tr, solver g = some tr → tr ∈ solverAll g)
    {uFuel : Nat} {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path pathIter : ConnFOClause σ}
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
          cases hS : solver (θ.applyConnFOAgenda gr) with
          | some trSub =>
              have hEq : .step_reduce pl :: trSub = tr := by
                simpa [tryReducePathFO, hU, hS] using h
              subst hEq
              have hSubMem : trSub ∈ solverAll (θ.applyConnFOAgenda gr) :=
                hsolver _ _ hS
              have hHere :
                  .step_reduce pl :: trSub ∈
                    prependStepToFOTraces (σ := σ) (.step_reduce pl)
                      (solverAll (θ.applyConnFOAgenda gr)) :=
                mem_prependStepToFOTraces_of_mem (σ := σ) hSubMem
              have hHereIf :
                  .step_reduce pl :: trSub ∈
                    (match unifyComplementLit? (σ := σ) uFuel g pl with
                     | some θ =>
                        prependStepToFOTraces (σ := σ) (.step_reduce pl)
                          (solverAll (θ.applyConnFOAgenda gr))
                     | none => []) := by
                simpa [hU] using hHere
              exact List.mem_append.mpr (Or.inl hHereIf)
          | none =>
              have hTail : tryReducePathFO (σ := σ) solver uFuel g gr path ptail = some tr := by
                simpa [tryReducePathFO, hU, hS] using h
              exact List.mem_append.mpr (Or.inr (ih hTail))

/-- Option-returning clause-extension success appears in all-traces clause collection. -/
theorem tryExtendClauseFO_some_mem_tryExtendClauseAllFO
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (hsolver : ∀ g tr, solver g = some tr → tr ∈ solverAll g)
    {uFuel : Nat} {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path clause clits : ConnFOClause σ}
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
              (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)) with
          | some trSub =>
              have hEq : .step_extend clause clit :: trSub = tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              subst hEq
              have hSubMem :
                  trSub ∈ solverAll
                    (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)) :=
                hsolver _ _ hS
              have hHere :
                  .step_extend clause clit :: trSub ∈
                    prependStepToFOTraces (σ := σ) (.step_extend clause clit)
                      (solverAll
                        (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr))) :=
                mem_prependStepToFOTraces_of_mem (σ := σ) hSubMem
              have hHereIf :
                  .step_extend clause clit :: trSub ∈
                    (match unifyComplementLit? (σ := σ) uFuel g clit with
                     | some θ =>
                        prependStepToFOTraces (σ := σ) (.step_extend clause clit)
                          (solverAll
                            (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)))
                     | none => []) := by
                simpa [hU] using hHere
              exact List.mem_append.mpr (Or.inl hHereIf)
          | none =>
              have hTail : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause ctail = some tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              exact List.mem_append.mpr (Or.inr (ih hTail))

/-- Option-returning matrix-extension success appears in all-traces matrix collection. -/
theorem tryExtendFO_some_mem_tryExtendAllFO
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (hsolver : ∀ g tr, solver g = some tr → tr ∈ solverAll g)
    {uFuel : Nat} {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path : ConnFOClause σ} {cands : ConnFOCNF σ}
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
theorem connProveFOAgendaDFS_some_mem_connProveFOAgendaAll
    (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel goals tr,
      connProveFOAgendaDFS (σ := σ) clauses uFuel goals fuel = some tr →
      tr ∈ connProveFOAgendaAll (σ := σ) clauses uFuel goals fuel
  | 0, goals, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFOAgendaDFS] at h
          subst h
          simp [connProveFOAgendaAll]
      | cons g gr =>
          rcases g with ⟨g, path⟩
          simp [connProveFOAgendaDFS] at h
  | n + 1, goals, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFOAgendaDFS] at h
          subst h
          simp [connProveFOAgendaAll]
      | cons g gr =>
          rcases g with ⟨g, path⟩
          simp [connProveFOAgendaDFS] at h
          cases hRed : tryReducePathFO
              (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
              uFuel g gr path path with
          | some trRed =>
              have hEq : trRed = tr := by simpa [hRed] using h
              subst hEq
              have hMemRed :
                  trRed ∈ tryReducePathAllFO
                    (σ := σ)
                    (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
                    uFuel g gr path path :=
                tryReducePathFO_some_mem_tryReducePathAllFO
                  (σ := σ)
                  (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                  (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
                  (hsolver := by
                    intro g' tr' hs
                    exact connProveFOAgendaDFS_some_mem_connProveFOAgendaAll clauses uFuel n g' tr' hs)
                  (h := hRed)
              exact List.mem_append.mpr (Or.inl hMemRed)
          | none =>
              have hMemExt :
                  tr ∈ tryExtendAllFO
                    (σ := σ)
                    (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
                    uFuel g gr path clauses :=
                tryExtendFO_some_mem_tryExtendAllFO
                  (σ := σ)
                  (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                  (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
                  (hsolver := by
                    intro g' tr' hs
                    exact connProveFOAgendaDFS_some_mem_connProveFOAgendaAll clauses uFuel n g' tr' hs)
                  (h := by simpa [hRed] using h)
              exact List.mem_append.mpr (Or.inr hMemExt)

/-- Operational correctness of branch-complete reduction collection. -/
theorem tryReducePathAllFO_sound_of_mem
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (hsolver : ∀ g tr, tr ∈ solverAll g → AgendaTraceDerivableFO clauses uFuel g tr)
    {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path pathIter : ConnFOClause σ} {tr : FOProofTrace σ}
    (hmemPath : ∀ pl ∈ pathIter, pl ∈ path)
    (h : tr ∈ tryReducePathAllFO (σ := σ) solverAll uFuel g gr path pathIter) :
    AgendaTraceDerivableFO clauses uFuel (⟨g, path⟩ :: gr) tr := by
  induction pathIter generalizing tr with
  | nil =>
      simp [tryReducePathAllFO] at h
  | cons pl ptail ih =>
      have hsplit :
          tr ∈ (match unifyComplementLit? (σ := σ) uFuel g pl with
            | some θ =>
                prependStepToFOTraces (σ := σ) (.step_reduce pl)
                  (solverAll (θ.applyConnFOAgenda gr))
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
                  (solverAll (θ.applyConnFOAgenda gr)) := by
              have hHere' := hHere
              simp [hU] at hHere'
              exact hHere'
            unfold prependStepToFOTraces at hHere'
            rcases List.mem_map.mp hHere' with ⟨trSub, hSub, hEq⟩
            subst hEq
            exact AgendaTraceDerivableFO.reduce g gr path pl trSub θ
              (hmemPath pl (by simp))
              hU
              (hsolver _ _ hSub)
      · exact ih
          (by
            intro p hp
            exact hmemPath p (by simp [hp]))
          hTail

/-- Operational correctness of branch-complete single-clause extension collection. -/
theorem tryExtendClauseAllFO_sound_of_mem
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (hsolver : ∀ g tr, tr ∈ solverAll g → AgendaTraceDerivableFO clauses uFuel g tr)
    {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path clause clits : ConnFOClause σ} {tr : FOProofTrace σ}
    (hClause : clause ∈ clauses)
    (hmemClits : ∀ clit ∈ clits, clit ∈ clause)
    (h : tr ∈ tryExtendClauseAllFO (σ := σ) solverAll uFuel g gr path clause clits) :
    AgendaTraceDerivableFO clauses uFuel (⟨g, path⟩ :: gr) tr := by
  induction clits generalizing tr with
  | nil =>
      simp [tryExtendClauseAllFO] at h
  | cons clit ctail ih =>
      have hsplit :
          tr ∈ (match unifyComplementLit? (σ := σ) uFuel g clit with
            | some θ =>
                prependStepToFOTraces (σ := σ) (.step_extend clause clit)
                  (solverAll
                    (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)))
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
                    (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr))) := by
              have hHere' := hHere
              simp [hU] at hHere'
              exact hHere'
            unfold prependStepToFOTraces at hHere'
            rcases List.mem_map.mp hHere' with ⟨trSub, hSub, hEq⟩
            subst hEq
            exact AgendaTraceDerivableFO.extend g gr path clause clit trSub θ
              hClause
              (hmemClits clit (by simp))
              hU
              (hsolver _ _ hSub)
      · exact ih
          (by
            intro c hc
            exact hmemClits c (by simp [hc]))
          hTail

/-- Operational correctness of branch-complete matrix extension collection. -/
theorem tryExtendAllFO_sound_of_mem
    (solverAll : ConnFOAgenda σ → List (FOProofTrace σ))
    (hsolver : ∀ g tr, tr ∈ solverAll g → AgendaTraceDerivableFO clauses uFuel g tr)
    {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path : ConnFOClause σ} {cands : ConnFOCNF σ}
    {tr : FOProofTrace σ}
    (hsubset : ∀ c ∈ cands, c ∈ clauses)
    (h : tr ∈ tryExtendAllFO (σ := σ) solverAll uFuel g gr path cands) :
    AgendaTraceDerivableFO clauses uFuel (⟨g, path⟩ :: gr) tr := by
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

/-- Operational correctness of branch-complete FO search by membership. -/
theorem connProveFOAgendaAll_sound_of_mem
    (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel goals tr,
      tr ∈ connProveFOAgendaAll (σ := σ) clauses uFuel goals fuel →
      AgendaTraceDerivableFO clauses uFuel goals tr
  | 0, goals, tr, h => by
      cases goals with
      | nil =>
          have hEq : tr = [] := by simpa [connProveFOAgendaAll] using h
          subst hEq
          exact AgendaTraceDerivableFO.done
      | cons g gr =>
          rcases g with ⟨g, path⟩
          simp [connProveFOAgendaAll] at h
  | n + 1, goals, tr, h => by
      cases goals with
      | nil =>
          have hEq : tr = [] := by simpa [connProveFOAgendaAll] using h
          subst hEq
          exact AgendaTraceDerivableFO.done
      | cons g gr =>
          rcases g with ⟨g, path⟩
          have hsplit :
              tr ∈ tryReducePathAllFO
                (σ := σ)
                (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
                uFuel g gr path path
                ∨
              tr ∈ tryExtendAllFO
                (σ := σ)
                (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
                uFuel g gr path clauses := by
            simpa [connProveFOAgendaAll] using (List.mem_append.mp h)
          rcases hsplit with hRed | hExt
          · exact tryReducePathAllFO_sound_of_mem
              (σ := σ) (clauses := clauses) (uFuel := uFuel)
              (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
              (hsolver := by
                intro g' tr' hs
                exact connProveFOAgendaAll_sound_of_mem clauses uFuel n g' tr' hs)
              (g := g) (gr := gr) (path := path) (pathIter := path)
              (tr := tr)
              (hmemPath := by intro pl hpl; exact hpl)
              hRed
          · exact tryExtendAllFO_sound_of_mem
              (σ := σ) (clauses := clauses) (uFuel := uFuel)
              (solverAll := fun g' => connProveFOAgendaAll clauses uFuel g' n)
              (hsolver := by
                intro g' tr' hs
                exact connProveFOAgendaAll_sound_of_mem clauses uFuel n g' tr' hs)
              (g := g) (gr := gr) (path := path) (cands := clauses) (tr := tr)
              (hsubset := by intro c hc; exact hc)
              hExt

/-- Erased statement: any trace in `connProveFOAgendaAll` is semantically derivable. -/
theorem connProveFOAgendaAll_sound
    {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {goals : ConnFOAgenda σ} {tr : FOProofTrace σ}
    (h : tr ∈ connProveFOAgendaAll (σ := σ) clauses uFuel goals fuel) :
    AgendaTraceDerivableFO clauses uFuel goals tr :=
  connProveFOAgendaAll_sound_of_mem (σ := σ) clauses uFuel fuel goals tr h

/-- Soundness of `tryReducePathFO` under a sound recursive solver. -/
theorem tryReducePathFO_sound_of_some
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (hsolver :
      ∀ g tr, solver g = some tr → AgendaTraceDerivableFO clauses uFuel g tr)
    {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path pathIter : ConnFOClause σ} {tr : FOProofTrace σ}
    (hmem : ∀ pl ∈ pathIter, pl ∈ path)
    (h : tryReducePathFO (σ := σ) solver uFuel g gr path pathIter = some tr) :
    AgendaTraceDerivableFO clauses uFuel (⟨g, path⟩ :: gr) tr := by
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
          cases hS : solver (θ.applyConnFOAgenda gr) with
          | some trSub =>
              have hEq : some (.step_reduce pl :: trSub) = some tr := by
                simpa [tryReducePathFO, hU, hS] using h
              have hEqTrace : .step_reduce pl :: trSub = tr := Option.some.inj hEq
              cases hEqTrace
              exact AgendaTraceDerivableFO.reduce g gr path pl trSub θ
                (hmem pl (by simp))
                hU
                (hsolver _ _ hS)
          | none =>
              have hTail : tryReducePathFO (σ := σ) solver uFuel g gr path ptail = some tr := by
                simpa [tryReducePathFO, hU, hS] using h
              exact ih
                (by intro p hp; exact hmem p (by simp [hp]))
                hTail

/-- Soundness of `tryExtendClauseFO` under a sound recursive solver. -/
theorem tryExtendClauseFO_sound_of_some
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (hsolver :
      ∀ g tr, solver g = some tr → AgendaTraceDerivableFO clauses uFuel g tr)
    {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path clause clits : ConnFOClause σ} {tr : FOProofTrace σ}
    (hClause : clause ∈ clauses)
    (hmem : ∀ clit ∈ clits, clit ∈ clause)
    (h : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause clits = some tr) :
    AgendaTraceDerivableFO clauses uFuel (⟨g, path⟩ :: gr) tr := by
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
          cases hS : solver (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)) with
          | some trSub =>
              have hEq : some (.step_extend clause clit :: trSub) = some tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              have hEqTrace : .step_extend clause clit :: trSub = tr := Option.some.inj hEq
              cases hEqTrace
              exact AgendaTraceDerivableFO.extend g gr path clause clit trSub θ
                hClause
                (hmem clit (by simp))
                hU
                (hsolver _ _ hS)
          | none =>
              have hTail : tryExtendClauseFO (σ := σ) solver uFuel g gr path clause ctail = some tr := by
                simpa [tryExtendClauseFO, hU, hS] using h
              exact ih
                (by intro c hc; exact hmem c (by simp [hc]))
                hTail

/-- Soundness of `tryExtendFO` under a sound recursive solver. -/
theorem tryExtendFO_sound_of_some
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    (hsolver :
      ∀ g tr, solver g = some tr → AgendaTraceDerivableFO clauses uFuel g tr)
    {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path : ConnFOClause σ} {cands : ConnFOCNF σ} {tr : FOProofTrace σ}
    (hsubset : ∀ c ∈ cands, c ∈ clauses)
    (h : tryExtendFO (σ := σ) solver uFuel g gr path cands = some tr) :
    AgendaTraceDerivableFO clauses uFuel (⟨g, path⟩ :: gr) tr := by
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
theorem connProveFOAgendaDFS_sound_of_some
    (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ fuel goals tr,
      connProveFOAgendaDFS (σ := σ) clauses uFuel goals fuel = some tr →
      AgendaTraceDerivableFO clauses uFuel goals tr
  | 0, goals, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFOAgendaDFS] at h
          subst h
          exact AgendaTraceDerivableFO.done
      | cons g gr =>
          rcases g with ⟨g, path⟩
          simp [connProveFOAgendaDFS] at h
  | n + 1, goals, tr, h => by
      cases goals with
      | nil =>
          simp [connProveFOAgendaDFS] at h
          subst h
          exact AgendaTraceDerivableFO.done
      | cons g gr =>
          rcases g with ⟨g, path⟩
          simp [connProveFOAgendaDFS] at h
          cases hRed : tryReducePathFO
            (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
            uFuel g gr path path with
          | some trRed =>
              have hEq : trRed = tr := by simpa [hRed] using h
              subst hEq
              exact tryReducePathFO_sound_of_some
                (σ := σ) (clauses := clauses) (uFuel := uFuel)
                (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                (hsolver := by
                  intro g' tr' hs
                  exact connProveFOAgendaDFS_sound_of_some clauses uFuel n g' tr' hs)
                (g := g) (gr := gr) (path := path) (pathIter := path)
                (tr := trRed)
                (hmem := by intro pl hpl; exact hpl)
                (by simp [hRed])
          | none =>
              exact tryExtendFO_sound_of_some
                (σ := σ) (clauses := clauses) (uFuel := uFuel)
                (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                (hsolver := by
                  intro g' tr' hs
                  exact connProveFOAgendaDFS_sound_of_some clauses uFuel n g' tr' hs)
                (g := g) (gr := gr) (path := path)
                (cands := clauses) (tr := tr)
                (hsubset := by intro c hc; exact hc)
                (by simpa [hRed] using h)

/-- Executable FO DFS soundness (erased statement). -/
theorem connProveFOAgendaDFS_sound
    {clauses : ConnFOCNF σ} {uFuel fuel}
    {goals : ConnFOAgenda σ} {tr : FOProofTrace σ}
    (h : connProveFOAgendaDFS (σ := σ) clauses uFuel goals fuel = some tr) :
    AgendaTraceDerivableFO clauses uFuel goals tr :=
  connProveFOAgendaDFS_sound_of_some (σ := σ) clauses uFuel fuel goals tr h

/--
Combined refinement endpoint for FO DFS:
returned traces are operationally derivable and included in branch-complete collection.
-/
theorem connProveFOAgendaDFS_some_refines_connProveFOAgendaAll
    {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {goals : ConnFOAgenda σ} {tr : FOProofTrace σ}
    (h : connProveFOAgendaDFS (σ := σ) clauses uFuel goals fuel = some tr) :
    tr ∈ connProveFOAgendaAll (σ := σ) clauses uFuel goals fuel
      ∧ AgendaTraceDerivableFO clauses uFuel goals tr := by
  exact ⟨
    connProveFOAgendaDFS_some_mem_connProveFOAgendaAll (σ := σ) clauses uFuel fuel goals tr h,
    connProveFOAgendaDFS_sound (σ := σ) h
  ⟩

/-- Completeness helper for path-reduction search. -/
theorem tryReducePathFO_exists_of_member
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    {uFuel : Nat} {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path pathIter : ConnFOClause σ}
    {pl : ConnFOLit σ} {θ : Subst σ}
    (hmem : pl ∈ pathIter)
    (hUnify : unifyComplementLit? (σ := σ) uFuel g pl = some θ)
    (hSub : ∃ tr, solver (θ.applyConnFOAgenda gr) = some tr) :
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
            cases hS0 : solver (θ0.applyConnFOAgenda gr) with
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
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    {uFuel : Nat} {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path clause clits : ConnFOClause σ}
    {clit : ConnFOLit σ} {θ : Subst σ}
    (hmem : clit ∈ clits)
    (hUnify : unifyComplementLit? (σ := σ) uFuel g clit = some θ)
    (hSub :
      ∃ tr, solver
        (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)) = some tr) :
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
                (θ0.applyConnFOAgenda (connectionGoals (clause.erase cl0) (g :: path) ++ gr)) with
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
    (solver : ConnFOAgenda σ → Option (FOProofTrace σ))
    {uFuel : Nat} {g : ConnFOLit σ} {gr : ConnFOAgenda σ} {path : ConnFOClause σ}
    {cands : ConnFOCNF σ} {clause : ConnFOClause σ}
    (hClauseMem : clause ∈ cands)
    {clit : ConnFOLit σ} {θ : Subst σ}
    (hLit : clit ∈ clause)
    (hUnify : unifyComplementLit? (σ := σ) uFuel g clit = some θ)
    (hSub :
      ∃ tr, solver
        (θ.applyConnFOAgenda (connectionGoals (clause.erase clit) (g :: path) ++ gr)) = some tr) :
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
theorem connProveFOAgendaDFS_complete_of_trace
    {clauses : ConnFOCNF σ} {uFuel : Nat}
    {goals : ConnFOAgenda σ} {trace : FOProofTrace σ} {fuel : Nat}
    (hDer : AgendaTraceDerivableFO clauses uFuel goals trace)
    (hLen : trace.length ≤ fuel) :
    ∃ tr, connProveFOAgendaDFS (σ := σ) clauses uFuel goals fuel = some tr := by
  induction hDer generalizing fuel with
  | done =>
      refine ⟨[], ?_⟩
      cases fuel <;> simp [connProveFOAgendaDFS]
  | reduce g gr path pl steps θ hMem hUnify hSub ih =>
      cases fuel with
      | zero =>
          simp at hLen
      | succ n =>
          have hLenSub : steps.length ≤ n := Nat.le_of_succ_le_succ (by simpa using hLen)
          rcases ih hLenSub with ⟨trSub, hRunSub⟩
          rcases tryReducePathFO_exists_of_member
              (σ := σ)
              (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
              (uFuel := uFuel) (g := g) (gr := gr) (path := path)
              (pathIter := path) (pl := pl) (θ := θ)
              hMem hUnify
              ⟨trSub, by simpa using hRunSub⟩ with ⟨trRed, hRed⟩
          exact ⟨trRed, by simp [connProveFOAgendaDFS, hRed]⟩
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
                  (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                  uFuel g gr path path = some trRed
          · rcases hRedEx with ⟨trRed, hRed⟩
            exact ⟨trRed, by simp [connProveFOAgendaDFS, hRed]⟩
          · rcases tryExtendFO_exists_of_clause_member
              (σ := σ)
              (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
              (uFuel := uFuel) (g := g) (gr := gr) (path := path)
              (cands := clauses) (clause := clause)
              (hClauseMem := hClause)
              (clit := clit) (θ := θ)
              hLit hUnify
              ⟨trSub, by simpa using hRunSub⟩ with ⟨trExt, hExt⟩
            have hNoRed :
                tryReducePathFO
                  (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                  uFuel g gr path path = none := by
              cases hTry :
                  tryReducePathFO
                    (solver := fun g' => connProveFOAgendaDFS clauses uFuel g' n)
                    uFuel g gr path path with
              | some trTry =>
                  exact (hRedEx ⟨trTry, hTry⟩).elim
              | none =>
                  rfl
            exact ⟨trExt, by simp [connProveFOAgendaDFS, hNoRed, hExt]⟩

/-- Existential FO DFS witness completeness (from trace-level derivability). -/
theorem connProveFOAgendaDFS_witness_complete
    {clauses : ConnFOCNF σ} {uFuel : Nat}
    {goals : ConnFOAgenda σ}
    (h : ∃ trace, AgendaTraceDerivableFO clauses uFuel goals trace) :
    ∃ fuel tr, connProveFOAgendaDFS (σ := σ) clauses uFuel goals fuel = some tr := by
  rcases h with ⟨trace, hTrace⟩
  rcases connProveFOAgendaDFS_complete_of_trace
      (σ := σ) (clauses := clauses) (uFuel := uFuel)
      (goals := goals) (trace := trace) (fuel := trace.length)
      hTrace (Nat.le_refl _) with ⟨tr, hRun⟩
  exact ⟨trace.length, tr, hRun⟩


end

end Mettapedia.Logic.LP
