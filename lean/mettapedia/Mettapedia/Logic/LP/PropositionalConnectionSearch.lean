import Mettapedia.Logic.LP.PropositionalConnectionCore

/-!
# Propositional connection search over the checked branch-local agenda

Both first-success and branch-complete search use the same goal frames as
replay. Their soundness and trace-budget completeness concern that actual
state; a completed sibling never becomes an ancestor of the next goal.
-/

namespace Mettapedia.Logic.LP

section PropositionalConnection

variable {α : Type*} [DecidableEq α]

def tryExtendWith (solver : ConnAgenda α → Option (ProofTrace α))
    (clauses : ConnCNF α) (literal : Lit α) (rest : ConnAgenda α) (path : ConnClause α) :
    ConnCNF α → Option (ProofTrace α)
  | [] => none
  | clause :: tail =>
      if literal.complement ∈ clause then
        match solver (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) with
        | some trace => some (.step_extend literal clause :: trace)
        | none => tryExtendWith solver clauses literal rest path tail
      else tryExtendWith solver clauses literal rest path tail

def connProveAgendaDFS (clauses : ConnCNF α) (agenda : ConnAgenda α) : Nat → Option (ProofTrace α)
  | 0 => match agenda with | [] => some [] | _ :: _ => none
  | fuel + 1 =>
      match agenda with
      | [] => some []
      | ⟨literal, path⟩ :: rest =>
          if literal.complement ∈ path then
            match connProveAgendaDFS clauses rest fuel with
            | some trace => some (.step_reduce literal :: trace)
            | none => tryExtendWith (fun agenda => connProveAgendaDFS clauses agenda fuel) clauses literal rest path clauses
          else tryExtendWith (fun agenda => connProveAgendaDFS clauses agenda fuel) clauses literal rest path clauses

def connProveDFS (clauses : ConnCNF α) (goals path : ConnClause α) (fuel : Nat) : Option (ProofTrace α) :=
  connProveAgendaDFS clauses (connectionGoals goals path) fuel

def tryExtendDFS (clauses : ConnCNF α) (literal : Lit α) (rest path : ConnClause α) (fuel : Nat)
    (candidates : ConnCNF α) : Option (ProofTrace α) :=
  tryExtendWith (fun agenda => connProveAgendaDFS clauses agenda fuel) clauses literal (connectionGoals rest path) path candidates

def prependStepToTraces (step : ProofStep α) (traces : List (ProofTrace α)) : List (ProofTrace α) :=
  traces.map (fun trace => step :: trace)

def tryExtendAllWith (solver : ConnAgenda α → List (ProofTrace α))
    (clauses : ConnCNF α) (literal : Lit α) (rest : ConnAgenda α) (path : ConnClause α) :
    ConnCNF α → List (ProofTrace α)
  | [] => []
  | clause :: tail =>
      (if literal.complement ∈ clause then
        prependStepToTraces (.step_extend literal clause)
          (solver (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest))
       else []) ++ tryExtendAllWith solver clauses literal rest path tail

def connProveAgendaAll (clauses : ConnCNF α) (agenda : ConnAgenda α) : Nat → List (ProofTrace α)
  | 0 => match agenda with | [] => [[]] | _ :: _ => []
  | fuel + 1 =>
      match agenda with
      | [] => [[]]
      | ⟨literal, path⟩ :: rest =>
          (if literal.complement ∈ path then
            prependStepToTraces (.step_reduce literal) (connProveAgendaAll clauses rest fuel)
           else []) ++
            tryExtendAllWith (fun agenda => connProveAgendaAll clauses agenda fuel) clauses literal rest path clauses

def connProveAll (clauses : ConnCNF α) (goals path : ConnClause α) (fuel : Nat) : List (ProofTrace α) :=
  connProveAgendaAll clauses (connectionGoals goals path) fuel

theorem tryExtendWith_sound_of_some (solver : ConnAgenda α → Option (ProofTrace α))
    (sound : ∀ agenda trace, solver agenda = some trace → AgendaTraceDerivable clauses agenda trace)
    {literal : Lit α} {rest : ConnAgenda α} {path : ConnClause α} {candidates : ConnCNF α} {trace : ProofTrace α}
    (subset : ∀ clause ∈ candidates, clause ∈ clauses)
    (computed : tryExtendWith solver clauses literal rest path candidates = some trace) :
    AgendaTraceDerivable clauses (⟨literal, path⟩ :: rest) trace := by
  induction candidates generalizing trace with
  | nil => simp [tryExtendWith] at computed
  | cons clause tail earlier =>
      by_cases complementary : literal.complement ∈ clause
      · simp only [tryExtendWith, if_pos complementary] at computed
        cases branch : solver (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) with
        | none =>
            exact earlier (fun other member => subset other (List.mem_cons_of_mem _ member))
              (by simpa only [branch] using computed)
        | some subtrace =>
            have same : .step_extend literal clause :: subtrace = trace := by simpa only [branch, Option.some.injEq] using computed
            subst trace
            exact .extend literal rest path clause subtrace (subset clause List.mem_cons_self) complementary
              (sound _ _ branch)
      · exact earlier (fun other member => subset other (List.mem_cons_of_mem _ member))
          (by simpa only [tryExtendWith, if_neg complementary] using computed)

theorem connProveAgendaDFS_sound_of_some (clauses : ConnCNF α) :
    ∀ fuel agenda trace, connProveAgendaDFS clauses agenda fuel = some trace → AgendaTraceDerivable clauses agenda trace
  | 0, [], trace, computed => by
      have same : [] = trace := by simpa [connProveAgendaDFS] using computed
      subst trace
      exact .done
  | 0, _ :: _, _, computed => by simp [connProveAgendaDFS] at computed
  | _ + 1, [], trace, computed => by
      have same : [] = trace := by simpa [connProveAgendaDFS] using computed
      subst trace
      exact .done
  | fuel + 1, ⟨literal, path⟩ :: rest, trace, computed => by
      have extendSound := tryExtendWith_sound_of_some
        (solver := fun agenda => connProveAgendaDFS clauses agenda fuel)
        (sound := fun agenda trace checked => connProveAgendaDFS_sound_of_some clauses fuel agenda trace checked)
        (literal := literal) (rest := rest) (path := path) (candidates := clauses) (trace := trace)
        (fun _ member => member)
      by_cases complementary : literal.complement ∈ path
      · simp only [connProveAgendaDFS, if_pos complementary] at computed
        cases reduced : connProveAgendaDFS clauses rest fuel with
        | none => exact extendSound (by simpa only [reduced] using computed)
        | some subtrace =>
            have same : .step_reduce literal :: subtrace = trace := by simpa only [reduced, Option.some.injEq] using computed
            subst trace
            exact .reduce literal rest path subtrace complementary
              (connProveAgendaDFS_sound_of_some clauses fuel rest subtrace reduced)
      · exact extendSound (by simpa only [connProveAgendaDFS, if_neg complementary] using computed)

theorem connProveDFS_sound_of_some (clauses : ConnCNF α) (fuel : Nat) (goals path : ConnClause α) (trace : ProofTrace α)
    (computed : connProveDFS clauses goals path fuel = some trace) : TraceDerivable clauses goals path trace :=
  connProveAgendaDFS_sound_of_some clauses fuel _ trace computed

theorem connProveDFS_sound {clauses goals path fuel trace}
    (computed : connProveDFS (α := α) clauses goals path fuel = some trace) : ConnDerivable clauses goals path :=
  (connProveDFS_sound_of_some clauses fuel goals path trace computed).toConnDerivable

theorem tryExtendWith_exists_of_clause (solver : ConnAgenda α → Option (ProofTrace α))
    {literal : Lit α} {rest : ConnAgenda α} {path : ConnClause α} {candidates : ConnCNF α} {clause : ConnClause α}
    (member : clause ∈ candidates) (complementary : literal.complement ∈ clause)
    (branch : ∃ trace, solver (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) = some trace) :
    ∃ trace, tryExtendWith solver clauses literal rest path candidates = some trace := by
  induction candidates with
  | nil => cases member
  | cons head tail earlier =>
      by_cases same : clause = head
      · subst head
        obtain ⟨trace, computed⟩ := branch
        exact ⟨.step_extend literal clause :: trace, by simp [tryExtendWith, complementary, computed]⟩
      · have inTail := (List.mem_cons.mp member).resolve_left same
        by_cases headComplement : literal.complement ∈ head
        · cases headBranch : solver (connectionGoals (head.erase literal.complement) (literal :: path) ++ rest) with
          | some trace => exact ⟨.step_extend literal head :: trace, by simp [tryExtendWith, headComplement, headBranch]⟩
          | none =>
              obtain ⟨trace, computed⟩ := earlier inTail
              exact ⟨trace, by simpa [tryExtendWith, headComplement, headBranch] using computed⟩
        · obtain ⟨trace, computed⟩ := earlier inTail
          exact ⟨trace, by simpa [tryExtendWith, headComplement] using computed⟩

theorem connProveAgendaDFS_complete_of_trace {clauses agenda trace fuel}
    (derived : AgendaTraceDerivable (α := α) clauses agenda trace) (budget : trace.length ≤ fuel) :
    ∃ result, connProveAgendaDFS clauses agenda fuel = some result := by
  induction derived generalizing fuel with
  | done => exact ⟨[], by cases fuel <;> rfl⟩
  | reduce literal rest path steps complementary tail earlier =>
      cases fuel with
      | zero => simp at budget
      | succ fuel =>
          obtain ⟨trace, computed⟩ := earlier (Nat.le_of_succ_le_succ budget)
          exact ⟨.step_reduce literal :: trace, by simp [connProveAgendaDFS, complementary, computed]⟩
  | extend literal rest path clause steps member complementary tail earlier =>
      cases fuel with
      | zero => simp at budget
      | succ fuel =>
          obtain ⟨trace, computed⟩ := earlier (Nat.le_of_succ_le_succ budget)
          have extension := tryExtendWith_exists_of_clause
            (solver := fun agenda => connProveAgendaDFS clauses agenda fuel)
            (clauses := clauses) member complementary ⟨trace, computed⟩
          by_cases onPath : literal.complement ∈ path
          · cases reduced : connProveAgendaDFS clauses rest fuel with
            | some trace => exact ⟨.step_reduce literal :: trace, by simp [connProveAgendaDFS, onPath, reduced]⟩
            | none =>
                obtain ⟨result, run⟩ := extension
                exact ⟨result, by simp [connProveAgendaDFS, onPath, reduced, run]⟩
          · obtain ⟨result, run⟩ := extension
            exact ⟨result, by simp [connProveAgendaDFS, onPath, run]⟩

theorem connProveDFS_complete_of_trace {clauses goals path trace fuel}
    (derived : TraceDerivable (α := α) clauses goals path trace) (budget : trace.length ≤ fuel) :
    ∃ result, connProveDFS clauses goals path fuel = some result :=
  connProveAgendaDFS_complete_of_trace derived budget

theorem connProveDFS_witness_complete {clauses goals path}
    (derived : ConnDerivable (α := α) clauses goals path) : ∃ fuel trace, connProveDFS clauses goals path fuel = some trace := by
  obtain ⟨trace, traced⟩ := derived.exists_trace
  obtain ⟨result, computed⟩ := connProveDFS_complete_of_trace traced (Nat.le_refl trace.length)
  exact ⟨trace.length, result, computed⟩

omit [DecidableEq α] in
theorem mem_prependStepToTraces_of_mem {step : ProofStep α} {trace : ProofTrace α} {traces : List (ProofTrace α)}
    (member : trace ∈ traces) : step :: trace ∈ prependStepToTraces step traces :=
  List.mem_map.mpr ⟨trace, member, rfl⟩

theorem tryExtendWith_some_mem_tryExtendAllWith (solver : ConnAgenda α → Option (ProofTrace α))
    (solverAll : ConnAgenda α → List (ProofTrace α))
    (included : ∀ agenda trace, solver agenda = some trace → trace ∈ solverAll agenda)
    {clauses : ConnCNF α} {literal : Lit α} {rest : ConnAgenda α} {path : ConnClause α}
    {candidates : ConnCNF α} {trace : ProofTrace α}
    (computed : tryExtendWith solver clauses literal rest path candidates = some trace) :
    trace ∈ tryExtendAllWith solverAll clauses literal rest path candidates := by
  induction candidates generalizing trace with
  | nil => simp [tryExtendWith] at computed
  | cons clause tail earlier =>
      by_cases complementary : literal.complement ∈ clause
      · simp only [tryExtendWith, if_pos complementary] at computed
        cases branch : solver (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) with
        | none =>
            have inTail := earlier (by simpa only [branch] using computed)
            exact List.mem_append_right _ inTail
        | some subtrace =>
            have same : .step_extend literal clause :: subtrace = trace := by simpa only [branch, Option.some.injEq] using computed
            subst trace
            apply List.mem_append_left
            simpa only [tryExtendAllWith, if_pos complementary] using
              mem_prependStepToTraces_of_mem (step := .step_extend literal clause) (included _ _ branch)
      · have inTail := earlier (by simpa only [tryExtendWith, if_neg complementary] using computed)
        exact List.mem_append_right _ inTail

theorem connProveAgendaDFS_some_mem_all (clauses : ConnCNF α) :
    ∀ fuel agenda trace, connProveAgendaDFS clauses agenda fuel = some trace → trace ∈ connProveAgendaAll clauses agenda fuel
  | 0, [], trace, computed => by
      have same : [] = trace := by simpa [connProveAgendaDFS] using computed
      subst trace
      simp [connProveAgendaAll]
  | 0, _ :: _, _, computed => by simp [connProveAgendaDFS] at computed
  | _ + 1, [], trace, computed => by
      have same : [] = trace := by simpa [connProveAgendaDFS] using computed
      subst trace
      simp [connProveAgendaAll]
  | fuel + 1, ⟨literal, path⟩ :: rest, trace, computed => by
      have extension := tryExtendWith_some_mem_tryExtendAllWith
        (solver := fun agenda => connProveAgendaDFS clauses agenda fuel)
        (solverAll := fun agenda => connProveAgendaAll clauses agenda fuel)
        (included := fun agenda trace checked => connProveAgendaDFS_some_mem_all clauses fuel agenda trace checked)
        (clauses := clauses) (literal := literal) (rest := rest) (path := path) (candidates := clauses) (trace := trace)
      by_cases complementary : literal.complement ∈ path
      · simp only [connProveAgendaDFS, if_pos complementary] at computed
        cases reduced : connProveAgendaDFS clauses rest fuel with
        | none =>
            have member := extension (by simpa only [reduced] using computed)
            exact List.mem_append_right _ member
        | some subtrace =>
            have same : .step_reduce literal :: subtrace = trace := by simpa only [reduced, Option.some.injEq] using computed
            subst trace
            apply List.mem_append_left
            simpa only [if_pos complementary] using mem_prependStepToTraces_of_mem
              (step := .step_reduce literal) (connProveAgendaDFS_some_mem_all clauses fuel rest subtrace reduced)
      · have member := extension (by simpa only [connProveAgendaDFS, if_neg complementary] using computed)
        exact List.mem_append_right _ member

theorem connProveDFS_some_mem_connProveAll (clauses : ConnCNF α) (fuel : Nat) (goals path : ConnClause α)
    (trace : ProofTrace α) (computed : connProveDFS clauses goals path fuel = some trace) :
    trace ∈ connProveAll clauses goals path fuel := connProveAgendaDFS_some_mem_all clauses fuel _ trace computed

theorem tryExtendAllWith_sound_of_mem (solver : ConnAgenda α → List (ProofTrace α))
    (sound : ∀ agenda trace, trace ∈ solver agenda → AgendaTraceDerivable clauses agenda trace)
    {literal : Lit α} {rest : ConnAgenda α} {path : ConnClause α} {candidates : ConnCNF α} {trace : ProofTrace α}
    (subset : ∀ clause ∈ candidates, clause ∈ clauses)
    (member : trace ∈ tryExtendAllWith solver clauses literal rest path candidates) :
    AgendaTraceDerivable clauses (⟨literal, path⟩ :: rest) trace := by
  induction candidates generalizing trace with
  | nil => cases member
  | cons clause tail earlier =>
      simp only [tryExtendAllWith, List.mem_append] at member
      rcases member with here | later
      · by_cases complementary : literal.complement ∈ clause
        · rw [if_pos complementary] at here
          obtain ⟨subtrace, subMember, rfl⟩ := List.mem_map.mp here
          exact .extend literal rest path clause subtrace (subset clause List.mem_cons_self) complementary
            (sound _ _ subMember)
        · simp only [if_neg complementary, List.not_mem_nil] at here
      · exact earlier (fun other selected => subset other (List.mem_cons_of_mem _ selected)) later

theorem connProveAgendaAll_sound_of_mem (clauses : ConnCNF α) :
    ∀ fuel agenda trace, trace ∈ connProveAgendaAll clauses agenda fuel → AgendaTraceDerivable clauses agenda trace
  | 0, [], trace, member => by
      have same : trace = [] := List.mem_singleton.mp member
      subst trace
      exact .done
  | 0, _ :: _, _, member => by cases member
  | _ + 1, [], trace, member => by
      have same : trace = [] := List.mem_singleton.mp member
      subst trace
      exact .done
  | fuel + 1, ⟨literal, path⟩ :: rest, trace, member => by
      rcases List.mem_append.mp member with reduced | extended
      · by_cases complementary : literal.complement ∈ path
        · rw [if_pos complementary] at reduced
          obtain ⟨subtrace, subMember, rfl⟩ := List.mem_map.mp reduced
          exact .reduce literal rest path subtrace complementary
            (connProveAgendaAll_sound_of_mem clauses fuel rest subtrace subMember)
        · simp only [if_neg complementary, List.not_mem_nil] at reduced
      · exact tryExtendAllWith_sound_of_mem
          (solver := fun agenda => connProveAgendaAll clauses agenda fuel)
          (sound := fun agenda trace selected => connProveAgendaAll_sound_of_mem clauses fuel agenda trace selected)
          (fun _ selected => selected) extended

theorem connProveAll_sound_of_mem {clauses goals path fuel trace}
    (member : trace ∈ connProveAll (α := α) clauses goals path fuel) : TraceDerivable clauses goals path trace :=
  connProveAgendaAll_sound_of_mem clauses fuel _ trace member

end PropositionalConnection

end Mettapedia.Logic.LP
