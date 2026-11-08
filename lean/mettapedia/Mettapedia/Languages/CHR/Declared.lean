import Mettapedia.Languages.CHR.Operational
import Mettapedia.Languages.CHR.Admission

/-! Admitted programs store only declared constraints. Under a program whose
rule bodies tell only declared constraints, a refined run from declared
constraints keeps every stored constraint, and every constraint a pending
goal tells, declared. Admission (`Admission.diagnose`) establishes the
condition on rule bodies. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

/-- The program declares the constraint name with this arity. -/
def Declared (program : Program) (name : String) (arity : Nat) : Prop :=
  ∃ declaration ∈ program.declarations, declaration.name = name ∧ declaration.arity = arity

/-- Every constraint the goals tell is declared. -/
def TellsDeclared (program : Program) (goals : List Goal) : Prop :=
  ∀ head, Goal.tell head ∈ goals → Declared program head.name head.arguments.length

/-- Every rule body tells only declared constraints. -/
def BodiesDeclared (program : Program) : Prop :=
  ∀ (index : Nat) (rule : Rule), program.rules[index]? = some rule → TellsDeclared program rule.body

/-- The store holds, and the pending goals tell, only declared constraints. -/
structure StateDeclared (program : Program) (state : State) : Prop where
  store : ∀ occurrence ∈ state.store,
    Declared program occurrence.constraint.name occurrence.constraint.arguments.length
  tasks : ∀ (environment : Environment) (goals : List Goal), Task.goals environment goals ∈ state.tasks →
    TellsDeclared program goals

theorem declared_of_admission {program : Program} {head : Head}
    (known : Admission.declared program head = true) : Declared program head.name head.arguments.length := by
  simp only [Admission.declared, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at known
  exact known

/-! ## Admission -/

theorem goals_declared (program : Program) (ruleIndex : Nat) :
    ∀ (bound : List Nat) (goals : List Goal), Admission.goalsDiagnostic program ruleIndex bound goals = none →
      TellsDeclared program goals
  | _, [], _ => fun _ member => by simp at member
  | bound, .tell told :: rest, clean => by
    have known : Admission.declared program told = true := by
      cases decided : Admission.declared program told
      · simp [Admission.goalsDiagnostic, decided] at clean
      · rfl
    have restClean : Admission.goalsDiagnostic program ruleIndex bound rest = none := by
      by_cases readable : Admission.available bound told.variables = true
      · simpa [Admission.goalsDiagnostic, known, readable] using clean
      · simp [Admission.goalsDiagnostic, known, readable] at clean
    intro head member
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact declared_of_admission known
    · exact goals_declared program ruleIndex bound rest restClean head later
  | bound, .assign index expression :: rest, clean => by
    have restClean : Admission.goalsDiagnostic program ruleIndex (index :: bound) rest = none := by
      by_cases readable : Admission.available bound expression.variables = true
      · simpa [Admission.goalsDiagnostic, readable] using clean
      · simp [Admission.goalsDiagnostic, readable] at clean
    intro head member
    rcases List.mem_cons.mp member with same | later
    · cases same
    · exact goals_declared program ruleIndex (index :: bound) rest restClean head later
  | bound, .fail :: rest, clean => by
    have restClean : Admission.goalsDiagnostic program ruleIndex bound rest = none := by
      simpa [Admission.goalsDiagnostic] using clean
    intro head member
    rcases List.mem_cons.mp member with same | later
    · cases same
    · exact goals_declared program ruleIndex bound rest restClean head later

/-- **Admitted programs tell only declared constraints.** -/
theorem bodies_admitted (program : Program) (admitted : Admission.diagnose program = none) :
    BodiesDeclared program := by
  intro index rule atRule
  unfold Admission.diagnose at admitted
  split at admitted
  · cases admitted
  · rw [List.findSome?_eq_none_iff] at admitted
    have ruled := admitted (rule, index) (List.mk_mem_zipIdx_iff_getElem?.mpr atRule)
    simp only [Admission.ruleDiagnostic] at ruled
    split at ruled
    · cases ruled
    · split at ruled
      · cases ruled
      · split at ruled
        · cases ruled
        · exact goals_declared program index rule.variables rule.body ruled

/-! ## Runs keep the store declared -/

theorem mapM_some_length {α β : Type} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = some outputs → outputs.length = inputs.length
  | [], outputs, mapped => by simp at mapped; simp [← mapped]
  | first :: rest, outputs, mapped => by
    rw [List.mapM_cons] at mapped
    cases head : f first with
    | none => simp [head] at mapped
    | some value =>
      cases tail : rest.mapM f with
      | none => simp [head, tail] at mapped
      | some values =>
        simp only [head, tail, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at mapped
        subst mapped
        simp [mapM_some_length f rest values tail]

theorem instantiate_shape {environment : Environment} {head : Head} {constraint : Constraint}
    (grounded : head.instantiate environment = some constraint) :
    constraint.name = head.name ∧ constraint.arguments.length = head.arguments.length := by
  obtain ⟨name, arguments⟩ := constraint
  unfold Head.instantiate at grounded
  cases mapped : head.arguments.mapM (Term.instantiate environment) with
  | none => simp [mapped] at grounded
  | some values =>
    simp [mapped] at grounded
    obtain ⟨rfl, rfl⟩ := grounded
    exact ⟨rfl, mapM_some_length (Term.instantiate environment) head.arguments values mapped⟩

theorem step_declared {program : Program} (bodies : BodiesDeclared program) {first second : State}
    (step : Step program first second) (declared : StateDeclared program first) :
    StateDeclared program second := by
  have later : ∀ {task : Task} {tail : List Task}, first.tasks = task :: tail →
      ∀ (environment : Environment) (goals : List Goal), Task.goals environment goals ∈ tail →
        TellsDeclared program goals :=
    fun tasks environment goals member =>
      declared.tasks environment goals (by rw [tasks]; exact List.mem_cons_of_mem _ member)
  cases step with
  | endGoals environment tail tasks running => exact ⟨declared.store, later tasks⟩
  | introduce environment head goals tail constraint tasks running grounded =>
    obtain ⟨named, lengths⟩ := instantiate_shape grounded
    have told := declared.tasks environment (.tell head :: goals) (by rw [tasks]; exact List.mem_cons_self)
    refine ⟨fun occurrence member => ?_, fun environment' goals' member => ?_⟩
    · have member' : occurrence ∈ first.store ++ [⟨first.nextId, constraint⟩] := member
      rcases List.mem_append.mp member' with old | new
      · exact declared.store occurrence old
      · rw [List.mem_singleton] at new
        subst new
        show Declared program constraint.name constraint.arguments.length
        rw [named, lengths]
        exact told head List.mem_cons_self
    · have member' : Task.goals environment' goals' ∈
          Task.scan first.nextId 0 :: Task.goals environment goals :: tail := member
      rcases List.mem_cons.mp member' with scanned | rest
      · cases scanned
      · rcases List.mem_cons.mp rest with same | others
        · cases same
          exact fun told' inside => told told' (List.mem_cons_of_mem _ inside)
        · exact later tasks environment' goals' others
  | tellFault environment head goals tail tasks running ungrounded => exact ⟨declared.store, declared.tasks⟩
  | assign environment index expression goals tail result tasks running evaluated compatible =>
    have told := declared.tasks environment (.assign index expression :: goals)
      (by rw [tasks]; exact List.mem_cons_self)
    refine ⟨declared.store, fun environment' goals' member => ?_⟩
    have member' : Task.goals environment' goals' ∈
        Task.goals ((index, .integer result) :: environment) goals :: tail := member
    rcases List.mem_cons.mp member' with same | others
    · cases same
      exact fun told' inside => told told' (List.mem_cons_of_mem _ inside)
    · exact later tasks environment' goals' others
  | assignFailed environment index expression goals tail result old tasks running evaluated bound different =>
    exact ⟨declared.store, declared.tasks⟩
  | assignFault environment index expression goals tail reason tasks running evaluated =>
    exact ⟨declared.store, declared.tasks⟩
  | fail environment goals tail tasks running => exact ⟨declared.store, declared.tasks⟩
  | missingActive active cursor tail tasks running missing => exact ⟨declared.store, later tasks⟩
  | endScan active cursor tail tasks running finished => exact ⟨declared.store, later tasks⟩
  | skip active cursor tail occurrence rule tasks running atCursor atRule unusable =>
    refine ⟨declared.store, fun environment goals member => ?_⟩
    have member' : Task.goals environment goals ∈ Task.scan active (cursor + 1) :: tail := member
    rcases List.mem_cons.mp member' with same | others
    · cases same
    · exact later tasks environment goals others
  | fire active cursor tail occurrence rule environment selection tasks running atCursor atRule matched activeHead
      fresh guarded =>
    refine ⟨fun stored member => ?_, fun environment' goals member => ?_⟩
    · have member' : stored ∈ selection.kept ++ selection.rest := member
      apply declared.store
      apply matched.1.symm.subset
      rcases List.mem_append.mp member' with kept | rest
      · exact List.mem_append_left _ (List.mem_append_left _ kept)
      · exact List.mem_append_right _ rest
    · have member' : Task.goals environment' goals ∈ Task.goals environment rule.body ::
          (if selection.removed.any (fun occurrence => occurrence.id == active) then tail
            else Task.scan active cursor :: tail) := member
      rcases List.mem_cons.mp member' with same | others
      · cases same
        exact bodies occurrence.rule rule atRule
      · split at others
        · exact later tasks environment' goals others
        · rcases List.mem_cons.mp others with scanned | rest
          · cases scanned
          · exact later tasks environment' goals rest
  | guardFault active cursor tail occurrence rule environment selection reason tasks running atCursor atRule
      matched activeHead fresh fault =>
    exact ⟨declared.store, declared.tasks⟩

theorem initial_declared (program : Program) (constraints : List Constraint)
    (seeds : ∀ constraint ∈ constraints, Declared program constraint.name constraint.arguments.length) :
    StateDeclared program (initial constraints) := by
  refine ⟨fun occurrence member => by simp [initial] at member, fun environment goals member => ?_⟩
  have member' : Task.goals environment goals ∈
      [Task.goals [] (constraints.map (Goal.tell ∘ Constraint.asHead))] := member
  rw [List.mem_singleton] at member'
  cases member'
  intro head told
  obtain ⟨constraint, inside, same⟩ := List.mem_map.mp told
  cases same
  simpa [Constraint.asHead] using seeds constraint inside

/-- **Runs keep the store declared.** -/
theorem steps_declared {program : Program} (bodies : BodiesDeclared program) {first second : State}
    (run : Relation.ReflTransGen (Step program) first second) (declared : StateDeclared program first) :
    StateDeclared program second := by
  induction run with
  | refl => exact declared
  | tail _ step ih => exact step_declared bodies step ih

/-- A run of an admitted program from declared constraints stores only
declared constraints. -/
theorem admitted_store_declared (program : Program) (admitted : Admission.diagnose program = none)
    (constraints : List Constraint)
    (seeds : ∀ constraint ∈ constraints, Declared program constraint.name constraint.arguments.length)
    {state : State} (run : Relation.ReflTransGen (Step program) (initial constraints) state) :
    ∀ occurrence ∈ state.store,
      Declared program occurrence.constraint.name occurrence.constraint.arguments.length :=
  (steps_declared (bodies_admitted program admitted) run (initial_declared program constraints seeds)).store

/-! ## Examples -/

/-- A program declaring `gate/0` and `opened/0`, whose rule opens a gate. -/
private def opening : Program :=
  ⟨[⟨"gate", 0⟩, ⟨"opened", 0⟩], [⟨"open", [], [⟨"gate", []⟩], [], [.tell ⟨"opened", []⟩]⟩]⟩

example : Admission.diagnose opening = none := by decide +kernel

example : BodiesDeclared opening := bodies_admitted opening (by decide +kernel)

/-- The same rule without the `opened/0` declaration: admission refuses its
body, and its body does tell an undeclared constraint. -/
private def undeclared : Program :=
  ⟨[⟨"gate", 0⟩], [⟨"open", [], [⟨"gate", []⟩], [], [.tell ⟨"opened", []⟩]⟩]⟩

example : Admission.diagnose undeclared = some (.undeclaredGoal 0 ⟨"opened", []⟩) := by decide +kernel

example : ¬ BodiesDeclared undeclared := by
  intro bodies
  obtain ⟨declaration, member, named, _⟩ := bodies 0 _ rfl ⟨"opened", []⟩ (by simp)
  have single : declaration = ⟨"gate", 0⟩ := by simpa [undeclared] using member
  subst single
  exact absurd named (by decide +kernel)

#print axioms bodies_admitted
#print axioms admitted_store_declared

end Mettapedia.Languages.CHR
