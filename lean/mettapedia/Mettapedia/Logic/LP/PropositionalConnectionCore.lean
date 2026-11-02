import Mettapedia.Logic.LP.ConnectionAgenda
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.TakeDrop

/-!
# Branch-local propositional connection replay

The proof-object format contains reduction and extension steps. Its replay
uses an agenda with a separate ancestor path for each literal. The Boolean
semantic theorem interprets the clause matrix independently: a satisfying
valuation always leaves a true open branch, so an accepted root proof
refutes every Boolean valuation.
-/

namespace Mettapedia.Logic.LP

section PropositionalConnection

variable {α : Type*} [DecidableEq α]

inductive Lit (α : Type*)
  | pos : α → Lit α
  | neg : α → Lit α
  deriving DecidableEq, Repr

def Lit.complement : Lit α → Lit α
  | .pos atom => .neg atom
  | .neg atom => .pos atom

omit [DecidableEq α] in
@[simp] theorem complement_complement (literal : Lit α) : literal.complement.complement = literal := by
  cases literal <;> rfl

abbrev ConnClause (α : Type*) := List (Lit α)
abbrev ConnCNF (α : Type*) := List (ConnClause α)
abbrev ConnAgenda (α : Type*) := ConnectionAgenda (Lit α)

inductive ProofStep (α : Type*)
  | step_reduce : Lit α → ProofStep α
  | step_extend : Lit α → ConnClause α → ProofStep α
  deriving DecidableEq, Repr

abbrev ProofTrace (α : Type*) := List (ProofStep α)

structure ProofObj (α : Type*) where
  fuel : Nat
  root : ConnClause α
  trace : ProofTrace α
  deriving Repr

def replayAgenda (clauses : ConnCNF α) (agenda : ConnAgenda α) : ProofTrace α → Bool
  | [] => decide (agenda = [])
  | step :: steps =>
      match agenda with
      | [] => false
      | ⟨literal, path⟩ :: rest =>
          match step with
          | .step_reduce selected =>
              if literal = selected ∧ literal.complement ∈ path then replayAgenda clauses rest steps else false
          | .step_extend selected clause =>
              if literal = selected ∧ clause ∈ clauses ∧ literal.complement ∈ clause then
                replayAgenda clauses (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) steps
              else false

def replay (clauses : ConnCNF α) (goals path : ConnClause α) (trace : ProofTrace α) : Bool :=
  replayAgenda clauses (connectionGoals goals path) trace

def checkProof (clauses : ConnCNF α) (p : ProofObj α) : Bool :=
  decide (p.root ∈ clauses) && replay clauses p.root [] p.trace

inductive AgendaTraceDerivable (clauses : ConnCNF α) : ConnAgenda α → ProofTrace α → Prop
  | done : AgendaTraceDerivable clauses [] []
  | reduce (literal : Lit α) (rest : ConnAgenda α) (path : ConnClause α) (steps : ProofTrace α)
      (complementary : literal.complement ∈ path) (tail : AgendaTraceDerivable clauses rest steps) :
      AgendaTraceDerivable clauses (⟨literal, path⟩ :: rest) (.step_reduce literal :: steps)
  | extend (literal : Lit α) (rest : ConnAgenda α) (path clause : ConnClause α) (steps : ProofTrace α)
      (member : clause ∈ clauses) (complementary : literal.complement ∈ clause)
      (tail : AgendaTraceDerivable clauses
        (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) steps) :
      AgendaTraceDerivable clauses (⟨literal, path⟩ :: rest) (.step_extend literal clause :: steps)

inductive AgendaConnDerivable (clauses : ConnCNF α) : ConnAgenda α → Prop
  | done : AgendaConnDerivable clauses []
  | reduce (literal : Lit α) (rest : ConnAgenda α) (path : ConnClause α)
      (complementary : literal.complement ∈ path) (tail : AgendaConnDerivable clauses rest) :
      AgendaConnDerivable clauses (⟨literal, path⟩ :: rest)
  | extend (literal : Lit α) (rest : ConnAgenda α) (path clause : ConnClause α)
      (member : clause ∈ clauses) (complementary : literal.complement ∈ clause)
      (tail : AgendaConnDerivable clauses
        (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest)) :
      AgendaConnDerivable clauses (⟨literal, path⟩ :: rest)

abbrev TraceDerivable (clauses : ConnCNF α) (goals path : ConnClause α) (trace : ProofTrace α) : Prop :=
  AgendaTraceDerivable clauses (connectionGoals goals path) trace

abbrev ConnDerivable (clauses : ConnCNF α) (goals path : ConnClause α) : Prop :=
  AgendaConnDerivable clauses (connectionGoals goals path)

theorem replayAgenda_true_of_derivable {clauses agenda trace}
    (derived : AgendaTraceDerivable (α := α) clauses agenda trace) : replayAgenda clauses agenda trace = true := by
  induction derived with
  | done => rfl
  | reduce literal rest path steps complementary tail checked => simp [replayAgenda, complementary, checked]
  | extend literal rest path clause steps member complementary tail checked =>
      simp [replayAgenda, member, complementary, checked]

theorem agendaDerivable_of_replay_true (clauses : ConnCNF α) :
    ∀ agenda trace, replayAgenda clauses agenda trace = true → AgendaTraceDerivable clauses agenda trace
  | agenda, [], checked => by
      have empty : agenda = [] := by simpa [replayAgenda] using checked
      subst agenda
      exact .done
  | [], _ :: _, checked => by simp [replayAgenda] at checked
  | ⟨literal, path⟩ :: rest, step :: steps, checked => by
      cases step with
      | step_reduce selected =>
          have parts : literal = selected ∧ literal.complement ∈ path ∧ replayAgenda clauses rest steps = true := by
            simpa [replayAgenda, Bool.ite_eq_true_distrib, and_assoc] using checked
          obtain ⟨rfl, complementary, tail⟩ := parts
          exact .reduce literal rest path steps complementary (agendaDerivable_of_replay_true clauses rest steps tail)
      | step_extend selected clause =>
          have parts : literal = selected ∧ clause ∈ clauses ∧ literal.complement ∈ clause ∧
              replayAgenda clauses (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) steps = true := by
            simpa [replayAgenda, Bool.ite_eq_true_distrib, and_assoc] using checked
          obtain ⟨rfl, member, complementary, tail⟩ := parts
          exact .extend literal rest path clause steps member complementary
            (agendaDerivable_of_replay_true clauses _ steps tail)

theorem replayAgenda_true_iff_derivable (clauses : ConnCNF α) (agenda : ConnAgenda α) (trace : ProofTrace α) :
    replayAgenda clauses agenda trace = true ↔ AgendaTraceDerivable clauses agenda trace :=
  ⟨agendaDerivable_of_replay_true clauses agenda trace, replayAgenda_true_of_derivable⟩

theorem AgendaTraceDerivable.toConnDerivable {clauses agenda trace}
    (derived : AgendaTraceDerivable (α := α) clauses agenda trace) : AgendaConnDerivable clauses agenda := by
  induction derived with
  | done => exact .done
  | reduce literal rest path steps complementary tail ih => exact .reduce literal rest path complementary ih
  | extend literal rest path clause steps member complementary tail ih =>
      exact .extend literal rest path clause member complementary ih

theorem AgendaConnDerivable.exists_trace {clauses agenda}
    (derived : AgendaConnDerivable (α := α) clauses agenda) : ∃ trace, AgendaTraceDerivable clauses agenda trace := by
  induction derived with
  | done => exact ⟨[], .done⟩
  | reduce literal rest path complementary tail ih =>
      obtain ⟨trace, checked⟩ := ih
      exact ⟨.step_reduce literal :: trace, .reduce literal rest path trace complementary checked⟩
  | extend literal rest path clause member complementary tail ih =>
      obtain ⟨trace, checked⟩ := ih
      exact ⟨.step_extend literal clause :: trace, .extend literal rest path clause trace member complementary checked⟩

theorem replay_true_of_traceDerivable (clauses goals path trace)
    (derived : TraceDerivable (α := α) clauses goals path trace) : replay clauses goals path trace = true :=
  replayAgenda_true_of_derivable derived

theorem traceDerivable_of_replay_true (clauses : ConnCNF α) (goals path : ConnClause α) (trace : ProofTrace α)
    (checked : replay clauses goals path trace = true) : TraceDerivable clauses goals path trace :=
  agendaDerivable_of_replay_true clauses _ trace checked

theorem replay_true_iff_traceDerivable (clauses goals path trace) :
    replay (α := α) clauses goals path trace = true ↔ TraceDerivable clauses goals path trace :=
  replayAgenda_true_iff_derivable clauses _ trace

theorem TraceDerivable.toConnDerivable {clauses goals path trace}
    (derived : TraceDerivable (α := α) clauses goals path trace) : ConnDerivable clauses goals path :=
  AgendaTraceDerivable.toConnDerivable derived

theorem ConnDerivable.exists_trace {clauses goals path}
    (derived : ConnDerivable (α := α) clauses goals path) : ∃ trace, TraceDerivable clauses goals path trace :=
  AgendaConnDerivable.exists_trace derived

theorem connDerivable_iff_exists_trace (clauses goals path) :
    ConnDerivable (α := α) clauses goals path ↔ ∃ trace, TraceDerivable clauses goals path trace :=
  ⟨ConnDerivable.exists_trace, fun ⟨_, derived⟩ => derived.toConnDerivable⟩

/-- Operational replay correspondence for the branch-local agenda. -/
theorem replay_sound {clauses goals path trace}
    (checked : replay (α := α) clauses goals path trace = true) : ConnDerivable clauses goals path :=
  (traceDerivable_of_replay_true clauses goals path trace checked).toConnDerivable

theorem replay_complete {clauses goals path} (derived : ConnDerivable (α := α) clauses goals path) :
    ∃ trace, replay clauses goals path trace = true := by
  obtain ⟨trace, traced⟩ := derived.exists_trace
  exact ⟨trace, replay_true_of_traceDerivable clauses goals path trace traced⟩

theorem checkProof_true_iff_root_mem_and_traceDerivable (clauses : ConnCNF α) (p : ProofObj α) :
    checkProof clauses p = true ↔ p.root ∈ clauses ∧ TraceDerivable clauses p.root [] p.trace := by
  simp only [checkProof, Bool.and_eq_true, decide_eq_true_eq, replay_true_iff_traceDerivable]

/-- Operational root derivability. Boolean semantic soundness is `checkProof_unsatisfiable`. -/
theorem checkProof_sound (clauses : ConnCNF α) (proof : ProofObj α) (checked : checkProof clauses proof = true) :
    proof.root ∈ clauses ∧ ConnDerivable clauses proof.root [] := by
  obtain ⟨member, traced⟩ := (checkProof_true_iff_root_mem_and_traceDerivable clauses proof).mp checked
  exact ⟨member, traced.toConnDerivable⟩

theorem exists_checkProof_true_of_root_mem_and_connDerivable (clauses : ConnCNF α) (root : ConnClause α)
    (member : root ∈ clauses) (derived : ConnDerivable clauses root []) :
    ∃ proof : ProofObj α, checkProof clauses proof = true := by
  obtain ⟨trace, checked⟩ := replay_complete derived
  exact ⟨⟨trace.length, root, trace⟩, by simp [checkProof, member, checked]⟩

omit [DecidableEq α] in
def Lit.eval (valuation : α → Bool) : Lit α → Bool
  | .pos atom => valuation atom
  | .neg atom => !(valuation atom)

omit [DecidableEq α] in
@[simp] theorem Lit.eval_complement (valuation : α → Bool) (literal : Lit α) :
    literal.complement.eval valuation = !(literal.eval valuation) := by
  cases literal <;> simp [Lit.eval, Lit.complement]

def ConnSatisfies (valuation : α → Bool) (clauses : ConnCNF α) : Prop :=
  ∀ clause ∈ clauses, ∃ literal ∈ clause, literal.eval valuation = true

def TrueConnectionGoal (valuation : α → Bool) (goal : ConnectionGoal (Lit α)) : Prop :=
  goal.literal.eval valuation = true ∧ ∀ ancestor ∈ goal.path, ancestor.eval valuation = true

def TrueConnectionAgenda (valuation : α → Bool) (agenda : ConnAgenda α) : Prop :=
  ∃ goal ∈ agenda, TrueConnectionGoal valuation goal

omit [DecidableEq α] in
theorem true_agenda_after_reduction (valuation : α → Bool) (literal : Lit α) (path : ConnClause α)
    (rest : ConnAgenda α) (complementary : literal.complement ∈ path)
    (before : TrueConnectionAgenda valuation (⟨literal, path⟩ :: rest)) : TrueConnectionAgenda valuation rest := by
  obtain ⟨goal, member, trueGoal⟩ := before
  rcases List.mem_cons.mp member with same | retained
  · subst goal
    have impossible := trueGoal.2 _ complementary
    rw [Lit.eval_complement, trueGoal.1] at impossible
    cases impossible
  · exact ⟨goal, retained, trueGoal⟩

theorem true_agenda_after_extension (valuation : α → Bool) (clauses : ConnCNF α)
    (satisfies : ConnSatisfies valuation clauses) (literal : Lit α) (path clause : ConnClause α)
    (rest : ConnAgenda α) (member : clause ∈ clauses)
    (before : TrueConnectionAgenda valuation (⟨literal, path⟩ :: rest)) :
    TrueConnectionAgenda valuation (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) := by
  obtain ⟨goal, selected, trueGoal⟩ := before
  rcases List.mem_cons.mp selected with same | retained
  · subst goal
    obtain ⟨child, childMember, childTrue⟩ := satisfies clause member
    have different : child ≠ literal.complement := by
      intro same
      rw [same, Lit.eval_complement, trueGoal.1] at childTrue
      cases childTrue
    have retainedChild : child ∈ clause.erase literal.complement := (List.mem_erase_of_ne different).mpr childMember
    refine ⟨⟨child, literal :: path⟩, List.mem_append_left _ ?_, childTrue, ?_⟩
    · exact List.mem_map.mpr ⟨child, retainedChild, rfl⟩
    · intro ancestor ancestorMember
      rcases List.mem_cons.mp ancestorMember with same | old
      · simpa only [same] using trueGoal.1
      · exact trueGoal.2 ancestor old
  · exact ⟨goal, List.mem_append_right _ retained, trueGoal⟩

/-- This proof uses Boolean truth and the actual replay transitions, independently of derivability. -/
theorem replayAgenda_excludes_true_agenda (valuation : α → Bool) (clauses : ConnCNF α)
    (satisfies : ConnSatisfies valuation clauses) :
    ∀ agenda trace, replayAgenda clauses agenda trace = true → ¬ TrueConnectionAgenda valuation agenda
  | agenda, [], checked, before => by
      have empty : agenda = [] := by simpa [replayAgenda] using checked
      subst agenda
      obtain ⟨_, member, _⟩ := before
      cases member
  | [], _ :: _, checked, _ => by simp [replayAgenda] at checked
  | ⟨literal, path⟩ :: rest, step :: steps, checked, before => by
      cases step with
      | step_reduce selected =>
          have parts : literal = selected ∧ literal.complement ∈ path ∧ replayAgenda clauses rest steps = true := by
            simpa [replayAgenda, Bool.ite_eq_true_distrib, and_assoc] using checked
          exact replayAgenda_excludes_true_agenda valuation clauses satisfies rest steps parts.2.2
            (true_agenda_after_reduction valuation literal path rest parts.2.1 before)
      | step_extend selected clause =>
          have parts : literal = selected ∧ clause ∈ clauses ∧ literal.complement ∈ clause ∧
              replayAgenda clauses (connectionGoals (clause.erase literal.complement) (literal :: path) ++ rest) steps = true := by
            simpa [replayAgenda, Bool.ite_eq_true_distrib, and_assoc] using checked
          exact replayAgenda_excludes_true_agenda valuation clauses satisfies _ steps parts.2.2.2
            (true_agenda_after_extension valuation clauses satisfies literal path clause rest parts.2.1 before)

theorem checkProof_unsatisfiable (clauses : ConnCNF α) (proof : ProofObj α)
    (checked : checkProof clauses proof = true) : ∀ valuation : α → Bool, ¬ ConnSatisfies valuation clauses := by
  intro valuation satisfies
  have parts : decide (proof.root ∈ clauses) = true ∧ replay clauses proof.root [] proof.trace = true := by
    simpa only [checkProof, Bool.and_eq_true] using checked
  have rootMember : proof.root ∈ clauses := of_decide_eq_true parts.1
  obtain ⟨literal, member, isTrue⟩ := satisfies proof.root rootMember
  apply replayAgenda_excludes_true_agenda valuation clauses satisfies _ proof.trace parts.2
  exact ⟨⟨literal, []⟩, List.mem_map.mpr ⟨literal, member, rfl⟩, isTrue,
    fun _ absent => False.elim (List.not_mem_nil absent)⟩

theorem checkProof_rejects_model (clauses : ConnCNF α) (valuation : α → Bool)
    (satisfies : ConnSatisfies valuation clauses) (proof : ProofObj α) : checkProof clauses proof = false := by
  cases computed : checkProof clauses proof with
  | false => rfl
  | true => exact False.elim (checkProof_unsatisfiable clauses proof computed valuation satisfies)

end PropositionalConnection

end Mettapedia.Logic.LP
