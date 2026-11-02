import Mettapedia.Logic.LP.ConnectionAgenda
import Mettapedia.Logic.LP.Unification

/-!
# First-order connection replay with branch-local ancestor paths

Substitutions propagate to every open goal and every stored ancestor path.
Only an extension's new children receive the current goal as an ancestor;
pending siblings retain their own paths. The trace format is unchanged.

This fixed-variable replay profile checks matrix clauses as supplied. It
does not standardize clause variables apart on each use. Independent
first-order model soundness is proved in `FirstOrderConnectionSoundness`;
the operational correspondence here is not its logical justification.
Completeness of a fresh-instance connection calculus is separate.
-/

namespace Mettapedia.Logic.LP

noncomputable section

variable {σ : LPSignature}

inductive ConnFOLit (σ : LPSignature) where
  | pos : Atom σ → ConnFOLit σ
  | neg : Atom σ → ConnFOLit σ

abbrev ConnFOClause (σ : LPSignature) := List (ConnFOLit σ)
abbrev ConnFOCNF (σ : LPSignature) := List (ConnFOClause σ)
abbrev ConnFOAgenda (σ : LPSignature) := ConnectionAgenda (ConnFOLit σ)

noncomputable instance : DecidableEq (ConnFOLit σ) := Classical.decEq _

def ConnFOLit.complement : ConnFOLit σ → ConnFOLit σ
  | .pos atom => .neg atom
  | .neg atom => .pos atom

def Subst.applyConnFOLit (substitution : Subst σ) : ConnFOLit σ → ConnFOLit σ
  | .pos atom => .pos (substitution.applyAtom atom)
  | .neg atom => .neg (substitution.applyAtom atom)

def Subst.applyConnFOClause (substitution : Subst σ) (clause : ConnFOClause σ) : ConnFOClause σ :=
  clause.map substitution.applyConnFOLit

def Subst.applyConnFOAgenda (substitution : Subst σ) (agenda : ConnFOAgenda σ) : ConnFOAgenda σ :=
  ConnectionAgenda.map substitution.applyConnFOLit agenda

@[simp] theorem Subst.applyConnFOLit_id (literal : ConnFOLit σ) :
    (Subst.id σ).applyConnFOLit literal = literal := by
  cases literal <;> simp only [Subst.applyConnFOLit, Subst.applyAtom_id]

@[simp] theorem Subst.applyConnFOClause_id (clause : ConnFOClause σ) :
    (Subst.id σ).applyConnFOClause clause = clause := by
  have same : (Subst.id σ).applyConnFOLit = _root_.id := funext Subst.applyConnFOLit_id
  simp only [Subst.applyConnFOClause, same, List.map_id]

@[simp] theorem Subst.applyConnFOAgenda_id (agenda : ConnFOAgenda σ) :
    (Subst.id σ).applyConnFOAgenda agenda = agenda := by
  have same : (Subst.id σ).applyConnFOLit = _root_.id := funext Subst.applyConnFOLit_id
  have goals : ConnectionGoal.map (_root_.id : ConnFOLit σ → ConnFOLit σ) = _root_.id := by
    funext goal
    cases goal
    simp [ConnectionGoal.map]
  simp only [Subst.applyConnFOAgenda, ConnectionAgenda.map, same, goals, List.map_id]

@[simp] theorem Subst.applyConnFOAgenda_nil (substitution : Subst σ) : substitution.applyConnFOAgenda [] = [] := rfl

@[simp] theorem Subst.applyConnFOAgenda_cons (substitution : Subst σ) (literal : ConnFOLit σ)
    (path : ConnFOClause σ) (rest : ConnFOAgenda σ) :
    substitution.applyConnFOAgenda (⟨literal, path⟩ :: rest) =
      ⟨substitution.applyConnFOLit literal, substitution.applyConnFOClause path⟩ :: substitution.applyConnFOAgenda rest := rfl

theorem Subst.applyConnFOAgenda_append (substitution : Subst σ) (first second : ConnFOAgenda σ) :
    substitution.applyConnFOAgenda (first ++ second) =
      substitution.applyConnFOAgenda first ++ substitution.applyConnFOAgenda second := List.map_append

@[simp] theorem Subst.applyConnFOAgenda_open (substitution : Subst σ) (goals path : ConnFOClause σ) :
    substitution.applyConnFOAgenda (connectionGoals goals path) =
      connectionGoals (substitution.applyConnFOClause goals) (substitution.applyConnFOClause path) := by
  induction goals with
  | nil => rfl
  | cons literal rest earlier =>
      simpa only [connectionGoals_cons, Subst.applyConnFOAgenda_cons, Subst.applyConnFOClause, List.map_cons]
        using congrArg (List.cons ⟨substitution.applyConnFOLit literal, substitution.applyConnFOClause path⟩) earlier

variable [DecidableEq σ.vars] [DecidableEq σ.constants]
variable [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

def unifyComplementLit? (fuel : Nat) (left right : ConnFOLit σ) : Option (Subst σ) :=
  match left, right with
  | .pos first, .neg second => unifyAtoms first second fuel
  | .neg first, .pos second => unifyAtoms first second fuel
  | _, _ => none

inductive FOProofStep (σ : LPSignature) where
  | step_reduce : ConnFOLit σ → FOProofStep σ
  | step_extend : ConnFOClause σ → ConnFOLit σ → FOProofStep σ

abbrev FOProofTrace (σ : LPSignature) := List (FOProofStep σ)

structure FOProofObj (σ : LPSignature) where
  fuel : Nat
  root : ConnFOClause σ
  trace : FOProofTrace σ

def replayFOAgenda (clauses : ConnFOCNF σ) (uFuel : Nat) (agenda : ConnFOAgenda σ) : FOProofTrace σ → Bool
  | [] => decide (agenda = [])
  | step :: steps =>
      match agenda with
      | [] => false
      | ⟨literal, path⟩ :: rest =>
          match step with
          | .step_reduce selected =>
              if selected ∈ path then
                match unifyComplementLit? uFuel literal selected with
                | some substitution => replayFOAgenda clauses uFuel (substitution.applyConnFOAgenda rest) steps
                | none => false
              else false
          | .step_extend clause selected =>
              if clause ∈ clauses ∧ selected ∈ clause then
                match unifyComplementLit? uFuel literal selected with
                | some substitution =>
                    replayFOAgenda clauses uFuel
                      (substitution.applyConnFOAgenda (connectionGoals (clause.erase selected) (literal :: path) ++ rest)) steps
                | none => false
              else false

def replayFO (clauses : ConnFOCNF σ) (uFuel : Nat) (goals path : ConnFOClause σ) (trace : FOProofTrace σ) : Bool :=
  replayFOAgenda clauses uFuel (connectionGoals goals path) trace

def checkProofFO (clauses : ConnFOCNF σ) (uFuel : Nat) (proof : FOProofObj σ) : Bool :=
  decide (proof.root ∈ clauses) && replayFO clauses uFuel proof.root [] proof.trace

inductive AgendaTraceDerivableFO (clauses : ConnFOCNF σ) (uFuel : Nat) : ConnFOAgenda σ → FOProofTrace σ → Prop
  | done : AgendaTraceDerivableFO clauses uFuel [] []
  | reduce (literal : ConnFOLit σ) (rest : ConnFOAgenda σ) (path : ConnFOClause σ)
      (selected : ConnFOLit σ) (steps : FOProofTrace σ) (substitution : Subst σ)
      (member : selected ∈ path) (unified : unifyComplementLit? uFuel literal selected = some substitution)
      (tail : AgendaTraceDerivableFO clauses uFuel (substitution.applyConnFOAgenda rest) steps) :
      AgendaTraceDerivableFO clauses uFuel (⟨literal, path⟩ :: rest) (.step_reduce selected :: steps)
  | extend (literal : ConnFOLit σ) (rest : ConnFOAgenda σ) (path clause : ConnFOClause σ)
      (selected : ConnFOLit σ) (steps : FOProofTrace σ) (substitution : Subst σ)
      (member : clause ∈ clauses) (selectedMember : selected ∈ clause)
      (unified : unifyComplementLit? uFuel literal selected = some substitution)
      (tail : AgendaTraceDerivableFO clauses uFuel
        (substitution.applyConnFOAgenda (connectionGoals (clause.erase selected) (literal :: path) ++ rest)) steps) :
      AgendaTraceDerivableFO clauses uFuel (⟨literal, path⟩ :: rest) (.step_extend clause selected :: steps)

abbrev TraceDerivableFO (clauses : ConnFOCNF σ) (uFuel : Nat) (goals path : ConnFOClause σ) (trace : FOProofTrace σ) : Prop :=
  AgendaTraceDerivableFO clauses uFuel (connectionGoals goals path) trace

theorem replayFOAgenda_true_of_derivable {clauses uFuel agenda trace}
    (derived : AgendaTraceDerivableFO (σ := σ) clauses uFuel agenda trace) : replayFOAgenda clauses uFuel agenda trace = true := by
  induction derived with
  | done => rfl
  | reduce literal rest path selected steps substitution member unified tail checked =>
      simp [replayFOAgenda, member, unified, checked]
  | extend literal rest path clause selected steps substitution member selectedMember unified tail checked =>
      simp [replayFOAgenda, member, selectedMember, unified, checked]

theorem agendaDerivableFO_of_replay_true (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ agenda trace, replayFOAgenda clauses uFuel agenda trace = true → AgendaTraceDerivableFO clauses uFuel agenda trace
  | agenda, [], checked => by
      have empty : agenda = [] := by simpa [replayFOAgenda] using checked
      subst agenda
      exact .done
  | [], _ :: _, checked => by simp [replayFOAgenda] at checked
  | ⟨literal, path⟩ :: rest, step :: steps, checked => by
      cases step with
      | step_reduce selected =>
          by_cases member : selected ∈ path
          · simp only [replayFOAgenda, if_pos member] at checked
            cases unified : unifyComplementLit? uFuel literal selected with
            | none => simp only [unified, Bool.false_eq_true] at checked
            | some substitution =>
                exact .reduce literal rest path selected steps substitution member unified
                  (agendaDerivableFO_of_replay_true clauses uFuel _ steps (by simpa only [unified] using checked))
          · simp only [replayFOAgenda, if_neg member, Bool.false_eq_true] at checked
      | step_extend clause selected =>
          by_cases member : clause ∈ clauses ∧ selected ∈ clause
          · simp only [replayFOAgenda, if_pos member] at checked
            cases unified : unifyComplementLit? uFuel literal selected with
            | none => simp only [unified, Bool.false_eq_true] at checked
            | some substitution =>
                exact .extend literal rest path clause selected steps substitution member.1 member.2 unified
                  (agendaDerivableFO_of_replay_true clauses uFuel _ steps (by simpa only [unified] using checked))
          · simp only [replayFOAgenda, if_neg member, Bool.false_eq_true] at checked

theorem traceDerivableFO_of_replayFO_true (clauses : ConnFOCNF σ) (uFuel : Nat)
    (goals path : ConnFOClause σ) (trace : FOProofTrace σ) (checked : replayFO clauses uFuel goals path trace = true) :
    TraceDerivableFO clauses uFuel goals path trace := agendaDerivableFO_of_replay_true clauses uFuel _ trace checked

/-- Operational correspondence for the supplied fixed-variable clause profile. -/
theorem replayFO_sound {clauses : ConnFOCNF σ} {uFuel : Nat} {goals path : ConnFOClause σ} {trace : FOProofTrace σ}
    (checked : replayFO clauses uFuel goals path trace = true) : TraceDerivableFO clauses uFuel goals path trace :=
  traceDerivableFO_of_replayFO_true clauses uFuel goals path trace checked

theorem replayFO_true_iff_derivable (clauses : ConnFOCNF σ) (uFuel : Nat) (goals path : ConnFOClause σ) (trace : FOProofTrace σ) :
    replayFO clauses uFuel goals path trace = true ↔ TraceDerivableFO clauses uFuel goals path trace :=
  ⟨traceDerivableFO_of_replayFO_true clauses uFuel goals path trace, replayFOAgenda_true_of_derivable⟩

end

end Mettapedia.Logic.LP
