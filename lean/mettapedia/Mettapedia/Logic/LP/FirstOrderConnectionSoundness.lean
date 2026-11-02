import Mettapedia.Logic.LP.FirstOrderConnectionCore
import Mettapedia.Logic.LP.FirstOrderBridge

/-!
# Independent first-order model soundness of connection replay

Literals are interpreted in an arbitrary nonempty structure for the existing
LP first-order language. Matrix clauses are universally closed. Every actual
unifier transports the uniform true-agenda invariant through the same semantic
substitution law used for ordinary first-order terms.

Acceptance therefore refutes every such structure, independently of the
operational derivability relation. This result applies to the existing
fixed-variable replay. Per-use standardization apart and proof-search
completeness are separate obligations.
-/

namespace Mettapedia.Logic.LP

noncomputable section

open FirstOrderBridge

variable {σ : LPSignature} {Model : Type*} [(language σ).Structure Model]

def ConnFOLit.Holds (assignment : σ.vars → Model) : ConnFOLit σ → Prop
  | .pos atom => realizeAtom assignment atom
  | .neg atom => ¬ realizeAtom assignment atom

theorem ConnFOLit.holds_complement (assignment : σ.vars → Model) (literal : ConnFOLit σ) :
    literal.complement.Holds assignment ↔ ¬ literal.Holds assignment := by
  cases literal <;> simp [ConnFOLit.complement, ConnFOLit.Holds]

theorem ConnFOLit.holds_substitution (assignment : σ.vars → Model) (substitution : Subst σ)
    (literal : ConnFOLit σ) :
    (substitution.applyConnFOLit literal).Holds assignment ↔
      literal.Holds (fun name => realizeTerm assignment (substitution name)) := by
  cases literal <;> simp only [Subst.applyConnFOLit, ConnFOLit.Holds, realizeAtom_applyAtom]

def ConnFOModels (clauses : ConnFOCNF σ) (Model : Type*) [(language σ).Structure Model] : Prop :=
  ∀ clause ∈ clauses, ∀ assignment : σ.vars → Model, ∃ literal ∈ clause, literal.Holds assignment

def TrueFOConnectionGoal (assignment : σ.vars → Model) (goal : ConnectionGoal (ConnFOLit σ)) : Prop :=
  goal.literal.Holds assignment ∧ ∀ ancestor ∈ goal.path, ancestor.Holds assignment

def TrueFOConnectionAgenda (assignment : σ.vars → Model) (agenda : ConnFOAgenda σ) : Prop :=
  ∃ goal ∈ agenda, TrueFOConnectionGoal assignment goal

theorem true_fo_agenda_substitution (assignment : σ.vars → Model) (substitution : Subst σ)
    (agenda : ConnFOAgenda σ) :
    TrueFOConnectionAgenda assignment (substitution.applyConnFOAgenda agenda) ↔
      TrueFOConnectionAgenda (fun name => realizeTerm assignment (substitution name)) agenda := by
  constructor
  · rintro ⟨goal, member, current, ancestors⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    refine ⟨original, present, (ConnFOLit.holds_substitution assignment substitution original.literal).mp current, ?_⟩
    intro ancestor inPath
    exact (ConnFOLit.holds_substitution assignment substitution ancestor).mp
      (ancestors _ (List.mem_map.mpr ⟨ancestor, inPath, rfl⟩))
  · rintro ⟨goal, member, current, ancestors⟩
    refine ⟨goal.map substitution.applyConnFOLit, List.mem_map.mpr ⟨goal, member, rfl⟩,
      (ConnFOLit.holds_substitution assignment substitution goal.literal).mpr current, ?_⟩
    intro ancestor inPath
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp inPath
    exact (ConnFOLit.holds_substitution assignment substitution original).mpr (ancestors original present)

variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

theorem unifyComplementLit?_complementary (fuel : Nat) (left right : ConnFOLit σ)
    (substitution : Subst σ) (unified : unifyComplementLit? fuel left right = some substitution) :
    (substitution.applyConnFOLit left).complement = substitution.applyConnFOLit right := by
  cases left with
  | pos first =>
      cases right with
      | pos second => simp [unifyComplementLit?] at unified
      | neg second =>
          exact congrArg ConnFOLit.neg (unifyAtoms_sound first second fuel substitution unified)
  | neg first =>
      cases right with
      | neg second => simp [unifyComplementLit?] at unified
      | pos second =>
          exact congrArg ConnFOLit.pos (unifyAtoms_sound first second fuel substitution unified)

private theorem connected_truth_excludes (fuel : Nat) (left right : ConnFOLit σ)
    (substitution : Subst σ) (unified : unifyComplementLit? fuel left right = some substitution)
    (assignment : σ.vars → Model) :
    ¬ (left.Holds (fun name => realizeTerm assignment (substitution name)) ∧
      right.Holds (fun name => realizeTerm assignment (substitution name))) := by
  rintro ⟨leftTrue, rightTrue⟩
  have first := (ConnFOLit.holds_substitution assignment substitution left).mpr leftTrue
  have second := (ConnFOLit.holds_substitution assignment substitution right).mpr rightTrue
  rw [← unifyComplementLit?_complementary fuel left right substitution unified] at second
  exact (ConnFOLit.holds_complement assignment _).mp second first

theorem uniform_true_fo_agenda_after_reduction (fuel : Nat) (literal selected : ConnFOLit σ)
    (path : ConnFOClause σ) (rest : ConnFOAgenda σ) (substitution : Subst σ)
    (member : selected ∈ path) (unified : unifyComplementLit? fuel literal selected = some substitution)
    (before : ∀ assignment : σ.vars → Model, TrueFOConnectionAgenda assignment (⟨literal, path⟩ :: rest)) :
    ∀ assignment : σ.vars → Model, TrueFOConnectionAgenda assignment (substitution.applyConnFOAgenda rest) := by
  intro assignment
  apply (true_fo_agenda_substitution assignment substitution rest).mpr
  obtain ⟨goal, present, current, ancestors⟩ := before (fun name => realizeTerm assignment (substitution name))
  rcases List.mem_cons.mp present with same | retained
  · subst goal
    exact False.elim (connected_truth_excludes fuel literal selected substitution unified assignment
      ⟨current, ancestors selected member⟩)
  · exact ⟨goal, retained, current, ancestors⟩

theorem uniform_true_fo_agenda_after_extension (clauses : ConnFOCNF σ)
    (model : ConnFOModels clauses Model) (fuel : Nat) (literal selected : ConnFOLit σ)
    (path clause : ConnFOClause σ) (rest : ConnFOAgenda σ) (substitution : Subst σ)
    (member : clause ∈ clauses) (unified : unifyComplementLit? fuel literal selected = some substitution)
    (before : ∀ assignment : σ.vars → Model, TrueFOConnectionAgenda assignment (⟨literal, path⟩ :: rest)) :
    ∀ assignment : σ.vars → Model, TrueFOConnectionAgenda assignment
      (substitution.applyConnFOAgenda (connectionGoals (clause.erase selected) (literal :: path) ++ rest)) := by
  intro assignment
  apply (true_fo_agenda_substitution assignment substitution _).mpr
  obtain ⟨goal, present, current, ancestors⟩ := before (fun name => realizeTerm assignment (substitution name))
  rcases List.mem_cons.mp present with same | retained
  · subst goal
    obtain ⟨child, childMember, childTrue⟩ := model clause member (fun name => realizeTerm assignment (substitution name))
    have different : child ≠ selected := by
      intro same
      subst child
      exact connected_truth_excludes fuel literal selected substitution unified assignment ⟨current, childTrue⟩
    refine ⟨⟨child, literal :: path⟩,
      List.mem_append_left _ (List.mem_map.mpr ⟨child, (List.mem_erase_of_ne different).mpr childMember, rfl⟩),
      childTrue, ?_⟩
    intro ancestor onPath
    rcases List.mem_cons.mp onPath with same | previous
    · simpa only [same] using current
    · exact ancestors ancestor previous
  · exact ⟨goal, List.mem_append_right _ retained, current, ancestors⟩

variable [Nonempty Model]

/-- Direct induction on the executable replay, interpreted in arbitrary
structures. No operational derivability theorem supplies the conclusion. -/
theorem replayFOAgenda_excludes_uniform_true (clauses : ConnFOCNF σ)
    (model : ConnFOModels clauses Model) (fuel : Nat) :
    ∀ agenda trace, replayFOAgenda clauses fuel agenda trace = true →
      ¬ (∀ assignment : σ.vars → Model, TrueFOConnectionAgenda assignment agenda)
  | agenda, [], checked, before => by
      have empty : agenda = [] := by simpa [replayFOAgenda] using checked
      subst agenda
      let assignment : σ.vars → Model := fun _ => Classical.choice (inferInstance : Nonempty Model)
      obtain ⟨_, member, _⟩ := before assignment
      cases member
  | [], _ :: _, checked, _ => by simp [replayFOAgenda] at checked
  | ⟨literal, path⟩ :: rest, step :: steps, checked, before => by
      cases step with
      | step_reduce selected =>
          by_cases member : selected ∈ path
          · simp only [replayFOAgenda, if_pos member] at checked
            cases unified : unifyComplementLit? fuel literal selected with
            | none => simp only [unified, Bool.false_eq_true] at checked
            | some substitution =>
                exact replayFOAgenda_excludes_uniform_true clauses model fuel _ steps
                  (by simpa only [unified] using checked)
                  (uniform_true_fo_agenda_after_reduction fuel literal selected path rest substitution member unified before)
          · simp only [replayFOAgenda, if_neg member, Bool.false_eq_true] at checked
      | step_extend clause selected =>
          by_cases member : clause ∈ clauses ∧ selected ∈ clause
          · simp only [replayFOAgenda, if_pos member] at checked
            cases unified : unifyComplementLit? fuel literal selected with
            | none => simp only [unified, Bool.false_eq_true] at checked
            | some substitution =>
                exact replayFOAgenda_excludes_uniform_true clauses model fuel _ steps
                  (by simpa only [unified] using checked)
                  (uniform_true_fo_agenda_after_extension clauses model fuel literal selected path clause rest substitution member.1 unified before)
          · simp only [replayFOAgenda, if_neg member, Bool.false_eq_true] at checked

theorem checkProofFO_unsatisfiable (clauses : ConnFOCNF σ) (fuel : Nat) (proof : FOProofObj σ)
    (checked : checkProofFO clauses fuel proof = true) : ¬ ConnFOModels clauses Model := by
  intro model
  have parts : proof.root ∈ clauses ∧ replayFO clauses fuel proof.root [] proof.trace = true := by
    simpa only [checkProofFO, Bool.and_eq_true, decide_eq_true_eq] using checked
  apply replayFOAgenda_excludes_uniform_true clauses model fuel _ proof.trace parts.2
  intro assignment
  obtain ⟨literal, member, trueLiteral⟩ := model proof.root parts.1 assignment
  exact ⟨⟨literal, []⟩, List.mem_map.mpr ⟨literal, member, rfl⟩,
    trueLiteral, fun _ absent => False.elim (List.not_mem_nil absent)⟩

theorem checkProofFO_rejects_model (clauses : ConnFOCNF σ) (fuel : Nat) (proof : FOProofObj σ)
    (model : ConnFOModels clauses Model) : checkProofFO clauses fuel proof = false := by
  cases computed : checkProofFO clauses fuel proof with
  | false => rfl
  | true => exact False.elim (checkProofFO_unsatisfiable clauses fuel proof computed model)

end

end Mettapedia.Logic.LP
