import Mettapedia.Logic.LP.FirstOrderConnectionTrace

/-!
# First-order sibling restoration and substitution controls

The three-step completed-branch reduction is rejected for arbitrary atoms
and unification fuel. This checks the replay path discipline without
assuming a particular unifier result. Substitution propagates through both
pending frames while retaining their separate ancestor lists.
-/

namespace Mettapedia.Logic.LP.FirstOrderConnectionControls

noncomputable section

variable {σ : LPSignature}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
variable [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

theorem an_empty_path_cannot_supply_a_reduction (clauses : ConnFOCNF σ) (uFuel : Nat)
    (literal selected : ConnFOLit σ) (rest : ConnFOAgenda σ) (steps : FOProofTrace σ) :
    replayFOAgenda clauses uFuel (⟨literal, []⟩ :: rest) (.step_reduce selected :: steps) = false := by
  simp [replayFOAgenda]

theorem completed_child_cannot_reduce_its_root_sibling (clauses : ConnFOCNF σ) (uFuel : Nat)
    (first second selected child unit reduction : ConnFOLit σ) :
    replayFO clauses uFuel [first, second] []
      [.step_extend [selected, child] selected, .step_extend [unit] unit, .step_reduce reduction] = false := by
  cases firstUnify : unifyComplementLit? uFuel first selected with
  | none =>
      simp [replayFO, replayFOAgenda, connectionGoals, firstUnify]
  | some firstSubstitution =>
      cases secondUnify : unifyComplementLit? uFuel (firstSubstitution.applyConnFOLit child) unit with
      | none =>
          simp [replayFO, replayFOAgenda, connectionGoals, firstUnify, secondUnify,
            Subst.applyConnFOAgenda, ConnectionAgenda.map, ConnectionGoal.map]
      | some secondSubstitution =>
          simp [replayFO, replayFOAgenda, connectionGoals, firstUnify, secondUnify,
            Subst.applyConnFOAgenda, ConnectionAgenda.map, ConnectionGoal.map]

def siblingLeakClauses (first second : Atom σ) : ConnFOCNF σ :=
  [[.pos first, .pos second], [.neg first, .neg second], [.pos second]]

def siblingLeakProof (first second : Atom σ) : FOProofObj σ :=
  ⟨3, [.pos first, .pos second],
    [.step_extend [.neg first, .neg second] (.neg first), .step_extend [.pos second] (.pos second),
      .step_reduce (.neg second)]⟩

theorem the_corresponding_first_order_trace_is_rejected (first second : Atom σ) (uFuel : Nat) :
    checkProofFO (siblingLeakClauses first second) uFuel (siblingLeakProof first second) = false := by
  have rejected := completed_child_cannot_reduce_its_root_sibling (siblingLeakClauses first second) uFuel
    (.pos first) (.pos second) (.neg first) (.neg second) (.pos second) (.neg second)
  simp only [checkProofFO, siblingLeakProof, rejected, Bool.and_false]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem substitution_keeps_the_two_sibling_paths_separate (substitution : Subst σ)
    (first second : ConnFOLit σ) (firstPath secondPath : ConnFOClause σ) :
    substitution.applyConnFOAgenda [⟨first, firstPath⟩, ⟨second, secondPath⟩] =
      [⟨substitution.applyConnFOLit first, substitution.applyConnFOClause firstPath⟩,
       ⟨substitution.applyConnFOLit second, substitution.applyConnFOClause secondPath⟩] := rfl

end

end Mettapedia.Logic.LP.FirstOrderConnectionControls
