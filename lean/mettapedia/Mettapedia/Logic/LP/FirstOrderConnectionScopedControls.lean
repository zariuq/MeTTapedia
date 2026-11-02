import Mettapedia.Logic.LP.FirstOrderConnectionScopedSearch
import Mettapedia.Logic.LP.FirstOrderConnectionSemanticControls

/-!
# Fresh repeated clause uses in the actual connection replay

The same authored variable is copied at different activation scopes. A
two-literal root uses one source unit twice; the old unscoped profile instead
meets its own variable beneath a constructor and fails the occurs check.
-/

namespace Mettapedia.Logic.LP.FirstOrderConnectionScopedControls

noncomputable section

abbrev signature : LPSignature where
  constants := Unit
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 1
  functionSymbols := Bool
  functionArity _ := 1

def predicate (term : Term signature) : Atom signature := ⟨(), fun _ => term⟩
def scopedPredicate (term : Term signature.scoped) : Atom signature.scoped := ⟨(), fun _ => term⟩
def unary (which : Bool) (term : Term signature) : Term signature := .app which (fun _ => term)
def scopedUnary (which : Bool) (term : Term signature.scoped) : Term signature.scoped := .app which (fun _ => term)
def scopedVariable (scope : Nat) : Term signature.scoped := .var (ScopedVar.at scope 0)

def root : ConnFOClause signature :=
  [.pos (predicate (unary false (.var 0))), .pos (predicate (unary true (.var 0)))]
def negativeUnit : ConnFOClause signature := [.neg (predicate (.var 0))]
def matrix : ConnFOCNF signature := [root, negativeUnit]

def firstSubstitution : Subst signature.scoped :=
  Subst.single (ScopedVar.at 1 0) (scopedUnary false (scopedVariable 0))
def secondSubstitution : Subst signature.scoped :=
  Subst.single (ScopedVar.at 2 0) (scopedUnary true (scopedVariable 0))

theorem first_actual_unifier :
    unifyComplementLit? 4 (.pos (scopedPredicate (scopedUnary false (scopedVariable 0))))
      (.neg (scopedPredicate (scopedVariable 1))) = some firstSubstitution := by
  change some ((Subst.id signature.scoped).comp firstSubstitution) = some firstSubstitution
  congr 1
  funext name
  exact Subst.applyTerm_id _

theorem second_actual_unifier :
    unifyComplementLit? 4 (.pos (scopedPredicate (scopedUnary true (scopedVariable 0))))
      (.neg (scopedPredicate (scopedVariable 2))) = some secondSubstitution := by
  change some ((Subst.id signature.scoped).comp secondSubstitution) = some secondSubstitution
  congr 1
  funext name
  exact Subst.applyTerm_id _

theorem the_first_unifier_keeps_the_root_sibling :
    firstSubstitution.applyConnFOAgenda
      [⟨.pos (scopedPredicate (scopedUnary true (scopedVariable 0))), []⟩] =
      [⟨.pos (scopedPredicate (scopedUnary true (scopedVariable 0))), []⟩] := by
  simp [firstSubstitution, Subst.applyConnFOAgenda, ConnectionAgenda.map, ConnectionGoal.map,
    Subst.applyConnFOLit, Subst.applyAtom, Subst.applyTerm,
    Subst.single, scopedPredicate, scopedUnary, scopedVariable, ScopedVar.at]

def proof : FOProofObj signature.scoped :=
  ⟨2, connFOClauseAtScope 0 root,
    [.step_extend (connFOClauseAtScope 1 negativeUnit) (.neg (scopedPredicate (scopedVariable 1))),
     .step_extend (connFOClauseAtScope 2 negativeUnit) (.neg (scopedPredicate (scopedVariable 2)))]⟩

theorem the_same_source_unit_is_used_at_two_fresh_scopes : checkProofScopedFO matrix 4 proof = true := by
  have rootMember : connFOClauseAtScope 0 root ∈ connFOMatrixAtScope matrix 0 := by
    exact List.mem_map.mpr ⟨root, by simp [matrix], rfl⟩
  have firstMember : connFOClauseAtScope 1 negativeUnit ∈ connFOMatrixAtScope matrix 1 := by
    exact List.mem_map.mpr ⟨negativeUnit, by simp [matrix], rfl⟩
  have secondMember : connFOClauseAtScope 2 negativeUnit ∈ connFOMatrixAtScope matrix 2 := by
    exact List.mem_map.mpr ⟨negativeUnit, by simp [matrix], rfl⟩
  simp only [checkProofScopedFO, proof, rootMember, decide_true, Bool.true_and]
  change replayFOClauseSource (connFOMatrixAtScope matrix) 4 1
    [⟨.pos (scopedPredicate (scopedUnary false (scopedVariable 0))), []⟩,
     ⟨.pos (scopedPredicate (scopedUnary true (scopedVariable 0))), []⟩]
    [.step_extend (connFOClauseAtScope 1 negativeUnit) (.neg (scopedPredicate (scopedVariable 1))),
     .step_extend (connFOClauseAtScope 2 negativeUnit) (.neg (scopedPredicate (scopedVariable 2)))] = true
  have firstUnit : connFOClauseAtScope 1 negativeUnit = [.neg (scopedPredicate (scopedVariable 1))] := rfl
  have secondUnit : connFOClauseAtScope 2 negativeUnit = [.neg (scopedPredicate (scopedVariable 2))] := rfl
  rw [replayFOClauseSource.eq_def (σ := signature.scoped)]
  dsimp only
  rw [if_pos ⟨firstMember, by simp [firstUnit]⟩, first_actual_unifier]
  dsimp only
  rw [firstUnit, List.erase_cons_head, connectionGoals_nil, List.nil_append,
    the_first_unifier_keeps_the_root_sibling]
  rw [replayFOClauseSource.eq_def (σ := signature.scoped)]
  dsimp only
  rw [if_pos ⟨secondMember, by simp [secondUnit]⟩, second_actual_unifier]
  dsimp only
  simp [secondUnit, replayFOClauseSource]

theorem the_old_unscoped_head_connection_fails_the_occurs_check :
    unifyComplementLit? 4 (.pos (predicate (unary false (.var 0))))
      (.neg (predicate (.var 0))) = none := by
  rfl

theorem copied_variables_retain_their_actual_activation_identity :
    (ScopedVar.at (V := Nat) 1 0) ≠ ScopedVar.at 2 0 := by decide

theorem a_fresh_unit_copy_cannot_be_substituted_for_a_different_activation :
    connFOClauseAtScope 2 negativeUnit ∉ connFOMatrixAtScope matrix 1 := by
  intro member
  simp only [connFOMatrixAtScope, matrix, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with wrongRoot | wrongUnit
  · have lengths := congrArg List.length wrongRoot
    simp [connFOClauseAtScope, root, negativeUnit] at lengths
  · have literals := (List.cons.inj wrongUnit).1
    have atoms := ConnFOLit.neg.inj literals
    have arguments := congrArg (fun atom : Atom signature.scoped => atom.args 0) atoms
    change Term.var (σ := signature.scoped) (ScopedVar.at 2 0) = .var (ScopedVar.at 1 0) at arguments
    have names := Term.var.inj arguments
    have scopes := congrArg ScopedVar.scope names
    cases scopes

theorem the_actual_root_is_bounded_before_its_first_copy :
    ConnectionAgendaScopesBelow 1 (connectionGoals (connFOClauseAtScope 0 root) []) :=
  connection_root_scope_bound root

def groundAtom : Atom signature := predicate (.const ())
def otherGroundAtom : Atom signature := predicate (unary false (.const ()))
def groundRoot : ConnFOClause signature := [.pos groundAtom]
def groundFirst : ConnFOClause signature := [.neg groundAtom, .pos otherGroundAtom]
def groundSecond : ConnFOClause signature := [.neg otherGroundAtom, .neg groundAtom]
def groundMatrix : ConnFOCNF signature := [groundRoot, groundFirst, groundSecond]
def runtimeGround : Atom signature.scoped := scopedPredicate (.const ())
def runtimeOther : Atom signature.scoped := scopedPredicate (scopedUnary false (.const ()))
def reductionProof : FOProofObj signature.scoped :=
  ⟨3, connFOClauseAtScope 0 groundRoot,
    [.step_extend (connFOClauseAtScope 1 groundFirst) (.neg runtimeGround),
     .step_extend (connFOClauseAtScope 2 groundSecond) (.neg runtimeOther),
     .step_reduce (.pos runtimeGround)]⟩

theorem an_actual_child_reduces_against_its_own_ancestor : checkProofScopedFO groundMatrix 4 reductionProof = true := by
  have rootMember : connFOClauseAtScope 0 groundRoot ∈ connFOMatrixAtScope groundMatrix 0 :=
    List.mem_map.mpr ⟨groundRoot, by simp [groundMatrix], rfl⟩
  have firstMember : connFOClauseAtScope 1 groundFirst ∈ connFOMatrixAtScope groundMatrix 1 :=
    List.mem_map.mpr ⟨groundFirst, by simp [groundMatrix], rfl⟩
  have secondMember : connFOClauseAtScope 2 groundSecond ∈ connFOMatrixAtScope groundMatrix 2 :=
    List.mem_map.mpr ⟨groundSecond, by simp [groundMatrix], rfl⟩
  have firstCopy : connFOClauseAtScope 1 groundFirst = [.neg runtimeGround, .pos runtimeOther] := rfl
  have secondCopy : connFOClauseAtScope 2 groundSecond = [.neg runtimeOther, .neg runtimeGround] := rfl
  have firstUnifier : unifyComplementLit? 4 (.pos runtimeGround) (.neg runtimeGround) = some (Subst.id signature.scoped) := rfl
  have secondUnifier : unifyComplementLit? 4 (.pos runtimeOther) (.neg runtimeOther) = some (Subst.id signature.scoped) := rfl
  have lastUnifier : unifyComplementLit? 4 (.neg runtimeGround) (.pos runtimeGround) = some (Subst.id signature.scoped) := rfl
  simp only [checkProofScopedFO, reductionProof, rootMember, decide_true, Bool.true_and]
  change replayFOClauseSource (connFOMatrixAtScope groundMatrix) 4 1
    [⟨.pos runtimeGround, []⟩] _ = true
  rw [replayFOClauseSource.eq_def (σ := signature.scoped)]
  dsimp only
  rw [if_pos ⟨firstMember, by simp [firstCopy]⟩, firstUnifier]
  dsimp only
  rw [firstCopy, List.erase_cons_head]
  simp only [connectionGoals_cons, connectionGoals_nil, List.append_nil, Subst.applyConnFOAgenda_id]
  rw [replayFOClauseSource.eq_def (σ := signature.scoped)]
  dsimp only
  rw [if_pos ⟨secondMember, by simp [secondCopy]⟩, secondUnifier]
  dsimp only
  rw [secondCopy, List.erase_cons_head]
  simp only [connectionGoals_cons, connectionGoals_nil, List.append_nil, Subst.applyConnFOAgenda_id]
  rw [replayFOClauseSource.eq_def (σ := signature.scoped)]
  dsimp only
  rw [if_pos (by simp), lastUnifier]
  simp [replayFOClauseSource]

theorem a_fresh_search_finds_a_checked_trace :
    ∃ trace, connProveFOClauseSourceDFS (connFOMatrixAtScope matrix) 4 1
      (connectionGoals (connFOClauseAtScope 0 root) []) 2 = some trace :=
  connProveFOClauseSourceDFS_complete_of_checked_trace (connFOMatrixAtScope matrix) 4 2 1 _ proof.trace
    (by simp [proof]) (by
      have parts : decide (proof.root ∈ connFOMatrixAtScope matrix 0) = true ∧
          replayFOClauseSource (connFOMatrixAtScope matrix) 4 1
            (connectionGoals proof.root []) proof.trace = true := by
        simpa only [checkProofScopedFO, Bool.and_eq_true] using the_same_source_unit_is_used_at_two_fresh_scopes
      exact parts.2)

theorem a_satisfiable_source_matrix_has_no_accepted_scoped_proof
    (candidate : FOProofObj FirstOrderConnectionSemanticControls.signature.scoped) (fuel : Nat) :
    checkProofScopedFO FirstOrderConnectionSemanticControls.satisfiableMatrix fuel candidate = false := by
  cases computed : checkProofScopedFO FirstOrderConnectionSemanticControls.satisfiableMatrix fuel candidate with
  | false => rfl
  | true =>
      exact False.elim (checkProofScopedFO_unsatisfiable
        FirstOrderConnectionSemanticControls.satisfiableMatrix fuel candidate computed
        FirstOrderConnectionSemanticControls.the_satisfiable_matrix_has_a_nonempty_first_order_model)

end

end Mettapedia.Logic.LP.FirstOrderConnectionScopedControls
