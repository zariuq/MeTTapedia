import Mettapedia.Logic.LP.FirstOrderConnectionScoped
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Actual connection unifiers preserve the scope bound of their inputs

Fresh clause copies use the existing numeric activation coordinate. The
relevance theorem for the actual Martelli–Montanari unifier shows that its
images cannot introduce a variable outside the selected input scopes.
Thus later clause activations are disjoint from the current live agenda;
freshness is not an assumed property of an unspecified solver.
-/

namespace Mettapedia.Logic.LP

noncomputable section

variable {σ : LPSignature} [DecidableEq σ.vars]

def ConnFOLit.freeVars : ConnFOLit σ → Finset σ.vars
  | .pos atom | .neg atom => atom.freeVars

def ConnectionAtomScopesBelow (bound : Nat) (atom : Atom σ.scoped) : Prop :=
  ∀ name ∈ atom.freeVars, name.scope < bound

def ConnectionLiteralScopesBelow (bound : Nat) (literal : ConnFOLit σ.scoped) : Prop :=
  ∀ name ∈ literal.freeVars, name.scope < bound

def ConnectionAgendaScopesBelow (bound : Nat) (agenda : ConnFOAgenda σ.scoped) : Prop :=
  ∀ goal ∈ agenda, ∀ literal ∈ goal.literal :: goal.path, ConnectionLiteralScopesBelow bound literal

theorem connection_copy_scope (scope : Nat) (literal : ConnFOLit σ)
    (name : ScopedVar σ.vars) (member : name ∈ (literal.atScope scope).freeVars) : name.scope = scope := by
  cases literal with
  | pos atom => exact Atom.scope_eq_of_mem_freeVars_atScope scope atom name member
  | neg atom => exact Atom.scope_eq_of_mem_freeVars_atScope scope atom name member

theorem connection_copy_avoids_old_agenda (nextScope : Nat) (agenda : ConnFOAgenda σ.scoped)
    (bounded : ConnectionAgendaScopesBelow nextScope agenda) (literal : ConnFOLit σ)
    (goal : ConnectionGoal (ConnFOLit σ.scoped)) (present : goal ∈ agenda)
    (old : ConnFOLit σ.scoped) (onGoal : old ∈ goal.literal :: goal.path) :
    Disjoint old.freeVars (literal.atScope nextScope).freeVars := by
  apply Finset.disjoint_left.mpr
  intro name previous copied
  have smaller := bounded goal present old onGoal name previous
  rw [connection_copy_scope nextScope literal name copied] at smaller
  exact Nat.lt_irrefl _ smaller

variable [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

theorem connection_unifyAtoms_preserves_scope (bound : Nat) (first second : Atom σ.scoped)
    (substitution : Subst σ.scoped) (fuel : Nat)
    (accepted : unifyAtoms first second fuel = some substitution)
    (firstBound : ConnectionAtomScopesBelow bound first)
    (secondBound : ConnectionAtomScopesBelow bound second) :
    ∀ term : Term σ.scoped,
      (∀ name ∈ term.freeVars, name.scope < bound) →
        ∀ name ∈ (substitution.applyTerm term).freeVars, name.scope < bound := by
  rcases first with ⟨firstSymbol, firstArguments⟩
  rcases second with ⟨secondSymbol, secondArguments⟩
  unfold unifyAtoms at accepted
  split at accepted
  · rename_i sameSymbol
    change firstSymbol = secondSymbol at sameSymbol
    subst secondSymbol
    have relevant := unifyFuel_relevantIdempotent fuel
      (finPairsToList firstArguments secondArguments) substitution accepted
    have equationBound : ∀ name ∈ eqVars (finPairsToList firstArguments secondArguments), name.scope < bound := by
      intro name occurs
      obtain ⟨equation, member, left | right⟩ := mem_eqVars.mp occurs
      · obtain ⟨position, _, same⟩ := List.mem_map.mp member
        cases same
        exact firstBound name (Finset.mem_biUnion.mpr ⟨position, Finset.mem_univ _, left⟩)
      · obtain ⟨position, _, same⟩ := List.mem_map.mp member
        cases same
        exact secondBound name (Finset.mem_biUnion.mpr ⟨position, Finset.mem_univ _, right⟩)
    intro term bounded name member
    rcases Finset.mem_union.mp (relevant.freeVars_applyTerm_subset term member) with old | new
    · exact bounded name old
    · exact equationBound name new
  · simp at accepted

theorem connection_unifier_preserves_scope (bound : Nat) (first second : ConnFOLit σ.scoped)
    (substitution : Subst σ.scoped) (fuel : Nat)
    (accepted : unifyComplementLit? fuel first second = some substitution)
    (firstBound : ConnectionLiteralScopesBelow bound first)
    (secondBound : ConnectionLiteralScopesBelow bound second) :
    ∀ term : Term σ.scoped,
      (∀ name ∈ term.freeVars, name.scope < bound) →
        ∀ name ∈ (substitution.applyTerm term).freeVars, name.scope < bound := by
  cases first with
  | pos atom =>
      cases second with
      | pos other => simp [unifyComplementLit?] at accepted
      | neg other => exact connection_unifyAtoms_preserves_scope bound atom other substitution fuel accepted firstBound secondBound
  | neg atom =>
      cases second with
      | neg other => simp [unifyComplementLit?] at accepted
      | pos other => exact connection_unifyAtoms_preserves_scope bound atom other substitution fuel accepted firstBound secondBound

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem connection_substitution_preserves_literal_scope (bound : Nat) (substitution : Subst σ.scoped)
    (preserves : ∀ term : Term σ.scoped,
      (∀ name ∈ term.freeVars, name.scope < bound) →
        ∀ name ∈ (substitution.applyTerm term).freeVars, name.scope < bound)
    (literal : ConnFOLit σ.scoped) (bounded : ConnectionLiteralScopesBelow bound literal) :
    ConnectionLiteralScopesBelow bound (substitution.applyConnFOLit literal) := by
  have atomPreserved : ∀ atom : Atom σ.scoped, ConnectionAtomScopesBelow bound atom →
      ConnectionAtomScopesBelow bound (substitution.applyAtom atom) := by
    intro atom boundAtom name occurs
    obtain ⟨position, _, member⟩ := Finset.mem_biUnion.mp occurs
    exact preserves (atom.args position)
      (fun identity member => boundAtom identity (Finset.mem_biUnion.mpr ⟨position, Finset.mem_univ _, member⟩))
      name member
  cases literal with
  | pos atom => exact atomPreserved atom bounded
  | neg atom => exact atomPreserved atom bounded

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem connection_substitution_preserves_agenda_scope (bound : Nat) (substitution : Subst σ.scoped)
    (preserves : ∀ term : Term σ.scoped,
      (∀ name ∈ term.freeVars, name.scope < bound) →
        ∀ name ∈ (substitution.applyTerm term).freeVars, name.scope < bound)
    (agenda : ConnFOAgenda σ.scoped) (bounded : ConnectionAgendaScopesBelow bound agenda) :
    ConnectionAgendaScopesBelow bound (substitution.applyConnFOAgenda agenda) := by
  intro goal member literal onGoal
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rcases List.mem_cons.mp onGoal with rfl | inPath
  · exact connection_substitution_preserves_literal_scope bound substitution preserves original.literal
      (bounded original present original.literal (by simp))
  · obtain ⟨ancestor, onPath, rfl⟩ := List.mem_map.mp inPath
    exact connection_substitution_preserves_literal_scope bound substitution preserves ancestor
      (bounded original present ancestor (List.mem_cons_of_mem _ onPath))

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem connection_scoped_clause_below (clauses : ConnFOCNF σ) (scope bound : Nat) (smaller : scope < bound)
    (clause : ConnFOClause σ.scoped) (copied : clause ∈ connFOMatrixAtScope clauses scope) :
    ∀ literal ∈ clause, ConnectionLiteralScopesBelow bound literal := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp copied
  intro literal member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  intro name occurs
  rw [connection_copy_scope scope original name occurs]
  exact smaller

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem connection_root_scope_bound (clause : ConnFOClause σ) :
    ConnectionAgendaScopesBelow 1 (connectionGoals (connFOClauseAtScope 0 clause) []) := by
  intro goal member literal onGoal
  obtain ⟨source, onClause, rfl⟩ := List.mem_map.mp member
  have same : literal = source := by simpa using onGoal
  subst literal
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp onClause
  intro name occurs
  rw [connection_copy_scope 0 original name occurs]
  exact Nat.zero_lt_succ 0

theorem connection_reduction_scope_bound (nextScope : Nat) (literal selected : ConnFOLit σ.scoped)
    (path : ConnFOClause σ.scoped) (rest : ConnFOAgenda σ.scoped) (substitution : Subst σ.scoped) (fuel : Nat)
    (bounded : ConnectionAgendaScopesBelow nextScope (⟨literal, path⟩ :: rest))
    (member : selected ∈ path) (accepted : unifyComplementLit? fuel literal selected = some substitution) :
    ConnectionAgendaScopesBelow nextScope (substitution.applyConnFOAgenda rest) := by
  apply connection_substitution_preserves_agenda_scope nextScope substitution
    (connection_unifier_preserves_scope nextScope literal selected substitution fuel accepted
      (bounded ⟨literal, path⟩ (by simp) literal (by simp))
      (bounded ⟨literal, path⟩ (by simp) selected (List.mem_cons_of_mem _ member))) rest
  intro goal present old onGoal
  exact bounded goal (List.mem_cons_of_mem _ present) old onGoal

theorem connection_extension_scope_bound (clauses : ConnFOCNF σ) (nextScope : Nat)
    (literal selected : ConnFOLit σ.scoped) (path clause : ConnFOClause σ.scoped)
    (rest : ConnFOAgenda σ.scoped) (substitution : Subst σ.scoped) (fuel : Nat)
    (bounded : ConnectionAgendaScopesBelow nextScope (⟨literal, path⟩ :: rest))
    (copied : clause ∈ connFOMatrixAtScope clauses nextScope) (member : selected ∈ clause)
    (accepted : unifyComplementLit? fuel literal selected = some substitution) :
    ConnectionAgendaScopesBelow (nextScope + 1)
      (substitution.applyConnFOAgenda (connectionGoals (clause.erase selected) (literal :: path) ++ rest)) := by
  have copyBound := connection_scoped_clause_below clauses nextScope (nextScope + 1)
    (Nat.lt_succ_self _) clause copied
  have priorBound : ConnectionAgendaScopesBelow (nextScope + 1) (⟨literal, path⟩ :: rest) := by
    intro goal present old onGoal name occurs
    exact Nat.lt_trans (bounded goal present old onGoal name occurs) (Nat.lt_succ_self _)
  apply connection_substitution_preserves_agenda_scope (nextScope + 1) substitution
    (connection_unifier_preserves_scope (nextScope + 1) literal selected substitution fuel accepted
      (priorBound ⟨literal, path⟩ (by simp) literal (by simp)) (copyBound selected member))
  intro goal present old onGoal
  rcases List.mem_append.mp present with child | previous
  · obtain ⟨childLiteral, onClause, rfl⟩ := List.mem_map.mp child
    rcases List.mem_cons.mp onGoal with rfl | ancestor
    · exact copyBound old (List.mem_of_mem_erase onClause)
    · exact priorBound ⟨literal, path⟩ (by simp) old ancestor
  · exact priorBound goal (List.mem_cons_of_mem _ previous) old onGoal

/-- The exact activation counter choices made by clause-source replay.
Reduction does not allocate a clause; extension does. -/
def connectionActivationScopes (nextScope : Nat) : FOProofTrace σ → List Nat
  | [] => []
  | .step_reduce _ :: rest => connectionActivationScopes nextScope rest
  | .step_extend _ _ :: rest => nextScope :: connectionActivationScopes (nextScope + 1) rest

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem connection_activation_scope_lower_bound :
    ∀ (trace : FOProofTrace σ) (nextScope scope : Nat),
      scope ∈ connectionActivationScopes nextScope trace → nextScope ≤ scope
  | [], _, _, member => by cases member
  | .step_reduce _ :: rest, nextScope, scope, member =>
      connection_activation_scope_lower_bound rest nextScope scope member
  | .step_extend _ _ :: rest, nextScope, scope, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ _) (connection_activation_scope_lower_bound rest (nextScope + 1) scope later)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem connection_activation_scopes_increase :
    ∀ (trace : FOProofTrace σ) (nextScope : Nat),
      (connectionActivationScopes nextScope trace).Pairwise (· < ·)
  | [], _ => .nil
  | .step_reduce _ :: rest, nextScope => connection_activation_scopes_increase rest nextScope
  | .step_extend _ _ :: rest, nextScope =>
      List.pairwise_cons.mpr ⟨fun scope member =>
        connection_activation_scope_lower_bound rest (nextScope + 1) scope member,
        connection_activation_scopes_increase rest (nextScope + 1)⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem connection_activation_scopes_are_never_reused (trace : FOProofTrace σ) (nextScope : Nat) :
    (connectionActivationScopes nextScope trace).Nodup :=
  (connection_activation_scopes_increase trace nextScope).imp (fun smaller => Nat.ne_of_lt smaller)

end

end Mettapedia.Logic.LP
