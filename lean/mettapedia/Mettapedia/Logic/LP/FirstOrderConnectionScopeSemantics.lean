import Mettapedia.Logic.LP.FirstOrderConnectionScoped

/-!
# Scoped connection replay refutes independent first-order models

Changing only the variable carrier leaves the interpretation of every
authored function and relation unchanged. A source clause universally true
in a structure therefore remains true in each computed fresh scope. The
actual clause-source replay preserves the uniform true-agenda invariant,
so its accepted scoped proofs exclude every nonempty source structure.
-/

namespace Mettapedia.Logic.LP

noncomputable section

open FirstOrderBridge

variable {σ : LPSignature} {Model : Type*}

@[instance_reducible]
def connectionScopedStructure [(language σ).Structure Model] : (language σ.scoped).Structure Model where
  funMap
    | .constant symbol, arguments =>
        FirstOrder.Language.Structure.funMap (L := language σ) (FunctionSymbol.constant (σ := σ) symbol) arguments
    | .function symbol, arguments =>
        FirstOrder.Language.Structure.funMap (L := language σ) (FunctionSymbol.function (σ := σ) symbol) arguments
  RelMap
    | .relation symbol, arguments =>
        FirstOrder.Language.Structure.RelMap (L := language σ) (RelationSymbol.relation (σ := σ) symbol) arguments

section SourceStructure

variable [(language σ).Structure Model]

theorem realizeTerm_at_connection_scope (scope : Nat) (assignment : ScopedVar σ.vars → Model)
    (term : Term σ) :
    @realizeTerm σ.scoped Model connectionScopedStructure assignment (term.atScope scope) =
      realizeTerm (fun name => assignment (ScopedVar.at scope name)) term := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app symbol arguments earlier =>
      change FirstOrder.Language.Structure.funMap (L := language σ) (.function symbol)
        (fun position => @realizeTerm σ.scoped Model connectionScopedStructure assignment
          ((arguments position).atScope scope)) = _
      exact congrArg (FirstOrder.Language.Structure.funMap (L := language σ) (.function symbol))
        (funext earlier)

theorem realizeAtom_at_connection_scope (scope : Nat) (assignment : ScopedVar σ.vars → Model)
    (atom : Atom σ) :
    @realizeAtom σ.scoped Model connectionScopedStructure assignment (atom.atScope scope) ↔
      realizeAtom (fun name => assignment (ScopedVar.at scope name)) atom := by
  simp only [realizeAtom, Atom.atScope, Atom.renameVars]
  change FirstOrder.Language.Structure.RelMap (L := language σ) (.relation atom.symbol)
    (fun position => @realizeTerm σ.scoped Model connectionScopedStructure assignment
      ((atom.args position).atScope scope)) ↔ _
  simp only [realizeTerm_at_connection_scope]

theorem literal_at_connection_scope (scope : Nat) (assignment : ScopedVar σ.vars → Model)
    (literal : ConnFOLit σ) :
    @ConnFOLit.Holds σ.scoped Model connectionScopedStructure assignment (literal.atScope scope) ↔
      literal.Holds (fun name => assignment (ScopedVar.at scope name)) := by
  cases literal <;> simp only [ConnFOLit.atScope, ConnFOLit.Holds, realizeAtom_at_connection_scope]

theorem matrix_model_at_connection_scope (clauses : ConnFOCNF σ) (model : ConnFOModels clauses Model)
    (scope : Nat) : @ConnFOModels σ.scoped (connFOMatrixAtScope clauses scope) Model connectionScopedStructure := by
  intro clause member assignment
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨literal, onClause, trueLiteral⟩ := model source present (fun name => assignment (ScopedVar.at scope name))
  exact ⟨literal.atScope scope, List.mem_map.mpr ⟨literal, onClause, rfl⟩,
    (literal_at_connection_scope scope assignment literal).mpr trueLiteral⟩

end SourceStructure

section RuntimeStructure

variable [(language σ).Structure Model] [Nonempty Model]
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

theorem replayFOClauseSource_excludes_uniform_true (source : Nat → ConnFOCNF σ)
    (models : ∀ scope, ConnFOModels (source scope) Model) (fuel : Nat) :
    ∀ (trace : FOProofTrace σ) (agenda : ConnFOAgenda σ) (nextScope : Nat),
      replayFOClauseSource source fuel nextScope agenda trace = true →
      ¬ (∀ assignment : σ.vars → Model, TrueFOConnectionAgenda assignment agenda)
  | [], agenda, _, checked, before => by
      have empty : agenda = [] := by simpa [replayFOClauseSource] using checked
      subst agenda
      let assignment : σ.vars → Model := fun _ => Classical.choice (inferInstance : Nonempty Model)
      obtain ⟨_, member, _⟩ := before assignment
      cases member
  | _ :: _, [], _, checked, _ => by simp [replayFOClauseSource] at checked
  | step :: steps, ⟨literal, path⟩ :: rest, nextScope, checked, before => by
      cases step with
      | step_reduce selected =>
          by_cases member : selected ∈ path
          · simp only [replayFOClauseSource, if_pos member] at checked
            cases unified : unifyComplementLit? fuel literal selected with
            | none => simp only [unified, Bool.false_eq_true] at checked
            | some substitution =>
                exact replayFOClauseSource_excludes_uniform_true source models fuel steps _ nextScope
                  (by simpa only [unified] using checked)
                  (uniform_true_fo_agenda_after_reduction fuel literal selected path rest substitution member unified before)
          · simp only [replayFOClauseSource, if_neg member, Bool.false_eq_true] at checked
      | step_extend clause selected =>
          by_cases member : clause ∈ source nextScope ∧ selected ∈ clause
          · simp only [replayFOClauseSource, if_pos member] at checked
            cases unified : unifyComplementLit? fuel literal selected with
            | none => simp only [unified, Bool.false_eq_true] at checked
            | some substitution =>
                exact replayFOClauseSource_excludes_uniform_true source models fuel steps _ (nextScope + 1)
                  (by simpa only [unified] using checked)
                  (uniform_true_fo_agenda_after_extension (source nextScope) (models nextScope) fuel literal selected path clause rest substitution member.1 unified before)
          · simp only [replayFOClauseSource, if_neg member, Bool.false_eq_true] at checked

end RuntimeStructure

theorem checkProofScopedFO_unsatisfiable [(language σ).Structure Model] [Nonempty Model]
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (clauses : ConnFOCNF σ) (fuel : Nat) (proof : FOProofObj σ.scoped)
    (checked : checkProofScopedFO clauses fuel proof = true) : ¬ ConnFOModels clauses Model := by
  intro model
  let : (language σ.scoped).Structure Model := connectionScopedStructure
  have parts : proof.root ∈ connFOMatrixAtScope clauses 0 ∧
      replayFOClauseSource (connFOMatrixAtScope clauses) fuel 1 (connectionGoals proof.root []) proof.trace = true := by
    simpa only [checkProofScopedFO, Bool.and_eq_true, decide_eq_true_eq] using checked
  apply replayFOClauseSource_excludes_uniform_true (connFOMatrixAtScope clauses)
    (matrix_model_at_connection_scope clauses model) fuel proof.trace _ 1 parts.2
  intro assignment
  obtain ⟨literal, member, trueLiteral⟩ := matrix_model_at_connection_scope clauses model 0 proof.root parts.1 assignment
  exact ⟨⟨literal, []⟩, List.mem_map.mpr ⟨literal, member, rfl⟩,
    trueLiteral, fun _ absent => False.elim (List.not_mem_nil absent)⟩

end

end Mettapedia.Logic.LP
