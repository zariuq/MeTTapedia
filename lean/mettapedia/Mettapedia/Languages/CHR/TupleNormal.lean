import Mettapedia.Languages.CHR.Admission
import Mettapedia.Languages.CHR.Operational

/-! Tuple normal form. A term may carry a tuple of values either as one
value or as the tuple of those values' terms; both denote the same data.
The normal form writes every tuple as a term tuple. Normalizing keeps each
term's variables and instantiations, is idempotent, and keeps admission. A
guard over normalized terms evaluates as before, up to the normalized term
named by an `uninstantiated` fault. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.TupleNormal

mutual
  /-- The term a value reads back as: tuples become term tuples. -/
  def normalValue : Value → Term
    | .integer number => .value (.integer number)
    | .atom name => .value (.atom name)
    | .tuple fields => .tuple (normalValues fields)
  def normalValues : List Value → List Term
    | [] => []
    | first :: rest => normalValue first :: normalValues rest
end

mutual
  /-- Tuple normal form of a term. -/
  def normalTerm : Term → Term
    | .value datum => normalValue datum
    | .var index => .var index
    | .tuple fields => .tuple (normalTerms fields)
  def normalTerms : List Term → List Term
    | [] => []
    | first :: rest => normalTerm first :: normalTerms rest
end

def normalHead (head : Head) : Head := ⟨head.name, normalTerms head.arguments⟩

def normalGuard : Guard → Guard
  | .identical left right => .identical (normalTerm left) (normalTerm right)
  | .distinct left right => .distinct (normalTerm left) (normalTerm right)
  | .compare comparison left right => .compare comparison left right

def normalGoal : Goal → Goal
  | .tell head => .tell (normalHead head)
  | other => other

def normalRule (rule : Rule) : Rule :=
  ⟨rule.name, rule.kept.map normalHead, rule.removed.map normalHead, rule.guards.map normalGuard,
    rule.body.map normalGoal⟩

def normalProgram (program : Program) : Program := ⟨program.declarations, program.rules.map normalRule⟩

/-- The fault a normalized guard or goal reports. -/
def normalFault : ArithmeticFault → ArithmeticFault
  | .uninstantiated term => .uninstantiated (normalTerm term)
  | other => other

theorem normalValues_eq : ∀ data : List Value, normalValues data = data.map normalValue
  | [] => rfl
  | first :: rest => by simp [normalValues, normalValues_eq rest]

theorem normalTerms_eq : ∀ terms : List Term, normalTerms terms = terms.map normalTerm
  | [] => rfl
  | first :: rest => by simp [normalTerms, normalTerms_eq rest]

theorem normalTerms_length (terms : List Term) : (normalTerms terms).length = terms.length := by
  simp [normalTerms_eq]

/-! ## Variables -/

mutual
  theorem normalValue_variables : ∀ datum : Value, (normalValue datum).variables = []
    | .integer _ => by simp [normalValue, Term.variables]
    | .atom _ => by simp [normalValue, Term.variables]
    | .tuple fields => by simp [normalValue, Term.variables, normalValues_variables fields]
  theorem normalValues_variables : ∀ data : List Value, (normalValues data).flatMap Term.variables = []
    | [] => rfl
    | first :: rest => by simp [normalValues, normalValue_variables first, normalValues_variables rest]
end

mutual
  theorem normalTerm_variables : ∀ term : Term, (normalTerm term).variables = term.variables
    | .value datum => by simp [normalTerm, normalValue_variables datum, Term.variables]
    | .var _ => by simp [normalTerm]
    | .tuple fields => by simp [normalTerm, Term.variables, normalTerms_variables fields]
  theorem normalTerms_variables : ∀ terms : List Term,
      (normalTerms terms).flatMap Term.variables = terms.flatMap Term.variables
    | [] => rfl
    | first :: rest => by simp [normalTerms, normalTerm_variables first, normalTerms_variables rest]
end

theorem normalHead_variables (head : Head) : (normalHead head).variables = head.variables := by
  simp [normalHead, Head.variables, normalTerms_variables]

theorem normalGuard_variables (guard : Guard) : (normalGuard guard).variables = guard.variables := by
  cases guard <;> simp [normalGuard, Guard.variables, normalTerm_variables]

theorem normalRule_heads (rule : Rule) : (normalRule rule).heads = rule.heads.map normalHead := by
  simp [normalRule, Rule.heads]

theorem normalRule_variables (rule : Rule) : (normalRule rule).variables = rule.variables := by
  simp only [Rule.variables, normalRule_heads, List.flatMap_map, normalHead_variables]

/-! ## Instantiation -/

mutual
  theorem normalValue_instantiate (environment : Environment) : ∀ datum : Value,
      (normalValue datum).instantiate environment = some datum
    | .integer _ => by simp [normalValue, Term.instantiate]
    | .atom _ => by simp [normalValue, Term.instantiate]
    | .tuple fields => by
      simp only [normalValue, Term.instantiate, normalValues_instantiate environment fields]
      rfl
  theorem normalValues_instantiate (environment : Environment) : ∀ data : List Value,
      (normalValues data).mapM (Term.instantiate environment) = some data
    | [] => rfl
    | first :: rest => by
      simp only [normalValues, List.mapM_cons, normalValue_instantiate environment first,
        normalValues_instantiate environment rest]
      rfl
end

mutual
  theorem normalTerm_instantiate (environment : Environment) : ∀ term : Term,
      (normalTerm term).instantiate environment = term.instantiate environment
    | .value datum => by simp only [normalTerm, normalValue_instantiate environment datum, Term.instantiate]
    | .var _ => by simp [normalTerm]
    | .tuple fields => by simp only [normalTerm, Term.instantiate, normalTerms_instantiate environment fields]
  theorem normalTerms_instantiate (environment : Environment) : ∀ terms : List Term,
      (normalTerms terms).mapM (Term.instantiate environment) = terms.mapM (Term.instantiate environment)
    | [] => rfl
    | first :: rest => by
      simp only [normalTerms, List.mapM_cons, normalTerm_instantiate environment first,
        normalTerms_instantiate environment rest]
end

theorem normalHead_instantiate (environment : Environment) (head : Head) :
    (normalHead head).instantiate environment = head.instantiate environment := by
  simp only [Head.instantiate, normalHead, normalTerms_instantiate]

/-! ## Idempotence -/

mutual
  theorem normalTerm_normalValue : ∀ datum : Value, normalTerm (normalValue datum) = normalValue datum
    | .integer _ => by simp [normalValue, normalTerm]
    | .atom _ => by simp [normalValue, normalTerm]
    | .tuple fields => by simp [normalValue, normalTerm, normalTerms_normalValues fields]
  theorem normalTerms_normalValues : ∀ data : List Value, normalTerms (normalValues data) = normalValues data
    | [] => rfl
    | first :: rest => by simp [normalValues, normalTerms, normalTerm_normalValue first, normalTerms_normalValues rest]
end

mutual
  theorem normalTerm_idem : ∀ term : Term, normalTerm (normalTerm term) = normalTerm term
    | .value datum => by simp [normalTerm, normalTerm_normalValue datum]
    | .var _ => by simp [normalTerm]
    | .tuple fields => by simp [normalTerm, normalTerms_idem fields]
  theorem normalTerms_idem : ∀ terms : List Term, normalTerms (normalTerms terms) = normalTerms terms
    | [] => rfl
    | first :: rest => by simp [normalTerms, normalTerm_idem first, normalTerms_idem rest]
end

theorem normalHead_idem (head : Head) : normalHead (normalHead head) = normalHead head := by
  simp [normalHead, normalTerms_idem]

theorem normalGuard_idem (guard : Guard) : normalGuard (normalGuard guard) = normalGuard guard := by
  cases guard <;> simp [normalGuard, normalTerm_idem]

theorem normalGoal_idem (goal : Goal) : normalGoal (normalGoal goal) = normalGoal goal := by
  cases goal <;> simp [normalGoal, normalHead_idem]

theorem normalRule_idem (rule : Rule) : normalRule (normalRule rule) = normalRule rule := by
  simp [normalRule, Function.comp_def, normalHead_idem, normalGuard_idem, normalGoal_idem]

theorem normalProgram_idem (program : Program) : normalProgram (normalProgram program) = normalProgram program := by
  simp [normalProgram, Function.comp_def, normalRule_idem]

/-! ## Guards -/

theorem intExpr_fault (environment : Environment) :
    ∀ (expression : IntExpr) (reason : ArithmeticFault),
      expression.eval environment = .error reason → normalFault reason = reason
  | .literal _, reason, evaluated => by simp [IntExpr.eval] at evaluated
  | .index index, reason, evaluated => by
    simp only [IntExpr.eval] at evaluated
    split at evaluated
    · cases evaluated
      rfl
    · cases evaluated
    · cases evaluated
      rfl
  | .operation operator left right, reason, evaluated => by
    simp only [IntExpr.eval, bind, Except.bind] at evaluated
    cases leftValue : left.eval environment with
    | error leftReason =>
      rw [leftValue] at evaluated
      cases evaluated
      exact intExpr_fault environment left reason leftValue
    | ok leftNumber =>
      rw [leftValue] at evaluated
      cases rightValue : right.eval environment with
      | error rightReason =>
        rw [rightValue] at evaluated
        cases evaluated
        exact intExpr_fault environment right reason rightValue
      | ok rightNumber =>
        rw [rightValue] at evaluated
        cases operator <;> simp only [IntOperator.eval] at evaluated <;>
          first
          | cases evaluated
          | (split at evaluated <;> cases evaluated; rfl)

theorem mapError_fixed {α : Type} (computation : Except ArithmeticFault α)
    (fixed : ∀ reason, computation = .error reason → normalFault reason = reason) :
    computation.mapError normalFault = computation := by
  cases computed : computation with
  | error reason => simp [Except.mapError, fixed reason computed]
  | ok value => rfl

theorem normalGuard_eval (environment : Environment) (guard : Guard) :
    (normalGuard guard).eval environment = (guard.eval environment).mapError normalFault := by
  cases guard with
  | identical left right =>
    simp only [normalGuard, Guard.eval, normalTerm_instantiate]
    cases left.instantiate environment <;> cases right.instantiate environment <;> rfl
  | distinct left right =>
    simp only [normalGuard, Guard.eval, normalTerm_instantiate]
    cases left.instantiate environment <;> cases right.instantiate environment <;> rfl
  | compare comparison left right =>
    simp only [normalGuard]
    refine (mapError_fixed _ fun reason evaluated => ?_).symm
    simp only [Guard.eval, bind, Except.bind] at evaluated
    cases leftValue : left.eval environment with
    | error leftReason =>
      rw [leftValue] at evaluated
      cases evaluated
      exact intExpr_fault environment left reason leftValue
    | ok leftNumber =>
      rw [leftValue] at evaluated
      cases rightValue : right.eval environment with
      | error rightReason =>
        rw [rightValue] at evaluated
        cases evaluated
        exact intExpr_fault environment right reason rightValue
      | ok rightNumber =>
        rw [rightValue] at evaluated
        cases evaluated

theorem normalGuards_eval (environment : Environment) : ∀ guards : List Guard,
    guardsEval environment (guards.map normalGuard) = (guardsEval environment guards).mapError normalFault
  | [] => rfl
  | guard :: guards => by
    simp only [List.map_cons, guardsEval, normalGuard_eval, bind, Except.bind]
    cases guard.eval environment with
    | error reason => rfl
    | ok holds =>
      cases holds
      · rfl
      · exact normalGuards_eval environment guards

/-! ## Admission -/

theorem declared_normalHead (program : Program) (head : Head) :
    Admission.declared program (normalHead head) = Admission.declared program head := by
  simp [Admission.declared, normalHead, normalTerms_length]

theorem goalsDiagnostic_normal (program : Program) (rule : Nat) :
    ∀ (bound : List Nat) (goals : List Goal),
      (Admission.goalsDiagnostic program rule bound (goals.map normalGoal)).isNone =
        (Admission.goalsDiagnostic program rule bound goals).isNone
  | _, [] => rfl
  | bound, goal :: rest => by
    cases goal with
    | tell head =>
      simp only [List.map_cons, normalGoal, Admission.goalsDiagnostic, declared_normalHead, normalHead_variables]
      split
      · rfl
      · split
        · rfl
        · exact goalsDiagnostic_normal program rule bound rest
    | assign index expression =>
      simp only [List.map_cons, normalGoal, Admission.goalsDiagnostic]
      split
      · rfl
      · exact goalsDiagnostic_normal program rule (index :: bound) rest
    | fail =>
      simp only [List.map_cons, normalGoal, Admission.goalsDiagnostic]
      exact goalsDiagnostic_normal program rule bound rest

theorem find?_map_isSome {α β : Type} (convert : α → β) (test : β → Bool) (items : List α) :
    ((items.map convert).find? test).isSome = (items.find? (test ∘ convert)).isSome := by
  rw [List.find?_map]
  cases items.find? (test ∘ convert) <;> rfl

theorem ruleDiagnostic_normal (program : Program) (index : Nat) (rule : Rule) :
    (Admission.ruleDiagnostic program index (normalRule rule)).isNone =
      (Admission.ruleDiagnostic program index rule).isNone := by
  have heads : (normalRule rule).heads.find? (fun head => !Admission.declared program head) =
      (rule.heads.find? fun head => !Admission.declared program head).map normalHead := by
    rw [normalRule_heads, List.find?_map]
    congr 2
    funext head
    simp [declared_normalHead]
  have guards : (normalRule rule).guards.find?
        (fun guard => !Admission.available (normalRule rule).variables guard.variables) =
      (rule.guards.find? fun guard => !Admission.available rule.variables guard.variables).map normalGuard := by
    simp only [normalRule_variables]
    simp only [normalRule]
    rw [List.find?_map]
    congr 2
    funext guard
    simp [normalGuard_variables]
  have empty : (normalRule rule).heads.isEmpty = rule.heads.isEmpty := by
    simp [normalRule_heads]
  unfold Admission.ruleDiagnostic
  rw [empty, heads, guards, normalRule_variables]
  split
  · rfl
  · cases rule.heads.find? (fun head => !Admission.declared program head) with
    | some head => rfl
    | none =>
      cases rule.guards.find? (fun guard => !Admission.available rule.variables guard.variables) with
      | some guard => rfl
      | none => exact goalsDiagnostic_normal program index rule.variables rule.body

theorem declared_same {first second : Program} (same : first.declarations = second.declarations)
    (head : Head) : Admission.declared first head = Admission.declared second head := by
  simp [Admission.declared, same]

theorem goalsDiagnostic_same {first second : Program} (same : first.declarations = second.declarations)
    (rule : Nat) : ∀ (bound : List Nat) (goals : List Goal),
      Admission.goalsDiagnostic first rule bound goals = Admission.goalsDiagnostic second rule bound goals
  | _, [] => rfl
  | bound, goal :: rest => by
    cases goal <;> simp only [Admission.goalsDiagnostic, declared_same same, goalsDiagnostic_same same rule]

theorem ruleDiagnostic_same {first second : Program} (same : first.declarations = second.declarations)
    (index : Nat) (rule : Rule) :
    Admission.ruleDiagnostic first index rule = Admission.ruleDiagnostic second index rule := by
  simp only [Admission.ruleDiagnostic, declared_same same, goalsDiagnostic_same same]

theorem diagnose_normal (program : Program) :
    (Admission.diagnose (normalProgram program)).isNone = (Admission.diagnose program).isNone := by
  have same : (normalProgram program).declarations = program.declarations := rfl
  have zipped : (normalProgram program).rules.zipIdx =
      program.rules.zipIdx.map fun pair => (normalRule pair.1, pair.2) := by
    simp [normalProgram, List.zipIdx_map]
  unfold Admission.diagnose
  rw [same, zipped, List.findSome?_map]
  simp only [Function.comp_def, ruleDiagnostic_same same]
  split
  · rfl
  · rw [Bool.eq_iff_iff, Option.isNone_iff_eq_none, Option.isNone_iff_eq_none, List.findSome?_eq_none_iff,
      List.findSome?_eq_none_iff]
    constructor
    · intro every pair member
      have := every pair member
      rw [← Option.isNone_iff_eq_none] at this ⊢
      rw [← ruleDiagnostic_normal]
      exact this
    · intro every pair member
      have := every pair member
      rw [← Option.isNone_iff_eq_none] at this ⊢
      rw [ruleDiagnostic_normal]
      exact this

/-- A normalized program is admitted exactly when the program is. -/
theorem diagnose_normal_none (program : Program) :
    Admission.diagnose (normalProgram program) = none ↔ Admission.diagnose program = none := by
  rw [← Option.isNone_iff_eq_none, ← Option.isNone_iff_eq_none, diagnose_normal]

/-! Examples: a value tuple and its term tuple share one normal form; a
variable stays a variable. -/

example : normalTerm (.value (.tuple [.integer 1, .atom "a"])) =
    normalTerm (.tuple [.value (.integer 1), .value (.atom "a")]) := by
  simp [normalTerm, normalValue, normalValues, normalTerms]

example : normalTerm (.tuple [.var 0, .value (.tuple [])]) = .tuple [.var 0, .tuple []] := by
  simp [normalTerm, normalValue, normalValues, normalTerms]

/-- Normal form is not the identity: a value tuple changes shape. -/
example : normalTerm (.value (.tuple [])) ≠ .value (.tuple []) := by
  simp [normalTerm, normalValue, normalValues]

#print axioms normalTerm_instantiate
#print axioms normalTerm_idem
#print axioms normalGuards_eval
#print axioms diagnose_normal_none

end Mettapedia.Languages.CHR.TupleNormal
