import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.GraphRelations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Evaluator

/-!
# Executing root rules with finite relation answers

A program is a list of schemas. Each premise names an executable built-in relation,
supplies arguments fixed by the matches so far, and matches a returned row.
The same matcher handles the initial row, repeated variables, and the
bindings introduced by all the previous premises. Successor enumeration
preserves the list order of rules and of the built-in relation's answers.

The proof relates this evaluation to the relational Transform rule. Range
checks ensure the algorithm can compute its arguments and resulting row
from the matches it actually has. A separately declared built-in relation supplies
a finite answer list on the given arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm inst toTerm inst_congr agree_of_inst_eq
  lift applyTerm_lift applyTerm_toTerm inst_toTerm)
open RuleSyntax.Machines (rowRule row_of_singleton)
open Step.Bridges.Machines.Table (groundAssignment inst_groundAssignment)

namespace Executable

abbrev Builtins := ℕ → List Expr → List Expr

def Builtins.relates (builtins : Builtins) : Relations :=
  fun name arguments value => value ∈ builtins name arguments

structure Schema where
  left : Tm
  conditions : List (Condition ℕ Tm)
  right : Tm

def Schema.rule (schema : Schema) : RuleWithCondition ℕ Tm :=
  ⟨rowRule schema.left schema.right, schema.conditions⟩

abbrev Matches := List (Tm × Expr)

def Satisfies (matchedRows : Matches) (assignment : ℕ → Expr) : Prop :=
  ∀ p ∈ matchedRows, inst assignment p.1 = p.2

private def equations (matchedRows : Matches) : List (Tm × Tm) :=
  matchedRows.map fun (pattern, value) => (pattern, toTerm value)

/-- Subjects are ground rows, so unification can bind only variables of the
patterns. This avoids computing a rigid-variable set for the subjects. -/
def findAssignment (matchedRows : Matches) : Option (ℕ → Expr) :=
  (unifyTotal (equations matchedRows)).map groundAssignment

theorem findAssignment_sound {matchedRows : Matches} {assignment : ℕ → Expr}
    (found : findAssignment matchedRows = some assignment) : Satisfies matchedRows assignment := by
  obtain ⟨substitution, matched, rfl⟩ := Option.map_eq_some_iff.mp found
  intro p member
  have hit := unifyTotal_sound _ substitution matched
    (p.1, toTerm p.2) (List.mem_map.mpr ⟨p, member, rfl⟩)
  change substitution.applyTerm p.1 = substitution.applyTerm (toTerm p.2) at hit
  rw [applyTerm_toTerm] at hit
  rw [inst_groundAssignment, hit, inst_toTerm]

theorem findAssignment_complete {matchedRows : Matches} {assignment : ℕ → Expr}
    (holds : Satisfies matchedRows assignment) : ∃ other, findAssignment matchedRows = some other := by
  have solvable : ∃ substitution, Unifies substitution (equations matchedRows) := by
    refine ⟨lift assignment, ?_⟩
    intro p member
    obtain ⟨source, found, rfl⟩ := List.mem_map.mp member
    rw [applyTerm_lift, holds source found, applyTerm_toTerm]
  obtain ⟨substitution, accepted⟩ := unifyTotal_complete solvable
  exact ⟨groundAssignment substitution, by simp [findAssignment, accepted]⟩

/-- The term only mentions variables fixed by the listed patterns. -/
def BoundBy (patterns : List Tm) (term : Tm) : Prop :=
  ∀ x ∈ term.freeVars, ∃ pattern ∈ patterns, x ∈ pattern.freeVars

instance (patterns : List Tm) (term : Tm) : Decidable (BoundBy patterns term) := by
  unfold BoundBy
  infer_instance

theorem inst_eq_of_bound {matchedRows : Matches} {assignment other : ℕ → Expr}
    (holds : Satisfies matchedRows assignment) (holds' : Satisfies matchedRows other)
    {term : Tm} (bound : BoundBy (matchedRows.map Prod.fst) term) :
    inst assignment term = inst other term := by
  apply inst_congr
  intro x used
  obtain ⟨p, available, hasVar⟩ := bound x used
  obtain ⟨m, member, rfl⟩ := List.mem_map.mp available
  exact agree_of_inst_eq _ ((holds m member).trans (holds' m member).symm) x hasVar

/-- Sequential mode correctness and range restriction of the result. -/
def Ready (right : Tm) (available : List Tm) (conditions : List (Condition ℕ Tm)) : Prop :=
  RuleWithCondition.WellModedAfter available conditions ∧
    BoundBy (available ++ conditions.map Condition.value) right

instance (right : Tm) (available : List Tm) (conditions : List (Condition ℕ Tm)) :
    Decidable (Ready right available conditions) := by
  unfold Ready
  infer_instance

/-- Evaluate each condition on the current bindings. An answer supplies the
next match constraint and therefore cannot overwrite previous bindings. -/
def returns (builtins : Builtins) (right : Tm) :
    List (Condition ℕ Tm) → Matches → List Expr
  | [], matchedRows => ((findAssignment matchedRows).map fun assignment => inst assignment right).toList
  | c :: rest, matchedRows =>
      match findAssignment matchedRows with
      | none => []
      | some assignment =>
          (builtins c.name (c.arguments.map (inst assignment))).flatMap fun answer =>
            returns builtins right rest (matchedRows ++ [(c.value, answer)])

private theorem mem_returns (builtins : Builtins) (right : Tm) :
    ∀ (conditions : List (Condition ℕ Tm)) (matchedRows : Matches) (result : Expr),
      Ready right (matchedRows.map Prod.fst) conditions →
      (result ∈ returns builtins right conditions matchedRows ↔
        ∃ assignment : ℕ → Expr, Satisfies matchedRows assignment ∧
          (∀ c ∈ conditions, builtins.relates c.name (c.arguments.map (inst assignment))
            (inst assignment c.value)) ∧ inst assignment right = result) := by
  intro conditions
  induction conditions with
  | nil =>
      intro matchedRows result ready
      have outputBound : BoundBy (matchedRows.map Prod.fst) right := by simpa using ready.2
      constructor
      · intro member
        have found := Option.mem_toList.mp member
        obtain ⟨assignment, accepted, rfl⟩ := Option.map_eq_some_iff.mp found
        exact ⟨assignment, findAssignment_sound accepted, by simp, rfl⟩
      · rintro ⟨assignment, holds, _, output⟩
        obtain ⟨other, found⟩ := findAssignment_complete holds
        have same := inst_eq_of_bound (findAssignment_sound found) holds outputBound
        simp [returns, found, same, output]
  | cons c rest ih =>
      intro matchedRows result ready
      obtain ⟨modes, outputBound⟩ := ready
      obtain ⟨argsBound, restBound⟩ := modes
      have readyRest (answer : Expr) : Ready right ((matchedRows ++ [(c.value, answer)]).map Prod.fst) rest := by
        refine ⟨by simpa using restBound, ?_⟩
        simpa [List.map_cons, List.append_assoc] using outputBound
      have agree {a b : ℕ → Expr} (holds : Satisfies matchedRows a) (holds' : Satisfies matchedRows b) :
          c.arguments.map (inst a) = c.arguments.map (inst b) :=
        List.map_congr_left fun arg member => inst_eq_of_bound holds holds' (argsBound arg member)
      constructor
      · intro member
        cases found : findAssignment matchedRows with
        | none => simp [returns, found] at member
        | some first =>
            simp only [returns, found, List.mem_flatMap] at member
            obtain ⟨answer, allowed, more⟩ := member
            obtain ⟨assignment, holds, conditions, output⟩ :=
              (ih (matchedRows ++ [(c.value, answer)]) result (readyRest _)).mp more
            have headHolds : Satisfies matchedRows assignment := fun p h =>
              holds p (List.mem_append_left _ h)
            have equal := holds (c.value, answer) (List.mem_append_right _ (List.mem_singleton_self _))
            refine ⟨assignment, headHolds, ?_, output⟩
            intro condition member
            rcases List.mem_cons.mp member with rfl | later
            · unfold Builtins.relates
              change inst assignment condition.value = answer at equal
              rw [equal, ← agree (findAssignment_sound found) headHolds]
              exact allowed
            · exact conditions condition later
      · rintro ⟨assignment, holds, conditions, output⟩
        obtain ⟨first, found⟩ := findAssignment_complete holds
        simp only [returns, found, List.mem_flatMap]
        refine ⟨inst assignment c.value, ?_, ?_⟩
        · rw [agree (findAssignment_sound found) holds]
          exact conditions c (List.mem_cons_self ..)
        · apply (ih (matchedRows ++ [(c.value, inst assignment c.value)]) result (readyRest _)).mpr
          refine ⟨assignment, ?_, fun condition member =>
            conditions condition (List.mem_cons_of_mem _ member), output⟩
          intro p member
          rcases List.mem_append.mp member with earlier | new
          · exact holds p earlier
          · rw [List.mem_singleton.mp new]

def Schema.successors (builtins : Builtins) (schema : Schema) (source : Expr) : List Expr :=
  returns builtins schema.right schema.conditions [(schema.left, source)]

/-- **Every listed successor is exactly an admitted relational firing**, and
every admitted successor appears, when the arguments pass the range check. -/
theorem mem_successors_iff (builtins : Builtins) (schema : Schema)
    (ready : Ready schema.right [schema.left] schema.conditions) (source target : Expr) :
    target ∈ schema.successors builtins source ↔
      RelationStep builtins.relates schema.rule {source} {target} := by
  rw [Schema.successors, mem_returns _ _ _ _ _ ready]
  constructor
  · rintro ⟨assignment, holds, conditions, rfl⟩
    have input := holds (schema.left, source) (List.mem_singleton_self _)
    exact ⟨assignment, 0, by simpa [Schema.rule, rowRule] using input,
      by simp [Schema.rule, rowRule], by simp [Schema.rule, rowRule, Presentation.Schematic.equationsOf],
      conditions, by simp [Schema.rule, rowRule]⟩
  · rintro ⟨assignment, rest, split, _, _, conditions, output⟩
    have input : inst assignment schema.left = source ∧ rest = 0 := by
      simpa [Schema.rule, rowRule] using row_of_singleton split
    have result : inst assignment schema.right = target := by
      simpa [Schema.rule, rowRule, input.2] using output.symm
    refine ⟨assignment, ?_, conditions, result⟩
    intro p member
    rw [List.mem_singleton.mp member]
    exact input.1

def successors (builtins : Builtins) (program : List Schema) (source : Expr) : List Expr :=
  program.flatMap fun schema => schema.successors builtins source

theorem mem_program_successors (builtins : Builtins) (program : List Schema)
    (ready : ∀ schema ∈ program, Ready schema.right [schema.left] schema.conditions) (source target : Expr) :
    target ∈ successors builtins program source ↔
      ∃ schema ∈ program, RelationStep builtins.relates schema.rule {source} {target} := by
  simp only [successors, List.mem_flatMap]
  exact exists_congr fun schema => and_congr_right fun member =>
    mem_successors_iff builtins schema (ready schema member) source target

#print axioms mem_program_successors

end Executable
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
