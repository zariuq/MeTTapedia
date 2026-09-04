import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics

/-!
# Evidence-bearing CNF for definitionally named Skolem FOF matrices

This module is the independent semantic authority for the CNF stage after
definitional naming.  It translates each full predicate equivalence to the
three standard clauses and adds one unit clause for the named root.  Generated
clauses retain the naming language's terms and predicate symbols; TPTP text is
a later serialization concern.

Truth constants remain explicit references in this semantic form.  Removing
them is a later equivalence-preserving simplification, not an implicit special
case in clause generation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfSemantics

open LO FirstOrder
open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics

/-- Logical complement of a truth constant or signed atom. -/
def negate {depth : Nat} : Reference depth -> Reference depth
  | .verum => .falsum
  | .falsum => .verum
  | .positive relation arguments => .negative relation arguments
  | .negative relation arguments => .positive relation arguments

theorem eval_negate_iff_not {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (reference : Reference depth) :
    evalReference target values (negate reference) <->
      Not (evalReference target values reference) := by
  classical
  cases reference <;> simp [negate, evalReference]

/-- Clauses are finite disjunctions of signed references. -/
abbrev Clause (depth : Nat) := List (Reference depth)

def evalClause {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain) : Clause depth -> Prop
  | [] => False
  | reference :: rest =>
      evalReference target values reference \/
        evalClause target values rest

def SatisfiesClauses {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (clauses : List (Clause depth)) : Prop :=
  forall clause, clause ∈ clauses -> evalClause target values clause

theorem satisfiesClauses_append_iff {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (left right : List (Clause depth)) :
    SatisfiesClauses target values (left ++ right) <->
      SatisfiesClauses target values left /\
        SatisfiesClauses target values right := by
  constructor
  · intro satisfied
    exact ⟨fun clause membership => satisfied clause (by simp [membership]),
      fun clause membership => satisfied clause (by simp [membership])⟩
  · rintro ⟨leftSatisfied, rightSatisfied⟩ clause membership
    rcases List.mem_append.mp membership with membership | membership
    · exact leftSatisfied clause membership
    · exact rightSatisfied clause membership

/-- The three-clause encoding of one full predicate equivalence. -/
def clausesForDefinition {depth : Nat}
    (definition : Definition depth) : List (Clause depth) :=
  let head := definedReference depth definition.id
  match definition.connective with
  | .and =>
      [[negate head, definition.left],
       [negate head, definition.right],
       [head, negate definition.left, negate definition.right]]
  | .or =>
      [[negate head, definition.left, definition.right],
       [head, negate definition.left],
       [head, negate definition.right]]

theorem clausesForDefinition_length {depth : Nat}
    (definition : Definition depth) :
    (clausesForDefinition definition).length = 3 := by
  cases definition with
  | mk id source connective left right => cases connective <;> rfl

/-- The clause encoding is exactly the definition's full equivalence. -/
theorem clausesForDefinition_satisfied_iff {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (definition : Definition depth) :
    SatisfiesClauses target values (clausesForDefinition definition) <->
      Definition.Satisfied target values definition := by
  classical
  cases definition with
  | mk id source connective left right =>
      cases connective <;>
        simp [clausesForDefinition, SatisfiesClauses, evalClause,
          Definition.Satisfied, Connective.holds,
          eval_negate_iff_not] <;>
        tauto

def clausesForDefinitions {depth : Nat} :
    List (Definition depth) -> List (Clause depth)
  | [] => []
  | definition :: rest =>
      clausesForDefinition definition ++ clausesForDefinitions rest

theorem clausesForDefinitions_length {depth : Nat}
    (definitions : List (Definition depth)) :
    (clausesForDefinitions definitions).length = 3 * definitions.length := by
  induction definitions with
  | nil => rfl
  | cons definition rest inductionHypothesis =>
      simp [clausesForDefinitions, clausesForDefinition_length,
        inductionHypothesis]
      omega

theorem clausesForDefinitions_satisfied_iff {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (definitions : List (Definition depth)) :
    SatisfiesClauses target values (clausesForDefinitions definitions) <->
      forall definition, definition ∈ definitions ->
        Definition.Satisfied target values definition := by
  induction definitions with
  | nil => simp [clausesForDefinitions, SatisfiesClauses]
  | cons definition rest inductionHypothesis =>
      rw [clausesForDefinitions, satisfiesClauses_append_iff,
        clausesForDefinition_satisfied_iff, inductionHypothesis]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨headSatisfied, restSatisfied⟩ candidate (rfl | membership)
        · exact headSatisfied
        · exact restSatisfied candidate membership
      · intro allSatisfied
        exact ⟨allSatisfied definition (by simp), fun candidate membership =>
          allSatisfied candidate (by simp [membership])⟩

/-- Definition clauses followed by a unit clause asserting the named root. -/
def clausesForOutput {depth : Nat} (output : Output depth) :
    List (Clause depth) :=
  clausesForDefinitions output.definitions ++ [[output.root]]

theorem clausesForOutput_length {depth : Nat} (output : Output depth) :
    (clausesForOutput output).length = 3 * output.definitions.length + 1 := by
  simp [clausesForOutput, clausesForDefinitions_length]

theorem clausesForOutput_satisfied_iff {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain) (output : Output depth) :
    SatisfiesClauses target values (clausesForOutput output) <->
      ((forall definition, definition ∈ output.definitions ->
          Definition.Satisfied target values definition) /\
        evalReference target values output.root) := by
  rw [clausesForOutput, satisfiesClauses_append_iff,
    clausesForDefinitions_satisfied_iff]
  simp [SatisfiesClauses, evalClause]

def Satisfiable {depth : Nat} (output : Output depth) : Prop :=
  exists (Domain : Type) (_ : Nonempty Domain)
      (model : TptpFofDefinitionalNamingSemantics.Model Domain),
    forall values : Fin depth -> Domain,
      SatisfiesClauses model.interpretation values (clausesForOutput output)

theorem outputSatisfiable_iff_cnfSatisfiable {depth : Nat}
    (output : Output depth) :
    TptpFofDefinitionalNamingSemantics.Satisfiable output <->
      Satisfiable output := by
  constructor
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    refine ⟨Domain, domainNonempty, model, ?_⟩
    intro values
    exact (clausesForOutput_satisfied_iff model.interpretation values output).2
      (satisfied values)
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    refine ⟨Domain, domainNonempty, model, ?_⟩
    intro values
    exact (clausesForOutput_satisfied_iff model.interpretation values output).1
      (satisfied values)

/-- The composed naming-plus-CNF transformation preserves satisfiability in
both directions. -/
theorem sourceSatisfiable_iff_cnfSatisfiable
    {depth : Nat} (source : TptpFofDefinitionalNamingSemantics.Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    TptpFofDefinitionalNamingSemantics.SourceSatisfiable source <->
      Satisfiable (nameFrom source quantifierFree frontier) := by
  exact (sourceSatisfiable_iff_namedSatisfiable source
    quantifierFree frontier).trans
      (outputSatisfiable_iff_cnfSatisfiable
        (nameFrom source quantifierFree frontier))

/-- Removing an explicit all-only prefix, naming its matrix, and generating
clauses preserves satisfiability in both directions. -/
theorem universallyClosedSourceSatisfiable_iff_cnfSatisfiable
    {depth : Nat}
    (source : TptpFofDefinitionalNamingSemantics.Source.Formula depth)
    (opened : TptpFofDefinitionalNamingSemantics.OpenedMatrix)
    (openedExact :
      TptpFofDefinitionalNamingSemantics.openUniversals? source = some opened)
    (frontier : Nat) :
    TptpFofDefinitionalNamingSemantics.SourceSatisfiable source <->
      Satisfiable
        (nameFrom opened.formula opened.quantifierFree frontier) := by
  exact
    (TptpFofDefinitionalNamingSemantics.sourceSatisfiable_iff_openedNamedSatisfiable
      source opened openedExact frontier).trans
      (outputSatisfiable_iff_cnfSatisfiable
        (nameFrom opened.formula opened.quantifierFree frontier))

/-! ## Positive and negative canaries -/

namespace Canary

abbrev source := TptpFofDefinitionalNamingSemantics.Canary.source
abbrev sourceQuantifierFree :=
  TptpFofDefinitionalNamingSemantics.Canary.source_quantifierFree

theorem nested_source_has_seven_clauses :
    (clausesForOutput
      (nameFrom source sourceQuantifierFree 7)).length = 7 := by
  rw [clausesForOutput_length]
  have idsExact :=
    TptpFofDefinitionalNamingSemantics.Canary.source_definition_ids_are_topological
  have definitionsLength :
      (nameFrom source sourceQuantifierFree 7).definitions.length = 2 := by
    have lengthsExact := congrArg List.length idsExact
    simpa [definitionIds] using lengthsExact
  rw [definitionsLength]

theorem nested_source_is_equisatisfiable_with_cnf :
    TptpFofDefinitionalNamingSemantics.SourceSatisfiable source <->
      Satisfiable (nameFrom source sourceQuantifierFree 7) :=
  sourceSatisfiable_iff_cnfSatisfiable source sourceQuantifierFree 7

theorem empty_clause_is_rejected {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain) :
    Not (evalClause target values []) := by
  simp [evalClause]

theorem true_unit_clause_is_accepted {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain) :
    evalClause target values [.verum] := by
  simp [evalClause, evalReference]

end Canary

#print axioms clausesForDefinition_satisfied_iff
#print axioms clausesForDefinitions_satisfied_iff
#print axioms clausesForOutput_satisfied_iff
#print axioms outputSatisfiable_iff_cnfSatisfiable
#print axioms sourceSatisfiable_iff_cnfSatisfiable
#print axioms universallyClosedSourceSatisfiable_iff_cnfSatisfiable
#print axioms Canary.empty_clause_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfSemantics
