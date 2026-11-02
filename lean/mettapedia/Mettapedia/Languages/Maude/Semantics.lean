import Mettapedia.Languages.Maude.Substitution
import Mathlib.Data.List.Forall2

/-! An independent rewriting-logic specification for M0. Axioms A are tied
to the selected operator declaration; conditional equations E are distinct
from rules R. Rule execution is modulo the symmetric equation theory, not a
single oriented normalization step. Termination, confluence and coherence
certificates are required separately for an executable realization. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

inductive AlgebraSchema (signature : Signature) : Term → Term → Prop where
  | associative {declaration : Operator} {first second third : Term} :
      declaration ∈ signature.operators → declaration.attributes.associative = true →
      AlgebraSchema signature
        (.app declaration.id [.app declaration.id [first, second], third])
        (.app declaration.id [first, .app declaration.id [second, third]])
  | commutative {declaration : Operator} {first second : Term} :
      declaration ∈ signature.operators → declaration.attributes.commutative = true →
      AlgebraSchema signature (.app declaration.id [first, second]) (.app declaration.id [second, first])
  | leftUnit {declaration : Operator} {unit term : Term} :
      declaration ∈ signature.operators → declaration.attributes.identity = some unit →
      AlgebraSchema signature (.app declaration.id [unit, term]) term
  | rightUnit {declaration : Operator} {unit term : Term} :
      declaration ∈ signature.operators → declaration.attributes.identity = some unit →
      AlgebraSchema signature (.app declaration.id [term, unit]) term

/-- An algebra schema may fire only within one sort. Checking only the
source would make the reverse identity law admit an ill-sorted context. -/
structure AlgebraStep (signature : Signature) (context : VariableContext) (sort : String)
    (source target : Term) : Prop where
  schema : AlgebraSchema signature source target
  source_sorted : HasSort signature context source sort
  target_sorted : HasSort signature context target sort

structure ArgumentContext (signature : Signature) (context : VariableContext) (hole result : String) where
  declaration : Operator
  declared : declaration ∈ signature.operators
  beforeSorts : List String
  afterSorts : List String
  before : List Term
  after : List Term
  argumentSorts : declaration.arguments = beforeSorts ++ hole :: afterSorts
  resultSort : declaration.result = result
  beforeTyped : List.Forall₂ (HasSort signature context) before beforeSorts
  afterTyped : List.Forall₂ (HasSort signature context) after afterSorts

def ArgumentContext.plug {signature : Signature} {context : VariableContext} {hole result : String}
    (frame : ArgumentContext signature context hole result) (term : Term) : Term :=
  .app frame.declaration.id (frame.before ++ term :: frame.after)

theorem ArgumentContext.plug_sorted {signature : Signature} {context : VariableContext} {hole result : String}
    (frame : ArgumentContext signature context hole result) {term : Term}
    (typed : HasSort signature context term hole) : HasSort signature context (frame.plug term) result := by
  have arguments : List.Forall₂ (HasSort signature context)
      (frame.before ++ term :: frame.after) frame.declaration.arguments := by
    rw [frame.argumentSorts]
    exact List.rel_append frame.beforeTyped (.cons typed frame.afterTyped)
  have constructed := HasSort.app frame.declared arguments
  simpa only [frame.resultSort, ArgumentContext.plug] using constructed

mutual
inductive Equivalent (theory : Theory) (context : VariableContext) : String → Term → Term → Prop where
  | refl {term : Term} {sort : String} : HasSort theory.signature context term sort → Equivalent theory context sort term term
  | symm {sort : String} {first second} :
      Equivalent theory context sort first second → Equivalent theory context sort second first
  | trans {sort : String} {first middle last} :
      Equivalent theory context sort first middle → Equivalent theory context sort middle last →
      Equivalent theory context sort first last
  | argument {hole sort : String} (frame : ArgumentContext theory.signature context hole sort) {first second : Term} :
      Equivalent theory context hole first second →
      Equivalent theory context sort (frame.plug first) (frame.plug second)
  | algebra {sort : String} {first second} :
      AlgebraStep theory.signature context sort first second → Equivalent theory context sort first second
  | equation {row : Row} {sort : String} (assignment : Valuation) :
      row ∈ theory.equations → row.check theory.signature = true →
      HasSort theory.signature row.usedContext row.left sort →
      HasSort theory.signature row.usedContext row.right sort →
      TypedValuation theory.signature context row.usedContext assignment →
      Conditions theory context assignment row.conditions →
      Equivalent theory context sort (row.left.substitute assignment) (row.right.substitute assignment)

inductive Conditions (theory : Theory) (context : VariableContext) : Valuation → List Condition → Prop where
  | nil (assignment : Valuation) : Conditions theory context assignment []
  | cons {assignment : Valuation} {condition : Condition} {rest : List Condition} {sort : String} :
      Equivalent theory context sort (condition.left.substitute assignment) (condition.right.substitute assignment) →
      Conditions theory context assignment rest → Conditions theory context assignment (condition :: rest)
end

inductive RawStep (theory : Theory) (context : VariableContext) : String → Term → Term → Prop where
  | rule {row : Row} {sort : String} (assignment : Valuation) :
      row ∈ theory.rules → row.check theory.signature = true →
      HasSort theory.signature row.usedContext row.left sort →
      HasSort theory.signature row.usedContext row.right sort →
      TypedValuation theory.signature context row.usedContext assignment →
      Conditions theory context assignment row.conditions →
      RawStep theory context sort (row.left.substitute assignment) (row.right.substitute assignment)
  | argument {hole sort : String} (frame : ArgumentContext theory.signature context hole sort) {first second : Term} :
      RawStep theory context hole first second → RawStep theory context sort (frame.plug first) (frame.plug second)

def Step (theory : Theory) (context : VariableContext) (sort : String) (source target : Term) : Prop :=
  ∃ redex contractum, Equivalent theory context sort source redex ∧ RawStep theory context sort redex contractum ∧
    Equivalent theory context sort contractum target

inductive Reaches (theory : Theory) (context : VariableContext) (sort : String) : Term → Term → Prop where
  | refl {term : Term} : HasSort theory.signature context term sort → Reaches theory context sort term term
  | next {source middle target} :
      Step theory context sort source middle → Reaches theory context sort middle target → Reaches theory context sort source target

theorem Equivalent.sorted {theory : Theory} {context : VariableContext} {sort : String} {source target : Term}
    (equivalent : Equivalent theory context sort source target) :
    HasSort theory.signature context source sort ∧ HasSort theory.signature context target sort := by
  refine Equivalent.rec
    (motive_1 := fun sort source target _ =>
      HasSort theory.signature context source sort ∧ HasSort theory.signature context target sort)
    (motive_2 := fun assignment conditions _ => ∀ condition ∈ conditions, ∃ sort,
      HasSort theory.signature context (condition.left.substitute assignment) sort ∧
      HasSort theory.signature context (condition.right.substitute assignment) sort)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro term sort typed
    exact ⟨typed, typed⟩
  · intro sort first second _ ih
    exact ih.symm
  · intro sort first middle last _ _ firstIH lastIH
    exact ⟨firstIH.1, lastIH.2⟩
  · intro hole sort frame first second _ ih
    exact ⟨frame.plug_sorted ih.1, frame.plug_sorted ih.2⟩
  · intro sort first second step
    exact ⟨step.source_sorted, step.target_sorted⟩
  · intro row sort assignment _ _ first last typed _ _
    exact ⟨substitute_preserves_sort assignment typed first, substitute_preserves_sort assignment typed last⟩
  · intro assignment condition impossible
    cases impossible
  · intro assignment condition rest sort _ _ firstIH restIH actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨sort, firstIH⟩
    · exact restIH actual member

theorem RawStep.sorted {theory : Theory} {context : VariableContext} {sort : String} {source target : Term}
    (step : RawStep theory context sort source target) :
    HasSort theory.signature context source sort ∧ HasSort theory.signature context target sort := by
  induction step with
  | rule assignment _ _ first last typed _ =>
      exact ⟨substitute_preserves_sort assignment typed first, substitute_preserves_sort assignment typed last⟩
  | argument frame _ ih => exact ⟨frame.plug_sorted ih.1, frame.plug_sorted ih.2⟩

theorem Step.raw {theory : Theory} {context : VariableContext} {sort : String} {source target : Term}
    (step : RawStep theory context sort source target) : Step theory context sort source target :=
  ⟨source, target, .refl step.sorted.1, step, .refl step.sorted.2⟩

theorem Step.respects_equations {theory : Theory} {context : VariableContext}
    {sort : String} {source source' target target' : Term} (left : Equivalent theory context sort source' source)
    (step : Step theory context sort source target) (right : Equivalent theory context sort target target') :
    Step theory context sort source' target' := by
  obtain ⟨redex, contractum, first, firing, last⟩ := step
  exact ⟨redex, contractum, .trans left first, firing, .trans last right⟩

end Mettapedia.Languages.Maude
