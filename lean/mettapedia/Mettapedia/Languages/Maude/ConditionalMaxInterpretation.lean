import Mettapedia.Languages.Maude.ConditionalMaxExpression

/-! A two-sorted interpretation of the conditional max theory. Equality
evidence must preserve both natural-number and Boolean values, including
the equality evidence used to authorize a conditional equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Maude.ConditionalMax

inductive SemanticValue where
  | natural (value : Nat)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

def finishValue (label : String) (arguments : List (Option SemanticValue)) : Option SemanticValue :=
  match label, arguments with
  | "max.zero", [] => some (.natural 0)
  | "max.succ", [some (.natural value)] => some (.natural (value + 1))
  | "max.max", [some (.natural left), some (.natural right)] => some (.natural (max left right))
  | "max.true", [] => some (.boolean true)
  | "max.false", [] => some (.boolean false)
  | "max.le", [some (.natural left), some (.natural right)] => some (.boolean (decide (left ≤ right)))
  | _, _ => none

def interpret (assignment : String → Option SemanticValue) : Term → Option SemanticValue
  | .var name => assignment name
  | .app label arguments => finishValue label (arguments.map (interpret assignment))

def FitsSort : Option SemanticValue → String → Prop
  | some (.natural _), "Nat" => True
  | some (.boolean _), "Bool" => True
  | _, _ => False

def SortedAssignment (context : VariableContext) (assignment : String → Option SemanticValue) : Prop :=
  ∀ name sort, context.lookup name = some sort → FitsSort (assignment name) sort

theorem fits_natural_iff (value : Option SemanticValue) :
    FitsSort value "Nat" ↔ ∃ number, value = some (.natural number) := by
  cases value with
  | none => simp [FitsSort]
  | some value => cases value <;> simp [FitsSort]

theorem operators {declaration : Operator} (member : declaration ∈ Examples.conditional.signature.operators) :
    declaration = zeroOperator ∨ declaration = successorOperator ∨ declaration = trueOperator ∨
      declaration = falseOperator ∨ declaration = leOperator ∨ declaration = maxOperator := by
  simpa only [Examples.conditional, Examples.natData, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, zeroOperator, successorOperator,
    trueOperator, falseOperator, leOperator, maxOperator, String.reduceAppend] using member

theorem interpret_sorted {context : VariableContext} {assignment : String → Option SemanticValue}
    (assigned : SortedAssignment context assignment) {source : Term} {sort : String}
    (typed : HasSort Examples.conditional.signature context source sort) :
    FitsSort (interpret assignment source) sort := by
  refine HasSort.rec
    (motive_1 := fun source sort _ => FitsSort (interpret assignment source) sort)
    (motive_2 := fun sources sorts _ => List.Forall₂ (fun source sort =>
      FitsSort (interpret assignment source) sort) sources sorts)
    ?_ ?_ ?_ ?_ typed
  · intro name sort found
    simpa only [interpret] using assigned name sort found
  · intro declaration arguments member _ ih
    rcases operators member with rfl | rfl | rfl | rfl | rfl | rfl
    · cases ih
      simp only [zeroOperator, interpret, List.map_nil, finishValue, FitsSort]
    · cases ih with
      | @cons child _ _ _ first rest =>
        cases rest
        obtain ⟨number, same⟩ := (fits_natural_iff _).mp first
        simp only [successorOperator, interpret, List.map_cons, List.map_nil, same, finishValue, FitsSort]
    · cases ih
      simp only [trueOperator, interpret, List.map_nil, finishValue, FitsSort]
    · cases ih
      simp only [falseOperator, interpret, List.map_nil, finishValue, FitsSort]
    · cases ih with
      | @cons left _ _ _ first rest =>
        cases rest with
        | @cons right _ _ _ second tail =>
          cases tail
          obtain ⟨firstNumber, firstSame⟩ := (fits_natural_iff _).mp first
          obtain ⟨secondNumber, secondSame⟩ := (fits_natural_iff _).mp second
          simp only [leOperator, interpret, List.map_cons, List.map_nil, firstSame, secondSame, finishValue, FitsSort]
    · cases ih with
      | @cons left _ _ _ first rest =>
        cases rest with
        | @cons right _ _ _ second tail =>
          cases tail
          obtain ⟨firstNumber, firstSame⟩ := (fits_natural_iff _).mp first
          obtain ⟨secondNumber, secondSame⟩ := (fits_natural_iff _).mp second
          simp only [maxOperator, interpret, List.map_cons, List.map_nil, firstSame, secondSame, finishValue, FitsSort]
  · exact .nil
  · intro first sort rest sorts _ _ firstIH restIH
    exact .cons firstIH restIH

theorem interpret_substitute (assignment : String → Option SemanticValue) (replacement : Valuation)
    (source : Term) : interpret assignment (source.substitute replacement) =
      interpret (fun name => interpret assignment (replacement name)) source := by
  refine Term.rec
    (motive_1 := fun source => interpret assignment (source.substitute replacement) =
      interpret (fun name => interpret assignment (replacement name)) source)
    (motive_2 := fun sources => sources.map (fun source => interpret assignment (source.substitute replacement)) =
      sources.map (interpret (fun name => interpret assignment (replacement name))))
    ?_ ?_ ?_ ?_ source
  · intro name
    simp only [Term.substitute, interpret]
  · intro label arguments ih
    simpa only [Term.substitute, interpret, List.map_map, Function.comp_def] using congrArg (finishValue label) ih
  · rfl
  · intro first rest firstIH restIH
    simp only [List.map_cons, firstIH, restIH]

theorem interpret_frame {context : VariableContext} {hole result : String}
    (frame : ArgumentContext Examples.conditional.signature context hole result)
    (assignment : String → Option SemanticValue) {source target : Term}
    (same : interpret assignment source = interpret assignment target) :
    interpret assignment (frame.plug source) = interpret assignment (frame.plug target) := by
  simp only [ArgumentContext.plug, interpret, List.map_append, List.map_cons, same]

theorem interpret_row {row : Row} (member : row ∈ Examples.conditional.equations)
    (assignment : String → Option SemanticValue) (assigned : SortedAssignment row.usedContext assignment)
    (conditions : ∀ condition ∈ row.conditions,
      interpret assignment condition.left = interpret assignment condition.right) :
    interpret assignment row.left = interpret assignment row.right := by
  have natValue (name : String) (found : row.usedContext.lookup name = some "Nat") :
      ∃ value, assignment name = some (.natural value) :=
    (fits_natural_iff _).mp (assigned name "Nat" found)
  simp only [Examples.conditional, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨value, same⟩ := natValue "N" (by decide_cbv)
    simp only [Examples.binary, Examples.constant, Examples.numeral, Examples.n, interpret,
      String.reduceAppend, List.map_cons, List.map_nil, same, finishValue, Nat.zero_le, decide_true]
  · obtain ⟨value, same⟩ := natValue "N" (by decide_cbv)
    have falseComparison : ¬ value + 1 ≤ 0 := by omega
    simp only [Examples.binary, Examples.constant, Examples.numeral, Examples.n, interpret,
      String.reduceAppend, List.map_cons, List.map_nil, same, finishValue,
      falseComparison, decide_false]
  · obtain ⟨first, firstSame⟩ := natValue "N" (by decide_cbv)
    obtain ⟨second, secondSame⟩ := natValue "M" (by decide_cbv)
    simp only [Examples.binary, Examples.n, Examples.m, interpret, List.map_cons, List.map_nil,
      firstSame, secondSame, finishValue, Nat.add_le_add_iff_right]
  · obtain ⟨first, firstSame⟩ := natValue "N" (by decide_cbv)
    obtain ⟨second, secondSame⟩ := natValue "M" (by decide_cbv)
    have guard := conditions ⟨Examples.binary "max.le" Examples.m Examples.n, Examples.constant "max.true"⟩
      List.mem_cons_self
    simp only [Examples.binary, Examples.constant, Examples.n, Examples.m, interpret,
      List.map_cons, List.map_nil, firstSame, secondSame, finishValue,
      Option.some.injEq, SemanticValue.boolean.injEq, decide_eq_true_eq] at guard
    simp only [Examples.binary, Examples.n, Examples.m, interpret, List.map_cons, List.map_nil,
      firstSame, secondSame, finishValue, Nat.max_eq_left guard]
  · obtain ⟨first, firstSame⟩ := natValue "N" (by decide_cbv)
    obtain ⟨second, secondSame⟩ := natValue "M" (by decide_cbv)
    have guard := conditions ⟨Examples.binary "max.le" Examples.n Examples.m, Examples.constant "max.true"⟩
      List.mem_cons_self
    simp only [Examples.binary, Examples.constant, Examples.n, Examples.m, interpret,
      List.map_cons, List.map_nil, firstSame, secondSame, finishValue,
      Option.some.injEq, SemanticValue.boolean.injEq, decide_eq_true_eq] at guard
    simp only [Examples.binary, Examples.n, Examples.m, interpret, List.map_cons, List.map_nil,
      firstSame, secondSame, finishValue, Nat.max_eq_right guard]

theorem algebra_impossible {source target : Term} :
    ¬ AlgebraSchema Examples.conditional.signature source target := by
  intro schema
  have attributes : ∀ declaration ∈ Examples.conditional.signature.operators,
      declaration.attributes.associative = false ∧ declaration.attributes.commutative = false ∧
        declaration.attributes.identity = none := by
    intro declaration member
    rcases operators member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  cases schema with
  | associative member active => simp [(attributes _ member).1] at active
  | commutative member active => simp [(attributes _ member).2.1] at active
  | leftUnit member active => simp [(attributes _ member).2.2] at active
  | rightUnit member active => simp [(attributes _ member).2.2] at active

theorem equivalent_same_interpretation {context : VariableContext} {sort : String} {source target : Term}
    (equivalent : Equivalent Examples.conditional context sort source target)
    (assignment : String → Option SemanticValue) (assigned : SortedAssignment context assignment) :
    interpret assignment source = interpret assignment target := by
  refine Equivalent.rec
    (motive_1 := fun _ source target _ => interpret assignment source = interpret assignment target)
    (motive_2 := fun replacement conditions _ => ∀ condition ∈ conditions,
      interpret assignment (condition.left.substitute replacement) =
        interpret assignment (condition.right.substitute replacement))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro _ _ _
    rfl
  · intro _ _ _ _ ih
    exact ih.symm
  · intro _ _ _ _ _ _ first last
    exact first.trans last
  · intro _ _ frame _ _ _ ih
    exact interpret_frame frame assignment ih
  · intro _ _ _ schema
    exact (algebra_impossible schema.schema).elim
  · intro row _ replacement member _ _ _ typed _ conditions
    rw [interpret_substitute, interpret_substitute]
    apply interpret_row member
    · intro name sort found
      exact interpret_sorted assigned (typed name sort found)
    · intro condition inside
      simpa only [interpret_substitute] using conditions condition inside
  · intro replacement condition impossible
    cases impossible
  · intro replacement condition rest sort _ _ first restIH actual member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact restIH actual member

def closedAssignment : String → Option SemanticValue := fun _ => none

theorem closedAssignment_sorted : SortedAssignment [] closedAssignment := by
  intro name sort impossible
  cases impossible

theorem interpret_numeral (assignment : String → Option SemanticValue) (value : Nat) :
    interpret assignment (numeral value) = some (.natural value) := by
  induction value with
  | zero => simp only [numeral, Examples.numeral, Examples.constant, String.reduceAppend,
      interpret, List.map_nil, finishValue]
  | succ value ih =>
    change interpret assignment (.app "max.succ" [numeral value]) = some (.natural (value + 1))
    simp only [interpret, List.map_cons, List.map_nil, ih, finishValue]

theorem comparison_true_iff (left right : Nat) :
    Equivalent Examples.conditional [] "Bool" (le (numeral left) (numeral right)) truth ↔ left ≤ right := by
  constructor
  · intro equivalent
    have same := equivalent_same_interpretation equivalent closedAssignment closedAssignment_sorted
    simpa only [le, truth, interpret, List.map_cons, List.map_nil, interpret_numeral,
      finishValue, Option.some.injEq, SemanticValue.boolean.injEq, decide_eq_true_eq] using same
  · intro ordered
    simpa only [if_pos ordered] using comparison_equivalent left right

theorem false_comparison_not_true (left right : Nat) (unordered : right < left) :
    ¬ Equivalent Examples.conditional [] "Bool" (le (numeral left) (numeral right)) truth := by
  intro equivalent
  have ordered := (comparison_true_iff left right).mp equivalent
  omega

theorem truth_not_falsehood : ¬ Equivalent Examples.conditional [] "Bool" truth falsehood := by
  intro equivalent
  have same := equivalent_same_interpretation equivalent closedAssignment closedAssignment_sorted
  simp only [truth, falsehood, interpret, List.map_nil, finishValue, Option.some.injEq,
    SemanticValue.boolean.injEq, Bool.true_eq_false] at same

theorem numerals_equivalent_iff (first second : Nat) :
    Equivalent Examples.conditional [] "Nat" (numeral first) (numeral second) ↔ first = second := by
  constructor
  · intro equivalent
    have same := equivalent_same_interpretation equivalent closedAssignment closedAssignment_sorted
    simpa only [interpret_numeral, Option.some.injEq, SemanticValue.natural.injEq] using same
  · rintro rfl
    exact .refl (numeral_sorted [] first)

theorem observed_numeral_unique {source : Term} {observed candidate : Nat}
    (typed : HasSort Examples.conditional.signature [] source "Nat")
    (value : value? source = some observed)
    (equivalent : Equivalent Examples.conditional [] "Nat" source (numeral candidate)) :
    candidate = observed := by
  apply (numerals_equivalent_iff candidate observed).mp
  exact .trans equivalent.symm (observed_value_equivalent source observed value typed)

#guard decide (¬ (3 ≤ 2))

example : Equivalent Examples.conditional [] "Bool" (le (numeral 2) (numeral 3)) truth :=
  (comparison_true_iff 2 3).mpr (by omega)

example : ¬ Equivalent Examples.conditional [] "Bool" (le (numeral 3) (numeral 2)) truth :=
  false_comparison_not_true 3 2 (by omega)

example : ¬ Equivalent Examples.conditional [] "Nat" (numeral 2) (numeral 3) := by
  rw [numerals_equivalent_iff]
  omega

#print axioms equivalent_same_interpretation
#print axioms comparison_true_iff
#print axioms observed_numeral_unique

end Mettapedia.Languages.Maude.ConditionalMax
