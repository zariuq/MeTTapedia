import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateImplication
import Mettapedia.CategoryTheory.InternalPredicateLogicalUniqueness
import Mettapedia.CategoryTheory.ElementaryTypePredicateReadout

/-!
# Native classifier, quantifier and implication controls

An independently supplied proper predicate depends on both a Boolean value
and an external number. The actual native quantified function, qualified by
its finite diagrams, reads precisely numbers above one. A future parameter
map changes that answer; reading only the false coordinate accepts a value
which the complete quantifier rejects.
The implication consumes two independently supplied predicates and separates
both projections by its complete pointwise reading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.HigherOrderInternalPredicateControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryTypePredicateReadout
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier

abbrev logic := ElementaryTypePredicateReadout.doctrine

def forgetBoolean : Bool ⟶ PUnit := TypeCat.ofHom (fun _ => PUnit.unit)

def suppliedPredicate : Subobject (Bool ⊗ Nat) :=
  fromSet {point | if point.1 then point.2 > 1 else point.2 > 0}

def suppliedName : Nat ⟶ power logic Bool :=
  curry (logic.generic.characteristic _ suppliedPredicate)

theorem supplied_family : family logic suppliedName = suppliedPredicate := by
  change logic.reindex (uncurry (curry (logic.generic.characteristic _ suppliedPredicate)))
    logic.generic.truth = suppliedPredicate
  rw [uncurry_curry]
  exact logic.generic.classifies _ _

def quantifier := forallQualification logic forgetBoolean

def output : Subobject (PUnit ⊗ Nat) := family logic (suppliedName ≫ quantifier.operation)

theorem output_evaluation :
    output = logic.forallAlong (forgetBoolean ▷ Nat) suppliedPredicate :=
  (forall_supplied logic forgetBoolean suppliedName).trans
    (congrArg (logic.forallAlong (forgetBoolean ▷ Nat)) supplied_family)

theorem complete_output_read (parameter : Nat) :
    Contains output (PUnit.unit, parameter) ↔ parameter > 1 := by
  rw [output_evaluation, contains_forall]
  constructor
  · intro supplied
    have read := (contains_fromSet _ _).mp (supplied (true, parameter) rfl)
    exact read
  · intro admitted supplied reading
    have parameterRead := congrArg Prod.snd reading
    change supplied.2 = parameter at parameterRead
    apply (contains_fromSet _ _).mpr
    change (if supplied.1 then supplied.2 > 1 else supplied.2 > 0)
    rw [parameterRead]
    cases supplied.1 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem the_complete_native_answer_is_not_constant :
    Contains output (PUnit.unit, 2) ∧ ¬ Contains output (PUnit.unit, 1) := by
  rw [complete_output_read, complete_output_read]
  exact ⟨by omega, Nat.lt_irrefl 1⟩

theorem a_single_coordinate_cannot_replace_the_native_quantifier :
    Contains (family logic suppliedName) (false, 1) ∧
      ¬ Contains output (PUnit.unit, 1) := by
  rw [supplied_family, suppliedPredicate, contains_fromSet, complete_output_read]
  exact ⟨by decide, Nat.lt_irrefl 1⟩

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem complete_future_read (parameter : Nat) :
    Contains (family logic ((future ≫ suppliedName) ≫ quantifier.operation))
      (PUnit.unit, parameter) ↔ parameter + 1 > 1 := by
  have complete : family logic ((future ≫ suppliedName) ≫ quantifier.operation) =
      logic.reindex (PUnit ◁ future) output :=
    (congrArg (family logic) (Category.assoc future suppliedName quantifier.operation)).trans
      (family_substitution logic future (suppliedName ≫ quantifier.operation))
  rw [complete, contains_reindex]
  exact complete_output_read (parameter + 1)

theorem the_actual_future_changes_the_answer :
    ¬ Contains output (PUnit.unit, 1) ∧
      Contains (family logic ((future ≫ suppliedName) ≫ quantifier.operation)) (PUnit.unit, 1) := by
  rw [complete_output_read, complete_future_read]
  exact ⟨Nat.lt_irrefl 1, by omega⟩

def existential := existsQualification logic forgetBoolean

def existentialOutput : Subobject (PUnit ⊗ Nat) :=
  family logic (suppliedName ≫ existential.operation)

theorem existential_output_evaluation :
    existentialOutput = logic.existsAlong (forgetBoolean ▷ Nat) suppliedPredicate :=
  (exists_supplied logic forgetBoolean suppliedName).trans
    (congrArg (logic.existsAlong (forgetBoolean ▷ Nat)) supplied_family)

theorem the_existential_keeps_an_actual_supplied_coordinate :
    Contains existentialOutput (PUnit.unit, 1) ∧ ¬ Contains output (PUnit.unit, 1) := by
  constructor
  · rw [existential_output_evaluation, contains_exists]
    refine ⟨(false, 1), ?_, rfl⟩
    exact (contains_fromSet _ _).mpr (by decide)
  · exact (complete_output_read 1).not.mpr (Nat.lt_irrefl 1)

def suppliedAntecedent : Subobject Nat := fromSet {parameter | parameter > 0}
def suppliedConsequent : Subobject Nat := fromSet {parameter | parameter > 1}

def antecedentName : Nat ⟶ logic.generic.object :=
  logic.generic.characteristic _ suppliedAntecedent
def consequentName : Nat ⟶ logic.generic.object :=
  logic.generic.characteristic _ suppliedConsequent

def implication := HigherOrderInternalPredicateImplication.qualification logic

def implicationName : Nat ⟶ logic.generic.object :=
  implication.implies (operations logic) antecedentName consequentName

theorem implication_output_evaluation :
    decode logic implicationName =
      (logic.algebra Nat).himp suppliedAntecedent suppliedConsequent := by
  have complete := HigherOrderInternalPredicateImplication.applied_read logic
    antecedentName consequentName
  change decode logic implicationName = _ at complete
  exact complete.trans (congrArg₂ (logic.algebra Nat).himp
    (logic.generic.classifies _ _) (logic.generic.classifies _ _))

theorem complete_implication_read (parameter : Nat) :
    Contains (decode logic implicationName) parameter ↔ (parameter > 0 → parameter > 1) := by
  rw [implication_output_evaluation, contains_implication]
  simp only [suppliedAntecedent, suppliedConsequent, contains_fromSet, Set.mem_ofPred_eq]

theorem implication_retains_both_supplied_inputs :
    Contains (decode logic implicationName) 0 ∧
      ¬ Contains suppliedConsequent 0 ∧ Contains suppliedAntecedent 1 ∧
      ¬ Contains (decode logic implicationName) 1 ∧
      Contains (decode logic implicationName) 2 := by
  rw [complete_implication_read, complete_implication_read, complete_implication_read,
    suppliedConsequent, suppliedAntecedent, contains_fromSet, contains_fromSet]
  change ((0 : Nat) > 0 → 0 > 1) ∧ ¬ ((0 : Nat) > 1) ∧ (1 : Nat) > 0 ∧
    ¬ ((1 : Nat) > 0 → 1 > 1) ∧ ((2 : Nat) > 0 → 2 > 1)
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem any_locally_qualified_universal_reads_the_complete_predicate
    (candidate : InternalPredicateQuantifier.Universal (operations logic) forgetBoolean)
    (parameter : Nat) :
    Contains (family logic (suppliedName ≫ candidate.operation)) (PUnit.unit, parameter) ↔
      parameter > 1 := by
  rw [InternalPredicateLogicalUniqueness.universal_operation_unique (operations logic)
    (laws logic) forgetBoolean candidate quantifier]
  exact complete_output_read parameter

theorem any_locally_qualified_implication_retains_both_inputs
    (candidate : InternalPredicateImplication.Qualification (operations logic)) (parameter : Nat) :
    Contains (decode logic (candidate.implies (operations logic) antecedentName consequentName)) parameter ↔
      (parameter > 0 → parameter > 1) := by
  have complete := InternalPredicateLogicalUniqueness.implication_operation_unique
    (operations logic) (laws logic) candidate implication
  change Contains (decode logic (InternalPredicateImplication.applyOperation (operations logic)
    candidate.operation antecedentName consequentName)) parameter ↔ _
  rw [complete]
  exact complete_implication_read parameter

theorem finite_qualification_yields_the_complete_context_adjunction (context : Type) :
    letI : SemilatticeInf (context ⟶ power logic PUnit) :=
      (InternalPredicateQuantifier.functions (operations logic) PUnit).semilattice
        (InternalPredicateQuantifier.functionLaws (operations logic) (laws logic) PUnit) context
    letI : SemilatticeInf (context ⟶ power logic Bool) :=
      (InternalPredicateQuantifier.functions (operations logic) Bool).semilattice
        (InternalPredicateQuantifier.functionLaws (operations logic) (laws logic) Bool) context
    GaloisConnection
      (fun predicate : context ⟶ power logic PUnit =>
        (predicate ≫ InternalPredicateQuantifier.precomposition (operations logic) forgetBoolean :
          context ⟶ power logic Bool))
      (fun predicate : context ⟶ power logic Bool =>
        (predicate ≫ quantifier.operation : context ⟶ power logic PUnit)) :=
  InternalPredicateQuantifier.Universal.adjunction (operations logic) (laws logic)
    forgetBoolean quantifier context

end Mettapedia.CategoryTheory.HigherOrderInternalPredicateControls
