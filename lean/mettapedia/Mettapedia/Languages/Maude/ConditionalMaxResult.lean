import Mettapedia.Languages.Maude.ConditionalMaxTermination

/-! The result contract for closed Nat observations. A settled source
normalization returns exactly the independent value observation; a pending
prefix is not required to have returned it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ConditionalMax

theorem value_interpretation {source : Term} {value : Nat}
    (typed : HasSort Examples.conditional.signature [] source "Nat")
    (observed : value? source = some value) :
    interpret closedAssignment source = some (.natural value) := by
  have same := equivalent_same_interpretation (observed_value_equivalent source value observed typed)
    closedAssignment closedAssignment_sorted
  exact same.trans (interpret_numeral closedAssignment value)

theorem value_path {source : Term} {value : Nat}
    (typed : HasSort Examples.conditional.signature [] source "Nat")
    (observed : value? source = some value) :
    EquationPath Examples.conditional [] "Nat" source (numeral value) := by
  obtain ⟨actual, actualObserved, path⟩ := normalize_path source "Nat" typed
  have same : actual = .natural value :=
    Option.some.inj (actualObserved.symm.trans (value_interpretation typed observed))
  simpa only [same, represent] using path

theorem normal_value {source target : Term} {value : Nat}
    (typed : HasSort Examples.conditional.signature [] source "Nat")
    (observed : value? source = some value)
    (path : EquationPath Examples.conditional [] "Nat" source target)
    (normal : ∀ next, ¬ EquationReduction Examples.conditional [] "Nat" target next) :
    target = numeral value := by
  obtain ⟨actual, actualObserved, targetSame⟩ := normal_result typed path normal
  have same : actual = .natural value :=
    Option.some.inj (actualObserved.symm.trans (value_interpretation typed observed))
  simpa only [same, represent] using targetSame

theorem settled_result_exists {source : Term}
    (typed : HasSort Examples.conditional.signature [] source "Nat") :
    ∃ value, value? source = some value ∧
      EquationPath Examples.conditional [] "Nat" source (numeral value) ∧
      ∀ target, EquationPath Examples.conditional [] "Nat" source target →
        (∀ next, ¬ EquationReduction Examples.conditional [] "Nat" target next) →
        target = numeral value := by
  obtain ⟨value, observed⟩ := closed_value_total typed
  exact ⟨value, observed, value_path typed observed, fun _ path normal => normal_value typed observed path normal⟩

example : EquationPath Examples.conditional [] "Nat"
    (successor (maximum (numeral 1) (numeral 3))) (numeral 4) := by
  apply value_path
  · exact .app successor_member (.cons (max_sorted (numeral_sorted [] 1) (numeral_sorted [] 3)) .nil)
  · decide_cbv

example : ¬ EquationPath Examples.conditional [] "Nat" (maximum (numeral 2) (numeral 1)) (numeral 1) := by
  intro path
  have unique := observed_numeral_unique (max_sorted (numeral_sorted [] 2) (numeral_sorted [] 1))
    (by decide_cbv : value? (maximum (numeral 2) (numeral 1)) = some 2)
    (path.equivalent (max_sorted (numeral_sorted [] 2) (numeral_sorted [] 1)))
  omega

#print axioms value_path
#print axioms normal_value
#print axioms settled_result_exists

end Mettapedia.Languages.Maude.ConditionalMax
