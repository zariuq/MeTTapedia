import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension

/-!
# Inserting independent computational components

Definitions inserted between two parts of a program preserve the original
dispatch when they do not claim any of its called names. Original equation
order is retained. The resulting comparison preserves every outcome and fuel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem DispatchAgreement.insert (leading trailing addition : Program)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ (leading ++ trailing).calledHeads) :
    DispatchAgreement (leading ++ trailing) (leading ++ addition ++ trailing) (leading ++ trailing).calledHeads := by
  have undefined (head : String) (used : head ∈ (leading ++ trailing).calledHeads) :
      addition.defines head = false := by
    simp only [Program.defines, List.any_eq_false]
    intro equation member
    have different : equation.head ≠ head := fun same => disjoint equation member (same.symm ▸ used)
    simp [different]
  constructor
  · intro head used arity
    simp only [Program.definesAt, List.any_append]
    change (leading.definesAt head arity || trailing.definesAt head arity) =
      ((leading.definesAt head arity || addition.definesAt head arity) || trailing.definesAt head arity)
    rw [Program.definesAt_false_of_defines_false (undefined head used) arity, Bool.or_false]
  · intro head used
    simp only [Program.defines, List.any_append]
    change (leading.defines head || trailing.defines head) =
      ((leading.defines head || addition.defines head) || trailing.defines head)
    rw [undefined head used, Bool.or_false]
  · intro head used arguments
    simp only [Program.select, List.findSome?_append]
    change (leading.select head arguments).or (trailing.select head arguments) =
      ((leading.select head arguments).or (addition.select head arguments)).or (trailing.select head arguments)
    rw [Program.select_none_of_undefined (undefined head used) arguments, Option.or_none]

theorem apply_insert_eq (leading trailing addition : Program) (host : Host)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ (leading ++ trailing).calledHeads)
    (fuel : Nat) (head : String) (used : head ∈ (leading ++ trailing).calledHeads) (arguments : List Term) :
    apply (leading ++ addition ++ trailing) host fuel head arguments =
      apply (leading ++ trailing) host fuel head arguments :=
  (apply_dispatch_eq host (DispatchAgreement.insert leading trailing addition disjoint)
    (fun _ member => Program.calledHeads_body member) fuel head used arguments).symm

theorem Applies.insert_iff (leading trailing addition : Program) (host : Host)
    (disjoint : ∀ equation ∈ addition, equation.head ∉ (leading ++ trailing).calledHeads)
    (head : String) (used : head ∈ (leading ++ trailing).calledHeads) (arguments : List Term) (result : Term) :
    Applies (leading ++ addition ++ trailing) host head arguments result ↔
      Applies (leading ++ trailing) host head arguments result := by
  unfold Applies
  simp only [apply_insert_eq leading trailing addition host disjoint _ head used arguments]

namespace ProgramInsertionControls

private def leading : Program := [⟨"first", "choose", [], .sym "first"⟩]
private def trailing : Program := [⟨"second", "choose", [], .sym "second"⟩]
private def independent : Program := [⟨"other", "other", [], .sym "other"⟩]
private def host : Host := ⟨fun _ _ => .unhandled⟩

theorem insertion_preserves_ordered_selection (fuel : Nat) :
    apply (leading ++ independent ++ trailing) host fuel "choose" [] =
      apply (leading ++ trailing) host fuel "choose" [] :=
  apply_insert_eq leading trailing independent host (by decide) fuel "choose" (by decide) []

theorem reordering_existing_rules_changes_result :
    apply (leading ++ trailing) host 1 "choose" [] = .value (.sym "first") ∧
      apply (trailing ++ leading) host 1 "choose" [] = .value (.sym "second") := by
  constructor <;> rfl

theorem claiming_existing_name_is_not_independent :
    ¬ (∀ equation ∈ leading, equation.head ∉ (leading ++ trailing).calledHeads) := by
  intro independent
  exact independent leading[0] (by simp [leading]) (by decide)

end ProgramInsertionControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
