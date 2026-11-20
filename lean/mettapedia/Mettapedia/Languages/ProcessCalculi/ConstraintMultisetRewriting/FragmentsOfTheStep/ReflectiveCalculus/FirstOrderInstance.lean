import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Bisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# The rule set on the first-order instance of the step's interface

The firings of `Rules` are the admitted events of `AnnotatedRuns.firstOrder action label`, the
one-frame instance of the interface, whose firings carry no predicate queries
(`fires_iff_firstOrder`). The theorems proved once for that instance therefore hold for this rule
set; with the bisimulation they transfer to the reflective higher-order calculus only through
`Represents`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.FirstOrderInstance

/-- **The firings of a rule are the admitted query-free events of the first-order instance.** -/
theorem fires_iff_firstOrder (rule : RuleInstance Tm) (C C' : Store) :
    Fires rule C C' ↔ ∃ (selection : Selection Occ)
      (permitted : (AnnotatedRuns.firstOrder action label).Admits (s := C)
        (AnnotatedRuns.Firing.ofPlain (rule, selection))),
      (AnnotatedRuns.firstOrder action label).result _ permitted = C' := by
  constructor
  · rintro ⟨selection, valid, rfl⟩
    exact ⟨selection, (AnnotatedRuns.Firing.valid_ofPlain_iff action label _ C).mpr valid, rfl⟩
  · rintro ⟨selection, permitted, rfl⟩
    exact ⟨selection, (AnnotatedRuns.Firing.valid_ofPlain_iff action label _ C).mp permitted, rfl⟩

/-- Every firing of the rule set is an admitted event of the first-order instance. -/
theorem rules_fire_on_firstOrder {C C' : Store} (fires : ∃ rule, Rules rule ∧ Fires rule C C') :
    ∃ (rule : RuleInstance Tm) (selection : Selection Occ)
      (permitted : (AnnotatedRuns.firstOrder action label).Admits (s := C)
        (AnnotatedRuns.Firing.ofPlain (rule, selection))),
      Rules rule ∧ (AnnotatedRuns.firstOrder action label).result _ permitted = C' := by
  obtain ⟨rule, member, fires⟩ := fires
  obtain ⟨selection, permitted, same⟩ := (fires_iff_firstOrder rule C C').mp fires
  exact ⟨rule, selection, permitted, member, same⟩

#print axioms fires_iff_firstOrder

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.FirstOrderInstance
