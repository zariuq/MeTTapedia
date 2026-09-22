import Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralSemantics
import Mettapedia.OSLF.Framework.WMCalculusSemantics

/-!
# A nontrivial counting reading of overlap and scoped forgetting

The combined authored syntax has separate `Revise` and `OverlapMerge` state
operations. This reading models revision by addition of query counts and
overlap-aware merge by their pointwise maximum. The overlap factor is the
pointwise minimum, so the correction is genuine when sources coincide.
Forgetting removes counts in a Boolean scope. The laws here cover the core
reading and the three guarded-extension root computations; they do not yet
interpret every raw authored pattern or certify a relation environment.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading

open Mettapedia.OSLF.Framework.WMCalculusSemantics

set_option autoImplicit false

/-- Laws for the added operations over an existing lawful core reading.
`outsideScope` is a semantic property that a rule provider must certify. -/
structure CombinedReading (State Query Ev Ov Scope : Type) where
  core : WMReading State Query Ev
  coreLaws : core.CoreLaws
  overlapMerge : State → State → State
  overlapFactor : State → State → Query → Ov
  overlapCorrect : Ev → Ev → Ov → Ev
  forget : Scope → State → State
  inScope : Scope → Query → Prop
  overlapExtract : ∀ first second query,
    core.extract (overlapMerge first second) query =
      overlapCorrect (core.extract first query) (core.extract second query)
        (overlapFactor first second query)
  forgetIdempotent : ∀ scope state,
    forget scope (forget scope state) = forget scope state
  forgetOutside : ∀ {scope state query}, ¬ inScope scope query →
    core.extract (forget scope state) query = core.extract state query

/-- Exactly the nontrivial behavioral congruence obligations among the ten
guarded-extension argument positions. Positions whose semantics is literal
equality are congruent automatically. -/
structure CombinedCongruence {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope) : Prop where
  overlapMergeLeft : ∀ first first' second,
    reading.core.Agree .state first first' →
      reading.core.Agree .state
        (reading.overlapMerge first second)
        (reading.overlapMerge first' second)
  overlapMergeRight : ∀ first second second',
    reading.core.Agree .state second second' →
      reading.core.Agree .state
        (reading.overlapMerge first second)
        (reading.overlapMerge first second')
  overlapFactorFirst : ∀ first first' second query,
    reading.core.Agree .state first first' →
      reading.overlapFactor first second query =
        reading.overlapFactor first' second query
  overlapFactorSecond : ∀ first second second' query,
    reading.core.Agree .state second second' →
      reading.overlapFactor first second query =
        reading.overlapFactor first second' query
  forgetState : ∀ scope first second,
    reading.core.Agree .state first second →
      reading.core.Agree .state
        (reading.forget scope first) (reading.forget scope second)

abbrev CountState := String → Nat
abbrev CountScope := String → Bool

def countingCore : WMReading CountState String Nat where
  revise first second query := first query + second query
  extract state query := state query
  combine := Nat.add
  zero := 0
  world := fun worldName queried => if queried = worldName then 1 else 0
  query := id

theorem countingCore_laws : countingCore.CoreLaws := by
  constructor
  · intro first second query
    rfl
  · intro first second
    exact Nat.add_comm first second
  · intro first second third
    exact Nat.add_assoc first second third
  · intro value
    exact Nat.add_zero value

/-- The overlap correction is `a + b - min(a,b) = max(a,b)`; it is not a
posterior-probability addition masquerading as evidence addition. -/
def countingCombined : CombinedReading CountState String Nat Nat CountScope where
  core := countingCore
  coreLaws := countingCore_laws
  overlapMerge first second query := max (first query) (second query)
  overlapFactor first second query := min (first query) (second query)
  overlapCorrect first second factor := first + second - factor
  forget scope state query := if scope query then 0 else state query
  inScope scope query := scope query = true
  overlapExtract := by
    intro first second query
    change max (first query) (second query) =
      first query + second query - min (first query) (second query)
    omega
  forgetIdempotent := by
    intro scope state
    funext query
    cases h : scope query <;> simp [h]
  forgetOutside := by
    intro scope state query outside
    change (if scope query then 0 else state query) = state query
    cases h : scope query <;> simp_all

private theorem countingAgree_iff_eq (first second : CountState) :
    countingCore.Agree .state first second ↔ first = second := by
  constructor
  · intro agreement
    funext query
    exact agreement query
  · intro equality
    rw [equality]
    exact countingCore.agree_refl .state second

/-- The concrete counting reading respects all five behavioral positions;
the remaining guarded-vertex positions follow from literal equality. -/
theorem countingCombined_congruence : CombinedCongruence countingCombined := by
  constructor
  · intro first first' second agreement
    have equality := (countingAgree_iff_eq first first').mp agreement
    subst first'
    exact countingCore.agree_refl .state _
  · intro first second second' agreement
    have equality := (countingAgree_iff_eq second second').mp agreement
    subst second'
    exact countingCore.agree_refl .state _
  · intro first first' second query agreement
    have equality := (countingAgree_iff_eq first first').mp agreement
    subst first'
    rfl
  · intro first second second' query agreement
    have equality := (countingAgree_iff_eq second second').mp agreement
    subst second'
    rfl
  · intro scope first second agreement
    have equality := (countingAgree_iff_eq first second).mp agreement
    subst second
    exact countingCore.agree_refl .state _

/-- Correlated identical sources carry a nonzero overlap correction. -/
theorem identical_worlds_overlap :
    countingCombined.overlapFactor (countingCore.world "x")
      (countingCore.world "x") "x" = 1 := by
  decide +kernel

/-- Overlap-aware merge is observably different from additive revision. -/
theorem overlap_merge_not_revision :
    countingCore.extract
      (countingCombined.overlapMerge (countingCore.world "x")
        (countingCore.world "x")) "x" ≠
      countingCore.extract
        (countingCore.revise (countingCore.world "x")
          (countingCore.world "x")) "x" := by
  decide +kernel

/-- The outside-scope premise is necessary: inside the forgotten scope,
extraction can change. -/
theorem forgetting_changes_inside_scope :
    countingCore.extract
      (countingCombined.forget (fun query => query == "x")
        (countingCore.world "x")) "x" ≠
      countingCore.extract (countingCore.world "x") "x" := by
  decide +kernel

#print axioms countingCore_laws
#print axioms countingCombined
#print axioms countingCombined_congruence
#print axioms identical_worlds_overlap
#print axioms overlap_merge_not_revision
#print axioms forgetting_changes_inside_scope

end Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
