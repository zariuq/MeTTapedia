import Mettapedia.OSLF.Framework.WMCalculusFreeSemanticModel
import Mettapedia.OSLF.Framework.WMCalculusContextEncoding
import Mettapedia.OSLF.Framework.WMCalculusSemantics

/-!
# A closed semantic equality missing from contextual WM reduction

The WM core laws require evidence combination to be associative, whereas
the authored five directed core rules contain no evidence-associativity
step. For three distinct atomic observations, contextual reduction can
commute children but cannot move an atom from one root subtree to the other.
The two associations consequently have the same denotation in every lawful
reading but are not reachable from one another by the authored contextual
step relation. This is a negative operational-completeness result, not a
proposal to orient an equation or to erase directional computation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusRewriteCompletenessBoundary

open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusFreeSemanticModel

/-- Atomic observations and their combinations contain neither a revisable
state nor zero evidence. This fragment is closed under its available steps. -/
inductive PureEvidence : WMTerm .evidence → Prop where
  | atom (state query : String) :
      PureEvidence (.extract (.state state) (.query query))
  | combine {first second : WMTerm .evidence} :
      PureEvidence first → PureEvidence second →
        PureEvidence (.combine first second)

/-- The multiset of the two root-subtree evidence normal forms. Child
commutations do not change these groups, while reassociation does. -/
def rootGroups : WMTerm .evidence →
    Option (Multiset (Multiset (String × String)))
  | .combine first second =>
      some ({evidenceNormalForm first, evidenceNormalForm second} :
        Multiset (Multiset (String × String)))
  | _ => none

/-- Free semantic soundness gives normal-form invariance under any
contextual WM step, including steps nested inside a root group. -/
theorem evidenceNormalForm_of_contextStep
    {first second : WMTerm .evidence}
    (step : WMContextStep first second) :
    evidenceNormalForm first = evidenceNormalForm second := by
  have agree := freeReading_coreLaws.agree_of_contextStep step
  change freeReading.denote first = freeReading.denote second at agree
  simpa only [freeReading_denote_evidence] using agree

/-- No contextual step can start at an atomic state term. -/
private theorem no_state_atom_step (name : String)
    {target : WMTerm .state} :
    ¬ WMContextStep (.state name) target := by
  intro step
  cases step with
  | root root => cases root

/-- No contextual step can start at a query atom. -/
private theorem no_query_atom_step (name : String)
    {target : WMTerm .query} :
    ¬ WMContextStep (.query name) target := by
  intro step
  cases step with
  | root root => cases root

/-- Each step available in the pure fragment preserves both purity and the
partition of evidence atoms between the root's two children. -/
theorem pure_contextStep_invariant :
    ∀ {first second : WMTerm .evidence},
      PureEvidence first → WMContextStep first second →
        PureEvidence second ∧ rootGroups first = rootGroups second := by
  intro first second pure step
  induction pure generalizing second with
  | atom name queryName =>
      cases step with
      | root root => cases root
      | extract_left query inner =>
          exact False.elim (no_state_atom_step name inner)
      | extract_right world inner =>
          exact False.elim (no_query_atom_step queryName inner)
  | combine pureLeft pureRight ihLeft ihRight =>
      cases step with
      | root root =>
          cases root with
          | combine_comm left right =>
              refine ⟨.combine pureRight pureLeft, ?_⟩
              simp only [rootGroups]
              exact congrArg some (Multiset.pair_comm _ _)
          | combine_zero term =>
              cases pureRight
      | combine_left right inner =>
          obtain ⟨pureTarget, _⟩ := ihLeft inner
          refine ⟨.combine pureTarget pureRight, ?_⟩
          simp only [rootGroups]
          rw [evidenceNormalForm_of_contextStep inner]
      | combine_right left inner =>
          obtain ⟨pureTarget, _⟩ := ihRight inner
          refine ⟨.combine pureLeft pureTarget, ?_⟩
          simp only [rootGroups]
          rw [evidenceNormalForm_of_contextStep inner]

/-- The root partition remains unchanged after any finite sequence of
contextual steps from a pure evidence term. -/
theorem pure_contextStepStar_invariant
    {first second : WMTerm .evidence}
    (pure : PureEvidence first)
    (steps : WMContextStepStar first second) :
    PureEvidence second ∧ rootGroups first = rootGroups second := by
  induction steps with
  | refl => exact ⟨pure, rfl⟩
  | tail _ last previous =>
      obtain ⟨pureMiddle, sameFirst⟩ := previous
      obtain ⟨pureLast, sameLast⟩ :=
        pure_contextStep_invariant pureMiddle last
      exact ⟨pureLast, sameFirst.trans sameLast⟩

private def a : WMTerm .evidence :=
  .extract (.state "a") (.query "q")
private def b : WMTerm .evidence :=
  .extract (.state "b") (.query "q")
private def c : WMTerm .evidence :=
  .extract (.state "c") (.query "q")

def leftAssoc : WMTerm .evidence := .combine (.combine a b) c
def rightAssoc : WMTerm .evidence := .combine a (.combine b c)

theorem leftAssoc_pure : PureEvidence leftAssoc :=
  .combine (.combine (.atom "a" "q") (.atom "b" "q")) (.atom "c" "q")

theorem rightAssoc_pure : PureEvidence rightAssoc :=
  .combine (.atom "a" "q") (.combine (.atom "b" "q") (.atom "c" "q"))

/-- The two root partitions really differ, even though their flattened
state/query pair multisets coincide. -/
theorem rootGroups_assoc_distinct :
    rootGroups leftAssoc ≠ rootGroups rightAssoc := by
  intro equal
  have groupEqual :
      ({evidenceNormalForm (.combine a b), evidenceNormalForm c} :
        Multiset (Multiset (String × String))) =
      ({evidenceNormalForm a, evidenceNormalForm (.combine b c)} :
        Multiset (Multiset (String × String))) := by
    simpa only [rootGroups, leftAssoc, rightAssoc, Option.some.injEq] using equal
  have cMember : evidenceNormalForm c ∈
      ({evidenceNormalForm (.combine a b), evidenceNormalForm c} :
        Multiset (Multiset (String × String))) := by simp
  rw [groupEqual] at cMember
  simp [a, b, c, evidenceNormalForm, stateNormalForm, queryName] at cMember

theorem normalForm_assoc_equal :
    evidenceNormalForm leftAssoc = evidenceNormalForm rightAssoc := by
  simp only [leftAssoc, rightAssoc, a, b, c, evidenceNormalForm,
    stateNormalForm, queryName, Multiset.map_singleton]
  ac_rfl

/-- Associativity is valid in every lawful reading but cannot be realized
by contextual execution in either direction for these closed terms. -/
theorem semantic_assoc_not_contextually_reachable :
    (∀ (State Query V : Type) (R : WMReading State Query V),
      R.CoreLaws → R.denote leftAssoc = R.denote rightAssoc) ∧
    ¬ WMContextStepStar leftAssoc rightAssoc ∧
    ¬ WMContextStepStar rightAssoc leftAssoc := by
  refine ⟨(allReadingsAgree_iff_normalForm_eq
    leftAssoc rightAssoc).2 normalForm_assoc_equal, ?_, ?_⟩
  · intro steps
    exact rootGroups_assoc_distinct
      (pure_contextStepStar_invariant leftAssoc_pure steps).2
  · intro steps
    exact rootGroups_assoc_distinct
      (pure_contextStepStar_invariant rightAssoc_pure steps).2.symm

end Mettapedia.OSLF.Framework.WMCalculusRewriteCompletenessBoundary
