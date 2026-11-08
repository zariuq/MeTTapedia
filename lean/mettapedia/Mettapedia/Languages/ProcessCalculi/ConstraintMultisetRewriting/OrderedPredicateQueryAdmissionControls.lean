import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedPredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffectsControls

/-! # A reversed complete scanner preserves the bag but invalidates order -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedPredicateQueryAdmission.Controls

open Mettapedia.Logic.LP
open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature A)
open StagedSourceEffects.Controls (label)

def before : Configuration (Term signature) Nat := ⟨[], {0, 1}⟩
def kept : Commit Nat (Term signature) := ⟨∅, {0, 1}, ∅, []⟩
def program : ReadOnlyQuery.Program (Term signature → Bool) (List Nat) (List Nat) :=
  .read (fun _ => true) (fun seen => .pure seen)
def original := Sources.Query.scanList label [0, 1]
def reversed := Sources.Query.scanList label [1, 0]
def query : PredicateQuery Nat (Term signature) := ⟨fun _ => true, {0, 1}⟩

theorem both_providers_are_complete :
    Sources.Query.Complete label before.present original ∧ Sources.Query.Complete label before.present reversed := by
  constructor
  · exact Sources.Query.scanList_complete label [0, 1] (by decide +kernel)
  · have same : ([1, 0] : List Nat).toFinset = before.present := by decide +kernel
    rw [← same]
    exact Sources.Query.scanList_complete label [1, 0] (by decide +kernel)

theorem admitted_in_the_observed_order :
    Valid A label (CensusSourceCompilation.rule label kept []) [] before
      (CensusSourceCompilation.selection kept) program original original := by
  refine ⟨?_, both_providers_are_complete.1, ReadOnlyQuery.run_agrees original program⟩
  exact CensusSourceCompilation.realize_commit A label kept [] before (by decide +kernel)
    ⟨A.identity, by intro equation member; cases member⟩

theorem reordering_preserves_the_unordered_census :
    (original (fun _ => true)).toFinset = (reversed (fun _ => true)).toFinset ∧ query.Holds label before.present := by
  decide +kernel

theorem reordering_changes_the_answer :
    (ReadOnlyQuery.run original program).answer = [0, 1] ∧
      (ReadOnlyQuery.run reversed program).answer = [1, 0] := by
  decide +kernel

theorem the_order_certificate_refuses_reversal :
    ReadOnlyQuery.checkReads reversed (ReadOnlyQuery.run original program).reads = false := by
  decide +kernel

theorem a_bag_census_does_not_admit_reversed_order :
    ¬ Valid A label (CensusSourceCompilation.rule label kept []) [] before
      (CensusSourceCompilation.selection kept) program original reversed := by
  intro valid
  have checked := valid.checked
  rw [the_order_certificate_refuses_reversal] at checked
  cases checked

theorem ordered_admission_retains_its_read_census :
    PredicateQueryAdmission.Valid A label (CensusSourceCompilation.rule label kept [])
      (readCensuses (ReadOnlyQuery.run original program).reads) before (CensusSourceCompilation.selection kept) :=
  admitted_in_the_observed_order.with_read_censuses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedPredicateQueryAdmission.Controls
