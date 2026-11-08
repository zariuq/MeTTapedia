import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsExec

/-!
# MM2's complete snapshot and set update in one admitted firing

The MM2 comparator already constructs the combined removal and insertion
lists from its independently specified complete snapshot. Here that same
firing additionally validates the snapshot as a predicate query at admission.
An added occurrence invalidates the retained census, even if the old five
ports still allow the ground update.

The configuration here represents the one space passed to the MM2 operation.
Its full-region census is conservative: an indexed implementation can use a
smaller sufficient region only with the corresponding source-locality proof.
This does not require copying rows, choose a storage layout, or turn all
spaces in an agent into a single observation domain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusMM2

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MetaMeTTaComparison (atomAction)
open MeTTaOperationsExec

variable {O : Type*} [DecidableEq O]

def snapshot (world : Finset O) : PredicateQuery O Atom := ⟨fun _ => true, world⟩

omit [DecidableEq O] in
theorem snapshot_holds (label : O → Atom) (world : Finset O) :
    (snapshot world).Holds label world := by
  simp only [PredicateQuery.Holds, snapshot, regionOf, Finset.filter_true]

theorem complete_exec_is_one_firing {label : O → Atom} {before : Configuration Atom O}
    {space : Finset Atom} {exec : Exec} (covered : Covered exec)
    (represents : before.present.image label = space) (injective : Set.InjOn label before.present)
    {selfOcc : O} (selfPresent : selfOcc ∈ before.present) (selfLabel : label selfOcc = exec.self)
    (supply : ∀ (avoid : Finset O) (atom : Atom), ∃ made, made ∉ avoid ∧ label made = atom)
    (base : atomAction.Consistent before.equations) :
    ∃ removed : List O, ∃ added : List Atom, ∃ made : List O,
      PredicateQueryAdmission.Valid atomAction label (stepRule label (selfOcc :: removed) added)
        [PredicateQueryAdmission.Query.fixed (snapshot before.present)] before
        (stepSelection (selfOcc :: removed) made) ∧
      Result space exec (((stepSelection (selfOcc :: removed) made).result label
        (stepRule label (selfOcc :: removed) added) before).present.image label) := by
  obtain ⟨removed, added, made, valid, exactResult⟩ :=
    exec_is_one_firing covered represents injective selfPresent selfLabel supply base
  refine ⟨removed, added, made, ?_, exactResult⟩
  exact (PredicateQueryAdmission.valid_fixed_iff _ _ _ [snapshot before.present] _ _).mpr
    ⟨valid, fun query member => (List.mem_singleton.mp member) ▸ snapshot_holds label before.present⟩

theorem arrival_invalidates_snapshot (label : O → Atom) (world : Finset O) (newOccurrence : O)
    (fresh : newOccurrence ∉ world) :
    ¬ (snapshot world).Holds label (insert newOccurrence world) := by
  intro holds
  have inSeen : newOccurrence ∈ regionOf label (insert newOccurrence world) (snapshot world).region := by
    simp only [snapshot, regionOf, Finset.filter_true, Finset.mem_insert, true_or]
  rw [holds] at inSeen
  exact fresh inSeen

/-- The census is checked at the original source cut, not on the result
after the operation has consumed its own exec atom and removal targets. -/
theorem p5_with_complete_admission :
    PredicateQueryAdmission.Valid atomAction Probe.label5
      (stepRule Probe.label5 [3, 2] [Probe.pair "r" Probe.one, Probe.pair "r" Probe.two])
      [PredicateQueryAdmission.Query.fixed (snapshot Probe.before5.present)] Probe.before5
      (stepSelection [3, 2] [4, 5]) ∧
    Result Probe.space5 Probe.exec5
      (((stepSelection [3, 2] [4, 5]).result Probe.label5
        (stepRule Probe.label5 [3, 2] [Probe.pair "r" Probe.one, Probe.pair "r" Probe.two])
        Probe.before5).present.image Probe.label5) := by
  obtain ⟨valid, exactResult⟩ := Probe.p5_one_firing
  refine ⟨?_, ?_⟩
  swap
  · rw [exactResult]
    exact Probe.result5_reference
  exact (PredicateQueryAdmission.valid_fixed_iff _ _ _ [snapshot Probe.before5.present] _ _).mpr
    ⟨valid, fun query member => (List.mem_singleton.mp member) ▸ snapshot_holds Probe.label5 Probe.before5.present⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusMM2
