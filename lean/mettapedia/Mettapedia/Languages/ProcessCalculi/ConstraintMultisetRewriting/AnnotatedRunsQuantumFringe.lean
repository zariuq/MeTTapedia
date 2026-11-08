import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantumAttention
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeRulesControls

/-!
# With identities kept, the dark fringe of the amplitude controls is a recorded pair

`AnnotatedRunsAmplitudeRulesControls.Fringe.dark_fringe` has three superposed alternatives: two of
amplitudes `1` and `-1` end in the outcome `yes`, one of amplitude `1` in `no`. The coherent sum
`Z_yes` vanishes, so the Born probability of `yes` computed from `Z_yes` and `Z_no` is `0`.

The two `yes` alternatives make the answer rows `20` and `21`, so they end in different
configuration classes: each made row is a record. The record-respecting readout therefore adds
their Born weights (`yes_recorded`, `dark_fringe_recorded`): `yes` reads `2`, `no` reads `1`, and
the probability of `yes` is `2/3`, the incoherent value. A dark fringe needs the two routes to
reach one state, as the quiet pair of `AnnotatedRunsQuantumAttention` does.

This is the identity-observing end. The nominal end (`AmplitudeRuns.nominalEnd`) renames occurrence
identities that no observation has seen; under it the two `yes` histories share an end and the
fringe is dark (`AggregationControls.Superposed.nominal_interferes` for the same pair).

The same alternatives are not certified for attention (`superposed_not_one_end`): their attention
collection is incomplete (`superposed_attention_uncertified`), so the gather the controls call
incomplete is the one they get, and the commit is refused at every cut, where the certified guard
after a complete gather fires (`honest_commit_refuses_recorded`). The quiet pair, whose routes reach
one state, is certified: its status gather is the complete gather, the commit fires, and it
certifies a readout of `0` (`quiet_commit_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

namespace QuantumFringe

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label)
open MeTTaCalculus.OccurrenceCommits (regionOf)
open AnnotatedRunUnfolding (CausalClass)
open AnnotatedRunBranchCollection.Controls.Superpose (root first second alternatives branches)
open AmplitudeControls (everything regionBranches_everything)
open AmplitudeControls.Superposed (shifted alternatives₃ superposed_cancel)
open WaveControls (Run waveLabel wave region row bits statusBits pathRow incompleteGather
  completeGather completeGather_valid encodes afterComplete afterComplete_consistent
  complete_published_fires incomplete_published_refused)
open WaveControls.Fringe (yesOutcome noOutcome yes_branches no_branches yes_paths no_paths)
open Attention.Recorded (superposed_ends_differ)

/-- **The `yes` alternatives of the dark fringe are recorded**: they reach different
configuration classes. -/
theorem yes_recorded :
    Set.InjOn (classEnd A label root) (regionBranches A label alternatives₃ 1 root yesOutcome) := by
  rw [yes_branches]
  intro x inX y inY same
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at inX inY
  rcases inX with rfl | rfl <;> rcases inY with rfl | rfl
  · rfl
  · exact absurd same superposed_ends_differ
  · exact absurd same.symm superposed_ends_differ
  · rfl

theorem no_recorded :
    Set.InjOn (classEnd A label root) (regionBranches A label alternatives₃ 1 root noOutcome) := by
  rw [no_branches, Finset.coe_singleton]
  exact Set.injOn_singleton _ _

/-- **The dark fringe, read with its records.** The coherent probability of `yes` is `0`; the
record-respecting readouts of `yes` and `no` are `2` and `1`, so the probability of `yes` is
`2/3`. -/
theorem dark_fringe_recorded :
    bornProbability (regionalAmplitude A label shifted alternatives₃ 1 root yesOutcome)
        (regionalAmplitude A label shifted alternatives₃ 1 root noOutcome) = 0 ∧
      branchReadout A label shifted alternatives₃ 1 root yesOutcome = 2 ∧
      branchReadout A label shifted alternatives₃ 1 root noOutcome = 1 ∧
      branchReadout A label shifted alternatives₃ 1 root yesOutcome /
          (branchReadout A label shifted alternatives₃ 1 root yesOutcome +
            branchReadout A label shifted alternatives₃ 1 root noOutcome) = 2 / 3 := by
  have yes : branchReadout A label shifted alternatives₃ 1 root yesOutcome = 2 := by
    rw [branchReadout_of_recorded A label shifted yes_recorded, yes_paths, incoherent_pair,
      born_neg, born_one]
    norm_num
  have no : branchReadout A label shifted alternatives₃ 1 root noOutcome = 1 := by
    rw [branchReadout_of_recorded A label shifted no_recorded, no_paths]
    simp [incoherent]
  refine ⟨WaveControls.Fringe.dark_fringe.2.2.2.2.2.1, yes, no, ?_⟩
  rw [yes, no]
  norm_num

open Classical in
/-- **The superposed alternatives are not certified for attention**: their routes reach two
configuration classes. -/
theorem superposed_not_one_end : ¬ Attention.OneEnd A label alternatives 1 root everything := by
  rintro ⟨e, shared⟩
  have inFirst : (Quot.mk _ [first] : CausalClass A label root) ∈
      regionBranches A label alternatives 1 root everything := by
    rw [regionBranches_everything, branches]
    exact Finset.mem_insert_self _ _
  have inSecond : (Quot.mk _ [second] : CausalClass A label root) ∈
      regionBranches A label alternatives 1 root everything := by
    rw [regionBranches_everything, branches]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact superposed_ends_differ ((shared _ inFirst).trans (shared _ inSecond).symm)

theorem superposed_attention_uncertified :
    Attention.attentionCollection A label shifted alternatives 1 root everything =
      .incomplete {1, -1} := by
  classical
  unfold Attention.attentionCollection
  rw [if_neg fun both => superposed_not_one_end both.2, superposed_cancel.1]

/-- **The honest commit refuses the recorded pair.** The certified guard of the amplitude controls
fires after the superposed alternatives are gathered as a complete collection. Gathered as their
attention collection, which is not certified because the alternatives are recorded, the gather is
the incomplete gather of those controls, and the commit is refused at every cut. -/
theorem honest_commit_refuses_recorded :
    (certifiedCancellationFiring A waveLabel wave statusBits bits row region
        (regionOf waveLabel afterComplete.present region) 33 40 : Run).Valid A waveLabel
        afterComplete ∧
      statusGatherFiring A statusBits
          (Attention.attentionCollection A label shifted alternatives 1 root everything) pathRow
          [1, -1] [30, 31] 34 = incompleteGather ∧
      ∀ (seen : Finset Nat) (r : Nat) (D : Configuration (Term signature) Nat),
        ¬ (certifiedCancellationFiring A waveLabel wave statusBits bits row region seen 34 r :
          Run).Valid A waveLabel D := by
  refine ⟨complete_published_fires, ?_, incomplete_published_refused.2.2⟩
  rw [superposed_attention_uncertified]
  rfl

/-- **The honest commit fires on the quiet pair, end to end.** The attention collection of the two
unrecorded routes out of phase is complete; gathered with its status, it is the complete gather of
the controls; the commit fires there, and by `commit_sound` it certifies that the record-respecting
readout of the routes is `0` over every terminal causal history. -/
theorem quiet_commit_fires :
    Attention.attentionCollection A label Attention.QuietPair.phase Attention.QuietPair.routes 1 root
        everything = .complete {1, -1} ∧
      statusGatherFiring A statusBits
          (Attention.attentionCollection A label Attention.QuietPair.phase
            Attention.QuietPair.routes 1 root everything) pathRow [1, -1] [30, 31] 33 =
        completeGather ∧
      (certifiedCancellationFiring A waveLabel wave statusBits bits row region
          (regionOf waveLabel afterComplete.present region) 33 40 : Run).Valid A waveLabel
          afterComplete ∧
      branchReadout A label Attention.QuietPair.phase Attention.QuietPair.routes 1 root
        everything = 0 := by
  have complete : Attention.attentionCollection A label Attention.QuietPair.phase
      Attention.QuietPair.routes 1 root everything = .complete {1, -1} :=
    (Attention.attentionCollection_eq_complete_iff A label Attention.QuietPair.phase {1, -1}).mpr
      ⟨Attention.QuietPair.routes_closed, Attention.QuietPair.routes_one_end,
        Attention.QuietPair.routes_cancel.1.symm⟩
  have certified := Attention.commit_sound A waveLabel wave complete rfl completeGather_valid
    (by decide) encodes rfl (by decide) (by simp [row, waveLabel]) afterComplete_consistent
    complete_published_fires
  refine ⟨complete, ?_, complete_published_fires, certified.1⟩
  rw [complete]
  rfl

end QuantumFringe

end AmplitudeRuns

open AmplitudeRuns.QuantumFringe

#print axioms yes_recorded
#print axioms no_recorded
#print axioms dark_fringe_recorded
#print axioms superposed_not_one_end
#print axioms superposed_attention_uncertified
#print axioms honest_commit_refuses_recorded
#print axioms quiet_commit_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
