import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestResolution

/-!
# Data-only request soundness needs only its selected occurrences

The exact source receipt restricts to its actual take/read footprint. Its
assignment, shared reads, outputs and finite data computation are retained;
only the irrelevant query snapshot is recomputed on the smaller world.

This theorem concerns request recipes whose condition reads finite supplied
data, not arbitrary absence/count or world-dependent guards.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DataRequestFootprint

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open RequestActivation

variable {V Head P : Type} {O : Type*} [DecidableEq O]

def gathers (receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head)) : Finset O :=
  receipt.takes.toFinset ∪ receipt.reads.toFinset

noncomputable def restrict (layer : TermLayer V (Term Head) P) (recipe : Recipe V Head P)
    (label : O → Term Head) (receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head)) :
    GuardedMultisetRewriting.FiringReceipt O V (Term Head) :=
  ⟨receipt.assignment, receipt.takes, receipt.reads, receipt.outputs,
    [regionOf label (gathers receipt) (semRegion layer receipt.assignment recipe.request)]⟩

theorem gathers_subset {layer : TermLayer V (Term Head) P} {recipe : Recipe V Head P}
    {label : O → Term Head} {receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head)}
    {world : Finset O} (qualified : receipt.ValidAt layer recipe.matchingRule label world) : gathers receipt ⊆ world :=
  Finset.union_subset qualified.takesPresent qualified.readsPresent

theorem restrict_valid {layer : TermLayer V (Term Head) P} {recipe : Recipe V Head P}
    {label : O → Term Head} {receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head)}
    {world : Finset O} (qualified : receipt.ValidAt layer recipe.matchingRule label world) :
    (restrict layer recipe label receipt).ValidAt layer recipe.matchingRule label (gathers receipt) := by
  refine ⟨qualified.uniqueTakes, qualified.uniqueOutputs, Finset.subset_union_left, Finset.subset_union_right,
    qualified.apart, ?_, qualified.binds, qualified.takesMatch, qualified.readsMatch, qualified.makes, ?_⟩
  · exact Finset.disjoint_of_subset_right (gathers_subset qualified) qualified.fresh
  · refine .cons ⟨rfl, ?_⟩ .nil
    exact qualified.checks_hold ⟨recipe.request, fun assignment _ => recipe.dataCondition assignment = true⟩
      (by simp [Recipe.matchingRule, GuardedMultisetRewriting.requestRule])

theorem selected_step [DecidableEq Head]
    {layer : TermLayer V (Term Head) P} {recipe : Recipe V Head P}
    {label : O → Term Head} {receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head)}
    {world : Finset O} (qualified : receipt.ValidAt layer recipe.matchingRule label world) :
    GuardedMultisetRewriting.Step layer recipe.matchingRule (labels label (gathers receipt))
      (labels label (fire (gathers receipt) ((restrict layer recipe label receipt).commit layer recipe.matchingRule))) :=
  (restrict_valid qualified).step

theorem made_in_selected_destination
    {layer : TermLayer V (Term Head) P} {recipe : Recipe V Head P}
    {label : O → Term Head} {receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head)}
    {occurrence : O} (made : occurrence ∈ receipt.outputs) :
    occurrence ∈ fire (gathers receipt) ((restrict layer recipe label receipt).commit layer recipe.matchingRule) := by
  apply mem_fire.mpr
  right
  simpa only [restrict, GuardedMultisetRewriting.FiringReceipt.commit, List.mem_toFinset] using made

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DataRequestFootprint
