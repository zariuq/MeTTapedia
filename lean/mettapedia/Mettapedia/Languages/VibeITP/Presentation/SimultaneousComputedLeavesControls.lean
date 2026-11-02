import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofControls

/-! Concrete computed leaves and mixed certificates for the supplied v2 guest.
Finite execution supplies each leaf's fuel. Numerical runtime calibration
allowances remain in the separate executable request panel. -/
set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2.Controls
open ComputationalData ComputationalShift ComputationalProofs
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem crossing_runs : ∃ fuel,
    (authoredComputation Primary.hosted).runs ⟨crossingWitness, Primary.crossing, fuel⟩ = true := by
  obtain ⟨fuel, enough⟩ := (authoredComputation Primary.hosted).runs_of_relation
    ((SimultaneousProofs.Witness.check_iff _ _ _).mp crossing_checked)
  exact ⟨fuel, enough fuel le_rfl⟩

theorem crossing_leaf_checked :
    ∃ fuel, InferenceComputedLeaves.check (SimultaneousPresentation.validatedV2 Primary.theory Primary.allocated)
      (qualification Primary.hosted).computation.evaluate (jThm (encTerm Primary.theory.sig Primary.crossing))
      (.computed ⟨crossingWitness, Primary.crossing, fuel⟩) = true :=
  checked_witness_has_leaf Primary.hosted ((SimultaneousProofs.Witness.check_iff _ _ _).mp crossing_checked)

theorem crossing_leaf_derives : Spec.DerivesV2 Primary.theory Primary.crossing := by
  obtain ⟨_, accepted⟩ := crossing_leaf_checked
  exact (supplied_leaf_derives Primary.hosted accepted).2.1

theorem crossing_has_expanded_article : ∃ article,
    checkRaw (SimultaneousPresentation.validatedV2 Primary.theory Primary.allocated)
      (jThm (encTerm Primary.theory.sig Primary.crossing)) article = true := by
  obtain ⟨_, accepted⟩ := crossing_leaf_checked
  exact accepted_has_replay (qualification Primary.hosted).computation accepted

theorem crossing_scope_exact :
    (∃ proof, InferenceComputedLeaves.check
      (SimultaneousPresentation.validatedV2 Primary.theory Primary.allocated)
      (qualification Primary.hosted).computation.evaluate
      (jThm (encTerm Primary.theory.sig Primary.crossing)) proof = true) ↔
    ∃ article, checkRaw (SimultaneousPresentation.validatedV2 Primary.theory Primary.allocated)
      (jThm (encTerm Primary.theory.sig Primary.crossing)) article = true :=
  scope_exact Primary.hosted _

theorem unformed_shadow_has_no_leaf (answer : Spec.Term) (fuel : Nat)
    (goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    InferenceComputedLeaves.check (SimultaneousPresentation.validatedV2 Primary.theory Primary.allocated)
      (qualification Primary.hosted).computation.evaluate goal
      (.computed ⟨unformedShadow, answer, fuel⟩) = false := by
  apply (qualification Primary.hosted).refused_no_leaf
  exact (SimultaneousProofs.Witness.result_none_iff _ _).mp (by decide +kernel)

private abbrev D := SimultaneousPresentation.validatedV2 KernelControls.controlTheory 4
private abbrev E := (qualification KernelControls.controlTheory_hosted).computation.evaluate
private def implicationGoal := jThm (encTerm KernelControls.controlTheory.sig (.impl KernelControls.atomA KernelControls.atomB))
private def premiseGoal := jThm (encTerm KernelControls.controlTheory.sig KernelControls.atomA)
private def conclusionGoal := jThm (encTerm KernelControls.controlTheory.sig KernelControls.atomB)

private theorem root_instantiated : instantiateRule? D ⟨⟨rMp.id⟩, KernelControls.mpArguments⟩ =
    some ([implicationGoal, premiseGoal], conclusionGoal) := by decide +kernel

def mixedProofAt (firstFuel secondFuel : Nat) : CompactProof (Leaf SimultaneousProofs.Witness Spec.Term) :=
  .node ⟨⟨rMp.id⟩, KernelControls.mpArguments⟩
    [.computed { implicationLeaf with fuel := firstFuel }, .computed { premiseLeaf with fuel := secondFuel }]

theorem mixed_proof_checked : ∃ firstFuel secondFuel,
    InferenceComputedLeaves.check D E conclusionGoal (mixedProofAt firstFuel secondFuel) = true := by
  have implicationChecked : SimultaneousProofs.Witness.Checks KernelControls.controlTheory
      implicationLeaf.query implicationLeaf.answer :=
    (SimultaneousProofs.Witness.check_iff _ _ _).mp (by decide +kernel)
  have premiseChecked : SimultaneousProofs.Witness.Checks KernelControls.controlTheory
      premiseLeaf.query premiseLeaf.answer :=
    (SimultaneousProofs.Witness.check_iff _ _ _).mp (by decide +kernel)
  obtain ⟨firstFuel, first⟩ := checked_witness_has_leaf KernelControls.controlTheory_hosted implicationChecked
  obtain ⟨secondFuel, second⟩ := checked_witness_has_leaf KernelControls.controlTheory_hosted premiseChecked
  change check D E implicationGoal (.computed { implicationLeaf with fuel := firstFuel }) = true at first
  change check D E premiseGoal (.computed { premiseLeaf with fuel := secondFuel }) = true at second
  refine ⟨firstFuel, secondFuel, ?_⟩
  rw [mixedProofAt, check, root_instantiated]
  simp only [decide_true, Bool.true_and, checkChildren]
  exact Bool.and_eq_true_iff.mpr ⟨first, Bool.and_eq_true_iff.mpr ⟨second, rfl⟩⟩

theorem mixed_proof_source_derives : Spec.DerivesV2 KernelControls.controlTheory KernelControls.atomB := by
  obtain ⟨_, _, accepted⟩ := mixed_proof_checked
  exact mixed_proof_derives KernelControls.controlTheory_hosted accepted

theorem reversed_computed_children_refused (firstFuel secondFuel : Nat) :
    InferenceComputedLeaves.check D E conclusionGoal
      (.node ⟨⟨rMp.id⟩, KernelControls.mpArguments⟩
        [.computed { premiseLeaf with fuel := firstFuel }, .computed { implicationLeaf with fuel := secondFuel }]) = false := by
  have wrong : check D E implicationGoal (.computed { premiseLeaf with fuel := firstFuel }) = false := by
    cases accepted : check D E implicationGoal (.computed { premiseLeaf with fuel := firstFuel }) with
    | false => rfl
    | true =>
        have same := (supplied_leaf_exact KernelControls.controlTheory_hosted _ _).mp accepted |>.2
        have different : implicationGoal ≠ jThm (encTerm KernelControls.controlTheory.sig premiseLeaf.answer) := by decide +kernel
        exact False.elim (different same)
  rw [check, root_instantiated]
  simp only [decide_true, Bool.true_and, checkChildren, wrong, Bool.false_and]

#print axioms crossing_leaf_derives
#print axioms mixed_proof_source_derives
end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2.Controls
