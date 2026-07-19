/-
# Root-parametric certified pruning

Semantic pruning is stated over a search node `(budget, prefix, state)`, not a
bare root state.  This is necessary because the sealed refinement interface
decodes complete traces: it does not assert that `State` alone determines the
completed program.  A node remains proof-free and executable; reachability is
part of the completion proposition.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.AtomicRefinement

namespace Mettapedia.GSLT.LanguageDef.CertifiedMask

open Mettapedia.GSLT.LanguageDef.RefinementInterface

universe uState uHole uAction uProgram

/-- Policy-visible state together with the trace and budget that produced it. -/
structure SearchNode (root : RefinementInterface) where
  budget : Nat
  actions : List root.Action
  state : root.State

namespace SearchNode

variable {root : RefinementInterface}

/-- The stored state is the actual result of the stored prefix. -/
def Reached (node : SearchNode root) : Prop :=
  root.run node.actions (root.initial node.budget) = some node.state

/-- A program completes this exact search node through the root decoder. -/
def Completes (node : SearchNode root) (program : root.Program) : Prop :=
  node.Reached ∧
    ∃ suffix, root.Accepts node.budget (node.actions ++ suffix) program

/-- A completion satisfying the property licensed for hard pruning. -/
def HasPropertyCompletion (property : root.Program → Prop)
    (node : SearchNode root) : Prop :=
  ∃ program, node.Completes program ∧ property program

/-- Ideal semantic pruning: every actual completion violates the property. -/
def SemanticallyPrunable (property : root.Program → Prop)
    (node : SearchNode root) : Prop :=
  ∀ program, node.Completes program → ¬ property program

theorem semanticallyPrunable_iff_no_propertyCompletion
    {property : root.Program → Prop} {node : SearchNode root} :
    node.SemanticallyPrunable property ↔
      ¬ node.HasPropertyCompletion property := by
  constructor
  · intro hprunable hcompletion
    rcases hcompletion with ⟨program, hcompletes, hproperty⟩
    exact hprunable program hcompletes hproperty
  · intro hnone program hcompletes hproperty
    exact hnone ⟨program, hcompletes, hproperty⟩

/-- Classical converse used only to characterize survivors of the ideal mask. -/
theorem not_semanticallyPrunable_iff_hasPropertyCompletion
    {property : root.Program → Prop} {node : SearchNode root} :
    ¬ node.SemanticallyPrunable property ↔
      node.HasPropertyCompletion property := by
  classical
  rw [semanticallyPrunable_iff_no_propertyCompletion]
  exact not_not

/-- Any accepted completion of a node is an ordinary state completion. -/
theorem Completes.hasCompletion {node : SearchNode root}
    {program : root.Program} (hcompletes : node.Completes program) :
    root.HasCompletion node.state := by
  rcases hcompletes with ⟨hreached, suffix, finalState, hrun, hterminal, _hdecode⟩
  rw [root.run_append, hreached] at hrun
  exact ⟨suffix, finalState, hrun, hterminal⟩

end SearchNode

/-- A completed-program rejection theorem, ready to be lifted to search nodes. -/
structure CertifiedProgramRejector {Program : Type uProgram}
    (property : Program → Prop) where
  rejects : Program → Prop
  sound : ∀ program, rejects program → ¬ property program

/-- Lift a program rejection predicate through every completion of a node. -/
def liftProgramRejector {root : RefinementInterface}
    {property : root.Program → Prop}
    (certificate : CertifiedProgramRejector property)
    (node : SearchNode root) : Prop :=
  ∀ program, node.Completes program → certificate.rejects program

/-- T1 crown: a certified completed-program rejection lifts to state pruning. -/
theorem liftProgramRejector_semanticallyPrunable
    {root : RefinementInterface} {property : root.Program → Prop}
    (certificate : CertifiedProgramRejector property)
    {node : SearchNode root}
    (hlifted : liftProgramRejector certificate node) :
    node.SemanticallyPrunable property := by
  intro program hcompletes
  exact certificate.sound program (hlifted program hcompletes)

/-- A hard mask is licensed exactly when every selected node is semantically prunable. -/
def CertifiedHardMask {root : RefinementInterface}
    (property : root.Program → Prop) (hardMask : SearchNode root → Prop) : Prop :=
  ∀ node, hardMask node → node.SemanticallyPrunable property

/-- Recall safety means no property-satisfying completion lies under a pruned node. -/
def RecallSafe {root : RefinementInterface}
    (property : root.Program → Prop) (hardMask : SearchNode root → Prop) : Prop :=
  ∀ node program,
    node.Completes program → property program → ¬ hardMask node

/-- T3 hard boundary: recall safety is equivalent to certification, not merely implied by it. -/
theorem hardMask_recallSafe_iff_certified
    {root : RefinementInterface} {property : root.Program → Prop}
    {hardMask : SearchNode root → Prop} :
    RecallSafe property hardMask ↔ CertifiedHardMask property hardMask := by
  constructor
  · intro hsafe node hmask program hcompletes hproperty
    exact hsafe node program hcompletes hproperty hmask
  · intro hcertified node program hcompletes hproperty hmask
    exact hcertified node hmask program hcompletes hproperty

/-- A Boolean test is a sound sufficient condition for semantic pruning. -/
structure CertifiedStateTest {root : RefinementInterface}
    (property : root.Program → Prop) where
  test : SearchNode root → Bool
  sound : ∀ node, test node = true → node.SemanticallyPrunable property

namespace CertifiedStateTest

variable {root : RefinementInterface} {property : root.Program → Prop}

/-- Completeness is optional: a sound test may conservatively retain unknown nodes. -/
def Complete (stateTest : CertifiedStateTest property) : Prop :=
  ∀ node, node.SemanticallyPrunable property → stateTest.test node = true

/-- A property completion is never removed by a sound sufficient test. -/
theorem false_of_hasPropertyCompletion (stateTest : CertifiedStateTest property)
    {node : SearchNode root} (hcompletion : node.HasPropertyCompletion property) :
    stateTest.test node = false := by
  cases htest : stateTest.test node with
  | false => rfl
  | true =>
      exfalso
      exact (SearchNode.semanticallyPrunable_iff_no_propertyCompletion.mp
        (stateTest.sound node htest)) hcompletion

/-- Only a complete test may read `false` as evidence of a property completion. -/
theorem false_iff_hasPropertyCompletion_of_complete
    (stateTest : CertifiedStateTest property) (hcomplete : stateTest.Complete)
    {node : SearchNode root} :
    stateTest.test node = false ↔ node.HasPropertyCompletion property := by
  constructor
  · intro hfalse
    classical
    by_contra hnone
    have hprunable : node.SemanticallyPrunable property :=
      SearchNode.semanticallyPrunable_iff_no_propertyCompletion.mpr hnone
    rw [hcomplete node hprunable] at hfalse
    contradiction
  · exact stateTest.false_of_hasPropertyCompletion

end CertifiedStateTest

/-- Every prefix state retained by a hard mask along one accepted trace. -/
def EveryPrefixRetained {root : RefinementInterface}
    (hardMask : SearchNode root → Prop) (budget : Nat)
    (trace : List root.Action) : Prop :=
  ∀ before after state,
    trace = before ++ after →
    root.run before (root.initial budget) = some state →
      ¬ hardMask { budget := budget, actions := before, state := state }

/-- T1 trace recall: certified state pruning preserves every accepted property trace. -/
theorem certifiedHardMask_preserves_accepted_trace
    {root : RefinementInterface} {property : root.Program → Prop}
    {hardMask : SearchNode root → Prop}
    (hcertified : CertifiedHardMask property hardMask)
    {budget : Nat} {trace : List root.Action} {program : root.Program}
    (haccepts : root.Accepts budget trace program)
    (hproperty : property program) :
    EveryPrefixRetained hardMask budget trace := by
  intro before after state htrace hrun hmask
  apply hcertified { budget := budget, actions := before, state := state } hmask
      program ⟨hrun, after, ?_⟩ hproperty
  simpa [htrace] using haccepts

/-! ## Exact interaction with no-dead-ends -/

/-- A survivor of the ideal semantic mask has a property completion, hence a completion. -/
theorem idealSurvivor_hasCompletion
    {root : RefinementInterface} {property : root.Program → Prop}
    {node : SearchNode root}
    (hsurvives : ¬ node.SemanticallyPrunable property) :
    root.HasCompletion node.state := by
  rcases SearchNode.not_semanticallyPrunable_iff_hasPropertyCompletion.mp hsurvives with
    ⟨program, hcompletes, _hproperty⟩
  exact hcompletes.hasCompletion

/-- The true sufficient-test guarantee: nodes on certified solutions survive. -/
theorem certifiedStateTest_preserves_property_path
    {root : RefinementInterface} {property : root.Program → Prop}
    (stateTest : CertifiedStateTest property)
    {node : SearchNode root} {program : root.Program}
    (hcompletes : node.Completes program) (hproperty : property program) :
    stateTest.test node = false :=
  stateTest.false_of_hasPropertyCompletion ⟨program, hcompletes, hproperty⟩

/-! ## Soft ranking boundary -/

/--
T3 soft boundary (compatibility restatement): changing scores or order while
listing exactly the legal actions cannot change accepted traces.
-/
theorem softRanking_always_safe {root : RefinementInterface}
    (laws : RefinementLaws root)
    (ranking : root.State → List root.Action)
    (hcoverage : root.ListsAllLegalActions ranking)
    {budget : Nat} {trace : List root.Action} {program : root.Program} :
    root.RankedAccepts ranking budget trace program ↔
      root.Accepts budget trace program :=
  laws.rankedAccepts_iff_accepts ranking hcoverage

#print axioms SearchNode.semanticallyPrunable_iff_no_propertyCompletion
#print axioms liftProgramRejector_semanticallyPrunable
#print axioms hardMask_recallSafe_iff_certified
#print axioms certifiedHardMask_preserves_accepted_trace
#print axioms idealSurvivor_hasCompletion
#print axioms softRanking_always_safe

end Mettapedia.GSLT.LanguageDef.CertifiedMask
