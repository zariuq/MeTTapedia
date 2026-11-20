import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceProofSuffix
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.RegisteredProofBlocksControls

/-! An actual native-source prefix earns a further cache entry in one carried
interpretation. Equal declaration contexts alone do not supply that entry in
the earlier cache. -/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics SourceProfileModels
open RegisteredProofBlocks
open RegisteredProofBlocks.Controls

universe w

theorem first_replayed : Registered.replayFrom SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext) [SourcePrefix.truthCommand] = some SourcePrefix.withTruth := by
  simp only [Registered.replayFrom, SourcePrefix.truth_applied, bind, Option.bind]

def nodes : List Receipt := (GraphExpansion.expandBlock [] SourcePrefix.withTruth.cache.size SourcePrefix.reflBlock).1

theorem suffix_replayed : Registered.replayFrom SourceProfileModels.policy SourcePrefix.withTruth
    (commands SourcePrefix.instances nodes) = some SourcePrefix.received :=
  relocated_replay SourceProfileModels.policy SourcePrefix.withTruth SourcePrefix.instances [] [] SourcePrefix.reflexivity
    SourcePrefix.reflBlock rfl SourcePrefix.refl_block_checked SourcePrefix.refl_formed

def frame : ProfileFrame.{w} SourcePrefix.withTruth :=
  sourceReplayFrame [SourcePrefix.truthCommand] SourcePrefix.withTruth first_replayed

def carried : ProfileFrame.{w} SourcePrefix.received :=
  carry frame SourcePrefix.instances nodes suffix_replayed

theorem actual_model_retained (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    carried.frame.model other assignment = frame.frame.model other assignment :=
  carry_model frame SourcePrefix.instances nodes suffix_replayed other assignment

theorem actual_context_retained : SourcePrefix.received.context = SourcePrefix.withTruth.context :=
  context_eq SourcePrefix.instances nodes suffix_replayed

theorem retained_definition : SourcePrefix.received.cache[0]? = some SourcePrefix.defined.output.definitionTheorem :=
  old_lookup SourcePrefix.instances nodes suffix_replayed rfl

theorem new_fact_needs_actual_later_cache :
    SourcePrefix.withTruth.context = SourcePrefix.received.context ∧ SourcePrefix.withTruth.cache[1]? = none ∧
      SourcePrefix.received.cache[1]? = some SourcePrefix.reflexivity :=
  ⟨actual_context_retained.symm, rfl, SourcePrefix.prefix_root⟩

def identityFormula : HOL.ClosedFormula Symbol :=
  .eq (.lam (.var .vz) : HOL.ClosedTerm Symbol (HOL.Ty.arr .prop .prop)) (.lam (.var .vz))

theorem after_read_accepted :
    (ExactFormulaReadback.read? SourcePrefix.received 1 identityFormula).isSome = true := by
  decide +kernel

def identityRead : ExactFormulaReadback.ReadFact SourcePrefix.received identityFormula :=
  (ExactFormulaReadback.read? SourcePrefix.received 1 identityFormula).get after_read_accepted

theorem newly_earned_fact_in_original_model (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (frame.frame.model other assignment).models identityFormula :=
  read_in_prefix_model frame SourcePrefix.instances nodes suffix_replayed other assignment identityFormula identityRead

theorem earlier_read_refused : ExactFormulaReadback.read? SourcePrefix.withTruth 1 identityFormula = none := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix.Controls.actual_model_retained
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProofSuffix.Controls.newly_earned_fact_in_original_model
