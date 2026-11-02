import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintTheoremApplication
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingTheoremControls

/-!
# Actual MM0 dependency admission controls for constraint request activation

The non-occurrence declaration fires through an ordinary constraint step in
the independent context. The same source declaration and argument expressions
are refused in the dependent context. Successful contextual instantiation alone
does not authorize that second firing.

A second receipt retains two premise reads of one physical occurrence. These
controls exercise the original finite admission computation and the actual
take/read/output selections.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintTheoremControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting
open MM0Rewriting.TheoremControls
open MM0ConstraintTheoremApplication

def nfLabel (occurrence : Nat) : Tm :=
  if occurrence = 0 then requestValue "apply-nf" (arguments.map (encode independentContext))
  else proofValue independentContext goal

def nfBefore : Configuration Tm Nat := ⟨[], {0}⟩

noncomputable def nfReceipt : GuardedMultisetRewriting.FiringReceipt Nat Nat Tm :=
  ⟨expressionAssignment independentContext arguments, [0], [], [1],
    [regionOf nfLabel nfBefore.present (semRegion ContextualPatterns.layer
      (expressionAssignment independentContext arguments)
      (theoremRequest independentContext.length nf.arguments.length "apply-nf"))]⟩

theorem nf_receipt_from_the_actual_admitted_instance :
    nfReceipt.ValidAt ContextualPatterns.layer (theoremRule signature independentContext "apply-nf" nf)
      nfLabel nfBefore.present := by
  classical
  have scopedArguments := admitted_arguments_supported independentContext_formed nf_instance.admissible
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    theoremRule_binds signature independentContext "apply-nf" nf arguments rfl, ?_, .nil, ?_, ?_⟩
  · refine .cons ((ContextualPatterns.solves_iff _ _ _).mpr ?_) .nil
    change (theoremRequest independentContext.length arguments.length "apply-nf").inst
      (expressionAssignment independentContext arguments) =
      some (requestValue "apply-nf" (arguments.map (encode independentContext)))
    exact theoremRequest_instantiation independentContext arguments scopedArguments "apply-nf"
  · change instTemplate ContextualPatterns.layer (expressionAssignment independentContext arguments)
      [proofPattern independentContext.length nf.conclusion] = some [nfLabel 1]
    have applied := proofPattern_instantiation independentContext arguments scopedArguments nf.conclusion
    rw [nf_instance.conclusion.eval] at applied
    change ((proofPattern independentContext.length nf.conclusion).inst
      (expressionAssignment independentContext arguments)).bind (fun value => some [value]) = _
    rw [applied]
    rfl
  · refine .cons ⟨rfl, ?_⟩ .nil
    change (admitArguments signature nf.arguments independentContext
      (expressionAssignment independentContext arguments)).isSome = true
    rw [(admitArguments_iff _ _ _ _ _).mpr ⟨nf_instance.admissible, fun _ _ => rfl⟩]
    rfl

theorem nf_has_an_ordinary_constraint_step :
    ∃ rule, RequestActivation.activate ContextualPatterns.layer falseHead trueHead
        (recipe signature independentContext "apply-nf" nf) nfReceipt.assignment = some rule ∧
      Step (MM0ConstraintParameters.action independentContext) nfLabel rule nfBefore
        ((RequestActivation.physicalSelection nfReceipt).result nfLabel rule nfBefore) := by
  apply RequestActivation.step_of_matching_receipt ContextualPatterns.layer rfl falseHead trueHead
    boolean_heads_distinct independentContext.length (recipe signature independentContext "apply-nf" nf)
    nfLabel nfBefore nfReceipt nf_receipt_from_the_actual_admitted_instance
  exact ⟨(MM0ConstraintParameters.action independentContext).identity, fun _ member => by cases member⟩

theorem nf_preserves_the_physical_replacement (rule : RuleInstance Tm) :
    ((RequestActivation.physicalSelection nfReceipt).result nfLabel rule nfBefore).present = {1} := by
  change (({0} : Finset Nat) \ {0}) ∪ {1} = {1}
  decide +kernel

def refusedAssignment : Subst Nat Tm := expressionAssignment dependentContext arguments

theorem the_dependent_source_condition_really_is_false :
    (recipe signature dependentContext "apply-nf" nf).dataCondition refusedAssignment = false := by
  change (admitArguments signature nf.arguments dependentContext
    (expressionAssignment dependentContext arguments)).isSome = false
  rw [nf_arguments_refused]
  rfl

theorem refused_templates_still_activate :
    (RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      (recipe signature dependentContext "apply-nf" nf) refusedAssignment).isSome = true := by
  decide +kernel

/-- Even successful template formation cannot replace the dependency guard
by a supplied true code. Every actually computed activation is refused. -/
theorem forbidden_dependency_blocks_every_computed_firing {O : Type*} [DecidableEq O]
    (rule : RuleInstance Tm) (picked : Selection O) (label : O → Tm) (before : Configuration Tm O)
    (computed : RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      (recipe signature dependentContext "apply-nf" nf) refusedAssignment = some rule) :
    ¬picked.Valid (MM0ConstraintParameters.action dependentContext) label rule before :=
  RequestActivation.false_condition_refuses ContextualPatterns.layer falseHead trueHead
    boolean_heads_distinct dependentContext.length (recipe signature dependentContext "apply-nf" nf)
    refusedAssignment picked label before computed the_dependent_source_condition_really_is_false

def repeatedLabel (occurrence : Nat) : Tm :=
  if occurrence = 0 then requestValue "apply-repeat" [encode independentContext (.var 1)]
  else proofValue independentContext (.var 1)

def repeatedBefore : Configuration Tm Nat := ⟨[], {0, 1}⟩

noncomputable def repeatedReceipt : GuardedMultisetRewriting.FiringReceipt Nat Nat Tm :=
  ⟨expressionAssignment independentContext [.var 1], [0], [1, 1], [2],
    [regionOf repeatedLabel repeatedBefore.present (semRegion ContextualPatterns.layer
      (expressionAssignment independentContext [.var 1])
      (theoremRequest independentContext.length repeated.arguments.length "apply-repeat"))]⟩

theorem repeated_receipt_from_the_actual_admitted_instance :
    repeatedReceipt.ValidAt ContextualPatterns.layer (theoremRule signature independentContext "apply-repeat" repeated)
      repeatedLabel repeatedBefore.present := by
  classical
  have scopedArguments := admitted_arguments_supported independentContext_formed repeated_instance.admissible
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    theoremRule_binds signature independentContext "apply-repeat" repeated [.var 1] rfl, ?_, ?_, ?_, ?_⟩
  · refine .cons ((ContextualPatterns.solves_iff _ _ _).mpr ?_) .nil
    change (theoremRequest independentContext.length 1 "apply-repeat").inst
      (expressionAssignment independentContext [.var 1]) =
      some (requestValue "apply-repeat" [encode independentContext (.var 1)])
    exact theoremRequest_instantiation independentContext [.var 1] scopedArguments "apply-repeat"
  · simpa [repeatedReceipt, theoremRule, GuardedMultisetRewriting.requestRule, repeatedLabel] using
      proofPatterns_match independentContext [.var 1] scopedArguments repeated_instance.hypotheses
  · change instTemplate ContextualPatterns.layer (expressionAssignment independentContext [.var 1])
      [proofPattern independentContext.length repeated.conclusion] = some [repeatedLabel 2]
    have applied := proofPattern_instantiation independentContext [.var 1] scopedArguments repeated.conclusion
    rw [repeated_instance.conclusion.eval] at applied
    change ((proofPattern independentContext.length repeated.conclusion).inst
      (expressionAssignment independentContext [.var 1])).bind (fun value => some [value]) = _
    rw [applied]
    rfl
  · refine .cons ⟨rfl, ?_⟩ .nil
    change (admitArguments signature repeated.arguments independentContext
      (expressionAssignment independentContext [.var 1])).isSome = true
    rw [(admitArguments_iff _ _ _ _ _).mpr ⟨repeated_instance.admissible, fun _ _ => rfl⟩]
    rfl

theorem repeated_hypotheses_still_share_one_constraint_read :
    ∃ rule, RequestActivation.activate ContextualPatterns.layer falseHead trueHead
        (recipe signature independentContext "apply-repeat" repeated) repeatedReceipt.assignment = some rule ∧
      Step (MM0ConstraintParameters.action independentContext) repeatedLabel rule repeatedBefore
        ((RequestActivation.physicalSelection repeatedReceipt).result repeatedLabel rule repeatedBefore) := by
  apply RequestActivation.step_of_matching_receipt ContextualPatterns.layer rfl falseHead trueHead
    boolean_heads_distinct independentContext.length (recipe signature independentContext "apply-repeat" repeated)
    repeatedLabel repeatedBefore repeatedReceipt repeated_receipt_from_the_actual_admitted_instance
  exact ⟨(MM0ConstraintParameters.action independentContext).identity, fun _ member => by cases member⟩

theorem the_repeated_read_selection_is_unchanged :
    (RequestActivation.physicalSelection repeatedReceipt).read = [1, 1] := rfl

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintTheoremControls
