import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRuleLoadParametric

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def parametricRuleRow (rule : Atom) : Atom :=
  linkedRow "compressed-verifier-rule" compressedVerifierRuleOwner 0 1 rule

def parametricLoadProgram (rule : Atom) : List Atom :=
  [sourceCompressedRuleLoadRule, canaryLoading 0, parametricRuleRow rule]

def parametricLoadFinal (rule : Atom) : List Atom :=
  cFireReflectiveSourceExecFact (parametricLoadProgram rule)
    sourceCompressedRuleLoadDirective

def parametricLoadRows (rule : Atom) : List Subst :=
  (Conformance.Computable.cmatchInputSpec []
    (sourceCompressedRuleLoadDirective.atom ::
      (parametricLoadProgram rule).erase
        sourceCompressedRuleLoadDirective.atom)
    sourceCompressedRuleLoadDirective.rule.input).map Prod.fst

def parametricLoadSubstitution (rule : Atom) : Subst :=
  [("compressed-verifier-rule", rule),
   ("next-rule-position", natAtom 1),
   ("rule-position", natAtom 0),
   ("position", natAtom canaryPosition),
   ("source", canarySource),
   ("load-output", outputSurface compressedRuleLoadSinks),
   ("load-input", inputSurface compressedRuleLoadPatterns)]

@[simp] theorem parametricLoadSubstitution_instantiates_rule (rule : Atom) :
    instantiateTemplateAtom? (parametricLoadSubstitution rule)
      (.var "compressed-verifier-rule") = some rule := by
  simp [parametricLoadSubstitution, instantiateTemplateAtom?, templateCovered,
    applySubst, Subst.lookup]

@[simp] theorem parametricLoadSubstitution_instantiates_successor
    (rule : Atom) :
    instantiateTemplateAtom? (parametricLoadSubstitution rule)
      compressedRuleNextLoadingTemplate = some (canaryLoading 1) := by
  simp [parametricLoadSubstitution, compressedRuleNextLoadingTemplate,
    instantiateTemplateAtom?, templateCovered, applySubst, Subst.lookup,
    canaryLoading, canarySource, canaryPosition, canaryProofOwner,
    canaryHeaderControl, sourceProofOwnerTemplate, headerControlTemplate]

theorem parametricLoadFinal_eq (rule : Atom) :
    parametricLoadFinal rule =
      cApplyReflectiveSinkBatch (parametricLoadRows rule)
        ((parametricLoadProgram rule).erase
          sourceCompressedRuleLoadDirective.atom)
        compressedRuleLoadSinks := by
  rfl

/-- Once the canonical matcher row is present, the loader sinks are parametric
in the supplied target rule: they emit the exact opaque value and advance the
occurrence-indexed cursor. -/
theorem load_sinks_emit_supplied_rule_and_successor_of_match (rule : Atom)
    (rowMember :
      parametricLoadSubstitution rule ∈ parametricLoadRows rule) :
    rule ∈ parametricLoadFinal rule ∧ canaryLoading 1 ∈ parametricLoadFinal rule := by
  rw [parametricLoadFinal_eq]
  constructor
  · simp only [compressedRuleLoadSinks, cApplyReflectiveSinkBatch]
    apply mem_cApplyReflectiveSinkBatch_add_cons_of_row
      (parametricLoadRows rule) _ (.var "compressed-verifier-rule") rule
      [.add compressedRuleNextLoadingTemplate]
      (parametricLoadSubstitution rule)
    · exact rowMember
    · exact parametricLoadSubstitution_instantiates_rule rule
    · intro sink member
      simp only [List.mem_singleton] at member
      subst sink
      exact ⟨compressedRuleNextLoadingTemplate, rfl⟩
  · simp only [compressedRuleLoadSinks, cApplyReflectiveSinkBatch]
    apply mem_cApplyReflectiveSinkBatch_add_cons_of_row
      (parametricLoadRows rule) _ compressedRuleNextLoadingTemplate
      (canaryLoading 1) [] (parametricLoadSubstitution rule)
    · exact rowMember
    · exact parametricLoadSubstitution_instantiates_successor rule
    · simp

#print axioms parametricLoadSubstitution_instantiates_rule
#print axioms parametricLoadSubstitution_instantiates_successor
#print axioms parametricLoadFinal_eq
#print axioms load_sinks_emit_supplied_rule_and_successor_of_match

end Mettapedia.Languages.Metamath.MM2CompressedProofRuleLoadParametric
