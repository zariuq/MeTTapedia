import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticDefinitionData
import Mettapedia.Languages.HOLLight.DefinitionReplayModels
import Mettapedia.Languages.HOLLight.StandardTheoryInterpretation

/-! # The actual semantic-effect definition history through the HOL receiver

The exported defining terms are admitted by the existing registered HOL
definition operation. Its chronological model construction supplies their
meanings at all type instances. Specializing those meanings to the indexed
frame encoding is a further semantic theorem, not assumed by this receiver.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticDefinitions

open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic

theorem reference_available :
    (SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis HOLSemanticDefinitionData.records).isSome = true := by
  decide +kernel

def received : ExportCodec.State :=
  (SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis HOLSemanticDefinitionData.records).get reference_available

theorem received_exact :
    SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis HOLSemanticDefinitionData.records = some received :=
  (Option.some_get reference_available).symm

theorem definition_inventory : HOLSemanticDefinitionData.records.length = 19 := rfl

private theorem lookup_of_same {found : Option Const} {expected : Const}
    (agrees : found.any (fun actual => Const.same actual expected) = true) : found = some expected := by
  cases found with
  | none => cases agrees
  | some actual =>
      have same : actual = expected := (Const.same_eq_true_iff _ _).mp agrees
      rw [same]

/-- Full provenance-bearing identities agree with the already interpreted
Boolean definitions. Equality of printed names alone would not establish this. -/
theorem standard_boolean_identities :
    List.lookup "T" received.symbols.constants = some StandardTheoryInterpretation.Source.truthConstant ∧
    List.lookup "/\\" received.symbols.constants = some StandardTheoryInterpretation.Source.conjunctionConstant ∧
    List.lookup "==>" received.symbols.constants = some StandardTheoryInterpretation.Source.implicationConstant ∧
    List.lookup "!" received.symbols.constants = some StandardTheoryInterpretation.Source.universalConstant ∧
    List.lookup "?" received.symbols.constants = some StandardTheoryInterpretation.Source.existentialConstant ∧
    List.lookup "F" received.symbols.constants = some StandardTheoryInterpretation.Source.falsityConstant ∧
    List.lookup "~" received.symbols.constants = some StandardTheoryInterpretation.Source.negationConstant := by
  have checked : [
      (List.lookup "T" received.symbols.constants).any (fun actual => Const.same actual StandardTheoryInterpretation.Source.truthConstant),
      (List.lookup "/\\" received.symbols.constants).any (fun actual => Const.same actual StandardTheoryInterpretation.Source.conjunctionConstant),
      (List.lookup "==>" received.symbols.constants).any (fun actual => Const.same actual StandardTheoryInterpretation.Source.implicationConstant),
      (List.lookup "!" received.symbols.constants).any (fun actual => Const.same actual StandardTheoryInterpretation.Source.universalConstant),
      (List.lookup "?" received.symbols.constants).any (fun actual => Const.same actual StandardTheoryInterpretation.Source.existentialConstant),
      (List.lookup "F" received.symbols.constants).any (fun actual => Const.same actual StandardTheoryInterpretation.Source.falsityConstant),
      (List.lookup "~" received.symbols.constants).any (fun actual => Const.same actual StandardTheoryInterpretation.Source.negationConstant)
    ].all id = true := by decide +kernel
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true, id_eq] at checked
  obtain ⟨truth, conjunction, implication, universal, existential, falsity, negation⟩ := checked
  exact ⟨lookup_of_same truth, lookup_of_same conjunction, lookup_of_same implication,
    lookup_of_same universal, lookup_of_same existential, lookup_of_same falsity, lookup_of_same negation⟩

namespace Controls

def first : Lean.Json := HOLSemanticDefinitionData.records[0]'(by decide +kernel)

theorem first_definition_accepted :
    (SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis [first]).isSome = true := by
  decide +kernel

theorem repeated_definition_refused :
    SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis [first, first] = none := by
  decide +kernel

def booleanType : Lean.Json := .arr #[.str "op", .str "bool", .arr #[]]
def wrongType : Lean.Json := .arr #[.str "op", .str "fun", .arr #[booleanType, booleanType]]

/-- Keep the actual defining equation and claim, but advertise the wrong
constant type. The registered receiver compares the annotation to the body. -/
def wrongAnnotation : Lean.Json :=
  Lean.Json.mkObj [
    ("id", (ExportCodec.field? first "id").getD .null),
    ("rule", .str "DEFINITION"),
    ("arguments", .arr #[
      ((ExportCodec.field? first "arguments").bind (fun args => ExportCodec.at? args 0)).getD .null,
      .str "T", wrongType]),
    ("theorem", (ExportCodec.field? first "theorem").getD .null)]

theorem wrong_annotation_refused :
    SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis [wrongAnnotation] = none := by
  decide +kernel

end Controls

universe w

theorem defining_equations_have_constructed_model
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ∃ finalModel : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      finalModel.Carrier = model.Carrier ∧
      (model.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ received.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula :=
  DefinitionReplayModels.reference_definitions_models SourceProfile.primitiveBasis
    HOLSemanticDefinitionData.records received received_exact rfl model

#print axioms reference_available
#print axioms defining_equations_have_constructed_model
#print axioms Controls.wrong_annotation_refused
#print axioms standard_boolean_identities

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticDefinitions
