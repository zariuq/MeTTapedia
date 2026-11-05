import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireCodecSupport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire

/-! Compositional support certificates for emitted plan data. The theorems
follow the original encoders and do not evaluate admission decisions or
rebuild a compiled plan to inspect its fixed wire vocabulary. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WirePlanSupport

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open WireCodeSupport

open PremiseOperationsExecution


def tags : List String := WireCodecSupport.tags ++
  ["PremiseSignature","PremiseProviderRow","PremiseProvider","PremiseSpecification","ReflectiveRule",
    "ReflectivePresentation","PremiseReflection","PremiseEnvironment","Binding","TermSlot","OperationalPermissions",
    "EquationDepth","EquationJobDeclaration","CompletePlan","USome","CollectionLaw","Extrusion",
    "Standard","Canonical","Reflective","Model","CollectionRootSearch","CollectionOccurrenceSearch"]

def Supported (allowed : String → Bool) : Prop := ∀ tag ∈ tags, allowed tag = true

private theorem tag_static : ∀ tag ∈ tags, tag ≠ "eval" ∧ tag ≠ "unique" := by decide +kernel

theorem base (allowed : String → Bool) (supported : Supported allowed) : WireCodecSupport.Supported allowed := by
  intro tag member
  exact supported tag (List.mem_append_left _ member)

theorem app (allowed : String → Bool) (supported : Supported allowed) (head : String)
    (member : head ∈ tags) (arguments : List Term) (children : checkMany allowed arguments = true) :
    check allowed (.application head arguments) = true :=
  check_application allowed head arguments (by
    have static := tag_static head member
    simp [Eval.expressionHeadWithin, supported head member, static.1, static.2]) children

theorem list (allowed : String → Bool) (supported : Supported allowed) {α : Type}
    (encode : α → Term) (values : List α) (valid : ∀ value ∈ values, check allowed (encode value) = true) :
    check allowed (CettaWire.encodeList encode values) = true :=
  check_encodeList allowed encode (supported "LCons" (by decide)) values valid

theorem mode (allowed : String → Bool) (value : RelationArgMode) :
    check allowed (GeneralExecution.modeTerm value) = true := by cases value <;> rfl

theorem signature (allowed : String → Bool) (supported : Supported allowed) (value : GeneralPremise.Signature) :
    check allowed (GeneralExecution.signatureTerm value) = true := by
  apply app allowed supported "PremiseSignature" (by decide)
  have types := list allowed supported AuthoredRule.typeTerm value.argumentTypes
    (fun item _ => WireCodecSupport.type allowed (base allowed supported) item)
  have modes := list allowed supported GeneralExecution.modeTerm value.modes (fun item _ => mode allowed item)
  simp only [GeneralExecution.Base.typesTerm,checkMany,check_string,types,modes,Bool.true_and]

theorem providerRow (allowed : String → Bool) (supported : Supported allowed) (value : GeneralPremise.ProviderRow) :
    check allowed (GeneralExecution.providerRowTerm value) = true := by
  apply app allowed supported "PremiseProviderRow" (by decide)
  simp only [GeneralExecution.Base.patternsTerm,checkMany,check_string,
    WireCodecSupport.patterns allowed (base allowed supported) value.values,Bool.true_and]

theorem provider (allowed : String → Bool) (supported : Supported allowed) (value : GeneralPremise.ProviderSnapshot) :
    check allowed (GeneralExecution.providerTerm value) = true := by
  apply app allowed supported "PremiseProvider" (by decide)
  have signatures := list allowed supported GeneralExecution.signatureTerm value.signatures
    (fun item _ => signature allowed supported item)
  have rows := list allowed supported GeneralExecution.providerRowTerm value.rows (fun item _ => providerRow allowed supported item)
  simp only [checkMany,signatures,rows,Bool.true_and]

theorem specification (allowed : String → Bool) (supported : Supported allowed) (value : Nat × RuleBindingSpec) :
    check allowed (GeneralExecution.specificationTerm value) = true := by
  apply app allowed supported "PremiseSpecification" (by decide)
  simp only [checkMany,check_natural,WireCodecSupport.bindingSpec allowed (base allowed supported) value.2,Bool.true_and]

theorem reflectiveRule (allowed : String → Bool) (supported : Supported allowed) (value : ReflectiveRuleDecl) :
    check allowed (GeneralExecution.reflectiveRuleTerm value) = true := by
  exact app allowed supported "ReflectiveRule" (by decide) _ rfl

theorem reflectivePresentation (allowed : String → Bool) (supported : Supported allowed) (value : ReflectivePresentationDecl) :
    check allowed (AuthoredRule.reflectivePresentationTerm value) = true := by
  apply app allowed supported "ReflectivePresentation" (by decide)
  simp only [checkMany,check_string,WireCodecSupport.collectionType,Bool.true_and]

theorem reflection (allowed : String → Bool) (supported : Supported allowed) (value : Reflection.ReflectionProfile) :
    check allowed (GeneralExecution.reflectionTerm value) = true := by
  apply app allowed supported "PremiseReflection" (by decide)
  have declarations := list allowed supported AuthoredRule.reflectivePresentationTerm value.presentations
    (fun item _ => reflectivePresentation allowed supported item)
  have rules := list allowed supported GeneralExecution.reflectiveRuleTerm value.rules
    (fun item _ => reflectiveRule allowed supported item)
  simp only [checkMany,declarations,rules,Bool.true_and]

theorem freeContext (allowed : String → Bool) (supported : Supported allowed) (value : List (String × TypeExpr)) :
    check allowed (PremiseOperationsExecution.DeclarationTyping.freeContextTerm value) = true := by
  unfold PremiseOperationsExecution.DeclarationTyping.freeContextTerm MatchAutomataBindingExecution.payloadBindingsTerm
  apply list allowed supported
  intro item member
  obtain ⟨entry,_,rfl⟩ := List.mem_map.mp member
  apply app allowed supported "Binding" (by decide)
  simp only [checkMany,check_string,WireCodecSupport.type allowed (base allowed supported) entry.2,Bool.true_and]

theorem environment (allowed : String → Bool) (supported : Supported allowed)
    (value : GeneralPremise.Environment) (free : List (String × TypeExpr)) :
    check allowed (GeneralExecution.environmentTerm value free) = true := by
  apply app allowed supported "PremiseEnvironment" (by decide)
  have terms := list allowed supported AuthoredRule.typingDeclarationTerm value.language.terms
    (fun item _ => WireCodecSupport.typingDeclaration allowed (base allowed supported) item)
  have rules := list allowed supported AuthoredRule.rewriteTerm value.language.rewrites
    (fun item _ => WireCodecSupport.rewrite allowed (base allowed supported) item)
  have specifications := list allowed supported GeneralExecution.specificationTerm value.specifications
    (fun item _ => specification allowed supported item)
  simp only [checkMany,terms,rules,specifications,provider allowed supported value.provider,
    reflection allowed supported value.reflection,freeContext allowed supported free,Bool.true_and]

theorem boolean (allowed : String → Bool) (value : Bool) :
    check allowed (ContextObservation.booleanTerm value) = true := by cases value <;> rfl

theorem slot (allowed : String → Bool) (supported : Supported allowed) (value : String × Nat) :
    check allowed (ContextObservation.slotTerm value) = true :=
  app allowed supported "TermSlot" (by decide) _ rfl

theorem permissions (allowed : String → Bool) (supported : Supported allowed)
    (value : GeneralTypedSites.OperationalPermissions) :
    check allowed (ContextObservation.permissionsTerm value) = true := by
  apply app allowed supported "OperationalPermissions" (by decide)
  have slots := list allowed supported ContextObservation.slotTerm value.constructorArguments
    (fun item _ => slot allowed supported item)
  have kinds := list allowed supported encodeCollectionType value.collectionKinds
    (fun item _ => WireCodecSupport.collectionType allowed item)
  simp only [checkMany,boolean,InferenceCettaWire.encodeList,slots,kinds,Bool.true_and]

theorem equationDepth (allowed : String → Bool) (supported : Supported allowed)
    (plan : GeneralExecutionAdmission.Plan) (value : GeneralExecutionAdmission.EquationPlan) :
    check allowed (CompletePlanWire.equationDepthTerm plan value) = true := by
  unfold CompletePlanWire.equationDepthTerm
  split
  · apply app allowed supported "EquationDepth" (by decide)
    have names := list allowed supported Term.string value.rule.left.freeFvarNames (fun _ _ => rfl)
    simpa only [checkMany,check_natural,Bool.true_and,Bool.and_true] using names
  · rfl

theorem equation (allowed : String → Bool) (supported : Supported allowed)
    (plan : GeneralExecutionAdmission.Plan) (value : GeneralExecutionAdmission.EquationPlan × Nat) :
    check allowed (CompletePlanWire.equationDeclarationTerm plan value) = true := by
  apply app allowed supported "EquationJobDeclaration" (by decide)
  simp only [checkMany,check_natural,WireCodecSupport.rewrite allowed (base allowed supported) value.1.rule,
    WireCodecSupport.bindingSpec allowed (base allowed supported) value.1.binding.spec,
    equationDepth allowed supported plan value.1,Bool.true_and]

theorem admitted (allowed : String → Bool) (value : Bool) :
    check allowed (CompletePlanWire.admittedTerm value) = true := rfl

theorem plan (allowed : String → Bool) (supported : Supported allowed)
    (value : GeneralExecutionAdmission.Plan) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) : check allowed (CompletePlanWire.planTerm value table bound expected) = true := by
  apply app allowed supported "CompletePlan" (by decide)
  have bounds := list allowed supported AuthoredRule.typeTerm bound
    (fun item _ => WireCodecSupport.type allowed (base allowed supported) item)
  have rules := list allowed supported ScopedRuleJobReadoutExecution.rulePlanTerm value.rules
    (fun item _ => WireCodecSupport.rulePlan allowed (base allowed supported) item)
  have equations := list allowed supported (CompletePlanWire.equationDeclarationTerm value) value.equations.zipIdx
    (fun item _ => equation allowed supported value item)
  simp only [checkMany,environment allowed supported,permissions allowed supported,bounds,
    WireCodecSupport.type allowed (base allowed supported) expected,rules,equations,admitted,Bool.true_and]

theorem unit (allowed : String → Bool) (supported : Supported allowed) (value : Option String) :
    check allowed (StandardWire.unitTerm value) = true := by
  cases value with
  | none => rfl
  | some name => exact app allowed supported "USome" (by decide) _ rfl

theorem law (allowed : String → Bool) (supported : Supported allowed) (value : CollectionLaws.Laws) :
    check allowed (StandardWire.lawTerm value) = true := by
  apply app allowed supported "CollectionLaw" (by decide)
  simp only [checkMany,WireCodecSupport.collectionType,unit allowed supported value.unit,Bool.true_and]

theorem extrusion (allowed : String → Bool) (supported : Supported allowed) (value : CollectionLaws.Extrusion) :
    check allowed (StandardWire.extrusionTerm value) = true := by
  apply app allowed supported "Extrusion" (by decide)
  simp only [checkMany,WireCodecSupport.collectionType,check_string,Bool.true_and]

theorem standard (allowed : String → Bool) (supported : Supported allowed) (value : GeneralExecutionAdmission.Plan) :
    check allowed (StandardWire.standardTerm value) = true := by
  apply app allowed supported "Standard" (by decide)
  have laws := list allowed supported StandardWire.lawTerm (Complete.Normalized.laws value)
    (fun item _ => law allowed supported item)
  have extrusions := list allowed supported StandardWire.extrusionTerm (Complete.Normalized.extrusions value)
    (fun item _ => extrusion allowed supported item)
  simp only [checkMany,laws,extrusions,Bool.true_and]

#print axioms plan
#print axioms standard

#print axioms environment

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WirePlanSupport
