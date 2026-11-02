import Mettapedia.GSLT.LanguageDef.AdmittedPayloadContextInterpretation
import Mettapedia.GSLT.LanguageDef.AdmittedSourceCasePremiseControls
import Mettapedia.GSLT.LanguageDef.NestedFieldGuardEliminationControls

/-!
# Original Cons and mixed registered payload-context controls

The admitted Cons case consumes its actual source guard premise. The mixed
List/Vector description preserves open data variables and both shape fields.
The inverse construction recovers the original field evidence; a false shape
guard therefore cannot be admitted through the generated context.
These are payload interpretations, with recursive membership kept separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.PayloadContextInterpretationControls

open Mettapedia.Logic.HOL
open IndexedContainerPositionTerms FiniteConstructorEncoding PredicateContexts
open IndexedContainerPositionTerms.FieldGuards

namespace Cons

open AdmittedContainerHOL AdmittedContainerGeneratedControls
open AdmittedContainerInductionControls (initial num ctor bottom profile)

noncomputable section

def base : Telescope Symbol AdmittedSourceCasePremiseControls.context :=
  .snoc .nil (PredicateProducts.full (number ⇒ space))

def ambientImages : Subst Symbol AdmittedSourceCasePremiseControls.context AdmittedSourceCasePremiseControls.context :=
  Subst.comp AdmittedSourceCasePremiseControls.images
    (Subst.ofRename AdmittedSourceCasePremiseControls.signature.constructorRenaming)

def ambientGuards : base.Realizes ambientImages AdmittedSourceCasePremiseControls.hypotheses := fun index =>
  match index with
  | .vz => .impE (.eqPropER (.beta (ambientImages .vz) .top)) .topI

theorem ambientGuards_free : ∀ {type} (index : Var AdmittedSourceCasePremiseControls.context type),
    (ambientGuards index).FunctionExtensionalityFree := by
  intro type index
  cases index with
  | vz => exact ⟨True.intro, True.intro⟩
  | vs impossible => nomatch impossible

def realized : (guards.payloadTelescope (codeAt reading (codes block registered) consOccurrence) base initial).Realizes
    (payloadAssignment (codeAt reading (codes block registered) consOccurrence) ambientImages
      AdmittedSourceCasePremiseControls.arguments) AdmittedSourceCasePremiseControls.hypotheses :=
  scopedSourcePayloadRealizer block registered guards initial num ctor
  AdmittedSourceCasePremiseControls.zero AdmittedSourceCasePremiseControls.successor bottom
  AdmittedSourceCasePremiseControls.predicate (profile AdmittedSourceCasePremiseControls.extra)
  base AdmittedSourceCasePremiseControls.images consOccurrence AdmittedSourceCasePremiseControls.arguments ambientGuards

theorem realized_free : ∀ {type} (index : Var (payloadScope (reading := reading)
    (codeAt reading (codes block registered) consOccurrence) AdmittedSourceCasePremiseControls.context) type),
    (realized index).FunctionExtensionalityFree :=
  scopedSourcePayloadRealizer_free block registered guards initial num ctor
    AdmittedSourceCasePremiseControls.zero AdmittedSourceCasePremiseControls.successor bottom
    AdmittedSourceCasePremiseControls.predicate (profile AdmittedSourceCasePremiseControls.extra)
    base AdmittedSourceCasePremiseControls.images consOccurrence AdmittedSourceCasePremiseControls.arguments ambientGuards ambientGuards_free

theorem field_order_roundtrip :
    substituteArguments
      (payloadAssignment (codeAt reading (codes block registered) consOccurrence) ambientImages AdmittedSourceCasePremiseControls.arguments)
      (reading.fields (codeAt reading (codes block registered) consOccurrence))
      (payloadVariables (codeAt reading (codes block registered) consOccurrence) AdmittedSourceCasePremiseControls.context) =
        AdmittedSourceCasePremiseControls.arguments :=
  payloadVariables_instantiate _ _ _

theorem payload_scope_exact : payloadScope (reading := reading)
    (codeAt reading (codes block registered) consOccurrence) AdmittedSourceCasePremiseControls.context =
      [element, number, number ⇒ space] := rfl

end
end Cons

namespace Mixed

open IndexedContainerPositionTermsControls

def emptySubstitution : Subst Symbol [] [] := fun impossible => nomatch impossible
def images : Subst Symbol [] NestedFieldGuardEliminationControls.context := fun impossible => nomatch impossible
def base : Telescope Symbol [] := .nil
def baseRealizer : base.Realizes images ([] : List (Formula Symbol NestedFieldGuardEliminationControls.context)) :=
  fun impossible => nomatch impossible

def realized : (NestedFieldGuardEliminationControls.guards.payloadTelescope mixedCode base emptySubstitution).Realizes
    (payloadAssignment mixedCode images NestedFieldGuardEliminationControls.arguments)
      ([] : List (Formula Symbol NestedFieldGuardEliminationControls.context)) :=
  NestedFieldGuardEliminationControls.guards.realizePayload mixedCode base emptySubstitution images
  NestedFieldGuardEliminationControls.arguments baseRealizer NestedFieldGuardEliminationControls.fieldEvidence

theorem realized_free : ∀ {type} (index : Var (payloadScope (reading := reading) mixedCode []) type),
    (realized index).FunctionExtensionalityFree := by
  apply FieldGuards.realizePayload_free
  · intro type impossible
    nomatch impossible
  · exact NestedFieldGuardEliminationControls.fieldEvidence_free

def recovered := NestedFieldGuardEliminationControls.guards.unpackPayload mixedCode base emptySubstitution images
  NestedFieldGuardEliminationControls.arguments realized

theorem recovered_free : NestedFieldGuardEliminationControls.guards.EvidenceFree
    ([] : List (Formula Symbol NestedFieldGuardEliminationControls.context)) mixedCode
    (Subst.comp images emptySubstitution) NestedFieldGuardEliminationControls.arguments recovered.2 :=
  (FieldGuards.unpackPayload_free _ _ _ _ _ _ realized realized_free).2

theorem four_payload_fields : payloadScope (reading := reading) mixedCode [] = [number, number, number, number] := rfl

theorem field_order_roundtrip : substituteArguments
    (payloadAssignment mixedCode images NestedFieldGuardEliminationControls.arguments)
    (reading.fields mixedCode) (payloadVariables mixedCode []) = NestedFieldGuardEliminationControls.arguments :=
  payloadVariables_instantiate mixedCode images NestedFieldGuardEliminationControls.arguments

def closedAssignment : Subst Symbol (payloadScope (reading := reading) mixedCode []) [] :=
  payloadAssignment mixedCode emptySubstitution NestedFieldGuardEliminationControls.closedArguments

theorem false_shape_refused : ¬ Nonempty
    ((NestedFieldGuardEliminationControls.falseShapeGuards.payloadTelescope mixedCode base emptySubstitution).Realizes
      closedAssignment ([] : List (Formula Symbol []))) := by
  rintro ⟨bad⟩
  let evidence := (NestedFieldGuardEliminationControls.falseShapeGuards.unpackPayload mixedCode base emptySubstitution
    emptySubstitution NestedFieldGuardEliminationControls.closedArguments bad).2
  have same : @Eq (Subst Symbol [] []) (Subst.comp emptySubstitution emptySubstitution) Subst.id := by
    funext type impossible
    nomatch impossible
  have original := NestedFieldGuardEliminationControls.falseShapeGuards.castEvidence mixedCode same
    NestedFieldGuardEliminationControls.closedArguments evidence
  exact NestedFieldGuardEliminationControls.false_shape_guard_refused
    ⟨NestedFieldGuardEliminationControls.falseShapeGuards.introduce mixedCode Subst.id
      NestedFieldGuardEliminationControls.closedArguments original⟩

end Mixed

#print axioms Cons.realized_free
#print axioms Mixed.realized_free
#print axioms Mixed.recovered_free
#print axioms Mixed.false_shape_refused

end Mettapedia.GSLT.LanguageDef.PayloadContextInterpretationControls
