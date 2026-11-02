import Mettapedia.GSLT.LanguageDef.AdmittedSourceCasePremises
import Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseModelControls
import Mettapedia.Logic.HOL.ContextualConstructorInstantiation

/-!
# Original Cons cases retain the extracted source premises

The same hypothesis list is consumed by the existing admitted source-case
proof and by the new guard/child-condition readers. Constructor substitution
supplies the original tag, payload and open child array while leaving the
ambient source context unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedSourceCasePremiseControls

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms FiniteConstructorEncoding
open AdmittedContainerHOL AdmittedContainerGeneratedControls
open AdmittedContainerInductionControls (initial num ctor bottom motive profile sourceCases sourceCases_free)

noncomputable section

abbrev context := AdmittedChildPremiseControls.context
def zero : ClosedTerm Symbol number := .const .zero
def successor : ClosedTerm Symbol (number ⇒ number) := .const .successor
def signature := recursiveSignature block registered (guards := guards) (initial (Γ := context)) num zero successor bottom ctor
def predicate : Term Symbol context (space ⇒ .prop) := PredicateFixedPoint.intersection signature.least
  (IndexedPredicateInduction.lift ((inventory block registered guards initial num).rootProgram ctor) motive)
def arguments := AdmittedChildPremiseControls.sourceArguments
def data := payloadTerm reading (codes block registered) consOccurrence arguments
def children := AdmittedChildPremiseControls.children
def tag : Term Symbol context number := .app (.const .successor) (.const .zero)
def images : Subst Symbol signature.constructorContext context :=
  signature.constructorSubstitution Subst.id tag data children
def extra := AdmittedChildPremiseControls.conditions

def hypotheses := scopedSourceCaseAssumptions block registered guards initial num ctor zero successor bottom predicate
  (profile extra) images consOccurrence arguments

def fields := scopedSourceFieldEvidence block registered guards initial num ctor zero successor bottom predicate
  (profile extra) images consOccurrence arguments

theorem fields_free :
    let scope : Subst Symbol context signature.constructorContext := Subst.ofRename signature.constructorRenaming
    guards.EvidenceFree hypotheses (codeAt reading (codes block registered) consOccurrence)
      (Subst.comp images (Subst.comp scope initial)) arguments fields :=
  scopedSourceFieldEvidence_free block registered guards initial num ctor zero successor bottom predicate
    (profile extra) images consOccurrence arguments

def fullChildCondition := scopedSourceChildConditions block registered guards initial num ctor zero successor bottom predicate
  (profile extra) images consOccurrence arguments

theorem fullChildCondition_free : fullChildCondition.FunctionExtensionalityFree :=
  scopedSourceChildConditions_free block registered guards initial num ctor zero successor bottom predicate
    (profile extra) images consOccurrence arguments

def target : Formula Symbol context :=
  let scope : Subst Symbol context signature.constructorContext := Subst.ofRename signature.constructorRenaming
  let localInventory := inventory block registered guards (Subst.comp scope initial) (fun n => HOL.subst scope (num n))
  .app (.app (HOL.subst images (weaken (weaken (weaken motive))))
    ((localInventory.subst images).constructorValue (HOL.subst images (HOL.subst scope ctor)) consOccurrence
      (inventoryArguments reading (codes block registered) consOccurrence arguments)
      (HOL.subst images signature.constructorChildren)))
    (reading.indexTerm (codeAt reading (codes block registered) consOccurrence)
      (Subst.comp images (Subst.comp scope initial)) arguments)

def originalCase : ProofSyntax Symbol hypotheses target :=
  sourceCases extra images consOccurrence arguments

theorem originalCase_free : originalCase.FunctionExtensionalityFree :=
  sourceCases_free extra images consOccurrence arguments

def retainedCase : ProofSyntax Symbol hypotheses
    (.and target ((signature.constructorScope.subst images).childConditions
      (HOL.subst images (weaken (weaken (weaken predicate)))) data (HOL.subst images signature.constructorChildren))) :=
  .andI originalCase fullChildCondition

theorem retainedCase_free : retainedCase.FunctionExtensionalityFree :=
  ⟨originalCase_free, fullChildCondition_free⟩

#print axioms fields_free
#print axioms retainedCase_free

end
end Mettapedia.GSLT.LanguageDef.AdmittedSourceCasePremiseControls
