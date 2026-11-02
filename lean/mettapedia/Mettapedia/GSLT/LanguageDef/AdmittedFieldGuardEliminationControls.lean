import Mettapedia.Logic.HOL.IndexedContainerGuardElimination
import Mettapedia.GSLT.LanguageDef.AdmittedContainerProofControls

/-!
# Guard recovery at the admitted Vector source telescope

Closed and open source arguments exercise both retained data-field guards.
A false guard cannot yield a closed admitted field proof. Child conditions
are not weakened or used as substitute data-field evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedFieldGuardEliminationControls

open Mettapedia.Logic.HOL
open IndexedContainerPositionTerms FiniteConstructorEncoding
open AdmittedContainerHOL AdmittedContainerGeneratedControls

noncomputable section

def code := codeAt reading (codes block registered) consOccurrence

def closedGuard : ProofSyntax Symbol [AdmittedContainerProofControls.consConditions]
    (applyArguments (reading.fields code) (guards.compile code Subst.id) consArguments) :=
  guards.introduce code Subst.id consArguments AdmittedContainerProofControls.consFields

theorem closedGuard_free : closedGuard.FunctionExtensionalityFree :=
  guards.introduce_free code Subst.id consArguments AdmittedContainerProofControls.consFields
    AdmittedContainerProofControls.consFields_free

def recovered := guards.eliminate code Subst.id consArguments closedGuard

theorem recovered_free : guards.EvidenceFree [AdmittedContainerProofControls.consConditions]
    code Subst.id consArguments recovered :=
  guards.eliminate_free code Subst.id consArguments closedGuard closedGuard_free

namespace Open
open AdmittedContainerProofControls.Open

def openGuard : ProofSyntax Symbol ([] : List (Formula Symbol context))
    (applyArguments (reading.fields code) (sourceGuards.compile code substitution) arguments) :=
  sourceGuards.introduce code substitution arguments fieldEvidence

theorem openGuard_free : openGuard.FunctionExtensionalityFree := by
  apply sourceGuards.introduce_free
  change _ ∧ _ ∧ True
  simp only [fieldEvidence, ProofSyntax.FunctionExtensionalityFree, and_self]

def recoveredOpen := sourceGuards.eliminate code substitution arguments openGuard

theorem recoveredOpen_free : sourceGuards.EvidenceFree ([] : List (Formula Symbol context))
    code substitution arguments recoveredOpen :=
  sourceGuards.eliminate_free code substitution arguments openGuard openGuard_free

end Open

def refusingGuards : FieldGuards reading where
  value _ := .lam .bot
  shape _ _ impossible _ := by cases impossible

def refusedGuard : ClosedFormula Symbol :=
  applyArguments (reading.fields code) (refusingGuards.compile code Subst.id) consArguments

theorem false_field_guard_refused : ¬ Nonempty (ProofSyntax Symbol [] refusedGuard) := by
  rintro ⟨present⟩
  let evidence := refusingGuards.eliminate code Subst.id consArguments present
  have impossible : ProofSyntax Symbol [] .bot := .impE (.eqPropEL (.beta _ _)) evidence.1
  have falseResult := Soundness.extDerivation_sound impossible.erase (M := model) (ρ := empty)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ absent; nomatch absent)
    (by intro _ absent; nomatch absent)
  exact falseResult

#print axioms recovered_free
#print axioms Open.recoveredOpen_free
#print axioms false_field_guard_refused

end
end Mettapedia.GSLT.LanguageDef.AdmittedFieldGuardEliminationControls
