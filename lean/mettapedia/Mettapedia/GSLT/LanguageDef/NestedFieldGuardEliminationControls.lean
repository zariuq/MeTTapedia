import Mettapedia.Logic.HOL.IndexedContainerGuardElimination
import Mettapedia.GSLT.LanguageDef.IndexedContainerPositionTermsControls

/-!
# Guard recovery with interleaved registered List and Vector fields

The existing mixed description retains two open data fields, direct children,
a List shape and a dependent Vector shape. These controls select zero shape
codes, recover both shape premises, and reject a false shape guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.NestedFieldGuardEliminationControls

open Mettapedia.Logic.HOL
open IndexedContainerPositionTerms FiniteConstructorEncoding
open IndexedContainerPositionTermsControls

def guards : FieldGuards reading where
  value _ := .lam (.eq (.var .vz) (.var .vz))
  shape _ _ _ _ := .lam (.eq (.var .vz) (weakenCtx _ zero))

abbrev context : Ctx Unit := [number, number]

def substitution : Subst Symbol [] context := fun impossible => nomatch impossible

def arguments : Arguments Symbol context (reading.fields mixedCode) :=
  (.var .vz, (weakenCtx context zero, (.var (.vs .vz), (weakenCtx context zero, PUnit.unit))))

def fieldEvidence : guards.Evidence ([] : List (Formula Symbol context)) mixedCode substitution arguments := by
  refine ⟨?_, ?_, ?_, ?_, PUnit.unit⟩
  all_goals exact .impE (.eqPropER (.beta _ _)) (.eqRefl _)

theorem fieldEvidence_free :
    guards.EvidenceFree ([] : List (Formula Symbol context)) mixedCode substitution arguments fieldEvidence := by
  change _ ∧ _ ∧ _ ∧ _ ∧ True
  simp only [fieldEvidence, ProofSyntax.FunctionExtensionalityFree, and_self]

def present := guards.introduce mixedCode substitution arguments fieldEvidence

theorem present_free : present.FunctionExtensionalityFree :=
  guards.introduce_free mixedCode substitution arguments fieldEvidence fieldEvidence_free

def recovered := guards.eliminate mixedCode substitution arguments present

theorem recovered_free :
    guards.EvidenceFree ([] : List (Formula Symbol context)) mixedCode substitution arguments recovered :=
  guards.eliminate_free mixedCode substitution arguments present present_free

def falseShapeGuards : FieldGuards reading where
  value _ := .lam (.eq (.var .vz) (.var .vz))
  shape _ _ _ _ := .lam .bot

def closedArguments : Arguments Symbol [] (reading.fields mixedCode) :=
  (zero, (zero, (zero, (zero, PUnit.unit))))

theorem false_shape_guard_refused : ¬ Nonempty (ProofSyntax Symbol []
    (applyArguments (reading.fields mixedCode)
      (falseShapeGuards.compile mixedCode Subst.id) closedArguments)) := by
  rintro ⟨guardProof⟩
  have evidence := falseShapeGuards.eliminate mixedCode Subst.id closedArguments guardProof
  have impossible : ProofSyntax Symbol [] .bot :=
    .impE (.eqPropEL (.beta _ _)) evidence.2.1
  exact Soundness.extDerivation_sound impossible.erase (M := model) (ρ := empty)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ absent; nomatch absent)
    (by intro _ absent; nomatch absent)

#print axioms recovered_free
#print axioms false_shape_guard_refused

end Mettapedia.GSLT.LanguageDef.NestedFieldGuardEliminationControls
