import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorProgram

/-!
# Transporting the original supplied case to the computed constructor

The original constructor variable alone is replaced by the curried program.
All field, method and ambient hypotheses undergo that same substitution.
Retained beta computation then transports the existential motive conclusion
to the actual recursive-space value. No hypothesis is discharged merely by
substitution, and no equation for an arbitrary original constructor follows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorCaseTransport
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original constructorCarrier)
open IndexedContainerNativeVectorLogicalRow (fieldCarrier fieldContext existsAt variableAt)
open IndexedContainerNativeVectorConstructorProgram

def images (replacement : Term Const fieldCarrier constructorCarrier) : Subst Const fieldCarrier fieldCarrier
  | _, .vs (.vs (.vs (.vs (.vs (.vs .vz))))) => replacement
  | _, .vz => .var .vz
  | _, .vs .vz => .var (.vs .vz)
  | _, .vs (.vs .vz) => .var (.vs (.vs .vz))
  | _, .vs (.vs (.vs .vz)) => .var (.vs (.vs (.vs .vz)))
  | _, .vs (.vs (.vs (.vs .vz))) => .var (.vs (.vs (.vs (.vs .vz))))
  | _, .vs (.vs (.vs (.vs (.vs .vz)))) => .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  | _, .vs (.vs (.vs (.vs (.vs (.vs (.vs entry)))))) =>
      .var (.vs (.vs (.vs (.vs (.vs (.vs (.vs entry)))))))

theorem images_constructor (replacement : Term Const fieldCarrier constructorCarrier) :
    images replacement IndexedContainerNativeVectorLogicalRow.constructorIndex = replacement := rfl

theorem images_other (replacement : Term Const fieldCarrier constructorCarrier)
    {type : Ty Base} (entry : Var fieldCarrier type)
    (different : entry.toFin.val ≠ 6) : images replacement entry = .var entry := by
  cases entry with
  | vz => rfl
  | vs entry => cases entry with
    | vz => rfl
    | vs entry => cases entry with
      | vz => rfl
      | vs entry => cases entry with
        | vz => rfl
        | vs entry => cases entry with
          | vz => rfl
          | vs entry => cases entry with
            | vz => rfl
            | vs entry => cases entry with
              | vz => exact False.elim (different rfl)
              | vs entry => cases entry with
                | vz => rfl
                | vs entry => cases entry with
                  | vz => rfl
                  | vs entry => cases entry with
                    | vz => rfl
                    | vs impossible => nomatch impossible

theorem existsAt_subst {Γ Ξ : Ctx Base} (replacement : Subst Const Γ Ξ)
    (predicate : Term Const Γ (W ⇒ .prop)) :
    HOL.subst replacement (existsAt predicate) = existsAt (HOL.subst replacement predicate) := by
  change Term.ex (.app (HOL.subst (Subst.lift replacement) (weaken predicate)) (.var .vz)) = _
  exact congrArg (fun function => Term.ex (.app function (.var .vz))) (subst_weaken replacement predicate)

variable (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (construct : Term Const fieldCarrier RawConstructor) (bottom : Term Const fieldCarrier E)

def payload := IndexedContainerNativeVectorCaseFieldEvidence.payload
def length := IndexedContainerNativeVectorCaseFieldEvidence.length
def tag := IndexedContainerNativeVectorCaseFieldEvidence.tag
def vector := IndexedContainerNativeVectorCaseFieldEvidence.vector
def before := IndexedContainerNativeVectorCaseFromChildren.before
def after := IndexedContainerNativeVectorCaseFromChildren.after
def motive : Term Const fieldCarrier (E ⇒ W ⇒ .prop) := .var IndexedContainerNativeVectorLogicalRow.motiveIndex

def replacement := program elementSelection arraySelection payload construct bottom
def sourceImages : Subst Const fieldCarrier fieldCarrier :=
  images (replacement elementSelection arraySelection construct bottom)
def value := constructed elementSelection arraySelection payload construct bottom length before tag vector after

theorem constructorCode_subst :
    HOL.subst (sourceImages elementSelection arraySelection construct bottom)
      IndexedContainerNativeVectorLogicalRow.constructorCode =
      applySource (replacement elementSelection arraySelection construct bottom) length before tag vector after := rfl

variable {Δ : List (Formula Const fieldCarrier)}

def resultEquality : ProofSyntax Const Δ (.eq
    (HOL.subst (sourceImages elementSelection arraySelection construct bottom)
      (existsAt IndexedContainerNativeVectorLogicalRow.resultPredicate))
    (existsAt (.app motive (value elementSelection arraySelection construct bottom)))) := by
  have equality := computation (Δ := Δ) elementSelection arraySelection payload construct bottom length before tag vector after
  have underWitness := (ProofSyntax.eqAppArg motive equality).rename (Rename.weaken (σ := W))
  apply ProofSyntax.castIndices rfl ?_ (ContextualTrinity.exCongr (ProofSyntax.eqApp (.var .vz) underWitness))
  rw [existsAt_subst]
  rfl

theorem resultEquality_free :
    (resultEquality (Δ := Δ) elementSelection arraySelection construct bottom).FunctionExtensionalityFree := by
  unfold resultEquality
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  rw [ContextualTrinity.exCongr_free]
  exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr
    (computation_free elementSelection arraySelection payload construct bottom length before tag vector after)

def transport (proof : ProofSyntax Const Δ (existsAt IndexedContainerNativeVectorLogicalRow.resultPredicate)) :
    ProofSyntax Const (Δ.map (HOL.subst (sourceImages elementSelection arraySelection construct bottom)))
      (existsAt (.app motive (value elementSelection arraySelection construct bottom))) :=
  .impE (.eqPropEL (resultEquality elementSelection arraySelection construct bottom))
    (proof.subst (sourceImages elementSelection arraySelection construct bottom))

theorem transport_free (proof : ProofSyntax Const Δ (existsAt IndexedContainerNativeVectorLogicalRow.resultPredicate))
    (free : proof.FunctionExtensionalityFree) :
    (transport elementSelection arraySelection construct bottom proof).FunctionExtensionalityFree :=
  ⟨resultEquality_free elementSelection arraySelection construct bottom,
    (ProofSyntax.functionExtensionalityFree_subst _ _).mpr free⟩

#print axioms images_other
#print axioms resultEquality_free
#print axioms transport_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorCaseTransport
