import Mettapedia.GSLT.LanguageDef.AdmittedContainerInduction
import Mettapedia.Logic.HOL.ConstructorNonbottom

/-!
# A uniform retained induction client for admitted families

Original constructor telescopes generate the cases. Their field guards,
computed indices and complete recursive-child conditions remain in scope.
The two representation laws are explicit premises, and the generic admitted
induction program builds the layer closure rather than assuming it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerNonbottom

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open AdmittedContainerHOL IndexedContainerPositionTerms FiniteConstructorEncoding
open IndexedPolynomial.Description

universe u v w
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
    {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
    {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
    (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
    {space : Ty Base} (bottomCode : Term Const Γ space)
    (constructorCode : Term Const Γ (reading.number ⇒
      payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))

private theorem scope_subst (signature : RecursiveSpacePredicate.Contextual Const Γ)
    {type : Ty Base} (term : Term Const Γ type) {Ξ : Ctx Base}
    (images : Subst Const signature.constructorContext Ξ) :
    HOL.subst images (weaken (weaken (weaken term))) =
      HOL.subst (Subst.comp images (Subst.ofRename signature.constructorRenaming)) term := by
  rw [← signature.rename_constructorRenaming, ← subst_ofRename, HOL.subst_comp]

def sourceCases (extra : Formula Const Γ) :
    ScopedSourceIndexedCases block registered guards rho numeral constructorCode zero successor bottomCode
      (PredicateFixedPoint.intersection
        (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
        (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode)
          (ConstructorNonbottom.motive bottomCode reading.indices.index)))
      (ConstructorNonbottom.motive bottomCode reading.indices.index)
      [extra, ConstructorInjectivity.statement constructorCode, ConstructorNonbottom.separation constructorCode bottomCode] := by
  let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
  let scope : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  intro Ξ images occurrence arguments
  let localInventory := inventory block registered guards (Subst.comp scope rho)
    (fun n => HOL.subst scope (numeral n))
  let shifted := localInventory.subst images
  let data := inventoryArguments reading (codes block registered) occurrence arguments
  let descendants := HOL.subst images signature.constructorChildren
  let tag := shifted.numeral occurrence.val
  let encoded := encode shifted.fields occurrence data
  let constructor := HOL.subst images (HOL.subst scope constructorCode)
  let bottom := HOL.subst images (HOL.subst scope bottomCode)
  let value := shifted.constructorValue constructor occurrence data descendants
  let index := reading.indexTerm (codeAt reading (codes block registered) occurrence)
    (Subst.comp images (Subst.comp scope rho)) arguments
  let motive := ConstructorNonbottom.motive bottomCode reading.indices.index
  let predicate := PredicateFixedPoint.intersection signature.least
    (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) motive)
  let assumptions := [extra, ConstructorInjectivity.statement constructorCode,
    ConstructorNonbottom.separation constructorCode bottomCode]
  let hypotheses :=
    applyArguments _ (guards.compile (codeAt reading (codes block registered) occurrence)
      (Subst.comp images (Subst.comp scope rho))) arguments ::
    .app (HOL.subst images (signature.constructorScope.childPredicate
      (weaken (weaken (weaken predicate))) signature.constructorChildren))
      (payloadTerm reading (codes block registered) occurrence arguments) ::
    (signature.methodAssumptions (assumptions := assumptions) predicate).map (HOL.subst images)
  change ProofSyntax Const hypotheses
    (.app (.app (HOL.subst images (weaken (weaken (weaken motive)))) value) index)
  have motiveSame : HOL.subst images (weaken (weaken (weaken motive))) =
      ConstructorNonbottom.motive bottom reading.indices.index := by
    rw [scope_subst signature, ConstructorNonbottom.subst_motive]
    exact congrArg (fun term => ConstructorNonbottom.motive term reading.indices.index)
      (HOL.subst_comp images scope bottomCode).symm
  have separationSame : HOL.subst images
      (weaken (weaken (weaken (ConstructorNonbottom.separation constructorCode bottomCode)))) =
      ConstructorNonbottom.separation constructor bottom := by
    rw [scope_subst signature, ConstructorNonbottom.subst_separation]
    simp only [constructor, bottom, HOL.subst_comp]
    rfl
  let inherited : ProofSyntax Const hypotheses
      (HOL.subst images (weaken (weaken (weaken (ConstructorNonbottom.separation constructorCode bottomCode))))) :=
    .hyp ⟨6, by simp [hypotheses, RecursiveSpacePredicate.Contextual.methodAssumptions, assumptions, weakenHyps]⟩
  let available := ProofSyntax.castIndices rfl separationSame inherited
  apply ProofSyntax.castIndices rfl
    (congrArg (fun term => Term.app (Term.app term value) index) motiveSame.symm)
  exact .impE (.eqPropER (ConstructorNonbottom.motive_beta bottom value index))
    (ConstructorNonbottom.specialize constructor bottom tag encoded descendants available)

theorem sourceCases_free (extra : Formula Const Γ)
    {Ξ : Ctx Base}
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    occurrence arguments :
    (sourceCases block registered guards rho numeral zero successor bottomCode constructorCode extra images occurrence arguments).FunctionExtensionalityFree := by
  unfold sourceCases
  dsimp only [id]
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨ConstructorNonbottom.motive_beta_free _ _ _, ?_⟩
  apply ConstructorNonbottom.specialize_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def member (value : Term Const Γ space) (index : Term Const Γ reading.indices.index) : Formula Const Γ :=
  .app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) index

def proof (value : Term Const Γ space) (index : Term Const Γ reading.indices.index) :
    ProofSyntax Const
      [ConstructorInjectivity.statement constructorCode, ConstructorNonbottom.separation constructorCode bottomCode]
      (.imp (member block registered guards rho numeral zero successor bottomCode constructorCode value index)
        (.not (.eq value bottomCode))) := by
  apply ProofSyntax.impI
  have derived := memberInductionFromSourceCases block registered guards rho numeral constructorCode
    zero successor bottomCode (ConstructorNonbottom.motive bottomCode reading.indices.index)
    (ProofSyntax.hyp ⟨1, by simp⟩)
    (sourceCases block registered guards rho numeral zero successor bottomCode constructorCode
      (member block registered guards rho numeral zero successor bottomCode constructorCode value index))
    value index (ProofSyntax.hyp ⟨0, by simp⟩)
  exact .impE (.eqPropEL (ConstructorNonbottom.motive_beta bottomCode value index)) derived

theorem proof_free (value : Term Const Γ space) (index : Term Const Γ reading.indices.index) :
    (proof block registered guards rho numeral zero successor bottomCode constructorCode value index).FunctionExtensionalityFree := by
  unfold proof
  refine ⟨ConstructorNonbottom.motive_beta_free _ _ _, ?_⟩
  apply memberInductionFromSourceCases_free
  · trivial
  · exact sourceCases_free _ _ _ _ _ _ _ _ _ _
  · trivial

#print axioms sourceCases
#print axioms sourceCases_free
#print axioms proof
#print axioms proof_free

end Mettapedia.GSLT.LanguageDef.AdmittedContainerNonbottom
