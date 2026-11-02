import Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicate
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.IndexedPredicateInduction

/-!
# Retained proofs of admitted recursive-family membership

The parent shape and computed result index come from the original admitted
constructor fields. Recursive children must supply their edge, least-member
and inactive-padding conditions. The resulting proof proves the complete
compiled member program, retaining its surrounding context and target index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description

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
    FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
  {assumptions : List (Formula Const Γ)}

@[irreducible] def memberProgram_beta (value : Term Const Γ space) (target : Term Const Γ reading.indices.index) :
    ProofSyntax Const assumptions (.eq
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)
      (.and
        (.app (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least value)
        (.app (.app ((inventory block registered guards rho numeral).rootProgram constructorCode) value) target))) :=
  CurriedGuardProgramProofs.conjunctionProgram_beta
    (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
    ((inventory block registered guards rho numeral).rootProgram constructorCode) value target

theorem memberProgram_beta_free (value : Term Const Γ space) (target : Term Const Γ reading.indices.index) :
    (memberProgram_beta block registered guards rho numeral zero successor bottomCode constructorCode
      (assumptions := assumptions) value target).FunctionExtensionalityFree := by
  unfold memberProgram_beta
  exact CurriedGuardProgramProofs.conjunctionProgram_beta_free
    (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
    ((inventory block registered guards rho numeral).rootProgram constructorCode) value target

def memberLeast (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)) :
    ProofSyntax Const assumptions
      (.app (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least value) :=
  .andEL (.impE (.eqPropEL
    (memberProgram_beta block registered guards rho numeral zero successor bottomCode constructorCode value target)) member)

def memberRoot (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)) :
    ProofSyntax Const assumptions (.app (.app ((inventory block registered guards rho numeral).rootProgram constructorCode) value) target) :=
  .andER (.impE (.eqPropEL
    (memberProgram_beta block registered guards rho numeral zero successor bottomCode constructorCode value target)) member)

theorem memberLeast_free (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target))
    (free : member.FunctionExtensionalityFree) :
    (memberLeast block registered guards rho numeral zero successor bottomCode constructorCode value target member).FunctionExtensionalityFree := by
  exact ⟨memberProgram_beta_free block registered guards rho numeral zero successor bottomCode constructorCode value target, free⟩

theorem memberRoot_free (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target))
    (free : member.FunctionExtensionalityFree) :
    (memberRoot block registered guards rho numeral zero successor bottomCode constructorCode value target member).FunctionExtensionalityFree := by
  exact ⟨memberProgram_beta_free block registered guards rho numeral zero successor bottomCode constructorCode value target, free⟩

@[irreducible] def memberInduction (property : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
        (PredicateFixedPoint.intersection
          (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
          (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) property)))
      (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) property)))
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)) :
    ProofSyntax Const assumptions (.app (.app property value) target) :=
  IndexedPredicateInduction.induction
    (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
    ((inventory block registered guards rho numeral).rootProgram constructorCode) property value target
    (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).monotonicity
    step (memberLeast block registered guards rho numeral zero successor bottomCode constructorCode value target member)
    (memberRoot block registered guards rho numeral zero successor bottomCode constructorCode value target member)

theorem memberInduction_free (property : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
        (PredicateFixedPoint.intersection
          (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
          (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) property)))
      (IndexedPredicateInduction.lift ((inventory block registered guards rho numeral).rootProgram constructorCode) property)))
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target))
    (stepFree : step.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (memberInduction block registered guards rho numeral zero successor bottomCode constructorCode property value target step member).FunctionExtensionalityFree := by
  unfold memberInduction
  apply IndexedPredicateInduction.induction_free
  · exact RecursiveSpacePredicate.Contextual.monotonicity_free _
  · exact stepFree
  · exact memberLeast_free block registered guards rho numeral zero successor bottomCode constructorCode value target member memberFree
  · exact memberRoot_free block registered guards rho numeral zero successor bottomCode constructorCode value target member memberFree

variable (children : Term Const Γ (reading.number ⇒ space))
  (occurrence : Fin ((codes block registered).map reading.fields).length)
  (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading (codes block registered) occurrence)))
  (evidence : guards.Evidence assumptions (codeAt reading (codes block registered) occurrence) rho arguments)
  (childProof : ProofSyntax Const assumptions
    ((recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).childConditions
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
      (payloadTerm reading (codes block registered) occurrence arguments) children))

@[irreducible] def constructorLeastProof :
    ProofSyntax Const assumptions (.app
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
      ((inventory block registered guards rho numeral).constructorValue constructorCode occurrence
        (inventoryArguments reading (codes block registered) occurrence arguments) children)) :=
  (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructor_intro
    (numeral occurrence.val) (payloadTerm reading (codes block registered) occurrence arguments) children
    (.impE (.eqPropER ((inventory block registered guards rho numeral).shapeProgram_beta _ _))
      (guards.shapeProof (codes block registered) rho numeral occurrence arguments evidence)) childProof

@[irreducible] def constructorMemberProof :
    ProofSyntax Const assumptions
      (.app (.app (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode)
        ((inventory block registered guards rho numeral).constructorValue constructorCode occurrence
          (inventoryArguments reading (codes block registered) occurrence arguments) children))
        (reading.indexTerm (codeAt reading (codes block registered) occurrence) rho arguments)) :=
  .impE (.eqPropER (memberProgram_beta block registered guards rho numeral zero successor bottomCode constructorCode _ _))
    (.andI
      (constructorLeastProof block registered guards rho numeral zero successor bottomCode constructorCode
        children occurrence arguments evidence childProof)
      (.impE (.eqPropER ((inventory block registered guards rho numeral).rootProgram_beta constructorCode _ _))
        (rootProof block registered guards rho numeral constructorCode children occurrence arguments evidence)))

theorem constructorLeastProof_free
    (fieldFree : guards.EvidenceFree assumptions (codeAt reading (codes block registered) occurrence) rho arguments evidence)
    (childrenFree : childProof.FunctionExtensionalityFree) :
    (constructorLeastProof block registered guards rho numeral zero successor bottomCode constructorCode
      children occurrence arguments evidence childProof).FunctionExtensionalityFree := by
  unfold constructorLeastProof
  apply RecursiveSpacePredicate.Contextual.constructor_intro_free
  · exact ⟨IndexedConstructorGuards.ConstructorPrograms.shapeProgram_beta_free _ _ _,
      guards.shapeProof_free _ _ _ _ _ _ fieldFree⟩
  · exact childrenFree

theorem constructorMemberProof_free
    (fieldFree : guards.EvidenceFree assumptions (codeAt reading (codes block registered) occurrence) rho arguments evidence)
    (childrenFree : childProof.FunctionExtensionalityFree) :
    (constructorMemberProof block registered guards rho numeral zero successor bottomCode constructorCode
      children occurrence arguments evidence childProof).FunctionExtensionalityFree := by
  unfold constructorMemberProof
  exact ⟨memberProgram_beta_free block registered guards rho numeral zero successor bottomCode constructorCode _ _,
    constructorLeastProof_free block registered guards rho numeral zero successor bottomCode constructorCode
      children occurrence arguments evidence childProof fieldFree childrenFree,
    IndexedConstructorGuards.ConstructorPrograms.rootProgram_beta_free _ _ _ _,
    rootProof_free block registered guards rho numeral constructorCode children occurrence arguments evidence fieldFree⟩

#print axioms constructorLeastProof
#print axioms constructorMemberProof
#print axioms constructorMemberProof_free

end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
