import Mettapedia.Logic.HOL.IndexedContainerInventoryPredicate
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.IndexedPredicateInduction

/-!
# Retained membership proofs for complete indexed inventories

The parent shape and computed result index come from the original indexed
constructor fields. Recursive children must supply their edge, least-member
and inactive-padding conditions. The resulting proof proves the complete
compiled member program, retaining its surrounding context and target index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedContainerInventory

open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description

universe u v w
variable {I : Interface.{u}} {registry : IndexedPositiveContainer.Registry I} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
  (codes : List (IndexedPositiveContainer.Code I registry parameterCount context))
  {reading : Reading I registry Const}
  (guards : FieldGuards reading)
  (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
  (numeral : Nat → Term Const Γ reading.number)
  (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
  {space : Ty Base} (bottomCode : Term Const Γ space)
  (constructorCode : Term Const Γ (reading.number ⇒
    FiniteConstructorEncoding.payloadType (codes.map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
  {assumptions : List (Formula Const Γ)}

@[irreducible] def memberProgram_beta (value : Term Const Γ space) (target : Term Const Γ reading.indices.index) :
    ProofSyntax Const assumptions (.eq
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)
      (.and
        (.app (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least value)
        (.app (.app ((guards.constructors codes rho numeral).rootProgram constructorCode) value) target))) :=
  CurriedGuardProgramProofs.conjunctionProgram_beta
    (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least
    ((guards.constructors codes rho numeral).rootProgram constructorCode) value target

theorem memberProgram_beta_free (value : Term Const Γ space) (target : Term Const Γ reading.indices.index) :
    (memberProgram_beta codes guards rho numeral zero successor bottomCode constructorCode
      (assumptions := assumptions) value target).FunctionExtensionalityFree := by
  unfold memberProgram_beta
  exact CurriedGuardProgramProofs.conjunctionProgram_beta_free
    (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least
    ((guards.constructors codes rho numeral).rootProgram constructorCode) value target

def memberLeast (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)) :
    ProofSyntax Const assumptions
      (.app (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least value) :=
  .andEL (.impE (.eqPropEL
    (memberProgram_beta codes guards rho numeral zero successor bottomCode constructorCode value target)) member)

def memberRoot (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)) :
    ProofSyntax Const assumptions (.app (.app ((guards.constructors codes rho numeral).rootProgram constructorCode) value) target) :=
  .andER (.impE (.eqPropEL
    (memberProgram_beta codes guards rho numeral zero successor bottomCode constructorCode value target)) member)

theorem memberLeast_free (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target))
    (free : member.FunctionExtensionalityFree) :
    (memberLeast codes guards rho numeral zero successor bottomCode constructorCode value target member).FunctionExtensionalityFree := by
  exact ⟨memberProgram_beta_free codes guards rho numeral zero successor bottomCode constructorCode value target, free⟩

theorem memberRoot_free (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target))
    (free : member.FunctionExtensionalityFree) :
    (memberRoot codes guards rho numeral zero successor bottomCode constructorCode value target member).FunctionExtensionalityFree := by
  exact ⟨memberProgram_beta_free codes guards rho numeral zero successor bottomCode constructorCode value target, free⟩

@[irreducible] def memberInduction (property : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
        (PredicateFixedPoint.intersection
          (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least
          (IndexedPredicateInduction.lift ((guards.constructors codes rho numeral).rootProgram constructorCode) property)))
      (IndexedPredicateInduction.lift ((guards.constructors codes rho numeral).rootProgram constructorCode) property)))
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target)) :
    ProofSyntax Const assumptions (.app (.app property value) target) :=
  IndexedPredicateInduction.induction
    (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
    ((guards.constructors codes rho numeral).rootProgram constructorCode) property value target
    (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).monotonicity
    step (memberLeast codes guards rho numeral zero successor bottomCode constructorCode value target member)
    (memberRoot codes guards rho numeral zero successor bottomCode constructorCode value target member)

theorem memberInduction_free (property : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop))
    (value : Term Const Γ space) (target : Term Const Γ reading.indices.index)
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
        (PredicateFixedPoint.intersection
          (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least
          (IndexedPredicateInduction.lift ((guards.constructors codes rho numeral).rootProgram constructorCode) property)))
      (IndexedPredicateInduction.lift ((guards.constructors codes rho numeral).rootProgram constructorCode) property)))
    (member : ProofSyntax Const assumptions
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode) value) target))
    (stepFree : step.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (memberInduction codes guards rho numeral zero successor bottomCode constructorCode property value target step member).FunctionExtensionalityFree := by
  unfold memberInduction
  apply IndexedPredicateInduction.induction_free
  · exact RecursiveSpacePredicate.Contextual.monotonicity_free _
  · exact stepFree
  · exact memberLeast_free codes guards rho numeral zero successor bottomCode constructorCode value target member memberFree
  · exact memberRoot_free codes guards rho numeral zero successor bottomCode constructorCode value target member memberFree

variable (children : Term Const Γ (reading.number ⇒ space))
  (occurrence : Fin (codes.map reading.fields).length)
  (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
  (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments)
  (childProof : ProofSyntax Const assumptions
    ((recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).childConditions
      (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least
      (payloadTerm reading codes occurrence arguments) children))

@[irreducible] def constructorLeastProof :
    ProofSyntax Const assumptions (.app
      (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least
      ((guards.constructors codes rho numeral).constructorValue constructorCode occurrence
        (inventoryArguments reading codes occurrence arguments) children)) :=
  (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).constructor_intro
    (numeral occurrence.val) (payloadTerm reading codes occurrence arguments) children
    (.impE (.eqPropER ((guards.constructors codes rho numeral).shapeProgram_beta _ _))
      (guards.shapeProof codes rho numeral occurrence arguments evidence)) childProof

@[irreducible] def constructorMemberProof :
    ProofSyntax Const assumptions
      (.app (.app (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode)
        ((guards.constructors codes rho numeral).constructorValue constructorCode occurrence
          (inventoryArguments reading codes occurrence arguments) children))
        (reading.indexTerm (codeAt reading codes occurrence) rho arguments)) :=
  .impE (.eqPropER (memberProgram_beta codes guards rho numeral zero successor bottomCode constructorCode _ _))
    (.andI
      (constructorLeastProof codes guards rho numeral zero successor bottomCode constructorCode
        children occurrence arguments evidence childProof)
      (.impE (.eqPropER ((guards.constructors codes rho numeral).rootProgram_beta constructorCode _ _))
        (rootProof codes guards rho numeral constructorCode children occurrence arguments evidence)))

theorem constructorLeastProof_free
    (fieldFree : guards.EvidenceFree assumptions (codeAt reading codes occurrence) rho arguments evidence)
    (childrenFree : childProof.FunctionExtensionalityFree) :
    (constructorLeastProof codes guards rho numeral zero successor bottomCode constructorCode
      children occurrence arguments evidence childProof).FunctionExtensionalityFree := by
  unfold constructorLeastProof
  apply RecursiveSpacePredicate.Contextual.constructor_intro_free
  · exact ⟨IndexedConstructorGuards.ConstructorPrograms.shapeProgram_beta_free _ _ _,
      guards.shapeProof_free _ _ _ _ _ _ fieldFree⟩
  · exact childrenFree

theorem constructorMemberProof_free
    (fieldFree : guards.EvidenceFree assumptions (codeAt reading codes occurrence) rho arguments evidence)
    (childrenFree : childProof.FunctionExtensionalityFree) :
    (constructorMemberProof codes guards rho numeral zero successor bottomCode constructorCode
      children occurrence arguments evidence childProof).FunctionExtensionalityFree := by
  unfold constructorMemberProof
  exact ⟨memberProgram_beta_free codes guards rho numeral zero successor bottomCode constructorCode _ _,
    constructorLeastProof_free codes guards rho numeral zero successor bottomCode constructorCode
      children occurrence arguments evidence childProof fieldFree childrenFree,
    IndexedConstructorGuards.ConstructorPrograms.rootProgram_beta_free _ _ _ _,
    rootProof_free codes guards rho numeral constructorCode children occurrence arguments evidence fieldFree⟩

#print axioms constructorLeastProof
#print axioms constructorMemberProof
#print axioms constructorMemberProof_free

end Mettapedia.Logic.HOL.IndexedContainerInventory
