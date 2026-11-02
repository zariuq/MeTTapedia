import Mettapedia.Logic.HOL.ConstructorActiveProgramProofs
import Mettapedia.Logic.HOL.ConstructorChildWitnesses

/-!+# Original-row child evidence for constructor methods

The original field guard and declared relation establish activity. The
strengthened child condition then yields membership and motive evidence at
its retained index. A row method can consume that witness within its scope;
the result cannot depend on a selected representative of the index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
    {space : Ty Base} (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    (property : Term Const Γ (space ⇒ constructors.index ⇒ .prop))
    {assumptions : List (Formula Const Γ)}

def originalChildWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (conditions : ProofSyntax Const assumptions ((positions.contextual bottom construct).childConditions
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
      (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments)) :
    ProofSyntax Const assumptions
      (positions.indexedEdgeWitness bottom construct property occurrence arguments slot (.app children slot)) :=
  positions.guardedChildWitness bottom construct property occurrence arguments children slot conditions
    (positions.activeFromOriginal occurrence arguments slot index allowed related)

theorem originalChildWitness_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (conditions : ProofSyntax Const assumptions ((positions.contextual bottom construct).childConditions
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
      (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments))
    (conditionsFree : conditions.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    (positions.originalChildWitness bottom construct property occurrence arguments children slot index
      conditions allowed related).FunctionExtensionalityFree :=
  positions.guardedChildWitness_free bottom construct property occurrence arguments children slot conditions
    (positions.activeFromOriginal occurrence arguments slot index allowed related)
    conditionsFree (positions.activeFromOriginal_free occurrence arguments slot index allowed related allowedFree relatedFree)

def useIndexedEdgeWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (result : Formula Const Γ)
    (witness : ProofSyntax Const assumptions
      (positions.indexedEdgeWitness bottom construct property occurrence arguments slot child))
    (continuation : ProofSyntax Const
      (positions.indexedEdgeBody bottom construct property occurrence arguments slot child :: weakenHyps assumptions)
      (weaken result)) : ProofSyntax Const assumptions result :=
  .exE witness continuation

theorem useIndexedEdgeWitness_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (result : Formula Const Γ)
    (witness : ProofSyntax Const assumptions
      (positions.indexedEdgeWitness bottom construct property occurrence arguments slot child))
    (continuation : ProofSyntax Const
      (positions.indexedEdgeBody bottom construct property occurrence arguments slot child :: weakenHyps assumptions)
      (weaken result))
    (witnessFree : witness.FunctionExtensionalityFree) (continuationFree : continuation.FunctionExtensionalityFree) :
    (positions.useIndexedEdgeWitness bottom construct property occurrence arguments slot child result witness continuation).FunctionExtensionalityFree :=
  ⟨witnessFree, continuationFree⟩

#print axioms originalChildWitness_free
#print axioms useIndexedEdgeWitness_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
