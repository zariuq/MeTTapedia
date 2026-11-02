import Mettapedia.Logic.HOL.ConstructorEdgeWitnesses
import Mettapedia.Logic.HOL.IndexedChildHypotheses
import Mettapedia.Logic.HOL.IndexedConstructorInduction
import Mettapedia.Logic.HOL.IndexedChildComponents

/-!
# Membership and motive evidence at the edge's retained index

The edge supplies its original index witness and root proof. Least membership
and the lifted motive are transported into that witness's scope, so the
result preserves the row relation together with both dependent obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
    {space : Ty Base} (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    (property : Term Const Γ (space ⇒ constructors.index ⇒ .prop))

def indexedEdgeBody (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) :
    Formula Const (constructors.index :: Γ) :=
  let rho : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let data := substituteArguments rho _ arguments
  let signature := (positions.contextual bottom construct).subst rho
  let root := HOL.subst rho (constructors.rootProgram construct)
  .and (applyArguments _ ((constructors.subst rho).allowed occurrence) data)
    (.and (applyArguments _ (.app (.app ((positions.subst rho).graph occurrence) (HOL.subst rho slot)) (.var .vz)) data)
      (.and (.app (.app (signature.memberProgram root) (HOL.subst rho child)) (.var .vz))
        (.app (.app (HOL.subst rho property) (HOL.subst rho child)) (.var .vz))))

def indexedEdgeWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) : Formula Const Γ :=
  .ex (positions.indexedEdgeBody bottom construct property occurrence arguments slot child)

def consumeEdgeWitness {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (member : ProofSyntax Const assumptions (.app (positions.contextual bottom construct).least child))
    (lifted : ProofSyntax Const assumptions
      (.app (IndexedPredicateInduction.lift (constructors.rootProgram construct) property) child))
    (edge : ProofSyntax Const assumptions
      (.app (.app (.app (positions.edgeProgram construct) (encode constructors.fields occurrence arguments)) slot) child)) :
    ProofSyntax Const assumptions (positions.indexedEdgeWitness bottom construct property occurrence arguments slot child) := by
  have witness := positions.edgeProgramReadback construct occurrence arguments slot child edge
  apply ProofSyntax.impE (ContextualTrinity.exImp ?_) witness
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let rho : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let data := substituteArguments rho _ arguments
  let signature := (positions.contextual bottom construct).subst rho
  let root := HOL.subst rho (constructors.rootProgram construct)
  let antecedent := Term.and (applyArguments _ ((constructors.subst rho).allowed occurrence) data)
    (.and (applyArguments _ (.app (.app ((positions.subst rho).graph occurrence) (HOL.subst rho slot)) (.var .vz)) data)
      ((constructors.subst rho).rootIndex (HOL.subst rho construct) (HOL.subst rho child) (.var .vz)))
  let localAssumptions := antecedent :: weakenHyps assumptions
  have original : ProofSyntax Const localAssumptions antecedent := .hyp 0
  have rootProof : ProofSyntax Const localAssumptions (.app (.app root (HOL.subst rho child)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_
      (.impE (.eqPropER ((constructors.subst rho).rootProgram_beta
        (HOL.subst rho construct) (HOL.subst rho child) (.var .vz))) (.andER (.andER original)))
    exact congrArg (fun function => Term.app (.app function (HOL.subst rho child)) (.var .vz))
      (constructors.rootProgram_subst construct rho).symm
  have childMember : ProofSyntax Const localAssumptions (.app signature.least (HOL.subst rho child)) := by
    apply ProofSyntax.castIndices ?_ ?_ ((ProofSyntax.subst rho member).prepend antecedent)
    · change antecedent :: assumptions.map (HOL.subst rho) = antecedent :: assumptions.map HOL.weaken
      apply congrArg (List.cons antecedent)
      apply List.map_congr_left
      intro formula _
      exact subst_ofRename Rename.weaken formula
    · simp only [HOL.subst, RecursiveSpacePredicate.Contextual.subst_least, signature]
  have childLift : ProofSyntax Const localAssumptions
      (.app (IndexedPredicateInduction.lift root (HOL.subst rho property)) (HOL.subst rho child)) := by
    apply ProofSyntax.castIndices ?_ ?_ ((ProofSyntax.subst rho lifted).prepend antecedent)
    · change antecedent :: assumptions.map (HOL.subst rho) = antecedent :: assumptions.map HOL.weaken
      apply congrArg (List.cons antecedent)
      apply List.map_congr_left
      intro formula _
      exact subst_ofRename Rename.weaken formula
    · simp only [HOL.subst, IndexedPredicateInduction.subst_lift, root]
  let memberProof := ProofSyntax.impE
    (ProofSyntax.eqPropER (signature.member_beta root (HOL.subst rho child) (.var .vz)))
    (ProofSyntax.andI childMember rootProof)
  let motiveProof := IndexedPredicateInduction.eliminate root (HOL.subst rho property)
    (HOL.subst rho child) (.var .vz) childLift rootProof
  exact .andI (.andEL original) (.andI (.andEL (.andER original)) (.andI memberProof motiveProof))

theorem consumeEdgeWitness_free {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (member : ProofSyntax Const assumptions (.app (positions.contextual bottom construct).least child))
    (lifted : ProofSyntax Const assumptions
      (.app (IndexedPredicateInduction.lift (constructors.rootProgram construct) property) child))
    (edge : ProofSyntax Const assumptions
      (.app (.app (.app (positions.edgeProgram construct) (encode constructors.fields occurrence arguments)) slot) child))
    (memberFree : member.FunctionExtensionalityFree) (liftedFree : lifted.FunctionExtensionalityFree)
    (edgeFree : edge.FunctionExtensionalityFree) :
    (positions.consumeEdgeWitness bottom construct property occurrence arguments slot child member lifted edge).FunctionExtensionalityFree := by
  unfold consumeEdgeWitness
  refine ⟨?_, positions.edgeProgramReadback_free construct occurrence arguments slot child edge edgeFree⟩
  apply (ContextualTrinity.exImp_free _).mpr
  refine ⟨trivial, trivial, ?_, ?_⟩
  · constructor
    · exact RecursiveSpacePredicate.Contextual.member_beta_free _ _ _ _
    · constructor
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr memberFree
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact ⟨ConstructorPrograms.rootProgram_beta_free _ _ _ _, trivial⟩
  · apply IndexedPredicateInduction.eliminate_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr liftedFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact ⟨ConstructorPrograms.rootProgram_beta_free _ _ _ _, trivial⟩

#print axioms consumeEdgeWitness
#print axioms consumeEdgeWitness_free

def guardedChildWitness {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space)) (slot : Term Const Γ constructors.number)
    (conditions : ProofSyntax Const assumptions ((positions.contextual bottom construct).childConditions
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
      (encode constructors.fields occurrence arguments) children))
    (active : ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot)) :
    ProofSyntax Const assumptions
      (positions.indexedEdgeWitness bottom construct property occurrence arguments slot (.app children slot)) := by
  let signature := positions.contextual bottom construct
  let root := constructors.rootProgram construct
  let components := signature.childComponents root property
    (encode constructors.fields occurrence arguments) children slot conditions active
  exact positions.consumeEdgeWitness bottom construct property occurrence arguments slot (.app children slot)
    (.andEL (.andER components)) (.andER (.andER components)) (.andEL components)

theorem guardedChildWitness_free {assumptions : List (Formula Const Γ)}
    (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space)) (slot : Term Const Γ constructors.number)
    (conditions : ProofSyntax Const assumptions ((positions.contextual bottom construct).childConditions
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
      (encode constructors.fields occurrence arguments) children))
    (active : ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot))
    (conditionsFree : conditions.FunctionExtensionalityFree) (activeFree : active.FunctionExtensionalityFree) :
    (positions.guardedChildWitness bottom construct property occurrence arguments children slot conditions active).FunctionExtensionalityFree := by
  unfold guardedChildWitness
  apply consumeEdgeWitness_free
  all_goals exact (RecursiveSpacePredicate.Contextual.childComponents_free
    (positions.contextual bottom construct) (constructors.rootProgram construct) property
    (encode constructors.fields occurrence arguments) children slot conditions active conditionsFree activeFree)

#print axioms guardedChildWitness_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
