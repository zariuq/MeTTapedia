import Mettapedia.Logic.HOL.ConstructorRowChildProofs

/-!
# Requested child indices through retained comparisons

An existential child witness is kept until a supplied retained comparison
identifies its guarded row index with the requested one. Equality transports
both membership and the motive before the witness scope is closed. The
comparison is an explicit proof obligation, separate from activity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (signature : Contextual Const Γ) {index : Ty Base}

theorem memberProgram_subst (images : Subst Const Γ Ξ) (root : Term Const Γ (signature.space ⇒ index ⇒ .prop)) :
    HOL.subst images (signature.memberProgram root) =
      (signature.subst images).memberProgram (HOL.subst images root) := by
  simp only [memberProgram, CurriedGuardProgramProofs.subst_conjunctionProgram, subst_least]

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)

def indexComparisonBody (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index) :
    Formula Const (constructors.index :: Γ) :=
  let images : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let fields := substituteArguments images _ arguments
  .imp (.and (applyArguments _ ((constructors.subst images).allowed occurrence) fields)
    (applyArguments _ (.app (.app ((positions.subst images).graph occurrence) (HOL.subst images slot)) (.var .vz)) fields))
    (.eq (.var .vz) (HOL.subst images requested))

def indexComparison (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index) : Formula Const Γ :=
  .all (positions.indexComparisonBody occurrence arguments slot requested)

variable {space : Ty Base} (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    (property : Term Const Γ (space ⇒ constructors.index ⇒ .prop))
    {assumptions : List (Formula Const Γ)}

def selectIndexedEdgeWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (requested : Term Const Γ constructors.index)
    (witness : ProofSyntax Const assumptions
      (positions.indexedEdgeWitness bottom construct property occurrence arguments slot child))
    (comparison : ProofSyntax Const assumptions (positions.indexComparison occurrence arguments slot requested)) :
    ProofSyntax Const assumptions
      (.and (.app (.app ((positions.contextual bottom construct).memberProgram (constructors.rootProgram construct)) child) requested)
        (.app (.app property child) requested)) := by
  apply ProofSyntax.exE witness
  let images : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let body := positions.indexedEdgeBody bottom construct property occurrence arguments slot child
  let hypotheses := body :: weakenHyps assumptions
  let signature := (positions.contextual bottom construct).subst images
  let root := HOL.subst images (constructors.rootProgram construct)
  let present : ProofSyntax Const hypotheses body := .hyp 0
  let comparisonAt := ContextualTrinity.instantiateFresh
    ((ProofSyntax.rename Rename.weaken comparison).prepend body)
  have equal : ProofSyntax Const hypotheses (.eq (.var .vz) (HOL.subst images requested)) :=
    .impE comparisonAt (.andI (.andEL present) (.andEL (.andER present)))
  let memberFunction := Term.app (signature.memberProgram root) (HOL.subst images child)
  let propertyFunction := Term.app (HOL.subst images property) (HOL.subst images child)
  let selectedMember := ProofSyntax.impE (.eqPropEL (.eqAppArg memberFunction equal)) (.andEL (.andER (.andER present)))
  let selectedProperty := ProofSyntax.impE (.eqPropEL (.eqAppArg propertyFunction equal)) (.andER (.andER (.andER present)))
  apply ProofSyntax.castIndices rfl ?_ (.andI selectedMember selectedProperty)
  change Term.and
      (.app (.app (signature.memberProgram root) (HOL.subst images child)) (HOL.subst images requested))
      (.app (.app (HOL.subst images property) (HOL.subst images child)) (HOL.subst images requested)) = _
  rw [← (positions.contextual bottom construct).memberProgram_subst images (constructors.rootProgram construct)]
  change HOL.subst images
      (.and (.app (.app ((positions.contextual bottom construct).memberProgram (constructors.rootProgram construct)) child) requested)
        (.app (.app property child) requested)) = _
  exact subst_ofRename Rename.weaken _

theorem selectIndexedEdgeWitness_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space)
    (requested : Term Const Γ constructors.index)
    (witness : ProofSyntax Const assumptions
      (positions.indexedEdgeWitness bottom construct property occurrence arguments slot child))
    (comparison : ProofSyntax Const assumptions (positions.indexComparison occurrence arguments slot requested))
    (witnessFree : witness.FunctionExtensionalityFree) (comparisonFree : comparison.FunctionExtensionalityFree) :
    (positions.selectIndexedEdgeWitness bottom construct property occurrence arguments slot child requested witness comparison).FunctionExtensionalityFree := by
  unfold selectIndexedEdgeWitness
  refine ⟨witnessFree, ?_⟩
  simp only [ProofSyntax.functionExtensionalityFree_castIndices]
  constructor
  all_goals
    constructor
    · constructor
      · apply (ContextualTrinity.instantiateFresh_free _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr comparisonFree
      · trivial
    · trivial

#print axioms RecursiveSpacePredicate.Contextual.memberProgram_subst
#print axioms selectIndexedEdgeWitness_free

def requestedChildHypothesis (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (conditions : ProofSyntax Const assumptions ((positions.contextual bottom construct).childConditions
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
      (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) requested) arguments))
    (comparison : ProofSyntax Const assumptions (positions.indexComparison occurrence arguments slot requested)) :
    ProofSyntax Const assumptions
      (.and (.app (.app ((positions.contextual bottom construct).memberProgram (constructors.rootProgram construct))
        (.app children slot)) requested) (.app (.app property (.app children slot)) requested)) :=
  positions.selectIndexedEdgeWitness bottom construct property occurrence arguments slot (.app children slot) requested
    (positions.originalChildWitness bottom construct property occurrence arguments children slot requested conditions allowed related)
    comparison

theorem requestedChildHypothesis_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (conditions : ProofSyntax Const assumptions ((positions.contextual bottom construct).childConditions
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
      (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) requested) arguments))
    (comparison : ProofSyntax Const assumptions (positions.indexComparison occurrence arguments slot requested))
    (conditionsFree : conditions.FunctionExtensionalityFree) (allowedFree : allowed.FunctionExtensionalityFree)
    (relatedFree : related.FunctionExtensionalityFree) (comparisonFree : comparison.FunctionExtensionalityFree) :
    (positions.requestedChildHypothesis bottom construct property occurrence arguments children slot requested
      conditions allowed related comparison).FunctionExtensionalityFree :=
  positions.selectIndexedEdgeWitness_free bottom construct property occurrence arguments slot (.app children slot) requested
    (positions.originalChildWitness bottom construct property occurrence arguments children slot requested conditions allowed related)
    comparison (positions.originalChildWitness_free bottom construct property occurrence arguments children slot requested
      conditions allowed related conditionsFree allowedFree relatedFree) comparisonFree

#print axioms requestedChildHypothesis_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
