import Mettapedia.Logic.HOL.OrderedPositionFunctionality

/-!
# Original child premises from an ordered lookup

The positive original-field lookup constructs its own guarded index
comparison. It then yields membership and the motive at the requested
index, retaining the lookup and the same child slot in one conjunction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number)
    (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {space : Ty Base} (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))
    (property : Term Const Γ (space ⇒ constructors.index ⇒ .prop))
    {assumptions : List (Formula Const Γ)}

def childAtFromLookup (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (fieldGraph zero successor _ (plans occurrence)) slot) requested) arguments)) :
    ProofSyntax Const assumptions
      (.and
        (applyArguments _ (.app (.app (fieldGraph zero successor _ (plans occurrence)) slot) requested) arguments)
        (.and (.app (.app
            (((ofSegments constructors zero successor plans).contextual bottom construct).memberProgram
              (constructors.rootProgram construct)) (.app children slot)) requested)
          (.app (.app property (.app children slot)) requested))) := by
  let comparison := guardedIndexComparisonFromWitness constructors zero successor plans occurrence arguments slot
    requested arithmetic (related.prepend (applyArguments _ (constructors.allowed occurrence) arguments))
  exact .andI related ((ofSegments constructors zero successor plans).requestedChildHypothesis bottom construct property
    occurrence arguments children slot requested conditions allowed related comparison)

theorem childAtFromLookup_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (fieldGraph zero successor _ (plans occurrence)) slot) requested) arguments))
    (arithmeticFree : arithmetic.Free) (conditionsFree : conditions.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    (childAtFromLookup constructors zero successor plans bottom construct property occurrence arguments children slot
      requested arithmetic conditions allowed related).FunctionExtensionalityFree := by
  unfold childAtFromLookup
  refine ⟨relatedFree, ?_⟩
  apply requestedChildHypothesis_free
  · exact conditionsFree
  · exact allowedFree
  · exact relatedFree
  · apply guardedIndexComparisonFromWitness_free
    · exact arithmeticFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr relatedFree

#print axioms childAtFromLookup
#print axioms childAtFromLookup_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
