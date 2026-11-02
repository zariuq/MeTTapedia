import Mettapedia.Logic.HOL.OrderedConstructorSelectedChildren
import Mettapedia.Logic.HOL.OrderedPositionOffsets

/-!
# Original child evidence at an exact local segment position

The offset relation selects the same absolute child application used by the
existing membership and motive proofs. The result keeps that offset relation
alongside both conclusions. Constructor fields and the child array stay open.
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

def childAtLocalPosition (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (segment : Fin (fieldTerms _ (plans occurrence) Subst.id arguments).length)
    (localPos slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (offset : ProofSyntax Const assumptions (selectedOffsetAt zero successor segment.val
      (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id localPos slot))
    (bounded : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) localPos)
      (HOL.subst Subst.id ((fieldTerms _ (plans occurrence) Subst.id arguments).get segment).1)))
    (indexEqual : ProofSyntax Const assumptions (.eq requested
      (HOL.subst Subst.id ((fieldTerms _ (plans occurrence) Subst.id arguments).get segment).2))) :
    ProofSyntax Const assumptions
      (.and (selectedOffsetAt zero successor segment.val
        (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id localPos slot)
        (.and (.app (.app (((ofSegments constructors zero successor plans).contextual bottom construct).memberProgram
            (constructors.rootProgram construct)) (.app children slot)) requested)
          (.app (.app property (.app children slot)) requested))) :=
  .andI offset (.andER (selectedChildAtFromLookup constructors zero successor plans bottom construct property
    occurrence arguments children segment.val slot requested arithmetic conditions allowed
    (selectedOffsetAt_selected zero successor _ segment Subst.id localPos slot requested offset bounded indexEqual)))

theorem childAtLocalPosition_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (segment : Fin (fieldTerms _ (plans occurrence) Subst.id arguments).length)
    (localPos slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (offset : ProofSyntax Const assumptions (selectedOffsetAt zero successor segment.val
      (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id localPos slot))
    (bounded : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) localPos)
      (HOL.subst Subst.id ((fieldTerms _ (plans occurrence) Subst.id arguments).get segment).1)))
    (indexEqual : ProofSyntax Const assumptions (.eq requested
      (HOL.subst Subst.id ((fieldTerms _ (plans occurrence) Subst.id arguments).get segment).2)))
    (arithmeticFree : arithmetic.Free) (conditionsFree : conditions.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (offsetFree : offset.FunctionExtensionalityFree)
    (boundedFree : bounded.FunctionExtensionalityFree) (indexFree : indexEqual.FunctionExtensionalityFree) :
    (childAtLocalPosition constructors zero successor plans bottom construct property occurrence arguments children
      segment localPos slot requested arithmetic conditions allowed offset bounded indexEqual).FunctionExtensionalityFree := by
  refine ⟨offsetFree, ?_⟩
  apply selectedChildAtFromLookup_free
  · exact arithmeticFree
  · exact conditionsFree
  · exact allowedFree
  · exact selectedOffsetAt_selected_free zero successor _ segment Subst.id localPos slot requested
      offset bounded indexEqual offsetFree boundedFree indexFree

#print axioms childAtLocalPosition_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
