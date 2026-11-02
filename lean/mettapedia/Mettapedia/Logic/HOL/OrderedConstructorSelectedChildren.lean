import Mettapedia.Logic.HOL.OrderedConstructorChildProofs
import Mettapedia.Logic.HOL.OrderedPositionSelection

/-!
# Child evidence retaining its original segment selection

The selected relation identifies the original segment occurrence as well as
the absolute slot. Its ordinary lookup supplies membership and the indexed
motive at that same array application. The selection remains in the result.
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

def selectedChildAtFromLookup (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (ordinal : Nat) (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (selected : ProofSyntax Const assumptions (selectedAt zero successor ordinal
      (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id slot requested)) :
    ProofSyntax Const assumptions
      (.and (selectedAt zero successor ordinal (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id slot requested)
        (.and (.app (.app (((ofSegments constructors zero successor plans).contextual bottom construct).memberProgram
            (constructors.rootProgram construct)) (.app children slot)) requested)
          (.app (.app property (.app children slot)) requested))) := by
  let ordinary := selectedAt_sound zero successor ordinal (fieldTerms _ (plans occurrence) Subst.id arguments)
    Subst.id slot requested selected
  let related := ProofSyntax.impE
    (ProofSyntax.eqPropER (fieldGraph_beta zero successor _ (plans occurrence) slot requested arguments)) ordinary
  exact .andI selected (.andER (childAtFromLookup constructors zero successor plans bottom construct property
    occurrence arguments children slot requested arithmetic conditions allowed related))

theorem selectedChildAtFromLookup_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (children : Term Const Γ (constructors.number ⇒ space))
    (ordinal : Nat) (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (conditions : ProofSyntax Const assumptions
      (((ofSegments constructors zero successor plans).contextual bottom construct).childConditions
        (PredicateFixedPoint.intersection
          ((ofSegments constructors zero successor plans).contextual bottom construct).least
          (IndexedPredicateInduction.lift (constructors.rootProgram construct) property))
        (encode constructors.fields occurrence arguments) children))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (selected : ProofSyntax Const assumptions (selectedAt zero successor ordinal
      (fieldTerms _ (plans occurrence) Subst.id arguments) Subst.id slot requested))
    (arithmeticFree : arithmetic.Free) (conditionsFree : conditions.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (selectedFree : selected.FunctionExtensionalityFree) :
    (selectedChildAtFromLookup constructors zero successor plans bottom construct property occurrence arguments children
      ordinal slot requested arithmetic conditions allowed selected).FunctionExtensionalityFree := by
  unfold selectedChildAtFromLookup
  constructor
  · exact selectedFree
  · apply childAtFromLookup_free
    · exact arithmeticFree
    · exact conditionsFree
    · exact allowedFree
    · exact ⟨fieldGraph_beta_free _ _ _ _ _ _ _, selectedAt_sound_free _ _ _ _ _ _ _ _ selectedFree⟩

#print axioms selectedChildAtFromLookup_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
