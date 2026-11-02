import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditions
import Mettapedia.Logic.HOL.ContextualConstructorAdmission
import Mettapedia.Logic.HOL.IndexedConstructorInduction

/-!
# Guarded recovery at the original mixed-vector constructor

The actual source allowed condition introduces its generated shape guard.
The complete source child condition supplies canonical padding. Together they
establish the admission predicate consumed by guarded payload/child recovery.
The constructor's guarded uniqueness and selection principles remain explicit;
this module does not assume unrestricted raw-payload injectivity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorAdmission
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorChildGuard
open FiniteConstructorEncoding CurriedPredicates

private def shapeFromAllowed {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (inventory : IndexedConstructorGuards.ConstructorPrograms Const Γ)
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (allowed : ProofSyntax Const Δ (applyArguments _ (inventory.allowed occurrence) arguments)) :
    ProofSyntax Const Δ (.app (.app inventory.shapeProgram (inventory.numeral occurrence.val))
      (encode inventory.fields occurrence arguments)) := by
  apply ProofSyntax.impE (.eqPropER (inventory.shapeProgram_beta _ _))
  apply ConstructorDataPredicates.introduce inventory.fields
    (inventory.shapeCondition (inventory.numeral occurrence.val)) occurrence arguments
  apply conjoin_intro _ arguments
  · exact allowed
  · exact constant_intro _ arguments (.eqRefl (inventory.numeral occurrence.val))

private theorem shapeFromAllowed_free {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (inventory : IndexedConstructorGuards.ConstructorPrograms Const Γ)
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (allowed : ProofSyntax Const Δ (applyArguments _ (inventory.allowed occurrence) arguments))
    (free : allowed.FunctionExtensionalityFree) :
    (shapeFromAllowed inventory occurrence arguments allowed).FunctionExtensionalityFree := by
  unfold shapeFromAllowed
  refine ⟨inventory.shapeProgram_beta_free _ _,?_⟩
  apply ConstructorDataPredicates.introduce_free
  apply conjoin_intro_free
  · exact free
  · exact constant_intro_free _ _ _ True.intro

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (payload : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E))
    (bottom : Term Const Γ E)

def signature := (positions payload).contextual bottom construct
def domain := (signature payload construct bottom).constructorAdmission

def sourceShape (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape)) :
    ProofSyntax Const Δ ((signature payload construct bottom).shapeAt (numeral Γ 0) (encoded payload length tag shape)) := by
  exact shapeFromAllowed (constructors payload) (occurrence payload) (sourceArguments payload length tag shape) allowed

theorem sourceShape_free (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (free : allowed.FunctionExtensionalityFree) :
    (sourceShape payload construct bottom length tag shape allowed).FunctionExtensionalityFree := by
  exact shapeFromAllowed_free (constructors payload) (occurrence payload) (sourceArguments payload length tag shape) allowed free

def sourceAdmission (elements : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N) (children : Term Const Γ (N ⇒ E))
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (conditions : ProofSyntax Const Δ
      ((signature payload construct bottom).childConditions elements (encoded payload length tag shape) children)) :
    ProofSyntax Const Δ (GuardedConstructorProjections.admitted (domain payload construct bottom)
      (numeral Γ 0) (encoded payload length tag shape) children) :=
  (signature payload construct bottom).admission_from_children elements (numeral Γ 0)
    (encoded payload length tag shape) children (sourceShape payload construct bottom length tag shape allowed) conditions

theorem sourceAdmission_free (elements : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N) (children : Term Const Γ (N ⇒ E))
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (conditions : ProofSyntax Const Δ
      ((signature payload construct bottom).childConditions elements (encoded payload length tag shape) children))
    (allowedFree : allowed.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (sourceAdmission payload construct bottom elements length tag shape children allowed conditions).FunctionExtensionalityFree :=
  (signature payload construct bottom).admission_from_children_free elements (numeral Γ 0)
    (encoded payload length tag shape) children _ conditions
    (sourceShape_free payload construct bottom length tag shape allowed allowedFree) conditionsFree

def recoverPayload (selection : Term Const Γ (SelectionProofs.Selection (payloadType [[N,E,N]])))
    (elements : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (shape : Term Const Γ N) (children : Term Const Γ (N ⇒ E))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (unique : ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective construct (domain payload construct bottom)))
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (conditions : ProofSyntax Const Δ
      ((signature payload construct bottom).childConditions elements (encoded payload length tag shape) children)) :
    ProofSyntax Const Δ (.eq
      (.app (GuardedConstructorProjections.secondProjection selection construct (domain payload construct bottom))
        (ConstructorProjections.apply construct (numeral Γ 0) (encoded payload length tag shape) children))
      (encoded payload length tag shape)) :=
  GuardedConstructorProjections.second_at selection construct (domain payload construct bottom) (numeral Γ 0)
    (encoded payload length tag shape) children choice unique
    (sourceAdmission payload construct bottom elements length tag shape children allowed conditions)

def recoverChildren (selection : Term Const Γ (SelectionProofs.Selection (N ⇒ E)))
    (elements : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (shape : Term Const Γ N) (children : Term Const Γ (N ⇒ E))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (unique : ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective construct (domain payload construct bottom)))
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (conditions : ProofSyntax Const Δ
      ((signature payload construct bottom).childConditions elements (encoded payload length tag shape) children)) :
    ProofSyntax Const Δ (.eq
      (.app (GuardedConstructorProjections.thirdProjection selection construct (domain payload construct bottom))
        (ConstructorProjections.apply construct (numeral Γ 0) (encoded payload length tag shape) children)) children) :=
  GuardedConstructorProjections.third_at selection construct (domain payload construct bottom) (numeral Γ 0)
    (encoded payload length tag shape) children choice unique
    (sourceAdmission payload construct bottom elements length tag shape children allowed conditions)

theorem recoverPayload_free (selection : Term Const Γ (SelectionProofs.Selection (payloadType [[N,E,N]])))
    (elements : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (shape : Term Const Γ N) (children : Term Const Γ (N ⇒ E))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (unique : ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective construct (domain payload construct bottom)))
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (conditions : ProofSyntax Const Δ
      ((signature payload construct bottom).childConditions elements (encoded payload length tag shape) children))
    (choiceFree : choice.FunctionExtensionalityFree) (uniqueFree : unique.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (recoverPayload payload construct bottom selection elements length tag shape children choice unique allowed conditions).FunctionExtensionalityFree :=
  GuardedConstructorProjections.second_at_free _ _ _ _ _ _ choice unique _ choiceFree uniqueFree
    (sourceAdmission_free payload construct bottom elements length tag shape children allowed conditions allowedFree conditionsFree)

theorem recoverChildren_free (selection : Term Const Γ (SelectionProofs.Selection (N ⇒ E)))
    (elements : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (shape : Term Const Γ N) (children : Term Const Γ (N ⇒ E))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (unique : ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective construct (domain payload construct bottom)))
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (conditions : ProofSyntax Const Δ
      ((signature payload construct bottom).childConditions elements (encoded payload length tag shape) children))
    (choiceFree : choice.FunctionExtensionalityFree) (uniqueFree : unique.FunctionExtensionalityFree)
    (allowedFree : allowed.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (recoverChildren payload construct bottom selection elements length tag shape children choice unique allowed conditions).FunctionExtensionalityFree :=
  GuardedConstructorProjections.third_at_free _ _ _ _ _ _ choice unique _ choiceFree uniqueFree
    (sourceAdmission_free payload construct bottom elements length tag shape children allowed conditions allowedFree conditionsFree)

#print axioms sourceAdmission_free
#print axioms recoverPayload_free
#print axioms recoverChildren_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorAdmission
