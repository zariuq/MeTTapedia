import Mettapedia.Logic.HOL.ConstructorDataPredicatePrograms
import Mettapedia.Logic.HOL.IndexedConstructorInduction
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.ContextualConstructorAdmission

/-!
# Constructor-shape elimination into guarded payload membership

Each actual shape case retains its occurrence, original row condition and
payload equation. A checked implication on that row introduces the target
data guard at the same payload. Typed substitutions and hypothesis
occurrences remain explicit throughout the elimination.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {Δ : List (Formula Const Γ)}

def RowImplication (premises : List (Formula Const Γ)) (inventory : ConstructorPrograms Const Γ)
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (_transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (occurrence : Fin inventory.fields.length) (arguments : Arguments Const Ξ (inventory.fields.get occurrence)),
    ProofSyntax Const assumptions (applyArguments _ (HOL.subst images (inventory.allowed occurrence)) arguments) →
    ProofSyntax Const assumptions (applyArguments _ (HOL.subst images (conditions occurrence)) arguments)

def RowImplication.Free {premises : List (Formula Const Γ)} {inventory : ConstructorPrograms Const Γ}
    {conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields}
    (refine : RowImplication premises inventory conditions) : Prop :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (occurrence : Fin inventory.fields.length) (arguments : Arguments Const Ξ (inventory.fields.get occurrence))
    (allowed : ProofSyntax Const assumptions (applyArguments _ (HOL.subst images (inventory.allowed occurrence)) arguments)),
    allowed.FunctionExtensionalityFree → (refine images transport occurrence arguments allowed).FunctionExtensionalityFree

def shapeDataCase (inventory : ConstructorPrograms Const Γ)
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication Δ inventory conditions)
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (occurrence : Fin inventory.fields.length) :
    FieldCase Δ (inventory.fields.get occurrence) (inventory.shapeCasePredicate tag payload occurrence)
      (ConstructorDataPredicates.guard inventory.fields conditions payload) := by
  intro Ξ images arguments
  let localHypotheses := applyArguments _
    (HOL.subst images (inventory.shapeCasePredicate tag payload occurrence)) arguments :: Δ.map (HOL.subst images)
  have current : ProofSyntax Const localHypotheses (applyArguments _
      ((inventory.subst images).shapeCasePredicate (HOL.subst images tag) (HOL.subst images payload) occurrence) arguments) :=
    .castIndices rfl (congrArg (fun predicate => applyArguments _ predicate arguments)
      (inventory.shapeCasePredicate_subst images tag payload occurrence)) (.hyp 0)
  have parts := (inventory.subst images).shapeCase_parts (HOL.subst images tag) (HOL.subst images payload)
    occurrence arguments current
  let transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) localHypotheses :=
    ⟨fun index => index.succ,fun _ => rfl⟩
  have allowed := refine images transport occurrence arguments (.andEL parts)
  have result := ConstructorDataPredicates.introduceAt (fun index => HOL.subst images (conditions index))
    (HOL.subst images payload) occurrence arguments allowed (.andER (.andER parts))
  exact .castIndices rfl (ConstructorDataPredicates.guard_subst images inventory.fields conditions payload).symm result

theorem shapeDataCase_free (inventory : ConstructorPrograms Const Γ)
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication Δ inventory conditions) (refineFree : RowImplication.Free refine)
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (occurrence : Fin inventory.fields.length) (images : Subst Const Γ Ξ)
    (arguments : Arguments Const Ξ (inventory.fields.get occurrence)) :
    (shapeDataCase inventory conditions refine tag payload occurrence images arguments).FunctionExtensionalityFree := by
  unfold shapeDataCase
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ConstructorDataPredicates.introduceAt_free
  · apply refineFree
    apply shapeCase_parts_free
    exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro
  · apply shapeCase_parts_free
    exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def shapeDataGuard (inventory : ConstructorPrograms Const Γ)
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication Δ inventory conditions)
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (present : ProofSyntax Const Δ (.app (.app inventory.shapeProgram tag) payload)) :
    ProofSyntax Const Δ (ConstructorDataPredicates.guard inventory.fields conditions payload) :=
  inventory.shapeProgram_elim tag payload _ (shapeDataCase inventory conditions refine tag payload) present

theorem shapeDataGuard_free (inventory : ConstructorPrograms Const Γ)
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication Δ inventory conditions) (refineFree : RowImplication.Free refine)
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (present : ProofSyntax Const Δ (.app (.app inventory.shapeProgram tag) payload))
    (presentFree : present.FunctionExtensionalityFree) :
    (shapeDataGuard inventory conditions refine tag payload present).FunctionExtensionalityFree :=
  inventory.shapeProgram_elim_free tag payload _ _ present
    (fun occurrence {Ξ} images arguments =>
      shapeDataCase_free (Ξ := Ξ) inventory conditions refine refineFree tag payload occurrence images arguments) presentFree

#print axioms shapeDataGuard
#print axioms shapeDataGuard_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding ConstructorPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {inventory : ConstructorPrograms Const Γ} {space : Ty Base} {Δ : List (Formula Const Γ)}

def admissionDataGuard (positions : PositionPrograms inventory)
    (bottom : Term Const Γ space)
    (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication Δ inventory conditions)
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (children : Term Const Γ (inventory.number ⇒ space))
    (present : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (positions.contextual bottom construct).constructorAdmission tag payload children)) :
    ProofSyntax Const Δ (ConstructorDataPredicates.guard inventory.fields conditions payload) :=
  inventory.shapeDataGuard conditions refine tag payload (.andEL (.impE (.eqPropEL
    ((positions.contextual bottom construct).constructorAdmission_at tag payload children)) present))

theorem admissionDataGuard_free (positions : PositionPrograms inventory)
    (bottom : Term Const Γ space)
    (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication Δ inventory conditions) (refineFree : RowImplication.Free refine)
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (children : Term Const Γ (inventory.number ⇒ space))
    (present : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (positions.contextual bottom construct).constructorAdmission tag payload children))
    (presentFree : present.FunctionExtensionalityFree) :
    (admissionDataGuard positions bottom construct conditions refine tag payload children present).FunctionExtensionalityFree :=
  inventory.shapeDataGuard_free conditions refine refineFree tag payload _
    ⟨(positions.contextual bottom construct).constructorAdmission_at_free tag payload children,presentFree⟩

#print axioms admissionDataGuard
#print axioms admissionDataGuard_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
