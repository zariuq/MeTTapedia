import Mettapedia.Logic.HOL.ConstructorGuardSubstitution
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionTransport

/-!
# Transported constructor admission and retained payload guards

Admission of the original position program yields its actual constructor
shape after typed substitution. A transported row implication then yields
the corresponding data guard at the same payload. The substitution and
hypothesis-occurrence transports remain explicit, and each construction
preserves freedom from function extensionality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding ConstructorPrograms

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {inventory : ConstructorPrograms Const Γ} {space : Ty Base}
  {premises : List (Formula Const Γ)}

@[irreducible] def admissionShapeSubst (positions : PositionPrograms inventory)
    (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ inventory.number) (payload : Term Const Ξ (payloadType inventory.fields))
    (children : Term Const Ξ (inventory.number ⇒ space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (positions.contextual bottom construct).constructorAdmission) tag payload children)) :
    ProofSyntax Const assumptions (.app (.app (inventory.subst images).shapeProgram tag) payload) :=
  .castIndices rfl
    (congrArg (fun program => Term.app (Term.app program tag) payload)
      (inventory.shapeProgram_subst images))
    ((positions.contextual bottom construct).admissionShapeSubst images tag payload children present)

theorem admissionShapeSubst_free (positions : PositionPrograms inventory)
    (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (tag : Term Const Ξ inventory.number) (payload : Term Const Ξ (payloadType inventory.fields))
    (children : Term Const Ξ (inventory.number ⇒ space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (positions.contextual bottom construct).constructorAdmission) tag payload children))
    (presentFree : present.FunctionExtensionalityFree) :
    (admissionShapeSubst positions bottom construct images tag payload children present).FunctionExtensionalityFree := by
  unfold admissionShapeSubst
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (positions.contextual bottom construct).admissionShapeSubst_free
    images tag payload children present presentFree

@[irreducible] def admissionDataGuardSubst (positions : PositionPrograms inventory)
    (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication premises inventory conditions)
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ inventory.number) (payload : Term Const Ξ (payloadType inventory.fields))
    (children : Term Const Ξ (inventory.number ⇒ space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (positions.contextual bottom construct).constructorAdmission) tag payload children)) :
    ProofSyntax Const assumptions (ConstructorDataPredicates.guard inventory.fields
      (fun occurrence => HOL.subst images (conditions occurrence)) payload) :=
  (inventory.subst images).shapeDataGuard (fun occurrence => HOL.subst images (conditions occurrence))
    (RowImplication.reindexPremises (RowImplication.substitute refine images) transport) tag payload
    (admissionShapeSubst positions bottom construct images tag payload children present)

theorem admissionDataGuardSubst_free (positions : PositionPrograms inventory)
    (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (conditions : ConstructorDataPredicates.Conditions Const Γ inventory.fields)
    (refine : RowImplication premises inventory conditions) (refineFree : RowImplication.Free refine)
    (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ inventory.number) (payload : Term Const Ξ (payloadType inventory.fields))
    (children : Term Const Ξ (inventory.number ⇒ space))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (positions.contextual bottom construct).constructorAdmission) tag payload children))
    (presentFree : present.FunctionExtensionalityFree) :
    (admissionDataGuardSubst positions bottom construct conditions refine images transport
      tag payload children present).FunctionExtensionalityFree := by
  unfold admissionDataGuardSubst
  exact (inventory.subst images).shapeDataGuard_free
    (fun occurrence => HOL.subst images (conditions occurrence))
    (RowImplication.reindexPremises (RowImplication.substitute refine images) transport)
    (RowImplication.reindexPremises_free _ (RowImplication.substitute_free refine refineFree images) transport)
    tag payload (admissionShapeSubst positions bottom construct images tag payload children present)
    (admissionShapeSubst_free positions bottom construct images tag payload children present presentFree)

#print axioms admissionShapeSubst
#print axioms admissionShapeSubst_free
#print axioms admissionDataGuardSubst
#print axioms admissionDataGuardSubst_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
