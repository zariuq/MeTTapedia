import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamily
import Mettapedia.Logic.HOL.ConstructorPositionSubstitution
import Mettapedia.Logic.HOL.IndexedContainerFieldProofs
import Mettapedia.Logic.HOL.IndexedContainerIndexPrograms
import Mettapedia.Logic.HOL.OrderedConstructorChildExistence
import Mathlib.Tactic.FinCases

/-!
# Typed substitution of the family derived from the parsed inventory

The original answer predicate, numeric guard, constructor terms, ordinal
programs and bottom are transported together. Inventory equality follows
from the actual compiled row guards and position programs; the family is
never identified with an independently supplied predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyTransport
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding IndexedConstructorGuards OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {N A E : Ty Base}
  (images : Subst Const Γ Ξ) (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
  (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)

theorem allowed_subst (occurrence : Fin (VectorTreeFieldEmbedding.storedSignature N E).length) :
    HOL.subst images ((IndexedVectorTreeStoredFamily.inventory given source numbers zero one tags).allowed occurrence) =
      (IndexedVectorTreeStoredFamily.inventory (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one (fun n => HOL.subst images (tags n))).allowed occurrence := by
  unfold IndexedVectorTreeStoredFamily.inventory
  rw [IndexedVectorTreeStoredFieldGuards.allowed_eq, IndexedVectorTreeStoredFieldGuards.allowed_eq]
  exact IndexedVectorTreeStoredFieldGuards.compiledConditions_subst given source numbers zero one images occurrence

theorem inventory_subst :
    (IndexedVectorTreeStoredFamily.inventory given source numbers zero one tags).subst images =
      IndexedVectorTreeStoredFamily.inventory (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one (fun n => HOL.subst images (tags n)) := by
  unfold IndexedVectorTreeStoredFamily.inventory IndexedVectorTreeStoredFieldGuards.inventory
    IndexedContainerPositionTerms.FieldGuards.constructors ConstructorPrograms.subst
  congr 1
  · funext occurrence
    exact allowed_subst images given source numbers zero one tags occurrence
  · funext occurrence
    fin_cases occurrence <;> rfl

theorem plans_subst (occurrence : Fin (VectorTreeFieldEmbedding.storedSignature N E).length) :
    substitute images
      (IndexedContainerPositionTerms.FieldGuards.plans
        (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one)
        IndexedVectorTreeStoredFieldGuards.codes Subst.id occurrence) =
      IndexedContainerPositionTerms.FieldGuards.plans
        (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Ξ) (E := E) one)
        IndexedVectorTreeStoredFieldGuards.codes Subst.id occurrence := by
  fin_cases occurrence <;> rfl

private theorem shape_heq {first second : ConstructorPrograms Const Ξ} (same : first = second) :
    HEq first.shapeProgram second.shapeProgram := by cases same; rfl

private theorem root_heq {first second : ConstructorPrograms Const Ξ} {space : Ty Base}
    (same : first = second)
    (left : Term Const Ξ (first.number ⇒ payloadType first.fields ⇒ (first.number ⇒ space) ⇒ space))
    (right : Term Const Ξ (second.number ⇒ payloadType second.fields ⇒ (second.number ⇒ space) ⇒ space))
    (constructors : HEq left right) : HEq (first.rootProgram left) (second.rootProgram right) := by
  cases same
  cases constructors
  rfl

private theorem least_heq {first second : RecursiveSpacePredicate.Contextual Const Ξ} (same : first = second) :
    HEq first.least second.least := by cases same; rfl

theorem shape_subst :
    HOL.subst images (IndexedVectorTreeStoredFamily.inventory given source numbers zero one tags).shapeProgram =
      (IndexedVectorTreeStoredFamily.inventory (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one (fun n => HOL.subst images (tags n))).shapeProgram := by
  rw [ConstructorPrograms.shapeProgram_subst]
  exact eq_of_heq (shape_heq (inventory_subst images given source numbers zero one tags))

theorem root_subst :
    HOL.subst images (IndexedVectorTreeStoredFamily.root given source numbers zero one tags) =
      IndexedVectorTreeStoredFamily.root (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one (fun n => HOL.subst images (tags n)) := by
  unfold IndexedVectorTreeStoredFamily.root IndexedVectorTreeStoredFamily.construct
  rw [ConstructorPrograms.rootProgram_subst]
  exact eq_of_heq (root_heq (inventory_subst images given source numbers zero one tags) _ _
    (heq_of_eq (IndexedVectorTreeStoredConstructorRecovery.storedConstructor_subst given images)))

theorem active_subst :
    HOL.subst images (IndexedVectorTreeStoredConstructorRecovery.positions given source numbers zero one successor tags).activeProgram =
      (IndexedVectorTreeStoredConstructorRecovery.positions (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n))).activeProgram := by
  change HOL.subst images
    (PositionPrograms.ofSegments (IndexedVectorTreeStoredFamily.inventory given source numbers zero one tags)
      zero successor (IndexedContainerPositionTerms.FieldGuards.plans
        (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one)
        IndexedVectorTreeStoredFieldGuards.codes Subst.id)).activeProgram =
    (PositionPrograms.ofSegments (IndexedVectorTreeStoredFamily.inventory (given.substitute images)
      (HOL.subst images source) (HOL.subst images numbers) zero one (fun n => HOL.subst images (tags n)))
      zero successor (IndexedContainerPositionTerms.FieldGuards.plans
        (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Ξ) (E := E) one)
        IndexedVectorTreeStoredFieldGuards.codes Subst.id)).activeProgram
  rw [PositionPrograms.activeProgram_subst, PositionPrograms.ofSegments_subst]
  simp only [plans_subst]
  have same := inventory_subst images given source numbers zero one tags
  simp only [IndexedVectorTreeStoredFamily.inventory, IndexedVectorTreeStoredFieldGuards.inventory,
    IndexedContainerPositionTerms.FieldGuards.constructors, ConstructorPrograms.subst] at same ⊢
  simp only [ConstructorPrograms.mk.injEq, heq_eq_eq, true_and] at same
  rcases same with ⟨_fields,_number,_index,allowed,result⟩
  rw [allowed,result]
  rfl

theorem edge_subst :
    HOL.subst images ((IndexedVectorTreeStoredConstructorRecovery.positions given source numbers zero one successor tags).edgeProgram
      (IndexedVectorTreeStoredFamily.construct given)) =
      (IndexedVectorTreeStoredConstructorRecovery.positions (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n))).edgeProgram
      (IndexedVectorTreeStoredFamily.construct (given.substitute images)) := by
  change HOL.subst images
    ((PositionPrograms.ofSegments (IndexedVectorTreeStoredFamily.inventory given source numbers zero one tags)
      zero successor (IndexedContainerPositionTerms.FieldGuards.plans
        (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one)
        IndexedVectorTreeStoredFieldGuards.codes Subst.id)).edgeProgram (IndexedVectorTreeStoredFamily.construct given)) =
    (PositionPrograms.ofSegments (IndexedVectorTreeStoredFamily.inventory (given.substitute images)
      (HOL.subst images source) (HOL.subst images numbers) zero one (fun n => HOL.subst images (tags n)))
      zero successor (IndexedContainerPositionTerms.FieldGuards.plans
        (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Ξ) (E := E) one)
        IndexedVectorTreeStoredFieldGuards.codes Subst.id)).edgeProgram
      (IndexedVectorTreeStoredFamily.construct (given.substitute images))
  rw [PositionPrograms.edgeProgram_subst, PositionPrograms.ofSegments_subst]
  simp only [plans_subst]
  have same := inventory_subst images given source numbers zero one tags
  simp only [IndexedVectorTreeStoredFamily.inventory, IndexedVectorTreeStoredFieldGuards.inventory,
    IndexedContainerPositionTerms.FieldGuards.constructors, ConstructorPrograms.subst] at same ⊢
  simp only [ConstructorPrograms.mk.injEq, heq_eq_eq, true_and] at same
  rcases same with ⟨_fields,_number,_index,allowed,result⟩
  rw [allowed,result]
  exact congrArg _ (IndexedVectorTreeStoredConstructorRecovery.storedConstructor_subst given images)

theorem signature_subst :
    (IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom).subst images =
      IndexedVectorTreeStoredFamily.signature (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n)) (HOL.subst images bottom) := by
  apply RecursiveSpacePredicate.Contextual.eq_of_fields
    (first := (IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom).subst images)
    (second := IndexedVectorTreeStoredFamily.signature (given.substitute images) (HOL.subst images source)
      (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n)) (HOL.subst images bottom))
    rfl rfl rfl (HEq.rfl)
  · exact heq_of_eq (IndexedVectorTreeStoredConstructorRecovery.storedConstructor_subst given images)
  · exact heq_of_eq (shape_subst images given source numbers zero one tags)
  · exact heq_of_eq (active_subst images given source numbers zero one successor tags)
  · exact heq_of_eq (edge_subst images given source numbers zero one successor tags)

theorem least_subst :
    HOL.subst images (IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom).least =
      (IndexedVectorTreeStoredFamily.signature (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n)) (HOL.subst images bottom)).least := by
  have least := eq_of_heq (least_heq
    (first := (IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom).subst images)
    (second := IndexedVectorTreeStoredFamily.signature (given.substitute images) (HOL.subst images source)
      (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n)) (HOL.subst images bottom))
    (signature_subst images given source numbers zero one successor tags bottom))
  rw [RecursiveSpacePredicate.Contextual.subst_least]
  exact least

theorem member_subst :
    HOL.subst images (IndexedVectorTreeStoredFamily.member given source numbers zero one successor tags bottom) =
      IndexedVectorTreeStoredFamily.member (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n)) (HOL.subst images bottom) := by
  simp only [IndexedVectorTreeStoredFamily.member, RecursiveSpacePredicate.Contextual.memberProgram,
    CurriedGuardProgramProofs.subst_conjunctionProgram, least_subst,root_subst]

theorem family_subst :
    HOL.subst images (IndexedVectorTreeStoredFamily.family given source numbers zero one successor tags bottom) =
      IndexedVectorTreeStoredFamily.family (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n)) (HOL.subst images bottom) := by
  change HOL.subst images
    (.lam (.app (.app (weaken (IndexedVectorTreeStoredFamily.member given source numbers zero one successor tags bottom))
      (.var .vz)) .top)) =
    .lam (.app (.app (weaken (IndexedVectorTreeStoredFamily.member (given.substitute images) (HOL.subst images source)
      (HOL.subst images numbers) zero one successor (fun n => HOL.subst images (tags n)) (HOL.subst images bottom))) (.var .vz)) .top)
  simp only [HOL.subst,subst_weaken,member_subst,Subst.lift]

theorem family_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (IndexedVectorTreeStoredFamily.family given source numbers zero one successor tags bottom) =
      IndexedVectorTreeStoredFamily.family (given.substitute (Subst.ofRename rho)) (HOL.rename rho source)
        (HOL.rename rho numbers) zero one successor (fun n => HOL.rename rho (tags n)) (HOL.rename rho bottom) := by
  simpa only [subst_ofRename] using family_subst (Subst.ofRename rho) given source numbers zero one successor tags bottom

private theorem rename_three {X Y Z T : Ty Base} (rho : Rename Base Γ Ξ)
    (build : Term Const Ξ X → Term Const Ξ Y → (Nat → Term Const Ξ Z) → Term Const Ξ T)
    (first : Term Const Γ X) (second : Term Const Γ Y) (third : Nat → Term Const Γ Z) :
    build (HOL.subst (Subst.ofRename rho) first) (HOL.subst (Subst.ofRename rho) second)
      (fun n => HOL.subst (Subst.ofRename rho) (third n)) =
    build (HOL.rename rho first) (HOL.rename rho second) (fun n => HOL.rename rho (third n)) := by
  have last : (fun n => HOL.subst (Subst.ofRename rho) (third n)) = (fun n => HOL.rename rho (third n)) :=
    funext (fun n => subst_ofRename rho (third n))
  rw [subst_ofRename,subst_ofRename,last]

private theorem rename_four {X Y Z B T : Ty Base} (rho : Rename Base Γ Ξ)
    (build : Term Const Ξ X → Term Const Ξ Y → (Nat → Term Const Ξ Z) → Term Const Ξ B → Term Const Ξ T)
    (first : Term Const Γ X) (second : Term Const Γ Y) (third : Nat → Term Const Γ Z) (fourth : Term Const Γ B) :
    build (HOL.subst (Subst.ofRename rho) first) (HOL.subst (Subst.ofRename rho) second)
      (fun n => HOL.subst (Subst.ofRename rho) (third n)) (HOL.subst (Subst.ofRename rho) fourth) =
    build (HOL.rename rho first) (HOL.rename rho second) (fun n => HOL.rename rho (third n)) (HOL.rename rho fourth) := by
  have earlier := rename_three rho (fun a b c => build a b c (HOL.subst (Subst.ofRename rho) fourth)) first second third
  exact earlier.trans (congrArg (build (HOL.rename rho first) (HOL.rename rho second) (fun n => HOL.rename rho (third n)))
    (subst_ofRename rho fourth))

set_option maxHeartbeats 1000000 in
theorem least_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom).least =
      (IndexedVectorTreeStoredFamily.signature (given.substitute (Subst.ofRename rho)) (HOL.rename rho source)
        (HOL.rename rho numbers) zero one successor (fun n => HOL.rename rho (tags n)) (HOL.rename rho bottom)).least := by
  exact (subst_ofRename rho _).symm.trans
    ((least_subst (Subst.ofRename rho) given source numbers zero one successor tags bottom).trans
      (rename_four (T := E ⇒ .prop) rho (fun p ns ts b =>
        (IndexedVectorTreeStoredFamily.signature (given.substitute (Subst.ofRename rho)) p ns zero one successor ts b).least)
        source numbers tags bottom))

set_option maxHeartbeats 1000000 in
theorem active_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (IndexedVectorTreeStoredConstructorRecovery.positions given source numbers zero one successor tags).activeProgram =
      (IndexedVectorTreeStoredConstructorRecovery.positions (given.substitute (Subst.ofRename rho)) (HOL.rename rho source)
        (HOL.rename rho numbers) zero one successor (fun n => HOL.rename rho (tags n))).activeProgram := by
  exact (subst_ofRename rho _).symm.trans
    ((active_subst (Subst.ofRename rho) given source numbers zero one successor tags).trans
      (rename_three (T := payloadType (VectorTreeFieldEmbedding.storedSignature N E) ⇒ N ⇒ .prop) rho (fun p ns ts =>
        (IndexedVectorTreeStoredConstructorRecovery.positions (given.substitute (Subst.ofRename rho)) p ns zero one successor ts).activeProgram)
        source numbers tags))

set_option maxHeartbeats 1000000 in
theorem edge_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho ((IndexedVectorTreeStoredConstructorRecovery.positions given source numbers zero one successor tags).edgeProgram
      (IndexedVectorTreeStoredFamily.construct given)) =
      (IndexedVectorTreeStoredConstructorRecovery.positions (given.substitute (Subst.ofRename rho)) (HOL.rename rho source)
        (HOL.rename rho numbers) zero one successor (fun n => HOL.rename rho (tags n))).edgeProgram
      (IndexedVectorTreeStoredFamily.construct (given.substitute (Subst.ofRename rho))) := by
  exact (subst_ofRename rho _).symm.trans
    ((edge_subst (Subst.ofRename rho) given source numbers zero one successor tags).trans
      (rename_three (T := payloadType (VectorTreeFieldEmbedding.storedSignature N E) ⇒ N ⇒ E ⇒ .prop) rho (fun p ns ts =>
        (IndexedVectorTreeStoredConstructorRecovery.positions (given.substitute (Subst.ofRename rho)) p ns zero one successor ts).edgeProgram
          (IndexedVectorTreeStoredFamily.construct (given.substitute (Subst.ofRename rho))))
        source numbers tags))

#print axioms inventory_subst
#print axioms signature_subst
#print axioms family_subst
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyTransport
