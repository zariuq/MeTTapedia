import Mettapedia.Logic.HOL.ConstructorActiveProgramProofs
import Mettapedia.Logic.HOL.IndexedConstructorInduction

/-!
# Substitution through constructor-position programs

The generated active and edge programs transport their original field
guards and relations through binder insertion. Their contextual recursive
signature therefore commutes with the same typed substitution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates
open ConstructorPrograms (beneathTwo beneathThree)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)

private theorem lift_two {first second type : Ty Base}
    (images : Subst Const Γ Ξ) (term : Term Const Γ type) :
    HOL.subst (Subst.lift (Subst.lift images))
      (HOL.subst (beneathTwo (first := first) (second := second)) term) =
      HOL.subst beneathTwo (HOL.subst images term) := by
  change HOL.subst (Subst.lift (Subst.lift images))
    (HOL.subst (Subst.ofRename (fun entry => .vs (.vs entry))) term) =
    HOL.subst (Subst.ofRename (fun entry => .vs (.vs entry))) (HOL.subst images term)
  rw [subst_ofRename, subst_ofRename]
  have expand {context : Ctx Base} (value : Term Const context type) :
      HOL.rename (fun entry => Var.vs (Var.vs entry)) value =
        weaken (σ := second) (weaken (σ := first) value) := by
    simp only [weaken, rename_comp]
    rfl
  rw [expand, expand, subst_weaken, subst_weaken]

private theorem lift_three {first second third type : Ty Base}
    (images : Subst Const Γ Ξ) (term : Term Const Γ type) :
    HOL.subst (Subst.lift (Subst.lift (Subst.lift images)))
      (HOL.subst (beneathThree (first := first) (second := second) (third := third)) term) =
      HOL.subst beneathThree (HOL.subst images term) := by
  change HOL.subst (Subst.lift (Subst.lift (Subst.lift images)))
    (HOL.subst (Subst.ofRename (fun entry => .vs (.vs (.vs entry)))) term) =
    HOL.subst (Subst.ofRename (fun entry => .vs (.vs (.vs entry)))) (HOL.subst images term)
  rw [subst_ofRename, subst_ofRename]
  have expand {context : Ctx Base} (value : Term Const context type) :
      HOL.rename (fun entry => Var.vs (Var.vs (Var.vs entry))) value =
        weaken (σ := third) (weaken (σ := second) (weaken (σ := first) value)) := by
    simp only [weaken, rename_comp]
    rfl
  rw [expand, expand, subst_weaken, subst_weaken, subst_weaken]

private theorem lift_three_comp {first second third : Ty Base}
    (images : Subst Const Γ Ξ) :
    @Subst.comp Base Const (third :: second :: first :: Γ) (third :: second :: first :: Ξ) Γ
        (Subst.lift (Subst.lift (Subst.lift images)))
        (beneathThree (first := first) (second := second) (third := third)) =
      @Subst.comp Base Const Ξ (third :: second :: first :: Ξ) Γ beneathThree images := by
  funext type entry
  change HOL.subst (Subst.lift (Subst.lift (Subst.lift images))) (.var (.vs (.vs (.vs entry)))) =
    HOL.subst beneathThree (images entry)
  have same := lift_three (first := first) (second := second) (third := third) images (.var entry)
  simpa only [beneathThree, HOL.subst] using same

theorem activeProgram_subst (images : Subst Const Γ Ξ) :
    HOL.subst images positions.activeProgram = (positions.subst images).activeProgram := by
  simp only [activeProgram, HOL.subst, activeGuard_subst, Subst.lift]
  apply congrArg Term.lam
  apply congrArg Term.lam
  unfold activeGuard
  apply congrArg₂ (ConstructorDataPredicates.guard constructors.fields)
  · funext occurrence
    simp only [activeCondition, PositionPrograms.subst, ConstructorPrograms.subst,
      lift_two]
  · rfl

variable {space : Ty Base}
    (bottom : Term Const Γ space)
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))

theorem edgeProgram_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (positions.edgeProgram construct) =
      (positions.subst images).edgeProgram (HOL.subst images construct) := by
  simp only [edgeProgram, HOL.subst, edgeGuard_subst]
  apply congrArg Term.lam
  apply congrArg Term.lam
  apply congrArg Term.lam
  unfold edgeGuard
  simp only [PositionPrograms.subst, ConstructorPrograms.subst, HOL.subst_comp, lift_three_comp]
  simp only [HOL.subst, Subst.lift, HOL.rename, Rename.weaken]
  congr 4 <;> simp only [lift_three]

theorem contextual_subst (images : Subst Const Γ Ξ) :
    (positions.contextual bottom construct).subst images =
      (positions.subst images).contextual (HOL.subst images bottom) (HOL.subst images construct) := by
  apply RecursiveSpacePredicate.Contextual.eq_of_fields
    (first := (positions.contextual bottom construct).subst images)
    (second := (positions.subst images).contextual (HOL.subst images bottom) (HOL.subst images construct)) rfl rfl rfl
  · rfl
  · rfl
  · exact heq_of_eq (constructors.shapeProgram_subst images)
  · exact heq_of_eq (positions.activeProgram_subst images)
  · exact heq_of_eq (positions.edgeProgram_subst construct images)

theorem strengthenedConditions_subst {index : Ty Base}
    (root property : Term Const Γ (space ⇒ index ⇒ .prop))
    (payload : Term Const Γ (payloadType constructors.fields))
    (children : Term Const Γ (constructors.number ⇒ space)) (images : Subst Const Γ Ξ) :
    HOL.subst images ((positions.contextual bottom construct).childConditions
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift root property)) payload children) =
      ((positions.subst images).contextual (HOL.subst images bottom) (HOL.subst images construct)).childConditions
        (PredicateFixedPoint.intersection
          ((positions.subst images).contextual (HOL.subst images bottom) (HOL.subst images construct)).least
          (IndexedPredicateInduction.lift (HOL.subst images root) (HOL.subst images property)))
        (HOL.subst images payload) (HOL.subst images children) := by
  rw [RecursiveSpacePredicate.Contextual.subst_childConditions]
  simp only [PredicateFixedPoint.subst_intersection, RecursiveSpacePredicate.Contextual.subst_least,
    IndexedPredicateInduction.subst_lift]
  unfold RecursiveSpacePredicate.Contextual.childConditions RecursiveSpacePredicate.Contextual.least
    RecursiveSpacePredicate.Contextual.operator RecursiveSpacePredicate.Contextual.code
  simp only [contextual, RecursiveSpacePredicate.Contextual.subst,
    ConstructorPrograms.shapeProgram_subst, activeProgram_subst, edgeProgram_subst]

#print axioms contextual_subst
#print axioms strengthenedConditions_subst

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
