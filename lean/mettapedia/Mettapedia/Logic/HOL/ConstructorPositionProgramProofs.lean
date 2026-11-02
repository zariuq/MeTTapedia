import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.ConstructorPositionReadback

/-!
# Substitution and retained computation for constructor-position queries

Child-index guards and edge queries retain their original formulas through
typed substitution and explicit computation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates CurriedGuardProgramProofs
open ConstructorPrograms (beneathTwo beneathThree)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)

theorem childGuard_subst (images : Subst Const Γ Ξ)
    (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index) :
    HOL.subst images (positions.childGuard payload slot index) =
      (positions.subst images).childGuard (HOL.subst images payload) (HOL.subst images slot) (HOL.subst images index) := by
  simp only [childGuard, ConstructorDataPredicates.guard_subst]
  apply congrArg (fun conditions => ConstructorDataPredicates.guard constructors.fields conditions (HOL.subst images payload))
  funext occurrence
  simp only [childCondition, conjoin_subst, HOL.subst, PositionPrograms.subst, ConstructorPrograms.subst]

private theorem subst_up {type bound : Ty Base} (term : Term Const Γ type) :
    HOL.subst (fun index => .var (.vs index)) term = HOL.weaken (σ := bound) term :=
  subst_ofRename Rename.weaken term

variable {space : Ty Base}
    (construct : Term Const Γ
      (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))

theorem edgeGuard_subst (images : Subst Const Γ Ξ)
    (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) :
    HOL.subst images (positions.edgeGuard construct payload slot child) =
      (positions.subst images).edgeGuard (HOL.subst images construct) (HOL.subst images payload)
        (HOL.subst images slot) (HOL.subst images child) := by
  cases constructors
  cases positions
  simp only [edgeGuard, HOL.subst, childGuard_subst, ConstructorPrograms.rootIndex_subst]
  simp only [PositionPrograms.subst, ConstructorPrograms.subst]
  simp only [subst_up, subst_weaken, Subst.lift]
  unfold ConstructorPrograms.rootIndex ConstructorPrograms.rootCondition ConstructorPrograms.rootBody
  unfold childGuard childCondition
  simp only [subst_up, subst_weaken]

private theorem cancel_two {first second type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (term : Term Const Γ type) :
    HOL.subst (Subst.single b) (HOL.subst (Subst.lift (Subst.single a))
      (HOL.subst beneathTwo term)) = term := by
  rw [HOL.subst_comp, HOL.subst_comp]
  exact ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem cancel_three {first second third type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (term : Term Const Γ type) :
    HOL.subst (Subst.single c) (HOL.subst (Subst.lift (Subst.single b))
      (HOL.subst (Subst.lift (Subst.lift (Subst.single a))) (HOL.subst beneathThree term))) = term := by
  rw [HOL.subst_comp, HOL.subst_comp, HOL.subst_comp]
  exact ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem cancel_weaken {first type : Ty Base} (a : Term Const Γ first) (term : Term Const Γ type) :
    HOL.subst (Subst.single a) (HOL.rename Rename.weaken term) = term :=
  PredicateFixedPoint.subst_single_weaken a term

variable {assumptions : List (Formula Const Γ)}

def edgeProgram_beta (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) :
    ProofSyntax Const assumptions
      (.eq (.app (.app (.app (positions.edgeProgram construct) payload) slot) child)
        (positions.edgeGuard construct payload slot child)) := by
  apply ProofSyntax.castIndices rfl ?_ (beta3
    ((positions.subst beneathThree).edgeGuard (HOL.subst beneathThree construct)
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)) payload slot child)
  apply congrArg₂ Term.eq
  · rfl
  · simp only [instantiate, edgeGuard_subst]
    simp only [PositionPrograms.subst, ConstructorPrograms.subst]
    simp only [HOL.subst, Subst.lift, Subst.single, cancel_three]
    simp [HOL.subst_rename, HOL.subst_comp, Subst.lift, Subst.single, HOL.rename, Rename.weaken]
    have payloadSame : HOL.subst (Subst.comp (Subst.single child) (fun index => .var (.vs index))) payload = payload :=
      ProofSyntax.term_subst_of_identity (fun _ => rfl) payload
    have slotSame : HOL.subst (fun index => .var index) slot = slot :=
      ProofSyntax.term_subst_of_identity (fun _ => rfl) slot
    rw [payloadSame, slotSame]
    unfold edgeGuard childGuard childCondition
    unfold ConstructorPrograms.rootIndex ConstructorPrograms.rootCondition ConstructorPrograms.rootBody
    simp only [PositionPrograms.subst, ConstructorPrograms.subst, HOL.subst_comp]
    rfl

theorem edgeProgram_beta_free (payload : Term Const Γ (payloadType constructors.fields))
    (slot : Term Const Γ constructors.number) (child : Term Const Γ space) :
    (positions.edgeProgram_beta construct (assumptions := assumptions) payload slot child).FunctionExtensionalityFree := by
  unfold edgeProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta3_free _ _ _ _

#print axioms childGuard_subst
#print axioms edgeGuard_subst
#print axioms edgeProgram_beta_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
