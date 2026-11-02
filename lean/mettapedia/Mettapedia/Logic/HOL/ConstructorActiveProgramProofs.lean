import Mettapedia.Logic.HOL.ConstructorPositionProgramProofs
import Mettapedia.Logic.HOL.CurriedExistentialProofs

/-!
# Activity derived from an original constructor-row relation

A concrete row relation supplies its existential child-index witness.
The retained query computation then establishes activity at the encoded
payload, preserving the row guard and all supplied assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates CurriedGuardProgramProofs
open ConstructorPrograms (beneathTwo)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)

theorem activeGuard_subst (images : Subst Const Γ Ξ)
    (payload : Term Const Γ (payloadType constructors.fields)) (slot : Term Const Γ constructors.number) :
    HOL.subst images (positions.activeGuard payload slot) =
      (positions.subst images).activeGuard (HOL.subst images payload) (HOL.subst images slot) := by
  simp only [activeGuard, ConstructorDataPredicates.guard_subst]
  apply congrArg (fun conditions => ConstructorDataPredicates.guard constructors.fields conditions (HOL.subst images payload))
  funext occurrence
  simp only [activeCondition, conjoin_subst, existsValue_subst, HOL.subst,
    PositionPrograms.subst, ConstructorPrograms.subst]

private theorem cancel_two {first second type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (term : Term Const Γ type) :
    HOL.subst (Subst.single b) (HOL.subst (Subst.lift (Subst.single a))
      (HOL.subst beneathTwo term)) = term := by
  rw [HOL.subst_comp, HOL.subst_comp]
  exact ProofSyntax.term_subst_of_identity (fun _ => rfl) term

def activeProgram_beta {assumptions : List (Formula Const Γ)}
    (payload : Term Const Γ (payloadType constructors.fields)) (slot : Term Const Γ constructors.number) :
    ProofSyntax Const assumptions (.eq (.app (.app positions.activeProgram payload) slot)
      (positions.activeGuard payload slot)) := by
  apply ProofSyntax.castIndices rfl ?_
    (beta2 ((positions.subst beneathTwo).activeGuard (.var (.vs .vz)) (.var .vz)) payload slot)
  apply congrArg₂ Term.eq
  · rfl
  · simp only [instantiate, activeGuard_subst, PositionPrograms.subst, ConstructorPrograms.subst]
    simp only [HOL.subst, Subst.lift, Subst.single, cancel_two]
    have payloadSame : HOL.subst (Subst.single slot) (HOL.rename Rename.weaken payload) = payload :=
      PredicateFixedPoint.subst_single_weaken slot payload
    rw [payloadSame]
    unfold activeGuard activeCondition
    simp only [cancel_two]

theorem activeProgram_beta_free {assumptions : List (Formula Const Γ)}
    (payload : Term Const Γ (payloadType constructors.fields)) (slot : Term Const Γ constructors.number) :
    (positions.activeProgram_beta (assumptions := assumptions) payload slot).FunctionExtensionalityFree := by
  unfold activeProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta2_free _ _ _

def activeFromOriginal {assumptions : List (Formula Const Γ)} (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments)) :
    ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot) :=
  .impE (.eqPropER (positions.activeProgram_beta _ slot))
    (ConstructorDataPredicates.introduce constructors.fields (positions.activeCondition slot) occurrence arguments
      (conjoin_intro _ arguments allowed (existsValue_intro _ (.app (positions.graph occurrence) slot) arguments index related)))

theorem activeFromOriginal_free {assumptions : List (Formula Const Γ)} (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (index : Term Const Γ constructors.index)
    (allowed : ProofSyntax Const assumptions (applyArguments _ (constructors.allowed occurrence) arguments))
    (related : ProofSyntax Const assumptions
      (applyArguments _ (.app (.app (positions.graph occurrence) slot) index) arguments))
    (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    (positions.activeFromOriginal occurrence arguments slot index allowed related).FunctionExtensionalityFree :=
  ⟨positions.activeProgram_beta_free _ _, ConstructorDataPredicates.introduce_free _ _ _ _ _
    (conjoin_intro_free _ _ _ _ allowedFree (existsValue_intro_free _ _ _ _ related relatedFree))⟩

#print axioms activeGuard_subst
#print axioms activeProgram_beta_free
#print axioms activeFromOriginal_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
