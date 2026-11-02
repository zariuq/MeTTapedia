import Mettapedia.Logic.HOL.IndexedConstructorRootGuards
import Mettapedia.Logic.HOL.CurriedPredicateProofs
import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Retained introduction of generated constructor root indices

One occurrence supplies the original ordered data, field validity, computed
result index and complete child function. Existential witnesses retain that
same occurrence and data. Recursive child membership is a separate premise
of recursive-space introduction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (inventory : ConstructorPrograms Const Γ) {space : Ty Base}
  (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

def constructorValue (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) : Term Const Γ space :=
  .app (.app (.app construct (inventory.numeral occurrence.val))
    (encode inventory.fields occurrence arguments)) children

theorem rootBody_natural (value : Term Const Γ space) (index : Term Const Γ inventory.index)
    (occurrence : Fin inventory.fields.length) :
    NaturalBody (inventory.rootBody construct value index occurrence) := by
  intro Ξ Ω earlier later arguments
  simp only [rootBody, HOL.subst, applyArguments_subst, applyFields_subst,
    HOL.subst_comp, HOL.subst_weaken, encode_subst]
  rfl

variable {Δ : List (Formula Const Γ)}

def constructorEquation_intro (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) :
    ProofSyntax Const Δ (.ex (.eq
      (weaken (inventory.constructorValue construct occurrence arguments children))
      (.app (.app (.app (weaken construct) (weaken (inventory.numeral occurrence.val)))
        (weaken (encode inventory.fields occurrence arguments))) (.var .vz)))) := by
  apply ProofSyntax.exI children
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl (inventory.constructorValue construct occurrence arguments children))
  simp only [instantiate, HOL.subst, PredicateFixedPoint.subst_single_weaken, Subst.single, constructorValue]

def rootCondition_intro (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (fields : ProofSyntax Const Δ (applyArguments _ (inventory.allowed occurrence) arguments))
    (result : ProofSyntax Const Δ (.eq (applyFields _ (inventory.result occurrence) arguments) index)) :
    ProofSyntax Const Δ (applyArguments _
      (inventory.rootCondition construct (inventory.constructorValue construct occurrence arguments children) index occurrence)
      arguments) := by
  let value := inventory.constructorValue construct occurrence arguments children
  have beta := abstractArguments_beta (assumptions := Δ) (inventory.fields.get occurrence)
    (inventory.rootBody construct value index occurrence)
    (inventory.rootBody_natural construct value index occurrence) arguments
  apply ProofSyntax.impE (.eqPropER beta)
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.andI fields (ProofSyntax.andI result
      (inventory.constructorEquation_intro construct occurrence arguments children)))
  simp only [rootBody, value, identityTerm]

def rootIndex_intro (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (fields : ProofSyntax Const Δ (applyArguments _ (inventory.allowed occurrence) arguments))
    (result : ProofSyntax Const Δ (.eq (applyFields _ (inventory.result occurrence) arguments) index)) :
    ProofSyntax Const Δ (inventory.rootIndex construct
      (inventory.constructorValue construct occurrence arguments children) index) := by
  let value := inventory.constructorValue construct occurrence arguments children
  let formulas := List.ofFn (fun selected => existsArguments (inventory.fields.get selected)
    (inventory.rootCondition construct value index selected))
  have bound : occurrence.val < formulas.length := by
    simpa only [formulas, List.length_ofFn] using occurrence.isLt
  apply any_introAt formulas ⟨occurrence.val, bound⟩
  apply ProofSyntax.castIndices rfl ?_
    (existsArguments_intro _ (inventory.rootCondition construct value index occurrence) arguments
      (inventory.rootCondition_intro construct occurrence arguments children index fields result))
  simp only [formulas, List.get_eq_getElem, List.getElem_ofFn]

theorem constructorEquation_intro_free (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) :
    (inventory.constructorEquation_intro (Δ := Δ) construct occurrence arguments children).FunctionExtensionalityFree := by
  simp [constructorEquation_intro, ProofSyntax.FunctionExtensionalityFree]

theorem rootCondition_intro_free (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (fields : ProofSyntax Const Δ (applyArguments _ (inventory.allowed occurrence) arguments))
    (result : ProofSyntax Const Δ (.eq (applyFields _ (inventory.result occurrence) arguments) index))
    (fieldsFree : fields.FunctionExtensionalityFree) (resultFree : result.FunctionExtensionalityFree) :
    (inventory.rootCondition_intro construct occurrence arguments children index fields result).FunctionExtensionalityFree := by
  simp [rootCondition_intro, abstractArguments_beta_free, constructorEquation_intro_free,
    ProofSyntax.FunctionExtensionalityFree, fieldsFree, resultFree]

theorem rootIndex_intro_free (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (fields : ProofSyntax Const Δ (applyArguments _ (inventory.allowed occurrence) arguments))
    (result : ProofSyntax Const Δ (.eq (applyFields _ (inventory.result occurrence) arguments) index))
    (fieldsFree : fields.FunctionExtensionalityFree) (resultFree : result.FunctionExtensionalityFree) :
    (inventory.rootIndex_intro construct occurrence arguments children index fields result).FunctionExtensionalityFree := by
  unfold rootIndex_intro
  apply any_introAt_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply existsArguments_intro_free
  exact inventory.rootCondition_intro_free construct occurrence arguments children index fields result fieldsFree resultFree

#print axioms rootIndex_intro
#print axioms rootIndex_intro_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
