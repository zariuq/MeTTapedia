import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.FiniteConstructorCaseProofs
import Mettapedia.Logic.HOL.ConstructorInjectivity
import Mettapedia.Logic.HOL.FiniteConstructorProgramReadout

/-!
# Retained inversion of generated constructor indices

Constructor comparison uses the explicit primitive injectivity theorem.
Payload equality is read through the actual finite constructor encoding, so
both constructor occurrences and all original data fields remain available.
No datatype injectivity or result-index equality is admitted as a new rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (inventory : ConstructorPrograms Const Γ) {space : Ty Base}
  (construct : Term Const Γ
    (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
  {assumptions : List (Formula Const Γ)}

@[simp] theorem constructorValue_subst {Ξ : Ctx Base} (images : Subst Const Γ Ξ)
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) :
    HOL.subst images (inventory.constructorValue construct occurrence arguments children) =
      (inventory.subst images).constructorValue (HOL.subst images construct) occurrence
        (substituteArguments images _ arguments) (HOL.subst images children) := by
  simp only [constructorValue, HOL.subst, encode_subst, ConstructorPrograms.subst]

def rootCondition_parts (value : Term Const Γ space) (index : Term Const Γ inventory.index)
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (present : ProofSyntax Const assumptions
      (applyArguments _ (inventory.rootCondition construct value index occurrence) arguments)) :
    ProofSyntax Const assumptions
      (.and (applyArguments _ (inventory.allowed occurrence) arguments)
        (.and (.eq (applyFields _ (inventory.result occurrence) arguments) index)
          (.ex (σ := inventory.number ⇒ space) (.eq (weaken value)
            (.app (.app (.app (weaken construct) (weaken (inventory.numeral occurrence.val)))
              (weaken (encode inventory.fields occurrence arguments))) (.var .vz)))))) := by
  have beta := abstractArguments_beta (assumptions := assumptions) (inventory.fields.get occurrence)
    (inventory.rootBody construct value index occurrence)
    (inventory.rootBody_natural construct value index occurrence) arguments
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.impE (ProofSyntax.eqPropEL beta) present)
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [rootBody, identityTerm]

theorem rootCondition_parts_free (value : Term Const Γ space) (index : Term Const Γ inventory.index)
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (present : ProofSyntax Const assumptions
      (applyArguments _ (inventory.rootCondition construct value index occurrence) arguments))
    (presentFree : present.FunctionExtensionalityFree) :
    (inventory.rootCondition_parts construct value index occurrence arguments present).FunctionExtensionalityFree := by
  unfold rootCondition_parts
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨abstractArguments_beta_free _ _ _ _, presentFree⟩

def results_of_constructor_eq (first second : Fin inventory.fields.length)
    (firstArguments : Arguments Const Γ (inventory.fields.get first))
    (secondArguments : Arguments Const Γ (inventory.fields.get second))
    (firstChildren secondChildren : Term Const Γ (inventory.number ⇒ space))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (same : ProofSyntax Const assumptions (.eq
      (inventory.constructorValue construct first firstArguments firstChildren)
      (inventory.constructorValue construct second secondArguments secondChildren))) :
    ProofSyntax Const assumptions (.eq
      (applyFields _ (inventory.result first) firstArguments)
      (applyFields _ (inventory.result second) secondArguments)) := by
  have compared := ConstructorInjectivity.compare construct
    (inventory.numeral first.val) (inventory.numeral second.val)
    (encode inventory.fields first firstArguments) (encode inventory.fields second secondArguments)
    firstChildren secondChildren
    (ConstructorInjectivity.specialize construct (inventory.numeral first.val)
      (encode inventory.fields first firstArguments) firstChildren injectivity)
  have payloads := ProofSyntax.andEL (ProofSyntax.andER
    (ProofSyntax.impE (ProofSyntax.eqPropEL compared) same))
  exact program_equal_of_payload inventory.fields inventory.result first second
    firstArguments secondArguments payloads

theorem results_of_constructor_eq_free (first second : Fin inventory.fields.length)
    (firstArguments : Arguments Const Γ (inventory.fields.get first))
    (secondArguments : Arguments Const Γ (inventory.fields.get second))
    (firstChildren secondChildren : Term Const Γ (inventory.number ⇒ space))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (same : ProofSyntax Const assumptions (.eq
      (inventory.constructorValue construct first firstArguments firstChildren)
      (inventory.constructorValue construct second secondArguments secondChildren)))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (sameFree : same.FunctionExtensionalityFree) :
    (inventory.results_of_constructor_eq construct first second firstArguments secondArguments
      firstChildren secondChildren injectivity same).FunctionExtensionalityFree := by
  unfold results_of_constructor_eq
  apply program_equal_of_payload_free
  simp only [ConstructorInjectivity.compare, ConstructorInjectivity.specialize,
    ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree,
    injectivityFree, sameFree, and_self]

def rootCondition_result (first second : Fin inventory.fields.length)
    (firstArguments : Arguments Const Γ (inventory.fields.get first))
    (secondArguments : Arguments Const Γ (inventory.fields.get second))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (present : ProofSyntax Const assumptions (applyArguments _
      (inventory.rootCondition construct
        (inventory.constructorValue construct first firstArguments children) index second) secondArguments)) :
    ProofSyntax Const assumptions (.eq (applyFields _ (inventory.result first) firstArguments) index) := by
  let value := inventory.constructorValue construct first firstArguments children
  have parts := inventory.rootCondition_parts construct value index second secondArguments present
  have resultIndex := ProofSyntax.andEL (ProofSyntax.andER parts)
  let lift : Subst Const Γ ((inventory.number ⇒ space) :: Γ) := Subst.ofRename Rename.weaken
  let shifted := inventory.subst lift
  let constructor := HOL.subst lift construct
  let firstData := substituteArguments lift _ firstArguments
  let secondData := substituteArguments lift _ secondArguments
  let originalChildren := HOL.subst lift children
  let equation : Formula Const ((inventory.number ⇒ space) :: Γ) :=
    .eq (weaken value)
      (.app (.app (.app (weaken construct) (weaken (inventory.numeral second.val)))
        (weaken (encode inventory.fields second secondArguments))) (.var .vz))
  let branchHypotheses := equation :: weakenHyps (σ := inventory.number ⇒ space) assumptions
  apply ProofSyntax.exE (ProofSyntax.andER (ProofSyntax.andER parts))
  have liftedInjectivity : ProofSyntax Const branchHypotheses (ConstructorInjectivity.statement constructor) := by
    apply ProofSyntax.castIndices rfl ?_ ((PredicateFixedPoint.weakenProof injectivity).prepend equation)
    simp only [constructor, lift, subst_ofRename, weaken, ConstructorInjectivity.rename_statement]
  have same : ProofSyntax Const branchHypotheses (.eq
      (shifted.constructorValue constructor first firstData originalChildren)
      (shifted.constructorValue constructor second secondData (.var .vz))) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Const) (Δ := branchHypotheses) 0)
    simp only [branchHypotheses, List.get_cons_zero, equation, value,
      shifted, constructor, firstData, secondData, originalChildren,
      constructorValue, ConstructorPrograms.subst, lift,
      ← encode_subst, subst_ofRename, weaken, HOL.rename]
  have computed := shifted.results_of_constructor_eq constructor first second firstData secondData
    originalChildren (.var .vz) liftedInjectivity same
  have computedIndex : ProofSyntax Const branchHypotheses (.eq
      (weaken (applyFields _ (inventory.result first) firstArguments))
      (weaken (applyFields _ (inventory.result second) secondArguments))) := by
    apply ProofSyntax.castIndices rfl ?_ computed
    simpa only [shifted, ConstructorPrograms.subst, firstData, secondData, lift, subst_ofRename, weaken]
      using congrArg₂ Term.eq
      (applyFields_subst lift _ (inventory.result first) firstArguments).symm
      (applyFields_subst lift _ (inventory.result second) secondArguments).symm
  exact ProofSyntax.eqTrans computedIndex ((PredicateFixedPoint.weakenProof resultIndex).prepend equation)

theorem rootCondition_result_free (first second : Fin inventory.fields.length)
    (firstArguments : Arguments Const Γ (inventory.fields.get first))
    (secondArguments : Arguments Const Γ (inventory.fields.get second))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (present : ProofSyntax Const assumptions (applyArguments _
      (inventory.rootCondition construct
        (inventory.constructorValue construct first firstArguments children) index second) secondArguments))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (presentFree : present.FunctionExtensionalityFree) :
    (inventory.rootCondition_result construct first second firstArguments secondArguments children index
      injectivity present).FunctionExtensionalityFree := by
  unfold rootCondition_result
  refine ⟨?_, ?_, ?_⟩
  · exact inventory.rootCondition_parts_free construct _ index second secondArguments present presentFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply results_of_constructor_eq_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
        PredicateFixedPoint.weakenProof, ProofSyntax.functionExtensionalityFree_castIndices,
        ProofSyntax.functionExtensionalityFree_rename] using injectivityFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      PredicateFixedPoint.weakenProof, ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.functionExtensionalityFree_rename,
      ProofSyntax.FunctionExtensionalityFree] using
      inventory.rootCondition_parts_free construct _ index second secondArguments present presentFree

def rootCondition_case (first second : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get first))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct)) :
    FieldCase assumptions (inventory.fields.get second)
      (inventory.rootCondition construct
        (inventory.constructorValue construct first arguments children) index second)
      (.eq (applyFields _ (inventory.result first) arguments) index) := by
  intro Ξ images otherArguments
  let shifted := inventory.subst images
  let constructor := HOL.subst images construct
  let sourceData := substituteArguments images _ arguments
  let originalChildren := HOL.subst images children
  let resultIndex := HOL.subst images index
  let condition := applyArguments _ (HOL.subst images
    (inventory.rootCondition construct
      (inventory.constructorValue construct first arguments children) index second)) otherArguments
  let localHypotheses := condition :: assumptions.map (HOL.subst images)
  have liftedInjectivity : ProofSyntax Const localHypotheses
      (ConstructorInjectivity.statement constructor) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.subst images injectivity).prepend condition)
    exact ConstructorInjectivity.subst_statement images construct
  have present : ProofSyntax Const localHypotheses (applyArguments _
      (shifted.rootCondition constructor
        (shifted.constructorValue constructor first sourceData originalChildren) resultIndex second)
      otherArguments) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Const) (Δ := localHypotheses) 0)
    simp only [localHypotheses, List.get_cons_zero, condition,
      inventory.rootCondition_subst construct images, constructorValue_subst,
      shifted, constructor, sourceData, originalChildren, resultIndex, ConstructorPrograms.subst]
  apply ProofSyntax.castIndices rfl ?_
    (shifted.rootCondition_result constructor first second sourceData otherArguments originalChildren resultIndex
      liftedInjectivity present)
  simp only [shifted, ConstructorPrograms.subst, sourceData, resultIndex, HOL.subst, applyFields_subst]

def rootIndex_result (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (present : ProofSyntax Const assumptions
      (inventory.rootIndex construct (inventory.constructorValue construct occurrence arguments children) index)) :
    ProofSyntax Const assumptions (.eq (applyFields _ (inventory.result occurrence) arguments) index) := by
  let value := inventory.constructorValue construct occurrence arguments children
  let formulas := List.ofFn (fun selected => existsArguments (inventory.fields.get selected)
    (inventory.rootCondition construct value index selected))
  apply any_elim formulas _ present
  intro selected
  let other : Fin inventory.fields.length :=
    ⟨selected.val, by simpa only [formulas, List.length_ofFn] using selected.isLt⟩
  let condition := existsArguments (inventory.fields.get other)
    (inventory.rootCondition construct value index other)
  apply ProofSyntax.impI
  apply ProofSyntax.castIndices ?_ rfl
    (FieldCase.eliminate _ _ _
      (inventory.rootCondition_case construct occurrence other arguments children index
        (injectivity.prepend condition)) (ProofSyntax.hyp 0))
  simp only [formulas, condition, other, List.get_eq_getElem, List.getElem_ofFn]

theorem rootCondition_case_free (first second : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get first))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (free : injectivity.FunctionExtensionalityFree) :
    ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ)
      (otherArguments : Arguments Const Ξ (inventory.fields.get second)),
      (inventory.rootCondition_case construct first second arguments children index injectivity images otherArguments).FunctionExtensionalityFree := by
  intro Ξ images otherArguments
  unfold rootCondition_case
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply rootCondition_result_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_subst] using free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

theorem rootIndex_result_free (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (present : ProofSyntax Const assumptions
      (inventory.rootIndex construct (inventory.constructorValue construct occurrence arguments children) index))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (presentFree : present.FunctionExtensionalityFree) :
    (inventory.rootIndex_result construct occurrence arguments children index injectivity present).FunctionExtensionalityFree := by
  unfold rootIndex_result
  apply any_elim_free
  · exact presentFree
  · intro selected
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply FieldCase.eliminate_free
    · apply rootCondition_case_free
      simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using injectivityFree
    · trivial

def rootIndex_motive (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (property : Term Const Γ (inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (root : ProofSyntax Const assumptions
      (inventory.rootIndex construct (inventory.constructorValue construct occurrence arguments children) index))
    (caseProof : ProofSyntax Const assumptions
      (.app property (applyFields _ (inventory.result occurrence) arguments))) :
    ProofSyntax Const assumptions (.app property index) :=
  .impE (.eqPropEL (.eqAppArg property
    (inventory.rootIndex_result construct occurrence arguments children index injectivity root))) caseProof

theorem rootIndex_motive_free (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space)) (index : Term Const Γ inventory.index)
    (property : Term Const Γ (inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (root : ProofSyntax Const assumptions
      (inventory.rootIndex construct (inventory.constructorValue construct occurrence arguments children) index))
    (caseProof : ProofSyntax Const assumptions
      (.app property (applyFields _ (inventory.result occurrence) arguments)))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (rootFree : root.FunctionExtensionalityFree)
    (caseFree : caseProof.FunctionExtensionalityFree) :
    (inventory.rootIndex_motive construct occurrence arguments children index property injectivity root caseProof).FunctionExtensionalityFree :=
  ⟨inventory.rootIndex_result_free construct occurrence arguments children index injectivity root
    injectivityFree rootFree, caseFree⟩

#print axioms results_of_constructor_eq
#print axioms results_of_constructor_eq_free
#print axioms constructorValue_subst
#print axioms rootCondition_parts
#print axioms rootCondition_parts_free
#print axioms rootCondition_result
#print axioms rootCondition_result_free
#print axioms rootCondition_case
#print axioms rootIndex_result
#print axioms rootCondition_case_free
#print axioms rootIndex_result_free
#print axioms rootIndex_motive
#print axioms rootIndex_motive_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
