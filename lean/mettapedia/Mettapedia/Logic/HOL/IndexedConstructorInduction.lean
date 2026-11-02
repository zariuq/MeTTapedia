import Mettapedia.Logic.HOL.IndexedConstructorRootInversion
import Mettapedia.Logic.HOL.IndexedPredicateInduction
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs

/-!
# Retained constructor cases for indexed induction

Generated shape guards expose an original constructor occurrence, its ordered
fields, its tag and its exact encoded payload. Case elimination keeps these
equations in the surrounding context. A constructor result at its computed
index extends to every permitted root index using explicit injectivity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  (inventory : ConstructorPrograms Const Γ) {assumptions : List (Formula Const Γ)}

theorem subst_comp {Ω : Ctx Base} (first : Subst Const Γ Ξ) (second : Subst Const Ξ Ω) :
    (inventory.subst first).subst second = inventory.subst (Subst.comp second first) := by
  cases inventory
  simp only [ConstructorPrograms.subst, HOL.subst_comp]

private theorem subst_beneathTwo {first second type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (beneathTwo : Subst Const Γ (second :: first :: Γ)) term = weaken (weaken term) := by
  change HOL.subst (Subst.ofRename (fun index => .vs (.vs index))) term = _
  simp only [subst_ofRename, weaken, rename_comp]
  rfl

private theorem lift_beneathTwo {first second : Ty Base} (images : Subst Const Γ Ξ) :
    @Subst.comp Base Const (second :: first :: Γ) (second :: first :: Ξ) Γ
        (Subst.lift (Subst.lift images)) beneathTwo =
      @Subst.comp Base Const Ξ (second :: first :: Ξ) Γ beneathTwo images := by
  funext type index
  simp only [Subst.comp, beneathTwo, HOL.subst, Subst.lift, subst_beneathTwo, weaken]

private theorem subst_lift_beneathTwo {first second type : Ty Base}
    (images : Subst Const Γ Ξ) (term : Term Const Γ type) :
    HOL.subst (Subst.lift (Subst.lift images))
        (HOL.subst (beneathTwo (first := first) (second := second)) term) =
      HOL.subst beneathTwo (HOL.subst images term) := by
  rw [HOL.subst_comp, HOL.subst_comp, lift_beneathTwo]

private theorem inventory_lift_beneathTwo {first second : Ty Base} (images : Subst Const Γ Ξ) :
    (inventory.subst (beneathTwo (first := first) (second := second))).subst
        (Subst.lift (Subst.lift images)) =
      (inventory.subst images).subst beneathTwo := by
  rw [inventory.subst_comp, inventory.subst_comp]
  exact congrArg (fun mapping : Subst Const Γ (second :: first :: Ξ) => inventory.subst mapping)
    (lift_beneathTwo images)

@[simp] theorem shapeProgram_subst (images : Subst Const Γ Ξ) :
    HOL.subst images inventory.shapeProgram = (inventory.subst images).shapeProgram := by
  simp only [shapeProgram, HOL.subst, shapeGuard_subst]
  unfold shapeGuard shapeCondition
  dsimp only [ConstructorPrograms.subst]
  simp only [subst_lift_beneathTwo, Subst.lift, HOL.rename, Rename.weaken]

@[simp] theorem rootProgram_subst {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (images : Subst Const Γ Ξ) :
    HOL.subst images (inventory.rootProgram construct) =
      (inventory.subst images).rootProgram (HOL.subst images construct) := by
  simp only [rootProgram, HOL.subst, rootIndex_subst]
  unfold rootIndex rootCondition rootBody
  dsimp only [ConstructorPrograms.subst]
  simp only [subst_lift_beneathTwo, Subst.lift, HOL.rename, Rename.weaken]

def shapeCasePredicate (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields))
    (occurrence : Fin inventory.fields.length) :
    Term Const Γ (handlerType (inventory.fields.get occurrence)) :=
  restrictedPredicate inventory.fields occurrence (inventory.shapeCondition tag occurrence) payload

theorem shapeCasePredicate_subst (images : Subst Const Γ Ξ)
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (occurrence : Fin inventory.fields.length) :
    HOL.subst images (inventory.shapeCasePredicate tag payload occurrence) =
      (inventory.subst images).shapeCasePredicate (HOL.subst images tag)
        (HOL.subst images payload) occurrence := by
  simp only [shapeCasePredicate, restrictedPredicate_subst]
  congr 1
  simp only [shapeCondition, conjoin_subst, constant_subst, HOL.subst, ConstructorPrograms.subst]

def shapeCase_parts (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields))
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (present : ProofSyntax Const assumptions
      (applyArguments _ (inventory.shapeCasePredicate tag payload occurrence) arguments)) :
    ProofSyntax Const assumptions (.and
      (applyArguments _ (inventory.allowed occurrence) arguments)
      (.and (.eq tag (inventory.numeral occurrence.val))
        (.eq payload (encode inventory.fields occurrence arguments)))) := by
  have parts := ProofSyntax.impE (ProofSyntax.eqPropEL
    (restrictedPredicate_beta inventory.fields occurrence (inventory.shapeCondition tag occurrence) payload arguments)) present
  have conditions := ProofSyntax.impE (ProofSyntax.eqPropEL
    (conjoin_beta _ (inventory.allowed occurrence)
      (constant _ (.eq tag (inventory.numeral occurrence.val))) arguments)) (ProofSyntax.andEL parts)
  exact .andI (.andEL conditions)
    (.andI (.impE (.eqPropEL (constant_beta _ (.eq tag (inventory.numeral occurrence.val)) arguments))
      (.andER conditions)) (.andER parts))

theorem shapeCase_parts_free (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields))
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (present : ProofSyntax Const assumptions
      (applyArguments _ (inventory.shapeCasePredicate tag payload occurrence) arguments))
    (free : present.FunctionExtensionalityFree) :
    (inventory.shapeCase_parts tag payload occurrence arguments present).FunctionExtensionalityFree := by
  unfold shapeCase_parts
  simp only [ProofSyntax.FunctionExtensionalityFree, restrictedPredicate_beta_free,
    conjoin_beta_free, constant_beta_free, free, and_self]

def shapeProgram_elim (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) (target : Formula Const Γ)
    (cases : (occurrence : Fin inventory.fields.length) →
      FieldCase assumptions (inventory.fields.get occurrence)
        (inventory.shapeCasePredicate tag payload occurrence) target)
    (present : ProofSyntax Const assumptions (.app (.app inventory.shapeProgram tag) payload)) :
    ProofSyntax Const assumptions target := by
  let formulas := List.ofFn (fun occurrence => existsArguments (inventory.fields.get occurrence)
    (inventory.shapeCasePredicate tag payload occurrence))
  apply any_elim formulas target
    (ProofSyntax.impE (ProofSyntax.eqPropEL (inventory.shapeProgram_beta tag payload)) present)
  intro selected
  let occurrence : Fin inventory.fields.length :=
    ⟨selected.val, by simpa only [formulas, List.length_ofFn] using selected.isLt⟩
  let condition := existsArguments (inventory.fields.get occurrence)
    (inventory.shapeCasePredicate tag payload occurrence)
  apply ProofSyntax.impI
  apply ProofSyntax.castIndices ?_ rfl
    (existsArguments_elim (inventory.fields.get occurrence)
      (inventory.shapeCasePredicate tag payload occurrence) target (ProofSyntax.hyp 0)
      ((FieldCase.introduce _ _ _ (cases occurrence)).prepend condition))
  simp only [formulas, condition, occurrence, List.get_eq_getElem, List.getElem_ofFn]

theorem shapeProgram_elim_free (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) (target : Formula Const Γ)
    (cases : (occurrence : Fin inventory.fields.length) →
      FieldCase assumptions (inventory.fields.get occurrence)
        (inventory.shapeCasePredicate tag payload occurrence) target)
    (present : ProofSyntax Const assumptions (.app (.app inventory.shapeProgram tag) payload))
    (casesFree : ∀ occurrence {Ξ : Ctx Base} (images : Subst Const Γ Ξ)
      (arguments : Arguments Const Ξ (inventory.fields.get occurrence)),
      (cases occurrence images arguments).FunctionExtensionalityFree)
    (presentFree : present.FunctionExtensionalityFree) :
    (inventory.shapeProgram_elim tag payload target cases present).FunctionExtensionalityFree := by
  unfold shapeProgram_elim
  apply any_elim_free
  · exact ⟨inventory.shapeProgram_beta_free _ _, presentFree⟩
  · intro selected
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply existsArguments_elim_free
    · trivial
    · apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact FieldCase.introduce_free _ _ _ _ (casesFree _)

def constructorLift {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (caseProof : ProofSyntax Const assumptions (.app
      (.app property (inventory.constructorValue construct occurrence arguments children))
      (applyFields _ (inventory.result occurrence) arguments))) :
    ProofSyntax Const assumptions (.app
      (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)
      (inventory.constructorValue construct occurrence arguments children)) := by
  let value := inventory.constructorValue construct occurrence arguments children
  apply ProofSyntax.impE (ProofSyntax.eqPropER
    (IndexedPredicateInduction.lift_beta (inventory.rootProgram construct) property value))
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let images : Subst Const Γ (inventory.index :: Γ) := Subst.ofRename Rename.weaken
  let shifted := inventory.subst images
  let constructor := HOL.subst images construct
  let data := substituteArguments images _ arguments
  let descendants := HOL.subst images children
  let condition : Formula Const (inventory.index :: Γ) :=
    .app (.app (weaken (inventory.rootProgram construct)) (weaken value)) (.var .vz)
  let localHypotheses := condition :: weakenHyps (σ := inventory.index) assumptions
  have shiftedValue : shifted.constructorValue constructor occurrence data descendants = weaken value := by
    simpa only [shifted, constructor, data, descendants, images, subst_ofRename, weaken, value,
      ConstructorPrograms.subst] using
      (inventory.constructorValue_subst construct images occurrence arguments children).symm
  have shiftedRoot : shifted.rootProgram constructor = weaken (inventory.rootProgram construct) := by
    simpa only [shifted, constructor, images, subst_ofRename, weaken] using
      (inventory.rootProgram_subst construct images).symm
  have shiftedResult : applyFields _ (shifted.result occurrence) data =
      weaken (applyFields _ (inventory.result occurrence) arguments) := by
    simpa only [shifted, data, ConstructorPrograms.subst, images, subst_ofRename, weaken] using
      (applyFields_subst images _ (inventory.result occurrence) arguments).symm
  have liftedInjectivity : ProofSyntax Const localHypotheses (ConstructorInjectivity.statement constructor) := by
    apply ProofSyntax.castIndices rfl ?_ ((PredicateFixedPoint.weakenProof injectivity).prepend condition)
    simp only [constructor, images, subst_ofRename, weaken, ConstructorInjectivity.rename_statement]
  have root : ProofSyntax Const localHypotheses
      (shifted.rootIndex constructor (shifted.constructorValue constructor occurrence data descendants) (.var .vz)) := by
    apply ProofSyntax.impE (ProofSyntax.eqPropEL
      (shifted.rootProgram_beta constructor _ (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Const) (Δ := localHypotheses) 0)
    simp only [localHypotheses, List.get_cons_zero, condition, shiftedValue, shiftedRoot]
  have sourceCase : ProofSyntax Const localHypotheses (.app
      (.app (weaken property) (weaken value))
      (applyFields _ (shifted.result occurrence) data)) := by
    apply ProofSyntax.castIndices rfl ?_ ((PredicateFixedPoint.weakenProof caseProof).prepend condition)
    exact congrArg (fun index => Term.app (.app (weaken property) (weaken value)) index) shiftedResult.symm
  exact shifted.rootIndex_motive constructor occurrence data descendants (.var .vz)
    (.app (weaken property) (weaken value)) liftedInjectivity root sourceCase

theorem constructorLift_free {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Γ (inventory.fields.get occurrence))
    (children : Term Const Γ (inventory.number ⇒ space))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (caseProof : ProofSyntax Const assumptions (.app
      (.app property (inventory.constructorValue construct occurrence arguments children))
      (applyFields _ (inventory.result occurrence) arguments)))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (caseFree : caseProof.FunctionExtensionalityFree) :
    (inventory.constructorLift construct occurrence arguments children property injectivity caseProof).FunctionExtensionalityFree := by
  unfold constructorLift
  refine ⟨IndexedPredicateInduction.lift_beta_free _ _ _, ?_⟩
  apply rootIndex_motive_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    simpa only [PredicateFixedPoint.weakenProof, ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono, ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.functionExtensionalityFree_rename] using injectivityFree
  · exact ⟨rootProgram_beta_free _ _ _ _,
      (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    simpa only [PredicateFixedPoint.weakenProof, ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono, ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.functionExtensionalityFree_rename] using caseFree

/-- Each case uses the original fields and the complete supplied child condition. -/
def IndexedCases {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (children : Term Const Γ (inventory.number ⇒ space))
    (childCondition : Term Const Γ (payloadType inventory.fields ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (assumptions : List (Formula Const Γ)) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) (occurrence : Fin inventory.fields.length)
    (arguments : Arguments Const Ξ (inventory.fields.get occurrence)),
    ProofSyntax Const
      (applyArguments _ ((inventory.subst images).allowed occurrence) arguments ::
        .app (HOL.subst images childCondition) (encode inventory.fields occurrence arguments) ::
        assumptions.map (HOL.subst images))
      (.app (.app (HOL.subst images property)
        ((inventory.subst images).constructorValue (HOL.subst images construct) occurrence arguments
          (HOL.subst images children)))
        (applyFields _ ((inventory.subst images).result occurrence) arguments))

def indexedShapeCase {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (children : Term Const Γ (inventory.number ⇒ space))
    (childCondition : Term Const Γ (payloadType inventory.fields ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (cases : inventory.IndexedCases construct children childCondition property assumptions)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (childProof : ProofSyntax Const assumptions (.app childCondition payload))
    (occurrence : Fin inventory.fields.length) :
    FieldCase assumptions (inventory.fields.get occurrence)
      (inventory.shapeCasePredicate tag payload occurrence)
      (.app (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)
        (.app (.app (.app construct tag) payload) children)) := by
  intro Ξ images arguments
  let shifted := inventory.subst images
  let constructor := HOL.subst images construct
  let descendants := HOL.subst images children
  let condition := applyArguments _ (HOL.subst images
    (inventory.shapeCasePredicate tag payload occurrence)) arguments
  let localHypotheses := condition :: assumptions.map (HOL.subst images)
  have present : ProofSyntax Const localHypotheses (applyArguments _
      (shifted.shapeCasePredicate (HOL.subst images tag) (HOL.subst images payload) occurrence) arguments) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Const) (Δ := localHypotheses) 0)
    simp only [localHypotheses, List.get_cons_zero, condition, shapeCasePredicate_subst, shifted,
      ConstructorPrograms.subst]
  have parts := shifted.shapeCase_parts (HOL.subst images tag) (HOL.subst images payload)
    occurrence arguments present
  have childEncoded : ProofSyntax Const localHypotheses
      (.app (HOL.subst images childCondition) (encode inventory.fields occurrence arguments)) :=
    .impE (.eqPropEL (.eqAppArg (HOL.subst images childCondition) (.andER (.andER parts))))
      ((ProofSyntax.subst images childProof).prepend condition)
  let supplied : ProofSyntax.HypothesisSubstitution
      (applyArguments _ (shifted.allowed occurrence) arguments ::
        .app (HOL.subst images childCondition) (encode inventory.fields occurrence arguments) ::
        assumptions.map (HOL.subst images)) localHypotheses :=
    Fin.cases (ProofSyntax.andEL parts)
      (Fin.cases childEncoded (fun prior => ProofSyntax.hyp (Δ := localHypotheses) prior.succ))
  have sourceCase : ProofSyntax Const localHypotheses (.app
      (.app (HOL.subst images property) (shifted.constructorValue constructor occurrence arguments descendants))
      (applyFields _ (shifted.result occurrence) arguments)) :=
    ProofSyntax.substituteHypotheses supplied (cases images occurrence arguments)
  have liftedInjectivity : ProofSyntax Const localHypotheses (ConstructorInjectivity.statement constructor) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.subst images injectivity).prepend condition)
    exact ConstructorInjectivity.subst_statement images construct
  have valueEqual : ProofSyntax Const localHypotheses (.eq
      (.app (.app (.app constructor (HOL.subst images tag)) (HOL.subst images payload)) descendants)
      (shifted.constructorValue constructor occurrence arguments descendants)) :=
    .eqApp descendants (.eqTrans
      (.eqApp (HOL.subst images payload) (.eqAppArg constructor (.andEL (.andER parts))))
      (.eqAppArg (.app constructor (shifted.numeral occurrence.val)) (.andER (.andER parts))))
  have lifted := shifted.constructorLift constructor occurrence arguments descendants
    (HOL.subst images property) liftedInjectivity sourceCase
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.impE (ProofSyntax.eqPropER (ProofSyntax.eqAppArg
      (IndexedPredicateInduction.lift (shifted.rootProgram constructor) (HOL.subst images property)) valueEqual)) lifted)
  simp only [HOL.subst, IndexedPredicateInduction.subst_lift, rootProgram_subst,
    shifted, constructor, descendants]

theorem indexedShapeCase_free {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (children : Term Const Γ (inventory.number ⇒ space))
    (childCondition : Term Const Γ (payloadType inventory.fields ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (cases : inventory.IndexedCases construct children childCondition property assumptions)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (childProof : ProofSyntax Const assumptions (.app childCondition payload))
    (occurrence : Fin inventory.fields.length)
    (casesFree : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) occurrence arguments,
      (cases images occurrence arguments).FunctionExtensionalityFree)
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (childrenFree : childProof.FunctionExtensionalityFree) :
    ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ)
      (arguments : Arguments Const Ξ (inventory.fields.get occurrence)),
      (inventory.indexedShapeCase construct tag payload children childCondition property cases injectivity
        childProof occurrence images arguments).FunctionExtensionalityFree := by
  intro Ξ images arguments
  unfold indexedShapeCase
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;>
      (apply shapeCase_parts_free; apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr; trivial)
  · apply constructorLift_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
        ProofSyntax.functionExtensionalityFree_subst] using injectivityFree
    · apply ProofSyntax.substituteHypotheses_free
      · exact casesFree images occurrence arguments
      · intro position
        refine Fin.cases ?_ (fun remaining => Fin.cases ?_ (fun _ => ?_) remaining) position
        · apply shapeCase_parts_free
          apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          trivial
        · refine ⟨?_, ?_⟩
          · apply shapeCase_parts_free
            apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
            trivial
          · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
              ProofSyntax.functionExtensionalityFree_subst] using childrenFree
        · trivial

def constructorCases_lift {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (children : Term Const Γ (inventory.number ⇒ space))
    (childCondition : Term Const Γ (payloadType inventory.fields ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (cases : inventory.IndexedCases construct children childCondition property assumptions)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (shape : ProofSyntax Const assumptions (.app (.app inventory.shapeProgram tag) payload))
    (childProof : ProofSyntax Const assumptions (.app childCondition payload)) :
    ProofSyntax Const assumptions
      (.app (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)
        (.app (.app (.app construct tag) payload) children)) :=
  inventory.shapeProgram_elim tag payload _
    (inventory.indexedShapeCase construct tag payload children childCondition property cases injectivity childProof) shape

theorem constructorCases_lift_free {space : Ty Base}
    (construct : Term Const Γ
      (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
    (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields))
    (children : Term Const Γ (inventory.number ⇒ space))
    (childCondition : Term Const Γ (payloadType inventory.fields ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (cases : inventory.IndexedCases construct children childCondition property assumptions)
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (shape : ProofSyntax Const assumptions (.app (.app inventory.shapeProgram tag) payload))
    (childProof : ProofSyntax Const assumptions (.app childCondition payload))
    (casesFree : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) occurrence arguments,
      (cases images occurrence arguments).FunctionExtensionalityFree)
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (shapeFree : shape.FunctionExtensionalityFree) (childrenFree : childProof.FunctionExtensionalityFree) :
    (inventory.constructorCases_lift construct tag payload children childCondition property cases injectivity shape childProof).FunctionExtensionalityFree :=
  inventory.shapeProgram_elim_free tag payload _ _ shape
    (fun occurrence => inventory.indexedShapeCase_free construct tag payload children childCondition property cases
      injectivity childProof occurrence casesFree injectivityFree childrenFree) shapeFree

#print axioms shapeCasePredicate_subst
#print axioms subst_comp
#print axioms shapeProgram_subst
#print axioms rootProgram_subst
#print axioms shapeCase_parts
#print axioms shapeCase_parts_free
#print axioms shapeProgram_elim
#print axioms shapeProgram_elim_free
#print axioms constructorLift
#print axioms constructorLift_free
#print axioms indexedShapeCase
#print axioms indexedShapeCase_free
#print axioms constructorCases_lift
#print axioms constructorCases_lift_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (signature : Contextual Const Γ) {assumptions : List (Formula Const Γ)}

def childPredicate (predicate : Term Const Γ (signature.space ⇒ .prop))
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    Term Const Γ (signature.payload ⇒ .prop) :=
  .lam ((signature.subst (Subst.ofRename Rename.weaken)).childConditions
    (weaken predicate) (.var .vz) (weaken children))

def childPredicate_beta (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    ProofSyntax Const assumptions (.eq (.app (signature.childPredicate predicate children) payload)
      (signature.childConditions predicate payload children)) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta payload
    ((signature.subst (Subst.ofRename Rename.weaken)).childConditions
      (weaken predicate) (.var .vz) (weaken children)))
  simp only [childPredicate, instantiate, subst_childConditions]
  unfold childConditions Contextual.subst
  have cancel {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (Subst.single payload) (HOL.rename Rename.weaken term) = term :=
    PredicateFixedPoint.subst_single_weaken payload term
  simp only [HOL.subst, subst_ofRename, PredicateFixedPoint.subst_single_weaken,
    Subst.single]
  simp only [cancel]

theorem childPredicate_beta_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    (signature.childPredicate_beta (assumptions := assumptions) predicate payload children).FunctionExtensionalityFree := by
  unfold childPredicate_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

#print axioms childPredicate_beta
#print axioms childPredicate_beta_free
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {inventory : ConstructorPrograms Const Γ} (positions : PositionPrograms inventory) {space : Ty Base}
  (bottom : Term Const Γ space)
  (construct : Term Const Γ
    (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))
  {assumptions : List (Formula Const Γ)}

def ScopedIndexedCases (predicate : Term Const Γ (space ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (assumptions : List (Formula Const Γ)) :=
      let signature := positions.contextual bottom construct
      let images : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
      (inventory.subst images).IndexedCases (HOL.subst images construct) signature.constructorChildren
        (signature.constructorScope.childPredicate (weaken (weaken (weaken predicate))) signature.constructorChildren)
        (weaken (weaken (weaken property)))
        (signature.methodAssumptions (assumptions := assumptions) predicate)

def constructorMethod_of_cases (predicate : Term Const Γ (space ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (cases : positions.ScopedIndexedCases bottom construct predicate property assumptions) :
    (positions.contextual bottom construct).ConstructorMethod (assumptions := assumptions) predicate
      (IndexedPredicateInduction.lift (inventory.rootProgram construct) property) := by
  let signature := positions.contextual bottom construct
  let images : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  let shifted := inventory.subst images
  let constructor := HOL.subst images construct
  let methodHypotheses := signature.methodAssumptions (assumptions := assumptions) predicate
  let predicate3 : Term Const signature.constructorContext (space ⇒ .prop) := weaken (weaken (weaken predicate))
  let property3 : Term Const signature.constructorContext (space ⇒ inventory.index ⇒ .prop) :=
    weaken (weaken (weaken property))
  let condition := signature.constructorScope.childPredicate predicate3 signature.constructorChildren
  have liftedInjectivity : ProofSyntax Const methodHypotheses (ConstructorInjectivity.statement constructor) := by
    apply ProofSyntax.castIndices ?_ ?_
      (((PredicateFixedPoint.weakenProof (PredicateFixedPoint.weakenProof
        (PredicateFixedPoint.weakenProof injectivity))).prepend
        (signature.constructorScope.childConditions predicate3 signature.constructorPayload signature.constructorChildren)).prepend
        (signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload))
    · rfl
    · simp only [constructor, images, subst_ofRename, signature.rename_constructorRenaming,
        ConstructorInjectivity.rename_statement, weaken]
  have shape : ProofSyntax Const methodHypotheses
      (.app (.app shifted.shapeProgram signature.constructorTag) signature.constructorPayload) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Const) (Δ := methodHypotheses)
      ⟨0, by simp [methodHypotheses, RecursiveSpacePredicate.Contextual.methodAssumptions]⟩)
    simp only [methodHypotheses, RecursiveSpacePredicate.Contextual.methodAssumptions,
      List.get_eq_getElem, List.getElem_cons_zero, RecursiveSpacePredicate.Contextual.shapeAt,
      RecursiveSpacePredicate.Contextual.constructorScope, RecursiveSpacePredicate.Contextual.subst,
      contextual, signature, shifted, images, ← ConstructorPrograms.shapeProgram_subst]
  have childProof : ProofSyntax Const methodHypotheses (.app condition signature.constructorPayload) :=
    .impE (.eqPropER (signature.constructorScope.childPredicate_beta predicate3
      signature.constructorPayload signature.constructorChildren))
      (.hyp ⟨1, by simp [methodHypotheses, RecursiveSpacePredicate.Contextual.methodAssumptions]⟩)
  have result := shifted.constructorCases_lift constructor signature.constructorTag signature.constructorPayload
    signature.constructorChildren condition property3 cases liftedInjectivity shape childProof
  apply ProofSyntax.castIndices rfl ?_ result
  have same : IndexedPredicateInduction.lift (shifted.rootProgram constructor) property3 =
      weaken (weaken (weaken (IndexedPredicateInduction.lift (inventory.rootProgram construct) property))) := by
    have rootSame : shifted.rootProgram constructor = HOL.subst images (inventory.rootProgram construct) :=
      (inventory.rootProgram_subst construct images).symm
    have propertySame : property3 = HOL.subst images property := by
      simp only [property3, images, subst_ofRename, signature.rename_constructorRenaming]
    rw [rootSame, propertySame, ← IndexedPredicateInduction.subst_lift]
    simpa only [images, subst_ofRename] using
      signature.rename_constructorRenaming (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)
  exact congrArg (fun term => Term.app term
    (signature.constructorScope.constructValue signature.constructorTag signature.constructorPayload signature.constructorChildren)) same

theorem constructorMethod_of_cases_free (predicate : Term Const Γ (space ⇒ .prop))
    (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (cases : positions.ScopedIndexedCases bottom construct predicate property assumptions)
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (casesFree :
      let signature := positions.contextual bottom construct
      ∀ {Ξ : Ctx Base} (images : Subst Const signature.constructorContext Ξ) occurrence arguments,
        (cases images occurrence arguments).FunctionExtensionalityFree) :
    (positions.constructorMethod_of_cases bottom construct predicate property injectivity cases).FunctionExtensionalityFree := by
  unfold constructorMethod_of_cases
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ConstructorPrograms.constructorCases_lift_free
  · exact casesFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      PredicateFixedPoint.weakenProof, ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.functionExtensionalityFree_rename] using injectivityFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · exact ⟨RecursiveSpacePredicate.Contextual.childPredicate_beta_free _ _ _ _, True.intro⟩

def induction_from_cases (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (cases : positions.ScopedIndexedCases bottom construct
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)) property assumptions)
    (point : Term Const Γ space) (target : Term Const Γ inventory.index)
    (member : ProofSyntax Const assumptions
      (.app (.app ((positions.contextual bottom construct).memberProgram (inventory.rootProgram construct)) point) target)) :
    ProofSyntax Const assumptions (.app (.app property point) target) := by
  let signature := positions.contextual bottom construct
  let lifted := IndexedPredicateInduction.lift (inventory.rootProgram construct) property
  have parts := ProofSyntax.impE (ProofSyntax.eqPropEL
    (signature.member_beta (inventory.rootProgram construct) point target)) member
  exact IndexedPredicateInduction.induction signature.operator (inventory.rootProgram construct) property point target
    signature.monotonicity
    (signature.constructor_closure (PredicateFixedPoint.intersection signature.least lifted) lifted
      (positions.constructorMethod_of_cases bottom construct _ property injectivity cases))
    (.andEL parts) (.andER parts)

theorem induction_from_cases_free (property : Term Const Γ (space ⇒ inventory.index ⇒ .prop))
    (injectivity : ProofSyntax Const assumptions (ConstructorInjectivity.statement construct))
    (cases : positions.ScopedIndexedCases bottom construct
      (PredicateFixedPoint.intersection (positions.contextual bottom construct).least
        (IndexedPredicateInduction.lift (inventory.rootProgram construct) property)) property assumptions)
    (point : Term Const Γ space) (target : Term Const Γ inventory.index)
    (member : ProofSyntax Const assumptions
      (.app (.app ((positions.contextual bottom construct).memberProgram (inventory.rootProgram construct)) point) target))
    (injectivityFree : injectivity.FunctionExtensionalityFree)
    (casesFree :
      let signature := positions.contextual bottom construct
      ∀ {Ξ : Ctx Base} (images : Subst Const signature.constructorContext Ξ) occurrence arguments,
        (cases images occurrence arguments).FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (positions.induction_from_cases bottom construct property injectivity cases point target member).FunctionExtensionalityFree := by
  unfold induction_from_cases
  apply IndexedPredicateInduction.induction_free
  · exact RecursiveSpacePredicate.Contextual.monotonicity_free _
  · apply RecursiveSpacePredicate.Contextual.constructor_closure_free
    exact positions.constructorMethod_of_cases_free bottom construct _ property injectivity cases injectivityFree casesFree
  · exact ⟨RecursiveSpacePredicate.Contextual.member_beta_free _ _ _ _, memberFree⟩
  · exact ⟨RecursiveSpacePredicate.Contextual.member_beta_free _ _ _ _, memberFree⟩

#print axioms constructorMethod_of_cases
#print axioms constructorMethod_of_cases_free
#print axioms induction_from_cases
#print axioms induction_from_cases_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
