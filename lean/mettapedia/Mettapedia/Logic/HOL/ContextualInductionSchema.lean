import Mettapedia.Logic.HOL.IndexedPredicateInduction
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs
import Mettapedia.Logic.HOL.IndexedConstructorInduction

/-!
# A closed constructor method for reusable indexed induction

The method's original hypothesis stack is shape, children, then ambient
premises. Closing that stack introduces the child implication before the
shape implication. Opening it recovers the same ordered method interface.
The indexed induction proof consumes this derived method explicitly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (signature : Contextual Const Γ)

def closedMethod (predicate property : Term Const Γ (signature.space ⇒ .prop)) : Formula Const Γ :=
  .all (.all (.all (.imp
    (signature.constructorScope.childConditions (weaken (weaken (weaken predicate)))
      signature.constructorPayload signature.constructorChildren)
    (.imp (signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload)
      (.app (weaken (weaken (weaken property)))
        (signature.constructorScope.constructValue signature.constructorTag
          signature.constructorPayload signature.constructorChildren))))))

def parametricMethod (property : Term Const Γ (signature.space ⇒ .prop)) : Formula Const Γ :=
  .all (.all (.all (.all
    (.imp (weaken (signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload))
      (.imp (.app (.var .vz) (weaken signature.constructorPayload))
        (.app (weaken (weaken (weaken (weaken property))))
          (weaken (signature.constructorScope.constructValue signature.constructorTag
            signature.constructorPayload signature.constructorChildren))))))))

@[simp] theorem subst_parametricMethod (images : Subst Const Γ Ξ)
    (property : Term Const Γ (signature.space ⇒ .prop)) :
    HOL.subst images (signature.parametricMethod property) =
      (signature.subst images).parametricMethod (HOL.subst images property) := by
  simp [parametricMethod, constructorScope, constructorTag, constructorPayload, constructorChildren,
    Contextual.subst, shapeAt, constructValue, HOL.subst, Subst.lift, subst_weaken, Rename.weaken]

@[simp] theorem subst_closedMethod (images : Subst Const Γ Ξ)
    (predicate property : Term Const Γ (signature.space ⇒ .prop)) :
    HOL.subst images (signature.closedMethod predicate property) =
      (signature.subst images).closedMethod (HOL.subst images predicate) (HOL.subst images property) := by
  simp [closedMethod, constructorScope, constructorTag, constructorPayload, constructorChildren,
    Contextual.subst, shapeAt, constructValue, childConditions, HOL.subst,
    Subst.lift, subst_weaken, Rename.weaken]

section Reading
universe u' v'
variable {Target : Type u'} {Symbols : Ty Target → Type v'}
    (reading : TermInterpretation Base Const Target Symbols)

@[simp] theorem read_indexedLift {space index : Ty Base}
    (root property : Term Const Γ (space ⇒ index ⇒ .prop)) :
    reading.term (IndexedPredicateInduction.lift root property) =
      IndexedPredicateInduction.lift (reading.term root) (reading.term property) := by
  simp only [IndexedPredicateInduction.lift, TermInterpretation.term_lam,
    TermInterpretation.term_all, TermInterpretation.term_imp, TermInterpretation.term_app,
    TermInterpretation.term_var, TermInterpretation.term_weaken, Var.mapTypes]

@[simp] theorem read_predicateIntersection {space : Ty Base}
    (first second : Term Const Γ (space ⇒ .prop)) :
    reading.term (PredicateFixedPoint.intersection first second) =
      PredicateFixedPoint.intersection (reading.term first) (reading.term second) := by
  simp only [PredicateFixedPoint.intersection, TermInterpretation.term_lam,
    TermInterpretation.term_and, TermInterpretation.term_app, TermInterpretation.term_var,
    TermInterpretation.term_weaken, Var.mapTypes]

@[simp] theorem read_closedMethod (predicate property : Term Const Γ (signature.space ⇒ .prop)) :
    reading.term (signature.closedMethod predicate property) =
      (signature.read reading).closedMethod (reading.term predicate) (reading.term property) := by
  simp [closedMethod, constructorScope, constructorTag, constructorPayload, constructorChildren,
    shapeAt, constructValue, childConditions, Contextual.read, Contextual.subst,
    subst_ofRename, signature.rename_constructorRenaming,
    TermInterpretation.term_all, TermInterpretation.term_imp, TermInterpretation.term_and,
    TermInterpretation.term_not, TermInterpretation.term_eq, TermInterpretation.term_app,
    TermInterpretation.term_var, TermInterpretation.term_weaken, Var.mapTypes]

@[simp] theorem read_parametricMethod (property : Term Const Γ (signature.space ⇒ .prop)) :
    reading.term (signature.parametricMethod property) =
      (signature.read reading).parametricMethod (reading.term property) := by
  simp [parametricMethod, constructorScope, constructorTag, constructorPayload, constructorChildren,
    shapeAt, constructValue, Contextual.read, Contextual.subst,
    subst_ofRename, signature.rename_constructorRenaming,
    TermInterpretation.term_all, TermInterpretation.term_imp, TermInterpretation.term_app,
    TermInterpretation.term_var, TermInterpretation.term_weaken, Var.mapTypes]

end Reading

private theorem subst_variables {type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (fun index => .var index) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem subst_drop_shift {domain type : Ty Base}
    (value : Term Const Γ domain) (term : Term Const Γ type) :
    HOL.subst (Subst.comp (Subst.single value) (fun index => .var (.vs index))) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem subst_drop_two {first second type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (term : Term Const Γ type) :
    HOL.subst (Subst.comp (Subst.single b)
      (Subst.comp (Subst.lift (Subst.single a)) (fun index => .var (.vs (.vs index))))) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem subst_drop_three {first second third type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (term : Term Const Γ type) :
    HOL.subst (Subst.comp (Subst.single c)
      (Subst.comp (Subst.lift (Subst.single b))
        (Subst.comp (Subst.lift (Subst.lift (Subst.single a)))
          (fun index => .var (.vs (.vs (.vs index))))))) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

@[simp] private theorem subst_weaken_variables {domain type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (fun index => .var (.vs (σ := domain) index)) term = HOL.rename Rename.weaken term :=
  subst_ofRename _ _

@[simp] private theorem subst_drop_two_lifted {first second domain type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (term : Term Const Γ type) :
    HOL.subst (Subst.comp (Subst.lift (σ := domain) (Subst.single b))
      (Subst.comp (Subst.lift (Subst.lift (Subst.single a)))
        (fun index => .var (.vs (.vs (.vs index)))))) term = HOL.rename Rename.weaken term := by
  rw [← subst_ofRename]
  apply HOL.subst_ext
  intro type index
  rfl

variable {assumptions : List (Formula Const Γ)}

def applyParametricMethod (property : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (condition : Term Const Γ (signature.payload ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.parametricMethod property)) :
    ProofSyntax Const assumptions (.imp (signature.shapeAt tag payload)
      (.imp (.app condition payload) (.app property (signature.constructValue tag payload children)))) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.allE condition (ProofSyntax.allE children (ProofSyntax.allE payload (ProofSyntax.allE tag proof))))
  simp [constructorScope, constructorTag, constructorPayload, constructorChildren,
    Contextual.subst, shapeAt, constructValue, instantiate, HOL.subst, Subst.single, Subst.lift,
    subst_rename, HOL.subst_comp, subst_drop_two, subst_variables, weaken, Rename.weaken]

theorem applyParametricMethod_free (property : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (condition : Term Const Γ (signature.payload ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.parametricMethod property))
    (free : proof.FunctionExtensionalityFree) :
    (signature.applyParametricMethod property tag payload children condition proof).FunctionExtensionalityFree := by
  unfold applyParametricMethod
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

def closeMethod (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property) :
    ProofSyntax Const assumptions (signature.closedMethod predicate property) :=
  .allI (.allI (.allI (.impI (.impI method))))

theorem closeMethod_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (free : method.FunctionExtensionalityFree) :
    (signature.closeMethod predicate property method).FunctionExtensionalityFree := free

def applyClosedMethod (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (proof : ProofSyntax Const assumptions (signature.closedMethod predicate property)) :
    ProofSyntax Const assumptions (.imp (signature.childConditions predicate payload children)
      (.imp (signature.shapeAt tag payload) (.app property (signature.constructValue tag payload children)))) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.allE children (ProofSyntax.allE payload (ProofSyntax.allE tag proof)))
  simp [constructorScope, constructorTag, constructorPayload, constructorChildren,
    Contextual.subst, shapeAt, constructValue, childConditions,
    instantiate, HOL.subst, Subst.single, Subst.lift,
    subst_rename, HOL.subst_comp, subst_drop_two, subst_variables, weaken, Rename.weaken]

theorem applyClosedMethod_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (proof : ProofSyntax Const assumptions (signature.closedMethod predicate property))
    (free : proof.FunctionExtensionalityFree) :
    (signature.applyClosedMethod predicate property tag payload children proof).FunctionExtensionalityFree := by
  unfold applyClosedMethod
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

def openMethod (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.closedMethod predicate property)) :
    signature.ConstructorMethod (assumptions := assumptions) predicate property := by
  let scope : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  have lifted : ProofSyntax Const
      (weakenHyps (σ := signature.number ⇒ signature.space)
        (weakenHyps (σ := signature.payload) (weakenHyps (σ := signature.number) assumptions)))
      (signature.constructorScope.closedMethod (weaken (weaken (weaken predicate)))
        (weaken (weaken (weaken property)))) := by
    apply ProofSyntax.castIndices ?_ ?_ (ProofSyntax.subst scope proof)
    · simp [scope, subst_ofRename, signature.rename_constructorRenaming, weakenHyps, List.map_map, Function.comp_def]
    · simpa only [scope, subst_ofRename, signature.rename_constructorRenaming, constructorScope] using
        signature.subst_closedMethod scope predicate property
  let child := signature.constructorScope.childConditions (weaken (weaken (weaken predicate)))
    signature.constructorPayload signature.constructorChildren
  let shape := signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload
  let available := (lifted.prepend child).prepend shape
  exact .impE (.impE
    (signature.constructorScope.applyClosedMethod (weaken (weaken (weaken predicate)))
      (weaken (weaken (weaken property))) signature.constructorTag signature.constructorPayload
      signature.constructorChildren available) (.hyp ⟨1, by simp [methodAssumptions]⟩))
    (.hyp ⟨0, by simp [methodAssumptions]⟩)

theorem openMethod_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.closedMethod predicate property))
    (free : proof.FunctionExtensionalityFree) :
    (signature.openMethod predicate property proof).FunctionExtensionalityFree := by
  unfold openMethod
  refine ⟨?_, trivial⟩
  refine ⟨?_, trivial⟩
  apply applyClosedMethod_free
  simp only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
    ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst]
  exact free

def openParametricMethod (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.parametricMethod property)) :
    signature.ConstructorMethod (assumptions := assumptions) predicate property := by
  let scope : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  have lifted : ProofSyntax Const
      (weakenHyps (σ := signature.number ⇒ signature.space)
        (weakenHyps (σ := signature.payload) (weakenHyps (σ := signature.number) assumptions)))
      (signature.constructorScope.parametricMethod (weaken (weaken (weaken property)))) := by
    apply ProofSyntax.castIndices ?_ ?_ (ProofSyntax.subst scope proof)
    · simp [scope, subst_ofRename, signature.rename_constructorRenaming, weakenHyps, List.map_map, Function.comp_def]
    · simpa only [scope, subst_ofRename, signature.rename_constructorRenaming, constructorScope] using
        signature.subst_parametricMethod scope property
  let predicate3 : Term Const signature.constructorContext (signature.space ⇒ .prop) :=
    weaken (weaken (weaken predicate))
  let child := signature.constructorScope.childConditions predicate3
    signature.constructorPayload signature.constructorChildren
  let shape := signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload
  let available := (lifted.prepend child).prepend shape
  let condition := signature.constructorScope.childPredicate predicate3 signature.constructorChildren
  have childProof : ProofSyntax Const (signature.methodAssumptions (assumptions := assumptions) predicate)
      (.app condition signature.constructorPayload) :=
    .impE (.eqPropER (signature.constructorScope.childPredicate_beta predicate3
      signature.constructorPayload signature.constructorChildren)) (.hyp ⟨1, by simp [methodAssumptions]⟩)
  exact .impE (.impE (signature.constructorScope.applyParametricMethod
    (weaken (weaken (weaken property))) signature.constructorTag signature.constructorPayload
    signature.constructorChildren condition available) (.hyp ⟨0, by simp [methodAssumptions]⟩)) childProof

theorem openParametricMethod_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.parametricMethod property))
    (free : proof.FunctionExtensionalityFree) :
    (signature.openParametricMethod predicate property proof).FunctionExtensionalityFree := by
  unfold openParametricMethod
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · apply applyParametricMethod_free
    simp only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst]
    exact free
  · exact ⟨signature.constructorScope.childPredicate_beta_free _ _ _, trivial⟩

def parametricToClosed (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.parametricMethod property)) :
    ProofSyntax Const assumptions (signature.closedMethod predicate property) :=
  signature.closeMethod predicate property (signature.openParametricMethod predicate property proof)

theorem parametricToClosed_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (proof : ProofSyntax Const assumptions (signature.parametricMethod property))
    (free : proof.FunctionExtensionalityFree) :
    (signature.parametricToClosed predicate property proof).FunctionExtensionalityFree :=
  signature.closeMethod_free predicate property _ (signature.openParametricMethod_free predicate property proof free)

def indexedFromClosedMethod {index : Ty Base}
    (root property : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (point : Term Const Γ signature.space) (target : Term Const Γ index)
    (method : ProofSyntax Const assumptions (signature.closedMethod
      (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property))
      (IndexedPredicateInduction.lift root property)))
    (member : ProofSyntax Const assumptions (.app (.app (signature.memberProgram root) point) target)) :
    ProofSyntax Const assumptions (.app (.app property point) target) := by
  let lifted := IndexedPredicateInduction.lift root property
  have parts := ProofSyntax.impE (.eqPropEL (signature.member_beta root point target)) member
  exact IndexedPredicateInduction.induction signature.operator root property point target
    signature.monotonicity
    (signature.constructor_closure (PredicateFixedPoint.intersection signature.least lifted) lifted
      (signature.openMethod _ _ method)) (.andEL parts) (.andER parts)

theorem indexedFromClosedMethod_free {index : Ty Base}
    (root property : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (point : Term Const Γ signature.space) (target : Term Const Γ index)
    (method : ProofSyntax Const assumptions (signature.closedMethod
      (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift root property))
      (IndexedPredicateInduction.lift root property)))
    (member : ProofSyntax Const assumptions (.app (.app (signature.memberProgram root) point) target))
    (methodFree : method.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (signature.indexedFromClosedMethod root property point target method member).FunctionExtensionalityFree := by
  unfold indexedFromClosedMethod
  apply IndexedPredicateInduction.induction_free
  · exact signature.monotonicity_free
  · apply signature.constructor_closure_free
    exact signature.openMethod_free _ _ method methodFree
  · exact ⟨signature.member_beta_free root point target, memberFree⟩
  · exact ⟨signature.member_beta_free root point target, memberFree⟩

#print axioms subst_closedMethod
#print axioms closeMethod_free
#print axioms applyClosedMethod_free
#print axioms openMethod_free
#print axioms indexedFromClosedMethod_free

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
