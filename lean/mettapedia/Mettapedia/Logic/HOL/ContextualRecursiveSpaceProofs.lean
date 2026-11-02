import Mettapedia.Logic.HOL.ContextualRecursiveSpacePredicate
import Mettapedia.Logic.HOL.PredicateFixedPointInduction
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Retained construction and induction for open recursive-space operators

Constructor operations and guards keep their surrounding context. Parent
shape, active-child edge and membership evidence, and inactive padding remain
explicit. The existing positive-code and fixed-point programs build the
resulting proof syntax without a new inference rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  (signature : Contextual Const Γ)

def constructValue (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) : Term Const Γ signature.space :=
  .app (.app (.app signature.construct tag) payload) children

def shapeAt (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload) : Formula Const Γ :=
  .app (.app signature.validShape tag) payload

def childConditions (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space)) : Formula Const Γ :=
  .all (.and
    (.imp (.app (.app (weaken signature.active) (weaken payload)) (.var .vz))
      (.and (.app (.app (.app (weaken signature.validEdge) (weaken payload)) (.var .vz))
        (.app (weaken children) (.var .vz)))
        (.app (weaken predicate) (.app (weaken children) (.var .vz)))))
    (.imp (.not (.app (.app (weaken signature.active) (weaken payload)) (.var .vz)))
      (.eq (.app (weaken children) (.var .vz)) (weaken signature.bottom))))

section Reading
universe u' v'
variable {Target : Type u'} {Symbols : Ty Target → Type v'}
  (reading : TermInterpretation Base Const Target Symbols)

@[simp] theorem read_constructValue (tag : Term Const Γ signature.number)
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space)) :
    reading.term (signature.constructValue tag payload children) =
      (signature.read reading).constructValue (reading.term tag) (reading.term payload) (reading.term children) := by
  simp only [constructValue, Contextual.read, TermInterpretation.term_app]

@[simp] theorem read_shapeAt (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload) :
    reading.term (signature.shapeAt tag payload) =
      (signature.read reading).shapeAt (reading.term tag) (reading.term payload) := by
  simp only [shapeAt, Contextual.read, TermInterpretation.term_app]

@[simp] theorem read_childConditions (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space)) :
    reading.term (signature.childConditions predicate payload children) =
      (signature.read reading).childConditions (reading.term predicate) (reading.term payload) (reading.term children) := by
  simp only [childConditions, Contextual.read, TermInterpretation.term_all, TermInterpretation.term_and,
    TermInterpretation.term_imp, TermInterpretation.term_not, TermInterpretation.term_eq,
    TermInterpretation.term_app, TermInterpretation.term_var, TermInterpretation.term_weaken, Var.mapTypes]

end Reading

@[simp] theorem subst_constructValue (theta : Subst Const Γ Ξ)
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    HOL.subst theta (signature.constructValue tag payload children) =
      (signature.subst theta).constructValue (HOL.subst theta tag) (HOL.subst theta payload) (HOL.subst theta children) := by
  rfl

@[simp] theorem subst_shapeAt (theta : Subst Const Γ Ξ)
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload) :
    HOL.subst theta (signature.shapeAt tag payload) =
      (signature.subst theta).shapeAt (HOL.subst theta tag) (HOL.subst theta payload) := rfl

@[simp] theorem subst_childConditions (theta : Subst Const Γ Ξ)
    (predicate : Term Const Γ (signature.space ⇒ .prop)) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    HOL.subst theta (signature.childConditions predicate payload children) =
      (signature.subst theta).childConditions (HOL.subst theta predicate) (HOL.subst theta payload) (HOL.subst theta children) := by
  simp [childConditions, Contextual.subst, HOL.subst, subst_weaken, Subst.lift]

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

variable {assumptions : List (Formula Const Γ)}

/-- The three witnesses of one constructor layer, with their original context. -/
abbrev constructorContext : Ctx Base :=
  (signature.number ⇒ signature.space) :: signature.payload :: signature.number :: Γ

def constructorRenaming : Rename Base Γ signature.constructorContext :=
  fun index => .vs (.vs (.vs index))

@[simp] theorem rename_constructorRenaming {type : Ty Base} (term : Term Const Γ type) :
    HOL.rename signature.constructorRenaming term = weaken (weaken (weaken term)) := by
  simp only [weaken, rename_comp]
  rfl

def constructorScope : Contextual Const signature.constructorContext :=
  signature.subst (Subst.ofRename signature.constructorRenaming)

def constructorTag : Term Const signature.constructorContext signature.number :=
  .var (.vs (.vs .vz))

def constructorPayload : Term Const signature.constructorContext signature.payload :=
  .var (.vs .vz)

def constructorChildren : Term Const signature.constructorContext (signature.number ⇒ signature.space) :=
  .var .vz

def layerBody (predicate : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space) (tag : Term Const Γ signature.number)
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space)) :
    Formula Const Γ :=
  .and (signature.shapeAt tag payload)
    (.and (.eq point (signature.constructValue tag payload children))
      (signature.childConditions predicate payload children))

def layer (predicate : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space) : Formula Const Γ :=
  .ex (σ := signature.number) (.ex (σ := signature.payload)
    (.ex (σ := signature.number ⇒ signature.space)
      (signature.constructorScope.layerBody
        (weaken (weaken (weaken predicate)))
        (weaken (weaken (weaken point)))
        signature.constructorTag signature.constructorPayload signature.constructorChildren)))

theorem body_eq_layer (predicate : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space) :
    signature.code.body predicate point = signature.layer predicate point := by
  simp [PositivePredicate.Code.body, code, PositivePredicate.Code.subst,
    PositivePredicate.Code.interpret, layer, layerBody, constructorScope,
    constructorTag, constructorPayload, constructorChildren,
    shapeAt, constructValue, childConditions, Contextual.subst,
    HOL.subst, HOL.subst_weaken, Subst.single, Subst.lift,
    Rename.weaken]
  all_goals simp only [weaken, rename_var, rename_comp, Rename.weaken]
  all_goals trivial

/-- A method sees both guards and the unchanged surrounding hypotheses. -/
def methodAssumptions (predicate : Term Const Γ (signature.space ⇒ .prop)) :
    List (Formula Const signature.constructorContext) :=
  signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload ::
    signature.constructorScope.childConditions
      (weaken (weaken (weaken predicate)))
      signature.constructorPayload signature.constructorChildren ::
    weakenHyps (σ := signature.number ⇒ signature.space)
      (weakenHyps (σ := signature.payload) (weakenHyps (σ := signature.number) assumptions))

abbrev ConstructorMethod (predicate property : Term Const Γ (signature.space ⇒ .prop)) :=
  ProofSyntax Const (signature.methodAssumptions (assumptions := assumptions) predicate)
    (.app (weaken (weaken (weaken property)))
      (signature.constructorScope.constructValue signature.constructorTag
        signature.constructorPayload signature.constructorChildren))

def rename_method (mapping : Rename Base Γ Ξ)
    (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property) :
    (signature.subst (Subst.ofRename mapping)).ConstructorMethod
      (assumptions := assumptions.map (HOL.rename mapping))
      (HOL.rename mapping predicate) (HOL.rename mapping property) := by
  apply ProofSyntax.castIndices _ _
    (ProofSyntax.rename (Rename.lift (Rename.lift (Rename.lift mapping))) method)
  all_goals simp [methodAssumptions, constructorScope, constructorRenaming,
    constructorTag, constructorPayload, constructorChildren,
    shapeAt, childConditions, constructValue, Contextual.subst,
    subst_ofRename, ExtDerivation.rename_weaken,
    HOL.rename, Rename.lift, weakenHyps, List.map_map]
  all_goals simp only [weaken, rename_comp, Rename.weaken]
  all_goals trivial

def prepend_method (head : Formula Const Γ)
    (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property) :
    signature.ConstructorMethod (assumptions := head :: assumptions) predicate property := by
  let shape := signature.constructorScope.shapeAt signature.constructorTag signature.constructorPayload
  let conditions := signature.constructorScope.childConditions
    (weaken (weaken (weaken predicate))) signature.constructorPayload signature.constructorChildren
  let head3 : Formula Const signature.constructorContext := weaken (weaken (weaken head))
  exact ProofSyntax.mono
    (((ProofSyntax.OccurrenceMap.prepend head3).lift conditions).lift shape) method

theorem rename_method_free (mapping : Rename Base Γ Ξ)
    (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (free : method.FunctionExtensionalityFree) :
    (signature.rename_method mapping predicate property method).FunctionExtensionalityFree := by
  unfold rename_method
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free

theorem prepend_method_free (head : Formula Const Γ)
    (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (free : method.FunctionExtensionalityFree) :
    (signature.prepend_method head predicate property method).FunctionExtensionalityFree := by
  simpa only [prepend_method, ProofSyntax.functionExtensionalityFree_mono] using free

/-- Eliminate the actual constructor witnesses and transport the method's
result along their equality with the requested point. -/
def layer_elim (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space)
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (present : ProofSyntax Const assumptions (signature.layer predicate point)) :
    ProofSyntax Const assumptions (.app property point) := by
  let liftedSignature := signature.constructorScope
  let predicate3 : Term Const signature.constructorContext (signature.space ⇒ .prop) :=
    weaken (weaken (weaken predicate))
  let property3 : Term Const signature.constructorContext (signature.space ⇒ .prop) :=
    weaken (weaken (weaken property))
  let point3 : Term Const signature.constructorContext signature.space :=
    weaken (weaken (weaken point))
  let shape := liftedSignature.shapeAt signature.constructorTag signature.constructorPayload
  let conditions := liftedSignature.childConditions predicate3 signature.constructorPayload signature.constructorChildren
  let constructed := liftedSignature.constructValue signature.constructorTag
    signature.constructorPayload signature.constructorChildren
  let third : Formula Const signature.constructorContext :=
    .and shape (.and (.eq point3 constructed) conditions)
  let second : Formula Const (signature.payload :: signature.number :: Γ) := .ex third
  let first : Formula Const (signature.number :: Γ) := .ex second
  let tail := weakenHyps (σ := signature.number ⇒ signature.space)
    (weakenHyps (σ := signature.payload) (weakenHyps (σ := signature.number) assumptions))
  let branchHypotheses := third :: weaken second :: weaken (weaken first) :: tail
  have displayed : ProofSyntax Const assumptions (.ex first) := present
  refine .exE displayed (.exE (.hyp 0) (.exE (.hyp 0) ?_))
  change ProofSyntax Const branchHypotheses (.app property3 point3)
  have prepared : ProofSyntax Const (shape :: conditions :: tail) (.app property3 constructed) := method
  let supplied : ProofSyntax.HypothesisSubstitution
      (shape :: conditions :: tail) branchHypotheses :=
    Fin.cases (.andEL (.hyp 0))
      (Fin.cases (.andER (.andER (.hyp 0)))
        (fun occurrence => ProofSyntax.hyp (Const := Const) (Δ := branchHypotheses)
          occurrence.succ.succ.succ))
  have constructedResult := ProofSyntax.substituteHypotheses supplied prepared
  have samePoint : ProofSyntax Const branchHypotheses (.eq point3 constructed) :=
    .andEL (.andER (.hyp 0))
  exact .impE (.eqPropER (.eqAppArg property3 samePoint)) constructedResult

theorem layer_elim_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space)
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (present : ProofSyntax Const assumptions (signature.layer predicate point))
    (methodFree : method.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (signature.layer_elim predicate property point method present).FunctionExtensionalityFree := by
  unfold layer_elim
  refine ⟨presentFree, True.intro, True.intro, True.intro, ?_⟩
  apply ProofSyntax.substituteHypotheses_free _ method methodFree
  intro occurrence
  refine Fin.cases ?_ (fun prior => ?_) occurrence
  · trivial
  · refine Fin.cases ?_ (fun tail => ?_) prior <;> trivial

def layer_intro (predicate : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const assumptions (signature.childConditions predicate payload children)) :
    ProofSyntax Const assumptions (signature.code.body predicate (signature.constructValue tag payload children)) := by
  refine .exI tag (.exI payload (.exI children ?_))
  apply ProofSyntax.castIndices rfl ?_
    (.andI shape (.andI (.eqRefl (signature.constructValue tag payload children)) childProof))
  simp [instantiate, HOL.subst, subst_weaken, Subst.single, Subst.lift, subst_rename, subst_comp,
    Rename.weaken, subst_drop_shift, subst_drop_two, subst_variables, childConditions, shapeAt, constructValue,
    PositivePredicate.Code.subst, PositivePredicate.Code.interpret]
  simp only [weaken, ← subst_ofRename]
  exact ⟨rfl, True.intro⟩

@[irreducible] def operator_body (predicate : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space) :
    ProofSyntax Const assumptions (.eq (.app (.app signature.operator predicate) point) (signature.code.body predicate point)) :=
  signature.code.operator_beta predicate point

theorem operator_body_free (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space) :
    (signature.operator_body (assumptions := assumptions) predicate point).FunctionExtensionalityFree := by
  simp [operator_body, PositivePredicate.Code.operator_beta, ProofSyntax.FunctionExtensionalityFree]

def operator_elim (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space)
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (present : ProofSyntax Const assumptions (.app (.app signature.operator predicate) point)) :
    ProofSyntax Const assumptions (.app property point) :=
  signature.layer_elim predicate property point method
    (ProofSyntax.castIndices rfl (signature.body_eq_layer predicate point)
      (.impE (.eqPropEL (signature.operator_body predicate point)) present))

theorem operator_elim_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space)
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (present : ProofSyntax Const assumptions (.app (.app signature.operator predicate) point))
    (methodFree : method.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (signature.operator_elim predicate property point method present).FunctionExtensionalityFree := by
  apply signature.layer_elim_free predicate property point method _ methodFree
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨signature.operator_body_free predicate point, presentFree⟩

/-- A guarded constructor method supplies the operator's complete layer
closure; the point binder is introduced by retained renaming. -/
def constructor_closure (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property) :
    ProofSyntax Const assumptions (PredicateFixedPoint.included (.app signature.operator predicate) property) := by
  refine .allI (.impI ?_)
  let liftedSignature := signature.subst (Subst.ofRename (Rename.weaken (σ := signature.space)))
  let point : Term Const (signature.space :: Γ) signature.space := .var .vz
  let premise : Formula Const (signature.space :: Γ) :=
    .app (weaken (.app signature.operator predicate)) point
  let moved := signature.rename_method (Rename.weaken (σ := signature.space)) predicate property method
  let usable := liftedSignature.prepend_method premise (weaken predicate) (weaken property) moved
  have samePremise : premise = .app (.app liftedSignature.operator (weaken predicate)) point := by
    exact congrArg
      (fun operator : Term Const (signature.space :: Γ) (PredicateFixedPoint.Operator signature.space) =>
        Term.app (Term.app operator (weaken predicate)) point)
      (signature.rename_operator (Rename.weaken (σ := signature.space)))
  let present : ProofSyntax Const (premise :: weakenHyps (σ := signature.space) assumptions)
      (.app (.app liftedSignature.operator (weaken predicate)) point) :=
    ProofSyntax.castIndices rfl samePremise (.hyp 0)
  exact liftedSignature.operator_elim (weaken predicate) (weaken property) point usable present

theorem constructor_closure_free (predicate property : Term Const Γ (signature.space ⇒ .prop))
    (method : signature.ConstructorMethod (assumptions := assumptions) predicate property)
    (free : method.FunctionExtensionalityFree) :
    (signature.constructor_closure predicate property method).FunctionExtensionalityFree := by
  unfold constructor_closure
  apply operator_elim_free
  · apply prepend_method_free
    exact signature.rename_method_free _ predicate property method free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def constructor_intro (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const assumptions (signature.childConditions signature.least payload children)) :
    ProofSyntax Const assumptions (.app signature.least (signature.constructValue tag payload children)) :=
  PredicateFixedPoint.closure_at signature.operator _ signature.monotonicity
    (.impE (.eqPropER (signature.operator_body signature.least (signature.constructValue tag payload children)))
      (signature.layer_intro signature.least tag payload children shape childProof))

def childConditions_intro (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (edges : ProofSyntax Const (weakenHyps (σ := signature.number) assumptions)
      (.imp (.app (.app (weaken signature.active) (weaken payload)) (.var .vz))
        (.app (.app (.app (weaken signature.validEdge) (weaken payload)) (.var .vz))
          (.app (weaken children) (.var .vz)))))
    (members : ProofSyntax Const (weakenHyps (σ := signature.number) assumptions)
      (.imp (.app (.app (weaken signature.active) (weaken payload)) (.var .vz))
        (.app (weaken predicate) (.app (weaken children) (.var .vz)))))
    (padding : ProofSyntax Const (weakenHyps (σ := signature.number) assumptions)
      (.imp (.not (.app (.app (weaken signature.active) (weaken payload)) (.var .vz)))
        (.eq (.app (weaken children) (.var .vz)) (weaken signature.bottom)))) :
    ProofSyntax Const assumptions (signature.childConditions predicate payload children) :=
  .allI (.andI (.impI (.andI
    (.impE (edges.prepend _) (.hyp 0)) (.impE (members.prepend _) (.hyp 0)))) padding)

theorem childConditions_intro_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (edges : ProofSyntax Const (weakenHyps (σ := signature.number) assumptions)
      (.imp (.app (.app (weaken signature.active) (weaken payload)) (.var .vz))
        (.app (.app (.app (weaken signature.validEdge) (weaken payload)) (.var .vz))
          (.app (weaken children) (.var .vz)))))
    (members : ProofSyntax Const (weakenHyps (σ := signature.number) assumptions)
      (.imp (.app (.app (weaken signature.active) (weaken payload)) (.var .vz))
        (.app (weaken predicate) (.app (weaken children) (.var .vz)))))
    (padding : ProofSyntax Const (weakenHyps (σ := signature.number) assumptions)
      (.imp (.not (.app (.app (weaken signature.active) (weaken payload)) (.var .vz)))
        (.eq (.app (weaken children) (.var .vz)) (weaken signature.bottom))))
    (edgeFree : edges.FunctionExtensionalityFree)
    (memberFree : members.FunctionExtensionalityFree)
    (paddingFree : padding.FunctionExtensionalityFree) :
    (signature.childConditions_intro predicate payload children edges members padding).FunctionExtensionalityFree := by
  simp only [childConditions_intro, ProofSyntax.FunctionExtensionalityFree,
    ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
    edgeFree, memberFree, paddingFree, and_self]

@[irreducible] def fixedPoint_at (point : Term Const Γ signature.space) :
    ProofSyntax Const assumptions (.eq (.app signature.least point)
      (.app (.app signature.operator signature.least) point)) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE point signature.fixedPoint)
  simp only [instantiate, HOL.subst, PredicateFixedPoint.subst_single_weaken, Subst.single, least]

def unfold_member (point : Term Const Γ signature.space)
    (member : ProofSyntax Const assumptions (.app signature.least point)) :
    ProofSyntax Const assumptions (signature.code.body signature.least point) :=
  .impE (.eqPropEL (signature.operator_body signature.least point))
    (.impE (.eqPropEL (signature.fixedPoint_at point)) member)

def induction (property : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space)
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app signature.operator (PredicateFixedPoint.intersection signature.least property)) property))
    (member : ProofSyntax Const assumptions (.app signature.least point)) :
    ProofSyntax Const assumptions (.app property point) :=
  PredicateFixedPoint.guarded_induction signature.operator property point signature.monotonicity step member

theorem layer_intro_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const assumptions (signature.childConditions predicate payload children))
    (shapeFree : shape.FunctionExtensionalityFree) (childrenFree : childProof.FunctionExtensionalityFree) :
    (signature.layer_intro predicate tag payload children shape childProof).FunctionExtensionalityFree := by
  simp [layer_intro, ProofSyntax.FunctionExtensionalityFree, shapeFree, childrenFree]

theorem constructor_intro_free (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const assumptions (signature.childConditions signature.least payload children))
    (shapeFree : shape.FunctionExtensionalityFree) (childrenFree : childProof.FunctionExtensionalityFree) :
    (signature.constructor_intro tag payload children shape childProof).FunctionExtensionalityFree := by
  unfold constructor_intro
  apply PredicateFixedPoint.closure_at_free
  · exact signature.monotonicity_free
  · exact ⟨signature.operator_body_free signature.least (signature.constructValue tag payload children),
      signature.layer_intro_free signature.least tag payload children shape childProof shapeFree childrenFree⟩

theorem fixedPoint_at_free (point : Term Const Γ signature.space) :
    (signature.fixedPoint_at (assumptions := assumptions) point).FunctionExtensionalityFree := by
  unfold fixedPoint_at
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact signature.fixedPoint_free

theorem unfold_member_free (point : Term Const Γ signature.space)
    (member : ProofSyntax Const assumptions (.app signature.least point)) (free : member.FunctionExtensionalityFree) :
    (signature.unfold_member point member).FunctionExtensionalityFree := by
  unfold unfold_member
  exact ⟨signature.operator_body_free signature.least point, signature.fixedPoint_at_free point, free⟩

theorem induction_free (property : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space)
    (step : ProofSyntax Const assumptions (PredicateFixedPoint.included
      (.app signature.operator (PredicateFixedPoint.intersection signature.least property)) property))
    (member : ProofSyntax Const assumptions (.app signature.least point))
    (stepFree : step.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (signature.induction property point step member).FunctionExtensionalityFree :=
  PredicateFixedPoint.guarded_induction_free signature.operator property point signature.monotonicity step member
    signature.monotonicity_free stepFree memberFree

/-- Guarded induction obtains its layer closure from the supplied constructor
method, retaining both recursive membership and the induction hypothesis. -/
def induction_from_method (property : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space)
    (method : signature.ConstructorMethod (assumptions := assumptions)
      (PredicateFixedPoint.intersection signature.least property) property)
    (member : ProofSyntax Const assumptions (.app signature.least point)) :
    ProofSyntax Const assumptions (.app property point) :=
  signature.induction property point
    (signature.constructor_closure (PredicateFixedPoint.intersection signature.least property) property method) member

theorem induction_from_method_free (property : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space)
    (method : signature.ConstructorMethod (assumptions := assumptions)
      (PredicateFixedPoint.intersection signature.least property) property)
    (member : ProofSyntax Const assumptions (.app signature.least point))
    (methodFree : method.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (signature.induction_from_method property point method member).FunctionExtensionalityFree :=
  signature.induction_free property point _ member
    (signature.constructor_closure_free _ _ method methodFree) memberFree

def memberProgram {index : Ty Base} (root : Term Const Γ (signature.space ⇒ index ⇒ .prop)) :
    Term Const Γ (signature.space ⇒ index ⇒ .prop) :=
  CurriedGuardProgramProofs.conjunctionProgram signature.least root

@[simp] theorem read_memberProgram {Target : Type*} {Symbols : Ty Target → Type*}
    (reading : TermInterpretation Base Const Target Symbols) {index : Ty Base}
    (root : Term Const Γ (signature.space ⇒ index ⇒ .prop)) :
    reading.term (signature.memberProgram root) = (signature.read reading).memberProgram (reading.term root) := by
  simp only [memberProgram, CurriedGuardProgramProofs.read_conjunctionProgram, Contextual.read_least]

@[irreducible] def member_beta {index : Ty Base} (root : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (point : Term Const Γ signature.space) (target : Term Const Γ index) :
    ProofSyntax Const assumptions (.eq (.app (.app (signature.memberProgram root) point) target)
      (.and (.app signature.least point) (.app (.app root point) target))) :=
  CurriedGuardProgramProofs.conjunctionProgram_beta signature.least root point target

theorem member_beta_free {index : Ty Base} (root : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (point : Term Const Γ signature.space) (target : Term Const Γ index) :
    (signature.member_beta (assumptions := assumptions) root point target).FunctionExtensionalityFree := by
  unfold member_beta
  exact CurriedGuardProgramProofs.conjunctionProgram_beta_free signature.least root point target

@[irreducible] def member_intro {index : Ty Base} (root : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) (target : Term Const Γ index)
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const assumptions (signature.childConditions signature.least payload children))
    (rootProof : ProofSyntax Const assumptions
      (.app (.app root (signature.constructValue tag payload children)) target)) :
    ProofSyntax Const assumptions
      (.app (.app (signature.memberProgram root) (signature.constructValue tag payload children)) target) :=
  .impE (.eqPropER (signature.member_beta root _ target))
    (.andI (signature.constructor_intro tag payload children shape childProof) rootProof)

theorem member_intro_free {index : Ty Base} (root : Term Const Γ (signature.space ⇒ index ⇒ .prop))
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) (target : Term Const Γ index)
    (shape : ProofSyntax Const assumptions (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const assumptions (signature.childConditions signature.least payload children))
    (rootProof : ProofSyntax Const assumptions
      (.app (.app root (signature.constructValue tag payload children)) target))
    (shapeFree : shape.FunctionExtensionalityFree) (childrenFree : childProof.FunctionExtensionalityFree)
    (rootFree : rootProof.FunctionExtensionalityFree) :
    (signature.member_intro root tag payload children target shape childProof rootProof).FunctionExtensionalityFree := by
  unfold member_intro
  exact ⟨signature.member_beta_free root _ target,
    signature.constructor_intro_free tag payload children shape childProof shapeFree childrenFree, rootFree⟩

#print axioms constructor_intro
#print axioms constructor_intro_free
#print axioms unfold_member_free
#print axioms induction_free
#print axioms body_eq_layer
#print axioms layer_elim
#print axioms layer_elim_free
#print axioms operator_elim
#print axioms operator_elim_free
#print axioms rename_method
#print axioms rename_method_free
#print axioms prepend_method
#print axioms prepend_method_free
#print axioms constructor_closure
#print axioms constructor_closure_free
#print axioms induction_from_method
#print axioms induction_from_method_free

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Contextual
