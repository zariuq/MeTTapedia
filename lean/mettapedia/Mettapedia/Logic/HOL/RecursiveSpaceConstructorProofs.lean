import Mettapedia.Logic.HOL.RecursiveSpacePredicate
import Mettapedia.Logic.HOL.PredicateFixedPointInduction

/-!
# Retained constructor proofs for guarded recursive spaces

Shape, child-edge, recursive-membership and inactive-padding evidence remain
separate inputs. The positive operator supplies monotonicity; constructor
introduction into its least predicate uses retained HOL inferences only.
The signature is fixed while constructor terms may have an arbitrary context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Signature
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
  (signature : RecursiveSpacePredicate.Signature Const) {Γ Ξ : Ctx Base}

private theorem rename_from_empty {type : Ty Base} (term : ClosedTerm Const type)
    (context : Ctx Base) (mapping : Rename Base [] context) :
    rename mapping term = weakenCtx context term := by
  simpa only [weakenCtx_nil] using rename_weakenCtx mapping term

private theorem subst_variables {type : Ty Base} (term : Term Const Γ type) :
    subst (fun index => .var index) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem subst_drop_shift {domain type : Ty Base}
    (value : Term Const Γ domain) (term : Term Const Γ type) :
    subst (Subst.comp (Subst.single value) (fun index => .var (.vs index))) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

def codeIn : PositivePredicate.Code Const signature.space (signature.space :: Γ) :=
  signature.code.rename (Rename.lift
    (fun {type} (impossible : Var ([] : Ctx Base) type) => nomatch impossible))

theorem codeIn_operator : (signature.codeIn (Γ := Γ)).operator = weakenCtx Γ signature.operator := by
  rw [codeIn, PositivePredicate.Code.operator_rename]
  change rename _ signature.operator = weakenCtx Γ signature.operator
  simpa only [weakenCtx_nil] using
    (rename_weakenCtx
      (fun {type} (impossible : Var ([] : Ctx Base) type) => nomatch impossible) signature.operator)

def constructValue (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) : Term Const Γ signature.space :=
  .app (.app (.app (weakenCtx Γ signature.construct) tag) payload) children

def shapeAt (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload) : Formula Const Γ :=
  .app (.app (weakenCtx Γ signature.validShape) tag) payload

def activeAt (payload : Term Const Γ signature.payload) (slot : Term Const Γ signature.number) : Formula Const Γ :=
  .app (.app (weakenCtx Γ signature.active) payload) slot

def edgeAt (payload : Term Const Γ signature.payload) (slot : Term Const Γ signature.number)
    (child : Term Const Γ signature.space) : Formula Const Γ :=
  .app (.app (.app (weakenCtx Γ signature.validEdge) payload) slot) child

def slotConditions (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (slot : Term Const Γ signature.number) : Formula Const Γ :=
  .and (.imp (signature.activeAt payload slot)
      (.and (signature.edgeAt payload slot (.app children slot)) (.app predicate (.app children slot))))
    (.imp (.not (signature.activeAt payload slot)) (.eq (.app children slot) (weakenCtx Γ signature.bottom)))

def childConditions (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space)) :
    Formula Const Γ :=
  .all (signature.slotConditions (weaken predicate) (weaken payload) (weaken children) (.var .vz))

def layerBody (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space)
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) : Formula Const Γ :=
  .and (signature.shapeAt tag payload)
    (.and (.eq point (signature.constructValue tag payload children))
      (signature.childConditions predicate payload children))

def layer (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space) : Formula Const Γ :=
  .ex (σ := signature.number) (.ex (σ := signature.payload) (.ex (σ := signature.number ⇒ signature.space)
    (signature.layerBody (weaken (weaken (weaken predicate))) (weaken (weaken (weaken point)))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

@[simp] theorem subst_constructValue (theta : Subst Const Γ Ξ)
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    subst theta (signature.constructValue tag payload children) =
      signature.constructValue (subst theta tag) (subst theta payload) (subst theta children) := by
  simp [constructValue, subst, subst_weakenCtx]

@[simp] theorem subst_slotConditions (theta : Subst Const Γ Ξ)
    (predicate : Term Const Γ (signature.space ⇒ .prop)) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) (slot : Term Const Γ signature.number) :
    subst theta (signature.slotConditions predicate payload children slot) =
      signature.slotConditions (subst theta predicate) (subst theta payload) (subst theta children) (subst theta slot) := by
  simp [slotConditions, activeAt, edgeAt, subst, subst_weakenCtx]

@[simp] theorem subst_childConditions (theta : Subst Const Γ Ξ)
    (predicate : Term Const Γ (signature.space ⇒ .prop)) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    subst theta (signature.childConditions predicate payload children) =
      signature.childConditions (subst theta predicate) (subst theta payload) (subst theta children) := by
  simp [childConditions, subst, subst_weaken, Subst.lift]

@[simp] theorem subst_layerBody (theta : Subst Const Γ Ξ)
    (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space)
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space)) :
    subst theta (signature.layerBody predicate point tag payload children) =
      signature.layerBody (subst theta predicate) (subst theta point) (subst theta tag)
        (subst theta payload) (subst theta children) := by
  simp [layerBody, shapeAt, subst, subst_weakenCtx]

theorem body_eq_layer (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space) :
    (signature.codeIn (Γ := Γ)).body predicate point = signature.layer predicate point := by
  simp [codeIn, RecursiveSpacePredicate.Signature.code, PositivePredicate.Code.body,
    PositivePredicate.Code.rename, PositivePredicate.Code.subst, PositivePredicate.Code.interpret,
    layer, layerBody, childConditions, slotConditions, shapeAt, activeAt, edgeAt, constructValue,
    HOL.subst, HOL.rename, subst_weaken, Subst.lift, Subst.single, Rename.lift, Rename.weaken]
  simp [weaken, rename_comp, Rename.weaken]
  simp [rename_from_empty, rename_weakenCtx]

variable {Δ : List (Formula Const Γ)}

def operator_layer (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space) :
    ProofSyntax Const Δ (.eq (.app (.app (weakenCtx Γ signature.operator) predicate) point)
      (signature.layer predicate point)) :=
  ProofSyntax.castIndices rfl
    (by rw [signature.codeIn_operator, signature.body_eq_layer])
    ((signature.codeIn (Γ := Γ)).operator_beta predicate point)

def layer_intro (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space)
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (body : ProofSyntax Const Δ (signature.layerBody predicate point tag payload children)) :
    ProofSyntax Const Δ (signature.layer predicate point) := by
  refine .exI tag (.exI payload (.exI children ?_))
  apply ProofSyntax.castIndices rfl ?_ body
  simp [instantiate, subst, subst_layerBody, subst_weaken, Subst.single, Subst.lift,
    subst_rename, subst_comp, Rename.weaken, subst_drop_shift, subst_variables]

def leastIn : Term Const Γ (signature.space ⇒ .prop) :=
  PredicateFixedPoint.least (weakenCtx Γ signature.operator)

def fold (point : Term Const Γ signature.space)
    (constructed : ProofSyntax Const Δ (signature.layer signature.leastIn point)) :
    ProofSyntax Const Δ (.app signature.leastIn point) := by
  apply PredicateFixedPoint.closure_at (weakenCtx Γ signature.operator) point
  · exact ProofSyntax.castIndices rfl (by rw [signature.codeIn_operator]) signature.codeIn.operator_monotone
  · exact .impE (.eqPropER (signature.operator_layer signature.leastIn point)) constructed

def childConditions_intro (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (edges : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (.imp (signature.activeAt (weaken payload) (.var .vz))
        (signature.edgeAt (weaken payload) (.var .vz) (.app (weaken children) (.var .vz)))))
    (members : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (.imp (signature.activeAt (weaken payload) (.var .vz))
        (.app (weaken predicate) (.app (weaken children) (.var .vz)))))
    (padding : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (.imp (.not (signature.activeAt (weaken payload) (.var .vz)))
        (.eq (.app (weaken children) (.var .vz)) (weakenCtx _ signature.bottom)))) :
    ProofSyntax Const Δ (signature.childConditions predicate payload children) :=
  .allI (.andI (.impI (.andI
    (.impE (edges.prepend _) (.hyp 0)) (.impE (members.prepend _) (.hyp 0)))) padding)

def constructor_intro (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const Δ (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const Δ (signature.childConditions signature.leastIn payload children)) :
    ProofSyntax Const Δ (.app signature.leastIn (signature.constructValue tag payload children)) :=
  signature.fold _ (signature.layer_intro _ _ tag payload children (.andI shape (.andI (.eqRefl _) childProof)))

def fixedPoint_at (point : Term Const Γ signature.space) :
    ProofSyntax Const Δ (.eq (.app signature.leastIn point)
      (.app (.app (weakenCtx Γ signature.operator) signature.leastIn) point)) := by
  have equation : ProofSyntax Const Δ (PredicateFixedPoint.equation (weakenCtx Γ signature.operator)) :=
    ProofSyntax.castIndices rfl (by rw [signature.codeIn_operator]) signature.codeIn.fixed_point
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE point equation)
  simp only [instantiate, HOL.subst,
    PredicateFixedPoint.subst_single_weaken, Subst.single, leastIn]

def unfold_member (point : Term Const Γ signature.space)
    (present : ProofSyntax Const Δ (.app signature.leastIn point)) :
    ProofSyntax Const Δ (signature.layer signature.leastIn point) :=
  .impE (.eqPropEL (signature.operator_layer signature.leastIn point))
    (.impE (.eqPropEL (signature.fixedPoint_at point)) present)

theorem operator_layer_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (point : Term Const Γ signature.space) :
    (signature.operator_layer (Δ := Δ) predicate point).FunctionExtensionalityFree := by
  simp [operator_layer, PositivePredicate.Code.operator_beta, ProofSyntax.FunctionExtensionalityFree]

theorem layer_intro_free (predicate : Term Const Γ (signature.space ⇒ .prop)) (point : Term Const Γ signature.space)
    (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (body : ProofSyntax Const Δ (signature.layerBody predicate point tag payload children))
    (free : body.FunctionExtensionalityFree) :
    (signature.layer_intro predicate point tag payload children body).FunctionExtensionalityFree := by
  simpa [layer_intro, ProofSyntax.FunctionExtensionalityFree] using free

theorem fold_free (point : Term Const Γ signature.space)
    (constructed : ProofSyntax Const Δ (signature.layer signature.leastIn point))
    (free : constructed.FunctionExtensionalityFree) :
    (signature.fold point constructed).FunctionExtensionalityFree := by
  apply PredicateFixedPoint.closure_at_free
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices] using
      (signature.codeIn (Γ := Γ)).operator_monotone_functionExtensionalityFree (assumptions := Δ)
  · exact ⟨signature.operator_layer_free signature.leastIn point, free⟩

theorem constructor_intro_free (tag : Term Const Γ signature.number) (payload : Term Const Γ signature.payload)
    (children : Term Const Γ (signature.number ⇒ signature.space))
    (shape : ProofSyntax Const Δ (signature.shapeAt tag payload))
    (childProof : ProofSyntax Const Δ (signature.childConditions signature.leastIn payload children))
    (shapeFree : shape.FunctionExtensionalityFree) (childrenFree : childProof.FunctionExtensionalityFree) :
    (signature.constructor_intro tag payload children shape childProof).FunctionExtensionalityFree := by
  apply signature.fold_free
  apply signature.layer_intro_free
  exact ⟨shapeFree, True.intro, childrenFree⟩

theorem childConditions_intro_free (predicate : Term Const Γ (signature.space ⇒ .prop))
    (payload : Term Const Γ signature.payload) (children : Term Const Γ (signature.number ⇒ signature.space))
    (edges : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (.imp (signature.activeAt (weaken payload) (.var .vz))
        (signature.edgeAt (weaken payload) (.var .vz) (.app (weaken children) (.var .vz)))))
    (members : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (.imp (signature.activeAt (weaken payload) (.var .vz))
        (.app (weaken predicate) (.app (weaken children) (.var .vz)))))
    (padding : ProofSyntax Const (weakenHyps (σ := signature.number) Δ)
      (.imp (.not (signature.activeAt (weaken payload) (.var .vz)))
        (.eq (.app (weaken children) (.var .vz)) (weakenCtx _ signature.bottom))))
    (edgesFree : edges.FunctionExtensionalityFree) (membersFree : members.FunctionExtensionalityFree)
    (paddingFree : padding.FunctionExtensionalityFree) :
    (signature.childConditions_intro predicate payload children edges members padding).FunctionExtensionalityFree := by
  simp [childConditions_intro, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
    edgesFree, membersFree, paddingFree]

theorem fixedPoint_at_free (point : Term Const Γ signature.space) :
    (signature.fixedPoint_at (Δ := Δ) point).FunctionExtensionalityFree := by
  simp [fixedPoint_at, ProofSyntax.FunctionExtensionalityFree,
    PositivePredicate.Code.fixed_point_functionExtensionalityFree]

theorem unfold_member_free (point : Term Const Γ signature.space)
    (present : ProofSyntax Const Δ (.app signature.leastIn point)) (free : present.FunctionExtensionalityFree) :
    (signature.unfold_member point present).FunctionExtensionalityFree := by
  exact ⟨signature.operator_layer_free signature.leastIn point, signature.fixedPoint_at_free point, free⟩

#print axioms operator_layer
#print axioms constructor_intro
#print axioms constructor_intro_free
#print axioms unfold_member_free
end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Signature
