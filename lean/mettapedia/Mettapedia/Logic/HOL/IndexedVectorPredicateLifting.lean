import Mettapedia.Logic.HOL.IndexedVectorPositions

/-!
# Position-dependent transport of vector membership

The induction motive retains the per-position implication for the current
index and vector. A cons step obtains the head implication at zero and moves
the tail implications through successor positions. No arithmetic, recursor,
selection or projection law is a premise of this membership transport.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPredicateLifting
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}

abbrev PointFields := [signature.number, signature.element]

def pointBody (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    ArgumentBody Const Γ (PointFields signature) := fun images fields =>
  .imp (IndexedVectorPositions.lookup signature (HOL.subst images index) (HOL.subst images vector)
    fields.1 fields.2.1)
    (.imp (.app (HOL.subst images source) fields.2.1) (.app (HOL.subst images target) fields.2.1))

theorem pointBody_natural (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    NaturalBody (pointBody signature source target index vector) := by
  intro Δ Ω earlier later fields
  simp only [pointBody, HOL.subst, IndexedVectorPositions.lookup_subst, HOL.subst_comp, substituteArguments]
  rfl

def condition (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) : Formula Const Γ :=
  forallArguments (PointFields signature) (pointBody signature source target index vector)

@[simp] theorem condition_subst (images : Subst Const Γ Ξ)
    (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    HOL.subst images (condition signature source target index vector) =
      condition signature (HOL.subst images source) (HOL.subst images target)
        (HOL.subst images index) (HOL.subst images vector) := by
  unfold condition
  rw [forallArguments_subst _ _ _ (pointBody_natural signature source target index vector)]
  apply congrArg (forallArguments (PointFields signature))
  funext laterContext later fields
  simp only [pointBody, HOL.subst_comp]
  rfl

@[simp] theorem condition_rename (rho : Rename Base Γ Ξ)
    (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    HOL.rename rho (condition signature source target index vector) =
      condition signature (HOL.rename rho source) (HOL.rename rho target)
        (HOL.rename rho index) (HOL.rename rho vector) := by
  simpa only [subst_ofRename] using condition_subst signature (Subst.ofRename rho) source target index vector

def motiveBody (source target : Term Const Γ (signature.element ⇒ .prop)) :
    ArgumentBody Const Γ [signature.number, signature.vector] := fun images fields =>
  .imp (condition signature (HOL.subst images source) (HOL.subst images target) fields.1 fields.2.1)
    (signature.member (HOL.subst images target) fields.1 fields.2.1)

theorem motiveBody_natural (source target : Term Const Γ (signature.element ⇒ .prop)) :
    NaturalBody (motiveBody signature source target) := by
  intro Δ Ω earlier later fields
  simp only [motiveBody, HOL.subst, condition_subst, IndexedVectorPredicate.Signature.subst_member,
    HOL.subst_comp, substituteArguments]
  rfl

def motive (source target : Term Const Γ (signature.element ⇒ .prop)) : Term Const Γ signature.Property :=
  abstractArguments [signature.number, signature.vector] (motiveBody signature source target)

@[simp] theorem motive_subst (images : Subst Const Γ Ξ)
    (source target : Term Const Γ (signature.element ⇒ .prop)) :
    HOL.subst images (motive signature source target) =
      motive signature (HOL.subst images source) (HOL.subst images target) := by
  unfold motive
  rw [abstractArguments_subst _ _ _ (motiveBody_natural signature source target)]
  apply congrArg (abstractArguments [signature.number, signature.vector])
  funext laterContext later fields
  simp only [motiveBody, HOL.subst_comp]
  rfl

@[simp] theorem motive_rename (rho : Rename Base Γ Ξ)
    (source target : Term Const Γ (signature.element ⇒ .prop)) :
    HOL.rename rho (motive signature source target) =
      motive signature (HOL.rename rho source) (HOL.rename rho target) := by
  simpa only [subst_ofRename] using motive_subst signature (Subst.ofRename rho) source target

variable {Δ : List (Formula Const Γ)}

def atPosition (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (given : ProofSyntax Const Δ (condition signature source target index vector)) :
    ProofSyntax Const Δ (.imp (IndexedVectorPositions.lookup signature index vector position element)
      (.imp (.app source element) (.app target element))) := by
  apply ProofSyntax.castIndices rfl ?_
    (forallArguments_elim _ _ (pointBody_natural signature source target index vector) (position, element, PUnit.unit) given)
  simp only [pointBody, HOL.subst_id]

theorem atPosition_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (given : ProofSyntax Const Δ (condition signature source target index vector))
    (free : given.FunctionExtensionalityFree) :
    (atPosition signature source target index vector position element given).FunctionExtensionalityFree := by
  unfold atPosition
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_elim_free _ _ _ _ given free

def motive_apply (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    ProofSyntax Const Δ (.eq (PredicatePair.holds (motive signature source target) index vector)
      (.imp (condition signature source target index vector) (signature.member target index vector))) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractArguments_beta _ _ (motiveBody_natural signature source target) (index, vector, PUnit.unit))
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun entry => Term.var entry) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [motiveBody, identityTerm]
  rfl

theorem motive_apply_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    (motive_apply (Δ := Δ) signature source target index vector).FunctionExtensionalityFree := by
  unfold motive_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

def tailPoint (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element)
    (given : ProofSyntax Const Δ (condition signature source target (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail)))
    (found : ProofSyntax Const Δ (IndexedVectorPositions.lookup signature index tail position element))
    (member : ProofSyntax Const Δ (.app source element)) : ProofSyntax Const Δ (.app target element) :=
  .impE (.impE (atPosition signature source target (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail) (.app (weakenCtx Γ signature.successor) position) element given)
    (IndexedVectorPositions.there signature index head tail position element found)) member

theorem tailPoint_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element)
    (given : ProofSyntax Const Δ (condition signature source target (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail)))
    (found : ProofSyntax Const Δ (IndexedVectorPositions.lookup signature index tail position element))
    (member : ProofSyntax Const Δ (.app source element))
    (givenFree : given.FunctionExtensionalityFree) (foundFree : found.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (tailPoint signature source target index head tail position element given found member).FunctionExtensionalityFree :=
  ⟨⟨atPosition_free signature _ _ _ _ _ _ given givenFree,
    IndexedVectorPositions.there_free signature index head tail position element found foundFree⟩, memberFree⟩

def tailConditionBranch (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector)
    (given : ProofSyntax Const Δ (condition signature source target (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail))) :
    ArgumentProof Δ (PointFields signature) (pointBody signature source target index tail) := by
  intro Ξ images fields
  let a := HOL.subst images source
  let b := HOL.subst images target
  let n := HOL.subst images index
  let h := HOL.subst images head
  let t := HOL.subst images tail
  let found := IndexedVectorPositions.lookup signature n t fields.1 fields.2.1
  let member := Term.app a fields.2.1
  have mapped : ProofSyntax Const (Δ.map (HOL.subst images))
      (condition signature a b (.app (weakenCtx Ξ signature.successor) n) (signature.consValue n h t)) := by
    apply ProofSyntax.castIndices rfl ?_ (given.subst images)
    simp only [condition_subst, HOL.subst, subst_weakenCtx, IndexedVectorPredicate.Signature.subst_consValue, a, b, n, h, t]
  exact .impI (.impI (tailPoint signature a b n h t fields.1 fields.2.1
    ((mapped.prepend found).prepend member) (.hyp 1) (.hyp 0)))

theorem tailConditionBranch_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector)
    (given : ProofSyntax Const Δ (condition signature source target (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail))) (free : given.FunctionExtensionalityFree)
    (images : Subst Const Γ Ξ) (fields : Arguments Const Ξ (PointFields signature)) :
    (tailConditionBranch signature source target index head tail given images fields).FunctionExtensionalityFree := by
  unfold tailConditionBranch
  apply tailPoint_free
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst] using free
  · trivial
  · trivial

def tailCondition (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector)
    (given : ProofSyntax Const Δ (condition signature source target (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail))) :
    ProofSyntax Const Δ (condition signature source target index tail) :=
  forallArguments_intro _ _ (tailConditionBranch signature source target index head tail given)

theorem tailCondition_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector)
    (given : ProofSyntax Const Δ (condition signature source target (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail))) (free : given.FunctionExtensionalityFree) :
    (tailCondition signature source target index head tail given).FunctionExtensionalityFree :=
  forallArguments_intro_free _ _ _ (tailConditionBranch_free signature source target index head tail given free)

def base (source target : Term Const Γ (signature.element ⇒ .prop)) :
    ProofSyntax Const Δ (PredicatePair.holds (motive signature source target)
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)) :=
  .impE (.eqPropER (motive_apply signature source target (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)))
    (.impI (signature.nil_member target))

theorem base_free (source target : Term Const Γ (signature.element ⇒ .prop)) :
    (base (Δ := Δ) signature source target).FunctionExtensionalityFree :=
  ⟨motive_apply_free signature source target _ _, signature.nil_member_free target⟩

def step_point (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) :
    ProofSyntax Const Δ (signature.stepBody source (motive signature source target) index head tail) := by
  let a := Term.app source head
  let b := signature.member source index tail
  let c := PredicatePair.holds (motive signature source target) index tail
  let parent := condition signature source target (.app (weakenCtx Γ signature.successor) index)
    (signature.consValue index head tail)
  refine .impI (.impI (.impI ?_))
  apply ProofSyntax.impE (.eqPropER (motive_apply signature source target
    (.app (weakenCtx Γ signature.successor) index) (signature.consValue index head tail)))
  refine .impI ?_
  let assumptions := parent :: c :: b :: a :: Δ
  have supplied : ProofSyntax Const assumptions parent := .hyp ⟨0, by simp [assumptions]⟩
  have headTarget : ProofSyntax Const assumptions (.app target head) :=
    .impE (.impE (atPosition signature source target (.app (weakenCtx Γ signature.successor) index)
        (signature.consValue index head tail) (weakenCtx Γ signature.zero) head supplied)
      (IndexedVectorPositions.here signature index head tail)) (.hyp ⟨3, by simp [assumptions]⟩)
  have tailTarget : ProofSyntax Const assumptions (signature.member target index tail) :=
    .impE (.impE (.eqPropEL (motive_apply signature source target index tail))
      (.hyp ⟨1, by simp [assumptions]⟩)) (tailCondition signature source target index head tail supplied)
  exact signature.cons_member target index head tail headTarget tailTarget

theorem step_point_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) :
    (step_point (Δ := Δ) signature source target index head tail).FunctionExtensionalityFree := by
  unfold step_point
  refine ⟨motive_apply_free signature source target _ _, ?_⟩
  apply signature.cons_member_free
  · exact ⟨⟨atPosition_free signature _ _ _ _ _ _ _ True.intro,
      IndexedVectorPositions.here_free signature index head tail⟩, True.intro⟩
  · exact ⟨⟨motive_apply_free signature source target index tail, True.intro⟩,
      tailCondition_free signature source target index head tail _ True.intro⟩

def step_condition (source target : Term Const Γ (signature.element ⇒ .prop)) :
    ProofSyntax Const Δ (signature.stepCondition source (motive signature source target)) := by
  refine .allI (.allI (.allI ?_))
  let a := weaken (σ := signature.vector) (weaken (σ := signature.element) (weaken (σ := signature.number) source))
  let b := weaken (σ := signature.vector) (weaken (σ := signature.element) (weaken (σ := signature.number) target))
  apply ProofSyntax.castIndices rfl ?_
    (step_point signature a b (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
  simp only [a, b, weaken, motive_rename]

theorem step_condition_free (source target : Term Const Γ (signature.element ⇒ .prop)) :
    (step_condition (Δ := Δ) signature source target).FunctionExtensionalityFree := by
  unfold step_condition
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact step_point_free signature _ _ _ _ _

def relationalLift (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (signature.member source index vector))
    (given : ProofSyntax Const Δ (condition signature source target index vector)) :
    ProofSyntax Const Δ (signature.member target index vector) :=
  .impE (.impE (.eqPropEL (motive_apply signature source target index vector))
    (signature.inductionProof source (motive signature source target) index vector
      (base signature source target) (step_condition signature source target) member)) given

theorem relationalLift_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (signature.member source index vector))
    (given : ProofSyntax Const Δ (condition signature source target index vector))
    (memberFree : member.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree) :
    (relationalLift signature source target index vector member given).FunctionExtensionalityFree :=
  ⟨⟨motive_apply_free signature source target index vector,
    signature.inductionProof_free source (motive signature source target) index vector
      (base signature source target) (step_condition signature source target) member
      (base_free signature source target) (step_condition_free signature source target) memberFree⟩, givenFree⟩

#print axioms relationalLift
#print axioms relationalLift_free
end Mettapedia.Logic.HOL.IndexedVectorPredicateLifting
