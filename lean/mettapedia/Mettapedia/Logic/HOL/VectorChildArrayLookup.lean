import Mettapedia.Logic.HOL.VectorChildArrays
import Mettapedia.Logic.HOL.IndexedVectorPositions

/-!
# The constructed child array agrees with least vector lookup

Lookup elimination proves the array equation for an arbitrary suffix, index,
vector, position and element. The six primitive premises retain the two
distinct selection/recursion instances and the original constructor projections.
No vector inversion, constructor injectivity or Peano separation is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

namespace Operations
variable (ops : Operations Const) {Γ Ξ : Ctx Base}

def headBody : ArgumentBody Const Γ (IndexedVectorPositions.HeadFields ops.toSignature) := fun _ fields =>
  .eq (.app (weakenCtx _ ops.head) (ops.toSignature.consValue fields.1 fields.2.1 fields.2.2.1)) fields.2.1

def tailBody : ArgumentBody Const Γ (IndexedVectorPositions.HeadFields ops.toSignature) := fun _ fields =>
  .eq (.app (weakenCtx _ ops.tail) (ops.toSignature.consValue fields.1 fields.2.1 fields.2.2.1)) fields.2.2.1

theorem headBody_natural : NaturalBody (ops.headBody (Γ := Γ)) := by
  intro Δ Ω earlier later fields
  simp only [headBody, HOL.subst, subst_weakenCtx, IndexedVectorPredicate.Signature.subst_consValue, substituteArguments]

theorem tailBody_natural : NaturalBody (ops.tailBody (Γ := Γ)) := by
  intro Δ Ω earlier later fields
  simp only [tailBody, HOL.subst, subst_weakenCtx, IndexedVectorPredicate.Signature.subst_consValue, substituteArguments]

def headLaw : Formula Const Γ := forallArguments _ ops.headBody
def tailLaw : Formula Const Γ := forallArguments _ ops.tailBody

@[simp] theorem headLaw_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (ops.headLaw (Γ := Γ)) = ops.headLaw (Γ := Ξ) := by
  unfold headLaw
  rw [forallArguments_subst _ _ _ ops.headBody_natural]
  rfl

@[simp] theorem tailLaw_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (ops.tailLaw (Γ := Γ)) = ops.tailLaw (Γ := Ξ) := by
  unfold tailLaw
  rw [forallArguments_subst _ _ _ ops.tailBody_natural]
  rfl

def selectionLaw (type : Ty Base) (selection : ClosedTerm Const (SelectionProofs.Selection type)) : Formula Const Γ :=
  SelectionProofs.principle (weakenCtx Γ selection)

@[simp] theorem selectionLaw_subst (images : Subst Const Γ Ξ)
    (type : Ty Base) (selection : ClosedTerm Const (SelectionProofs.Selection type)) :
    HOL.subst images (selectionLaw (Γ := Γ) type selection) = selectionLaw (Γ := Ξ) type selection := by
  simp [selectionLaw, SelectionProofs.principle, SelectionProofs.instanceFormula,
    HOL.subst, subst_weaken, subst_weakenCtx, Subst.lift]

def recursionLaw (result : Ty Base) : Formula Const Γ :=
  NaturalRecursionProofs.statement (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor) result

@[simp] theorem recursionLaw_subst (images : Subst Const Γ Ξ) (result : Ty Base) :
    HOL.subst images (ops.recursionLaw (Γ := Γ) result) = ops.recursionLaw (Γ := Ξ) result := by
  simp [recursionLaw, NaturalRecursionProofs.statement, NaturalRecursionProofs.subst_body,
    HOL.subst, subst_weaken, subst_weakenCtx, Subst.lift, Rename.weaken]

def assumptions (Γ : Ctx Base) : List (Formula Const Γ) :=
  [selectionLaw _ ops.elementSelection, ops.recursionLaw ops.element,
    selectionLaw _ ops.arraySelection, ops.recursionLaw (ops.vector ⇒ ops.ArrayType), ops.headLaw, ops.tailLaw]

theorem assumptions_subst (images : Subst Const Γ Ξ) :
    (ops.assumptions Γ).map (HOL.subst images) = ops.assumptions Ξ := by
  simp only [assumptions, List.map_cons, List.map_nil, selectionLaw_subst, recursionLaw_subst, headLaw_subst, tailLaw_subst]

variable {Δ : List (Formula Const Γ)}

def headAt (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (law : ProofSyntax Const Δ ops.headLaw) :
    ProofSyntax Const Δ (.eq (.app (weakenCtx Γ ops.head) (ops.toSignature.consValue index head tail)) head) :=
  forallArguments_elim _ _ ops.headBody_natural (index,head,tail,PUnit.unit) law

def tailAt (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (law : ProofSyntax Const Δ ops.tailLaw) :
    ProofSyntax Const Δ (.eq (.app (weakenCtx Γ ops.tail) (ops.toSignature.consValue index head tail)) tail) :=
  forallArguments_elim _ _ ops.tailBody_natural (index,head,tail,PUnit.unit) law

theorem headAt_free (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (law : ProofSyntax Const Δ ops.headLaw) (free : law.FunctionExtensionalityFree) :
    (ops.headAt index head tail law).FunctionExtensionalityFree := forallArguments_elim_free _ _ _ _ law free

theorem tailAt_free (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (law : ProofSyntax Const Δ ops.tailLaw) (free : law.FunctionExtensionalityFree) :
    (ops.tailAt index head tail law).FunctionExtensionalityFree := forallArguments_elim_free _ _ _ _ law free

structure ComputationPremises (assumptions : List (Formula Const Γ)) where
  elementChoice : ProofSyntax Const assumptions (selectionLaw _ ops.elementSelection)
  elementRecursion : ProofSyntax Const assumptions (ops.recursionLaw ops.element)
  arrayChoice : ProofSyntax Const assumptions (selectionLaw _ ops.arraySelection)
  arrayRecursion : ProofSyntax Const assumptions (ops.recursionLaw (ops.vector ⇒ ops.ArrayType))
  head : ProofSyntax Const assumptions ops.headLaw
  tail : ProofSyntax Const assumptions ops.tailLaw

namespace ComputationPremises
variable {ops}

def subst (premises : ops.ComputationPremises Δ) (images : Subst Const Γ Ξ) :
    ops.ComputationPremises (Δ.map (HOL.subst images)) where
  elementChoice := ProofSyntax.castIndices rfl (selectionLaw_subst images _ _) (premises.elementChoice.subst images)
  elementRecursion := ProofSyntax.castIndices rfl (ops.recursionLaw_subst images _) (premises.elementRecursion.subst images)
  arrayChoice := ProofSyntax.castIndices rfl (selectionLaw_subst images _ _) (premises.arrayChoice.subst images)
  arrayRecursion := ProofSyntax.castIndices rfl (ops.recursionLaw_subst images _) (premises.arrayRecursion.subst images)
  head := ProofSyntax.castIndices rfl (ops.headLaw_subst images) (premises.head.subst images)
  tail := ProofSyntax.castIndices rfl (ops.tailLaw_subst images) (premises.tail.subst images)

def prepend (premises : ops.ComputationPremises Δ) (formula : Formula Const Γ) :
    ops.ComputationPremises (formula :: Δ) where
  elementChoice := premises.elementChoice.prepend formula
  elementRecursion := premises.elementRecursion.prepend formula
  arrayChoice := premises.arrayChoice.prepend formula
  arrayRecursion := premises.arrayRecursion.prepend formula
  head := premises.head.prepend formula
  tail := premises.tail.prepend formula

def FunctionExtensionalityFree (premises : ops.ComputationPremises Δ) : Prop :=
  premises.elementChoice.FunctionExtensionalityFree ∧ premises.elementRecursion.FunctionExtensionalityFree ∧
    premises.arrayChoice.FunctionExtensionalityFree ∧ premises.arrayRecursion.FunctionExtensionalityFree ∧
    premises.head.FunctionExtensionalityFree ∧ premises.tail.FunctionExtensionalityFree

theorem subst_free (premises : ops.ComputationPremises Δ) (images : Subst Const Γ Ξ)
    (free : premises.FunctionExtensionalityFree) : (premises.subst images).FunctionExtensionalityFree := by
  simpa only [FunctionExtensionalityFree, subst, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_subst] using free

theorem prepend_free (premises : ops.ComputationPremises Δ) (formula : Formula Const Γ)
    (free : premises.FunctionExtensionalityFree) : (premises.prepend formula).FunctionExtensionalityFree := by
  simpa only [FunctionExtensionalityFree, prepend, ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using free
end ComputationPremises

def assumptionPremises : ops.ComputationPremises (ops.assumptions Γ) where
  elementChoice := .hyp ⟨0, by change 0 < 6; decide⟩
  elementRecursion := .hyp ⟨1, by change 1 < 6; decide⟩
  arrayChoice := .hyp ⟨2, by change 2 < 6; decide⟩
  arrayRecursion := .hyp ⟨3, by change 3 < 6; decide⟩
  head := .hyp ⟨4, by change 4 < 6; decide⟩
  tail := .hyp ⟨5, by change 5 < 6; decide⟩

theorem assumptionPremises_free : (ops.assumptionPremises (Γ := Γ)).FunctionExtensionalityFree := by
  exact ⟨trivial,trivial,trivial,trivial,trivial,trivial⟩

def lookupBody (rest : Term Const Γ ops.ArrayType) :
    ArgumentBody Const Γ (IndexedVectorPositions.Fields ops.toSignature) := fun images fields =>
  .eq (.app (ops.suffix fields.1 fields.2.1 (HOL.subst images rest)) fields.2.2.1) fields.2.2.2.1

theorem lookupBody_natural (rest : Term Const Γ ops.ArrayType) : NaturalBody (ops.lookupBody rest) := by
  intro Δ Ω earlier later fields
  simp only [lookupBody, HOL.subst, suffix_subst, HOL.subst_comp, substituteArguments]
  rfl

def lookupRelation (rest : Term Const Γ ops.ArrayType) :
    Term Const Γ (IndexedVectorPositions.Relation ops.toSignature) :=
  abstractArguments (IndexedVectorPositions.Fields ops.toSignature) (ops.lookupBody rest)

@[simp] theorem lookupRelation_subst (images : Subst Const Γ Ξ) (rest : Term Const Γ ops.ArrayType) :
    HOL.subst images (ops.lookupRelation rest) = ops.lookupRelation (HOL.subst images rest) := by
  unfold lookupRelation
  rw [abstractArguments_subst _ _ _ (ops.lookupBody_natural rest)]
  apply congrArg (abstractArguments (IndexedVectorPositions.Fields ops.toSignature))
  funext laterContext later fields
  simp only [lookupBody, HOL.subst_comp]
  rfl

def lookupRelation_apply (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (position : Term Const Γ ops.number) (element : Term Const Γ ops.element) :
    ProofSyntax Const Δ (.eq (IndexedVectorPositions.holds ops.toSignature (ops.lookupRelation rest)
      index vector position element) (.eq (.app (ops.suffix index vector rest) position) element)) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractArguments_beta _ _ (ops.lookupBody_natural rest) (index,vector,position,element,PUnit.unit))
  have identityTerm : HOL.subst (fun entry => Term.var entry) rest = rest :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) rest
  simp only [lookupBody, identityTerm]
  rfl

theorem lookupRelation_apply_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (position : Term Const Γ ops.number) (element : Term Const Γ ops.element) :
    (ops.lookupRelation_apply (Δ := Δ) rest index vector position element).FunctionExtensionalityFree := by
  unfold lookupRelation_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

def lookupHead (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector) (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (IndexedVectorPositions.holds ops.toSignature (ops.lookupRelation rest)
      (.app (weakenCtx Γ ops.successor) index) (ops.toSignature.consValue index head tail) (weakenCtx Γ ops.zero) head) :=
  .impE (.eqPropER (ops.lookupRelation_apply rest _ _ _ _))
    (.eqTrans (.eqApp (weakenCtx Γ ops.zero) (ops.suffix_cons index head tail rest premises.arrayChoice premises.arrayRecursion
      (ops.headAt index head tail premises.head) (ops.tailAt index head tail premises.tail)))
      (ops.prepend_zero head (ops.suffix index tail rest) premises.elementChoice premises.elementRecursion))

theorem lookupHead_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector) (premises : ops.ComputationPremises Δ)
    (free : premises.FunctionExtensionalityFree) : (ops.lookupHead rest index head tail premises).FunctionExtensionalityFree := by
  unfold lookupHead
  exact ⟨ops.lookupRelation_apply_free _ _ _ _ _,
    ⟨ops.suffix_cons_free _ _ _ _ _ _ _ _ free.2.2.1 free.2.2.2.1
      (ops.headAt_free _ _ _ _ free.2.2.2.2.1) (ops.tailAt_free _ _ _ _ free.2.2.2.2.2),
      ops.prepend_zero_free _ _ _ _ free.1 free.2.1⟩⟩

def lookupTail (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (position : Term Const Γ ops.number) (element : Term Const Γ ops.element) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (IndexedVectorPositions.holds ops.toSignature (ops.lookupRelation rest) index tail position element)) :
    ProofSyntax Const Δ (IndexedVectorPositions.holds ops.toSignature (ops.lookupRelation rest)
      (.app (weakenCtx Γ ops.successor) index) (ops.toSignature.consValue index head tail)
      (.app (weakenCtx Γ ops.successor) position) element) :=
  .impE (.eqPropER (ops.lookupRelation_apply rest _ _ _ _))
    (.eqTrans (.eqApp (.app (weakenCtx Γ ops.successor) position)
      (ops.suffix_cons index head tail rest premises.arrayChoice premises.arrayRecursion
        (ops.headAt index head tail premises.head) (ops.tailAt index head tail premises.tail)))
      (.eqTrans (ops.prepend_successor head (ops.suffix index tail rest) position premises.elementChoice premises.elementRecursion)
        (.impE (.eqPropEL (ops.lookupRelation_apply rest index tail position element)) previous)))

theorem lookupTail_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (position : Term Const Γ ops.number) (element : Term Const Γ ops.element) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (IndexedVectorPositions.holds ops.toSignature (ops.lookupRelation rest) index tail position element))
    (free : premises.FunctionExtensionalityFree) (previousFree : previous.FunctionExtensionalityFree) :
    (ops.lookupTail rest index head tail position element premises previous).FunctionExtensionalityFree := by
  unfold lookupTail
  exact ⟨ops.lookupRelation_apply_free _ _ _ _ _,
    ⟨ops.suffix_cons_free _ _ _ _ _ _ _ _ free.2.2.1 free.2.2.2.1
      (ops.headAt_free _ _ _ _ free.2.2.2.2.1) (ops.tailAt_free _ _ _ _ free.2.2.2.2.2),
      ⟨ops.prepend_successor_free _ _ _ _ _ free.1 free.2.1,
        ⟨ops.lookupRelation_apply_free _ _ _ _ _,previousFree⟩⟩⟩⟩

def lookupHeadBranch (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ) :
    ArgumentProof Δ (IndexedVectorPositions.HeadFields ops.toSignature)
      (IndexedVectorPositions.headBody ops.toSignature (ops.lookupRelation rest)) := by
  intro Ξ images fields
  apply ProofSyntax.castIndices rfl ?_
    (ops.lookupHead (HOL.subst images rest) fields.1 fields.2.1 fields.2.2.1 (premises.subst images))
  simp only [IndexedVectorPositions.headBody, lookupRelation_subst]

def lookupTailBranch (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ) :
    ArgumentProof Δ (IndexedVectorPositions.TailFields ops.toSignature)
      (IndexedVectorPositions.tailBody ops.toSignature (ops.lookupRelation rest)) := by
  intro Ξ images fields
  apply ProofSyntax.castIndices rfl ?_
    (.impI (ops.lookupTail (HOL.subst images rest) fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1 fields.2.2.2.2.1
      ((premises.subst images).prepend _) (.hyp 0)))
  simp only [IndexedVectorPositions.tailBody, lookupRelation_subst]
  rfl

theorem lookupHeadBranch_free (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ)
    (free : premises.FunctionExtensionalityFree) (images : Subst Const Γ Ξ) fields :
    (ops.lookupHeadBranch rest premises images fields).FunctionExtensionalityFree := by
  unfold lookupHeadBranch
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ops.lookupHead_free _ _ _ _ _ (premises.subst_free images free)

theorem lookupTailBranch_free (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ)
    (free : premises.FunctionExtensionalityFree) (images : Subst Const Γ Ξ) fields :
    (ops.lookupTailBranch rest premises images fields).FunctionExtensionalityFree := by
  unfold lookupTailBranch
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ops.lookupTail_free _ _ _ _ _ _ _ _
    ((premises.subst images).prepend_free _ (premises.subst_free images free)) trivial

def lookupRules (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (IndexedVectorPositions.closed ops.toSignature (ops.lookupRelation rest)) :=
  .andI (forallArguments_intro _ _ (ops.lookupHeadBranch rest premises))
    (forallArguments_intro _ _ (ops.lookupTailBranch rest premises))

theorem lookupRules_free (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ)
    (free : premises.FunctionExtensionalityFree) : (ops.lookupRules rest premises).FunctionExtensionalityFree :=
  ⟨forallArguments_intro_free _ _ _ (ops.lookupHeadBranch_free rest premises free),
    forallArguments_intro_free _ _ _ (ops.lookupTailBranch_free rest premises free)⟩

def valueAtLookup (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (position : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature index vector position element)) :
    ProofSyntax Const Δ (.eq (.app (ops.suffix index vector rest) position) element) :=
  .impE (.eqPropEL (ops.lookupRelation_apply rest index vector position element))
    (IndexedVectorPositions.eliminate ops.toSignature (ops.lookupRelation rest) index vector position element
      present (ops.lookupRules rest premises))

theorem valueAtLookup_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (position : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature index vector position element))
    (free : premises.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (ops.valueAtLookup rest index vector position element premises present).FunctionExtensionalityFree :=
  ⟨ops.lookupRelation_apply_free _ _ _ _ _, IndexedVectorPositions.eliminate_free _ _ _ _ _ _ present _
    presentFree (ops.lookupRules_free rest premises free)⟩

def mixedAtLookup (index : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature index vector position element)) :
    ProofSyntax Const Δ (.eq (.app (ops.mixed index before vector after bottom)
      (.app (weakenCtx Γ ops.successor) position)) element) :=
  .eqTrans (ops.prepend_successor before (ops.suffix index vector (ops.prepend after (ops.padding bottom)))
    position premises.elementChoice premises.elementRecursion)
    (ops.valueAtLookup (ops.prepend after (ops.padding bottom)) index vector position element premises present)

theorem mixedAtLookup_free (index : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature index vector position element))
    (free : premises.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (ops.mixedAtLookup index before vector after bottom position element premises present).FunctionExtensionalityFree :=
  ⟨ops.prepend_successor_free _ _ _ _ _ free.1 free.2.1,
    ops.valueAtLookup_free _ _ _ _ _ premises present free presentFree⟩

#print axioms valueAtLookup_free
#print axioms mixedAtLookup_free
end Operations
end Mettapedia.Logic.HOL.VectorChildArrays
