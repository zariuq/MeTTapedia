import Mettapedia.Logic.HOL.VectorTabulationLookup
import Mettapedia.Logic.HOL.VectorChildArraySingleSegment

/-!
# Pointwise reconstruction of a canonically padded source array

The vector is produced by the actual selected tabulator. Active lookup names
the original array element; all inactive positions compute the supplied
bottom value. Canonical padding of the original array then yields pointwise
equality. This is not whole-function equality or transport of an arbitrary
parent motive across a changed child function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorTabulation.Shifted
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
  (ops : VectorChildArrays.Operations Const) {Γ Ξ : Ctx Base}
  (selection : ClosedTerm Const (Selection ops.toSignature))

def choiceLaw : Formula Const Γ := SelectionProofs.principle (weakenCtx Γ selection)
def recursionLaw : Formula Const Γ := NaturalRecursionProofs.statement
  (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor) (Result ops.toSignature)

@[simp] theorem choiceLaw_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (choiceLaw (Γ := Γ) ops selection) = choiceLaw (Γ := Ξ) ops selection := by
  simp only [choiceLaw,SelectionProofs.principle,HOL.subst,SelectionProofs.subst_instanceFormula,
    subst_weaken,subst_weakenCtx,Subst.lift]

@[simp] theorem recursionLaw_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (recursionLaw (Γ := Γ) ops) = recursionLaw (Γ := Ξ) ops := by
  simp only [recursionLaw,NaturalRecursionProofs.statement,HOL.subst,NaturalRecursionProofs.subst_body,
    subst_weaken,subst_weakenCtx,Subst.lift]
  rfl

structure ComputationPremises (hypotheses : List (Formula Const Γ)) where
  choice : ProofSyntax Const hypotheses (choiceLaw ops selection)
  recursion : ProofSyntax Const hypotheses (recursionLaw ops)

namespace ComputationPremises
variable {ops selection} {Δ : List (Formula Const Γ)}

def subst (premises : ComputationPremises ops selection Δ) (images : Subst Const Γ Ξ) :
    ComputationPremises ops selection (Δ.map (HOL.subst images)) where
  choice := .castIndices rfl (choiceLaw_subst ops selection images) (premises.choice.subst images)
  recursion := .castIndices rfl (recursionLaw_subst ops images) (premises.recursion.subst images)

def weaken (premises : ComputationPremises ops selection Δ) (type : Ty Base) :
    ComputationPremises ops selection (weakenHyps (σ := type) Δ) where
  choice := .castIndices rfl (by
    simpa only [subst_ofRename] using
      choiceLaw_subst ops selection (Subst.ofRename (Rename.weaken (Γ := Γ) (σ := type))))
    (premises.choice.rename Rename.weaken)
  recursion := .castIndices rfl (by
    simpa only [subst_ofRename] using
      recursionLaw_subst ops (Subst.ofRename (Rename.weaken (Γ := Γ) (σ := type))))
    (premises.recursion.rename Rename.weaken)

def prepend (premises : ComputationPremises ops selection Δ) (formula : Formula Const Γ) :
    ComputationPremises ops selection (formula :: Δ) :=
  ⟨premises.choice.prepend formula,premises.recursion.prepend formula⟩

def Free (premises : ComputationPremises ops selection Δ) : Prop :=
  premises.choice.FunctionExtensionalityFree ∧ premises.recursion.FunctionExtensionalityFree

theorem subst_free (premises : ComputationPremises ops selection Δ) (images : Subst Const Γ Ξ)
    (free : premises.Free) : (premises.subst images).Free := by
  simpa only [Free,subst,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_subst] using free

theorem weaken_free (premises : ComputationPremises ops selection Δ) (type : Ty Base)
    (free : premises.Free) : (premises.weaken type).Free := by
  simpa only [Free,weaken,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

theorem prepend_free (premises : ComputationPremises ops selection Δ) (formula : Formula Const Γ)
    (free : premises.Free) : (premises.prepend formula).Free := by
  simpa only [Free,prepend,ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using free
end ComputationPremises

def rebuilt (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) : Term Const Γ ops.ArrayType :=
  ops.single length (tabulate ops.toSignature selection length array) bottom

@[simp] theorem rebuilt_subst (images : Subst Const Γ Ξ) (length : Term Const Γ ops.number)
    (array : Term Const Γ ops.ArrayType) (bottom : Term Const Γ ops.element) :
    HOL.subst images (rebuilt ops selection length array bottom) =
      rebuilt ops selection (HOL.subst images length) (HOL.subst images array) (HOL.subst images bottom) := by
  simp only [rebuilt,ops.single_subst,tabulate_subst]

theorem rebuilt_rename (rho : Rename Base Γ Ξ) (length : Term Const Γ ops.number)
    (array : Term Const Γ ops.ArrayType) (bottom : Term Const Γ ops.element) :
    HOL.rename rho (rebuilt ops selection length array bottom) =
      rebuilt ops selection (HOL.rename rho length) (HOL.rename rho array) (HOL.rename rho bottom) := by
  simpa only [subst_ofRename] using rebuilt_subst ops selection (Subst.ofRename rho) length array bottom

def paddingCondition (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) : Formula Const Γ :=
  .all (.imp (.not (.app (.app (weakenCtx _ (SuccessorOrder.less ops.successor)) (.var .vz)) (weaken length)))
    (.eq (.app (weaken array) (.var .vz)) (weaken bottom)))

@[simp] theorem paddingCondition_subst (images : Subst Const Γ Ξ) (length : Term Const Γ ops.number)
    (array : Term Const Γ ops.ArrayType) (bottom : Term Const Γ ops.element) :
    HOL.subst images (paddingCondition ops length array bottom) =
      paddingCondition ops (HOL.subst images length) (HOL.subst images array) (HOL.subst images bottom) := by
  simp only [paddingCondition,HOL.subst,subst_weaken,subst_weakenCtx,Subst.lift]

theorem paddingCondition_rename (rho : Rename Base Γ Ξ) (length : Term Const Γ ops.number)
    (array : Term Const Γ ops.ArrayType) (bottom : Term Const Γ ops.element) :
    HOL.rename rho (paddingCondition ops length array bottom) =
      paddingCondition ops (HOL.rename rho length) (HOL.rename rho array) (HOL.rename rho bottom) := by
  simpa only [subst_ofRename] using paddingCondition_subst ops (Subst.ofRename rho) length array bottom

variable {Δ : List (Formula Const Γ)}

def paddingAt (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (canonical : ProofSyntax Const Δ (paddingCondition ops length array bottom))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length))) :
    ProofSyntax Const Δ (.eq (.app array position) bottom) := by
  have atPosition : ProofSyntax Const Δ (.imp
      (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length))
      (.eq (.app array position) bottom)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE position canonical)
    simp only [instantiate,HOL.subst,subst_weakenCtx,PredicateFixedPoint.subst_single_weaken,Subst.single]
  exact .impE atPosition inactive

def activeAt (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (active : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length)) :
    ProofSyntax Const Δ (.eq (.app (rebuilt ops selection length array bottom) position) (.app array position)) :=
  ops.singleAtLookup length (tabulate ops.toSignature selection length array) bottom position (.app array position)
    arrays (lookup ops.toSignature selection length array position tabulation.choice tabulation.recursion arithmetic active)

def inactiveAt (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (elements : ProofSyntax Const Δ (bounded ops.toSignature predicate length array))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length))) :
    ProofSyntax Const Δ (.eq (.app (rebuilt ops selection length array bottom) position) bottom) :=
  ops.singlePadding predicate length (tabulate ops.toSignature selection length array) bottom position arrays arithmetic.induction
    (member ops.toSignature selection predicate length array tabulation.choice tabulation.recursion arithmetic.induction elements) inactive

def notBeforeAtEnd (length : Term Const Γ ops.number)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ) :
    ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) length) length)) :=
  SuccessorOrder.sumExcludesLeft ops.successor ops.zero length (weakenCtx Γ ops.zero) length
    arithmetic.separation arithmetic.injectivity arithmetic.induction (SuccessorOrder.sumZero ops.successor ops.zero length)

def notBeforeAfter (length position : Term Const Γ ops.number)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (later : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) length) position)) :
    ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length)) := by
  apply ProofSyntax.exE (SuccessorOrder.less_has_successorOffset ops.successor ops.zero length position later)
  let body : Formula Const (ops.number :: Γ) :=
    .app (.app (.app (weakenCtx _ (SuccessorOrder.sum ops.zero ops.successor)) (weaken length))
      (.app (weakenCtx _ ops.successor) (.var .vz))) (weaken position)
  have arithmetic' := (arithmetic.rename (Rename.weaken (σ := ops.number))).prepend body
  apply ProofSyntax.castIndices rfl ?_ (SuccessorOrder.sumExcludesLeft ops.successor ops.zero
    (weaken length) (.app (weakenCtx _ ops.successor) (.var .vz)) (weaken position)
    arithmetic'.separation arithmetic'.injectivity arithmetic'.induction (.hyp 0))
  simp only [weaken,HOL.rename,rename_weakenCtx]

def pointwiseAt (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (elements : ProofSyntax Const Δ (bounded ops.toSignature predicate length array))
    (canonical : ProofSyntax Const Δ (paddingCondition ops length array bottom)) :
    ProofSyntax Const Δ (.eq (.app (rebuilt ops selection length array bottom) position) (.app array position)) := by
  have vectorMember := member ops.toSignature selection predicate length array
    tabulation.choice tabulation.recursion arithmetic.induction elements
  apply ProofSyntax.orE (SuccessorOrder.comparisonCoverage ops.successor ops.zero length position arithmetic.induction)
  · let later : Formula Const Γ := .app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) length) position
    have absent := notBeforeAfter ops length position (arithmetic.prepend later) (.hyp 0)
    exact .eqTrans (ops.singlePadding predicate length (tabulate ops.toSignature selection length array) bottom position
      (arrays.prepend later) (arithmetic.induction.prepend later) (vectorMember.prepend later) absent)
      (.eqSymm (paddingAt ops length array bottom position (canonical.prepend later) absent))
  · apply ProofSyntax.orE (.hyp 0)
    · let outer : Formula Const Γ := .or (.eq length position)
        (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length)
      let same : Formula Const Γ := .eq length position
      have absent := notBeforeAtEnd ops length ((arithmetic.prepend outer).prepend same)
      have endpoint := ProofSyntax.eqTrans
        (ops.singleAtEnd predicate length (tabulate ops.toSignature selection length array) bottom
          ((arrays.prepend outer).prepend same) ((vectorMember.prepend outer).prepend same))
        (.eqSymm (paddingAt ops length array bottom length ((canonical.prepend outer).prepend same) absent))
      exact .eqTrans (.eqSymm (.eqAppArg (rebuilt ops selection length array bottom) (.hyp 0)))
        (.eqTrans endpoint (.eqAppArg array (.hyp 0)))
    · let outer : Formula Const Γ := .or (.eq length position)
        (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length)
      let active : Formula Const Γ := .app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length
      exact activeAt ops selection length array bottom position
        ((tabulation.prepend outer).prepend active) ((arithmetic.prepend outer).prepend active)
        ((arrays.prepend outer).prepend active) (.hyp 0)

def pointwise (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType) (bottom : Term Const Γ ops.element)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (elements : ProofSyntax Const Δ (bounded ops.toSignature predicate length array))
    (canonical : ProofSyntax Const Δ (paddingCondition ops length array bottom)) :
    ProofSyntax Const Δ (.all (.eq (.app (weaken (rebuilt ops selection length array bottom)) (.var .vz))
      (.app (weaken array) (.var .vz)))) := by
  apply ProofSyntax.allI
  have elements' : ProofSyntax Const (weakenHyps (σ := ops.number) Δ)
      (bounded ops.toSignature (weaken predicate) (weaken length) (weaken array)) :=
    .castIndices rfl (bounded_rename ops.toSignature Rename.weaken predicate length array) (elements.rename Rename.weaken)
  have canonical' : ProofSyntax Const (weakenHyps (σ := ops.number) Δ)
      (paddingCondition ops (weaken length) (weaken array) (weaken bottom)) :=
    .castIndices rfl (paddingCondition_rename ops Rename.weaken length array bottom) (canonical.rename Rename.weaken)
  apply ProofSyntax.castIndices rfl ?_ (pointwiseAt ops selection (weaken predicate) (weaken length) (weaken array)
    (weaken bottom) (.var .vz) (tabulation.weaken ops.number) (arithmetic.rename Rename.weaken)
    (arrays.weaken ops.number) elements' canonical')
  simp only [weaken,rebuilt_rename]

theorem paddingAt_free (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (canonical : ProofSyntax Const Δ (paddingCondition ops length array bottom))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length)))
    (canonicalFree : canonical.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (paddingAt ops length array bottom position canonical inactive).FunctionExtensionalityFree := by
  simpa only [paddingAt,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree] using
    And.intro canonicalFree inactiveFree

theorem activeAt_free (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (active : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length))
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) (activeFree : active.FunctionExtensionalityFree) :
    (activeAt ops selection length array bottom position tabulation arithmetic arrays active).FunctionExtensionalityFree :=
  ops.singleAtLookup_free _ _ _ _ _ arrays _ arraysFree
    (lookup_free ops.toSignature selection length array position tabulation.choice tabulation.recursion arithmetic active
      tabulationFree.1 tabulationFree.2 arithmeticFree activeFree)

theorem inactiveAt_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (elements : ProofSyntax Const Δ (bounded ops.toSignature predicate length array))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) position) length)))
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) (elementsFree : elements.FunctionExtensionalityFree)
    (inactiveFree : inactive.FunctionExtensionalityFree) :
    (inactiveAt ops selection predicate length array bottom position tabulation arithmetic arrays elements inactive).FunctionExtensionalityFree :=
  ops.singlePadding_free _ _ _ _ _ arrays arithmetic.induction _ inactive arraysFree arithmeticFree.2.2
    (member_free ops.toSignature selection predicate length array tabulation.choice tabulation.recursion arithmetic.induction elements
      tabulationFree.1 tabulationFree.2 arithmeticFree.2.2 elementsFree) inactiveFree

theorem notBeforeAtEnd_free (length : Term Const Γ ops.number)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ) (free : arithmetic.Free) :
    (notBeforeAtEnd ops length arithmetic).FunctionExtensionalityFree :=
  SuccessorOrder.sumExcludesLeft_free _ _ _ _ _ _ _ _ _ free.1 free.2.1 free.2.2
    (SuccessorOrder.sumZero_free _ _ _)

theorem notBeforeAfter_free (length position : Term Const Γ ops.number)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (later : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) length) position))
    (arithmeticFree : arithmetic.Free) (laterFree : later.FunctionExtensionalityFree) :
    (notBeforeAfter ops length position arithmetic later).FunctionExtensionalityFree := by
  unfold notBeforeAfter
  refine ⟨SuccessorOrder.less_has_successorOffset_free _ _ _ _ _ laterFree,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply SuccessorOrder.sumExcludesLeft_free
  · exact ((arithmetic.rename Rename.weaken).prepend_free _ (arithmetic.rename_free _ arithmeticFree)).1
  · exact ((arithmetic.rename Rename.weaken).prepend_free _ (arithmetic.rename_free _ arithmeticFree)).2.1
  · exact ((arithmetic.rename Rename.weaken).prepend_free _ (arithmetic.rename_free _ arithmeticFree)).2.2
  · trivial

theorem pointwiseAt_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (elements : ProofSyntax Const Δ (bounded ops.toSignature predicate length array))
    (canonical : ProofSyntax Const Δ (paddingCondition ops length array bottom))
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) (elementsFree : elements.FunctionExtensionalityFree)
    (canonicalFree : canonical.FunctionExtensionalityFree) :
    (pointwiseAt ops selection predicate length array bottom position tabulation arithmetic arrays elements canonical).FunctionExtensionalityFree := by
  have vectorFree := member_free ops.toSignature selection predicate length array
    tabulation.choice tabulation.recursion arithmetic.induction elements
    tabulationFree.1 tabulationFree.2 arithmeticFree.2.2 elementsFree
  simp only [pointwiseAt,ProofSyntax.FunctionExtensionalityFree]
  refine ⟨SuccessorOrder.comparisonCoverage_free _ _ _ _ _ arithmeticFree.2.2,?_,True.intro,?_,?_⟩
  · constructor
    · apply ops.singlePadding_free
      · exact arrays.prepend_free _ arraysFree
      · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr arithmeticFree.2.2
      · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr vectorFree
      · exact notBeforeAfter_free _ _ _ _ _ (arithmetic.prepend_free _ arithmeticFree) True.intro
    · exact paddingAt_free _ _ _ _ _ _ _ ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr canonicalFree)
        (notBeforeAfter_free _ _ _ _ _ (arithmetic.prepend_free _ arithmeticFree) True.intro)
  · simp only [true_and,and_true]
    constructor
    · exact ops.singleAtEnd_free _ _ _ _ _ _
        ((arrays.prepend _).prepend_free _ (arrays.prepend_free _ arraysFree))
        ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr vectorFree))
    · exact paddingAt_free _ _ _ _ _ _ _
        ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr canonicalFree))
        (notBeforeAtEnd_free _ _ _ ((arithmetic.prepend _).prepend_free _ (arithmetic.prepend_free _ arithmeticFree)))
  · exact activeAt_free _ _ _ _ _ _ _ _ _ _
      ((tabulation.prepend _).prepend_free _ (tabulation.prepend_free _ tabulationFree))
      ((arithmetic.prepend _).prepend_free _ (arithmetic.prepend_free _ arithmeticFree))
      ((arrays.prepend _).prepend_free _ (arrays.prepend_free _ arraysFree)) True.intro

theorem pointwise_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType) (bottom : Term Const Γ ops.element)
    (tabulation : ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (elements : ProofSyntax Const Δ (bounded ops.toSignature predicate length array))
    (canonical : ProofSyntax Const Δ (paddingCondition ops length array bottom))
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) (elementsFree : elements.FunctionExtensionalityFree)
    (canonicalFree : canonical.FunctionExtensionalityFree) :
    (pointwise ops selection predicate length array bottom tabulation arithmetic arrays elements canonical).FunctionExtensionalityFree := by
  unfold pointwise
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply pointwiseAt_free
  · exact tabulation.weaken_free _ tabulationFree
  · exact arithmetic.rename_free _ arithmeticFree
  · exact arrays.weaken_free _ arraysFree
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_rename] using elementsFree
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_rename] using canonicalFree

#print axioms activeAt
#print axioms inactiveAt
#print axioms pointwise
#print axioms pointwise_free
end Mettapedia.Logic.HOL.VectorTabulation.Shifted
