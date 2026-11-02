import Mettapedia.Logic.HOL.VectorChildArrayMembership

/-!
# Separately proved laws for membership in a mixed child array

The assembly uses leading/trailing equations, an actual lookup equation,
and bounded lookup coverage. These are retained source formulas rather than
an expanded copy of every proof that establishes them. The array function
is arbitrary until the implementation laws are supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildMembershipLaws
open FiniteConstructorEncoding IndexedVectorLookupWitnesses SuccessorOrder OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}

def lookupBody (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    ArgumentBody Const Γ [signature.number,signature.element] := fun images fields =>
  .imp (IndexedVectorPositions.lookup signature (HOL.subst images length) (HOL.subst images vector) fields.1 fields.2.1)
    (.eq (.app (HOL.subst images array) (.app (weakenCtx _ signature.successor) fields.1)) fields.2.1)

theorem lookupBody_natural (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    NaturalBody (lookupBody signature array length vector) := by
  intro Ω Ψ earlier later fields
  simp only [lookupBody,HOL.subst,IndexedVectorPositions.lookup_subst,HOL.subst_comp,subst_weakenCtx,substituteArguments]
  rfl

def lookupLaw (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) : Formula Const Γ :=
  forallArguments [signature.number,signature.element] (lookupBody signature array length vector)

theorem lookupLaw_subst (images : Subst Const Γ Ξ) (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    HOL.subst images (lookupLaw signature array length vector) =
      lookupLaw signature (HOL.subst images array) (HOL.subst images length) (HOL.subst images vector) := by
  unfold lookupLaw
  rw [forallArguments_subst _ _ _ (lookupBody_natural signature array length vector)]
  apply congrArg (forallArguments _)
  funext Ω later fields
  simp only [lookupBody,HOL.subst_comp]
  rfl

theorem lookupLaw_rename (rho : Rename Base Γ Ξ) (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    HOL.rename rho (lookupLaw signature array length vector) =
      lookupLaw signature (HOL.rename rho array) (HOL.rename rho length) (HOL.rename rho vector) := by
  simpa only [subst_ofRename] using lookupLaw_subst signature (Subst.ofRename rho) array length vector

variable {Δ : List (Formula Const Γ)}

def lookupAt (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (law : ProofSyntax Const Δ (lookupLaw signature array length vector)) :
    ProofSyntax Const Δ (.imp (IndexedVectorPositions.lookup signature length vector position element)
      (.eq (.app array (.app (weakenCtx Γ signature.successor) position)) element)) := by
  apply ProofSyntax.castIndices rfl ?_
    (forallArguments_elim _ _ (lookupBody_natural signature array length vector) (position,element,PUnit.unit) law)
  simp only [lookupBody,HOL.subst_id]

theorem lookupAt_free (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (law : ProofSyntax Const Δ (lookupLaw signature array length vector)) (free : law.FunctionExtensionalityFree) :
    (lookupAt signature array length vector position element law).FunctionExtensionalityFree := by
  unfold lookupAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_elim_free _ _ _ _ law free

def memberAtWitness (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (law : ProofSyntax Const Δ (lookupLaw signature array length vector))
    (present : ProofSyntax Const Δ (evidence signature predicate length vector position)) :
    ProofSyntax Const Δ (.app predicate (.app array (.app (weakenCtx Γ signature.successor) position))) := by
  apply ProofSyntax.exE present
  let body : Formula Const (signature.element :: Γ) :=
    .and (IndexedVectorPositions.lookup signature (weaken length) (weaken vector) (weaken position) (.var .vz))
      (.app (weaken predicate) (.var .vz))
  have shifted : ProofSyntax Const (body :: weakenHyps Δ)
      (lookupLaw signature (weaken array) (weaken length) (weaken vector)) :=
    ProofSyntax.castIndices rfl (lookupLaw_rename signature Rename.weaken array length vector)
      ((law.rename Rename.weaken).prepend body)
  have same := ProofSyntax.impE (lookupAt signature (weaken array) (weaken length) (weaken vector) (weaken position) (.var .vz) shifted)
    (ProofSyntax.andEL (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ (.impE (.eqPropER (.eqAppArg (weaken predicate) same)) (.andER (.hyp 0)))
  simp only [weaken,HOL.rename,rename_weakenCtx]

theorem memberAtWitness_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (law : ProofSyntax Const Δ (lookupLaw signature array length vector))
    (present : ProofSyntax Const Δ (evidence signature predicate length vector position))
    (lawFree : law.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (memberAtWitness signature predicate array length vector position law present).FunctionExtensionalityFree := by
  unfold memberAtWitness
  refine ⟨presentFree,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨⟨?_,True.intro⟩,True.intro⟩
  apply lookupAt_free
  simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using lawFree

def memberInterior (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (slot offset : Term Const Γ signature.number)
    (law : ProofSyntax Const Δ (lookupLaw signature array length vector))
    (coverage : ProofSyntax Const Δ (IndexedVectorLookupCoverage.condition signature predicate length vector))
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ signature.successor) offset)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) offset) length)) :
    ProofSyntax Const Δ (.app predicate (.app array slot)) :=
  .impE (.eqPropER (.eqAppArg predicate (.eqAppArg array address)))
    (memberAtWitness signature predicate array length vector offset law
      (.impE (IndexedVectorLookupCoverage.atPosition signature predicate length vector offset coverage) bounded))

theorem memberInterior_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (length : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (slot offset : Term Const Γ signature.number)
    (law : ProofSyntax Const Δ (lookupLaw signature array length vector))
    (coverage : ProofSyntax Const Δ (IndexedVectorLookupCoverage.condition signature predicate length vector))
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ signature.successor) offset)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) offset) length))
    (lawFree : law.FunctionExtensionalityFree) (coverageFree : coverage.FunctionExtensionalityFree)
    (addressFree : address.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (memberInterior signature predicate array length vector slot offset law coverage address bounded).FunctionExtensionalityFree :=
  ⟨addressFree,memberAtWitness_free _ _ _ _ _ _ law _ lawFree
    ⟨IndexedVectorLookupCoverage.atPosition_free _ _ _ _ _ coverage coverageFree,boundedFree⟩⟩

def memberAtBoundary (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element)) (slot boundary : Term Const Γ signature.number)
    (value : Term Const Γ signature.element)
    (equation : ProofSyntax Const Δ (.eq (.app array boundary) value))
    (member : ProofSyntax Const Δ (.app predicate value))
    (address : ProofSyntax Const Δ (.eq slot boundary)) : ProofSyntax Const Δ (.app predicate (.app array slot)) :=
  .impE (.eqPropER (.eqAppArg predicate (.eqTrans (.eqAppArg array address) equation))) member

theorem memberAtBoundary_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element)) (slot boundary : Term Const Γ signature.number)
    (value : Term Const Γ signature.element)
    (equation : ProofSyntax Const Δ (.eq (.app array boundary) value))
    (member : ProofSyntax Const Δ (.app predicate value))
    (address : ProofSyntax Const Δ (.eq slot boundary))
    (equationFree : equation.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (addressFree : address.FunctionExtensionalityFree) :
    (memberAtBoundary signature predicate array slot boundary value equation member address).FunctionExtensionalityFree :=
  ⟨⟨addressFree,equationFree⟩,memberFree⟩

def fromCases {indexType : Ty Base} (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (length slot : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (before after : Term Const Γ signature.element)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (leading : ProofSyntax Const Δ (.eq (.app array (weakenCtx Γ signature.zero)) before))
    (trailing : ProofSyntax Const Δ (.eq (.app array (.app (weakenCtx Γ signature.successor) length)) after))
    (lookup : ProofSyntax Const Δ (lookupLaw signature array length vector))
    (coverage : ProofSyntax Const Δ (IndexedVectorLookupCoverage.condition signature predicate length vector))
    (beforeMember : ProofSyntax Const Δ (.app predicate before)) (afterMember : ProofSyntax Const Δ (.app predicate after))
    (cases : ProofSyntax Const Δ (mixedCases signature.zero signature.successor length slot firstIndex vectorIndex lastIndex target)) :
    ProofSyntax Const Δ (.app predicate (.app array slot)) := by
  apply ProofSyntax.orE cases
  · exact memberAtBoundary signature predicate array slot _ before (leading.prepend _) (beforeMember.prepend _) (.andEL (.hyp 0))
  · let remaining : Formula Const Γ := .or
      (.ex (.and (.eq (weaken slot) (.app (weakenCtx _ signature.successor) (.var .vz)))
        (.and (.app (.app (weakenCtx _ (less signature.successor)) (.var .vz)) (weaken length))
          (.eq (weaken target) (weaken vectorIndex)))))
      (.and (.eq slot (.app (weakenCtx Γ signature.successor) length)) (.eq target lastIndex))
    apply ProofSyntax.orE (.hyp (Δ := remaining :: Δ) 0)
    · let interior : Formula Const Γ := .ex (.and (.eq (weaken slot) (.app (weakenCtx _ signature.successor) (.var .vz)))
        (.and (.app (.app (weakenCtx _ (less signature.successor)) (.var .vz)) (weaken length))
          (.eq (weaken target) (weaken vectorIndex))))
      apply ProofSyntax.exE (.hyp (Δ := interior :: remaining :: Δ) 0)
      let body : Formula Const (signature.number :: Γ) :=
        .and (.eq (weaken slot) (.app (weakenCtx _ signature.successor) (.var .vz)))
          (.and (.app (.app (weakenCtx _ (less signature.successor)) (.var .vz)) (weaken length))
            (.eq (weaken target) (weaken vectorIndex)))
      have currentLookup : ProofSyntax Const (body :: weakenHyps (interior :: remaining :: Δ))
          (lookupLaw signature (weaken array) (weaken length) (weaken vector)) :=
        ProofSyntax.castIndices rfl (lookupLaw_rename signature Rename.weaken array length vector)
          ((((lookup.prepend remaining).prepend interior).rename Rename.weaken).prepend body)
      have currentCoverage : ProofSyntax Const (body :: weakenHyps (interior :: remaining :: Δ))
          (IndexedVectorLookupCoverage.condition signature (weaken predicate) (weaken length) (weaken vector)) :=
        ProofSyntax.castIndices rfl (IndexedVectorLookupCoverage.condition_rename signature Rename.weaken predicate length vector)
          ((((coverage.prepend remaining).prepend interior).rename Rename.weaken).prepend body)
      apply ProofSyntax.castIndices rfl ?_
        (memberInterior signature (weaken predicate) (weaken array) (weaken length) (weaken vector) (weaken slot) (.var .vz)
          currentLookup currentCoverage (.andEL (.hyp 0)) (.andEL (.andER (.hyp 0))))
      rfl
    · exact memberAtBoundary signature predicate array slot _ after
        ((trailing.prepend remaining).prepend _) ((afterMember.prepend remaining).prepend _) (.andEL (.hyp 0))

theorem fromCases_free {indexType : Ty Base} (predicate : Term Const Γ (signature.element ⇒ .prop))
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (length slot : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (before after : Term Const Γ signature.element)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (leading : ProofSyntax Const Δ (.eq (.app array (weakenCtx Γ signature.zero)) before))
    (trailing : ProofSyntax Const Δ (.eq (.app array (.app (weakenCtx Γ signature.successor) length)) after))
    (lookup : ProofSyntax Const Δ (lookupLaw signature array length vector))
    (coverage : ProofSyntax Const Δ (IndexedVectorLookupCoverage.condition signature predicate length vector))
    (beforeMember : ProofSyntax Const Δ (.app predicate before)) (afterMember : ProofSyntax Const Δ (.app predicate after))
    (cases : ProofSyntax Const Δ (mixedCases signature.zero signature.successor length slot firstIndex vectorIndex lastIndex target))
    (leadingFree : leading.FunctionExtensionalityFree) (trailingFree : trailing.FunctionExtensionalityFree)
    (lookupFree : lookup.FunctionExtensionalityFree) (coverageFree : coverage.FunctionExtensionalityFree)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (afterFree : afterMember.FunctionExtensionalityFree)
    (casesFree : cases.FunctionExtensionalityFree) :
    (fromCases signature predicate array length slot vector before after firstIndex vectorIndex lastIndex target
      leading trailing lookup coverage beforeMember afterMember cases).FunctionExtensionalityFree := by
  unfold fromCases
  refine ⟨casesFree,?_,True.intro,?_,?_⟩
  · exact memberAtBoundary_free _ _ _ _ _ _ _ _ _
      ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr leadingFree)
      ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr beforeFree) True.intro
  · refine ⟨True.intro,?_⟩
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply memberInterior_free
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using lookupFree
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using coverageFree
    · trivial
    · trivial
  · apply memberAtBoundary_free
    · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using trailingFree
    · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using afterFree
    · trivial

#print axioms memberInterior_free
#print axioms fromCases_free
end Mettapedia.Logic.HOL.VectorChildMembershipLaws
