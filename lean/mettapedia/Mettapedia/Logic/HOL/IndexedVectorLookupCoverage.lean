import Mettapedia.Logic.HOL.IndexedVectorLookupWitnesses
import Mettapedia.Logic.HOL.NaturalConstructorCases
import Mettapedia.Logic.HOL.IndexedVectorPositionBounds
import Mettapedia.Logic.HOL.SuccessorOrderCoverage

/-!
# Retained bounded-position coverage for vector lookup

The induction motive quantifies the requested position inside each current
index/vector pair. A witness carries both the original lookup and element
membership. Arithmetic assumptions remain explicit throughout the proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorLookupCoverage
open FiniteConstructorEncoding IndexedVectorLookupWitnesses SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}
    {Δ : List (Formula Const Γ)}

def condition (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) : Formula Const Γ :=
  .all (.imp (.app (.app (weakenCtx _ (less signature.successor)) (.var .vz)) (weaken index))
    (evidence signature (weaken predicate) (weaken index) (weaken vector) (.var .vz)))

theorem condition_subst (images : Subst Const Γ Ξ) (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    HOL.subst images (condition signature predicate index vector) =
      condition signature (HOL.subst images predicate) (HOL.subst images index) (HOL.subst images vector) := by
  simp only [condition,HOL.subst,subst_weakenCtx,subst_weaken,evidence_subst,Subst.lift]

theorem condition_rename (rho : Rename Base Γ Ξ) (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    HOL.rename rho (condition signature predicate index vector) =
      condition signature (HOL.rename rho predicate) (HOL.rename rho index) (HOL.rename rho vector) := by
  simpa only [subst_ofRename] using condition_subst signature (Subst.ofRename rho) predicate index vector

def atPosition (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (coverage : ProofSyntax Const Δ (condition signature predicate index vector)) :
    ProofSyntax Const Δ (.imp (.app (.app (weakenCtx Γ (less signature.successor)) position) index)
      (evidence signature predicate index vector position)) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE position coverage)
  simp only [instantiate,HOL.subst,subst_weakenCtx,PredicateFixedPoint.subst_single_weaken,evidence_subst,Subst.single]

theorem atPosition_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (coverage : ProofSyntax Const Δ (condition signature predicate index vector)) (free : coverage.FunctionExtensionalityFree) :
    (atPosition signature predicate index vector position coverage).FunctionExtensionalityFree := by
  unfold atPosition
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def motiveBody (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    ArgumentBody Const Γ [signature.number,signature.vector] := fun images fields =>
  condition signature (HOL.subst images predicate) fields.1 fields.2.1

theorem motiveBody_natural (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    NaturalBody (motiveBody signature predicate) := by
  intro Ω Ψ earlier later fields
  simp only [motiveBody,condition_subst,HOL.subst_comp,substituteArguments]
  rfl

def motive (predicate : Term Const Γ (signature.element ⇒ .prop)) : Term Const Γ signature.Property :=
  abstractArguments [signature.number,signature.vector] (motiveBody signature predicate)

theorem motive_subst (images : Subst Const Γ Ξ) (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    HOL.subst images (motive signature predicate) = motive signature (HOL.subst images predicate) := by
  unfold motive
  rw [abstractArguments_subst _ _ _ (motiveBody_natural signature predicate)]
  apply congrArg (abstractArguments _)
  funext Ω later fields
  simp only [motiveBody,HOL.subst_comp]
  rfl

theorem motive_rename (rho : Rename Base Γ Ξ) (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    HOL.rename rho (motive signature predicate) = motive signature (HOL.rename rho predicate) := by
  simpa only [subst_ofRename] using motive_subst signature (Subst.ofRename rho) predicate

def motive_apply (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    ProofSyntax Const Δ (.eq (PredicatePair.holds (motive signature predicate) index vector)
      (condition signature predicate index vector)) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractArguments_beta _ _ (motiveBody_natural signature predicate) (index,vector,PUnit.unit))
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun entry => Term.var entry) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [motiveBody,identityTerm]
  rfl

theorem motive_apply_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) :
    (motive_apply (Δ := Δ) signature predicate index vector).FunctionExtensionalityFree := by
  unfold motive_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

def base (predicate : Term Const Γ (signature.element ⇒ .prop))
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ) :
    ProofSyntax Const Δ (PredicatePair.holds (motive signature predicate)
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.nil)) := by
  apply ProofSyntax.impE (.eqPropER (motive_apply signature predicate _ _))
  refine .allI (.impI (.botE ?_))
  let bound : Formula Const (signature.number :: Γ) :=
    .app (.app (weakenCtx _ (less signature.successor)) (.var .vz)) (weaken (weakenCtx Γ signature.zero))
  have separator := ((arithmetic.rename (Rename.weaken (σ := signature.number))).prepend bound).separation
  apply lessZeroRefute signature.successor signature.zero (.var .vz) separator
  apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := bound :: weakenHyps Δ) 0)
  change bound = _
  simp only [bound,weaken,rename_weakenCtx]

theorem base_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ) (free : arithmetic.Free) :
    (base signature predicate arithmetic).FunctionExtensionalityFree := by
  unfold base
  refine ⟨motive_apply_free _ _ _ _,?_⟩
  apply lessZeroRefute_free
  · exact ((arithmetic.rename Rename.weaken).prepend_free _ (arithmetic.rename_free _ free)).1
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

#print axioms base_free

def zeroPosition (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (same : ProofSyntax Const Δ (.eq position (weakenCtx Γ signature.zero)))
    (member : ProofSyntax Const Δ (.app predicate first)) :
    ProofSyntax Const Δ (evidence signature predicate (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index first vector) position) :=
  .impE (.eqPropER (positionEquation signature predicate (.app (weakenCtx Γ signature.successor) index)
    (signature.consValue index first vector) position (weakenCtx Γ signature.zero) same))
    (IndexedVectorLookupWitnesses.head signature predicate index first vector member)

theorem zeroPosition_free (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (same : ProofSyntax Const Δ (.eq position (weakenCtx Γ signature.zero)))
    (member : ProofSyntax Const Δ (.app predicate first))
    (sameFree : same.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (zeroPosition signature predicate index first vector position same member).FunctionExtensionalityFree :=
  ⟨positionEquation_free _ _ _ _ _ _ _ sameFree,IndexedVectorLookupWitnesses.head_free _ _ _ _ _ _ memberFree⟩

def successorPosition (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector)
    (position predecessor : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (coverage : ProofSyntax Const Δ (condition signature predicate index vector))
    (same : ProofSyntax Const Δ (.eq position (.app (weakenCtx Γ signature.successor) predecessor)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) position)
      (.app (weakenCtx Γ signature.successor) index))) :
    ProofSyntax Const Δ (evidence signature predicate (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index first vector) position) := by
  let bound := ProofSyntax.impE (.eqPropEL (.eqApp (.app (weakenCtx Γ signature.successor) index)
    (.eqAppArg (weakenCtx Γ (less signature.successor)) same))) bounded
  let smaller := lessSuccessorCancel signature.successor predecessor index arithmetic.injectivity bound
  let found := ProofSyntax.impE (atPosition signature predicate index vector predecessor coverage) smaller
  let advanced := IndexedVectorLookupWitnesses.tail signature predicate index first vector predecessor found
  exact .impE (.eqPropER (positionEquation signature predicate (.app (weakenCtx Γ signature.successor) index)
    (signature.consValue index first vector) position (.app (weakenCtx Γ signature.successor) predecessor) same)) advanced

theorem successorPosition_free (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector)
    (position predecessor : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (coverage : ProofSyntax Const Δ (condition signature predicate index vector))
    (same : ProofSyntax Const Δ (.eq position (.app (weakenCtx Γ signature.successor) predecessor)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) position)
      (.app (weakenCtx Γ signature.successor) index)))
    (arithmeticFree : arithmetic.Free) (coverageFree : coverage.FunctionExtensionalityFree)
    (sameFree : same.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (successorPosition signature predicate index first vector position predecessor arithmetic coverage same bounded).FunctionExtensionalityFree := by
  unfold successorPosition
  refine ⟨positionEquation_free _ _ _ _ _ _ _ sameFree,?_⟩
  apply IndexedVectorLookupWitnesses.tail_free
  refine ⟨atPosition_free _ _ _ _ _ coverage coverageFree,?_⟩
  exact lessSuccessorCancel_free _ _ _ _ _ arithmeticFree.2.1 ⟨sameFree,boundedFree⟩

def stepAt (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (.app predicate first))
    (coverage : ProofSyntax Const Δ (condition signature predicate index vector))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) position)
      (.app (weakenCtx Γ signature.successor) index))) :
    ProofSyntax Const Δ (evidence signature predicate (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index first vector) position) := by
  apply ProofSyntax.orE (NaturalConstructorCases.fromInduction signature.zero signature.successor position arithmetic.induction)
  · exact zeroPosition signature predicate index first vector position (.hyp 0) (member.prepend _)
  · let predecessor : Formula Const Γ := .ex (.eq (weaken position) (.app (weakenCtx _ signature.successor) (.var .vz)))
    apply ProofSyntax.exE (.hyp (Δ := predecessor :: Δ) 0)
    let same : Formula Const (signature.number :: Γ) := .eq (weaken position) (.app (weakenCtx _ signature.successor) (.var .vz))
    let currentArithmetic := (((arithmetic.prepend predecessor).rename Rename.weaken).prepend same)
    have currentCoverage : ProofSyntax Const (same :: weakenHyps (predecessor :: Δ))
        (condition signature (weaken predicate) (weaken index) (weaken vector)) :=
      ProofSyntax.castIndices rfl (condition_rename signature Rename.weaken predicate index vector)
        ((((coverage.prepend predecessor).rename Rename.weaken)).prepend same)
    have currentBound : ProofSyntax Const (same :: weakenHyps (predecessor :: Δ))
        (.app (.app (weakenCtx _ (less signature.successor)) (weaken position))
          (.app (weakenCtx _ signature.successor) (weaken index))) := by
      apply ProofSyntax.castIndices rfl ?_ ((((bounded.prepend predecessor).rename Rename.weaken)).prepend same)
      simp only [HOL.rename,rename_weakenCtx]
      rfl
    apply ProofSyntax.castIndices rfl ?_
      (successorPosition signature (weaken predicate) (weaken index) (weaken first) (weaken vector)
        (weaken position) (.var .vz) currentArithmetic currentCoverage (.hyp 0) currentBound)
    simp only [weaken,evidence_rename,HOL.rename,rename_weakenCtx,IndexedVectorPredicate.Signature.consValue]

theorem stepAt_free (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (.app predicate first))
    (coverage : ProofSyntax Const Δ (condition signature predicate index vector))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) position)
      (.app (weakenCtx Γ signature.successor) index)))
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree)
    (coverageFree : coverage.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (stepAt signature predicate index first vector position arithmetic member coverage bounded).FunctionExtensionalityFree := by
  unfold stepAt
  refine ⟨NaturalConstructorCases.fromInduction_free _ _ _ _ arithmeticFree.2.2,?_,?_⟩
  · apply zeroPosition_free
    · trivial
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr memberFree
  · refine ⟨True.intro,?_⟩
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply successorPosition_free
    · apply PeanoEvidence.prepend_free
      apply PeanoEvidence.rename_free
      exact arithmetic.prepend_free _ arithmeticFree
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using coverageFree
    · trivial
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using boundedFree

#print axioms stepAt_free

def step_point (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ) :
    ProofSyntax Const Δ (signature.stepBody predicate (motive signature predicate) index first vector) := by
  let a := Term.app predicate first
  let b := signature.member predicate index vector
  let c := PredicatePair.holds (motive signature predicate) index vector
  refine .impI (.impI (.impI ?_))
  apply ProofSyntax.impE (.eqPropER (motive_apply signature predicate
    (.app (weakenCtx Γ signature.successor) index) (signature.consValue index first vector)))
  refine .allI (.impI ?_)
  let bound : Formula Const (signature.number :: Γ) :=
    .app (.app (weakenCtx _ (less signature.successor)) (.var .vz))
      (weaken (.app (weakenCtx Γ signature.successor) index))
  let assumptions := bound :: weakenHyps (c :: b :: a :: Δ)
  let currentArithmetic := (((((arithmetic.prepend a).prepend b).prepend c).rename Rename.weaken).prepend bound)
  have previous : ProofSyntax Const assumptions
      (PredicatePair.holds (motive signature (weaken predicate)) (weaken index) (weaken vector)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := assumptions) ⟨1,by simp [assumptions,weakenHyps]⟩)
    change weaken c = _
    simp only [c,PredicatePair.holds,weaken,HOL.rename,motive_rename]
  have coverage : ProofSyntax Const assumptions (condition signature (weaken predicate) (weaken index) (weaken vector)) :=
    .impE (.eqPropEL (motive_apply signature (weaken predicate) (weaken index) (weaken vector))) previous
  have member : ProofSyntax Const assumptions (.app (weaken predicate) (weaken first)) :=
    .hyp ⟨3,by simp [assumptions,weakenHyps]⟩
  have bounded : ProofSyntax Const assumptions
      (.app (.app (weakenCtx _ (less signature.successor)) (.var .vz))
        (.app (weakenCtx _ signature.successor) (weaken index))) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := assumptions) 0)
    change bound = _
    simp only [bound,weaken,HOL.rename,rename_weakenCtx]
  apply ProofSyntax.castIndices rfl ?_
    (stepAt signature (weaken predicate) (weaken index) (weaken first) (weaken vector) (.var .vz)
      currentArithmetic member coverage bounded)
  simp only [weaken,HOL.rename,rename_weakenCtx,IndexedVectorPredicate.Signature.consValue]

theorem step_point_free (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ) (free : arithmetic.Free) :
    (step_point signature predicate index first vector arithmetic).FunctionExtensionalityFree := by
  unfold step_point
  refine ⟨motive_apply_free _ _ _ _,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply stepAt_free
  · apply PeanoEvidence.prepend_free
    apply PeanoEvidence.rename_free
    iterate 3 apply PeanoEvidence.prepend_free
    exact free
  · trivial
  · refine ⟨motive_apply_free _ _ _ _,?_⟩
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

def step_condition (predicate : Term Const Γ (signature.element ⇒ .prop))
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ) :
    ProofSyntax Const Δ (signature.stepCondition predicate (motive signature predicate)) := by
  refine .allI (.allI (.allI ?_))
  let currentPredicate := weaken (σ := signature.vector) (weaken (σ := signature.element) (weaken (σ := signature.number) predicate))
  let currentArithmetic := ((arithmetic.rename (Rename.weaken (σ := signature.number))).rename
    (Rename.weaken (σ := signature.element))).rename (Rename.weaken (σ := signature.vector))
  apply ProofSyntax.castIndices rfl ?_
    (step_point signature currentPredicate (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz) currentArithmetic)
  simp only [currentPredicate,weaken,motive_rename]

theorem step_condition_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ) (free : arithmetic.Free) :
    (step_condition signature predicate arithmetic).FunctionExtensionalityFree := by
  unfold step_condition
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply step_point_free
  iterate 3 apply PeanoEvidence.rename_free
  exact free

def fromMembership (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (signature.member predicate index vector)) :
    ProofSyntax Const Δ (condition signature predicate index vector) :=
  .impE (.eqPropEL (motive_apply signature predicate index vector))
    (signature.inductionProof predicate (motive signature predicate) index vector
      (base signature predicate arithmetic) (step_condition signature predicate arithmetic) member)

theorem fromMembership_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (signature.member predicate index vector))
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree) :
    (fromMembership signature predicate index vector arithmetic member).FunctionExtensionalityFree :=
  ⟨motive_apply_free _ _ _ _,signature.inductionProof_free _ _ _ _ _ _ _
    (base_free _ _ arithmetic arithmeticFree) (step_condition_free _ _ arithmetic arithmeticFree) memberFree⟩

def witnessFromBound (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (signature.member predicate index vector))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) position) index)) :
    ProofSyntax Const Δ (evidence signature predicate index vector position) :=
  .impE (atPosition signature predicate index vector position (fromMembership signature predicate index vector arithmetic member)) bounded

theorem witnessFromBound_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (signature.member predicate index vector))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) position) index))
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (witnessFromBound signature predicate index vector position arithmetic member bounded).FunctionExtensionalityFree :=
  ⟨atPosition_free _ _ _ _ _ _ (fromMembership_free _ _ _ _ arithmetic member arithmeticFree memberFree),boundedFree⟩

#print axioms fromMembership_free
#print axioms witnessFromBound_free

def boundFromWitness (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor)))
    (present : ProofSyntax Const Δ (evidence signature predicate index vector position)) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less signature.successor)) position) index) := by
  apply ProofSyntax.exE present
  let body : Formula Const (signature.element :: Γ) :=
    .and (IndexedVectorPositions.lookup signature (weaken index) (weaken vector) (weaken position) (.var .vz))
      (.app (weaken predicate) (.var .vz))
  let currentPrinciple := (inductionRename signature.successor signature.zero principle
    (Rename.weaken (σ := signature.element))).prepend body
  apply ProofSyntax.castIndices rfl ?_
    (IndexedVectorPositionBounds.lessOfLookup signature (weaken index) (weaken vector) (weaken position) (.var .vz)
      currentPrinciple (.andEL (.hyp 0)))
  simp only [weaken,HOL.rename,rename_weakenCtx]

theorem boundFromWitness_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor)))
    (present : ProofSyntax Const Δ (evidence signature predicate index vector position))
    (principleFree : principle.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (boundFromWitness signature predicate index vector position principle present).FunctionExtensionalityFree := by
  unfold boundFromWitness
  refine ⟨presentFree,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply IndexedVectorPositionBounds.lessOfLookup_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      (inductionRename_free _ _ principle _ principleFree)
  · trivial

def boundWitnessEquation (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (signature.member predicate index vector)) :
    ProofSyntax Const Δ (.eq (.app (.app (weakenCtx Γ (less signature.successor)) position) index)
      (evidence signature predicate index vector position)) :=
  .eqPropI (.impI (witnessFromBound signature predicate index vector position
    (arithmetic.prepend _) (member.prepend _) (.hyp 0)))
    (.impI (boundFromWitness signature predicate index vector position (arithmetic.induction.prepend _) (.hyp 0)))

theorem boundWitnessEquation_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (arithmetic : PeanoEvidence signature.successor signature.zero Δ)
    (member : ProofSyntax Const Δ (signature.member predicate index vector))
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree) :
    (boundWitnessEquation signature predicate index vector position arithmetic member).FunctionExtensionalityFree :=
  ⟨witnessFromBound_free _ _ _ _ _ _ _ _ (arithmetic.prepend_free _ arithmeticFree)
    ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr memberFree) trivial,
    boundFromWitness_free _ _ _ _ _ _ _ ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr arithmeticFree.2.2) trivial⟩

#print axioms boundWitnessEquation_free
end Mettapedia.Logic.HOL.IndexedVectorLookupCoverage
