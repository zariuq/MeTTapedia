import Mettapedia.Logic.HOL.NaturalConstructorCases
import Mettapedia.Logic.HOL.SuccessorOrderCoverage
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs

/-!
# Exact addresses of unit-length position segments

Zero-count sum inversion uses only zero/successor separation. A sum with
left input one has result successor of its offset without additional Peano
premises. Reading a position below one uses the explicit Peano evidence.
These retained equations identify the leading and trailing scalar fields of
a mixed vector layout without assuming the desired address equalities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number)) (zero : ClosedTerm Const number)
    {Δ : List (Formula Const Γ)}

def sumZeroCountBody (first : Term Const Γ number) : ArgumentBody Const Γ [number,number] :=
  fun images fields => .imp (.eq fields.1 (weakenCtx _ zero)) (.eq fields.2.1 (HOL.subst images first))

theorem sumZeroCountBody_natural (first : Term Const Γ number) : NaturalBody (sumZeroCountBody zero first) := by
  intro Ω Ψ earlier later fields
  simp only [sumZeroCountBody,HOL.subst,subst_weakenCtx,HOL.subst_comp,substituteArguments]
  rfl

def sumZeroCountPredicate (first : Term Const Γ number) : Term Const Γ (number ⇒ number ⇒ .prop) :=
  abstractArguments [number,number] (sumZeroCountBody zero first)

theorem sumZeroCountPredicate_subst (images : Subst Const Γ Ξ) (first : Term Const Γ number) :
    HOL.subst images (sumZeroCountPredicate zero first) = sumZeroCountPredicate zero (HOL.subst images first) := by
  unfold sumZeroCountPredicate
  rw [abstractArguments_subst _ _ _ (sumZeroCountBody_natural zero first)]
  apply congrArg (abstractArguments _)
  funext Ω later fields
  simp only [sumZeroCountBody,HOL.subst_comp]
  rfl

theorem sumZeroCountPredicate_rename (rho : Rename Base Γ Ξ) (first : Term Const Γ number) :
    HOL.rename rho (sumZeroCountPredicate zero first) = sumZeroCountPredicate zero (HOL.rename rho first) := by
  simpa only [subst_ofRename] using sumZeroCountPredicate_subst zero (Subst.ofRename rho) first

def sumZeroCountPredicate_beta (first count result : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (.app (.app (sumZeroCountPredicate zero first) count) result)
      (.imp (.eq count (weakenCtx Γ zero)) (.eq result first))) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractArguments_beta [number,number] _ (sumZeroCountBody_natural zero first) (count,result,PUnit.unit))
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun entry => Term.var entry) term = term := ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [sumZeroCountBody,identityTerm]
  rfl

theorem sumZeroCountPredicate_beta_free (first count result : Term Const Γ number) :
    (sumZeroCountPredicate_beta (Δ := Δ) zero first count result).FunctionExtensionalityFree := by
  unfold sumZeroCountPredicate_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

def sumZeroCountClosed (first : Term Const Γ number)
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (sumClosed successor (sumZeroCountPredicate zero first)) := by
  refine .allI (.allI (.impI ?_))
  let count : Term Const (number :: number :: Γ) number := .var (.vs .vz)
  let result : Term Const (number :: number :: Γ) number := .var .vz
  let old := Term.app (.app (weaken (weaken (sumZeroCountPredicate zero first))) count) result
  have law : ProofSyntax Const (old :: weakenHyps (weakenHyps Δ))
      (NaturalNumeralProofs.separation (weakenCtx _ zero) (weakenCtx _ successor)) := by
    apply ProofSyntax.castIndices rfl ?_ (((separate.rename Rename.weaken).rename Rename.weaken).prepend old)
    simp only [NaturalNumeralProofs.separation,HOL.rename,Rename.lift,weaken,rename_weakenCtx]
  have impossible := NaturalNumeralProofs.successorNeZero (weakenCtx _ zero) (weakenCtx _ successor) count law
  have next : ProofSyntax Const (old :: weakenHyps (weakenHyps Δ))
      (.app (.app (sumZeroCountPredicate zero (weaken (weaken first))) (.app (weakenCtx _ successor) count))
        (.app (weakenCtx _ successor) result)) :=
    .impE (.eqPropER (sumZeroCountPredicate_beta zero (weaken (weaken first))
      (.app (weakenCtx _ successor) count) (.app (weakenCtx _ successor) result)))
      (.impI (.botE (.notE (impossible.prepend _) (.hyp 0))))
  apply ProofSyntax.castIndices rfl ?_ next
  simp only [weaken,sumZeroCountPredicate_rename]
  rfl

theorem sumZeroCountClosed_free (first : Term Const Γ number)
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : separate.FunctionExtensionalityFree) : (sumZeroCountClosed successor zero first separate).FunctionExtensionalityFree := by
  unfold sumZeroCountClosed
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨sumZeroCountPredicate_beta_free _ _ _ _,?_⟩
  refine ⟨?_,True.intro⟩
  apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
  apply NaturalNumeralProofs.successorNeZero_free
  simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using free

def sumZeroCount (first result : Term Const Γ number)
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (present : ProofSyntax Const Δ (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) (weakenCtx Γ zero)) result)) :
    ProofSyntax Const Δ (.eq result first) :=
  .impE (.impE (.eqPropEL (sumZeroCountPredicate_beta zero first (weakenCtx Γ zero) result))
    (sumEliminate successor zero first (weakenCtx Γ zero) result (sumZeroCountPredicate zero first) present
      (.impE (.eqPropER (sumZeroCountPredicate_beta zero first (weakenCtx Γ zero) first)) (.impI (.eqRefl first)))
      (sumZeroCountClosed successor zero first separate))) (.eqRefl _)

theorem sumZeroCount_free (first result : Term Const Γ number)
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (present : ProofSyntax Const Δ (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) (weakenCtx Γ zero)) result))
    (separateFree : separate.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (sumZeroCount successor zero first result separate present).FunctionExtensionalityFree :=
  ⟨⟨sumZeroCountPredicate_beta_free _ _ _ _,sumEliminate_free _ _ _ _ _ _ present _ _ presentFree
    ⟨sumZeroCountPredicate_beta_free _ _ _ _,True.intro⟩ (sumZeroCountClosed_free _ _ first separate separateFree)⟩,True.intro⟩

def sumOneLeft (count result : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) (weakenCtx Γ zero))) count) result)) :
    ProofSyntax Const Δ (.eq result (.app (weakenCtx Γ successor) count)) := by
  apply ProofSyntax.exE (sumLeftSuccessor successor zero (weakenCtx Γ zero) count result present)
  let body := Term.and (.eq (weaken result) (.app (weakenCtx _ successor) (.var .vz)))
    (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (weakenCtx Γ zero))) (weaken count)) (.var .vz))
  have diagonal : ProofSyntax Const (body :: weakenHyps Δ)
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weakenCtx _ zero)) (weaken count)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.andER (.hyp (Δ := body :: weakenHyps Δ) 0))
    simp only [weaken,rename_weakenCtx]
  let same := sumZeroReflect successor zero (weaken count) (.var .vz) diagonal
  apply ProofSyntax.castIndices rfl ?_ (.eqTrans (.andEL (.hyp (Δ := body :: weakenHyps Δ) 0))
    (.eqAppArg (weakenCtx _ successor) (.eqSymm same)))
  simp only [weaken,HOL.rename,rename_weakenCtx]

theorem sumOneLeft_free (count result : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) (weakenCtx Γ zero))) count) result))
    (free : present.FunctionExtensionalityFree) : (sumOneLeft successor zero count result present).FunctionExtensionalityFree := by
  unfold sumOneLeft
  refine ⟨sumLeftSuccessor_free _ _ _ _ _ present free,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨True.intro,?_⟩
  apply sumZeroReflect_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

#print axioms sumZeroCount_free
#print axioms sumOneLeft_free

def lessOne (point : Term Const Γ number) (arithmetic : PeanoEvidence successor zero Δ)
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) point)
      (.app (weakenCtx Γ successor) (weakenCtx Γ zero)))) :
    ProofSyntax Const Δ (.eq point (weakenCtx Γ zero)) := by
  apply ProofSyntax.orE (NaturalConstructorCases.fromInduction zero successor point arithmetic.induction)
  · exact .hyp 0
  · let predecessor : Formula Const Γ := .ex (.eq (weaken point) (.app (weakenCtx _ successor) (.var .vz)))
    apply ProofSyntax.exE (.hyp (Δ := predecessor :: Δ) 0)
    let same : Formula Const (number :: Γ) := .eq (weaken point) (.app (weakenCtx _ successor) (.var .vz))
    let assumptions := same :: weakenHyps (predecessor :: Δ)
    let current := ((arithmetic.prepend predecessor).rename Rename.weaken).prepend same
    have oldBound : ProofSyntax Const assumptions
        (.app (.app (weakenCtx _ (less successor)) (weaken point)) (.app (weakenCtx _ successor) (weakenCtx _ zero))) := by
      apply ProofSyntax.castIndices rfl ?_ (((bounded.prepend predecessor).rename Rename.weaken).prepend same)
      simp only [HOL.rename,rename_weakenCtx]
      rfl
    have shifted := ProofSyntax.impE (.eqPropEL (.eqApp (.app (weakenCtx _ successor) (weakenCtx _ zero))
      (.eqAppArg (weakenCtx _ (less successor)) (.hyp (Δ := assumptions) 0)))) oldBound
    exact .botE (lessZeroRefute successor zero (.var .vz) current.separation
      (lessSuccessorCancel successor (.var .vz) (weakenCtx _ zero) current.injectivity shifted))

theorem lessOne_free (point : Term Const Γ number) (arithmetic : PeanoEvidence successor zero Δ)
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) point)
      (.app (weakenCtx Γ successor) (weakenCtx Γ zero))))
    (arithmeticFree : arithmetic.Free) (boundedFree : bounded.FunctionExtensionalityFree) :
    (lessOne successor zero point arithmetic bounded).FunctionExtensionalityFree := by
  unfold lessOne
  refine ⟨NaturalConstructorCases.fromInduction_free _ _ _ _ arithmeticFree.2.2,True.intro,True.intro,?_⟩
  apply lessZeroRefute_free
  · exact ((((arithmetic.prepend _).rename _).prepend_free _
      ((arithmetic.prepend _).rename_free _ (arithmetic.prepend_free _ arithmeticFree)))).1
  · apply lessSuccessorCancel_free
    · exact ((((arithmetic.prepend _).rename _).prepend_free _
        ((arithmetic.prepend _).rename_free _ (arithmetic.prepend_free _ arithmeticFree)))).2.1
    · refine ⟨True.intro,?_⟩
      simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using boundedFree

#print axioms lessOne_free
end Mettapedia.Logic.HOL.SuccessorOrder
