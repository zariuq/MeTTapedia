import Mettapedia.Logic.HOL.VectorTabulationGuard
import Mettapedia.Logic.HOL.IndexedVectorPositions
import Mettapedia.Logic.HOL.NaturalConstructorCases
import Mettapedia.Logic.HOL.IndexedVectorLookupCongruence

/-!
# Ordered lookup in the actual tabulated vector

The invariant quantifies the source array and requested position at each
length. Its conclusion names the original array value at that same position.
Arithmetic premises remain separate from the two computation premises of the
selected tabulator. No supplied vector or total array-decoding law is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorTabulation.Shifted
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
  (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}

def lookupPoint (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number) : Formula Const Γ :=
  IndexedVectorPositions.lookup signature length (.app function array) position (.app array position)

@[simp] theorem lookupPoint_subst (images : Subst Const Γ Ξ)
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number) :
    HOL.subst images (lookupPoint signature length function array position) =
      lookupPoint signature (HOL.subst images length) (HOL.subst images function)
        (HOL.subst images array) (HOL.subst images position) := by
  simp only [lookupPoint,IndexedVectorPositions.lookup_subst,HOL.subst]

theorem lookupPoint_rename (rho : Rename Base Γ Ξ)
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number) :
    HOL.rename rho (lookupPoint signature length function array position) =
      lookupPoint signature (HOL.rename rho length) (HOL.rename rho function)
        (HOL.rename rho array) (HOL.rename rho position) := by
  simpa only [subst_ofRename] using lookupPoint_subst signature (Subst.ofRename rho) length function array position

def lookupProperty (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    Formula Const Γ :=
  .all (.all (.imp
    (.app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (.var .vz)) (weaken (weaken length)))
    (lookupPoint signature (weaken (weaken length)) (weaken (weaken function)) (.var (.vs .vz)) (.var .vz))))

@[simp] theorem lookupProperty_subst (images : Subst Const Γ Ξ)
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    HOL.subst images (lookupProperty signature length function) =
      lookupProperty signature (HOL.subst images length) (HOL.subst images function) := by
  simp only [lookupProperty,HOL.subst,subst_weakenCtx,subst_weaken,lookupPoint_subst,Subst.lift]
  rfl

theorem lookupProperty_rename (rho : Rename Base Γ Ξ)
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    HOL.rename rho (lookupProperty signature length function) =
      lookupProperty signature (HOL.rename rho length) (HOL.rename rho function) := by
  simpa only [subst_ofRename] using lookupProperty_subst signature (Subst.ofRename rho) length function

def lookupFamily : Term Const Γ (signature.number ⇒ Result signature ⇒ .prop) :=
  .lam (.lam (lookupProperty signature (.var (.vs .vz)) (.var .vz)))

@[simp] theorem lookupFamily_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (lookupFamily (Γ := Γ) signature) = lookupFamily (Γ := Ξ) signature := by
  simp only [lookupFamily,HOL.subst,lookupProperty_subst,Subst.lift]
  rfl

theorem lookupFamily_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (lookupFamily (Γ := Γ) signature) = lookupFamily (Γ := Ξ) signature := by
  simpa only [subst_ofRename] using lookupFamily_subst signature (Subst.ofRename rho)

variable {Δ : List (Formula Const Γ)}

def lookupAt (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (present : ProofSyntax Const Δ (lookupProperty signature length function)) :
    ProofSyntax Const Δ (.imp (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) length)
      (lookupPoint signature length function array position)) := by
  have atArray : ProofSyntax Const Δ (.all (.imp
      (.app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (.var .vz)) (weaken length))
      (lookupPoint signature (weaken length) (weaken function) (weaken array) (.var .vz)))) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE array present)
    simp only [instantiate,HOL.subst,subst_weakenCtx,subst_weaken,lookupPoint_subst,
      PredicateFixedPoint.subst_single_weaken,Subst.single,Subst.lift]
    rfl
  apply ProofSyntax.castIndices rfl ?_ (.allE position atArray)
  simp only [instantiate,HOL.subst,subst_weakenCtx,lookupPoint_subst,
    PredicateFixedPoint.subst_single_weaken,Subst.single]

def lookupFamily_apply (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    ProofSyntax Const Δ (.eq (NaturalRecursionProofs.holds (lookupFamily signature) length function)
      (lookupProperty signature length function)) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2
    (lookupProperty signature (.var (.vs .vz)) (.var .vz)) length function)
  simp only [lookupFamily,NaturalRecursionProofs.holds,instantiate,lookupProperty_subst,HOL.subst,Subst.single,Subst.lift]
  apply congrArg (fun value : Term Const Γ signature.number => Term.eq
    (.app (.app (lookupFamily signature) length) function) (lookupProperty signature value function))
  exact instantiate_weaken function length

def lookupProperty_start
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor))) :
    ProofSyntax Const Δ (lookupProperty signature (weakenCtx Γ signature.zero) (start signature)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.botE
  let bound : Formula Const (signature.number :: Array signature :: Γ) :=
    .app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (.var .vz))
      (weaken (weaken (weakenCtx Γ signature.zero)))
  have law : ProofSyntax Const (bound :: weakenHyps (σ := signature.number) (weakenHyps Δ))
      (NaturalNumeralProofs.separation (weakenCtx _ signature.zero) (weakenCtx _ signature.successor)) := by
    apply ProofSyntax.castIndices rfl ?_ (((separate.rename Rename.weaken).rename Rename.weaken).prepend bound)
    simp only [NaturalNumeralProofs.separation,HOL.rename,Rename.lift,weaken,rename_weakenCtx]
  apply SuccessorOrder.lessZeroRefute signature.successor signature.zero (.var .vz) law
  apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := bound :: weakenHyps (σ := signature.number) (weakenHyps Δ)) 0)
  change bound = _
  simp only [bound,weaken,rename_weakenCtx]

def lookupBase
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor))) :
    ProofSyntax Const Δ (NaturalRecursionProofs.holds (lookupFamily signature)
      (weakenCtx Γ signature.zero) (start signature)) :=
  .impE (.eqPropER (lookupFamily_apply signature _ _)) (lookupProperty_start signature separate)

def lookupZeroAt (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (same : ProofSyntax Const Δ (.eq position (weakenCtx Γ signature.zero))) :
    ProofSyntax Const Δ (lookupPoint signature (.app (weakenCtx Γ signature.successor) length)
      (.app (.app (method signature) previous) length) array position) := by
  have here := IndexedVectorPositions.here (Δ := Δ) signature length (.app array (weakenCtx Γ signature.zero))
    (.app previous (shift signature array))
  have atZero := ProofSyntax.impE (.eqPropER (IndexedVectorPositions.lookup_vec_eq signature
    (.app (weakenCtx Γ signature.successor) length)
    (.app (.app (.app (method signature) previous) length) array) _ (weakenCtx Γ signature.zero)
    (.app array (weakenCtx Γ signature.zero)) (method_apply signature previous length array))) here
  exact .impE (.eqPropER (IndexedVectorPositions.lookup_arrayAt_eq signature
    (.app (weakenCtx Γ signature.successor) length) _ array position (weakenCtx Γ signature.zero) same)) atZero

def lookupSuccessorAt (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (prior : ProofSyntax Const Δ (lookupProperty signature length previous))
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) length)) :
    ProofSyntax Const Δ (lookupPoint signature (.app (weakenCtx Γ signature.successor) length)
      (.app (.app (method signature) previous) length) array (.app (weakenCtx Γ signature.successor) position)) := by
  have child := ProofSyntax.impE (lookupAt signature length previous (shift signature array) position prior) bound
  have child' := ProofSyntax.impE (.eqPropEL (IndexedVectorPositions.lookup_element_eq signature length
    (.app previous (shift signature array)) position (.app (shift signature array) position)
    (.app array (.app (weakenCtx Γ signature.successor) position)) (shift_apply signature array position))) child
  have later := IndexedVectorPositions.there signature length (.app array (weakenCtx Γ signature.zero))
    (.app previous (shift signature array)) position (.app array (.app (weakenCtx Γ signature.successor) position)) child'
  exact .impE (.eqPropER (IndexedVectorPositions.lookup_vec_eq signature
    (.app (weakenCtx Γ signature.successor) length)
    (.app (.app (.app (method signature) previous) length) array) _
    (.app (weakenCtx Γ signature.successor) position) (.app array (.app (weakenCtx Γ signature.successor) position))
    (method_apply signature previous length array))) later

def lookupByBound (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ)
    (prior : ProofSyntax Const Δ (lookupProperty signature length previous))
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position)
      (.app (weakenCtx Γ signature.successor) length))) :
    ProofSyntax Const Δ (lookupPoint signature (.app (weakenCtx Γ signature.successor) length)
      (.app (.app (method signature) previous) length) array position) := by
  apply ProofSyntax.orE (NaturalConstructorCases.fromInduction signature.zero signature.successor position arithmetic.induction)
  · exact lookupZeroAt signature length previous array position (.hyp 0)
  · let existsEquation : Formula Const Γ := .ex (.eq (weaken position)
      (.app (weakenCtx _ signature.successor) (.var .vz)))
    apply ProofSyntax.exE (.hyp (Δ := existsEquation :: Δ) 0)
    let body : Formula Const (signature.number :: Γ) := .eq (weaken position)
      (.app (weakenCtx _ signature.successor) (.var .vz))
    let hypotheses := body :: weakenHyps (existsEquation :: Δ)
    have same : ProofSyntax Const hypotheses body := .hyp 0
    have arithmetic' : SuccessorOrder.PeanoEvidence signature.successor signature.zero hypotheses :=
      ((arithmetic.prepend existsEquation).rename Rename.weaken).prepend body
    have inherited : ProofSyntax Const hypotheses
        (lookupProperty signature (weaken length) (weaken previous)) :=
      .castIndices rfl (lookupProperty_rename signature Rename.weaken length previous)
        (((prior.prepend existsEquation).rename Rename.weaken).prepend body)
    have originalBound : ProofSyntax Const hypotheses
        (.app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (weaken position))
          (.app (weakenCtx _ signature.successor) (weaken length))) := by
      apply ProofSyntax.castIndices rfl ?_ (((bound.prepend existsEquation).rename Rename.weaken).prepend body)
      simp only [weaken,HOL.rename,rename_weakenCtx]
    have movedBound := ProofSyntax.impE (.eqPropEL (.eqApp
      (.app (weakenCtx _ signature.successor) (weaken length))
      (.eqAppArg (weakenCtx _ (SuccessorOrder.less signature.successor)) same))) originalBound
    have smaller := SuccessorOrder.lessSuccessorCancel signature.successor (.var .vz) (weaken length)
      arithmetic'.injectivity movedBound
    have later := lookupSuccessorAt signature (weaken length) (weaken previous) (weaken array) (.var .vz) inherited smaller
    have transferred := ProofSyntax.impE (.eqPropER (IndexedVectorPositions.lookup_arrayAt_eq signature
      (.app (weakenCtx _ signature.successor) (weaken length))
      (.app (.app (.app (method signature) (weaken previous)) (weaken length)) (weaken array))
      (weaken array) (weaken position) (.app (weakenCtx _ signature.successor) (.var .vz)) same)) later
    apply ProofSyntax.castIndices rfl ?_ transferred
    simp only [lookupPoint,weaken,IndexedVectorPositions.lookup_rename,HOL.rename,rename_weakenCtx,method_rename]

def lookupProperty_next (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ)
    (prior : ProofSyntax Const Δ (lookupProperty signature length previous)) :
    ProofSyntax Const Δ (lookupProperty signature (.app (weakenCtx Γ signature.successor) length)
      (.app (.app (method signature) previous) length)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let bound : Formula Const (signature.number :: Array signature :: Γ) :=
    .app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (.var .vz))
      (weaken (weaken (.app (weakenCtx Γ signature.successor) length)))
  let hypotheses := bound :: weakenHyps (σ := signature.number) (weakenHyps Δ)
  have arithmetic' : SuccessorOrder.PeanoEvidence signature.successor signature.zero hypotheses :=
    ((arithmetic.rename Rename.weaken).rename Rename.weaken).prepend bound
  have inherited : ProofSyntax Const hypotheses
      (lookupProperty signature (weaken (weaken length)) (weaken (weaken previous))) := by
    apply ProofSyntax.castIndices rfl ?_ (((prior.rename Rename.weaken).rename Rename.weaken).prepend bound)
    simp only [lookupProperty_rename,weaken]
  have present : ProofSyntax Const hypotheses
      (.app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (.var .vz))
        (.app (weakenCtx _ signature.successor) (weaken (weaken length)))) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    change bound = _
    simp only [bound,weaken,HOL.rename,rename_weakenCtx]
  apply ProofSyntax.castIndices rfl ?_
    (lookupByBound signature (weaken (weaken length)) (weaken (weaken previous))
      (.var (.vs .vz)) (.var .vz) arithmetic' inherited present)
  simp only [lookupPoint,weaken,HOL.rename,rename_weakenCtx,method_rename]

def lookupStep (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ) :
    ProofSyntax Const Δ (NaturalRecursionProofs.methodPreserves
      (weakenCtx Γ signature.successor) (method signature) (lookupFamily signature)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let hypothesis : Formula Const (Result signature :: signature.number :: Γ) :=
    NaturalRecursionProofs.holds (weaken (weaken (lookupFamily signature))) (.var (.vs .vz)) (.var .vz)
  let hypotheses := hypothesis :: weakenHyps (σ := Result signature) (weakenHyps Δ)
  have arithmetic' : SuccessorOrder.PeanoEvidence signature.successor signature.zero hypotheses :=
    ((arithmetic.rename Rename.weaken).rename Rename.weaken).prepend hypothesis
  have prior : ProofSyntax Const hypotheses (lookupProperty signature (.var (.vs .vz)) (.var .vz)) := by
    apply ProofSyntax.impE (.eqPropEL (lookupFamily_apply signature (.var (.vs .vz)) (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    change hypothesis = _
    simp only [hypothesis,weaken,lookupFamily_rename]
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (lookupFamily_apply signature
      (.app (weakenCtx _ signature.successor) (.var (.vs .vz)))
      (.app (.app (method signature) (.var .vz)) (.var (.vs .vz)))))
      (lookupProperty_next signature (.var (.vs .vz)) (.var .vz) arithmetic' prior))
  simp only [NaturalRecursionProofs.holds,weaken,lookupFamily_rename,method_rename,rename_weakenCtx]

def lookup (selection : ClosedTerm Const (Selection signature))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (position : Term Const Γ signature.number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (Result signature)))
    (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ)
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) length)) :
    ProofSyntax Const Δ (IndexedVectorPositions.lookup signature length (tabulate signature selection length array)
      position (.app array position)) := by
  have every := NaturalRecursionProofs.dependent (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
    (weakenCtx Γ signature.successor) (start signature) (method signature) (lookupFamily signature)
    choice recursion arithmetic.induction (lookupBase signature arithmetic.separation) (lookupStep signature arithmetic)
  have atLength : ProofSyntax Const Δ (NaturalRecursionProofs.holds (lookupFamily signature) length
      (.app (recursor signature selection) length)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE length every)
    simp only [NaturalRecursionProofs.holds,instantiate,HOL.subst,
      PredicateFixedPoint.subst_single_weaken,Subst.single]
    rfl
  exact .impE (lookupAt signature length (.app (recursor signature selection) length) array position
    (.impE (.eqPropEL (lookupFamily_apply signature _ _)) atLength)) bound

theorem lookupAt_free (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (present : ProofSyntax Const Δ (lookupProperty signature length function)) (free : present.FunctionExtensionalityFree) :
    (lookupAt signature length function array position present).FunctionExtensionalityFree := by
  simpa only [lookupAt,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree] using free

theorem lookupFamily_apply_free (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    (lookupFamily_apply (Δ := Δ) signature length function).FunctionExtensionalityFree := by
  unfold lookupFamily_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

theorem lookupProperty_start_free
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (free : separate.FunctionExtensionalityFree) :
    (lookupProperty_start signature separate).FunctionExtensionalityFree := by
  simp only [lookupProperty_start,ProofSyntax.FunctionExtensionalityFree]
  apply SuccessorOrder.lessZeroRefute_free
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

theorem lookupBase_free
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (free : separate.FunctionExtensionalityFree) :
    (lookupBase signature separate).FunctionExtensionalityFree :=
  ⟨lookupFamily_apply_free _ _ _,lookupProperty_start_free _ _ free⟩

theorem lookupZeroAt_free (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (same : ProofSyntax Const Δ (.eq position (weakenCtx Γ signature.zero)))
    (sameFree : same.FunctionExtensionalityFree) :
    (lookupZeroAt signature length previous array position same).FunctionExtensionalityFree := by
  unfold lookupZeroAt
  exact ⟨IndexedVectorPositions.lookup_arrayAt_eq_free _ _ _ _ _ _ _ sameFree,
    IndexedVectorPositions.lookup_vec_eq_free _ _ _ _ _ _ _ (method_apply_free _ _ _ _),
    IndexedVectorPositions.here_free _ _ _ _⟩

theorem lookupSuccessorAt_free (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (prior : ProofSyntax Const Δ (lookupProperty signature length previous))
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) length))
    (priorFree : prior.FunctionExtensionalityFree) (boundFree : bound.FunctionExtensionalityFree) :
    (lookupSuccessorAt signature length previous array position prior bound).FunctionExtensionalityFree := by
  unfold lookupSuccessorAt
  refine ⟨IndexedVectorPositions.lookup_vec_eq_free _ _ _ _ _ _ _ (method_apply_free _ _ _ _),?_⟩
  apply IndexedVectorPositions.there_free
  exact ⟨IndexedVectorPositions.lookup_element_eq_free _ _ _ _ _ _ _ (shift_apply_free _ _ _),
    lookupAt_free _ _ _ _ _ _ priorFree,boundFree⟩

theorem lookupByBound_free (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number)
    (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ)
    (prior : ProofSyntax Const Δ (lookupProperty signature length previous))
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position)
      (.app (weakenCtx Γ signature.successor) length)))
    (arithmeticFree : arithmetic.Free) (priorFree : prior.FunctionExtensionalityFree)
    (boundFree : bound.FunctionExtensionalityFree) :
    (lookupByBound signature length previous array position arithmetic prior bound).FunctionExtensionalityFree := by
  simp only [lookupByBound,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  refine ⟨NaturalConstructorCases.fromInduction_free _ _ _ _ arithmeticFree.2.2,
    lookupZeroAt_free _ _ _ _ _ _ True.intro,True.intro,?_,?_⟩
  · exact IndexedVectorPositions.lookup_arrayAt_eq_free _ _ _ _ _ _ _ True.intro
  · apply lookupSuccessorAt_free
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using priorFree
    · apply SuccessorOrder.lessSuccessorCancel_free
      · simpa only [SuccessorOrder.PeanoEvidence.prepend,SuccessorOrder.PeanoEvidence.rename,
          ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
          ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using arithmeticFree.2.1
      · exact ⟨True.intro,by simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
          ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using boundFree⟩

theorem lookupProperty_next_free (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ)
    (prior : ProofSyntax Const Δ (lookupProperty signature length previous))
    (arithmeticFree : arithmetic.Free) (priorFree : prior.FunctionExtensionalityFree) :
    (lookupProperty_next signature length previous arithmetic prior).FunctionExtensionalityFree := by
  simp only [lookupProperty_next,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  apply lookupByBound_free
  · exact ((arithmetic.rename Rename.weaken).rename Rename.weaken).prepend_free _
      ((arithmetic.rename Rename.weaken).rename_free _ (arithmetic.rename_free _ arithmeticFree))
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using priorFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

theorem lookupStep_free (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ)
    (free : arithmetic.Free) : (lookupStep signature arithmetic).FunctionExtensionalityFree := by
  simp only [lookupStep,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  refine ⟨lookupFamily_apply_free _ _ _,lookupProperty_next_free _ _ _ _ _ ?_ ?_⟩
  · exact ((arithmetic.rename Rename.weaken).rename Rename.weaken).prepend_free _
      ((arithmetic.rename Rename.weaken).rename_free _ (arithmetic.rename_free _ free))
  · exact ⟨lookupFamily_apply_free _ _ _,by simp only [ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.FunctionExtensionalityFree]⟩

theorem lookup_free (selection : ClosedTerm Const (Selection signature))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (position : Term Const Γ signature.number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (Result signature)))
    (arithmetic : SuccessorOrder.PeanoEvidence signature.successor signature.zero Δ)
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) length))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (boundFree : bound.FunctionExtensionalityFree) :
    (lookup signature selection length array position choice recursion arithmetic bound).FunctionExtensionalityFree := by
  have dependentFree : (NaturalRecursionProofs.dependent (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) (start signature) (method signature) (lookupFamily signature)
      choice recursion arithmetic.induction (lookupBase signature arithmetic.separation) (lookupStep signature arithmetic)).FunctionExtensionalityFree := by
    unfold NaturalRecursionProofs.dependent
    exact NaturalRecursionProofs.invariant_free _ _ _ _ _ _ _ _ _ _ arithmeticFree.2.2
      (NaturalRecursionProofs.computation_free _ _ _ _ _ _ _ choiceFree recursionFree)
      (lookupBase_free _ _ arithmeticFree.1) (lookupStep_free _ _ arithmeticFree)
  simpa only [lookup,lookupAt,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree,lookupFamily_apply_free,true_and] using And.intro dependentFree boundFree

#print axioms lookupBase
#print axioms lookup
#print axioms lookup_free
end Mettapedia.Logic.HOL.VectorTabulation.Shifted
