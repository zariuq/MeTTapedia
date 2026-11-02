import Mettapedia.Logic.HOL.OrderedMixedPositionCoverage
import Mettapedia.Logic.HOL.SuccessorOrderUnitSegments

/-!
# Exact region and index readback for mixed ordered positions

The scalar/vector/scalar plan is read into leading, interior or trailing
addresses. Every branch retains its original child-index equality. Unit
segments are reduced by retained arithmetic proofs, not host normalization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
open SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))
    {Δ : List (Formula Const Γ)}

def unitReadback (label : Term Const Γ index) (slot : Term Const Γ number) (target : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero Δ)
    (related : ProofSyntax Const Δ (compileAt zero successor
      [(.app (weakenCtx Γ successor) (weakenCtx Γ zero),label)] Subst.id slot target)) :
    ProofSyntax Const Δ (.and (.eq slot (weakenCtx Γ zero)) (.eq target label)) := by
  have normalized : ProofSyntax Const Δ (.or
      (.and (.app (.app (weakenCtx Γ (less successor)) slot) (.app (weakenCtx Γ successor) (weakenCtx Γ zero))) (.eq target label))
      (.ex (.and (.app (.app (.app (weakenCtx _ (sum zero successor))
        (weaken (.app (weakenCtx Γ successor) (weakenCtx Γ zero)))) (.var .vz)) (weaken slot)) .bot))) := by
    apply ProofSyntax.castIndices rfl ?_ related
    simp only [compileAt,subst_id]
  apply ProofSyntax.orE normalized
  · have bounded : ProofSyntax Const
        ((.and (.app (.app (weakenCtx Γ (less successor)) slot)
          (.app (weakenCtx Γ successor) (weakenCtx Γ zero))) (.eq target label)) :: Δ)
        (.app (.app (weakenCtx Γ (less successor)) slot) (.app (weakenCtx Γ successor) (weakenCtx Γ zero))) := .andEL (.hyp 0)
    exact .andI (lessOne successor zero slot (arithmetic.prepend _) bounded) (.andER (.hyp 0))
  · apply ProofSyntax.exE (.hyp 0)
    exact .botE (.andER (.hyp 0))

theorem unitReadback_free (label : Term Const Γ index) (slot : Term Const Γ number) (target : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero Δ)
    (related : ProofSyntax Const Δ (compileAt zero successor
      [(.app (weakenCtx Γ successor) (weakenCtx Γ zero),label)] Subst.id slot target))
    (arithmeticFree : arithmetic.Free) (relatedFree : related.FunctionExtensionalityFree) :
    (unitReadback zero successor label slot target arithmetic related).FunctionExtensionalityFree := by
  unfold unitReadback
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr relatedFree,
    ⟨lessOne_free _ _ _ _ _ (arithmetic.prepend_free _ arithmeticFree) trivial,True.intro⟩,
    ⟨True.intro,True.intro⟩⟩

def tailCases (length slot : Term Const Γ number) (vectorIndex lastIndex target : Term Const Γ index) : Formula Const Γ :=
  .or (.and (.app (.app (weakenCtx Γ (less successor)) slot) length) (.eq target vectorIndex))
    (.and (.eq slot length) (.eq target lastIndex))

theorem tailCases_rename (rho : Rename Base Γ Ξ) (length slot : Term Const Γ number)
    (vectorIndex lastIndex target : Term Const Γ index) :
    HOL.rename rho (tailCases successor length slot vectorIndex lastIndex target) =
      tailCases successor (HOL.rename rho length) (HOL.rename rho slot)
        (HOL.rename rho vectorIndex) (HOL.rename rho lastIndex) (HOL.rename rho target) := by
  simp only [tailCases,HOL.rename,rename_weakenCtx]

def tailReadback (length slot : Term Const Γ number) (vectorIndex lastIndex target : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero Δ)
    (related : ProofSyntax Const Δ (compileAt zero successor
      [(length,vectorIndex),(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)] Subst.id slot target)) :
    ProofSyntax Const Δ (tailCases successor length slot vectorIndex lastIndex target) := by
  let later : Formula Const Γ := .ex (.and
    (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken length)) (.var .vz)) (weaken slot))
    (compileAt zero successor [(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)]
      (fun entry => weaken (Subst.id entry)) (.var .vz) (weaken target)))
  have normalized : ProofSyntax Const Δ (.or
      (.and (.app (.app (weakenCtx Γ (less successor)) slot) length) (.eq target vectorIndex)) later) := by
    apply ProofSyntax.castIndices rfl ?_ related
    change Term.or _ _ = Term.or _ _
    simp only [subst_id]
    rfl
  apply ProofSyntax.orE normalized
  · exact .orIL (.hyp 0)
  · apply ProofSyntax.exE (.hyp (Δ := later :: Δ) 0)
    let sumBody : Formula Const (number :: Γ) :=
      .app (.app (.app (weakenCtx _ (sum zero successor)) (weaken length)) (.var .vz)) (weaken slot)
    let remaining := compileAt zero successor [(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)]
      (fun entry => weaken (Subst.id entry)) (.var .vz) (weaken target)
    let body := Term.and sumBody remaining
    let assumptions := body :: weakenHyps (later :: Δ)
    let current := ((arithmetic.prepend later).rename Rename.weaken).prepend body
    have unit : ProofSyntax Const assumptions
        (compileAt zero successor [(.app (weakenCtx _ successor) (weakenCtx _ zero),weaken lastIndex)]
          Subst.id (.var .vz) (weaken target)) := by
      apply ProofSyntax.castIndices rfl ?_ (.andER (.hyp (Δ := assumptions) 0))
      have mapWeak {type : Ty Base} (term : Term Const Γ type) :
          HOL.subst (fun entry => weaken (Subst.id entry)) term = weaken (σ := number) term := by
        change HOL.subst (Subst.ofRename Rename.weaken) term = weaken term
        exact subst_ofRename _ _
      simp only [remaining,compileAt,HOL.subst,Subst.id,HOL.subst_id,subst_weakenCtx]
      rw [show HOL.subst (fun entry => weaken (Term.var entry)) lastIndex = weaken (σ := number) lastIndex from mapWeak lastIndex]
    let selected := unitReadback zero successor (weaken lastIndex) (.var .vz) (weaken target) current unit
    have shifted : ProofSyntax Const assumptions
        (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken length)) (weakenCtx _ zero)) (weaken slot)) :=
      .impE (.eqPropEL (.eqApp (weaken slot)
        (.eqAppArg (.app (weakenCtx _ (sum zero successor)) (weaken length)) (.andEL selected))))
        (.andEL (.hyp 0))
    let equal := sumZeroCount successor zero (weaken length) (weaken slot) current.separation shifted
    apply ProofSyntax.castIndices rfl ?_ (.orIR (φ := .and
        (.app (.app (weakenCtx _ (less successor)) (weaken slot)) (weaken length)) (.eq (weaken target) (weaken vectorIndex)))
      (.andI equal (.andER selected)))
    exact (tailCases_rename successor Rename.weaken length slot vectorIndex lastIndex target).symm

theorem tailReadback_free (length slot : Term Const Γ number) (vectorIndex lastIndex target : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero Δ)
    (related : ProofSyntax Const Δ (compileAt zero successor
      [(length,vectorIndex),(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)] Subst.id slot target))
    (arithmeticFree : arithmetic.Free) (relatedFree : related.FunctionExtensionalityFree) :
    (tailReadback zero successor length slot vectorIndex lastIndex target arithmetic related).FunctionExtensionalityFree := by
  unfold tailReadback
  refine ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr relatedFree,True.intro,True.intro,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨?_,?_⟩
  · apply sumZeroCount_free
    · exact ((((arithmetic.prepend _).rename _).prepend_free _
        ((arithmetic.prepend _).rename_free _ (arithmetic.prepend_free _ arithmeticFree)))).1
    · refine ⟨?_,True.intro⟩
      apply unitReadback_free
      · exact (((arithmetic.prepend _).rename _).prepend_free _
          ((arithmetic.prepend _).rename_free _ (arithmetic.prepend_free _ arithmeticFree)))
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial
  · apply unitReadback_free
    · exact (((arithmetic.prepend _).rename _).prepend_free _
        ((arithmetic.prepend _).rename_free _ (arithmetic.prepend_free _ arithmeticFree)))
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial

#print axioms unitReadback_free
#print axioms tailReadback_free

def mixedCases (length slot : Term Const Γ number) (firstIndex vectorIndex lastIndex target : Term Const Γ index) : Formula Const Γ :=
  .or (.and (.eq slot (weakenCtx Γ zero)) (.eq target firstIndex))
    (.or (.ex (.and (.eq (weaken slot) (.app (weakenCtx _ successor) (.var .vz)))
      (.and (.app (.app (weakenCtx _ (less successor)) (.var .vz)) (weaken length))
        (.eq (weaken target) (weaken vectorIndex)))))
      (.and (.eq slot (.app (weakenCtx Γ successor) length)) (.eq target lastIndex)))

theorem mixedCases_subst (images : Subst Const Γ Ξ) (length slot : Term Const Γ number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ index) :
    HOL.subst images (mixedCases zero successor length slot firstIndex vectorIndex lastIndex target) =
      mixedCases zero successor (HOL.subst images length) (HOL.subst images slot) (HOL.subst images firstIndex)
        (HOL.subst images vectorIndex) (HOL.subst images lastIndex) (HOL.subst images target) := by
  simp only [mixedCases,HOL.subst,subst_weakenCtx,subst_weaken,Subst.lift]

theorem mixedCases_rename (rho : Rename Base Γ Ξ) (length slot : Term Const Γ number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ index) :
    HOL.rename rho (mixedCases zero successor length slot firstIndex vectorIndex lastIndex target) =
      mixedCases zero successor (HOL.rename rho length) (HOL.rename rho slot) (HOL.rename rho firstIndex)
        (HOL.rename rho vectorIndex) (HOL.rename rho lastIndex) (HOL.rename rho target) := by
  simpa only [subst_ofRename] using mixedCases_subst zero successor (Subst.ofRename rho) length slot firstIndex vectorIndex lastIndex target

def mixedInteriorIntro (length slot offset : Term Const Γ number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ index)
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ successor) offset)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) offset) length))
    (label : ProofSyntax Const Δ (.eq target vectorIndex)) :
    ProofSyntax Const Δ (mixedCases zero successor length slot firstIndex vectorIndex lastIndex target) := by
  apply ProofSyntax.orIR
  apply ProofSyntax.orIL
  apply ProofSyntax.exI offset
  apply ProofSyntax.castIndices rfl ?_ (.andI address (.andI bounded label))
  simp only [instantiate,HOL.subst,subst_weakenCtx,PredicateFixedPoint.subst_single_weaken,Subst.single]

theorem mixedInteriorIntro_free (length slot offset : Term Const Γ number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ index)
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ successor) offset)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) offset) length))
    (label : ProofSyntax Const Δ (.eq target vectorIndex))
    (addressFree : address.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree)
    (labelFree : label.FunctionExtensionalityFree) :
    (mixedInteriorIntro zero successor length slot offset firstIndex vectorIndex lastIndex target address bounded label).FunctionExtensionalityFree := by
  unfold mixedInteriorIntro
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr ⟨addressFree,boundedFree,labelFree⟩

def mixedFromTail (length slot offset : Term Const Γ number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ index)
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ successor) offset)))
    (tail : ProofSyntax Const Δ (tailCases successor length offset vectorIndex lastIndex target)) :
    ProofSyntax Const Δ (mixedCases zero successor length slot firstIndex vectorIndex lastIndex target) :=
  .orE tail
    (mixedInteriorIntro zero successor length slot offset firstIndex vectorIndex lastIndex target
      (address.prepend _) (.andEL (.hyp 0)) (.andER (.hyp 0)))
    (.orIR (.orIR (.andI (.eqTrans (address.prepend _) (.eqAppArg (weakenCtx Γ successor) (.andEL (.hyp 0))))
      (.andER (.hyp 0)))))

theorem mixedFromTail_free (length slot offset : Term Const Γ number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ index)
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ successor) offset)))
    (tail : ProofSyntax Const Δ (tailCases successor length offset vectorIndex lastIndex target))
    (addressFree : address.FunctionExtensionalityFree) (tailFree : tail.FunctionExtensionalityFree) :
    (mixedFromTail zero successor length slot offset firstIndex vectorIndex lastIndex target address tail).FunctionExtensionalityFree := by
  unfold mixedFromTail
  exact ⟨tailFree,mixedInteriorIntro_free _ _ _ _ _ _ _ _ _ _ _ _
    ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr addressFree) trivial trivial,
    ⟨⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr addressFree,True.intro⟩,True.intro⟩⟩

def mixedReadback (length slot : Term Const Γ number) (firstIndex vectorIndex lastIndex target : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero Δ)
    (related : ProofSyntax Const Δ (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id slot target)) :
    ProofSyntax Const Δ (mixedCases zero successor length slot firstIndex vectorIndex lastIndex target) := by
  let later : Formula Const Γ := .ex (.and
    (.app (.app (.app (weakenCtx _ (sum zero successor))
      (weaken (.app (weakenCtx Γ successor) (weakenCtx Γ zero)))) (.var .vz)) (weaken slot))
    (compileAt zero successor [(length,vectorIndex),(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)]
      (fun entry => weaken (Subst.id entry)) (.var .vz) (weaken target)))
  have normalized : ProofSyntax Const Δ (.or
      (.and (.app (.app (weakenCtx Γ (less successor)) slot) (.app (weakenCtx Γ successor) (weakenCtx Γ zero)))
        (.eq target firstIndex)) later) := by
    apply ProofSyntax.castIndices rfl ?_ related
    change Term.or _ _ = Term.or _ _
    simp only [subst_id]
    rfl
  apply ProofSyntax.orE normalized
  · exact .orIL (.andI (lessOne successor zero slot (arithmetic.prepend _) (.andEL (.hyp 0))) (.andER (.hyp 0)))
  · apply ProofSyntax.exE (.hyp (Δ := later :: Δ) 0)
    let sumBody : Formula Const (number :: Γ) := .app (.app (.app (weakenCtx _ (sum zero successor))
      (weaken (.app (weakenCtx Γ successor) (weakenCtx Γ zero)))) (.var .vz)) (weaken slot)
    let remaining := compileAt zero successor [(length,vectorIndex),(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)]
      (fun entry => weaken (Subst.id entry)) (.var .vz) (weaken target)
    let body := Term.and sumBody remaining
    let assumptions := body :: weakenHyps (later :: Δ)
    let current := ((arithmetic.prepend later).rename Rename.weaken).prepend body
    have shifted : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx _ (sum zero successor))
        (.app (weakenCtx _ successor) (weakenCtx _ zero))) (.var .vz)) (weaken slot)) := by
      apply ProofSyntax.castIndices rfl ?_ (.andEL (.hyp (Δ := assumptions) 0))
      simp only [sumBody,weaken,HOL.rename,rename_weakenCtx]
    let address := sumOneLeft successor zero (.var .vz) (weaken slot) shifted
    have tail : ProofSyntax Const assumptions (compileAt zero successor
        [(weaken length,weaken vectorIndex),(.app (weakenCtx _ successor) (weakenCtx _ zero),weaken lastIndex)]
        Subst.id (.var .vz) (weaken target)) := by
      apply ProofSyntax.castIndices rfl ?_ (.andER (.hyp (Δ := assumptions) 0))
      have mapWeak {type : Ty Base} (term : Term Const Γ type) :
          HOL.subst (fun entry => weaken (Subst.id entry)) term = weaken (σ := number) term := by
        change HOL.subst (Subst.ofRename Rename.weaken) term = weaken term
        exact subst_ofRename _ _
      change remaining = _
      have bridge := compileAt_substitute zero successor
        ([(length,vectorIndex),(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)] : Plan Const Γ number index)
        (fun entry => weaken (Subst.id entry)) Subst.id (.var .vz) (weaken target)
      simp only [substitute,List.map_cons,List.map_nil,mapWeak,HOL.subst_id] at bridge
      have comparison := bridge.symm
      simpa only [remaining,weaken,HOL.rename,rename_weakenCtx] using comparison
    apply ProofSyntax.castIndices rfl ?_
      (mixedFromTail zero successor (weaken length) (weaken slot) (.var .vz)
        (weaken firstIndex) (weaken vectorIndex) (weaken lastIndex) (weaken target) address
        (tailReadback zero successor (weaken length) (.var .vz) (weaken vectorIndex) (weaken lastIndex) (weaken target) current tail))
    exact (mixedCases_rename zero successor Rename.weaken length slot firstIndex vectorIndex lastIndex target).symm

#print axioms mixedReadback

theorem mixedReadback_free (length slot : Term Const Γ number) (firstIndex vectorIndex lastIndex target : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero Δ)
    (related : ProofSyntax Const Δ (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id slot target)) (arithmeticFree : arithmetic.Free) (relatedFree : related.FunctionExtensionalityFree) :
    (mixedReadback zero successor length slot firstIndex vectorIndex lastIndex target arithmetic related).FunctionExtensionalityFree := by
  unfold mixedReadback
  refine ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr relatedFree,?_,True.intro,?_⟩
  · exact ⟨lessOne_free _ _ _ _ _ (arithmetic.prepend_free _ arithmeticFree) trivial,True.intro⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply mixedFromTail_free
    · apply sumOneLeft_free
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
    · apply tailReadback_free
      · exact (((arithmetic.prepend _).rename _).prepend_free _
          ((arithmetic.prepend _).rename_free _ (arithmetic.prepend_free _ arithmeticFree)))
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial

#print axioms mixedReadback_free
end Mettapedia.Logic.HOL.OrderedPositionPrograms
