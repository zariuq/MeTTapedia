import Mettapedia.Logic.HOL.VectorTabulationRoundtrip
import Mettapedia.Logic.HOL.FunctionExtensionalityEtaExpansion

/-!
# Observation and extensionality boundaries of vector reconstruction

Pointwise reconstruction supports every stated slot observation without eta.
A supplied, uniformly quantified observation law supports its declared
observer. Whole-array equality instead uses the eta-licensed derived rule;
that particular proof is explicitly outside FunctionExtensionalityFree.
No native conversion policy is inferred from the absence of primitive funExt.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorTabulation.Shifted
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {number element result : Ty Base}

def pointwiseFormula (first second : Term Const Γ (number ⇒ element)) : Formula Const Γ :=
  .all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))

@[simp] theorem pointwiseFormula_subst (images : Subst Const Γ Ξ)
    (first second : Term Const Γ (number ⇒ element)) :
    HOL.subst images (pointwiseFormula first second) =
      pointwiseFormula (HOL.subst images first) (HOL.subst images second) := by
  simp only [pointwiseFormula,HOL.subst,subst_weaken,Subst.lift]

def observationRespects (observer : Term Const Γ ((number ⇒ element) ⇒ result)) : Formula Const Γ :=
  .all (.all (.imp (pointwiseFormula (.var (.vs .vz)) (.var .vz))
    (.eq (.app (weaken (weaken observer)) (.var (.vs .vz)))
      (.app (weaken (weaken observer)) (.var .vz)))))

@[simp] theorem observationRespects_subst (images : Subst Const Γ Ξ)
    (observer : Term Const Γ ((number ⇒ element) ⇒ result)) :
    HOL.subst images (observationRespects observer) = observationRespects (HOL.subst images observer) := by
  simp only [observationRespects,HOL.subst,pointwiseFormula_subst,subst_weaken,Subst.lift]
  rfl

variable {Δ : List (Formula Const Γ)}

def observationAt (observer : Term Const Γ ((number ⇒ element) ⇒ result))
    (first second : Term Const Γ (number ⇒ element))
    (respects : ProofSyntax Const Δ (observationRespects observer)) :
    ProofSyntax Const Δ (.imp (pointwiseFormula first second) (.eq (.app observer first) (.app observer second))) := by
  have atFirst : ProofSyntax Const Δ (.all (.imp (pointwiseFormula (weaken first) (.var .vz))
      (.eq (.app (weaken observer) (weaken first)) (.app (weaken observer) (.var .vz))))) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE first respects)
    simp only [instantiate,HOL.subst,pointwiseFormula_subst,subst_weaken,Subst.single,Subst.lift,
      PredicateFixedPoint.subst_single_weaken]
    rfl
  apply ProofSyntax.castIndices rfl ?_ (.allE second atFirst)
  simp only [instantiate,HOL.subst,pointwiseFormula_subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem observationAt_free (observer : Term Const Γ ((number ⇒ element) ⇒ result))
    (first second : Term Const Γ (number ⇒ element))
    (respects : ProofSyntax Const Δ (observationRespects observer)) (free : respects.FunctionExtensionalityFree) :
    (observationAt observer first second respects).FunctionExtensionalityFree := by
  simpa only [observationAt,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree] using free

def evaluationObserver (position : Term Const Γ number) (operation : Term Const Γ (element ⇒ result)) :
    Term Const Γ ((number ⇒ element) ⇒ result) :=
  .lam (.app (weaken operation) (.app (.var .vz) (weaken position)))

@[simp] theorem evaluationObserver_subst (images : Subst Const Γ Ξ)
    (position : Term Const Γ number) (operation : Term Const Γ (element ⇒ result)) :
    HOL.subst images (evaluationObserver position operation) =
      evaluationObserver (HOL.subst images position) (HOL.subst images operation) := by
  simp only [evaluationObserver,HOL.subst,subst_weaken,Subst.lift]

theorem evaluationObserver_rename (rho : Rename Base Γ Ξ)
    (position : Term Const Γ number) (operation : Term Const Γ (element ⇒ result)) :
    HOL.rename rho (evaluationObserver position operation) =
      evaluationObserver (HOL.rename rho position) (HOL.rename rho operation) := by
  simpa only [subst_ofRename] using evaluationObserver_subst (Subst.ofRename rho) position operation

def evaluationObserver_apply (position : Term Const Γ number) (operation : Term Const Γ (element ⇒ result))
    (array : Term Const Γ (number ⇒ element)) :
    ProofSyntax Const Δ (.eq (.app (evaluationObserver position operation) array) (.app operation (.app array position))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta array (.app (weaken operation) (.app (.var .vz) (weaken position))))
  simp only [evaluationObserver,instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem evaluationObserver_apply_free (position : Term Const Γ number) (operation : Term Const Γ (element ⇒ result))
    (array : Term Const Γ (number ⇒ element)) :
    (evaluationObserver_apply (Δ := Δ) position operation array).FunctionExtensionalityFree := by
  unfold evaluationObserver_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def evaluationObserver_respects (position : Term Const Γ number) (operation : Term Const Γ (element ⇒ result)) :
    ProofSyntax Const Δ (observationRespects (evaluationObserver position operation)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let hypotheses := pointwiseFormula (Const := Const)
    (.var (.vs .vz) : Term Const ((number ⇒ element) :: (number ⇒ element) :: Γ) (number ⇒ element)) (.var .vz) ::
    weakenHyps (σ := number ⇒ element) (weakenHyps Δ)
  have equal : ProofSyntax Const hypotheses (.eq
      (.app (.var (.vs .vz)) (weaken (weaken position)))
      (.app (.var .vz) (weaken (weaken position)))) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE (weaken (weaken position)) (.hyp (Δ := hypotheses) 0))
    simp only [instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]
  have first := evaluationObserver_apply (Δ := hypotheses) (weaken (weaken position))
    (weaken (weaken operation)) (.var (.vs .vz))
  have second := evaluationObserver_apply (Δ := hypotheses) (weaken (weaken position))
    (weaken (weaken operation)) (.var .vz)
  apply ProofSyntax.castIndices rfl ?_ (.eqTrans first
    (.eqTrans (.eqAppArg (weaken (weaken operation)) equal) (.eqSymm second)))
  simp only [weaken,evaluationObserver_rename]

theorem evaluationObserver_respects_free (position : Term Const Γ number) (operation : Term Const Γ (element ⇒ result)) :
    (evaluationObserver_respects (Δ := Δ) position operation).FunctionExtensionalityFree := by
  simp only [evaluationObserver_respects,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree,evaluationObserver_apply_free,and_true]

variable (ops : VectorChildArrays.Operations Const)
  (selection : ClosedTerm Const (Selection ops.toSignature))
  (predicate : Term Const Γ (ops.element ⇒ .prop))
  (length : Term Const Γ ops.number) (array : Term Const Γ ops.ArrayType) (bottom : Term Const Γ ops.element)
  (tabulation : ComputationPremises ops selection Δ)
  (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
  (arrays : ops.ComputationPremises Δ)
  (elements : ProofSyntax Const Δ (bounded ops.toSignature predicate length array))
  (canonical : ProofSyntax Const Δ (paddingCondition ops length array bottom))

def wholeArrayViaEta : ProofSyntax Const Δ (.eq (rebuilt ops selection length array bottom) array) :=
  ProofSyntax.funExtViaEta (pointwise ops selection predicate length array bottom tabulation arithmetic arrays elements canonical)

theorem wholeArrayViaEta_not_free :
    ¬ (wholeArrayViaEta ops selection predicate length array bottom tabulation arithmetic arrays elements canonical).FunctionExtensionalityFree :=
  ProofSyntax.funExtViaEta_not_free _

def observerViaEta (observer : Term Const Γ (ops.ArrayType ⇒ result)) :
    ProofSyntax Const Δ (.eq (.app observer (rebuilt ops selection length array bottom)) (.app observer array)) :=
  .eqAppArg observer (wholeArrayViaEta ops selection predicate length array bottom tabulation arithmetic arrays elements canonical)

theorem observerViaEta_not_free (observer : Term Const Γ (ops.ArrayType ⇒ result)) :
    ¬ (observerViaEta ops selection predicate length array bottom tabulation arithmetic arrays elements canonical observer).FunctionExtensionalityFree :=
  wholeArrayViaEta_not_free ops selection predicate length array bottom tabulation arithmetic arrays elements canonical

def observerUnderLaw (observer : Term Const Γ (ops.ArrayType ⇒ result))
    (respects : ProofSyntax Const Δ (observationRespects observer)) :
    ProofSyntax Const Δ (.eq (.app observer (rebuilt ops selection length array bottom)) (.app observer array)) :=
  .impE (observationAt observer _ _ respects)
    (pointwise ops selection predicate length array bottom tabulation arithmetic arrays elements canonical)

theorem observerUnderLaw_free (observer : Term Const Γ (ops.ArrayType ⇒ result))
    (respects : ProofSyntax Const Δ (observationRespects observer))
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) (elementsFree : elements.FunctionExtensionalityFree)
    (canonicalFree : canonical.FunctionExtensionalityFree) (respectsFree : respects.FunctionExtensionalityFree) :
    (observerUnderLaw ops selection predicate length array bottom tabulation arithmetic arrays elements canonical observer respects).FunctionExtensionalityFree :=
  ⟨observationAt_free _ _ _ _ respectsFree,
    pointwise_free _ _ _ _ _ _ _ _ _ _ _ tabulationFree arithmeticFree arraysFree elementsFree canonicalFree⟩

#print axioms evaluationObserver_respects_free
#print axioms wholeArrayViaEta_not_free
#print axioms observerUnderLaw_free
end Mettapedia.Logic.HOL.VectorTabulation.Shifted
