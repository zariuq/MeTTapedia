import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionReading
import Mettapedia.Logic.HOL.IndexedContainerFieldProofs

/-!
# Original source admissibility from its payload guard

The registered Vector shape is its original zero shape. Natural fields have
the declared full guard; the payload field retains the caller's predicate.
The existing structural field-proof producer assembles the complete allowed
condition, including the shape check, from these primitive proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorSourceGuards
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading
open FiniteConstructorEncoding

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def fullAt (length : Term Const Γ N) : ProofSyntax Const Δ (.app (.lam .top) length) :=
  .impE (.eqPropER (.beta length .top)) .topI
theorem fullAt_free (length : Term Const Γ N) : (fullAt (Δ := Δ) length).FunctionExtensionalityFree := by trivial

def shapeAtZero : ProofSyntax Const Δ (.app (.lam (.eq (.var .vz) (weaken (weakenCtx Γ original.zero))))
    (weakenCtx Γ original.zero)) := by
  apply ProofSyntax.impE (.eqPropER (.beta (weakenCtx Γ original.zero)
    (.eq (.var .vz) (weaken (weakenCtx Γ original.zero)))))
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl (weakenCtx Γ original.zero))
  simp only [instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem shapeAtZero_free : (shapeAtZero (Γ := Γ) (Δ := Δ)).FunctionExtensionalityFree := by
  unfold shapeAtZero
  exact ⟨True.intro,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩

def fieldEvidence (payload : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app payload tag)) :
    guards.Evidence Δ code (parameterMap payload) (arguments length tag (weakenCtx Γ original.zero)) := by
  refine ⟨?_, ?_, ?_, PUnit.unit⟩
  · exact fullAt length
  · exact present
  · apply ProofSyntax.castIndices rfl ?_ shapeAtZero
    simp [guards, arguments, HOL.subst, Subst.lift]
    constructor
    · rfl
    · rw [subst_weakenCtx]

theorem fieldEvidence_free (payload : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app payload tag)) (free : present.FunctionExtensionalityFree) :
    guards.EvidenceFree Δ code (parameterMap payload) (arguments length tag (weakenCtx Γ original.zero))
      (fieldEvidence payload length tag present) := by
  unfold fieldEvidence
  refine ⟨fullAt_free length, free, ?_, True.intro⟩
  dsimp only
  simpa only [ProofSyntax.functionExtensionalityFree_castIndices] using (shapeAtZero_free (Γ := Γ) (Δ := Δ))

def allowedOfTag (payload : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app payload tag)) :
    ProofSyntax Const Δ (sourceAllowed payload length tag (weakenCtx Γ original.zero)) :=
  guards.introduce code (parameterMap payload) (arguments length tag (weakenCtx Γ original.zero))
    (fieldEvidence payload length tag present)

theorem allowedOfTag_free (payload : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app payload tag)) (free : present.FunctionExtensionalityFree) :
    (allowedOfTag payload length tag present).FunctionExtensionalityFree :=
  guards.introduce_free code (parameterMap payload) (arguments length tag (weakenCtx Γ original.zero))
    (fieldEvidence payload length tag present) (fieldEvidence_free payload length tag present free)

#print axioms allowedOfTag_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorSourceGuards
