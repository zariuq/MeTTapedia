import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveEdge
import Mettapedia.Logic.HOL.ConstructorPositionSubstitution
import Mettapedia.Logic.HOL.IndexedContainerFieldProofs
import Mettapedia.Logic.HOL.IndexedContainerIndexPrograms

/-!
# Binder transport for the original mixed-vector source interpretation

The generated constructor inventory, encoded payload, activity and root
section commute with typed substitution. These are syntactic transport laws;
they neither install a constructor nor discharge its semantic assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorScopeTransport
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorChildGuard
open IndexedContainerNativeVectorActiveEdge
open FiniteConstructorEncoding IndexedConstructorGuards OrderedPositionPrograms

variable {Γ Ξ : Ctx Base} (images : Subst Const Γ Ξ)

theorem numeral_subst (n : Nat) : HOL.subst images (numeral Γ n) = numeral Ξ n := by
  induction n with
  | zero => exact subst_weakenCtx images original.zero
  | succ n ih => simp only [numeral, HOL.subst, subst_weakenCtx, ih]

theorem parameterMap_comp (payload : Term Const Γ (E ⇒ .prop)) :
    (Subst.comp images (parameterMap payload) : Subst Const indices.parameters Ξ) =
      (fun {type} (entry : Var indices.parameters type) => parameterMap (HOL.subst images payload) entry) := by
  funext type entry
  cases entry with
  | vz => rfl
  | vs impossible => nomatch impossible

theorem constructors_subst (payload : Term Const Γ (E ⇒ .prop)) :
    (constructors payload).subst images = constructors (HOL.subst images payload) := by
  unfold constructors IndexedContainerPositionTerms.FieldGuards.constructors ConstructorPrograms.subst
  congr 1
  · funext n
    exact numeral_subst images n
  · funext occurrence
    have zero : occurrence.val = 0 := by have h := occurrence.isLt; change occurrence.val < 1 at h; omega
    have same : occurrence = IndexedContainerNativeVectorPositionReading.occurrence payload := Fin.ext zero
    subst occurrence
    have h := guards.compile_subst code (parameterMap payload) images
    rw [parameterMap_comp] at h
    exact h
  · funext occurrence
    have zero : occurrence.val = 0 := by have h := occurrence.isLt; change occurrence.val < 1 at h; omega
    have same : occurrence = IndexedContainerNativeVectorPositionReading.occurrence payload := Fin.ext zero
    subst occurrence
    have h := reading.resultProgram_subst code (parameterMap payload) images
    rw [parameterMap_comp] at h
    exact h

theorem sourceAllowed_subst (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N) :
    HOL.subst images (sourceAllowed payload length tag shape) =
      sourceAllowed (HOL.subst images payload) (HOL.subst images length) (HOL.subst images tag) (HOL.subst images shape) := by
  simp only [sourceAllowed, applyArguments_subst]
  change applyArguments [N,E,N] (HOL.subst images (guards.compile code (parameterMap payload))) _ =
    applyArguments [N,E,N] (guards.compile code (parameterMap (HOL.subst images payload))) _
  rw [guards.compile_subst, parameterMap_comp]
  rfl

theorem plans_subst (payload : Term Const Γ (E ⇒ .prop)) (entry : Fin 1) :
    substitute images (plans payload entry) = plans (HOL.subst images payload) entry := by
  have zero : entry.val = 0 := by omega
  have same : entry = ⟨0, by decide⟩ := Fin.ext zero
  subst entry
  change substitute images (reading.compile code (parameterMap payload)) =
    reading.compile code (parameterMap (HOL.subst images payload))
  rw [IndexedContainerPositionTerms.Reading.compile_subst, parameterMap_comp]

theorem activeProgram_subst (payload : Term Const Γ (E ⇒ .prop)) :
    HOL.subst images (positions payload).activeProgram =
      (positions (HOL.subst images payload)).activeProgram := by
  rw [PositionPrograms.activeProgram_subst]
  simp only [positions, PositionPrograms.ofSegments_subst]
  simp only [plans_subst]
  have same := constructors_subst images payload
  unfold constructors IndexedContainerPositionTerms.FieldGuards.constructors ConstructorPrograms.subst at same ⊢
  simp only [ConstructorPrograms.mk.injEq, heq_eq_eq, true_and] at same
  rcases same with ⟨numerals, allowed, result⟩
  dsimp only at numerals allowed result ⊢
  rw [numerals, allowed, result]

theorem encoded_subst (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N) :
    HOL.subst images (encoded payload length tag shape) =
      encoded (HOL.subst images payload) (HOL.subst images length) (HOL.subst images tag) (HOL.subst images shape) := by
  simp only [encoded, encode_subst]
  rfl

theorem sourceActivity_subst (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N) :
    HOL.subst images (sourceActivity payload length tag shape) =
      sourceActivity (HOL.subst images payload) (HOL.subst images length) (HOL.subst images tag) (HOL.subst images shape) := by
  change HOL.subst images (.app (positions payload).activeProgram (encoded payload length tag shape)) = _
  rw [HOL.subst, activeProgram_subst, encoded_subst]
  rfl

theorem edgeProgram_subst (payload : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType (constructors payload).fields ⇒ (N ⇒ E) ⇒ E)) :
    HOL.subst images ((positions payload).edgeProgram construct) =
      (positions (HOL.subst images payload)).edgeProgram (HOL.subst images construct) := by
  rw [PositionPrograms.edgeProgram_subst]
  simp only [positions, PositionPrograms.ofSegments_subst]
  simp only [plans_subst]
  have same := constructors_subst images payload
  unfold constructors IndexedContainerPositionTerms.FieldGuards.constructors ConstructorPrograms.subst at same ⊢
  simp only [ConstructorPrograms.mk.injEq, heq_eq_eq, true_and] at same
  rcases same with ⟨numerals, allowed, result⟩
  dsimp only at numerals allowed result ⊢
  rw [numerals, allowed, result]

theorem rootPredicate_subst (payload : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType (constructors payload).fields ⇒ (N ⇒ E) ⇒ E)) :
    HOL.subst images (rootPredicate payload construct) =
      rootPredicate (HOL.subst images payload) (HOL.subst images construct) := by
  simp only [rootPredicate, ConstructorPrograms.rootAt, HOL.subst, subst_weaken,
    Subst.lift, ConstructorPrograms.rootProgram_subst]
  have same := constructors_subst images payload
  unfold constructors IndexedContainerPositionTerms.FieldGuards.constructors ConstructorPrograms.subst at same ⊢
  simp only [ConstructorPrograms.mk.injEq, heq_eq_eq, true_and] at same
  rcases same with ⟨numerals, allowed, result⟩
  dsimp only at numerals allowed result ⊢
  rw [numerals, allowed, result]

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorScopeTransport
