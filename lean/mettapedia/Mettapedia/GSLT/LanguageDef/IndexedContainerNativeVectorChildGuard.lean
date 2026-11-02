import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActivityReadback
import Mettapedia.Logic.HOL.OrderedPositionTargetTransport
import Mettapedia.Logic.HOL.OrderedPositionChildIntroduction

/-!
# Original activity recovers the declared child index of the mixed source

All three canonical segments carry the original unit-index reading. The
common-label theorem recovers that index from activity, and retained plan
conversions rebuild the actual original child guard. No arithmetic or index
oracle is required for this selection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildGuard
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading
open FiniteConstructorEncoding OrderedPositionPrograms

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def positions (payload : Term Const Γ (E ⇒ .prop)) :=
  IndexedConstructorGuards.PositionPrograms.ofSegments (constructors payload) original.zero original.successor (plans payload)

def encoded (payload : Term Const Γ (E ⇒ .prop)) (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N) :=
  encode (constructors payload).fields (occurrence payload) (sourceArguments payload length tag shape)

def declaredCounts (length : Term Const Γ N) : List (Term Const Γ N) :=
  [.app (weakenCtx Γ original.successor) (weakenCtx Γ original.zero),length,
    .app (weakenCtx Γ original.successor) (weakenCtx Γ original.zero)]

def canonicalAtDeclaredIndex (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot)) :
    ProofSyntax Const Δ (compileAt original.zero original.successor
      (mixedPlan original.zero original.successor length .top .top .top) Subst.id slot .top) :=
  knownIndex original.zero original.successor (declaredCounts length) .top slot
    (.andER (IndexedContainerNativeVectorActivityReadback.fromActivity payload length tag shape slot active))

theorem canonicalAtDeclaredIndex_free (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (free : active.FunctionExtensionalityFree) :
    (canonicalAtDeclaredIndex payload length tag shape slot active).FunctionExtensionalityFree :=
  knownIndex_free _ _ _ _ _ _ (IndexedContainerNativeVectorActivityReadback.fromActivity_free _ _ _ _ _ active free)

@[irreducible] def childGuardCertificate (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (free : active.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ ((positions payload).childGuard (encoded payload length tag shape) slot .top) //
      proof.FunctionExtensionalityFree } :=
  IndexedConstructorGuards.PositionPrograms.certifiedChildFromCanonical (constructors payload) original.zero original.successor
    (plans payload) (occurrence payload) (sourceArguments payload length tag shape)
    (mixedPlan original.zero original.successor length .top .top .top) (planEquations payload length tag shape) slot .top
    (.andEL (IndexedContainerNativeVectorActivityReadback.fromActivity payload length tag shape slot active))
    (canonicalAtDeclaredIndex payload length tag shape slot active) (planEquations_free _ _ _ _)
    (IndexedContainerNativeVectorActivityReadback.fromActivity_free _ _ _ _ _ active free)
    (canonicalAtDeclaredIndex_free _ _ _ _ _ active free)

def childGuardFromActivity (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (free : active.FunctionExtensionalityFree) :
    ProofSyntax Const Δ ((positions payload).childGuard (encoded payload length tag shape) slot .top) :=
  (childGuardCertificate payload length tag shape slot active free).val

theorem childGuardFromActivity_free (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (free : active.FunctionExtensionalityFree) :
    (childGuardFromActivity payload length tag shape slot active free).FunctionExtensionalityFree :=
  (childGuardCertificate payload length tag shape slot active free).property

#print axioms childGuardFromActivity_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildGuard
