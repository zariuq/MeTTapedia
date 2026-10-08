import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverControls

/-!
# Actual caller-origin certificates survive native compilation

The family of contextual insertion witnesses is representable on the source
program's element category. Two distinct insertion witnesses can produce the
same program. Their transported certificates remain distinct, and both
certify the actual public-return execution of that compiled program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidenceControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open NamePassingLambda NamePassingContexts NamePassingObserverFunctor
open NamePassingObserverAdequacy NamePassingObserverControls NamePassingDependentEvidence

def sourcePoint : sourcePrograms.Elements :=
  ⟨Opposite.op (Opposite.op (⟨names⟩ : SourceScope)), identity⟩

/-- A substitution-coherent, proof-relevant family of actual caller origins. -/
def insertionFamily : DisplayedFamily sourcePrograms := coyoneda.obj (Opposite.op sourcePoint)

def immediateOrigin : insertionFamily.obj sourcePoint := 𝟙 sourcePoint

def renamedOrigin : insertionFamily.obj sourcePoint :=
  CategoryOfElements.homMk sourcePoint sourcePoint
    ((show (⟨names⟩ : SourceScope) ⟶ ⟨names⟩ from
      .reindex (fun _ name => name) .hole).op.op)
    (by
      change Mettapedia.Languages.LambdaCalculus.NamePassing.rename
        (fun _ name => name) identity = identity
      exact Mettapedia.Languages.LambdaCalculus.NamePassing.rename_id identity)

theorem origins_distinct : immediateOrigin ≠ renamedOrigin := by
  intro same
  have contexts := congrArg (fun arrow => arrow.val.unop.unop) same
  change (.hole : SourceContext names names) = .reindex (fun _ name => name) .hole at contexts
  cases contexts

theorem compiled_certificates_distinct :
    (carry insertionFamily).app sourcePoint immediateOrigin ≠
      (carry insertionFamily).app sourcePoint renamedOrigin :=
  fun same => origins_distinct (carry_injective insertionFamily sourcePoint same)

/-- Both distinct certificates certify a real emitted rho program with a
public return. The target observation is independent of source proof storage. -/
theorem both_certificates_return :
    ProtocolMayReturn (compilerMap.app sourcePoint.1 sourcePoint.2) :=
  receipt_public_return insertionFamily (compilerMap.mapElements.obj sourcePoint)
    ((carry insertionFamily).app sourcePoint renamedOrigin) identity_returns

/-- Program observation has no inverse recovering the supplied origin. -/
theorem program_cannot_recover_origin :
    ¬ ∃ recover : compiledPrograms.obj sourcePoint.1 →
        (compiledFamily insertionFamily).obj (compilerMap.mapElements.obj sourcePoint),
      recover (compilerMap.app sourcePoint.1 sourcePoint.2) =
          (carry insertionFamily).app sourcePoint immediateOrigin ∧
        recover (compilerMap.app sourcePoint.1 sourcePoint.2) =
          (carry insertionFamily).app sourcePoint renamedOrigin := by
  rintro ⟨_, first, second⟩
  exact compiled_certificates_distinct (first.symm.trans second)

def calledPoint : sourcePrograms.Elements :=
  ⟨sourcePoint.1, caller.plug identity⟩

def callingArrow : sourcePoint ⟶ calledPoint :=
  CategoryOfElements.homMk sourcePoint calledPoint
    ((show (⟨names⟩ : SourceScope) ⟶ ⟨names⟩ from caller).op.op) rfl

/-- Mere may-return support cannot be a dependent family over all callers.
The admitted application client already violates the required action. -/
theorem return_support_not_context_coherent :
    ¬ ∃ A : DisplayedFamily sourcePrograms,
      ∀ point, Nonempty (A.obj point) ↔ MayReturn point.2 := by
  rintro ⟨A, support⟩
  obtain ⟨certificate⟩ := (support sourcePoint).mpr identity_returns
  exact identity_call_does_not_return
    ((support calledPoint).mp ⟨A.map callingArrow certificate⟩)

set_option backward.isDefEq.respectTransparency false in
theorem native_product_retains_distinct_origins :
    applyCertificateIdentity insertionFamily sourcePoint.1
        ⟨compilerMap.app sourcePoint.1 sourcePoint.2,
          (carry insertionFamily).app sourcePoint immediateOrigin⟩ ≠
      applyCertificateIdentity insertionFamily sourcePoint.1
        ⟨compilerMap.app sourcePoint.1 sourcePoint.2,
          (carry insertionFamily).app sourcePoint renamedOrigin⟩ := by
  erw [applyCertificateIdentity_retains, applyCertificateIdentity_retains]
  intro same
  exact compiled_certificates_distinct (Sigma.mk.inj_iff.mp same).2.eq

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidenceControls
