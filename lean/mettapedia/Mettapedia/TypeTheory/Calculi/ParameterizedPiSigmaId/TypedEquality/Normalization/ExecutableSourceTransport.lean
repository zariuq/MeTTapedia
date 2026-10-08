import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.WrittenHeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenChecking

/-!
# Transport of complete annotated checking evidence

The transported certificate retains the source context, every written
expected-type annotation, its formation level and the checked term. This is
transport of accepted evidence; it makes no assertion that two finite-budget
checking runs make the same operational decision.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWrittenChecking

variable {H K J : Type} {n : Nat}

def SourceContext.mapHead (map : H → K) : {n : Nat} → SourceContext H n → SourceContext K n
  | _, .nil => .nil
  | _, .snoc context domain => .snoc (context.mapHead map) (domain.mapHead map)

@[simp] theorem SourceContext.erase_mapHead (map : H → K) (context : SourceContext H n) :
    (context.mapHead map).erase = context.erase.mapHead map := by
  induction context <;> simp_all [SourceContext.mapHead, SourceContext.erase, Ctx.mapHead]

@[simp] theorem SourceContext.mapHead_id (context : SourceContext H n) :
    context.mapHead _root_.id = context := by
  induction context <;> simp_all [SourceContext.mapHead]

@[simp] theorem SourceContext.mapHead_comp (first : H → K) (second : K → J)
    (context : SourceContext H n) :
    (context.mapHead first).mapHead second = context.mapHead (second ∘ first) := by
  induction context <;> simp_all [SourceContext.mapHead]

theorem SourceContext.Formed.mapHead {source : Rules H} {target : Rules K} {map : H → K}
    (morphism : source.Morphism target map) {context : SourceContext H n}
    (formed : context.Formed source) : (context.mapHead map).Formed target := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed isUniverse ih =>
      exact .snoc ih (by simpa only [SourceContext.erase_mapHead, Tm.mapHead] using typed.mapHead morphism)
        (morphism.isUniverse isUniverse)

def SourceJudgmentCertificate.mapHead {source : Rules H} {target : Rules K} {map : H → K}
    (morphism : source.Morphism target map) {context : SourceContext H n} {term type : ATm H n}
    (certificate : SourceJudgmentCertificate source context term type) :
    SourceJudgmentCertificate target (context.mapHead map) (term.mapHead map) (type.mapHead map) where
  contextChecked := certificate.contextChecked.mapHead morphism
  expectedUniverse := map certificate.expectedUniverse
  expectedIsUniverse := morphism.isUniverse certificate.expectedIsUniverse
  expectedChecked := by
    simpa only [SourceContext.erase_mapHead, Tm.mapHead] using certificate.expectedChecked.mapHead morphism
  termChecked := by
    simpa only [SourceContext.erase_mapHead, ATm.erase_mapHead] using
      certificate.termChecked.mapHead morphism

def SourceSynthesisCertificate.mapHead {source : Rules H} {target : Rules K} {map : H → K}
    (morphism : source.Morphism target map) {context : SourceContext H n} {term : ATm H n}
    (certificate : SourceSynthesisCertificate source context term) :
    SourceSynthesisCertificate target (context.mapHead map) (term.mapHead map) where
  contextChecked := certificate.contextChecked.mapHead morphism
  type := certificate.type.mapHead map
  termChecked := by
    simpa only [SourceContext.erase_mapHead] using certificate.termChecked.mapHead morphism

@[simp] theorem SourceJudgmentCertificate.mapHead_level
    {source : Rules H} {target : Rules K} {map : H → K}
    (morphism : source.Morphism target map) {context : SourceContext H n} {term type : ATm H n}
    (certificate : SourceJudgmentCertificate source context term type) :
    (certificate.mapHead morphism).expectedUniverse = map certificate.expectedUniverse := rfl

@[simp] theorem SourceSynthesisCertificate.mapHead_type
    {source : Rules H} {target : Rules K} {map : H → K}
    (morphism : source.Morphism target map) {context : SourceContext H n} {term : ATm H n}
    (certificate : SourceSynthesisCertificate source context term) :
    (certificate.mapHead morphism).type = certificate.type.mapHead map := rfl

end TypedEquality.Normalization.ExecutableWrittenChecking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
