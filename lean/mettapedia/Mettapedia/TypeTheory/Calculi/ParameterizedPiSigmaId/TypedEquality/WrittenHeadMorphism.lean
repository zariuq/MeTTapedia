import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.WrittenDomains
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedHeadMapping

/-!
# Rule morphisms preserve written source contracts

A rule morphism transports the annotated derivation itself. In particular,
the written domain of a lambda remains a formed type and remains equal to
the function domain after transport. Erasure alone would lose that contract.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality

variable {HeadOne HeadTwo : Type}

theorem ATyped.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map) {n : Nat}
    {context : Ctx HeadOne n} {term : ATm HeadOne n} {type : Tm HeadOne n}
    (typed : ATyped source context term type) :
    ATyped target (context.mapHead map) (term.mapHead map) (type.mapHead map) := by
  induction typed with
  | headType known => exact .headType (morphism.headTyping known)
  | @var n context index =>
      simpa only [ATm.mapHead, Ctx.lookup_mapHead] using
        (ATyped.var (R := target) (Γ := context.mapHead map) index)
  | const declared formed isUniverse =>
      simpa only [ATm.mapHead, Tm.mapHead_liftClosed] using
        (ATyped.const (morphism.constantType declared) (formed.mapHead morphism)
          (morphism.isUniverse isUniverse))
  | piForm _ hu _ hv joined ihA ihB =>
      simp only [ATm.mapHead, Tm.mapHead, ← ATm.erase_mapHead, Ctx.mapHead] at ihA ihB ⊢
      exact .piForm ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv)
        (morphism.join joined)
  | sigmaForm _ hu _ hv joined ihA ihB =>
      simp only [ATm.mapHead, Tm.mapHead, ← ATm.erase_mapHead, Ctx.mapHead] at ihA ihB ⊢
      exact .sigmaForm ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv)
        (morphism.join joined)
  | lamBare formed hu _ ihBody =>
      simp only [ATm.mapHead, Tm.mapHead, Ctx.mapHead] at ihBody ⊢
      exact .lamBare (formed.mapHead morphism) (morphism.isUniverse hu) ihBody
  | lamTyped _ hv equal formed hu _ ihW ihBody =>
      simp only [ATm.mapHead, Tm.mapHead, Ctx.mapHead] at ihW ihBody ⊢
      exact .lamTyped ihW (morphism.isUniverse hv)
        (by simpa only [ATm.erase_mapHead, Tm.mapHead] using equal.mapHead morphism)
        (formed.mapHead morphism) (morphism.isUniverse hu) ihBody
  | appElim _ _ ihFunction ihArgument =>
      simp only [ATm.mapHead, Tm.mapHead, Tm.mapHead_inst0, ← ATm.erase_mapHead]
        at ihFunction ihArgument ⊢
      exact .appElim ihFunction ihArgument
  | pairIntro formed hu _ _ ihFirst ihSecond =>
      simp only [ATm.mapHead, Tm.mapHead, Tm.mapHead_inst0, ← ATm.erase_mapHead]
        at ihFirst ihSecond ⊢
      exact .pairIntro (formed.mapHead morphism) (morphism.isUniverse hu) ihFirst ihSecond
  | fstElim _ ih =>
      simp only [ATm.mapHead, Tm.mapHead] at ih ⊢
      exact .fstElim ih
  | sndElim _ ih =>
      simp only [ATm.mapHead, Tm.mapHead, Tm.mapHead_inst0, ← ATm.erase_mapHead] at ih ⊢
      exact .sndElim ih
  | idForm _ hu _ _ ihA ihFirst ihSecond =>
      simp only [ATm.mapHead, Tm.mapHead, ← ATm.erase_mapHead] at ihA ihFirst ihSecond ⊢
      exact .idForm ihA (morphism.isUniverse hu) ihFirst ihSecond
  | reflIntro _ ih =>
      simp only [ATm.mapHead, Tm.mapHead, ← ATm.erase_mapHead] at ih ⊢
      exact .reflIntro ih
  | conv _ equal hu ih =>
      exact .conv ih (equal.mapHead morphism) (morphism.isUniverse hu)
  | sub _ below ih => exact .sub ih (Derivable.mapHead morphism below)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
