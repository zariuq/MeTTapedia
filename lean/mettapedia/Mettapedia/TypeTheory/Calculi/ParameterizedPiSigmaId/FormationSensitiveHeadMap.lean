import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws

/-! # Formation-sensitive judgments under morphisms of rule presentations -/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace FormationSensitive

variable {HeadOne HeadTwo : Type} {n m : Nat}

/-- Every refined constructor, including constant formation and conversion's
independently formed target, transports along an actual rule morphism. -/
theorem Typing.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map)
    {context : Ctx HeadOne n} {term type : Tm HeadOne n}
    (typing : Typing source context term type) :
    Typing target (context.mapHead map) (term.mapHead map) (type.mapHead map) := by
  induction typing with
  | headType head => exact .headType (morphism.headTyping head)
  | @var n context index =>
      simpa only [Tm.mapHead, Ctx.lookup_mapHead] using
        (Typing.var (R := target) (Γ := context.mapHead map) index)
  | const known _ universeWitness ihType =>
      simpa only [Tm.mapHead, Tm.mapHead_liftClosed] using
        (Typing.const (morphism.constantType known) ihType
          (morphism.isUniverse universeWitness))
  | piForm _ universeA _ universeB join ihA ihB =>
      exact .piForm ihA (morphism.isUniverse universeA)
        ihB (morphism.isUniverse universeB) (morphism.join join)
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      exact .sigmaForm ihA (morphism.isUniverse universeA)
        ihB (morphism.isUniverse universeB) (morphism.join join)
  | lamIntro _ universeWitness _ ihPi ihBody =>
      exact .lamIntro ihPi (morphism.isUniverse universeWitness) ihBody
  | appElim _ _ ihFunction ihArgument =>
      simpa only [Tm.mapHead, Tm.mapHead_inst0] using
        (Typing.appElim ihFunction ihArgument)
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      rw [Tm.mapHead_inst0] at ihSecond
      exact .pairIntro ihSigma (morphism.isUniverse universeWitness) ihFirst ihSecond
  | fstElim _ ihPair => exact .fstElim ihPair
  | sndElim _ ihPair =>
      simpa only [Tm.mapHead, Tm.mapHead_inst0] using (Typing.sndElim ihPair)
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      exact .idForm ihA (morphism.isUniverse universeWitness) ihLeft ihRight
  | reflIntro _ ihTerm => exact .reflIntro ihTerm
  | cumul _ order ihTerm => exact .cumul ihTerm (morphism.cumulative order)
  | conv _ _ universeWitness conversion ihTerm ihTarget =>
      exact .conv ihTerm ihTarget (morphism.isUniverse universeWitness)
        (conversion.mapHead map morphism.headEq morphism.computation)

theorem ContextFormation.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map)
    {context : Ctx HeadOne n} (formed : ContextFormation source context) :
    ContextFormation target (context.mapHead map) := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (typed.mapHead morphism) (morphism.isUniverse universeWitness)

theorem Judgment.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map)
    {context : Ctx HeadOne n} {term type : Tm HeadOne n}
    (judgment : Judgment source context term type) :
    Judgment target (context.mapHead map) (term.mapHead map) (type.mapHead map) :=
  ⟨judgment.context.mapHead morphism, judgment.typing.mapHead morphism⟩

theorem CtxMor.mapHead {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map)
    {context : Ctx HeadOne n} {replacement : Ctx HeadOne m}
    {substitution : Sub HeadOne n m}
    (typed : CtxMor source context replacement substitution) :
    CtxMor target (context.mapHead map) (replacement.mapHead map)
      (fun index => (substitution index).mapHead map) := by
  intro index
  simpa only [Ctx.lookup_mapHead, Tm.mapHead_subst] using
    (typed index).mapHead morphism

/-- Ordinary typed substitution and environment transport reach the same raw
term and annotation, in the independently transported formed target context. -/
theorem Judgment.mapHead_substitute {source : Rules HeadOne} {target : Rules HeadTwo}
    {map : HeadOne → HeadTwo} (morphism : source.Morphism target map)
    {context : Ctx HeadOne n} {replacement : Ctx HeadOne m}
    {term type : Tm HeadOne n} {substitution : Sub HeadOne n m}
    (judgment : Judgment source context term type)
    (formed : ContextFormation source replacement)
    (typed : CtxMor source context replacement substitution) :
    Judgment target (replacement.mapHead map)
      (subst (fun index => (substitution index).mapHead map) (term.mapHead map))
      (subst (fun index => (substitution index).mapHead map) (type.mapHead map)) :=
  (judgment.mapHead morphism).substitute (formed.mapHead morphism)
    (typed.mapHead morphism)

end FormationSensitive

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
