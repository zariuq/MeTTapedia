import Mettapedia.AutoBooks.Codex.Henkin1950.Theorem1Bridge

namespace Mettapedia.AutoBooks.Codex.Henkin1950

/-!
# Henkin 1950 Theorem 1 Bridge Regression

Positive canaries for the current obstruction surface around
`SentenceSoundBridge`.
-/

namespace Regression

open Mettapedia.Logic.HOL

example
    (M : GeneralModel)
    (hEM : ∀ p : Prop, p ∨ ¬ p) :
    HenkinModel.models M.toHenkinModel propBivalence :=
  models_propBivalence_of_excludedMiddle M hEM

example :
    ValidInGeneral propBivalence ↔ ∀ p : Prop, p ∨ ¬ p :=
  validInGeneral_propBivalence_iff_excludedMiddle

example :
    ValidInStandard propBivalence ↔ ∀ p : Prop, p ∨ ¬ p :=
  validInStandard_propBivalence_iff_excludedMiddle

example
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ ValidInGeneral propBivalence :=
  not_validInGeneral_propBivalence_of_not_excludedMiddle hNotEM

example
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ ValidInStandard propBivalence :=
  not_validInStandard_propBivalence_of_not_excludedMiddle hNotEM

example
    (CM : CanonicalClassModel)
    {M : GeneralModel}
    (hBridge : SentenceSoundBridge CM M) :
    ∀ p : Prop, p ∨ ¬ p :=
  excludedMiddle_of_sentenceSoundBridge CM hBridge

example
    {T : ClosedTheorySet}
    (hClass : CanonicalClassModel.ClassSatisfiable T)
    {M : GeneralModel}
    (hBridge : ∀ CM : CanonicalClassModel, CM.T = T → SentenceSoundBridge CM M) :
    ∀ p : Prop, p ∨ ¬ p :=
  excludedMiddle_of_classSatisfiable_of_sentenceSoundBridge hClass hBridge

example
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    {M : GeneralModel}
    (hBridge :
      ∀ CM : CanonicalClassModel, CM.T = T → SentenceSoundBridge CM M) :
    Satisfiable T :=
  theorem1_general_of_sentenceSoundBridge_family hT hEx hAll hBridge

example
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    {M : GeneralModel}
    (hBridge :
      SentenceSoundBridge
        { T := T
          completeConsistent := hT
          existsWitness := hEx
          allCounterexample := hAll }
        M) :
    ∀ p : Prop, p ∨ ¬ p :=
  excludedMiddle_of_theorem1_sentenceSoundBridge hT hEx hAll hBridge

example
    (CM : CanonicalClassModel)
    {M : GeneralModel}
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ SentenceSoundBridge CM M :=
  not_sentenceSoundBridge_of_not_excludedMiddle CM hNotEM

example
    {T : ClosedTheorySet}
    (hClass : CanonicalClassModel.ClassSatisfiable T)
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ ∃ M : GeneralModel,
        ∀ CM : CanonicalClassModel, CM.T = T → SentenceSoundBridge CM M :=
  not_exists_sentenceSoundBridge_family_of_not_excludedMiddle hClass hNotEM

example
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ ∃ M : GeneralModel,
        SentenceSoundBridge
          { T := T
            completeConsistent := hT
            existsWitness := hEx
            allCounterexample := hAll }
          M :=
  not_exists_theorem1_sentenceSoundBridge_of_not_excludedMiddle hT hEx hAll hNotEM

end Regression

end Mettapedia.AutoBooks.Codex.Henkin1950
