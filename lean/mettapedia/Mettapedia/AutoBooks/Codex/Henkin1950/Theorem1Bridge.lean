import Mettapedia.AutoBooks.Codex.Henkin1950.ClassSemantics
import Mettapedia.AutoBooks.Codex.Henkin1950.Semantics

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Minimal theorem-facing bridge from the paper-faithful class semantics already
surfaced in Codex to Henkin's paper-facing `GeneralModel` notion.

The current development has reached Theorem 1 as genuine class-model
satisfiability. What still remains is to connect that class-based truth
relation to the trusted `HenkinModel` semantics used by `GeneralModel`.

This file therefore starts with the abstract class-general bridge that would
turn the new class-semantics endpoint into paper-facing satisfiability, and
then studies the stronger canonical specialization that still exposes the
excluded-middle obstruction.
-/

/-- A closed proposition-bivalence sentence. In the class-based canonical
semantics this expresses Henkin's p. 86 collapse of proposition classes to
`⊤/⊥`. In the current paper-facing `GeneralModel` semantics it instead ranges
over all ambient meta-level propositions. -/
def propBivalence : Sentence :=
  .all
    (.or
      (.eq (.var (.vz : Var [o] o)) (.top : Formula [o]))
      (.eq (.var (.vz : Var [o] o)) (.bot : Formula [o])))

/-- The remaining paper-facing bridge after the class-semantics Theorem 1:
every closed sentence true in a chosen class general model is also true in a
chosen paper-general model. -/
def ClassSentenceSoundBridge
    (CM : ClassGeneralModel)
    (M : GeneralModel) : Prop :=
  ∀ φ : Sentence,
    CM.models φ →
      HenkinModel.models M.toHenkinModel φ

/-- A canonical sentence-sound bridge is the stronger specialization where the
class model is known to be the canonical quotient model itself. -/
def SentenceSoundBridge
    (CM : CanonicalClassModel)
    (M : GeneralModel) : Prop :=
  ∀ φ : Sentence,
    CM.denoteFormula CM.emptyAssignment φ →
      HenkinModel.models M.toHenkinModel φ

/-- If one fixed class general model satisfies a closed theory and its closed
sentences soundly transfer to a paper-general model, then the theory is
satisfiable in Henkin's paper-facing semantics. -/
theorem satisfiable_of_classGeneralModel_of_classSentenceSoundBridge
    {T : ClosedTheorySet}
    {CM : ClassGeneralModel}
    (hCM : ∀ φ : Sentence, φ ∈ T → CM.models φ)
    {M : GeneralModel}
    (hBridge : ClassSentenceSoundBridge CM M) :
    Satisfiable T := by
  refine ⟨M, ?_⟩
  intro φ hφ
  exact hBridge φ (hCM φ hφ)

/-- If a closed theory is satisfiable in the new class-general semantics, and
every such class witness soundly transfers to one paper-general model, then
the theory is satisfiable in Henkin's paper-facing model semantics. -/
theorem satisfiable_of_classGeneralSatisfiable_of_classSentenceSoundBridge
    {T : ClosedTheorySet}
    (hClass : SatisfiableInClassGeneral T)
    {M : GeneralModel}
    (hBridge :
      ∀ CM : ClassGeneralModel,
        (∀ φ : Sentence, φ ∈ T → CM.models φ) →
          ClassSentenceSoundBridge CM M) :
    Satisfiable T := by
  rcases hClass with ⟨CM, hCM⟩
  exact
    satisfiable_of_classGeneralModel_of_classSentenceSoundBridge
      hCM
      (hBridge CM hCM)

/-- Paper-facing Theorem 1 from the class-semantics endpoint plus the minimal
class-sentence-soundness bridge to a chosen general model. This is the exact
remaining semantic step once `theorem1_classGeneral` has been established. -/
theorem theorem1_general_of_classSentenceSoundBridge
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    {M : GeneralModel}
    (hBridge :
      ∀ CM : ClassGeneralModel,
        (∀ φ : Sentence, φ ∈ T → CM.models φ) →
          ClassSentenceSoundBridge CM M) :
    Satisfiable T :=
  satisfiable_of_classGeneralSatisfiable_of_classSentenceSoundBridge
    (CanonicalClassModel.theorem1_classGeneral hT hEx hAll)
    hBridge

/-- Any canonical sentence-sound bridge yields a class-general bridge for the
induced paper-faithful class model. -/
theorem classSentenceSoundBridge_of_sentenceSoundBridge
    (CM : CanonicalClassModel)
    {M : GeneralModel}
    (hBridge : SentenceSoundBridge CM M) :
    ClassSentenceSoundBridge CM.toClassGeneralModel M := by
  intro φ hφ
  exact hBridge φ ((CM.toClassGeneralModel_models_iff φ).1 hφ)

/-- If a closed theory is already satisfied in the canonical class-model sense,
and that class-model truth soundly transfers to some paper-general model, then
the theory is satisfiable in Henkin's paper-facing model semantics. -/
theorem satisfiable_of_classSatisfiable_of_sentenceSoundBridge
    {T : ClosedTheorySet}
    (hClass : CanonicalClassModel.ClassSatisfiable T)
    {M : GeneralModel}
    (hBridge : ∀ CM : CanonicalClassModel, CM.T = T → SentenceSoundBridge CM M) :
    Satisfiable T := by
  rcases hClass with ⟨CM, rfl, hCM⟩
  have hCMClass : ∀ φ : Sentence, φ ∈ CM.T → CM.toClassGeneralModel.models φ := by
    intro φ hφ
    exact (CM.toClassGeneralModel_models_iff φ).2 (hCM φ hφ)
  exact
    satisfiable_of_classGeneralModel_of_classSentenceSoundBridge
      hCMClass
      (classSentenceSoundBridge_of_sentenceSoundBridge CM (hBridge CM rfl))

/-- Paper-facing Theorem 1 from the currently surfaced canonical class-model
endpoint plus the minimal sentence-soundness bridge to a chosen general model.
This isolates the exact remaining step from the pp. 86-88 canonical semantics
to Henkin's stated satisfiability conclusion. -/
theorem theorem1_general_of_sentenceSoundBridge
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
    Satisfiable T := by
  let CM : CanonicalClassModel :=
    { T := T
      completeConsistent := hT
      existsWitness := hEx
      allCounterexample := hAll }
  have hCMClass : ∀ φ : Sentence, φ ∈ T → CM.toClassGeneralModel.models φ := by
    intro φ hφ
    exact (CM.toClassGeneralModel_models_iff φ).2 <|
      CanonicalClassModel.theorem1_canonicalClassModel_milestone
        (M := CM)
        hφ
  exact
    satisfiable_of_classGeneralModel_of_classSentenceSoundBridge
      hCMClass
      (classSentenceSoundBridge_of_sentenceSoundBridge CM hBridge)

/-- Family version of the current Theorem-1 bridge: if one paper-general model
soundly receives every canonical class model over `T`, then `T` is satisfiable
in the paper-facing semantics. -/
theorem theorem1_general_of_sentenceSoundBridge_family
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    {M : GeneralModel}
    (hBridge : ∀ CM : CanonicalClassModel, CM.T = T → SentenceSoundBridge CM M) :
    Satisfiable T :=
  satisfiable_of_classSatisfiable_of_sentenceSoundBridge
    (CanonicalClassModel.theorem1_canonicalClassSatisfiable hT hEx hAll)
    hBridge

/-- The proposition-bivalence sentence already holds in every packaged
canonical class model, because over a complete consistent theory every closed
proposition class is canonically `⊤` or `⊥`. -/
theorem canonicalClassModel_propBivalence
    (CM : CanonicalClassModel) :
    CM.denoteFormula CM.emptyAssignment propBivalence := by
  unfold propBivalence
  rw [CM.denoteFormula_all_iff]
  intro c
  let ν : CM.Assignment [o] := ClassAssignment.extend CM.emptyAssignment c
  have hcTopOrBot : c = CM.trueClass ∨ c = CM.falseClass := by
    let φ : Sentence := ClassAssignment.representative c
    have hrepr : classOf (T := CM.T) φ = c := by
      unfold φ
      exact ClassAssignment.classOf_representative (T := CM.T) c
    rcases CM.completeConsistent.complete φ with hMem | hNeg
    · have hTop : classOf (T := CM.T) φ = CM.trueClass := by
        exact
          (CanonicalFrame.propClassHolds_classOf_iff_mem
            (T := CM.T)
            CM.completeConsistent
            φ).2 hMem
      exact Or.inl (hrepr.symm.trans hTop)
    · have hNotMem : φ ∉ CM.T :=
        CompleteConsistentTheory.not_mem_of_neg_mem CM.completeConsistent hNeg
      have hBot : classOf (T := CM.T) φ = CM.falseClass := by
        exact
          (CanonicalFrame.classOf_eq_falseClass_iff_not_mem
            (T := CM.T)
            CM.completeConsistent
            φ).2 hNotMem
      exact Or.inr (hrepr.symm.trans hBot)
  change CM.denoteFormula ν
    (.or
      (.eq (.var (.vz : Var [o] o)) (.top : Formula [o]))
      (.eq (.var (.vz : Var [o] o)) (.bot : Formula [o])))
  rcases hcTopOrBot with hTop | hBot
  · have hEqTop :
        CM.denoteFormula ν
          (.eq (.var (.vz : Var [o] o)) (.top : Formula [o])) := by
      refine
        (CM.denoteFormula_eq_iff
          ν
          (.var (.vz : Var [o] o))
          (.top : Formula [o])).2 ?_
      simpa [ν, CanonicalClassModel.trueClass, CanonicalFrame.trueClass,
        CanonicalClassModel.denoteTerm, CanonicalFrame.denoteTerm,
        ClassAssignment.closeTerm, ClassAssignment.chooseRepresentatives_extend,
        RepresentativeAssignment.extend,
        Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm, subst] using hTop
    exact
      (CM.denoteFormula_or_iff
        ν
        (.eq (.var (.vz : Var [o] o)) (.top : Formula [o]))
        (.eq (.var (.vz : Var [o] o)) (.bot : Formula [o]))).2 (Or.inl hEqTop)
  · have hEqBot :
        CM.denoteFormula ν
          (.eq (.var (.vz : Var [o] o)) (.bot : Formula [o])) := by
      refine
        (CM.denoteFormula_eq_iff
          ν
          (.var (.vz : Var [o] o))
          (.bot : Formula [o])).2 ?_
      simpa [ν, CanonicalClassModel.falseClass, CanonicalFrame.falseClass,
        CanonicalClassModel.denoteTerm, CanonicalFrame.denoteTerm,
        ClassAssignment.closeTerm, ClassAssignment.chooseRepresentatives_extend,
        RepresentativeAssignment.extend,
        Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm, subst] using hBot
    exact
      (CM.denoteFormula_or_iff
        ν
        (.eq (.var (.vz : Var [o] o)) (.top : Formula [o]))
        (.eq (.var (.vz : Var [o] o)) (.bot : Formula [o]))).2 (Or.inr hEqBot)

/-- Any paper-general model satisfying proposition bivalence already yields
excluded middle for all ambient propositions. This exposes a real semantic
obstruction to identifying the current `GeneralModel` interface with Henkin's
canonical proposition-collapse semantics. -/
theorem excludedMiddle_of_models_propBivalence
    (M : GeneralModel) :
    HenkinModel.models M.toHenkinModel propBivalence →
      ∀ p : Prop, p ∨ ¬ p := by
  intro h p
  have hAll :
      ∀ x : Ty.denote M.Carrier o,
        M.adm o x →
          x.down ∨ ¬ x.down := by
    simpa [propBivalence, HenkinModel.models, PreModel.models,
      HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
      using h
  simpa using hAll (.up p) (M.prop_mem (.up p))

/-- Conversely, ambient excluded middle makes the paper-facing proposition-
bivalence sentence true in every current general model, because equality at
type `o` is interpreted as meta-level logical equivalence. -/
theorem models_propBivalence_of_excludedMiddle
    (M : GeneralModel)
    (hEM : ∀ p : Prop, p ∨ ¬ p) :
    HenkinModel.models M.toHenkinModel propBivalence := by
  unfold propBivalence
  simp [HenkinModel.models, PreModel.models, PreModel.denote, PreModel.extend]
  intro x hx
  rcases hEM x.down with hp | hnp
  · exact Or.inl hp
  · exact Or.inr hnp

/-- The current paper-facing proposition-bivalence sentence is equivalent to
ambient excluded middle in any fixed general model. -/
theorem models_propBivalence_iff_excludedMiddle
    (M : GeneralModel) :
    HenkinModel.models M.toHenkinModel propBivalence ↔ ∀ p : Prop, p ∨ ¬ p := by
  constructor
  · exact excludedMiddle_of_models_propBivalence M
  · exact models_propBivalence_of_excludedMiddle M

/-- Consequently, general validity of the proposition-bivalence sentence is
equivalent to ambient excluded middle. -/
theorem validInGeneral_propBivalence_iff_excludedMiddle :
    ValidInGeneral propBivalence ↔ ∀ p : Prop, p ∨ ¬ p := by
  constructor
  · intro hValid
    exact
      (models_propBivalence_iff_excludedMiddle
        (StandardModel.toGeneralModel defaultStandardModel)).1 (hValid _)
  · intro hEM M
    exact models_propBivalence_of_excludedMiddle M hEM

/-- The same equivalence already appears at paper-standard validity, since the
default paper-standard model is available as a concrete witness. -/
theorem validInStandard_propBivalence_iff_excludedMiddle :
    ValidInStandard propBivalence ↔ ∀ p : Prop, p ∨ ¬ p := by
  constructor
  · intro hValid
    exact
      (models_propBivalence_iff_excludedMiddle
        (StandardModel.toGeneralModel defaultStandardModel)).1
        (hValid defaultStandardModel)
  · intro hEM M
    exact
      models_propBivalence_of_excludedMiddle
        (StandardModel.toGeneralModel M)
        hEM

/-- Without ambient excluded middle, the proposition-bivalence sentence is not
general-valid in the current paper-facing semantics. -/
theorem not_validInGeneral_propBivalence_of_not_excludedMiddle
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ ValidInGeneral propBivalence := by
  intro hValid
  exact hNotEM (validInGeneral_propBivalence_iff_excludedMiddle.1 hValid)

/-- Without ambient excluded middle, the proposition-bivalence sentence is not
standard-valid either. -/
theorem not_validInStandard_propBivalence_of_not_excludedMiddle
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ ValidInStandard propBivalence := by
  intro hValid
  exact hNotEM (validInStandard_propBivalence_iff_excludedMiddle.1 hValid)

/-- Consequently, any actual `SentenceSoundBridge` from a packaged canonical
class model to the current paper-general semantics already forces excluded
middle. This sharply explains why the remaining Theorem-1 bridge is not just a
missing lemma but a potentially stronger semantic commitment. -/
theorem excludedMiddle_of_sentenceSoundBridge
    (CM : CanonicalClassModel)
    {M : GeneralModel}
    (hBridge : SentenceSoundBridge CM M) :
    ∀ p : Prop, p ∨ ¬ p := by
  exact
    excludedMiddle_of_models_propBivalence M <|
      hBridge propBivalence (canonicalClassModel_propBivalence CM)

/-- Specialized excluded-middle consequence for the exact packaged Theorem-1
bridge hypotheses. -/
theorem excludedMiddle_of_theorem1_sentenceSoundBridge
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
  excludedMiddle_of_sentenceSoundBridge _ hBridge

/-- Any bridge family for a class-satisfiable closed theory already forces
excluded middle by specializing to one packaged canonical class model for that
theory. -/
theorem excludedMiddle_of_classSatisfiable_of_sentenceSoundBridge
    {T : ClosedTheorySet}
    (hClass : CanonicalClassModel.ClassSatisfiable T)
    {M : GeneralModel}
    (hBridge : ∀ CM : CanonicalClassModel, CM.T = T → SentenceSoundBridge CM M) :
    ∀ p : Prop, p ∨ ¬ p := by
  rcases hClass with ⟨CM, hCM, _⟩
  subst hCM
  exact excludedMiddle_of_sentenceSoundBridge CM (hBridge CM rfl)

/-- If excluded middle fails, then no sentence-sound bridge to the current
paper-general semantics can exist for a packaged canonical class model. -/
theorem not_sentenceSoundBridge_of_not_excludedMiddle
    (CM : CanonicalClassModel)
    {M : GeneralModel}
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ SentenceSoundBridge CM M := by
  intro hBridge
  exact hNotEM (excludedMiddle_of_sentenceSoundBridge CM hBridge)

/-- If excluded middle fails, then no single paper-general model can provide a
sentence-sound bridge family for a class-satisfiable closed theory. -/
theorem not_exists_sentenceSoundBridge_family_of_not_excludedMiddle
    {T : ClosedTheorySet}
    (hClass : CanonicalClassModel.ClassSatisfiable T)
    (hNotEM : ¬ ∀ p : Prop, p ∨ ¬ p) :
    ¬ ∃ M : GeneralModel,
        ∀ CM : CanonicalClassModel, CM.T = T → SentenceSoundBridge CM M := by
  rintro ⟨M, hBridge⟩
  exact hNotEM (excludedMiddle_of_classSatisfiable_of_sentenceSoundBridge hClass hBridge)

/-- Paper-facing no-bridge corollary: without excluded middle, the exact
packaged Theorem-1 bridge assumptions cannot hold for any paper-general model. -/
theorem not_exists_theorem1_sentenceSoundBridge_of_not_excludedMiddle
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
          M := by
  rintro ⟨M, hBridge⟩
  exact hNotEM (excludedMiddle_of_theorem1_sentenceSoundBridge hT hEx hAll hBridge)

end Mettapedia.AutoBooks.Codex.Henkin1950
