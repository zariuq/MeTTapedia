import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentRetainedIdentityInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientMotiveCoverage
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientRetainedIdentityInterface

/-!
# Retained native identity interpretation on the shared quotient

Every independently admitted native tuple and every independently qualified
semantic frame has the same retained-input meaning. The actual quotient
operation therefore satisfies the generic constructor, beta and substitution
contracts without forgetting the submitted motive function. The original
family-only profile and its refuted canonical exact attachment are unchanged.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientRetainedIdentity

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment FormationSensitiveContextual
open SharedJudgmentQuotientInterpretation SharedJudgmentQuotientMotiveCoverage
open Mettapedia.TypeTheory

variable {assembly : Assembly}

noncomputable def retainedFrame {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    SharedJudgmentRetainedIdentityInterpretation.JFrame (data assembly) (frames assembly)
      source type left motive method where
  frame := nativeFrame source parameters
  functionType := QType.mk (QuotientIdentityInputCoherence.motiveFunctionType
    (nativeInput source parameters))
  function := TermFibre.mk (QuotientIdentityInputCoherence.motiveFunction
    (nativeInput source parameters))

theorem retained_frame_meaning {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    SharedJudgmentRetainedIdentityInterpretation.JFrameMeaning (data assembly) (frames assembly)
      (retainedFrame source parameters) :=
  ⟨native_frame_meaning source parameters,
    QuotientInterpretation.type_meaning (context source)
      (QuotientIdentityInputCoherence.motiveFunctionType (nativeInput source parameters)),
    QuotientInterpretation.term_meaning (context source)
      (QuotientIdentityInputCoherence.motiveFunction (nativeInput source parameters))⟩

/-- Uniqueness is for the interpretation of one complete native request,
not a uniqueness principle for arbitrary proof objects or motive functions. -/
theorem retained_frame_unique {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method)
    {retained : SharedJudgmentRetainedIdentityInterpretation.JFrame
      (data assembly) (frames assembly) source type left motive method}
    (meaning : SharedJudgmentRetainedIdentityInterpretation.JFrameMeaning
      (data assembly) (frames assembly) retained) :
    retained = retainedFrame source parameters := by
  rcases retained with ⟨frame, functionType, function⟩
  rcases meaning with ⟨frameMeaning, functionTypeMeaning, functionMeaning⟩
  have sameFrame := native_frame_unique parameters frameMeaning
  cases sameFrame
  have sameType := type_meaning_unique functionTypeMeaning
    (retained_frame_meaning source parameters).functionTypeMeaning
  cases sameType
  have sameFunction := term_meaning_unique functionMeaning
    (retained_frame_meaning source parameters).functionMeaning
  cases sameFunction
  rfl

theorem frame_coverage : SharedJudgmentRetainedIdentityInterpretation.FrameCoverage
    (data assembly) (frames assembly) :=
  SharedJudgmentRetainedIdentityInterpretation.frameCoverage_of_admittedTotal
    (data assembly) (frames assembly) based_motive_coverage admitted_total

/-- All qualified semantic frames are admitted, not merely a selected
canonical frame for each tuple. The image has no result-meaning premise. -/
theorem scope_coverage : SharedJudgmentRetainedIdentityInterpretation.ScopeCoverage
    (data assembly) (frames assembly) QuotientRetainedIdentityInterface.Scope := by
  intro n source type left motive method retained parameters meaning
  have same := retained_frame_unique parameters meaning
  subst retained
  exact QuotientRetainedIdentityInterface.native_admitted (nativeInput source parameters)

theorem constructor_meaning : SharedJudgmentRetainedIdentityInterpretation.ConstructorMeaning
    (data assembly) (frames assembly) QuotientRetainedIdentityInterface.Scope
      QuotientRetainedIdentityInterface.run := by
  intro n source type left motive method retained parameters meaning admitted
  have same := retained_frame_unique parameters meaning
  subst retained
  change (data assembly).term (nativeFrame source parameters).context _ _ _
    (QuotientCwf.tmSub
      (QuotientRetainedIdentityInterface.run
        (QuotientRetainedIdentityInterface.nativeInput (nativeInput source parameters)) admitted)
      (nativeFrame source parameters).comparison.forward)
  have sameRun := QuotientRetainedIdentityInterface.run_native (nativeInput source parameters) admitted
  exact Eq.mpr (congrArg (fun value => (data assembly).term
    (nativeFrame source parameters).context
    (FormationSensitiveBasedIdentity.genericTerm type left motive method)
    (FormationSensitiveBasedIdentity.motiveBody motive)
    (QuotientCwf.tySub (nativeFrame source parameters).motive
      (nativeFrame source parameters).comparison.forward)
    (QuotientCwf.tmSub value (nativeFrame source parameters).comparison.forward)) sameRun)
    (native_j_meaning source parameters)

theorem admitted_beta : SharedJudgmentRetainedIdentityInterpretation.AdmittedBeta
    (data assembly) (frames assembly) QuotientRetainedIdentityInterface.Scope
      QuotientRetainedIdentityInterface.run :=
  SharedJudgmentRetainedIdentityInterpretation.admittedBeta_of_beta
    (data assembly) (frames assembly) _ _ QuotientRetainedIdentityInterface.beta

theorem admitted_substitution : SharedJudgmentRetainedIdentityInterpretation.AdmittedSubstitution
    (data assembly) (frames assembly) QuotientRetainedIdentityInterface.Scope
      QuotientRetainedIdentityInterface.run QuotientRetainedIdentityInterface.reindexing :=
  SharedJudgmentRetainedIdentityInterpretation.admittedSubstitution_of_full
    (data assembly) (frames assembly) _ _ _ QuotientRetainedIdentityInterface.section_square
      QuotientRetainedIdentityInterface.substitution

/-- The same actual data satisfy all retained identity clauses together.
This is a constructor component, not a completed language or host model. -/
theorem retained_identity_qualified :
    SharedJudgmentRetainedIdentityInterpretation.FrameCoverage (data assembly) (frames assembly) ∧
      SharedJudgmentRetainedIdentityInterpretation.ScopeCoverage (data assembly) (frames assembly)
        QuotientRetainedIdentityInterface.Scope ∧
      SharedJudgmentRetainedIdentityInterpretation.ConstructorMeaning (data assembly) (frames assembly)
        QuotientRetainedIdentityInterface.Scope QuotientRetainedIdentityInterface.run ∧
      SharedJudgmentRetainedIdentityInterpretation.AdmittedBeta (data assembly) (frames assembly)
        QuotientRetainedIdentityInterface.Scope QuotientRetainedIdentityInterface.run ∧
      SharedJudgmentRetainedIdentityInterpretation.AdmittedSubstitution (data assembly) (frames assembly)
        QuotientRetainedIdentityInterface.Scope QuotientRetainedIdentityInterface.run
          QuotientRetainedIdentityInterface.reindexing :=
  ⟨frame_coverage, scope_coverage, constructor_meaning, admitted_beta, admitted_substitution⟩

#print axioms retained_frame_unique
#print axioms frame_coverage
#print axioms scope_coverage
#print axioms constructor_meaning
#print axioms admitted_beta
#print axioms admitted_substitution
#print axioms retained_identity_qualified

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientRetainedIdentity
