import Mettapedia.GSLT.Dynamics.BranchingEvidenceTarskiInterpretation
import Mettapedia.Logic.HOL.Embedding.LiftedStandardModelTarskiInterpretation

/-!
# A shared set-family semantics for simple, dependent, and operational faces

This module bundles one concrete semantic span into the large set-family CwF.
For a standard HOL model generated from small base carriers:

* every simple type and term is interpreted through an internal Tarski code;
* dependent products, dependent sums, contextual identity elimination, and a
  substitution-stable Pi/Sigma-closed Tarski universe inhabit the same CwF;
* exact evidence for a proof-relevant branching realization is another
  internal Tarski code in that CwF; and
* genuinely dependent evidence and varying universe families are proved not
  to descend to the selected coarse/simple observations.

The span deliberately has no field for reflection, quotation, effects in
conversion, a proof calculus, or a surface language.  Those structures need
additional interpretations or adequacy laws; the common set model alone does
not manufacture them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SetFamilySemanticSpan

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualEffectValuation
open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
open Mettapedia.GSLT.Dynamics.BranchingEvidenceTarskiInterpretation
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation
open Mettapedia.Logic.HOL.Embedding.LiftedStandardModelTarskiInterpretation
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.CwfTarskiUniverse
open Mettapedia.TypeTheory.CwfTarskiUniverse.SetFamilies
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

universe v

variable {Base : Type} {Const : Ty Base → Type v}

/-- Evidence that the three semantic faces meet in the same large
set-family CwF, together with the boundaries that prevent collapse. -/
structure SemanticSpan
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) where
  holTypeCodes :
    ∀ (context : Ctx Base) (A : Ty Base)
      (valuation : AdmissibleContext
        (liftedStandardModel SmallCarrier constantDenotation) context),
      Nonempty
        (smallTypes.{0}.el
            (typeCode SmallCarrier (context :=
              AdmissibleContext
                (liftedStandardModel SmallCarrier constantDenotation) context)
              A)
            valuation ≃
          AdmissibleValue
            (liftedStandardModel SmallCarrier constantDenotation) A)
  holTermSubstitution :
    ∀ {source target : Ctx Base} {A : Ty Base}
      (term : Term Const target A)
      (substitution :
        (ContextualStructure.holScwf Base Const).Sub source target),
      semanticCwf.{0}.tmSub
          (codedTerm SmallCarrier constantDenotation term)
          (interpretSubstitution
            (liftedStandardModel SmallCarrier constantDenotation)
            substitution) =
        codedTerm SmallCarrier constantDenotation
          ((ContextualStructure.holScwf Base Const).tmSub term substitution)
  products : Nonempty (DependentProductBeta semanticCwf.{0})
  sums : Nonempty (DependentSumBeta semanticCwf.{0})
  identity : Nonempty
    (IdentityEliminationBeta semanticCwf.{0}
      Families.identityFormation Families.identityReflexivity)
  tarskiUniverse : Nonempty (TarskiUniverse semanticCwf.{0})
  universeSubstitution : Nonempty smallTypes.{0}.SubstitutionStable
  universeProducts : Nonempty FibrewisePiClosed.{0}
  universeSums : Nonempty FibrewiseSigmaClosed.{0}
  operationalEvidenceCodes :
    ∀ state, Nonempty
      (smallTypes.{0}.el
          branchEvidenceCode
          (ULift.up state) ≃ exactFamily.Exact state)
  branchEvidenceNotCompletion :
    ¬ Nonempty
      (FamilyFactorization
        liftedCompletion
        (smallTypes.{0}.el
          branchEvidenceCode))
  varyingUniverseNotSimple :
    ∀ A : Ty Base,
      ¬ (∀ point : BoolContext.{0},
        Nonempty
          (smallTypes.{0}.el varyingCode point ≃
            AdmissibleValue
              (liftedStandardModel SmallCarrier constantDenotation) A))
  answerErasurePreservesHistory :
    sharedHistory visibleProgram () = sharedHistory evidenceProgram ()
  sequentialWorkSpan :
    sharedGrade sequentialWorkSpanValuation evidenceProgram () = some ⟨3, 3⟩
  parallelWorkSpan :
    sharedGrade parallelWorkSpanValuation evidenceProgram () = some ⟨3, 2⟩
  visibleAnswerDoesNotDetermineCost :
    ¬ Factors visibleOutcome realizedOutcomeCost

/-- The shared semantic span is inhabited for every small-carrier standard
HOL model. -/
def semanticSpan
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) :
    SemanticSpan SmallCarrier constantDenotation where
  holTypeCodes _context A valuation :=
    ⟨decodedAdmissibleTypeEquiv
      SmallCarrier constantDenotation A valuation⟩
  holTermSubstitution term substitution :=
    codedTerm_substitution SmallCarrier constantDenotation term substitution
  products := ⟨familiesProducts⟩
  sums := ⟨familiesSums⟩
  identity := ⟨Families.identityElimination⟩
  tarskiUniverse := ⟨smallTypes⟩
  universeSubstitution := ⟨smallTypes_substitutionStable⟩
  universeProducts := ⟨smallTypes_piClosed⟩
  universeSums := ⟨smallTypes_sigmaClosed⟩
  operationalEvidenceCodes state :=
    ⟨branchEvidenceEquiv state⟩
  branchEvidenceNotCompletion :=
    decodedEvidence_does_not_factor_through_completion
  varyingUniverseNotSimple :=
    varyingCode_not_an_interpreted_simple_type
      SmallCarrier constantDenotation
  answerErasurePreservesHistory := visible_erasure_preserves_history
  sequentialWorkSpan := evidenceProgram_sequential_workSpan
  parallelWorkSpan := evidenceProgram_parallel_workSpan
  visibleAnswerDoesNotDetermineCost := realized_cost_not_visible_determined

/-! ## Positive and negative controls -/

/-- Positive: the span contains both an internally coded simple fragment and
an internally coded proof-relevant operational family. -/
theorem span_has_both_internal_codes
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    (A : Ty Base) :
    Nonempty
        (smallTypes.{0}.el
            (typeCode SmallCarrier (context := PUnit) A) PUnit.unit ≃
          Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) ∧
      (∀ state, Nonempty
        (smallTypes.{0}.el
            branchEvidenceCode
            (ULift.up state) ≃ exactFamily.Exact state)) :=
  ⟨⟨decodedTypeEquiv SmallCarrier A PUnit.unit⟩,
    (semanticSpan SmallCarrier constantDenotation).operationalEvidenceCodes⟩

/-- Negative: sharing a dependent semantic CwF neither makes the completion
observer evidence-complete nor turns every dependent universe family into a
simple type. -/
theorem shared_model_does_not_collapse_faces
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) :
    (¬ Nonempty
      (FamilyFactorization
        liftedCompletion
        (smallTypes.{0}.el
          branchEvidenceCode))) ∧
      (∀ A : Ty Base,
        ¬ (∀ point : BoolContext.{0},
          Nonempty
            (smallTypes.{0}.el varyingCode point ≃
              AdmissibleValue
                (liftedStandardModel SmallCarrier constantDenotation) A))) :=
  ⟨(semanticSpan SmallCarrier constantDenotation).branchEvidenceNotCompletion,
    (semanticSpan SmallCarrier constantDenotation).varyingUniverseNotSimple⟩

#print axioms semanticSpan
#print axioms span_has_both_internal_codes
#print axioms shared_model_does_not_collapse_faces

end Mettapedia.TypeTheory.SetFamilySemanticSpan
