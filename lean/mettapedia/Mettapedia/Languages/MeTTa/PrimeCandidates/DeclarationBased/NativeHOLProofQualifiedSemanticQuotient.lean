import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeQualifiedHOTGOperationalIntegration
import Mettapedia.GSLT.Core.SemanticImplementation
import Mettapedia.OSLF.Framework.GSLTQuotientCoherence

/-!
# Proof-qualified execution at the equation-class boundary

An operational presentation has two useful views.  Authored terms retain the
representative needed by an implementation, while semantic terms are classes
under the presentation's equations.  Literal equality belongs in the first
view only when the equations themselves are literal equality.  In the second
view, equality is exactly authored equivalence, neither stronger nor weaker.

This module sends the proof-qualified execution cospan to that semantic view.
The original proof evidence and both complete execution paths are retained;
only their states are mapped to equation classes.  The generated OSLF diamond
then observes the common result on the quotient, while exact-history
observation may still distinguish the two paths.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeHOLProofQualifiedSemanticQuotient

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Logic
open Mettapedia.Logic.HOL.Embedding
open NativeHOLProofQualifiedExecutionCospan

universe uTerm uEvidence

/-! ## The canonical quotient translation -/

/-- Every GSLT maps to its equation-class theory.  Equations become literal
equalities and every authored step retains its representatives as a semantic
step witness. -/
def quotientTranslation (theory : GSLT.{uTerm}) :
    OperationalTranslation theory (semanticTheory theory) where
  mapTerm := Quotient.mk theory.equations
  mapEquiv := Quotient.sound
  mapStep := semanticStep_mk

@[simp] theorem quotientTranslation_mapTerm (theory : GSLT.{uTerm}) :
    (quotientTranslation theory).mapTerm = Quotient.mk theory.equations :=
  rfl

/-- Quotienting commutes literally with every equation-respecting operational
translation. -/
theorem quotientTranslation_natural
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    (quotientTranslation source).comp translation.onSemanticTheories =
      translation.comp (quotientTranslation target) := by
  apply OperationalTranslation.ext
  rfl

/-- Equality after quotienting is exactly the authored equation relation. -/
theorem quotient_mk_eq_iff_equivalent (theory : GSLT.{uTerm})
    (left right : theory.Term) :
    Quotient.mk theory.equations left = Quotient.mk theory.equations right ↔
      theory.Equiv left right := by
  exact ⟨Quotient.exact, Quotient.sound⟩

/-- The semantic view does not identify representatives from different
equation classes. -/
theorem quotient_does_not_overcollapse (theory : GSLT.{uTerm})
    {left right : theory.Term} (different : ¬ theory.Equiv left right) :
    Quotient.mk theory.equations left ≠ Quotient.mk theory.equations right := by
  intro equal
  exact different (Quotient.exact equal)

/-- When the authored equations are exactly equality, the quotient projection
is injective, so choosing semantic classes loses no literal distinction. -/
theorem quotient_injective_of_equiv_iff_eq (theory : GSLT.{uTerm})
    (literal : ∀ left right : theory.Term,
      theory.Equiv left right ↔ left = right) :
    Function.Injective (quotientTranslation theory).mapTerm := by
  intro left right equal
  exact (literal left right).mp (Quotient.exact equal)

/-- The representation-independent laws of the semantic quotient: it is
natural for every operational translation, and its equality is exactly the
authored equation relation. -/
structure SemanticQuotientLaws : Prop where
  natural :
    ∀ {source target : GSLT.{uTerm}}
      (translation : OperationalTranslation source target),
      (quotientTranslation source).comp translation.onSemanticTheories =
        translation.comp (quotientTranslation target)
  exact :
    ∀ (theory : GSLT.{uTerm}) (left right : theory.Term),
      Quotient.mk theory.equations left =
          Quotient.mk theory.equations right ↔
        theory.Equiv left right

/-- The canonical quotient projection satisfies both general laws. -/
theorem semanticQuotientLaws : SemanticQuotientLaws.{uTerm} where
  natural := quotientTranslation_natural
  exact := quotient_mk_eq_iff_equivalent

/-! ## Proof-qualified paths descend without losing provenance -/

/-- Qualification induced on equation classes by one representative-level
qualification witness. -/
def QuotientQualification {theory : GSLT.{uTerm}}
    (Evidence : Type uEvidence)
    (Qualifies : Evidence → theory.Term → theory.Term → Prop)
    (evidence : Evidence)
    (left right : (semanticTheory theory).Term) : Prop :=
  ∃ leftRepresentative rightRepresentative : theory.Term,
    Quotient.mk theory.equations leftRepresentative = left ∧
      Quotient.mk theory.equations rightRepresentative = right ∧
      Qualifies evidence leftRepresentative rightRepresentative

/-- An equation-invariant authored observation becomes an ordinary predicate
on semantic states.  The target theory's remaining equations are equality. -/
def quotientObservation {theory : GSLT.{uTerm}}
    (observation : EquationPredicate theory.closure) :
    EquationPredicate (semanticTheory theory).closure where
  val := descendPredicate theory.closure observation
  property := by
    intro left right equal
    subst right
    exact Iff.rfl

@[simp] theorem quotientObservation_mk {theory : GSLT.{uTerm}}
    (observation : EquationPredicate theory.closure) (term : theory.Term) :
    quotientObservation observation (Quotient.mk theory.equations term) ↔
      observation term :=
  Iff.rfl

/-- Send a proof-qualified execution cospan to equation classes.  Evidence is
unchanged, qualification remembers its representatives, and both paths are
mapped step by step. -/
def toSemantic
    {theory : GSLT.{uTerm}} {Evidence : Type uEvidence}
    {Qualifies : Evidence → theory.Term → theory.Term → Prop}
    {observation : EquationPredicate theory.closure}
    {left right : theory.Term}
    (cospan : ProofQualifiedExecutionCospan theory Evidence Qualifies
      observation left right) :
    ProofQualifiedExecutionCospan (semanticTheory theory) Evidence
      (QuotientQualification Evidence Qualifies)
      (quotientObservation observation)
      (Quotient.mk theory.equations left)
      (Quotient.mk theory.equations right) :=
  cospan.mapAlong (quotientTranslation theory) _root_.id
    (quotientObservation observation)
    (fun _evidence first second qualified =>
      ⟨first, second, rfl, rfl, qualified⟩)
    (fun _ observed => observed)

@[simp] theorem toSemantic_evidence
    {theory : GSLT.{uTerm}} {Evidence : Type uEvidence}
    {Qualifies : Evidence → theory.Term → theory.Term → Prop}
    {observation : EquationPredicate theory.closure}
    {left right : theory.Term}
    (cospan : ProofQualifiedExecutionCospan theory Evidence Qualifies
      observation left right) :
    (toSemantic cospan).evidence = cospan.evidence :=
  rfl

@[simp] theorem toSemantic_apex
    {theory : GSLT.{uTerm}} {Evidence : Type uEvidence}
    {Qualifies : Evidence → theory.Term → theory.Term → Prop}
    {observation : EquationPredicate theory.closure}
    {left right : theory.Term}
    (cospan : ProofQualifiedExecutionCospan theory Evidence Qualifies
      observation left right) :
    (toSemantic cospan).apex =
      Quotient.mk theory.equations cospan.apex :=
  rfl

/-- Quotienting states retains the exact number of primitive steps on both
branches. -/
theorem toSemantic_path_lengths
    {theory : GSLT.{uTerm}} {Evidence : Type uEvidence}
    {Qualifies : Evidence → theory.Term → theory.Term → Prop}
    {observation : EquationPredicate theory.closure}
    {left right : theory.Term}
    (cospan : ProofQualifiedExecutionCospan theory Evidence Qualifies
      observation left right) :
    (toSemantic cospan).leftPath.length = cospan.leftPath.length ∧
      (toSemantic cospan).rightPath.length = cospan.rightPath.length := by
  exact ⟨OperationalTranslation.mapRoute_length _ _,
    OperationalTranslation.mapRoute_length _ _⟩

/-- Generated modal observation and complete route length coexist after the
semantic quotient; the quotient forgets representatives, not executions. -/
theorem toSemantic_modal_and_path_coherence
    {theory : GSLT.{uTerm}} {Evidence : Type uEvidence}
    {Qualifies : Evidence → theory.Term → theory.Term → Prop}
    {observation : EquationPredicate theory.closure}
    {left right : theory.Term}
    (cospan : ProofQualifiedExecutionCospan theory Evidence Qualifies
      observation left right) :
    semanticDiamond (semanticTheory theory).closure
        (quotientObservation observation)
        (Quotient.mk theory.equations left) ∧
      semanticDiamond (semanticTheory theory).closure
        (quotientObservation observation)
        (Quotient.mk theory.equations right) ∧
      (toSemantic cospan).leftPath.length = cospan.leftPath.length ∧
      (toSemantic cospan).rightPath.length = cospan.rightPath.length := by
  exact ⟨(toSemantic cospan).semanticDiamonds.1,
    (toSemantic cospan).semanticDiamonds.2,
    (toSemantic_path_lengths cospan).1,
    (toSemantic_path_lengths cospan).2⟩

/-- The modal component of the semantic projection is consumed by the
canonical OSLF generated from the quotient GSLT.  This is the same diamond as
the cospan law, exposed through the generated type system rather than through
a second, hand-written observation interface. -/
theorem toSemantic_generated_oslf_diamonds
    {theory : GSLT.{uTerm}} {Evidence : Type uEvidence}
    {Qualifies : Evidence → theory.Term → theory.Term → Prop}
    {observation : EquationPredicate theory.closure}
    {left right : theory.Term}
    (cospan : ProofQualifiedExecutionCospan theory Evidence Qualifies
      observation left right) :
    (gsltOSLF ((semanticTheory theory).closure)).satisfies (S := ())
        (Quotient.mk theory.equations left)
        ((gsltOSLF ((semanticTheory theory).closure)).diamond
          (quotientObservation observation)) ∧
      (gsltOSLF ((semanticTheory theory).closure)).satisfies (S := ())
        (Quotient.mk theory.equations right)
        ((gsltOSLF ((semanticTheory theory).closure)).diamond
          (quotientObservation observation)) := by
  exact (toSemantic cospan).semanticDiamonds

/-! ## Positive and negative controls -/

namespace Controls

open SemanticCoveredTranslation.QuotientCanary

/-- Distinct authored target representatives can denote one semantic state. -/
theorem equivalent_representatives_become_literal :
    Quotient.mk target.equations (some true) =
      Quotient.mk target.equations none := by
  apply Quotient.sound
  rfl

/-- Their authored representations remain different. -/
theorem equivalent_representatives_are_not_literal :
    (some true : Option Bool) ≠ none := by
  decide

/-- Non-equivalent representatives remain different even after quotienting. -/
theorem inequivalent_representatives_remain_distinct :
    Quotient.mk target.equations (some false) ≠
      Quotient.mk target.equations none := by
  apply quotient_does_not_overcollapse
  intro equivalent
  exact Bool.false_ne_true equivalent

end Controls

/-! ## The actual retained HOL/HOTG/native instance -/

namespace HOTGMapFusion

open HOLLeibnizNativeQualifiedHOTGOperationalIntegration

/-- The exact generated-OSLF endpoint of the retained HOTG map-fusion
connection. -/
abbrev GeneratedOSLFClaim (level : LevelExpr)
    (lower : ZFSetUniverseClosure.CofinalInaccessibles.{uTerm})
    (x : ZFSetUniformListTraceTypeInterpretation.Value
      ZFSetUniverseLift.carrierCode.{uTerm}
      Mettapedia.Logic.HOL.UniformListInduction.element) : Prop :=
    (gsltOSLF
      ((semanticTheory
        (IntrinsicNativeListMapComputation.reduction level 3)).closure)).satisfies
        (S := ())
        (Quotient.mk
          (IntrinsicNativeListMapComputation.reduction level 3).equations
          programs.unfused)
        ((gsltOSLF
          ((semanticTheory
            (IntrinsicNativeListMapComputation.reduction level 3)).closure)).diamond
          (quotientObservation (observation level lower x))) ∧
      (gsltOSLF
        ((semanticTheory
          (IntrinsicNativeListMapComputation.reduction level 3)).closure)).satisfies
        (S := ())
        (Quotient.mk
          (IntrinsicNativeListMapComputation.reduction level 3).equations
          programs.fused)
        ((gsltOSLF
          ((semanticTheory
            (IntrinsicNativeListMapComputation.reduction level 3)).closure)).diamond
          (quotientObservation (observation level lower x))) ∧
      (toSemantic (executionCospan level lower x)).leftPath.length = 18 ∧
      (toSemantic (executionCospan level lower x)).rightPath.length = 10 ∧
      (toSemantic (executionCospan level lower x)).evidence.proof =
        NativeHOLRecursiveProofNIKQualification.Controls.retainedMapFusionProof

/-- The retained HOL induction proof and the two native executions survive
the semantic quotient together.  Generated diamonds see the common HOTG
result, while the proof-relevant paths still expose the exact `18` versus `10`
step distinction. -/
theorem semantic_projection (level : LevelExpr)
    (lower : ZFSetUniverseClosure.CofinalInaccessibles.{uTerm})
    (x : ZFSetUniformListTraceTypeInterpretation.Value
      ZFSetUniverseLift.carrierCode.{uTerm}
      Mettapedia.Logic.HOL.UniformListInduction.element) :
    semanticDiamond
        (semanticTheory
          (IntrinsicNativeListMapComputation.reduction level 3)).closure
        (quotientObservation (observation level lower x))
        (Quotient.mk
          (IntrinsicNativeListMapComputation.reduction level 3).equations
          programs.unfused) ∧
      semanticDiamond
        (semanticTheory
          (IntrinsicNativeListMapComputation.reduction level 3)).closure
        (quotientObservation (observation level lower x))
        (Quotient.mk
          (IntrinsicNativeListMapComputation.reduction level 3).equations
          programs.fused) ∧
      (toSemantic (executionCospan level lower x)).leftPath.length = 18 ∧
      (toSemantic (executionCospan level lower x)).rightPath.length = 10 ∧
      (toSemantic (executionCospan level lower x)).evidence.proof =
        NativeHOLRecursiveProofNIKQualification.Controls.retainedMapFusionProof := by
  have coherence :=
    toSemantic_modal_and_path_coherence (executionCospan level lower x)
  have lengths := execution_path_lengths level lower x
  exact ⟨coherence.1, coherence.2.1,
    coherence.2.2.1.trans lengths.1,
    coherence.2.2.2.trans lengths.2,
    execution_retains_source level lower x⟩

/-- The concrete retained map-fusion proof reaches the actual OSLF generated
from the semantic native-list GSLT.  Both programs satisfy its diamond, while
the cospan still retains the source proof and the unequal execution lengths. -/
theorem generated_oslf_projection (level : LevelExpr)
    (lower : ZFSetUniverseClosure.CofinalInaccessibles.{uTerm})
    (x : ZFSetUniformListTraceTypeInterpretation.Value
      ZFSetUniverseLift.carrierCode.{uTerm}
      Mettapedia.Logic.HOL.UniformListInduction.element) :
    GeneratedOSLFClaim level lower x := by
  have modal :=
    toSemantic_generated_oslf_diamonds (executionCospan level lower x)
  have projection := semantic_projection level lower x
  exact ⟨modal.1, modal.2, projection.2.2.1, projection.2.2.2.1,
    projection.2.2.2.2⟩

end HOTGMapFusion

#print axioms quotientTranslation_natural
#print axioms quotient_mk_eq_iff_equivalent
#print axioms quotient_does_not_overcollapse
#print axioms semanticQuotientLaws
#print axioms toSemantic_path_lengths
#print axioms toSemantic_modal_and_path_coherence
#print axioms toSemantic_generated_oslf_diamonds
#print axioms Controls.equivalent_representatives_become_literal
#print axioms Controls.inequivalent_representatives_remain_distinct
#print axioms HOTGMapFusion.semantic_projection
#print axioms HOTGMapFusion.generated_oslf_projection

end NativeHOLProofQualifiedSemanticQuotient
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
