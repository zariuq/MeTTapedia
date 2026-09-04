import Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedAgreement

/-!
# Exact composition from named FOF to NNF

This module composes the authored binder-resolution and normalization
languages at their literal shared carrier.  The first stage emits the exact
encoding admitted by `TptpResolvedFofLanguageDef`; the second stage consumes
that same encoding through its proved structural inclusion and canonical
codec.

The theorems retain both stage boundaries.  This prevents a successful final
example from hiding a mismatched intermediate representation, and makes
no-invention an end-to-end property of arbitrary reducts rather than only of
the selected successful run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpNamedFofToNnfAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- A successful semantic binder resolution induces two exact authored GSLT
stages whose intermediate pattern is literally shared. -/
theorem closed_resolution_then_normalization_exact
    (source : TptpFofBinderResolution.NamedFormula)
    (resolved : TptpFofNormalizationSemantics.Formula 0)
    (resolutionExact :
      TptpFofBinderResolution.resolveClosedFormula? source = some resolved)
    (polarity : Bool) (normalizationFuel : Nat)
    (enough : TptpFofNormalizationLanguageDef.semanticHeight resolved ≤ normalizationFuel) :
    TptpNamedFofToResolvedLanguageDef.EventuallyExact
        (TptpNamedFofToResolvedLanguageDef.resolveClosed (TptpNamedFofLanguageDef.encodeFormula source))
        (TptpResolvedFofLanguageDef.encodeFormula resolved) ∧
      rewriteAt (engineBasePremises RelationEnv.empty)
          TptpFofNormalizationLanguageDef.language normalizationFuel
          (TptpFofNormalizationLanguageDef.request polarity
            (TptpResolvedFofLanguageDef.encodeFormula resolved)) =
        [TptpFofNnfLanguageDef.encodeFormula
          (TptpFofNormalizationSemantics.normalize polarity resolved)] := by
  exact ⟨TptpNamedFofToResolvedLanguageDef.resolveClosedFormula?_eventuallyExact
      source resolved resolutionExact,
    TptpFofNormalizationLanguageDef.resolvedFof_rewriteAt_exact
      polarity resolved normalizationFuel enough⟩

/-- Arbitrary reducts across the two-stage pipeline cannot invent either a
different resolved formula or a different NNF result. -/
theorem closed_resolution_then_normalization_no_invention
    (source : TptpFofBinderResolution.NamedFormula)
    (resolved : TptpFofNormalizationSemantics.Formula 0)
    (resolutionExact :
      TptpFofBinderResolution.resolveClosedFormula? source = some resolved)
    (resolutionFuel normalizationFuel : Nat) (polarity : Bool)
    (enough : TptpFofNormalizationLanguageDef.semanticHeight resolved ≤ normalizationFuel)
    (resolvedCandidate nnfCandidate : Pattern)
    (resolvedMember : resolvedCandidate ∈
      rewriteAt (engineBasePremises TptpNamedFofToResolvedLanguageDef.relations)
        TptpNamedFofToResolvedLanguageDef.language resolutionFuel
        (TptpNamedFofToResolvedLanguageDef.resolveClosed
          (TptpNamedFofLanguageDef.encodeFormula source)))
    (nnfMember : nnfCandidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofNormalizationLanguageDef.language normalizationFuel
        (TptpFofNormalizationLanguageDef.request polarity resolvedCandidate)) :
    resolvedCandidate = TptpResolvedFofLanguageDef.encodeFormula resolved ∧
      nnfCandidate =
        TptpFofNnfLanguageDef.encodeFormula
          (TptpFofNormalizationSemantics.normalize polarity resolved) := by
  have resolvedEquality := TptpNamedFofToResolvedLanguageDef.resolveClosedFormula?_no_invention
    source resolved resolutionExact resolutionFuel resolvedCandidate resolvedMember
  subst resolvedCandidate
  constructor
  · rfl
  · have exact := TptpFofNormalizationLanguageDef.resolvedFof_rewriteAt_exact
      polarity resolved normalizationFuel enough
    rw [exact] at nnfMember
    simpa using nnfMember

/-- A formula accepted from the official grammar-shaped AST traverses all
three authored languages with exact, explicitly retained intermediate
representations. -/
theorem official_ast_to_nnf_exact
    (officialSource : Pattern)
    (named : TptpFofBinderResolution.NamedFormula)
    (resolved : TptpFofNormalizationSemantics.Formula 0)
    (elaborated :
      TptpOfficialFofElaboration.decodeFormula? officialSource = some named)
    (resolutionExact :
      TptpFofBinderResolution.resolveClosedFormula? named = some resolved)
    (polarity : Bool) (normalizationFuel : Nat)
    (enough : TptpFofNormalizationLanguageDef.semanticHeight resolved ≤
      normalizationFuel) :
    TptpOfficialFofToNamedFormulaLanguageDef.EventuallyExact
        (TptpOfficialFofToNamedFormulaLanguageDef.request
          "tptp-fof-elab:formula" officialSource)
        (TptpNamedFofLanguageDef.encodeFormula named) ∧
      TptpNamedFofToResolvedLanguageDef.EventuallyExact
        (TptpNamedFofToResolvedLanguageDef.resolveClosed
          (TptpNamedFofLanguageDef.encodeFormula named))
        (TptpResolvedFofLanguageDef.encodeFormula resolved) ∧
      rewriteAt (engineBasePremises RelationEnv.empty)
          TptpFofNormalizationLanguageDef.language normalizationFuel
          (TptpFofNormalizationLanguageDef.request polarity
            (TptpResolvedFofLanguageDef.encodeFormula resolved)) =
        [TptpFofNnfLanguageDef.encodeFormula
          (TptpFofNormalizationSemantics.normalize polarity resolved)] := by
  exact ⟨TptpOfficialFofToNamedFormulaLanguageDef.decodeFormula_eventuallyExact
      officialSource elaborated,
    TptpNamedFofToResolvedLanguageDef.resolveClosedFormula?_eventuallyExact
      named resolved resolutionExact,
    TptpFofNormalizationLanguageDef.resolvedFof_rewriteAt_exact
      polarity resolved normalizationFuel enough⟩

/-- Arbitrary reducts from the official-AST, binder-resolution, and NNF
stages are forced to be the three semantic encodings. -/
theorem official_ast_to_nnf_no_invention
    (officialSource : Pattern)
    (named : TptpFofBinderResolution.NamedFormula)
    (resolved : TptpFofNormalizationSemantics.Formula 0)
    (elaborated :
      TptpOfficialFofElaboration.decodeFormula? officialSource = some named)
    (resolutionExact :
      TptpFofBinderResolution.resolveClosedFormula? named = some resolved)
    (officialFuel resolutionFuel normalizationFuel : Nat) (polarity : Bool)
    (enough : TptpFofNormalizationLanguageDef.semanticHeight resolved ≤
      normalizationFuel)
    (namedCandidate resolvedCandidate nnfCandidate : Pattern)
    (namedMember : namedCandidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpOfficialFofToNamedFormulaLanguageDef.language officialFuel
        (TptpOfficialFofToNamedFormulaLanguageDef.request
          "tptp-fof-elab:formula" officialSource))
    (resolvedMember : resolvedCandidate ∈
      rewriteAt
        (engineBasePremises TptpNamedFofToResolvedLanguageDef.relations)
        TptpNamedFofToResolvedLanguageDef.language resolutionFuel
        (TptpNamedFofToResolvedLanguageDef.resolveClosed namedCandidate))
    (nnfMember : nnfCandidate ∈
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofNormalizationLanguageDef.language normalizationFuel
        (TptpFofNormalizationLanguageDef.request polarity resolvedCandidate)) :
    namedCandidate = TptpNamedFofLanguageDef.encodeFormula named ∧
      resolvedCandidate = TptpResolvedFofLanguageDef.encodeFormula resolved ∧
      nnfCandidate =
        TptpFofNnfLanguageDef.encodeFormula
          (TptpFofNormalizationSemantics.normalize polarity resolved) := by
  have namedEquality :=
    TptpOfficialFofToNamedFormulaLanguageDef.decodeFormula_no_invention
      officialSource elaborated namedMember
  subst namedCandidate
  have resolvedEquality :=
    TptpNamedFofToResolvedLanguageDef.resolveClosedFormula?_no_invention
      named resolved resolutionExact resolutionFuel resolvedCandidate resolvedMember
  subst resolvedCandidate
  constructor
  · rfl
  · constructor
    · rfl
    · have exact := TptpFofNormalizationLanguageDef.resolvedFof_rewriteAt_exact
        polarity resolved normalizationFuel enough
      rw [exact] at nnfMember
      simpa using nnfMember

/-- If official syntax elaborates successfully but closed binder resolution
fails, the first authored stage still has its exact named result while the
second authored stage has no reduct at any fuel. -/
theorem official_ast_resolution_failure_exact
    (officialSource : Pattern)
    (named : TptpFofBinderResolution.NamedFormula)
    (elaborated :
      TptpOfficialFofElaboration.decodeFormula? officialSource = some named)
    (resolutionFailure :
      TptpFofBinderResolution.resolveClosedFormula? named = none) :
    TptpOfficialFofToNamedFormulaLanguageDef.EventuallyExact
        (TptpOfficialFofToNamedFormulaLanguageDef.request
          "tptp-fof-elab:formula" officialSource)
        (TptpNamedFofLanguageDef.encodeFormula named) ∧
      TptpNamedFofToResolvedLanguageDef.AlwaysEmpty
        (TptpNamedFofToResolvedLanguageDef.resolveClosed
          (TptpNamedFofLanguageDef.encodeFormula named)) := by
  exact ⟨TptpOfficialFofToNamedFormulaLanguageDef.decodeFormula_eventuallyExact
      officialSource elaborated,
    TptpNamedFofToResolvedLanguageDef.resolveClosedFormula?_none_alwaysEmpty
      named resolutionFailure⟩

#print axioms closed_resolution_then_normalization_exact
#print axioms closed_resolution_then_normalization_no_invention
#print axioms official_ast_to_nnf_exact
#print axioms official_ast_to_nnf_no_invention
#print axioms official_ast_resolution_failure_exact

end Mettapedia.GSLT.LanguageDef.TptpNamedFofToNnfAgreement
