import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataSoundness
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLNaturalDeductionTraceAttachment
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceDisplayedTerms
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizProofSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofCoverage
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalConservativity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeExtensionalProofTranslation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceExtensionalCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizDisplayed
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLCompiledMapFusionTrace
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLCompiledMapFusionUniverse
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLCompiledMapFusionHOTG
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLUniformListTraceRepresentation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceContextMorphisms
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceDisplayedSubstitution
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceProofBridge

/-!
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

# Source, trace, native, and operational integration boundary

This import boundary collects the independently checked pieces of the current
uniform-list integration:

* exact rule-data correspondence with native computation and derivations;
* a typed trace meaning for the native lambda/application fragment;
* contextual morphisms, comprehension lift and trace-operation naturality;
* displayed native renaming and substitution commuting with trace denotation;
* exact trace meaning for native representations in arbitrary mixed contexts;
* literal agreement of the native Leibniz and primitive equality operators;
* semantic soundness of the native compiler for every supported HOL proof rule;
* an exact structural decision procedure for that compiler's current coverage;
* an opaque extensional HOL profile with exactly the base conversion relation;
* typed native attachment of actual propositional- and function-extensionality
  source nodes whose premises compile in the constructive fragment;
* literal Aczel-trace meanings for those emitted native applications, retaining
  the canonical equality proof sections rather than only semantic validity;
* the compiler's retained source map-fusion proof, specialized through its
  explicit theory environment and consumed by dependent identity elimination;
* explicit bottom-universe bounds for that proof, identity family, and concrete
  dependent consumer, with the finite-closure counterexample retained;
* literal type-code agreement with the shifted full HOTG set carrier, including
  map fusion instantiated at actual powerset and least-universe operations.
-/
