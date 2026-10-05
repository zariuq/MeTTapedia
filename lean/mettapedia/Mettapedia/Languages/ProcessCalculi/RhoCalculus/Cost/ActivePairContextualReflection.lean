import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairReflectionScope
import Mettapedia.OSLF.MeTTaIL.ScopedRuleInstantiation

/-!
# Scoped reflective activation of the funded synchronous pair

The original rule, binding declaration, matcher, and premise completion are
retained. Its explicit substitution uses binder-eliminating reflection with
the declaration selected by the existing Cost reflection profile. This is a
corrected interpretation, compared explicitly with the closed interpreter.
Canonical channel matching and general sorted subject reduction are separate
obligations; the scoped matcher used here compares repeated values literally.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairContextualReflection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ScopedRuleInstantiation
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

def declaration : ReflectivePresentationDecl :=
  costWrappedReflectivePresentationDecl rhoSyncIGSLT rhoReflectivePresentation

/-- The corrected operation uses the actual source-selected declaration. -/
theorem declaration_selected : substitutionPresentationForRule?
    ActivePair.presentation.reflection.1 ActivePair.rule = some declaration := rfl

abbrev operation := reflectiveOperation declaration

def correctedTarget : Pattern := .apply costContactConstructorName
  [.collection .hashBag
    [.collection .hashBag
      [FiniteWhole.zero, .apply (costWrappedConstructorName "PDrop") [.bvar 0]] none,
     FiniteWhole.zero] none,
   .apply costFundingConstructorName [FiniteWhole.retainedTail]]

/-- The exact existing matcher and RHS now release the local drop and lower
the surviving ambient index. Funding still loses exactly its matched head. -/
theorem corrected_open_firing : applyRuleWithAt operation
    Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty ActivePair.language 1
    ActivePair.rule ActivePair.openSource = [correctedTarget] := by decide +kernel

theorem corrected_target_typed : HasSort ActivePair.language FreeTypeContext.empty
    [.base (costBaseSortName "Name")] correctedTarget costWrappedSortName :=
  checkHasType_sound (by decide +kernel)

/-- Correction changes the escaping reflected result and the non-activating
ordinary scoped result. Neither of those immediate trees is substituted for it. -/
theorem corrected_target_comparisons :
    correctedTarget ≠ ActivePairReflectionScope.reflectedTarget ∧
    correctedTarget ≠ ActivePair.openTarget := by decide +kernel

def sourceWithStack (stack : Pattern) : Pattern := .apply costContactConstructorName
  [.apply costSignedConstructorName
    [decoratedRedex FiniteWhole.canonicalChannel ActivePair.openBody
      FiniteWhole.zero FiniteWhole.zero, FiniteWhole.unitSignature],
   .apply costFundingConstructorName [stack]]

/-- The repaired binder operation does not enable an empty purse. -/
theorem empty_purse_blocked : applyRuleWithAt operation
    Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty ActivePair.language 1
    ActivePair.rule (sourceWithStack FiniteWhole.emptyStack) = [] := by decide +kernel

/-- A distinct signature tree remains a rejected authorization key. -/
theorem wrong_key_blocked : applyRuleWithAt operation
    Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty ActivePair.language 1 ActivePair.rule
    (sourceWithStack (.apply costTokenStackConsConstructorName
      [.apply costSignatureProductConstructorName [FiniteWhole.unitSignature, FiniteWhole.unitSignature],
       FiniteWhole.retainedTail])) = [] := by decide +kernel

/-- Exact agreement on the established closed substitution domain, including
the existing normalization of rewrite-introduced quotation. -/
theorem closed_operation_agrees {body replacement : Pattern}
    (bodySafe : body.isWellScopedAt 1 = true)
    (replacementSafe :
      (normalizeReflectiveReplacement declaration replacement).isWellScopedAt 0 = true) :
    operation replacement body = substituteReflective declaration 0
      (normalizeReflectiveReplacement declaration replacement) body :=
  closed_agreement declaration bodySafe replacementSafe

/-- A closed actual funded firing agrees with the established reflected
engine. Its channel occurrences are literally the same, as required by the
unchanged scoped matcher. -/
theorem closed_funded_firing :
    let source := ActivePair.fundedPair FiniteWhole.canonicalChannel FiniteWhole.localBody
      FiniteWhole.zero FiniteWhole.afterOutput FiniteWhole.unitSignature FiniteWhole.retainedTail
    applyRuleWithAt operation Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
      ActivePair.language 0 ActivePair.rule source = [FiniteWhole.target] ∧
    Mettapedia.OSLF.MeTTaIL.ReflectiveEngine.rewriteStepWithReflection
      ActivePair.presentation.reflection.1 ActivePair.language source = [FiniteWhole.target] := by
  decide +kernel

/-- The replacement remains an ambient occurrence beneath another binder. -/
theorem replacement_lifted_beneath_binder :
    operation
      (.apply (costWrappedConstructorName "NQuote")
        [.apply (costWrappedConstructorName "PDrop") [.bvar 0]])
      (.lambda none (.apply (costWrappedConstructorName "PDrop") [.bvar 1])) =
    .lambda none (.apply (costWrappedConstructorName "PDrop") [.bvar 1]) := by decide +kernel

/-- A free dropped quote remains inert. Only receiving the name grants this
activation provenance; this is not an unconditional Drop reduction rule. -/
theorem free_drop_inert :
    operation (.apply (costWrappedConstructorName "NQuote") [FiniteWhole.zero])
      (.apply (costWrappedConstructorName "PDrop")
        [.apply (costWrappedConstructorName "NQuote") [FiniteWhole.zero]]) =
    .apply (costWrappedConstructorName "PDrop")
      [.apply (costWrappedConstructorName "NQuote") [FiniteWhole.zero]] := by decide +kernel

theorem normalized_bound_name_activates :
    operation (.apply (costWrappedConstructorName "NQuote") [FiniteWhole.zero])
      (.apply (costWrappedConstructorName "PDrop")
        [.apply (costWrappedConstructorName "NQuote")
          [.apply (costWrappedConstructorName "PDrop") [.bvar 0]]]) =
      FiniteWhole.zero := by decide +kernel

/-- Ordinary scope does not manufacture a sealed literal name for an open
received payload. A retained/generated name carrier is still required. -/
theorem open_received_quote_boundary :
    let result := operation
      (.apply (costWrappedConstructorName "NQuote")
        [.apply (costWrappedConstructorName "PDrop") [.bvar 0]]) (.bvar 0)
    result.isWellScopedAt 1 = true ∧
      binderSafeAt (costWrappedConstructorName "NQuote") 1 result = false := by decide +kernel

/-- The generic open-scope theorem applies to the actual local/ambient body;
its name-form premise is checked on the source, not assumed for the result. -/
theorem open_body_scope_preserved :
    (operation (.apply (costWrappedConstructorName "NQuote") [FiniteWhole.zero])
      ActivePair.openBody).isWellScopedAt 1 = true := by
  apply instantiate_scoped declaration (ambient := 1) (depth := 0)
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Ill-formed compound names are outside the atomic-name interpretation;
ordinary binder scope alone would not establish its preservation premise. -/
theorem compound_name_rejected :
    namesAdmitted declaration
      (.apply (costWrappedConstructorName "PDrop") [.apply "undeclared" [.bvar 0]]) = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairContextualReflection
