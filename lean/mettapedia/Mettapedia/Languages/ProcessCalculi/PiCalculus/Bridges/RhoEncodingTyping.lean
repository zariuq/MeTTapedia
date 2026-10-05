import Mettapedia.GSLT.LanguageDef.WellSortedClosing
import Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefTypingAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

/-!
# Sorting the maintained pi-to-rho encoding

The restriction- and replication-free compiler uses atomic free names at
rho's name sort. Its input binders are closed by the shared typed-closing
law. This supplies the independent sort evidence required by authored rho
COMM; no execution result is used to justify its own sorting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefTypingAgreement
open Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

open private rhoPar_eq_parComponents_append from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
open private rhoNoLiteralQuote rhoNoLiteralQuoteList encode_rf_rhoNoLiteralQuote
  rhoNoLiteralQuote_closeFVar from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

/-- Every source atomic name denotes a rho name variable. -/
def rhoAtomicNameContext : FreeSortContext := fun _ => some "Name"

private theorem rho_bag_elements {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : HasSort rhoCalc free bound (.collection .hashBag elements none) "Proc") :
    ElementsHaveType rhoCalc free bound elements TypeExpr.proc := by
  change HasType rhoCalc free bound (.collection .hashBag elements none) TypeExpr.proc at typed
  generalize resultEq : TypeExpr.proc = result at typed
  cases typed with
  | collection _ => cases resultEq
  | collectionConstructor member shape elementsTyped =>
      simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [TypeExpr.bag, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType] at shape
      obtain ⟨_, elementTypeEq⟩ := shape
      rw [← elementTypeEq] at elementsTyped
      exact elementsTyped

private theorem typed_components {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} (typed : HasSort rhoCalc free bound pattern "Proc") :
    ElementsHaveType rhoCalc free bound
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents pattern)
      TypeExpr.proc := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;>
        try exact .cons typed (.nil _ _)
      exact rho_bag_elements typed
  | bvar | fvar | apply | lambda | multiLambda | subst =>
      exact .cons typed (.nil _ _)

private theorem rhoPar_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {left right : Pattern}
    (leftTyped : HasSort rhoCalc free bound left "Proc")
    (rightTyped : HasSort rhoCalc free bound right "Proc") :
    HasSort rhoCalc free bound (rhoPar left right) "Proc" := by
  have appendTyped : ∀ {first second : List Pattern},
      ElementsHaveType rhoCalc free bound first TypeExpr.proc →
      ElementsHaveType rhoCalc free bound second TypeExpr.proc →
      ElementsHaveType rhoCalc free bound (first ++ second) TypeExpr.proc := by
    intro first second typedFirst typedSecond
    induction first with
    | nil => exact typedSecond
    | cons first rest ih =>
        cases typedFirst with
        | cons head tail => exact .cons head (ih tail)
  rw [rhoPar_eq_parComponents_append]
  exact rho_parallel_hasSort
    (appendTyped (typed_components leftTyped) (typed_components rightTyped))

/-- The compiler's open output is sorted by the authored rho signature. -/
theorem encode_hasSort {process : Process} (free : RestrictionFree process)
    (namespaceName valueName : String) :
    HasSort rhoCalc (liftFreeSortContext rhoAtomicNameContext) []
      (encode process namespaceName valueName) "Proc" := by
  induction process generalizing namespaceName with
  | nil => exact rho_parallel_hasSort (.nil _ _)
  | par left right leftIH rightIH =>
      exact rhoPar_typed (leftIH free.1 _) (rightIH free.2 _)
  | input channel binder body bodyIH =>
      have closed := (bodyIH free namespaceName).closeFVar binder TypeExpr.name rfl
      exact rho_input_hasSort (.fvar rfl) closed
  | output channel datum =>
      exact rho_output_hasSort (.fvar rfl) (rho_drop_hasSort (.fvar rfl))
  | nu | replicate => exact False.elim free

private theorem rhoPar_representation {left right : Pattern}
    (leftObject : isObjectPattern left = true)
    (rightObject : isObjectPattern right = true)
    (leftMetadata : left.hasCanonicalBinderMetadata = true)
    (rightMetadata : right.hasCanonicalBinderMetadata = true) :
    isObjectPattern (rhoPar left right) = true ∧
      (rhoPar left right).hasCanonicalBinderMetadata = true := by
  have componentsObject : ∀ pattern : Pattern, isObjectPattern pattern = true →
      isObjectPatternList
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents pattern) = true := by
    intro pattern object
    cases pattern <;> try simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents,
      isObjectPatternList] using object
    case collection kind elements rest =>
      cases kind <;> cases rest <;>
        simp_all [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents,
          isObjectPattern, isObjectPatternList]
  have componentsMetadata : ∀ pattern : Pattern,
      pattern.hasCanonicalBinderMetadata = true →
      Pattern.hasCanonicalBinderMetadataList
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents pattern) = true := by
    intro pattern metadata
    cases pattern <;> try simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents,
      Pattern.hasCanonicalBinderMetadataList] using metadata
    case collection kind elements rest =>
      cases kind <;> cases rest <;>
        simp_all [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents,
          Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  rw [rhoPar_eq_parComponents_append]
  simp only [isObjectPattern, Option.isNone_none,
    isObjectPatternList_append, componentsObject left leftObject,
    componentsObject right rightObject, Bool.and_self,
    Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_append,
    componentsMetadata left leftMetadata, componentsMetadata right rightMetadata,
    and_self]

/-- The compiler produces object syntax with canonical binder metadata. -/
theorem encode_representation {process : Process} (free : RestrictionFree process)
    (namespaceName valueName : String) :
    isObjectPattern (encode process namespaceName valueName) = true ∧
      (encode process namespaceName valueName).hasCanonicalBinderMetadata = true := by
  induction process generalizing namespaceName with
  | nil => exact ⟨rfl, rfl⟩
  | par left right leftIH rightIH =>
      obtain ⟨leftObject, leftMetadata⟩ := leftIH free.1 (namespaceName ++ "_L")
      obtain ⟨rightObject, rightMetadata⟩ := rightIH free.2 (namespaceName ++ "_R")
      exact rhoPar_representation leftObject rightObject leftMetadata rightMetadata
  | input channel binder body bodyIH =>
      obtain ⟨bodyObject, bodyMetadata⟩ := bodyIH free namespaceName
      simpa [encode, rhoInput, piNameToRhoName, isObjectPattern, isObjectPatternList,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        isObjectPattern_closeFVar, hasCanonicalBinderMetadata_closeFVar]
        using And.intro bodyObject bodyMetadata
  | output => exact ⟨rfl, rfl⟩
  | nu | replicate => exact False.elim free

/-- The compiler is sorted in the established rho judgment as well as the
generic signature-generated one. -/
theorem encode_procWellSorted {process : Process} (free : RestrictionFree process)
    (namespaceName valueName : String) :
    ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
      (encode process namespaceName valueName) :=
  languageDefHasSort_to_procWellSorted (encode_hasSort free namespaceName valueName)
    (encode_representation free namespaceName valueName).1
    (encode_representation free namespaceName valueName).2

/-- An encoded listener's body is sorted under the released input binder. -/
theorem close_encode_procWellSorted {process : Process} (free : RestrictionFree process)
    (binder namespaceName valueName : String) :
    ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext ["Name"]
      (closeFVar 0 binder (encode process namespaceName valueName)) := by
  apply languageDefHasSort_to_procWellSorted
  · exact (encode_hasSort free namespaceName valueName).closeFVar binder TypeExpr.name rfl
  · rw [isObjectPattern_closeFVar]
    exact (encode_representation free namespaceName valueName).1
  · rw [hasCanonicalBinderMetadata_closeFVar]
    exact (encode_representation free namespaceName valueName).2

/-- The source fragment cannot create an extended set inside a rho process. -/
theorem encode_hashSetFree {process : Process} (free : RestrictionFree process)
    (namespaceName valueName : String) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.HashSetFree
      (encode process namespaceName valueName) :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary.rhoProcWellSorted_hashSetFree
    (encode_procWellSorted free namespaceName valueName)

private theorem noQuoteList_iff (patterns : List Pattern) :
    rhoNoLiteralQuoteList patterns = true ↔
      ∀ pattern ∈ patterns, rhoNoLiteralQuote pattern = true := by
  induction patterns with
  | nil => simp [rhoNoLiteralQuoteList]
  | cons pattern patterns ih => simp [rhoNoLiteralQuoteList, ih]

private theorem noQuote_scoped_binderSafe {pattern : Pattern} {depth : Nat}
    (noQuote : rhoNoLiteralQuote pattern = true)
    (scopeSafe : pattern.isWellScopedAt depth = true) :
    binderSafeAt "NQuote" depth pattern = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simpa only [binderSafeAt, Pattern.isWellScopedAt] using scopeSafe
  | hfvar name => rfl
  | happly constructor arguments ih =>
      have distinct : constructor ≠ "NQuote" := by
        intro equal
        subst constructor
        simp [rhoNoLiteralQuote] at noQuote
      have argumentsFree : rhoNoLiteralQuoteList arguments = true := by
        simpa [rhoNoLiteralQuote, distinct] using noQuote
      have argumentsScoped : Pattern.isWellScopedListAt depth arguments = true := scopeSafe
      have argumentsSafe : binderSafeListAt "NQuote" depth arguments = true := by
        rw [binderSafeListAt_eq_true_iff]
        intro argument membership
        exact ih argument membership ((noQuoteList_iff arguments).mp argumentsFree argument membership)
          ((isWellScopedListAt_eq_true_iff depth arguments).mp argumentsScoped argument membership)
      cases arguments with
      | nil => exact argumentsSafe
      | cons first rest =>
          cases rest with
          | nil => simpa [binderSafeAt, distinct] using argumentsSafe
          | cons second rest => exact argumentsSafe
  | hlambda metadata body ih => exact ih noQuote scopeSafe
  | hmultiLambda arity metadata body ih => exact ih noQuote scopeSafe
  | hsubst body replacement bodyIH replacementIH =>
      simp only [rhoNoLiteralQuote, Pattern.isWellScopedAt, Bool.and_eq_true] at noQuote scopeSafe
      simp only [binderSafeAt, Bool.and_eq_true]
      exact ⟨bodyIH noQuote.1 scopeSafe.1, replacementIH noQuote.2 scopeSafe.2⟩
  | hcollection kind elements rest ih =>
      rw [binderSafeAt, binderSafeListAt_eq_true_iff]
      intro element membership
      exact ih element membership ((noQuoteList_iff elements).mp noQuote element membership)
        ((isWellScopedListAt_eq_true_iff depth elements).mp scopeSafe element membership)

/-- Source quotations are absent in this fragment, so its ordinary closure
also respects rho's quotation boundary. -/
theorem encode_binderSafe {process : Process} (free : RestrictionFree process)
    (n v : String) : binderSafeAt "NQuote" 0 (encode process n v) = true := by
  apply noQuote_scoped_binderSafe (encode_rf_rhoNoLiteralQuote free n v)
  rw [isWellScopedAt_eq_lc_at]
  exact encode_rf_lc free n v

theorem close_encode_binderSafe {process : Process} (free : RestrictionFree process)
    (binder n v : String) :
    binderSafeAt "NQuote" 1 (closeFVar 0 binder (encode process n v)) = true := by
  apply noQuote_scoped_binderSafe
  · rw [rhoNoLiteralQuote_closeFVar]
    exact encode_rf_rhoNoLiteralQuote free n v
  · rw [isWellScopedAt_eq_lc_at]
    exact lc_at_closeFVar (encode_rf_lc free n v)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
