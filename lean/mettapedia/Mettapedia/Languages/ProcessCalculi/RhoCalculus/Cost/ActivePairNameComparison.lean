import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveComparison
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePair

/-!
# Name-only canonical comparison for the actual funded COMM rule

Distinct closed quotations of a nonempty generated output compare by the
source-selected base reflection declaration. A different quoted input is
rejected, while signature values remain literal. These are controls of the
comparison adapter, not claims that a new scoped matcher has been installed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairNameComparison

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedReflectiveComparison

abbrev profile := ActivePair.presentation.reflection.1

def declaration : ReflectivePresentationDecl :=
  costBaseReflectivePresentationDecl rhoReflectivePresentation

theorem declaration_selected :
    matchingPresentationForRule? profile ActivePair.rule = some declaration := rfl

theorem channel_declared : ActivePair.rule.typeContext.filter
    (fun entry => entry.1 == costSourceSchemaName "n") =
      [(costSourceSchemaName "n", .base declaration.nameSort)] := by decide +kernel

/-- The actual channel declaration authorizes exactly the existing base
canonical comparison, independently of any spelling of the two names. -/
theorem channel_comparison (left right : Pattern) :
    bodyComparison profile ActivePair.rule (costSourceSchemaName "n") left right =
      canonicalEquivalent declaration left right :=
  bodyComparison_selected_name profile ActivePair.rule declaration _
    declaration_selected channel_declared left right

/-- The actual signature variable has its own result sort. Canonical name
comparison cannot weaken its literal authorization check. -/
theorem signature_comparison (left right : Pattern) :
    bodyComparison profile ActivePair.rule (costAdministrativeSchemaName "signature")
      left right = (left == right) := by
  apply bodyComparison_other_sort profile ActivePair.rule declaration _
    (.base costSignatureSortName) declaration_selected <;> decide +kernel

def sendProcess : Pattern := .apply (costBaseConstructorName "POutputK")
  [FiniteWhole.canonicalChannel, FiniteWhole.zero, FiniteWhole.zero]

def quotedSend : Pattern := .apply (costBaseConstructorName "NQuote") [sendProcess]

def expandedQuotedSend : Pattern := .apply (costBaseConstructorName "NQuote")
  [.collection .hashBag [FiniteWhole.baseZero, sendProcess] none]

def quotedReceive : Pattern := .apply (costBaseConstructorName "NQuote")
  [.apply (costBaseConstructorName "PInput")
    [FiniteWhole.canonicalChannel, .lambda none FiniteWhole.zero]]

theorem quotedSend_typed : HasSort ActivePair.language FreeTypeContext.empty []
    quotedSend (costBaseSortName "Name") :=
  checkHasType_sound (by decide +kernel)

theorem expandedQuotedSend_typed : HasSort ActivePair.language FreeTypeContext.empty []
    expandedQuotedSend (costBaseSortName "Name") :=
  checkHasType_sound (by decide +kernel)

theorem quotedReceive_typed : HasSort ActivePair.language FreeTypeContext.empty []
    quotedReceive (costBaseSortName "Name") :=
  checkHasType_sound (by decide +kernel)

/-- Both spellings retain a nonempty output in their canonical quotation;
they do not reduce to the quotation of the parallel unit. -/
theorem distinct_nonempty_quotations :
    quotedSend ≠ expandedQuotedSend ∧
      canonicalEquivalent declaration quotedSend expandedQuotedSend = true ∧
      canonicalEquivalent declaration quotedSend FiniteWhole.canonicalChannel = false := by
  decide +kernel

theorem equivalent_channels_accepted :
    bodyComparison profile ActivePair.rule (costSourceSchemaName "n")
      quotedSend expandedQuotedSend = true := by
  rw [channel_comparison]
  exact distinct_nonempty_quotations.2.1

theorem different_channels_rejected :
    canonicalEquivalent declaration quotedSend quotedReceive = false ∧
      bodyComparison profile ActivePair.rule (costSourceSchemaName "n")
        quotedSend quotedReceive = false := by
  rw [channel_comparison]
  decide +kernel

def productSignature : Pattern := .apply costSignatureProductConstructorName
  [FiniteWhole.unitSignature, FiniteWhole.unitSignature]

theorem signatures_typed :
    HasSort ActivePair.language FreeTypeContext.empty []
      FiniteWhole.unitSignature costSignatureSortName ∧
    HasSort ActivePair.language FreeTypeContext.empty []
      productSignature costSignatureSortName := by
  constructor <;> exact checkHasType_sound (by decide +kernel)

theorem distinct_signatures_rejected :
    FiniteWhole.unitSignature ≠ productSignature ∧
      bodyComparison profile ActivePair.rule (costAdministrativeSchemaName "signature")
        FiniteWhole.unitSignature productSignature = false := by
  rw [signature_comparison]
  decide +kernel

/-- The policy does not run the name normalizer at a non-name slot. These
arguments intentionally test the comparator outside the slot's typed domain;
the typed signature rejection is established separately above. -/
theorem equivalent_names_remain_distinct_at_signature_slot :
    bodyComparison profile ActivePair.rule (costAdministrativeSchemaName "signature")
      quotedSend expandedQuotedSend = false := by
  rw [signature_comparison]
  decide +kernel

/-- A duplicated name row, even with identical result sorts, does not select
one declaration opportunistically. -/
theorem duplicate_channel_declaration_is_literal :
    bodyComparison profile
      { ActivePair.rule with typeContext :=
        [(costSourceSchemaName "n", .base declaration.nameSort),
         (costSourceSchemaName "n", .base declaration.nameSort)] }
      (costSourceSchemaName "n") quotedSend expandedQuotedSend = false := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairNameComparison
