import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedOccurrenceSemantics
import Mettapedia.OSLF.Framework.SelectedNativeTypeSemanticDecoding

/-!
# Occurrence-indexed step claims for selected native types

A carrier-level reduction claim remembers only its endpoints.  That is too
weak for an occurrence-indexed modal former: distinct authored rewrite rows
may have the same source and target patterns.  This module introduces one
private proof-formula constructor per selected occurrence and gives it an
independent meaning in terms of the exact proof-relevant occurrence step.

The wire label is intentionally compact.  Occurrence identity lives in the
typed view and its decoding theorem rather than in a long repeated string.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
open Mettapedia.OSLF.Framework.SelectedNativeTypeDisplayedSemantics
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedOccurrenceSemantics
open Mettapedia.OSLF.Framework.TypeSynthesis

abbrev Occurrence {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

namespace Naming

/-- Compact private occurrence-step label, parallel to the `$m:` modal
namespace. -/
def label (slot : Nat) : String :=
  String.ofList ('$' :: 'r' :: ':' :: List.replicate slot 's')

theorem label_injective : Function.Injective label := by
  intro first second equality
  have lengths := congrArg String.length equality
  simp [label] at lengths
  omega

/-- Decode exactly the private occurrence-step namespace. -/
def slot? (name : String) : Option Nat :=
  match name.toList with
  | '$' :: 'r' :: ':' :: suffix =>
      if suffix = List.replicate suffix.length 's' then some suffix.length
      else none
  | _ => none

@[simp] theorem slot?_label (slot : Nat) : slot? (label slot) = some slot := by
  simp [slot?, label]

theorem label_of_slot?_eq_some {name : String} {slot : Nat}
    (decoded : slot? name = some slot) : label slot = name := by
  unfold slot? at decoded
  split at decoded
  next suffix equation =>
    split at decoded
    next canonical =>
      cases decoded
      rw [← String.ofList_toList (s := name), equation]
      unfold label
      rw [canonical]
      simp only [List.length_replicate]
    next notCanonical => simp at decoded
  next => simp at decoded

/-- Occurrence-step claims and modal constructors occupy disjoint compact
private namespaces. -/
theorem label_ne_modal (stepSlot modalSlot : Nat) :
    label stepSlot ≠ SelectedModalNaming.label modalSlot := by
  intro equality
  have lists := congrArg String.toList equality
  simp [label, SelectedModalNaming.label] at lists

/-- Occurrence-step claims cannot collide with the longer generated
constructor namespaces. -/
theorem label_ne_generatedPrefix (slot : Nat) (suffix : List Char) :
    label slot ≠ String.ofList ('$' :: 'o' :: 's' :: 'l' :: 'f' :: suffix) := by
  intro equality
  have lists := congrArg String.toList equality
  simp [label] at lists

end Naming

/-- One occurrence-indexed proof-formula constructor.  Both endpoints use
the selected rewrite carrier from the source-indexed carrier resolver. -/
def termAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    GrammarRule where
  label := Naming.label slot.val
  category := ContextualInference.formulaType.name
  params :=
    [ .simple "source" (.base
        (SelectedNativeTypeSourceIndexedCarrierSupport.resolve demand
          (typingAt demand slot).rewriteType))
    , .simple "target" (.base
        (SelectedNativeTypeSourceIndexedCarrierSupport.resolve demand
          (typingAt demand slot).rewriteType)) ]
  syntaxPattern := []

def terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List GrammarRule :=
  List.ofFn (termAt demand)

@[simp] theorem length_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (terms demand).length = demand.occurrences.length := by
  simp [terms]

theorem termLabels {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (terms demand).map GrammarRule.label =
      List.ofFn fun slot : Occurrence demand => Naming.label slot.val := by
  simp [terms, termAt, List.map_ofFn, Function.comp_def]

theorem termLabels_nodup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    ((terms demand).map GrammarRule.label).Nodup := by
  rw [termLabels]
  apply List.nodup_ofFn_ofInjective
  intro first second equality
  apply Fin.ext
  exact Naming.label_injective equality

/-- Term-only extension supplying the occurrence-indexed claim constructors.
It adds no operational or proof authority by itself. -/
def extension {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : CalculusLanguageExtension where
  newTerms := terms demand

@[simp] theorem extension_terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newTerms = terms demand :=
  rfl

@[simp] theorem extension_types_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newTypes = [] :=
  rfl

@[simp] theorem extension_judgments_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newJudgments = [] :=
  rfl

@[simp] theorem extension_rules_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newRules = [] :=
  rfl

@[simp] theorem extension_equations_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newEquations = [] :=
  rfl

@[simp] theorem extension_rewrites_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (extension demand).newRewrites = [] :=
  rfl

/-- Formula asserting a step by this exact selected authored occurrence. -/
def claim {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (slot : Occurrence demand)
    (before after : Pattern) : Pattern :=
  .apply (Naming.label slot.val) [before, after]

/-- Decoded occurrence-step formula with its exact authored occurrence and
ordered endpoints retained as data. -/
structure View {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  occurrence : Occurrence demand
  before : Pattern
  after : Pattern
deriving DecidableEq

def View.encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (view : View demand) : Pattern :=
  claim view.occurrence view.before view.after

/-- Independent meaning: the exact selected occurrence, not merely some cold
step, produces the claimed target. -/
def View.Meaning {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (relations : RelationEnv)
    (view : View demand) : Prop :=
  OccursAt relations (typingAt demand view.occurrence) view.before view.after

/-- Occurrence-claim meaning is precisely matching, ordered authored-premise
evidence, and structural reconstruction of the selected right-hand side. -/
theorem View.meaning_iff_exists_activation
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {relations : RelationEnv}
    (view : View demand) :
    view.Meaning relations ↔
      ∃ activation : SelectedOccurrenceActivation relations
          (typingAt demand view.occurrence) view.before,
        activation.target = view.after :=
  occursAt_iff_exists_activation

/-- Forgetting exact occurrence identity yields an ordinary cold-language
step, but not conversely. -/
theorem View.meaning_implies_cold
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {relations : RelationEnv}
    {view : View demand} :
    view.Meaning relations →
      langReducesUsing relations source.language view.before view.after :=
  occursAt_implies_cold

/-- Universe-profile selection does not alter behavioral meaning when two
selected slots retain the same displayed rewrite typing. -/
theorem View.meaning_iff_of_typingAt_eq
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {relations : RelationEnv}
    {first second : Occurrence demand}
    (sameTyping : typingAt demand first = typingAt demand second)
    (before after : Pattern) :
    (View.Meaning relations
        { occurrence := first, before, after } ↔
      View.Meaning relations
        { occurrence := second, before, after }) := by
  simp only [View.Meaning]
  rw [sameTyping]

/-- Fail-closed decoder for exact occurrence-step formulas. -/
def decode? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Pattern → Option (View demand)
  | .apply name [before, after] =>
      match Naming.slot? name with
      | none => none
      | some index =>
          match SelectedNativeTypeSemanticDecoding.occurrence? demand index with
          | none => none
          | some occurrence => some { occurrence, before, after }
  | _ => none

@[simp] theorem decode?_encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (view : View demand) :
    decode? demand view.encode = some view := by
  simp [decode?, View.encode, claim,
    SelectedNativeTypeSemanticDecoding.occurrence?]

/-- Successful decoding reconstructs the complete original formula wire. -/
theorem encode_of_decode?_eq_some {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {pattern : Pattern}
    {view : View demand} (decoded : decode? demand pattern = some view) :
    view.encode = pattern := by
  cases pattern with
  | apply name arguments =>
      cases arguments with
      | nil => simp [decode?] at decoded
      | cons before rest =>
          cases rest with
          | nil => simp [decode?] at decoded
          | cons after tail =>
              cases tail with
              | cons extra more => simp [decode?] at decoded
              | nil =>
                  unfold decode? at decoded
                  cases labelDecode : Naming.slot? name with
                  | none => simp [labelDecode] at decoded
                  | some index =>
                      cases occurrenceDecode :
                          SelectedNativeTypeSemanticDecoding.occurrence?
                            demand index with
                      | none => simp [labelDecode, occurrenceDecode] at decoded
                      | some occurrence =>
                          simp only [labelDecode, occurrenceDecode] at decoded
                          cases decoded
                          have valueEquality : occurrence.val = index := by
                            have mapped := congrArg (Option.map Fin.val)
                              occurrenceDecode
                            have facts :
                                index < demand.occurrences.length ∧
                                  occurrence.val = index := by
                              simpa [
                                SelectedNativeTypeSemanticDecoding.occurrence?]
                                using mapped.symm
                            exact facts.2
                          change Pattern.apply (Naming.label occurrence.val)
                              [before, after] = Pattern.apply name [before, after]
                          rw [valueEquality,
                            Naming.label_of_slot?_eq_some labelDecode]
  | _ => simp [decode?] at decoded

/-! ## Negative controls -/

theorem firstOutOfRange_rejected {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (before after : Pattern) :
    decode? demand
      (.apply (Naming.label demand.occurrences.length) [before, after]) = none := by
  simp [decode?, SelectedNativeTypeSemanticDecoding.occurrence?]

theorem wrongArity_rejected {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (onlyBefore : Pattern) :
    decode? demand (.apply (Naming.label slot.val) [onlyBefore]) = none := by
  simp [decode?]

/-- Equal endpoints do not collapse distinct authored occurrence claims. -/
theorem distinct_occurrences_have_distinct_claims
    {source : ValidatedLanguageDef} {demand : SelectedNativeTypeDemand source}
    {first second : Occurrence demand} (different : first ≠ second)
    (before after : Pattern) :
    claim first before after ≠ claim second before after := by
  intro equality
  apply different
  apply Fin.ext
  apply Naming.label_injective
  exact (Pattern.apply.inj equality).1

end Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim
