import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverseMapEvidence

/-!
# Evidence maps for native Vector All at neutral vectors

Both result-universe annotations support explicit maps on inhabitants, using
the existing Vector eliminator. Independent replay checks the open programs;
typed substitution and application transport inhabitants at arbitrary inputs.
The resulting equivalence concerns inhabitation. Judgmental equality, inverse
laws and preservation of witness identity are separate statements.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeNaturalVectorFamilies

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def forwardReplayed := FormationSensitiveElaboration.replay rules decoder
  Universes.context forward forwardType Certificate.forwardSubmission

def backwardReplayed := FormationSensitiveElaboration.replay rules decoder
  Universes.context backward backwardType Certificate.backwardSubmission

theorem forward_replayed : forwardReplayed = true := by
  rw [forwardReplayed, ← FormationSensitiveElaboration.replayWithSyntaxConversions_eq]
  decide +kernel
theorem backward_replayed : backwardReplayed = true := by
  rw [backwardReplayed, ← FormationSensitiveElaboration.replayWithSyntaxConversions_eq]
  decide +kernel

theorem forward_formed : FormationSensitive.Judgment rules Universes.context forward forwardType :=
  FormationSensitiveElaboration.replay_sound rules decoder forward_replayed

theorem backward_formed : FormationSensitive.Judgment rules Universes.context backward backwardType :=
  FormationSensitiveElaboration.replay_sound rules decoder backward_replayed

theorem forward_typed (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    FormationSensitive.Typing (extendRules rules extension) ambient
      (forwardAt element predicate length vector)
      (functionType resultLevel upperLevel element predicate length vector) := by
  have typed := (forward_formed.typing.includeSignature extension).substitute
    (CumulativeElimination.inputs_typed extension elementTyped predicateTyped lengthTyped vectorTyped)
  have typeExact : subst (Universes.arguments element predicate length vector) forwardType =
      functionType resultLevel upperLevel element predicate length vector := by
    rw [forwardType, substitute_functionType]
    rfl
  rw [typeExact] at typed
  exact typed

theorem backward_typed (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    FormationSensitive.Typing (extendRules rules extension) ambient
      (backwardAt element predicate length vector)
      (functionType upperLevel resultLevel element predicate length vector) := by
  have typed := (backward_formed.typing.includeSignature extension).substitute
    (CumulativeElimination.inputs_typed extension elementTyped predicateTyped lengthTyped vectorTyped)
  have typeExact : subst (Universes.arguments element predicate length vector) backwardType =
      functionType upperLevel resultLevel element predicate length vector := by
    rw [backwardType, substitute_functionType]
    rfl
  rw [typeExact] at typed
  exact typed

/-- The input vector may be neutral. The two implications use explicit object programs. -/
theorem inhabited_iff (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    (∃ evidence, FormationSensitive.Typing (extendRules rules extension) ambient evidence
      (Canonical.allTypeAtUniverse resultLevel element predicate length vector)) ↔
    (∃ evidence, FormationSensitive.Typing (extendRules rules extension) ambient evidence
      (Canonical.allTypeAtUniverse upperLevel element predicate length vector)) := by
  constructor
  · rintro ⟨evidence, typed⟩
    refine ⟨.app (forwardAt element predicate length vector) evidence, ?_⟩
    have mapped := FormationSensitive.Typing.appElim
      (forward_typed extension elementTyped predicateTyped lengthTyped vectorTyped) typed
    simpa only [inst0_rename_wk] using mapped
  · rintro ⟨evidence, typed⟩
    refine ⟨.app (backwardAt element predicate length vector) evidence, ?_⟩
    have mapped := FormationSensitive.Typing.appElim
      (backward_typed extension elementTyped predicateTyped lengthTyped vectorTyped) typed
    simpa only [inst0_rename_wk] using mapped

open NativeVectorAll.CanonicalAdequacy

def twoLower : Tower.Tm 0 := Canonical.allTypeAtUniverse resultLevel natTm twoPredicate
  (numeral twoValues.length) (encodeVector natTm twoValues)
def twoUpper : Tower.Tm 0 := Canonical.allTypeAtUniverse upperLevel natTm twoPredicate
  (numeral twoValues.length) (encodeVector natTm twoValues)
def twoForward : Tower.Tm 0 := .app (forwardAt natTm twoPredicate
  (numeral twoValues.length) (encodeVector natTm twoValues)) twoEvidence
def twoReturned : Tower.Tm 0 := .app (backwardAt natTm twoPredicate
  (numeral twoValues.length) (encodeVector natTm twoValues)) twoForward

theorem two_forward_function_typed :
    FormationSensitive.Typing (extendRules rules Signature.empty) .nil
      (forwardAt natTm twoPredicate (numeral twoValues.length) (encodeVector natTm twoValues))
      (functionType resultLevel upperLevel natTm twoPredicate
        (numeral twoValues.length) (encodeVector natTm twoValues)) :=
  forward_typed Signature.empty
    ((checked_sound two_element_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_predicate_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_length_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_vector_checked).typing.includeSignature Signature.empty)

theorem two_backward_function_typed :
    FormationSensitive.Typing (extendRules rules Signature.empty) .nil
      (backwardAt natTm twoPredicate (numeral twoValues.length) (encodeVector natTm twoValues))
      (functionType upperLevel resultLevel natTm twoPredicate
        (numeral twoValues.length) (encodeVector natTm twoValues)) :=
  backward_typed Signature.empty
    ((checked_sound two_element_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_predicate_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_length_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_vector_checked).typing.includeSignature Signature.empty)

/-- Both maps act on the existing nonconstant two-position predicate example. -/
theorem two_maps_typed :
    FormationSensitive.Typing (extendRules rules Signature.empty) .nil twoForward twoUpper ∧
    FormationSensitive.Typing (extendRules rules Signature.empty) .nil twoReturned twoLower := by
  have elementTyped := (checked_sound two_element_checked).typing.includeSignature Signature.empty
  have predicateTyped := (checked_sound two_predicate_checked).typing.includeSignature Signature.empty
  have lengthTyped := (checked_sound two_length_checked).typing.includeSignature Signature.empty
  have vectorTyped := (checked_sound two_vector_checked).typing.includeSignature Signature.empty
  have source := (checked_sound two_evidence_checked).typing.includeSignature Signature.empty
  have forwardFunction := forward_typed Signature.empty elementTyped predicateTyped lengthTyped vectorTyped
  have forwardResult : FormationSensitive.Typing (extendRules rules Signature.empty)
      .nil twoForward twoUpper := by
    simpa only [twoForward, twoUpper, inst0_rename_wk] using
      FormationSensitive.Typing.appElim forwardFunction source
  have backwardFunction := backward_typed Signature.empty elementTyped predicateTyped lengthTyped vectorTyped
  have backwardResult : FormationSensitive.Typing (extendRules rules Signature.empty)
      .nil twoReturned twoLower := by
    simpa only [twoReturned, twoLower, inst0_rename_wk] using
      FormationSensitive.Typing.appElim backwardFunction forwardResult
  exact ⟨forwardResult, backwardResult⟩

theorem two_positions_inhabited :
    (∃ evidence, FormationSensitive.Typing (extendRules rules Signature.empty) .nil evidence twoLower) ∧
    (∃ evidence, FormationSensitive.Typing (extendRules rules Signature.empty) .nil evidence twoUpper) := by
  have source := (checked_sound two_evidence_checked).typing.includeSignature Signature.empty
  have comparison := inhabited_iff Signature.empty
    ((checked_sound two_element_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_predicate_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_length_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_vector_checked).typing.includeSignature Signature.empty)
  exact ⟨⟨twoEvidence, source⟩, comparison.mp ⟨twoEvidence, source⟩⟩

def projectionShortcut : Tower.Tm 4 := .lam (.snd (.var 0))
def projectionReplay := FormationSensitiveElaboration.replay rules decoder
  Universes.context projectionShortcut forwardType Certificate.forwardSubmission
def swappedReplay := FormationSensitiveElaboration.replay rules decoder
  Universes.context forward forwardType Certificate.backwardSubmission

/-- A certificate for the full indexed map does not certify a projection shortcut. -/
theorem projection_certificate_refused : projectionReplay = false := by
  rw [projectionReplay, ← FormationSensitiveElaboration.replayWithSyntaxConversions_eq]
  decide +kernel

/-- The reverse map's evidence cannot be substituted for the forward map's evidence. -/
theorem swapped_certificate_refused : swappedReplay = false := by
  rw [swappedReplay, ← FormationSensitiveElaboration.replayWithSyntaxConversions_eq]
  decide +kernel

def conversionAccepted {n : Nat} (left right : Tower.Tm n) : Bool :=
  match choices.conversion 64 left right with
  | none => false
  | some code => code.check rules.headEq decoder.decode left right

def opaqueEvidence : Tower.Tm 1 := .var 0
def opaqueValues : List (Tower.Tm 1) := [zeroTm, zeroTm]
def opaqueForward : Tower.Tm 1 := .app
  (forwardAt natTm (.lam unitType) (numeral opaqueValues.length)
    (encodeVector natTm opaqueValues)) opaqueEvidence

def opaqueForwardConversion := conversionAccepted opaqueForward (PairSpine.expand 2 opaqueEvidence)
def opaqueHeadConversion := conversionAccepted (PairSpine.head 1 opaqueForward) (PairSpine.head 1 opaqueEvidence)
def opaqueTailConversion := conversionAccepted (PairSpine.tail 2 opaqueForward) (PairSpine.tail 2 opaqueEvidence)
def expansionSyntaxDifferent := decide (PairSpine.expand 2 opaqueEvidence ≠ opaqueEvidence)

theorem opaque_forward_conversion : opaqueForwardConversion = true := by decide +kernel
theorem opaque_head_conversion : opaqueHeadConversion = true := by decide +kernel
theorem opaque_tail_conversion : opaqueTailConversion = true := by decide +kernel

/-- Raw pair expansion is not an assertion that its syntax equals the opaque input. -/
theorem expansion_syntax_distinct : PairSpine.expand 2 opaqueEvidence ≠ opaqueEvidence := by decide +kernel

theorem expansion_syntax_checked : expansionSyntaxDifferent = true := by decide +kernel

theorem opaque_forward_steps : TypedEquality.Reduces rules opaqueForward
    (PairSpine.expand 2 opaqueEvidence) := by
  rw [opaqueForward, forwardAt_eq_map]
  exact canonical_steps resultLevel upperLevel natTm (.lam unitType) opaqueValues opaqueEvidence

theorem opaque_head_steps : TypedEquality.Reduces rules (PairSpine.head 1 opaqueForward)
    (PairSpine.head 1 opaqueEvidence) := by
  simpa only [opaqueForward, forwardAt_eq_map] using
    canonical_head resultLevel upperLevel natTm (.lam unitType) opaqueValues opaqueEvidence 1 (by decide)

theorem opaque_tail_steps : TypedEquality.Reduces rules (PairSpine.tail 2 opaqueForward)
    (PairSpine.tail 2 opaqueEvidence) := by
  rw [opaqueForward, forwardAt_eq_map]
  exact canonical_tail resultLevel upperLevel natTm (.lam unitType) opaqueValues opaqueEvidence

theorem opaque_expansion_head : TypedEquality.Reduces rules
    (PairSpine.head 1 (PairSpine.expand 2 opaqueEvidence)) (PairSpine.head 1 opaqueEvidence) :=
  PairSpine.head_expand rules 2 1 opaqueEvidence (by decide)

theorem opaque_expansion_tail : TypedEquality.Reduces rules
    (PairSpine.tail 2 (PairSpine.expand 2 opaqueEvidence)) (PairSpine.tail 2 opaqueEvidence) :=
  PairSpine.tail_expand rules 2 opaqueEvidence

theorem opaque_roundtrip_head :
    TypedEquality.Reduces rules
      (PairSpine.head 1 (.app
        (map upperLevel resultLevel natTm (.lam unitType) (numeral opaqueValues.length)
          (encodeVector natTm opaqueValues))
        (.app (map resultLevel upperLevel natTm (.lam unitType) (numeral opaqueValues.length)
          (encodeVector natTm opaqueValues)) opaqueEvidence)))
      (PairSpine.head 1 opaqueEvidence) :=
  roundtrip_head resultLevel upperLevel natTm (.lam unitType) opaqueValues opaqueEvidence 1 (by decide)

theorem opaque_roundtrip_tail :
    TypedEquality.Reduces rules
      (PairSpine.tail 2 (.app
        (map upperLevel resultLevel natTm (.lam unitType) (numeral opaqueValues.length)
          (encodeVector natTm opaqueValues))
        (.app (map resultLevel upperLevel natTm (.lam unitType) (numeral opaqueValues.length)
          (encodeVector natTm opaqueValues)) opaqueEvidence)))
      (PairSpine.tail 2 opaqueEvidence) :=
  roundtrip_tail resultLevel upperLevel natTm (.lam unitType) opaqueValues opaqueEvidence

def verdicts : List (String × Bool) :=
  [("neutral Vector All lower-to-upper evidence map replays", forwardReplayed),
   ("neutral Vector All upper-to-lower evidence map replays", backwardReplayed),
   ("Vector All projection cannot reuse a map certificate", !projectionReplay),
   ("Vector All reverse certificate cannot certify the forward program", !swappedReplay),
   ("constructor Vector with opaque evidence replays its pair expansion", opaqueForwardConversion),
   ("constructor Vector evidence retains its second head observation", opaqueHeadConversion),
   ("constructor Vector evidence retains its final tail observation", opaqueTailConversion),
   ("pair expansion retains distinct raw syntax from its opaque input", expansionSyntaxDifferent)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, forward_replayed, backward_replayed, projection_certificate_refused,
    swapped_certificate_refused, opaque_forward_conversion, opaque_head_conversion,
    opaque_tail_conversion, expansion_syntax_checked, Bool.not_false, List.all_cons, List.all_nil, Bool.and_self]

#print axioms forward_formed
#print axioms backward_formed
#print axioms inhabited_iff
#print axioms two_maps_typed
#print axioms two_positions_inhabited
#print axioms projection_certificate_refused
#print axioms swapped_certificate_refused

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps
