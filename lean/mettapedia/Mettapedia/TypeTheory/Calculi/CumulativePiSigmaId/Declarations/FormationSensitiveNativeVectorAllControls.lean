import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllTypeEvidence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaborationComponents
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchProjection
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllEvidenceComponents
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllNegativeComponents
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUndeclaredComponents
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalReplay

/-!
# Qualification controls for the native Vector `All` construction

The exact producer/replay observation shares checked telescope entries. Its
normalization hint is rewritten only during proof evaluation, using the
proved projection equation for the original bounded candidate producer.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Controls

open Presentation RussellTarski
open NativeNaturalVectorFamilies
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

private def proofEvaluationChoices : FormationSensitiveElaboration.Choices Tower.Head NativeVectorAll.decoder.Code :=
  { NativeVectorAll.choices with normalize := fun fuel term =>
      StructuralConversionSearch.termProjection NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel term }

private theorem proofEvaluationChoices_exact : NativeVectorAll.choices = proofEvaluationChoices := by
  have normalizationExact : (@NativeVectorAll.choices.normalize) =
      (fun {n} fuel (term : Tower.Tm n) =>
        StructuralConversionSearch.termProjection NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel term) := by
    funext n fuel term
    change (match StructuralConversionSearch.normalize NativeVectorAll.decoder NativeVectorAll.searchRoot
      (headEq := NativeVectorAll.rules.headEq) fuel term with
      | none => term
      | some candidate => candidate.term) = _
    rw [StructuralConversionSearch.normalize_eq_some_produce]
    exact StructuralConversionSearch.produce_term NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel term
  exact congrArg (fun normalize : {n : Nat} → Nat → Tower.Tm n → Tower.Tm n =>
    {NativeVectorAll.choices with normalize := normalize}) normalizationExact

private def entryAccepted {n : Nat} (context : Tower.Ctx n) (type : Tower.Tm n) : Bool :=
  FormationSensitiveElaboration.formationReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 128 context type

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem entryA : entryAccepted .nil (sortTm NativeVectorAll.elementLevel) = true := by
  unfold entryAccepted
  rw [proofEvaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem entryP : entryAccepted contextA predicateType = true := by
  unfold entryAccepted
  rw [proofEvaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem entryW : entryAccepted contextAP witnessType = true := by
  unfold entryAccepted
  rw [proofEvaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem entryN : entryAccepted contextAPW natTm = true := by
  unfold entryAccepted
  rw [proofEvaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem entryV : entryAccepted contextAPWN (vecApp (.var 3) (.var 0)) = true := by
  unfold entryAccepted
  rw [proofEvaluationChoices_exact]
  decide +kernel

private theorem context_checked : FormationSensitiveElaboration.contextReplayAccepted NativeVectorAll.rules
    NativeVectorAll.decoder NativeVectorAll.choices 128 contextAPWNV = true := by
  have a : FormationSensitiveElaboration.contextReplayAccepted NativeVectorAll.rules
      NativeVectorAll.decoder NativeVectorAll.choices 128 contextA = true := by
    rw [contextA, FormationSensitiveElaboration.contextReplayAccepted_snoc,
      FormationSensitiveElaboration.contextReplayAccepted_nil, Bool.true_and]
    exact entryA
  have p : FormationSensitiveElaboration.contextReplayAccepted NativeVectorAll.rules
      NativeVectorAll.decoder NativeVectorAll.choices 128 contextAP = true := by
    rw [contextAP, FormationSensitiveElaboration.contextReplayAccepted_snoc, a, Bool.true_and]
    exact entryP
  have w : FormationSensitiveElaboration.contextReplayAccepted NativeVectorAll.rules
      NativeVectorAll.decoder NativeVectorAll.choices 128 contextAPW = true := by
    rw [contextAPW, FormationSensitiveElaboration.contextReplayAccepted_snoc, p, Bool.true_and]
    exact entryW
  have n : FormationSensitiveElaboration.contextReplayAccepted NativeVectorAll.rules
      NativeVectorAll.decoder NativeVectorAll.choices 128 contextAPWN = true := by
    rw [contextAPWN, FormationSensitiveElaboration.contextReplayAccepted_snoc, w, Bool.true_and]
    exact entryN
  rw [contextAPWNV, FormationSensitiveElaboration.contextReplayAccepted_snoc, n, Bool.true_and]
  exact entryV

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem allType_accepted :
    accepted contextAPWNV allTypeControl (sortTm motiveLevel) = true := by
  rw [accepted, FormationSensitiveElaboration.elaborate_isSome_eq_components]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨context_checked, ?_⟩
  rw [proofEvaluationChoices_exact]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem allEvidence_accepted :
    accepted contextAPWNV allEvidenceControl allTypeControl = true := by
  rw [accepted, FormationSensitiveElaboration.elaborate_isSome_eq_components]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨context_checked,ReplayComponents.evidence_term_replay⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem wrong_type_refused :
    accepted contextAPWNV allEvidenceControl natTm = false := by
  rw [accepted, FormationSensitiveElaboration.elaborate_isSome_eq_components]
  apply Bool.and_eq_false_iff.mpr
  apply Or.inr
  exact ReplayComponents.evidence_at_nat_refused

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem undeclared_witness_refused :
    accepted contextAPWNV
      (allEvidence (.var 4) (.var 3) (.const `Undeclared.Witness)
        (.var 1) (.var 0)) allTypeControl = false := by
  rw [accepted, FormationSensitiveElaboration.elaborate_isSome_eq_components]
  apply Bool.and_eq_false_iff.mpr
  apply Or.inr
  exact ReplayComponents.Undeclared.evidence_with_undeclared_witness_refused

def verdicts : List (String × Bool) :=
  [("Vector All type is a type",
      accepted contextAPWNV allTypeControl (sortTm motiveLevel)),
   ("Vector All evidence has the generated type",
      accepted contextAPWNV allEvidenceControl allTypeControl),
   ("Vector All evidence is not a natural",
      !(accepted contextAPWNV allEvidenceControl natTm)),
   ("Vector All refuses an undeclared witness",
      !(accepted contextAPWNV
        (allEvidence (.var 4) (.var 3) (.const `Undeclared.Witness)
          (.var 1) (.var 0)) allTypeControl))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, allType_accepted, allEvidence_accepted,
    wrong_type_refused, undeclared_witness_refused]

theorem allType_formed :
    FormationSensitive.Judgment rules contextAPWNV
      allTypeControl (sortTm motiveLevel) :=
  accepted_sound allType_accepted

theorem allEvidence_typed :
    FormationSensitive.Judgment rules contextAPWNV
      allEvidenceControl allTypeControl :=
  accepted_sound allEvidence_accepted

namespace CanonicalAdequacyControls

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalAdequacy

def element : Tower.Tm 0 := .const `CanonicalAdequacy.Element
def predicate : Tower.Tm 0 := .const `CanonicalAdequacy.Predicate
def witness : Tower.Tm 0 := .const `CanonicalAdequacy.Witness
def first : Tower.Tm 0 := .const `CanonicalAdequacy.First
def second : Tower.Tm 0 := .const `CanonicalAdequacy.Second

def reflexivePredicate : Tower.Tm 0 :=
  .lam (.id natTm (.var 0) (.var 0))

def reflexiveWitness : Tower.Tm 0 :=
  .lam (.refl (.var 0))

def canonicalValues : List (Tower.Tm 0) :=
  [zeroTm, succApp zeroTm]

def canonicalBundleType : Tower.Tm 0 :=
  allType natTm reflexivePredicate (numeral canonicalValues.length)
    (encodeVector natTm canonicalValues)

def canonicalBundleEvidence : Tower.Tm 0 :=
  allEvidence natTm reflexivePredicate reflexiveWitness
    (numeral canonicalValues.length) (encodeVector natTm canonicalValues)

/-- The two-position native computation retains both witnesses in source
order and ends in the same singleton evidence as the semantic bundle. -/
theorem two_position_reduces :
    Steps
      (allEvidence element predicate witness (numeral 2)
        (encodeVector element [first, second]))
      (.pair (.app witness first)
        (.pair (.app witness second) unitEvidence)) := by
  simpa [pointwiseBundle, quoteBundle] using
    allEvidence_steps element predicate witness [first, second]

/-- Reordering distinguishable source positions cannot reuse the same object
bundle quotation. -/
theorem swapped_positions_refused :
    quoteBundle (pointwiseBundle witness [first, second]) ≠
      quoteBundle (pointwiseBundle witness [second, first]) :=
  two_position_order_retained witness first second (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem canonicalBundleAccepted :
    accepted .nil canonicalBundleEvidence canonicalBundleType = true := by
  change accepted .nil CanonicalChecking.evidence CanonicalChecking.type = true
  exact CanonicalChecking.Suffix.canonical_accepted

theorem canonicalBundle_formed :
    FormationSensitive.Judgment rules .nil
      canonicalBundleEvidence canonicalBundleType :=
  accepted_sound canonicalBundleAccepted

end CanonicalAdequacyControls

#print axioms allType_accepted
#print axioms allEvidence_accepted
#print axioms wrong_type_refused
#print axioms undeclared_witness_refused
#print axioms allType_formed
#print axioms allEvidence_typed
#print axioms CanonicalAdequacyControls.two_position_reduces
#print axioms CanonicalAdequacyControls.swapped_positions_refused
#print axioms CanonicalAdequacyControls.canonicalBundle_formed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Controls

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.TypeFormation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

theorem replay_checked : FormationSensitiveElaboration.replay NativeVectorAll.rules NativeVectorAll.decoder
    context subject (sortTm NativeVectorAll.motiveLevel) submission = true := by decide +kernel

theorem formed : FormationSensitive.Judgment NativeVectorAll.rules context subject
    (sortTm NativeVectorAll.motiveLevel) :=
  FormationSensitiveElaboration.replay_sound NativeVectorAll.rules NativeVectorAll.decoder replay_checked

def arguments {n : Nat} (element predicate length vector : Tower.Tm n) : Sub Tower.Head 4 n :=
  consSub vector (consSub length (consSub predicate (consSub element Fin.elim0)))

theorem inputs_typed (signature : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient element (sortTm NativeVectorAll.elementLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient predicate (.pi element (sortTm NativeVectorAll.motiveLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient vector (vecApp element length)) :
    FormationSensitive.CtxMor (extendRules NativeVectorAll.rules signature) context ambient
      (arguments element predicate length vector) := by
  intro index
  fin_cases index
  · change FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient vector (vecApp element length)
    exact vectorTyped
  · change FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient length natTm
    exact lengthTyped
  · change FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient predicate (.pi element (sortTm NativeVectorAll.motiveLevel))
    exact predicateTyped
  · change FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient element (sortTm NativeVectorAll.elementLevel)
    exact elementTyped

/-- Formation of the actual All type needs typed inputs, without a pointwise
inhabitant of the predicate. -/
theorem allType_typed (signature : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient element (sortTm NativeVectorAll.elementLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient predicate (.pi element (sortTm NativeVectorAll.motiveLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules NativeVectorAll.rules signature)
      ambient vector (vecApp element length)) :
    FormationSensitive.Typing (extendRules NativeVectorAll.rules signature) ambient
      (NativeVectorAll.allType element predicate length vector) (sortTm NativeVectorAll.motiveLevel) := by
  have instantiated := (formed.typing.includeSignature signature).substitute
    (inputs_typed signature elementTyped predicateTyped lengthTyped vectorTyped)
  have target : subst (arguments element predicate length vector) subject =
      NativeVectorAll.allType element predicate length vector := by
    rw [show subject = NativeVectorAll.allType (.var 3) (.var 2) (.var 1) (.var 0) from rfl,
      NativeVectorAll.subst_allType]
    rfl
  rw [target] at instantiated
  exact instantiated

def verdicts : List (String × Bool) :=
  [("Vector All forms without a pointwise witness",
    FormationSensitiveElaboration.replay NativeVectorAll.rules NativeVectorAll.decoder
      context subject (sortTm NativeVectorAll.motiveLevel) submission)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, replay_checked]

#print axioms replay_checked
#print axioms allType_typed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.TypeFormation
