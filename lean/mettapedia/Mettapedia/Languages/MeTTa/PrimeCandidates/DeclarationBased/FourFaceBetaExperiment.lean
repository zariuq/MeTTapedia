import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CumulativeEmbedding
import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedBetaSubjectReduction

/-!
# One typed beta law across four independent faces

This experiment follows one nondependent fragment of the cumulative tower
through four representations:

* an intrinsically typed simple-function syntax;
* the cumulative-tower DTT calculus;
* the declaration-aware first-order GSLT substitution checker;
* an extensional function semantics and its set-valued graph.

The semantic faces are defined without reference to checker acceptance or DTT
derivability.  The bridge proves that the canonical open identity beta step is
the same event in all four faces.  A singleton ground model supplies a negative
reflection control: extensional validity alone need not recover raw syntax.

This is a deliberately small experiment, not yet a semantic model of the full
cumulative tower and not an implementation of Megalodon HOTG.  Its set-valued
face isolates the exact preservation and reflection obligations that such a
realization must later discharge.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FourFaceBetaExperiment
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Face 0: a small intrinsically typed function fragment -/


/-! ## Face 1: type-preserving erasure into the cumulative-tower DTT fragment -/


/-! ## Face 2: the declaration-aware deep GSLT checker -/

namespace DeepGSLT

open IntrinsicSTT
open TowerDTT
open DeclarationAwareSubstitutionCompiler
open DeclarationAwareSubstitutionLanguage

variable {context : List IntrinsicSTT.Ty}
variable {selectedType : IntrinsicSTT.Ty}

/-- Direct first-order erasure into the independent GSLT companion algebra. -/
def rawErase : {context : List IntrinsicSTT.Ty} →
    {selectedType : IntrinsicSTT.Ty} →
      IntrinsicSTT.Term context selectedType →
        DeclarationAwareSubstitutionCompiler.RawTerm
  | _, _, .var typedVar => .var (eraseVar typedVar).val
  | _, _, .lam body => .lam (rawErase body)
  | _, _, .app function argument =>
      .app (rawErase function) (rawErase argument)

/-- The two erasure routes commute before any checker is run. -/
@[simp] theorem rawErase_eq_eraseTower
    (term : IntrinsicSTT.Term context selectedType) :
    rawErase term =
      DeclarationAwareSubstitutionSemantics.erase (eraseTerm term) := by
  induction term with
  | var typedVar => rfl
  | lam body induction => simp [rawErase, eraseTerm,
      DeclarationAwareSubstitutionSemantics.erase,
      induction]
  | app function argument functionInduction argumentInduction =>
      simp [rawErase, eraseTerm,
        DeclarationAwareSubstitutionSemantics.erase, functionInduction,
        argumentInduction]

def rawBody : DeclarationAwareSubstitutionCompiler.RawTerm :=
  rawErase canonicalBody

def rawArgument : DeclarationAwareSubstitutionCompiler.RawTerm :=
  rawErase canonicalArgument

def canonicalTarget : Pattern :=
  encodeRaw (rawErase canonicalClaim.target)

@[simp] theorem canonicalTarget_eq_argument :
    canonicalTarget = encodeRaw rawArgument :=
  rfl

def canonicalGoal : Pattern :=
  rootBeta
    (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument))
    canonicalTarget

@[simp] theorem canonical_raw_substitution_commutes :
    substituteRaw 0 rawArgument rawBody = rawErase canonicalClaim.target :=
  rfl

/-- The proof-producing generic GSLT compiler accepts the same beta event. -/
theorem canonical_deep_checked :
    checkRaw DeclarationAwareSubstitutionLanguage.definition canonicalGoal
      (betaRawProof rawBody rawArgument) = true := by
  unfold canonicalGoal canonicalTarget
  rw [← canonical_raw_substitution_commutes]
  exact betaRawProof_accepts rawBody rawArgument

/-- No accepted artifact for the canonical source can name another target. -/
theorem canonical_deep_no_invention
    {target : Pattern} {proof : RawProof}
    (accepted :
      checkRaw DeclarationAwareSubstitutionLanguage.definition
        (rootBeta
          (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument)) target)
        proof = true) :
    target = canonicalTarget := by
  have reflected :=
    DeclarationAwareSubstitutionReflection.checkRaw_beta_reflects
      rawBody rawArgument accepted
  calc
    target = encodeRaw (substituteRaw 0 rawArgument rawBody) := reflected
    _ = canonicalTarget := by
      rw [canonical_raw_substitution_commutes]
      rfl

/-- A changed target is rejected even when the proof tree is the canonical
generated beta certificate. -/
theorem changed_target_rejected :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rootBeta
        (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument))
        (encodeRaw (.lam rawBody)))
      (betaRawProof rawBody rawArgument) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have targetEquality := betaRawProof_no_invention rawBody rawArgument accepted
  simp [rawBody, rawArgument, canonicalBody, canonicalArgument, eraseTerm,
    eraseVar, DeclarationAwareSubstitutionSemantics.erase, encodeRaw,
    DeclarationAwareSubstitutionSemantics.encode, substituteRaw] at targetEquality

end DeepGSLT

/-! ## Faces 3 and 4: shallow STT and set-valued validity -/


/-! ## A NIK profile whose scope and meaning are independently stated -/

namespace NIKProfile

open IntrinsicSTT
open TowerDTT
open DeepGSLT
open ExtensionalFaces
open DeclarationAwareSubstitutionCompiler
open DeclarationAwareSubstitutionLanguage

/-- Intrinsic tower scope for a proposed result of the shared beta source.
The target equality prevents the selected authority from accepting an
arbitrary result merely because the underlying beta theorem is inhabited. -/
def IntrinsicScope (target : Pattern) : Prop :=
  target = canonicalTarget ∧
    StepCore Presentation.Tower.rules.computation
        Presentation.Tower.rules.headEq
        (eraseTerm canonicalClaim.source) (eraseTerm canonicalClaim.target) ∧
      Presentation.Tower.HasType (eraseContext canonicalContext)
        (eraseTerm canonicalClaim.source) (.head .legacyGround) ∧
      Presentation.Tower.HasType (eraseContext canonicalContext)
        (eraseTerm canonicalClaim.target) (.head .legacyGround)

/-- The selected experimental theory keeps DTT scope and extensional meaning
separate. -/
def theory : TheoryFamily Unit where
  Signature := ValidatedCalculusLanguageDef
  signatureOf := fun _ => DeclarationAwareSubstitutionLanguage.definition
  Claim := fun _ => Pattern
  Scope := fun _ target => IntrinsicScope target
  Meaning := fun _ target =>
    target = canonicalTarget ∧
      ShallowValid canonicalClaim ∧ SetGraphValid canonicalClaim
  scope_sound := by
    intro _kind target intrinsic
    exact ⟨intrinsic.1, canonical_shallow_valid, canonical_setGraph_valid⟩

/-- Native certificates are ordinary declaration-aware GSLT proof trees. -/
def checker : Checker Pattern RawProof where
  check target proof :=
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rootBeta
        (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument)) target)
      proof

/-- Exact replay is noncircular: soundness lands in native DTT scope, while
completeness is supplied by the independently generated GSLT certificate. -/
theorem checker_authority :
    checker.Authority IntrinsicScope where
  sound := by
    intro target proof accepted
    change checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rootBeta
        (tmApp (tmLam (encodeRaw rawBody)) (encodeRaw rawArgument)) target)
      proof = true at accepted
    exact ⟨canonical_deep_no_invention accepted, canonical_typedBeta⟩
  complete := by
    intro target intrinsic
    have targetEquality : target = canonicalTarget := intrinsic.1
    subst target
    exact ⟨betaRawProof rawBody rawArgument, canonical_deep_checked⟩

def contract : AuthorityContract theory where
  Certificate := fun _ => RawProof
  checker := fun _ => checker
  scopeAuthority := fun _ => checker_authority

theorem accepted_projects_to_both_extensional_faces
    (target : Pattern) (proof : RawProof)
    (accepted : (contract.checker ()).check target proof = true) :
    target = canonicalTarget ∧
      ShallowValid canonicalClaim ∧ SetGraphValid canonicalClaim :=
  (contract.projection ()).sound target proof accepted

theorem canonical_certificate_replays :
    (contract.checker ()).check canonicalTarget
      (betaRawProof rawBody rawArgument) = true :=
  canonical_deep_checked

def changedTarget : Pattern := encodeRaw (.lam rawBody)

theorem changedTarget_ne_canonicalTarget :
    changedTarget ≠ canonicalTarget := by
  simp [changedTarget, canonicalTarget, rawBody, canonicalBody,
    canonicalArgument, eraseTerm, eraseVar,
    DeclarationAwareSubstitutionSemantics.erase, encodeRaw,
    DeclarationAwareSubstitutionSemantics.encode]

/-- The negative target is outside the intrinsic authority scope, not merely
rejected by one particular proof tree. -/
theorem changed_target_outside_scope :
    IntrinsicScope changedTarget → False :=
  fun scopeEvidence => changedTarget_ne_canonicalTarget scopeEvidence.1

end NIKProfile

/-! ## Axiom audit -/

#print axioms DeepGSLT.canonical_deep_checked
#print axioms DeepGSLT.canonical_deep_no_invention
#print axioms DeepGSLT.changed_target_rejected
#print axioms NIKProfile.checker_authority
#print axioms NIKProfile.accepted_projects_to_both_extensional_faces
#print axioms NIKProfile.canonical_certificate_replays
#print axioms NIKProfile.changed_target_outside_scope

end FourFaceBetaExperiment
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
