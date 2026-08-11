import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
import Mettapedia.GSLT.LanguageDef.NIKGSLT
import Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy

/-!
# Exact Metamath authority at the NIK boundary

An admitted source prefix determines three independently useful views of one
Metamath judgment:

* execution of an authored label list by the verified `mm-lean4` normal fold;
* inhabitation of the generated ProofGSLT presentation; and
* supported declarative provability in the source-derived operational model.

The existing reflection and declarative-adequacy theorems identify all three.
This module packages that result as two exact certificate authorities with a
single meaning.  A dependent NIK family retains the evidence-kind tag, so a
native label list is never reinterpreted as a ProofGSLT wire article or vice
versa.
-/

namespace Mettapedia.Languages.Metamath.NIKAuthority

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.GSLT.LanguageDef.ProofGSLT.CheckerCapabilities
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceNormalFoldReflection
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy
open Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy

/-! The verified runtime intentionally exposes no global equality instance for
proof states.  Native replay nevertheless needs a decidable endpoint check.
The following private structural views derive exactly that instance without
changing the upstream checker API. -/

private def posView (position : Metamath.Verify.Pos) : Nat × Nat :=
  (position.line, position.col)

private theorem posView_injective : Function.Injective posView := by
  intro left right equal
  cases left
  cases right
  simpa [posView] using equal

private instance : DecidableEq Metamath.Verify.Pos :=
  posView_injective.decidableEq

private instance : DecidableEq Metamath.Verify.DJ :=
  inferInstanceAs (DecidableEq (String × String))

private def frameView (frame : RuntimeFrame) :
    Array Metamath.Verify.DJ × Array String :=
  (frame.dj, frame.hyps)

private theorem frameView_injective : Function.Injective frameView := by
  intro left right equal
  cases left
  cases right
  simpa [frameView] using equal

private instance : DecidableEq RuntimeFrame :=
  frameView_injective.decidableEq

private def proofTokenParserView :
    Metamath.Verify.ProofTokenParser → Nat × Nat
  | .start => (0, 0)
  | .preload => (1, 0)
  | .normal => (2, 0)
  | .compressed codepoint => (3, codepoint)

private theorem proofTokenParserView_injective :
    Function.Injective proofTokenParserView := by
  intro left right equal
  cases left <;> cases right <;> simp_all [proofTokenParserView]

private instance : DecidableEq Metamath.Verify.ProofTokenParser :=
  proofTokenParserView_injective.decidableEq

private def heapElementView : Metamath.Verify.HeapEl →
    Sum RuntimeFormula (RuntimeFormula × RuntimeFrame)
  | .fmla formula => .inl formula
  | .assert formula frame => .inr (formula, frame)

private theorem heapElementView_injective :
    Function.Injective heapElementView := by
  intro left right equal
  cases left <;> cases right <;> simp_all [heapElementView]

private instance : DecidableEq Metamath.Verify.HeapEl :=
  heapElementView_injective.decidableEq

private instance : DecidableEq RuntimeProofState :=
  fun left right =>
    decidable_of_iff
      (left.pos = right.pos ∧
        left.label = right.label ∧
        left.fmla = right.fmla ∧
        left.frame = right.frame ∧
        left.heap = right.heap ∧
        left.stack = right.stack ∧
        left.ptp = right.ptp ∧
        left.incomplete = right.incomplete)
      (by
        constructor
        · rintro ⟨hpos, hlabel, hfmla, hframe, hheap, hstack, hptp,
            hincomplete⟩
          cases left
          cases right
          simp_all
        · intro equal
          subst right
          simp)

/-- All fixed data and proved admission conditions for one source-owned
Metamath checking scope. -/
structure SourceScope where
  database : RuntimeDB
  source : SourcePrefix
  presentation : ValidatedPresentation
  base : RuntimeProofState
  sourceAdmitted :
    presentationOfSourcePrefix? source = some presentation.1
  runtimeProjects :
    projectPrefix? database = some source.toProjection
  baseStackEmpty : base.stack = #[]

namespace SourceScope

variable (scope : SourceScope)

/-- Admission of the source presentation also supplies the runtime-projection
presentation equation required by the normal-fold reflection theorem. -/
theorem projectionAdmitted :
    presentationOfProjection? scope.source.toProjection =
      some scope.presentation.1 := by
  rw [← presentationOfSourcePrefix?_eq_runtime]
  exact scope.sourceAdmitted

end SourceScope

/-- The exact supported claim domain.  Frame-respect is carried by the claim
rather than silently assumed by the checker. -/
structure Claim (scope : SourceScope) where
  formula : ConstantHeadedFormula
  frameRespect :
    formulaSymbolsRespectFrame
      (floatingVariableNames scope.source.activeHypotheses) formula = true

/-- Successful execution of precisely one submitted native label list. -/
def FoldAccepted (scope : SourceScope) (claim : Claim scope)
    (labels : List String) : Prop :=
  labels.foldlM
      (fun state label => scope.database.stepNormal state label) scope.base =
    Except.ok (scope.base.push claim.formula.toRuntime)

private instance foldAcceptedDecidable
    (scope : SourceScope) (claim : Claim scope) (labels : List String) :
    Decidable (FoldAccepted scope claim labels) := by
  unfold FoldAccepted
  infer_instance

/-- Native Metamath replay.  The certificate is the authored postfix label
sequence and acceptance is recomputed by `mm-lean4`. -/
def normalLabelChecker (scope : SourceScope) :
    Checker (Claim scope) (List String) where
  check claim labels := decide (FoldAccepted scope claim labels)

@[simp] theorem normalLabelChecker_accepts_iff
    (scope : SourceScope) (claim : Claim scope) (labels : List String) :
    (normalLabelChecker scope).check claim labels = true ↔
      FoldAccepted scope claim labels := by
  simp [normalLabelChecker]

/-- The generated ProofGSLT derivability predicate. -/
def Derivable (scope : SourceScope) (claim : Claim scope) : Prop :=
  Nonempty (Derivation scope.presentation
    (proves (encodeFormula claim.formula)))

/-- Independent supported declarative Metamath meaning. -/
def Meaning (scope : SourceScope) (claim : Claim scope) : Prop :=
  Metamath.Spec.Equivalence.SupportedProvable
    (sourceOperationalDatabase scope.source)
    (sourceOperationalCallerFrame scope.source)
    (Metamath.Spec.Equivalence.exprToFormula
      (Metamath.Spec.Equivalence.varMapOfFrame
        (sourceOperationalCallerFrame scope.source))
      (operationalExpr claim.formula))

/-- Generated ProofGSLT derivability is exactly existence of a native
mm-lean4 label trace in the same admitted scope. -/
theorem derivable_iff_exists_acceptedLabels
    (scope : SourceScope) (claim : Claim scope) :
    Derivable scope claim ↔
      ∃ labels : List String, FoldAccepted scope claim labels := by
  simpa [Derivable, FoldAccepted] using
    nonempty_provesDerivation_iff_exists_acceptedNormalLabels
      scope.database scope.source.toProjection scope.presentation scope.base
      claim.formula scope.projectionAdmitted scope.runtimeProjects
      scope.baseStackEmpty

/-- Native label-trace existence is exactly the independently stated
supported declarative semantics. -/
theorem exists_acceptedLabels_iff_meaning
    (scope : SourceScope) (claim : Claim scope) :
    (∃ labels : List String, FoldAccepted scope claim labels) ↔
      Meaning scope claim := by
  simpa [FoldAccepted, Meaning] using
    mmLean4_normalFold_exists_iff_supportedDeclarative
      scope.database scope.source scope.presentation scope.base claim.formula
      scope.sourceAdmitted scope.runtimeProjects scope.baseStackEmpty
      claim.frameRespect

/-- The generated calculus is sound and complete for supported declarative
Metamath provability on the explicitly admitted claim domain. -/
theorem derivable_iff_meaning
    (scope : SourceScope) (claim : Claim scope) :
    Derivable scope claim ↔ Meaning scope claim :=
  (derivable_iff_exists_acceptedLabels scope claim).trans
    (exists_acceptedLabels_iff_meaning scope claim)

def calculusExact (scope : SourceScope) :
    CalculusExact (Derivable scope) (Meaning scope) where
  sound claim := (derivable_iff_meaning scope claim).mp
  complete claim := (derivable_iff_meaning scope claim).mpr

/-- Native normal-label replay is exact for generated ProofGSLT
derivability. -/
theorem normalLabelChecker_derivationalAuthority
    (scope : SourceScope) :
    (normalLabelChecker scope).Authority (Derivable scope) where
  sound := by
    intro claim labels accepted
    apply (derivable_iff_exists_acceptedLabels scope claim).mpr
    exact ⟨labels,
      (normalLabelChecker_accepts_iff scope claim labels).mp accepted⟩
  complete := by
    intro claim derivable
    obtain ⟨labels, accepted⟩ :=
      (derivable_iff_exists_acceptedLabels scope claim).mp derivable
    exact ⟨labels,
      (normalLabelChecker_accepts_iff scope claim labels).mpr accepted⟩

/-- The same native checker is exact for supported declarative meaning, not
merely for a checker-defined certificate-existence predicate. -/
theorem normalLabelChecker_semanticAuthority
    (scope : SourceScope) :
    (normalLabelChecker scope).Authority (Meaning scope) :=
  semanticAuthority_of_replay_and_calculus
    (normalLabelChecker_derivationalAuthority scope) (calculusExact scope)

/-- The complete-judgment package records both exactness statements and their
independent bridge. -/
def completeJudgmentAuthority (scope : SourceScope) :
    CompleteJudgmentAuthority (Claim scope) (List String) where
  checker := normalLabelChecker scope
  Derivable := Derivable scope
  Meaning := Meaning scope
  replay := normalLabelChecker_derivationalAuthority scope
  calculus := calculusExact scope

/-- The already generated presentation, now equipped with its two-sided
declarative adequacy theorem. -/
def completeProofGSLT (scope : SourceScope) :
    SemanticallyCompleteProofGSLT (Claim scope) (Meaning scope) where
  presentation := scope.presentation
  adequacy :=
    { encode := fun claim => proves (encodeFormula claim.formula)
      derivation_sound := by
        intro claim derivable
        exact (derivable_iff_meaning scope claim).mp derivable
      derivation_complete := by
        intro claim meaningful
        exact (derivable_iff_meaning scope claim).mpr meaningful }

/-- The canonical article checker with its wire-certificate carrier exposed
at the module boundary. -/
def proofArticleChecker (scope : SourceScope) :
    Checker (Claim scope) WireArticle where
  check claim article :=
    (wireArticleAuthority () scope.presentation).check
      (proves (encodeFormula claim.formula)) article

/-- ProofGSLT wire articles give a second exact authority for the same
declarative Metamath meaning. -/
theorem proofArticleChecker_semanticAuthority
    (scope : SourceScope) :
    (proofArticleChecker scope).Authority (Meaning scope) := by
  constructor
  · intro claim article accepted
    apply (derivable_iff_meaning scope claim).mp
    exact (wireArticleAuthority () scope.presentation).sound accepted
  · intro claim meaningful
    obtain ⟨derivation⟩ :=
      (derivable_iff_meaning scope claim).mpr meaningful
    exact ⟨articleOfDerivation derivation,
      wireArticleAuthority_complete () derivation⟩

/-- A native label certificate exists exactly when a canonical ProofGSLT wire
article exists.  The equivalence is mediated by declarative meaning rather
than by translating one certificate format into the other. -/
theorem acceptedLabels_iff_acceptedArticle
    (scope : SourceScope) (claim : Claim scope) :
    (∃ labels : List String,
        (normalLabelChecker scope).check claim labels = true) ↔
      ∃ article : WireArticle,
        (proofArticleChecker scope).check claim article = true := by
  constructor
  · rintro ⟨labels, accepted⟩
    have meaningful :=
      (normalLabelChecker_semanticAuthority scope).sound
        claim labels accepted
    exact (proofArticleChecker_semanticAuthority scope).complete
      claim meaningful
  · rintro ⟨article, accepted⟩
    have meaningful :=
      (proofArticleChecker_semanticAuthority scope).sound
        claim article accepted
    exact (normalLabelChecker_semanticAuthority scope).complete
      claim meaningful

/-! ## One fail-closed NIK family with two evidence kinds -/

inductive EvidenceKind where
  | normalLabels
  | proofArticle
deriving DecidableEq

/-- Native and generic proof evidence coexist without representation
coercions.  Both component authorities are exact for `Meaning`. -/
def authorityFamily (scope : SourceScope) : AuthorityFamily EvidenceKind where
  Claim := fun _ => Claim scope
  Certificate
    | .normalLabels => List String
    | .proofArticle => WireArticle
  checker
    | .normalLabels => normalLabelChecker scope
    | .proofArticle => proofArticleChecker scope
  Certified := fun _ => Meaning scope
  Meaning := fun _ => Meaning scope
  projection := by
    intro kind
    cases kind with
    | normalLabels =>
        exact (normalLabelChecker_semanticAuthority scope).toProjection
    | proofArticle =>
        exact (proofArticleChecker_semanticAuthority scope).toProjection

/-- Cross-format evidence fails closed at the packed NIK boundary. -/
theorem normalLabels_rejected_for_articleClaim
    (scope : SourceScope) (claim : Claim scope) (labels : List String) :
    (authorityFamily scope).packedChecker.check
      ⟨EvidenceKind.proofArticle, claim⟩
      ⟨EvidenceKind.normalLabels, labels⟩ = false := by
  exact (authorityFamily scope).packedChecker_rejects_wrongKind
    (claimKind := EvidenceKind.proofArticle)
    (certificateKind := EvidenceKind.normalLabels)
    (by decide) claim labels

/-- Every supported declarative claim has an accepting execution in the
meta-level NIK GSLT for each selected evidence kind. -/
theorem meaning_has_accepting_NIK_execution
    (scope : SourceScope) (kind : EvidenceKind) (claim : Claim scope)
    (meaningful : Meaning scope claim) :
    ∃ certificate : (authorityFamily scope).PackedCertificate,
      (Mettapedia.GSLT.LanguageDef.NIKGSLT.Family.theory
        (authorityFamily scope)).MultiStep
        (.submitted ⟨kind, claim⟩ certificate)
        (.accepted ⟨kind, claim⟩) :=
  Mettapedia.GSLT.LanguageDef.NIKGSLT.Family.certified_has_accepting_execution
    (authorityFamily scope) ⟨kind, claim⟩ meaningful

end Mettapedia.Languages.Metamath.NIKAuthority
