import Mettapedia.GSLT.LanguageDef.BootstrapCell.CheckingWeakness
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# `CoreNIK` and the levelled reflexive cell

**`CoreNIK`** is the fixed, representation-independent statement about one
level: an implementation refines the abstract replay of a signature.  It has
two fields, exact soundness (every acceptance is the erasure of a
derivation) and completeness for representable derivations (every
derivation's erasure is accepted).

* Determinism is a consequence (`CoreNIK.goal_unique`).
* `CoreNIK` pins the implementation extensionally: `CoreNIK.iff_eq_replay`.
* Semantic qualification is a separate interface (`SemanticQualification`):
  `CoreNIK.accepted_meaning` composes acceptance, derivability and truth only
  when a qualification is supplied from outside.

Instances: replay itself, and the generic inference checker for every
validated calculus.  The too-strong kernel of `CheckingWeakness` is not a
`CoreNIK` implementation.

**The levelled cell.**  A reflexive cell (`ReflexiveCell`) is a validated
presentation of a calculus's replay rules.  `ReflexiveCell.layer` reads it as
a bootstrap layer at host level one in the vocabulary of `NIKMetalogic`:
* its claims are `LowerContract`s of kind `sourceSound` about level-zero
  checking facts;
* its certificates are level-one replay certificates;
* its checker is the generic checker run on the presentation;
* it is an exact authority for the claims' meaning, a derivation at level
  zero with the claimed erasure.

Every other contract kind is rejected, and by `LowerContract.target_ne_host`
no claim can target the host's own level.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe u

/-! ## `CoreNIK` -/

/-- **`CoreNIK`**: an implementation refines the abstract replay of a
signature. -/
structure CoreNIK (σ : ReplaySignature.{u}) (implementation : σ.Goal → RawProof → Bool) :
    Prop where
  sound : ∀ goal certificate, implementation goal certificate = true →
    ∃ derivation : σ.Deriv goal, derivation.erase = certificate
  complete : ∀ goal (derivation : σ.Deriv goal), implementation goal derivation.erase = true

namespace CoreNIK

variable {σ : ReplaySignature.{u}} {implementation : σ.Goal → RawProof → Bool}

/-- An accepted certificate determines its goal. -/
theorem goal_unique (core : CoreNIK σ implementation) {first second : σ.Goal}
    {certificate : RawProof} (firstAccepted : implementation first certificate = true)
    (secondAccepted : implementation second certificate = true) : first = second := by
  obtain ⟨firstDerivation, firstErased⟩ := core.sound first certificate firstAccepted
  obtain ⟨secondDerivation, secondErased⟩ := core.sound second certificate secondAccepted
  have firstReplay := firstDerivation.replay_erase
  have secondReplay := secondDerivation.replay_erase
  rw [firstErased] at firstReplay
  rw [secondErased] at secondReplay
  exact ReplaySignature.replay_goal_unique firstReplay secondReplay

/-- **`CoreNIK` determines the implementation**: it holds exactly for the
replay function itself, up to extensional equality. -/
theorem iff_eq_replay : CoreNIK σ implementation ↔ implementation = σ.replay := by
  constructor
  · intro core
    funext goal certificate
    apply Bool.eq_iff_iff.mpr
    rw [ReplaySignature.replay_iff]
    constructor
    · exact core.sound goal certificate
    · rintro ⟨derivation, rfl⟩
      exact core.complete goal derivation
  · rintro rfl
    exact ⟨fun goal certificate accepted =>
        (ReplaySignature.replay_iff goal certificate).mp accepted,
      fun _ derivation => derivation.replay_erase⟩

end CoreNIK

/-- Replay satisfies `CoreNIK`. -/
theorem coreNIK_replay (σ : ReplaySignature.{u}) : CoreNIK σ σ.replay :=
  CoreNIK.iff_eq_replay.mpr rfl

/-- The generic inference checker satisfies `CoreNIK` for every validated
calculus. -/
theorem coreNIK_checkRaw (definition : ValidatedCalculusLanguageDef) :
    CoreNIK (nikSignature definition) (checkRaw definition) :=
  CoreNIK.iff_eq_replay.mpr (funext fun goal => funext fun certificate =>
    checkRaw_eq_replay definition goal certificate)

/-- **Negative control.**  The too-strong kernel is not a `CoreNIK`
implementation. -/
theorem not_coreNIK_tooStrong :
    ¬ CoreNIK (CheckingWeakness.modusPonens ()) (CheckingWeakness.tooStrong ()) := by
  intro core
  have faithful : CheckingWeakness.Faithful CheckingWeakness.modusPonens
      CheckingWeakness.tooStrong := by
    rintro ⟨⟨⟩, goal, certificate⟩
    refine ⟨core.sound goal certificate, ?_⟩
    rintro ⟨derivation, erased⟩
    have erased' : derivation.erase = certificate := erased
    show CheckingWeakness.tooStrong () goal certificate = true
    rw [← erased']
    exact core.complete goal derivation
  exact CheckingWeakness.tooStrong_not_weakest
    ((CheckingWeakness.isWeakestAdmissible_iff_faithful _).mpr faithful)

/-! ## Semantic qualification: the separate interface -/

/-- A meaning closed under every local rule application, supplied separately
from `CoreNIK`. -/
structure SemanticQualification (σ : ReplaySignature.{u}) where
  Meaning : σ.Goal → Prop
  closed : ∀ label premises conclusion, σ.step label = some (premises, conclusion) →
    (∀ premise ∈ premises, Meaning premise) → Meaning conclusion

/-- Acceptance, derivability, truth: an accepted goal holds in every supplied
qualification. -/
theorem CoreNIK.accepted_meaning {σ : ReplaySignature.{u}}
    {implementation : σ.Goal → RawProof → Bool} (core : CoreNIK σ implementation)
    (qualification : SemanticQualification σ) {goal : σ.Goal} {certificate : RawProof}
    (accepted : implementation goal certificate = true) : qualification.Meaning goal := by
  obtain ⟨derivation, _⟩ := core.sound goal certificate accepted
  exact ReplaySignature.Deriv.sound qualification.Meaning qualification.closed derivation

/-- A goal outside the supplied meaning is rejected for every certificate. -/
theorem CoreNIK.rejects_outside_meaning {σ : ReplaySignature.{u}}
    {implementation : σ.Goal → RawProof → Bool} (core : CoreNIK σ implementation)
    (qualification : SemanticQualification σ) {goal : σ.Goal}
    (outside : ¬ qualification.Meaning goal) (certificate : RawProof) :
    implementation goal certificate = false := by
  cases accepted : implementation goal certificate with
  | false => rfl
  | true => exact absurd (core.accepted_meaning qualification accepted) outside

/-! ## The reflexive cell as a bootstrap layer -/

/-- A reflexive cell over a validated calculus: a validated presentation of
its replay rules. -/
structure ReflexiveCell (lower : ValidatedCalculusLanguageDef) where
  profile : CellProfile
  upper : ValidatedCalculusLanguageDef
  rulesEq : upper.1.rules = replayRules profile lower.1.rules

/-- Claims at every level are checking facts. -/
def CheckingClaim : Nat → Type := fun _ => Pattern × RawProof

/-- The meaning of a level-one claim about a validated calculus: its kind is
`sourceSound`, and a level-zero derivation of the goal erases to the
certificate. -/
def SourceSound (lower : ValidatedCalculusLanguageDef)
    (claim : LowerContract CheckingClaim 1) : Prop :=
  claim.kind = .sourceSound ∧
    ∃ derivation : Derivation lower claim.statement.1, derivation.erase = claim.statement.2

namespace ReflexiveCell

variable {lower : ValidatedCalculusLanguageDef} (cell : ReflexiveCell lower)

/-- The level-one checker: replay the certificate against the acceptance
judgment of the claimed fact; every other contract kind is rejected. -/
def checker : Checker (LowerContract CheckingClaim 1) RawProof where
  check claim certificate :=
    match claim.kind with
    | .sourceSound =>
        checkRaw cell.upper
          (acceptsJudgment cell.profile claim.statement.1
            (quoteProof cell.profile lower.1 claim.statement.2))
          certificate
    | _ => false

/-- A claim of another kind is rejected by every certificate. -/
theorem other_kind_rejected (claim : LowerContract CheckingClaim 1)
    (kindNe : claim.kind ≠ .sourceSound) (certificate : RawProof) :
    cell.checker.check claim certificate = false := by
  rcases claim with ⟨target, kind, statement⟩
  cases kind <;> first | exact absurd rfl kindNe | rfl

theorem checker_sound : cell.checker.Sound (SourceSound lower) := by
  intro claim certificate accepted
  by_cases kindEq : claim.kind = .sourceSound
  · rcases claim with ⟨target, kind, goal, rawCertificate⟩
    simp only at kindEq
    subst kindEq
    simp only [checker] at accepted
    refine ⟨rfl, ?_⟩
    obtain ⟨derivation⟩ := checkRaw_soundness accepted
    obtain ⟨found, foundAccepted, codeEq, _⟩ :=
      replay_sound cell.profile lower cell.upper cell.rulesEq (toDeriv derivation) goal _ rfl
    have same := quoteProof_injective cell.profile lower.1 _ _ codeEq
    subst same
    obtain ⟨replayDerivation, erased⟩ :=
      ReplaySignature.exists_deriv_of_replay _ _ foundAccepted
    exact ⟨ofDeriv replayDerivation, by
      rw [← erased, ← toDeriv_erase, toDeriv_ofDeriv]⟩
  · rw [cell.other_kind_rejected claim kindEq certificate] at accepted
    exact absurd accepted Bool.false_ne_true

theorem checker_complete : cell.checker.CertificateComplete (SourceSound lower) := by
  rintro ⟨target, kind, goal, rawCertificate⟩ ⟨kindEq, derivation, erased⟩
  simp only at kindEq
  subst kindEq
  refine ⟨replayProof cell.profile lower.1 rawCertificate, ?_⟩
  simp only [checker]
  rw [checkRaw_replayProof cell.profile lower cell.upper cell.rulesEq]
  have erased' : derivation.erase = rawCertificate := erased
  rw [← erased']
  exact checkRaw_erase derivation

/-- **The levelled cell.**  A reflexive cell is a bootstrap layer at host
level one whose checker is an exact authority for level-zero source
soundness. -/
def layer : BootstrapLayer CheckingClaim 1 where
  Certificate := RawProof
  Scope := SourceSound lower
  Meaning := SourceSound lower
  scope_sound := fun _ inScope => inScope
  checker := cell.checker
  scopeAuthority := ⟨cell.checker_sound, cell.checker_complete⟩

end ReflexiveCell

/-! ## Controls on the modus ponens package -/

section Controls

open Mettapedia.Languages.MeTTa.PrimeCandidates.MinimalCheckingPackage
open Mettapedia.GSLT.LanguageDef.BootstrapCell.Calibration

/-- The modus ponens cell as a reflexive cell. -/
def modusPonensReflexiveCell : ReflexiveCell mpValidated where
  profile := levelOne
  upper := modusPonensCellValidated
  rulesEq := modusPonensCell_rules

def sourceSoundClaim (goal : Pattern) (certificate : RawProof) :
    LowerContract CheckingClaim 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .sourceSound
  statement := (goal, certificate)

/-- **Positive control.**  The level-one layer accepts the claim that the
package derives `P(B)` with its certificate. -/
theorem layer_accepts_modusPonens :
    modusPonensReflexiveCell.layer.checker.check (sourceSoundClaim mpBGoal mpProofB)
      (replayProof levelOne mpCache mpProofB) = true :=
  modusPonensCell_accepts

/-- **Negative control.**  No certificate makes the layer accept the wrong
goal. -/
theorem layer_rejects_wrong_goal (certificate : RawProof) :
    modusPonensReflexiveCell.layer.checker.check (sourceSoundClaim mpWrongGoal mpProofB)
      certificate = false := by
  cases accepted : modusPonensReflexiveCell.layer.checker.check
      (sourceSoundClaim mpWrongGoal mpProofB) certificate with
  | false => rfl
  | true =>
      obtain ⟨_, derivation, erased⟩ :=
        modusPonensReflexiveCell.checker_sound _ certificate accepted
      have checked := checkRaw_erase derivation
      change derivation.erase = mpProofB at erased
      rw [erased] at checked
      change checkRaw mpValidated mpWrongGoal mpProofB = true at checked
      rw [mpWrongGoal_rejected] at checked
      exact absurd checked Bool.false_ne_true

/-- **Negative control.**  The replay layer cannot certify a model-soundness
claim, even about a fact it accepts. -/
theorem layer_rejects_modelSound (certificate : RawProof) :
    modusPonensReflexiveCell.layer.checker.check
      { targetLevel := ⟨0, by decide⟩, kind := .modelSound, statement := (mpBGoal, mpProofB) }
      certificate = false :=
  modusPonensReflexiveCell.other_kind_rejected _ (by decide) certificate

end Controls

end Mettapedia.GSLT.LanguageDef.BootstrapCell
