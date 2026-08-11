import Metamath.IncludeInterpretation
import Metamath.VerifyConformanceThms

/-!
# Order and agreement of Metamath verifier interpretations

The named verifier modes are points in a product of independent policy axes.
Consequently, mode comparison is generally a partial order rather than a
single strict/permissive ladder.

This file isolates the flag-governed local acceptance fragment from include
path identity and resolution.  The latter depend on an external file world
and are compared separately.
-/

namespace Mettapedia.Languages.Metamath.ModeInterpretationOrder

open Metamath.Verify
open Metamath.Verify.ModeConfig

/-- Uses of the local constructs whose acceptance is selected directly by an
`AcceptanceInterpretation`.  Include identity, path resolution, and cycle
handling are deliberately absent: those require a file-world semantics. -/
structure LocalFeatures where
  unknownStep : Bool := false
  toplevelEssential : Bool := false
  duplicateFloat : Bool := false
  constantInInnerScope : Bool := false
  includeInInnerScope : Bool := false
  tokenSplicing : Bool := false
  invalidCompressedByte : Bool := false
  deriving DecidableEq, Repr

/-- Declarative local acceptance for one feature profile. -/
def LocalAccepted (policy : AcceptanceInterpretation)
    (features : LocalFeatures) : Prop :=
  (features.unknownStep = true → policy.rejectUnknownSteps = false) ∧
  (features.toplevelEssential = true → policy.rejectToplevelEss = false) ∧
  (features.duplicateFloat = true → policy.allowDuplicateFloat = true) ∧
  (features.constantInInnerScope = true →
    policy.allowConstInnerScope = true) ∧
  (features.includeInInnerScope = true →
    policy.allowIncludeInnerScope = true) ∧
  (features.tokenSplicing = true → policy.allowTokenSplicing = true) ∧
  (features.invalidCompressedByte = true →
    policy.compressedProofs.invalidBytes = CompressedInvalidBytePolicy.ignore)

/-- `larger` is a local relaxation of `smaller` when it accepts every local
feature profile accepted by `smaller`. -/
def LocallyRelaxes (smaller larger : AcceptanceInterpretation) : Prop :=
  ∀ features, LocalAccepted smaller features → LocalAccepted larger features

/-- Two policies agree on a declared fragment of local feature profiles. -/
def LocallyAgreeOn (fragment : LocalFeatures → Prop)
    (left right : AcceptanceInterpretation) : Prop :=
  ∀ features, fragment features →
    (LocalAccepted left features ↔ LocalAccepted right features)

/-- A uniform policy relaxation may widen local acceptance, but must retain
the same external include interpretation. -/
def UniformlyRelaxes (smaller larger : AcceptanceInterpretation) : Prop :=
  LocallyRelaxes smaller larger ∧ smaller.includes = larger.includes

/-- The local fragment on which Zar and `metamath.exe` make identical gate
decisions. -/
def ZarExeSharedFragment (features : LocalFeatures) : Prop :=
  features.duplicateFloat = false ∧
  features.includeInInnerScope = false ∧
  features.tokenSplicing = false

/-- The local fragment on which Zar and `metamath-knife` make identical gate
decisions. -/
def ZarKnifeSharedFragment (features : LocalFeatures) : Prop :=
  features.unknownStep = false ∧
  features.toplevelEssential = false ∧
  features.invalidCompressedByte = false

/-- The local fragment on which the proof-certified default and
`metamath-knife` make identical gate decisions. -/
def SoundKnifeSharedFragment (features : LocalFeatures) : Prop :=
  features.toplevelEssential = false ∧
  features.invalidCompressedByte = false

/-- The proof-certified default differs from Zar only by rejecting incomplete
proof steps. -/
def SoundZarSharedFragment (features : LocalFeatures) : Prop :=
  features.unknownStep = false

theorem locallyRelaxes_refl (policy : AcceptanceInterpretation) :
    LocallyRelaxes policy policy := by
  intro features accepted
  exact accepted

theorem locallyRelaxes_trans {first second third : AcceptanceInterpretation}
    (h₁ : LocallyRelaxes first second)
    (h₂ : LocallyRelaxes second third) :
    LocallyRelaxes first third := by
  intro features accepted
  exact h₂ features (h₁ features accepted)

/-- Zar is a uniform relaxation of the proof-certified default: it restores
unknown proof steps while retaining every other local and include policy. -/
theorem zar_locally_relaxes_soundDefault :
    LocallyRelaxes soundDefaultAcceptancePolicy zarAcceptancePolicy := by
  intro features accepted
  rcases accepted with ⟨_, toplevel, duplicate, constant, includeInner,
    splicing, invalid⟩
  exact ⟨(fun _ => rfl), toplevel, duplicate, constant, includeInner,
    splicing, invalid⟩

theorem zar_uniformly_relaxes_soundDefault :
    UniformlyRelaxes soundDefaultAcceptancePolicy zarAcceptancePolicy :=
  ⟨zar_locally_relaxes_soundDefault, rfl⟩

theorem soundDefault_agrees_with_zar_on_shared_fragment :
    LocallyAgreeOn SoundZarSharedFragment soundDefaultAcceptancePolicy
      zarAcceptancePolicy := by
  intro features noUnknown
  constructor
  · exact zar_locally_relaxes_soundDefault features
  · intro accepted
    rcases accepted with ⟨_, toplevel, duplicate, constant, includeInner,
      splicing, invalid⟩
    have unknown : features.unknownStep = false := noUnknown
    exact ⟨by simp [unknown], toplevel, duplicate, constant, includeInner,
      splicing, invalid⟩

/-- On the flag-governed local axes, `metamath.exe` is a genuine relaxation
of Zar's interpretation. -/
theorem exe_locally_relaxes_zar :
    LocallyRelaxes zarAcceptancePolicy metamathExeAcceptanceRequirement := by
  intro features accepted
  rcases accepted with ⟨unknown, toplevel, duplicate, constant, includeInner,
    splicing, invalid⟩
  exact ⟨unknown, toplevel, (fun _ => rfl), constant,
    (fun _ => rfl), (fun _ => rfl), invalid⟩

/-- The local relaxation is conservative on the fragment that does not use
the three constructs newly admitted by `metamath.exe`. -/
theorem exe_agrees_with_zar_on_shared_fragment :
    LocallyAgreeOn ZarExeSharedFragment zarAcceptancePolicy
      metamathExeAcceptanceRequirement := by
  intro features shared
  rcases shared with ⟨duplicate, includeInner, splicing⟩
  constructor
  · exact exe_locally_relaxes_zar features
  · intro accepted
    rcases accepted with ⟨unknown, toplevel, _, constant, _, _, invalid⟩
    exact ⟨unknown, toplevel, by simp [duplicate], constant,
      by simp [includeInner], by simp [splicing], invalid⟩

/-- `metamath.exe` accepts a local duplicate-`$f` profile that Zar rejects. -/
def duplicateFloatFeatures : LocalFeatures :=
  { duplicateFloat := true }

theorem duplicateFloat_accepted_by_exe :
    LocalAccepted metamathExeAcceptanceRequirement duplicateFloatFeatures := by
  simp [LocalAccepted, duplicateFloatFeatures,
    metamathExeAcceptanceRequirement]

theorem duplicateFloat_rejected_by_zar :
    ¬ LocalAccepted zarAcceptancePolicy duplicateFloatFeatures := by
  simp [LocalAccepted, duplicateFloatFeatures, zarAcceptancePolicy]

theorem zar_does_not_locally_relax_exe :
    ¬ LocallyRelaxes metamathExeAcceptanceRequirement zarAcceptancePolicy := by
  intro relaxation
  exact duplicateFloat_rejected_by_zar
    (relaxation duplicateFloatFeatures duplicateFloat_accepted_by_exe)

/-- `metamath-knife` is not globally above or below Zar even before include
resolution is considered: it rejects unknown proof steps that Zar admits. -/
def unknownStepFeatures : LocalFeatures :=
  { unknownStep := true }

theorem unknownStep_accepted_by_zar :
    LocalAccepted zarAcceptancePolicy unknownStepFeatures := by
  simp [LocalAccepted, unknownStepFeatures, zarAcceptancePolicy]

theorem unknownStep_rejected_by_knife :
    ¬ LocalAccepted metamathKnifeAcceptanceRequirement unknownStepFeatures := by
  simp [LocalAccepted, unknownStepFeatures,
    metamathKnifeAcceptanceRequirement]

theorem unknownStep_rejected_by_soundDefault :
    ¬ LocalAccepted soundDefaultAcceptancePolicy unknownStepFeatures := by
  simp [LocalAccepted, unknownStepFeatures, soundDefaultAcceptancePolicy,
    zarAcceptancePolicy]

theorem soundDefault_does_not_locally_relax_zar :
    ¬ LocallyRelaxes zarAcceptancePolicy soundDefaultAcceptancePolicy := by
  intro relaxation
  exact unknownStep_rejected_by_soundDefault
    (relaxation unknownStepFeatures unknownStep_accepted_by_zar)

theorem knife_does_not_locally_relax_zar :
    ¬ LocallyRelaxes zarAcceptancePolicy metamathKnifeAcceptanceRequirement := by
  intro relaxation
  exact unknownStep_rejected_by_knife
    (relaxation unknownStepFeatures unknownStep_accepted_by_zar)

/-- Conversely, Knife ignores invalid compressed-proof bytes that Zar
rejects. -/
def invalidCompressedByteFeatures : LocalFeatures :=
  { invalidCompressedByte := true }

theorem invalidCompressedByte_accepted_by_knife :
    LocalAccepted metamathKnifeAcceptanceRequirement
      invalidCompressedByteFeatures := by
  simp [LocalAccepted, invalidCompressedByteFeatures,
    metamathKnifeAcceptanceRequirement, metamathKnifeCompressedProofPolicy]

theorem invalidCompressedByte_rejected_by_zar :
    ¬ LocalAccepted zarAcceptancePolicy invalidCompressedByteFeatures := by
  simp [LocalAccepted, invalidCompressedByteFeatures, zarAcceptancePolicy,
    strictCompressedProofPolicy]

theorem zar_does_not_locally_relax_knife :
    ¬ LocallyRelaxes metamathKnifeAcceptanceRequirement zarAcceptancePolicy := by
  intro relaxation
  exact invalidCompressedByte_rejected_by_zar
    (relaxation invalidCompressedByteFeatures
      invalidCompressedByte_accepted_by_knife)

theorem knife_agrees_with_zar_on_shared_fragment :
    LocallyAgreeOn ZarKnifeSharedFragment zarAcceptancePolicy
      metamathKnifeAcceptanceRequirement := by
  intro features shared
  rcases shared with ⟨unknown, toplevel, invalid⟩
  constructor <;> intro accepted
  · rcases accepted with ⟨_, _, duplicate, constant, includeInner, splicing, _⟩
    exact ⟨by simp [unknown], by simp [toplevel], duplicate, constant, includeInner,
      splicing, by simp [invalid]⟩
  · rcases accepted with ⟨_, _, duplicate, constant, includeInner, splicing, _⟩
    exact ⟨by simp [unknown], by simp [toplevel], duplicate, constant, includeInner,
      splicing, by simp [invalid]⟩

theorem knife_agrees_with_soundDefault_on_shared_fragment :
    LocallyAgreeOn SoundKnifeSharedFragment soundDefaultAcceptancePolicy
      metamathKnifeAcceptanceRequirement := by
  intro features shared
  rcases shared with ⟨toplevel, invalid⟩
  constructor <;> intro accepted
  · rcases accepted with ⟨unknown, _, duplicate, constant, includeInner, splicing, _⟩
    exact ⟨unknown, by simp [toplevel], duplicate, constant, includeInner, splicing,
      by simp [invalid]⟩
  · rcases accepted with ⟨unknown, _, duplicate, constant, includeInner, splicing, _⟩
    exact ⟨unknown, by simp [toplevel], duplicate, constant, includeInner, splicing,
      by simp [invalid]⟩

/-- The reference modes select distinct specification-licensed include
interpretations.  Therefore their local order must not be promoted to a
whole-source order without an explicit relation between file worlds. -/
theorem exe_include_interpretation_differs_from_zar :
    metamathExeAcceptanceRequirement.includes ≠ zarAcceptancePolicy.includes := by
  decide

theorem knife_include_interpretation_differs_from_zar :
    metamathKnifeAcceptanceRequirement.includes ≠ zarAcceptancePolicy.includes := by
  decide

theorem exe_does_not_uniformly_relax_zar :
    ¬ UniformlyRelaxes zarAcceptancePolicy metamathExeAcceptanceRequirement := by
  intro relaxation
  exact exe_include_interpretation_differs_from_zar relaxation.2.symm

/-- Prefix-proof authority is another independent capability axis: Knife and
the proof-certified default possess it, whereas `metamath.exe` does not. -/
theorem knife_is_prefixCertified : ModeConfig.prefixCertified ModeConfig.knife :=
  ModeConfig.knife_prefixCertified

theorem soundDefault_is_prefixCertified :
    ModeConfig.prefixCertified ModeConfig.soundDefault :=
  ModeConfig.soundDefault_prefixCertified

theorem exe_is_not_prefixCertified :
    ¬ ModeConfig.prefixCertified ModeConfig.exe :=
  ModeConfig.not_exe_prefixCertified

end Mettapedia.Languages.Metamath.ModeInterpretationOrder
